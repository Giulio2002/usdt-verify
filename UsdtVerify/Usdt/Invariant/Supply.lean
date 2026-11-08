import UsdtVerify.Summary
import UsdtVerify.Usdt.Spec.Strings

/-!
# The global invariant: the sum of all balances equals `_totalSupply`

The token state is read from the storage of the contract `C`:

- `balances[a]` is the word of slot `mapSlot a 2` (`keccak(a ++ 2)`), for the 2^160 addresses `a`
  (as words below 2^160);
- `_totalSupply` is the word of slot 1.

`sumBal C S` is the sum, as an integer, of the 2^160 balance words in the state `S`; `tot C S`
is the word of slot 1; `Inv C S` says they are equal.

The hypothesis `KeccakSep` is about keccak only, and it is NOT proved: distinct addresses have
distinct balance slots; a balance slot is never one of the fixed slots 0..10, never a slot of
`isBlackListed` (`mapSlot y 6`) nor of `allowed` (`mapSlot y (mapSlot z 5)`); slot 1 is never a
slot of `isBlackListed` nor of `allowed`.

Under `KeccakSep`, the end state of every proved success path of the 32 functions (contract not
deprecated) keeps `Inv` (`*_inv`); `Step` collects those end states, and `steps_inv` lifts the
invariant to any finite sequence of them. For destroyBlackFunds, whose subtraction from
`_totalSupply` is unchecked, `Inv` itself gives `d ≤ _totalSupply` (a balance is at most the sum),
so the subtraction does not wrap and `Inv` holds after it (`destroy_inv`).
-/

namespace UsdtVerify.Invariant

open EthLib.Base (Fork U256 Address)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open Transfer TransferOk TransferFee TransferFrom StringsGen

/-! ## The hypotheses on keccak

`mapSlot k b` is the concrete `keccak(k ++ b)`, so each hypothesis below is a closed proposition
about one fixed function, not proved. Since round 29 every one of them is about finitely many
slots: a given slot `n` against the 2^160 balance slots (`NotBal n`, `UniqBal x`), or a given
slot against the fixed slots 0..10. Treating keccak on these inputs as a random function, each fails with
probability about 2^160 / 2^256 = 2^-96 (or 11 / 2^256 against the fixed slots); a failure would be a keccak
collision between a given slot and one of 2^160 others, which nobody can find.

`SepOn A`: these facts for the slots keyed by the address words of a finite list `A`
(`callKeys message S`: the caller, the first two address arguments, the owner of `S`), and for
the fixed slots 0..10.

Through round 28 the theorems assumed `KeccakSep` instead: the same separation for ALL keys at
once. Its fields quantify over 2^256 or 2^512 inputs and are almost certainly false
(docs/AUDIT.md, finding 1), which made the theorems that assume it vacuous. `KeccakSep` and
`AllowSep` imply `SepOn A` for every `A` (`Security.sepOn_of_global`), so each old form follows
from the new one. -/

/-- No address word has `n` as its balance slot. -/
def NotBal (n : U256) : Prop := ∀ x : U256, x.toNat < 2 ^ 160 → n ≠ mapSlot x 2

/-- No address word other than `x` has the balance slot of `x`. -/
def UniqBal (x : U256) : Prop :=
  ∀ y : U256, y.toNat < 2 ^ 160 → mapSlot y 2 = mapSlot x 2 → y = x

/-- `n` is none of the eleven fixed slots 0..10. -/
def NotFixed (n : U256) : Prop := ∀ k : Nat, k < 11 → n ≠ BitVec.ofNat 256 k

/-- None of the eleven fixed slots 0..10 is a balance slot. -/
def FixedSep : Prop := ∀ n : Nat, n < 11 → NotBal (BitVec.ofNat 256 n)

/-- The separation that the invariant proofs use, for the slots keyed by the words of `A`:
the fixed slots are no balance slot; the balance slot of an address word of `A` is that of no
other address word; a slot of `isBlackListed` keyed by a word of `A` is no balance slot and not
slot 1; a slot of `allowed` keyed by two words of `A` is no balance slot and no fixed slot.
Finitely many facts, each about one given slot. -/
structure SepOn (A : List U256) : Prop where
  fixed : FixedSep
  uniq : ∀ x ∈ A, x.toNat < 2 ^ 160 → UniqBal x
  list : ∀ y ∈ A, NotBal (mapSlot y 6) ∧ mapSlot y 6 ≠ 1
  allow : ∀ y ∈ A, ∀ z ∈ A, NotBal (mapSlot y (mapSlot z 5)) ∧ NotFixed (mapSlot y (mapSlot z 5))

theorem SepOn.mono {A B : List U256} (h : SepOn B) (hAB : ∀ x ∈ A, x ∈ B) : SepOn A :=
  ⟨h.fixed, fun x hx => h.uniq x (hAB x hx), fun y hy => h.list y (hAB y hy),
    fun y hy z hz => h.allow y (hAB y hy) z (hAB z hz)⟩

theorem NotFixed.ne_one {n : U256} (h : NotFixed n) : n ≠ 1 := h 1 (by decide)

/-- The address words a call uses as mapping keys: the caller, the first two address arguments
(recipient, spender, `_from`, `_to`, the listed or destroyed address), and the owner (the low 160
bits of slot 0 of the start state `S`). -/
def callKeys {fork : Fork} (message : Message fork) (S : State.TransactionState) : List U256 :=
  [Owner.callerWord message, addrArg message.data 0, addrArg message.data 1,
    Owner.ownerOf S message.currentTarget]

/-- Through round 28: what the proofs assumed of keccak, for all keys at once. Almost certainly
false (docs/AUDIT.md, finding 1); kept only to state that, with `AllowSep`, it implies `SepOn A`
for every `A` (`Security.sepOn_of_global`). -/
structure KeccakSep : Prop where
  /-- Distinct addresses have distinct balance slots. -/
  inj : ∀ x y : U256, x.toNat < 2 ^ 160 → y.toNat < 2 ^ 160 → mapSlot x 2 = mapSlot y 2 → x = y
  /-- A balance slot is not one of the fixed slots 0..10. -/
  fixed : ∀ x : U256, ∀ n : Nat, n < 11 → mapSlot x 2 ≠ BitVec.ofNat 256 n
  /-- A balance slot is not a slot of `isBlackListed`. -/
  list : ∀ x y : U256, mapSlot x 2 ≠ mapSlot y 6
  /-- A balance slot is not a slot of `allowed`. -/
  allow : ∀ x y z : U256, mapSlot x 2 ≠ mapSlot y (mapSlot z 5)
  /-- Slot 1 is not a slot of `isBlackListed`. -/
  one_list : ∀ y : U256, mapSlot y 6 ≠ 1
  /-- Slot 1 is not a slot of `allowed`. -/
  one_allow : ∀ y z : U256, mapSlot y (mapSlot z 5) ≠ 1

/-! ## The token state -/

/-- `Σ_{i < n} f i`. -/
def sumTo (f : Nat → Int) : Nat → Int
  | 0 => 0
  | n + 1 => sumTo f n + f n

theorem sumTo_congr {f g : Nat → Int} : ∀ n, (∀ i, i < n → f i = g i) → sumTo f n = sumTo g n
  | 0, _ => rfl
  | n + 1, h => by
    rw [sumTo, sumTo, sumTo_congr n (fun i hi => h i (by omega)), h n (by omega)]

theorem sumTo_update {f g : Nat → Int} {a : Nat} :
    ∀ n, a < n → (∀ i, i < n → i ≠ a → g i = f i) → sumTo g n = sumTo f n - f a + g a
  | 0, h, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, h, hfg => by
    rw [sumTo, sumTo]
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ h) with h' | h'
    · rw [sumTo_update n h' (fun i hi hia => hfg i (by omega) hia), hfg n (by omega) (by omega)]
      omega
    · subst h'
      rw [sumTo_congr a (fun i hi => hfg i (by omega) (by omega))]; omega

theorem sumTo_nonneg {f : Nat → Int} (hf : ∀ i, 0 ≤ f i) : ∀ n, 0 ≤ sumTo f n
  | 0 => Int.le_refl _
  | n + 1 => by rw [sumTo]; have := sumTo_nonneg hf n; have := hf n; omega

theorem le_sumTo {f : Nat → Int} (hf : ∀ i, 0 ≤ f i) {a : Nat} : ∀ n, a < n → f a ≤ sumTo f n
  | 0, h => absurd h (Nat.not_lt_zero _)
  | n + 1, h => by
    rw [sumTo]
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ h) with h' | h'
    · have := le_sumTo hf n h'; have := hf n; omega
    · subst h'; have := sumTo_nonneg hf a; omega

/-- `balances[i]` (as an integer) for the address number `i`. -/
abbrev bal (C : Address) (S : State.TransactionState) (i : Nat) : Int :=
  ((storageAt S C (mapSlot (BitVec.ofNat 256 i) 2)).toNat : Int)

/-- The sum of the balances of the 2^160 addresses. -/
def sumBal (C : Address) (S : State.TransactionState) : Int := sumTo (bal C S) (2 ^ 160)

/-- `_totalSupply` (slot 1). -/
abbrev tot (C : Address) (S : State.TransactionState) : Int := ((storageAt S C 1).toNat : Int)

/-- The invariant: the sum of all balances is `_totalSupply`. -/
def Inv (C : Address) (S : State.TransactionState) : Prop := sumBal C S = tot C S

/-! ## Reads and writes -/

theorem mask_lt (x : U256) : (bitwiseAnd ADDR_MASK x).toNat < 2 ^ 160 := by
  simp only [bitwiseAnd, BitVec.toNat_and, ADDR_MASK, BitVec.toNat_ofNat]
  exact Nat.lt_of_le_of_lt Nat.and_le_left (by decide)

theorem ofNat_toNat (x : U256) : BitVec.ofNat 256 x.toNat = x := by
  apply BitVec.eq_of_toNat_eq; simp

variable {C : Address}

theorem sumBal_readSlot (S : State.TransactionState) (c : Address) (n : U256) :
    sumBal C (readSlot S c n) = sumBal C S := by
  unfold sumBal
  exact sumTo_congr _ (fun i _ => by simp only [bal, storageAt_readSlot])

theorem tot_readSlot (S : State.TransactionState) (c : Address) (n : U256) :
    tot C (readSlot S c n) = tot C S := by
  simp only [tot, storageAt_readSlot]

theorem inv_readSlot {S : State.TransactionState} (c : Address) (n : U256) :
    Inv C (readSlot S c n) ↔ Inv C S := by
  unfold Inv; rw [sumBal_readSlot, tot_readSlot]

theorem nb_fixed (F : FixedSep) {n : Nat} (h : n < 11) : NotBal (BitVec.ofNat 256 n) := F n h

/-- Slot 1 is no balance slot. -/
theorem nb1 (F : FixedSep) : NotBal 1 := F 1 (by decide)

theorem bal_ne_one (F : FixedSep) {x : U256} (hx : x.toNat < 2 ^ 160) : mapSlot x 2 ≠ 1 :=
  fun e => F 1 (by decide) x hx e.symm

theorem bal_ne_zero (F : FixedSep) {x : U256} (hx : x.toNat < 2 ^ 160) : mapSlot x 2 ≠ 0 :=
  fun e => F 0 (by decide) x hx e.symm

theorem sumBal_write_nb {S : State.TransactionState} (hacc : hasAccount S C) {n : U256}
    (hn : NotBal n) (v : U256) : sumBal C (writeSlot S C n v) = sumBal C S := by
  unfold sumBal
  refine sumTo_congr _ (fun i hi => ?_)
  have hi' : (BitVec.ofNat 256 i : U256).toNat < 2 ^ 160 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hi
  simp only [bal, storageAt_writeSlot_of_ne hacc (fun e => hn _ hi' e.symm)]

theorem sumBal_write_bal {S : State.TransactionState} (hacc : hasAccount S C)
    {x : U256} (hu : UniqBal x) (hx : x.toNat < 2 ^ 160) (v : U256) :
    sumBal C (writeSlot S C (mapSlot x 2) v) =
      sumBal C S - (storageAt S C (mapSlot x 2)).toNat + v.toNat := by
  unfold sumBal
  have h := sumTo_update (f := bal C S) (g := bal C (writeSlot S C (mapSlot x 2) v))
    (a := x.toNat) (2 ^ 160) hx (fun i hi2 hi => ?_)
  · rw [h]
    simp only [bal, ofNat_toNat, storageAt_writeSlot_self hacc]
  · have hne : mapSlot (BitVec.ofNat 256 i) 2 ≠ mapSlot x 2 := by
      intro e
      apply hi
      have := hu _ (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hi2) e
      rw [← this, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    simp only [bal, storageAt_writeSlot_of_ne hacc hne]

theorem tot_write_ne {S : State.TransactionState} (hacc : hasAccount S C) {n : U256} (hn : n ≠ 1)
    (v : U256) : tot C (writeSlot S C n v) = tot C S := by
  simp only [tot, storageAt_writeSlot_of_ne hacc (Ne.symm hn)]

theorem tot_write_one {S : State.TransactionState} (hacc : hasAccount S C) (v : U256) :
    tot C (writeSlot S C 1 v) = v.toNat := by
  simp only [tot, storageAt_writeSlot_self hacc]

/-- Threads `hasAccount` through reads and writes. -/
macro "acc" : tactic =>
  `(tactic| repeat (first | with_reducible assumption | with_reducible apply hasAccount_readSlot | with_reducible apply hasAccount_writeSlot))

theorem toNat_sub {x a : U256} (h : a.toNat ≤ x.toNat) : ((sub x a).toNat : Int) = x.toNat - a.toNat := by
  rw [IssueSpec.toNat_sub' h]; omega

theorem toNat_add {a b : U256} (h : a.toNat + b.toNat < 2 ^ 256) :
    ((add a b).toNat : Int) = a.toNat + b.toNat := by
  rw [Summary.toNat_add_of_lt' h]; omega

/-! ## transfer -/

variable {fork : Fork}

/-- transfer with fee 0 (`credited`, the end state of `transfer_ok` over its `S`). -/
theorem transferOk_inv (F : FixedSep) {S : State.TransactionState} {message : Message fork}
    {v a : U256} (hacc : hasAccount S message.currentTarget)
    (hus : UniqBal (callerKey message)) (hur : UniqBal (mkey a))
    (hv : v.toNat ≤ (balS S message).toNat)
    (ht : (balT S message v a).toNat + v.toNat < 2 ^ 256)
    (hI : Inv message.currentTarget S) : Inv message.currentTarget (credited S message v a) := by
  unfold Inv at *
  simp only [credited, debited, reads3, balT, balS, senderSlot, recipientSlot, callerKey, mkey] at *
  rw [sumBal_write_bal ?_ ?_ (mask_lt _), sumBal_readSlot, sumBal_write_bal ?_ ?_
    (mask_lt _), sumBal_readSlot, sumBal_readSlot, sumBal_readSlot,
    tot_write_ne ?_ (bal_ne_one F ?_), tot_readSlot, tot_write_ne ?_ (bal_ne_one F ?_),
    tot_readSlot, tot_readSlot, tot_readSlot, toNat_add ht, storageAt_readSlot,
    storageAt_readSlot, storageAt_readSlot, storageAt_readSlot, toNat_sub hv]
  · omega
  all_goals first | with_reducible assumption | exact mask_lt _ | acc

theorem addrArg_lt (d : ByteArray) (i : Nat) : (addrArg d i).toNat < 2 ^ 160 := mask_lt _

theorem nb0 (F : FixedSep) : NotBal (0 : U256) := nb_fixed F (n := 0) (by decide)
theorem nb3 (F : FixedSep) : NotBal (3 : U256) := nb_fixed F (n := 3) (by decide)
theorem nb4 (F : FixedSep) : NotBal (4 : U256) := nb_fixed F (n := 4) (by decide)
theorem nb10 (F : FixedSep) : NotBal (10 : U256) := nb_fixed F (n := 10) (by decide)

/-- transfer with a fee (`feeState`, the end state of `transfer_fee` over its `S`). -/
theorem transferFee_inv (F : FixedSep) {S : State.TransactionState} {message : Message fork}
    {v a : U256} (hacc : hasAccount S message.currentTarget)
    (hus : UniqBal (callerKey message)) (hur : UniqBal (mkey a))
    (huo : UniqBal (mkey (ownerKey (storageAt (creditedFee S message v a) message.currentTarget 0))))
    (hf : (feeOf S message v).toNat ≤ v.toNat)
    (hv : v.toNat ≤ (balS S message).toNat)
    (ht : (balT S message v a).toNat + (sendOf S message v).toNat < 2 ^ 256)
    (ho : (balO S message v a).toNat + (feeOf S message v).toNat < 2 ^ 256)
    (hI : Inv message.currentTarget S) : Inv message.currentTarget (feeState S message v a) := by
  unfold Inv at *
  simp only [feeState, ownedB, creditedFee, debited, reads3, balT, balS, sendOf, balO, balOf,
    ownerSlotOf, ownerSlot, senderSlot, recipientSlot, callerKey, mkey] at *
  simp only [sumBal_readSlot, tot_readSlot] at *
  rw [sumBal_write_bal ?_ ?_ (mask_lt _), sumBal_readSlot, sumBal_readSlot, sumBal_readSlot,
    sumBal_write_bal ?_ ?_ (mask_lt _), sumBal_readSlot, sumBal_write_bal ?_ ?_ (mask_lt _),
    sumBal_readSlot, sumBal_readSlot, sumBal_readSlot,
    tot_write_ne ?_ (bal_ne_one F ?_), tot_readSlot, tot_readSlot, tot_readSlot,
    tot_write_ne ?_ (bal_ne_one F ?_), tot_readSlot, tot_write_ne ?_ (bal_ne_one F ?_),
    tot_readSlot, tot_readSlot, tot_readSlot]
  simp only [storageAt_readSlot]
  rw [toNat_add ho, toNat_add ht, toNat_sub hf, toNat_sub hv]
  · omega
  all_goals first | with_reducible assumption | exact mask_lt _ | acc

/-- The allowance step of transferFrom keeps the balances and slot 1. -/
theorem allowState_keeps {S : State.TransactionState} {C : Address}
    (hacc : hasAccount S C) {n A v : U256} (hn : NotBal n) (h1 : n ≠ 1) :
    sumBal C (allowState S C n A v) = sumBal C S ∧
    tot C (allowState S C n A v) = tot C S ∧
    hasAccount (allowState S C n A v) C ∧
    ∀ x : U256, x.toNat < 2 ^ 160 →
      storageAt (allowState S C n A v) C (mapSlot x 2) = storageAt S C (mapSlot x 2) := by
  unfold allowState
  split
  · exact ⟨rfl, rfl, hacc, fun _ _ => rfl⟩
  · refine ⟨sumBal_write_nb hacc hn _, tot_write_ne hacc h1 _,
      hasAccount_writeSlot hacc, fun x hx => storageAt_writeSlot_of_ne hacc (fun e => hn x hx e.symm)⟩

theorem sumBal_allowState {S : State.TransactionState} {C : Address}
    (hacc : hasAccount S C) {n A v : U256} (hn : NotBal n) :
    sumBal C (allowState S C n A v) = sumBal C S := by
  unfold allowState; split
  · rfl
  · exact sumBal_write_nb hacc hn _

theorem tot_allowState {S : State.TransactionState} {C : Address}
    (hacc : hasAccount S C) {n A v : U256} (h1 : n ≠ 1) :
    tot C (allowState S C n A v) = tot C S := by
  unfold allowState; split
  · rfl
  · exact tot_write_ne hacc h1 _

theorem hasAccount_allowState {S : State.TransactionState} {C : Address} (hacc : hasAccount S C)
    {n A v : U256} : hasAccount (allowState S C n A v) C := by
  unfold allowState; split
  · exact hacc
  · exact hasAccount_writeSlot hacc

/-- Threads `hasAccount` through reads, writes and the allowance step. -/
macro "accF" : tactic =>
  `(tactic| repeat (first | with_reducible assumption | with_reducible apply hasAccount_readSlot | with_reducible apply hasAccount_writeSlot | with_reducible apply hasAccount_allowState))

/-- transferFrom with fee 0 (`creditedF`, the end state of `transferFrom_ok` over its `S`). -/
theorem transferFromOk_inv (F : FixedSep) {S : State.TransactionState} {message : Message fork}
    {v t f : U256} (hacc : hasAccount S message.currentTarget)
    (hnA : NotBal (allowFrom message f)) (h1A : allowFrom message f ≠ 1)
    (huf : UniqBal (mkey f)) (hut : UniqBal (mkey t))
    (hv : v.toNat ≤ (balFrom S message v f).toNat)
    (ht : (balTo S message v t f).toNat + v.toNat < 2 ^ 256)
    (hI : Inv message.currentTarget S) : Inv message.currentTarget (creditedF S message v t f) := by
  unfold Inv at *
  simp only [creditedF, debitedF, allowedF, balTo, balFrom, recipientSlot, allowFrom, readsF,
    allowOf, mkey] at *
  rw [sumBal_write_bal ?_ ?_ (mask_lt _), sumBal_readSlot, sumBal_write_bal ?_ ?_ (mask_lt _),
    sumBal_readSlot, sumBal_allowState ?_ ?_, sumBal_readSlot, sumBal_readSlot, sumBal_readSlot,
    tot_write_ne ?_ (bal_ne_one F ?_), tot_readSlot,
    tot_write_ne ?_ (bal_ne_one F ?_), tot_readSlot, tot_allowState ?_ ?_, tot_readSlot,
    tot_readSlot, tot_readSlot]
  simp only [storageAt_readSlot] at *
  rw [toNat_add ht, toNat_sub hv]
  · omega
  all_goals first | with_reducible assumption | exact mask_lt _ | accF

/-- transferFrom with a fee (`feeStateF`, the end state of `transferFrom_fee` over its `S`). -/
theorem transferFromFee_inv (F : FixedSep) {S : State.TransactionState} {message : Message fork}
    {v t f : U256} (hacc : hasAccount S message.currentTarget)
    (hnA : NotBal (allowFrom message f)) (h1A : allowFrom message f ≠ 1)
    (huf : UniqBal (mkey f)) (hut : UniqBal (mkey t))
    (huo : UniqBal (mkey (ownerKey (storageAt (creditedFeeF S message v t f)
      message.currentTarget 0))))
    (hf : (feeOf S message v).toNat ≤ v.toNat)
    (hv : v.toNat ≤ (balFrom S message v f).toNat)
    (ht : (balTo S message v t f).toNat + (sendOf S message v).toNat < 2 ^ 256)
    (ho : (balOF S message v t f).toNat + (feeOf S message v).toNat < 2 ^ 256)
    (hI : Inv message.currentTarget S) : Inv message.currentTarget (feeStateF S message v t f) := by
  unfold Inv at *
  simp only [feeStateF, ownedB, creditedFeeF, debitedF, allowedF, balTo, balFrom, sendOf, balOF,
    balOf, ownerSlotOf, ownerSlot, recipientSlot, allowFrom, readsF, allowOf, mkey] at *
  rw [sumBal_readSlot, sumBal_write_bal ?_ ?_ (mask_lt _), sumBal_readSlot, sumBal_readSlot,
    sumBal_readSlot, sumBal_write_bal ?_ ?_ (mask_lt _), sumBal_readSlot,
    sumBal_write_bal ?_ ?_ (mask_lt _), sumBal_readSlot, sumBal_allowState ?_ ?_, sumBal_readSlot,
    sumBal_readSlot, sumBal_readSlot, tot_readSlot, tot_write_ne ?_ (bal_ne_one F ?_), tot_readSlot,
    tot_readSlot, tot_readSlot, tot_write_ne ?_ (bal_ne_one F ?_), tot_readSlot,
    tot_write_ne ?_ (bal_ne_one F ?_), tot_readSlot, tot_allowState ?_ ?_, tot_readSlot,
    tot_readSlot, tot_readSlot]
  simp only [storageAt_readSlot] at *
  rw [toNat_add ho, toNat_add ht, toNat_sub hf, toNat_sub hv]
  · omega
  all_goals first | with_reducible assumption | exact mask_lt _ | accF

/-! ## Writes of other slots, and the read-only functions -/

theorem inv_write_nb {S : State.TransactionState} {C : Address} (hacc : hasAccount S C) {n : U256}
    (hn : NotBal n) (h1 : n ≠ 1) (v : U256) : Inv C (writeSlot S C n v) ↔ Inv C S := by
  unfold Inv; rw [sumBal_write_nb hacc hn, tot_write_ne hacc h1]

theorem one_ne0 : (0 : U256) ≠ 1 := by decide
theorem one_ne3 : (3 : U256) ≠ 1 := by decide
theorem one_ne4 : (4 : U256) ≠ 1 := by decide
theorem one_ne10 : (10 : U256) ≠ 1 := by decide

/-- The read-only functions: their end states only record reads (`readSlot`, and `rdSt` for the
data slots of a long string). -/
theorem inv_rdSt {S : State.TransactionState} {C c : Address} {h : U256} :
    ∀ j, Inv C (rdSt S c h j) ↔ Inv C S
  | 0 => Iff.rfl
  | j + 1 => by rw [rdSt, inv_readSlot, inv_rdSt j]

/-- approve(s, 0) (`approve_zero`'s end state). -/
theorem approveZero_inv {S : State.TransactionState} {message : Message fork}
    (hacc : hasAccount S message.currentTarget) (hn : NotBal (Approve.allowArg message))
    (h1 : Approve.allowArg message ≠ 1) (hI : Inv message.currentTarget S) :
    Inv message.currentTarget (writeSlot (readSlot S message.currentTarget 10) message.currentTarget
      (Approve.allowArg message) 0) := by
  rw [inv_write_nb (hasAccount_readSlot hacc) hn h1, inv_readSlot]
  exact hI

/-- approve(s, v), v ≠ 0 (`approve_set`'s end state). -/
theorem approveSet_inv {S : State.TransactionState} {message : Message fork}
    (hacc : hasAccount S message.currentTarget) (hn : NotBal (Approve.allowArg message))
    (h1 : Approve.allowArg message ≠ 1) (hI : Inv message.currentTarget S) :
    Inv message.currentTarget (writeSlot (readSlot (readSlot S message.currentTarget 10)
      message.currentTarget (Approve.allowArg message)) message.currentTarget
      (Approve.allowArg message) (wordArg message.data 1)) := by
  rw [inv_write_nb (hasAccount_readSlot (hasAccount_readSlot hacc)) hn h1, inv_readSlot,
    inv_readSlot]
  exact hI

/-- pause() / unpause() (one write of slot 0). -/
theorem pause_inv (F : FixedSep) {S : State.TransactionState} {C : Address} (hacc : hasAccount S C)
    (b : U256) (hI : Inv C S) : Inv C (writeSlot S C 0 (Pause.withPaused (storageAt S C 0) b)) := by
  rw [inv_write_nb hacc (nb0 F) one_ne0]; exact hI

/-- transferOwnership(a), a ≠ 0 (one write of slot 0). -/
theorem transferOwnership_inv (F : FixedSep) {S : State.TransactionState} {C : Address}
    (hacc : hasAccount S C) (a : U256) (hI : Inv C S) :
    Inv C (writeSlot S C 0 (AddrWrite.withAddr (storageAt S C 0) a)) := by
  rw [inv_write_nb hacc (nb0 F) one_ne0]; exact hI

/-- addBlackList(a) / removeBlackList(a) (`listState`). -/
theorem list_inv {S : State.TransactionState} {message : Message fork}
    (hacc : hasAccount S message.currentTarget)
    (hn : NotBal (BlackList.listSlot (addrArg message.data 0)))
    (h1 : BlackList.listSlot (addrArg message.data 0) ≠ 1) (v : U256)
    (hI : Inv message.currentTarget S) :
    Inv message.currentTarget (BlackListSpec.listState S message v) := by
  simp only [BlackListSpec.listState]
  rw [inv_write_nb (hasAccount_readSlot hacc) hn h1, inv_readSlot]
  exact hI

/-- setParams(b, m) (`paramsState`: writes of slots 3 and 4). -/
theorem params_inv (F : FixedSep) {S : State.TransactionState} {message : Message fork}
    (hacc : hasAccount S message.currentTarget) (hI : Inv message.currentTarget S) :
    Inv message.currentTarget (SetParamsSpec.paramsState S message) := by
  simp only [SetParamsSpec.paramsState]
  rw [inv_readSlot, inv_readSlot, inv_write_nb (by acc) (nb4 F) one_ne4, inv_readSlot,
    inv_write_nb (by acc) (nb3 F) one_ne3, inv_readSlot]
  exact hI

/-- deprecate(a) (`depState`: two writes of slot 10). -/
theorem deprecate_inv (F : FixedSep) {S : State.TransactionState} {message : Message fork}
    (hacc : hasAccount S message.currentTarget) (hI : Inv message.currentTarget S) :
    Inv message.currentTarget (AddrWriteSpec.depState S message) := by
  simp only [AddrWriteSpec.depState]
  rw [inv_write_nb (by acc) (nb10 F) one_ne10, inv_write_nb (by acc) (nb10 F) one_ne10, inv_readSlot]
  exact hI

/-! ## issue, redeem, destroyBlackFunds: the writes of slot 1 -/

/-- issue(n) (`issueState`): `balances[owner] += n`, then `_totalSupply += n`, with the two
`require`s of the code (no wrap) as hypotheses, as `issue` states them. -/
theorem issue_inv (F : FixedSep) {S : State.TransactionState} {message : Message fork}
    (hacc : hasAccount S message.currentTarget)
    (huo : UniqBal (Owner.ownerOf S message.currentTarget))
    (hT : (storageAt S message.currentTarget 1).toNat + (wordArg message.data 0).toNat < 2 ^ 256)
    (hB : (storageAt S message.currentTarget (Issue.ownerBal S message.currentTarget)).toNat +
        (wordArg message.data 0).toNat < 2 ^ 256)
    (hI : Inv message.currentTarget S) : Inv message.currentTarget (IssueSpec.issueState S message) := by
  unfold Inv at *
  simp only [IssueSpec.issueState, IssueSpec.issueState1, IssueSpec.reqState, Issue.ownerBal,
    Owner.ownerOf] at *
  have h1 : storageAt (writeSlot (readSlot (readSlot (readSlot (readSlot S message.currentTarget 0)
      message.currentTarget 1) message.currentTarget
      (mapSlot (bitwiseAnd ADDR_MASK (storageAt S message.currentTarget 0)) 2))
      message.currentTarget 0) message.currentTarget
      (mapSlot (bitwiseAnd ADDR_MASK (storageAt S message.currentTarget 0)) 2)
      (add (storageAt S message.currentTarget
        (mapSlot (bitwiseAnd ADDR_MASK (storageAt S message.currentTarget 0)) 2))
        (wordArg message.data 0))) message.currentTarget 1 = storageAt S message.currentTarget 1 := by
    rw [storageAt_writeSlot_of_ne (by acc) (Ne.symm (bal_ne_one F (mask_lt _)))]
    simp only [storageAt_readSlot]
  rw [sumBal_write_nb ?_ (nb1 F), sumBal_write_bal ?_ ?_ (mask_lt _),
    tot_write_one ?_, h1]
  simp only [sumBal_readSlot, storageAt_readSlot]
  rw [toNat_add hT, toNat_add hB]
  · simp only [tot] at *; omega
  all_goals first | with_reducible assumption | exact mask_lt _ | acc

/-- redeem(n) (`redeemState`): `_totalSupply -= n`, then `balances[owner] -= n`, with the two
`require`s of the code as hypotheses, as `redeem` states them. -/
theorem redeem_inv (F : FixedSep) {S : State.TransactionState} {message : Message fork}
    (hacc : hasAccount S message.currentTarget)
    (huo : UniqBal (Owner.ownerOf S message.currentTarget))
    (hT : (wordArg message.data 0).toNat ≤ (storageAt S message.currentTarget 1).toNat)
    (hB : (wordArg message.data 0).toNat ≤
      (storageAt S message.currentTarget (Issue.ownerBal S message.currentTarget)).toNat)
    (hI : Inv message.currentTarget S) : Inv message.currentTarget (IssueSpec.redeemState S message) := by
  unfold Inv at *
  simp only [IssueSpec.redeemState, IssueSpec.redeemState1, IssueSpec.reqState, Issue.ownerBal,
    Owner.ownerOf] at *
  rw [sumBal_write_bal ?_ ?_ (mask_lt _), sumBal_readSlot, sumBal_write_nb ?_
    (nb1 F), tot_write_ne ?_ (bal_ne_one F ?_), tot_readSlot,
    tot_write_one ?_, storageAt_readSlot, storageAt_writeSlot_of_ne ?_ (bal_ne_one F ?_)]
  simp only [sumBal_readSlot, storageAt_readSlot]
  rw [toNat_sub hT, toNat_sub hB]
  · simp only [tot] at *; omega
  all_goals first | with_reducible assumption | exact mask_lt _ | acc

/-- destroyBlackFunds(a), not deprecated (`destroyState`): `balances[a] := 0`, then
`_totalSupply := _totalSupply - d` UNCHECKED, `d` the old `balances[a]`. Under `Inv`, `d` is one
term of the sum, so `d ≤ _totalSupply` and the subtraction does not wrap: `Inv` holds after. -/
theorem destroy_inv (F : FixedSep) {S : State.TransactionState} {message : Message fork}
    (hacc : hasAccount S message.currentTarget) (hua : UniqBal (addrArg message.data 0))
    (hI : Inv message.currentTarget S) :
    Inv message.currentTarget (DestroySpec.destroyState S message) := by
  have hd : (DestroySpec.dirty S message).toNat ≤ (storageAt S message.currentTarget 1).toNat := by
    have hk := addrArg_lt message.data 0
    have hle := le_sumTo (f := bal message.currentTarget S) (fun i => Int.natCast_nonneg _)
      (a := (addrArg message.data 0).toNat) (2 ^ 160) hk
    unfold Inv sumBal at hI
    simp only [bal, ofNat_toNat] at hle
    simp only [DestroySpec.dirty, DestroySpec.balSlot, tot] at *
    omega
  unfold Inv at *
  simp only [DestroySpec.destroyState, DestroySpec.state1, DestroySpec.readState,
    DestroySpec.preState, DestroySpec.dirty, DestroySpec.balSlot, BlackList.listSlot] at *
  rw [sumBal_write_nb ?_ (nb1 F), sumBal_write_bal ?_ ?_
    (addrArg_lt _ _), tot_write_one ?_, storageAt_writeSlot_of_ne ?_ (Ne.symm (bal_ne_one F ?_))]
  simp only [sumBal_readSlot, storageAt_readSlot]
  rw [toNat_sub hd]
  · have z : (0 : U256).toNat = 0 := rfl
    simp only [tot, z] at *
    omega
  all_goals first | with_reducible assumption | exact addrArg_lt _ _ | acc

/-! ## Sequences of calls -/

/-- The changes of the state of the contract `C` made by the proved success paths (not
deprecated). A path's end state is reached from its start state by a few `Step`s: its reads
(`read`, `rd`), then its writes, each step with the no-wrap conditions that the path's
specification assumes (`hv`, `ht`, ...), and (round 29) the separation facts about the slots
that step writes (`NotBal`, `UniqBal`, each about one given slot). Read-only functions take only
`read` / `rd` steps. -/
inductive Step (C : Address) : State.TransactionState → State.TransactionState → Prop
  | read {S : State.TransactionState} (c : Address) (n : U256) : Step C S (readSlot S c n)
  | rd {S : State.TransactionState} (c : Address) (h : U256) (j : Nat) : Step C S (rdSt S c h j)
  /-- A write of slot 0, 3, 4 or 10 (pause, unpause, transferOwnership, setParams, deprecate). -/
  | fixedWrite {S : State.TransactionState} (hacc : hasAccount S C) (n : Nat)
      (hn : n = 0 ∨ n = 3 ∨ n = 4 ∨ n = 10) (v : U256) :
      Step C S (writeSlot S C (BitVec.ofNat 256 n) v)
  /-- A write of a slot of `isBlackListed` (addBlackList, removeBlackList). -/
  | listWrite {S : State.TransactionState} (hacc : hasAccount S C) (y v : U256)
      (hn : NotBal (mapSlot y 6)) (h1 : mapSlot y 6 ≠ 1) :
      Step C S (writeSlot S C (mapSlot y 6) v)
  /-- A write of a slot of `allowed` (approve). -/
  | allowWrite {S : State.TransactionState} (hacc : hasAccount S C) (y z v : U256)
      (hn : NotBal (mapSlot y (mapSlot z 5))) (h1 : mapSlot y (mapSlot z 5) ≠ 1) :
      Step C S (writeSlot S C (mapSlot y (mapSlot z 5)) v)
  | transferOk {fork : Fork} {S : State.TransactionState} (message : Message fork)
      (hC : message.currentTarget = C) (v a : U256) (hacc : hasAccount S C)
      (hus : UniqBal (callerKey message)) (hur : UniqBal (mkey a))
      (hv : v.toNat ≤ (balS S message).toNat)
      (ht : (balT S message v a).toNat + v.toNat < 2 ^ 256) : Step C S (credited S message v a)
  | transferFee {fork : Fork} {S : State.TransactionState} (message : Message fork)
      (hC : message.currentTarget = C) (v a : U256) (hacc : hasAccount S C)
      (hus : UniqBal (callerKey message)) (hur : UniqBal (mkey a))
      (huo : UniqBal (mkey (ownerKey (storageAt (creditedFee S message v a) C 0))))
      (hf : (feeOf S message v).toNat ≤ v.toNat) (hv : v.toNat ≤ (balS S message).toNat)
      (ht : (balT S message v a).toNat + (sendOf S message v).toNat < 2 ^ 256)
      (ho : (balO S message v a).toNat + (feeOf S message v).toNat < 2 ^ 256) :
      Step C S (feeState S message v a)
  | transferFromOk {fork : Fork} {S : State.TransactionState} (message : Message fork)
      (hC : message.currentTarget = C) (v t f : U256) (hacc : hasAccount S C)
      (hnA : NotBal (allowFrom message f)) (h1A : allowFrom message f ≠ 1)
      (huf : UniqBal (mkey f)) (hut : UniqBal (mkey t))
      (hv : v.toNat ≤ (balFrom S message v f).toNat)
      (ht : (balTo S message v t f).toNat + v.toNat < 2 ^ 256) :
      Step C S (creditedF S message v t f)
  | transferFromFee {fork : Fork} {S : State.TransactionState} (message : Message fork)
      (hC : message.currentTarget = C) (v t f : U256) (hacc : hasAccount S C)
      (hnA : NotBal (allowFrom message f)) (h1A : allowFrom message f ≠ 1)
      (huf : UniqBal (mkey f)) (hut : UniqBal (mkey t))
      (huo : UniqBal (mkey (ownerKey (storageAt (creditedFeeF S message v t f) C 0))))
      (hf : (feeOf S message v).toNat ≤ v.toNat)
      (hv : v.toNat ≤ (balFrom S message v f).toNat)
      (ht : (balTo S message v t f).toNat + (sendOf S message v).toNat < 2 ^ 256)
      (ho : (balOF S message v t f).toNat + (feeOf S message v).toNat < 2 ^ 256) :
      Step C S (feeStateF S message v t f)
  | issue {fork : Fork} {S : State.TransactionState} (message : Message fork)
      (hC : message.currentTarget = C) (hacc : hasAccount S C) (huo : UniqBal (Owner.ownerOf S C))
      (hT : (storageAt S C 1).toNat + (wordArg message.data 0).toNat < 2 ^ 256)
      (hB : (storageAt S C (Issue.ownerBal S C)).toNat + (wordArg message.data 0).toNat < 2 ^ 256) :
      Step C S (IssueSpec.issueState S message)
  | redeem {fork : Fork} {S : State.TransactionState} (message : Message fork)
      (hC : message.currentTarget = C) (hacc : hasAccount S C) (huo : UniqBal (Owner.ownerOf S C))
      (hT : (wordArg message.data 0).toNat ≤ (storageAt S C 1).toNat)
      (hB : (wordArg message.data 0).toNat ≤ (storageAt S C (Issue.ownerBal S C)).toNat) :
      Step C S (IssueSpec.redeemState S message)
  | destroy {fork : Fork} {S : State.TransactionState} (message : Message fork)
      (hC : message.currentTarget = C) (hacc : hasAccount S C)
      (hua : UniqBal (addrArg message.data 0)) :
      Step C S (DestroySpec.destroyState S message)

/-- Every step keeps the invariant. -/
theorem step_inv (F : FixedSep) {C : Address} {S S' : State.TransactionState} (h : Step C S S')
    (hI : Inv C S) : Inv C S' := by
  cases h with
  | read c n => exact (inv_readSlot c n).2 hI
  | rd c h j => exact (inv_rdSt j).2 hI
  | fixedWrite hacc n hn v =>
    have h1 : (BitVec.ofNat 256 n : U256) ≠ 1 := by
      rcases hn with rfl | rfl | rfl | rfl <;> decide
    exact (inv_write_nb hacc (nb_fixed F (by omega)) h1 v).2 hI
  | listWrite hacc y v hn h1 => exact (inv_write_nb hacc hn h1 v).2 hI
  | allowWrite hacc y z v hn h1 => exact (inv_write_nb hacc hn h1 v).2 hI
  | transferOk message hC v a hacc hus hur hv ht =>
    subst hC; exact transferOk_inv F hacc hus hur hv ht hI
  | transferFee message hC v a hacc hus hur huo hf hv ht ho =>
    subst hC; exact transferFee_inv F hacc hus hur huo hf hv ht ho hI
  | transferFromOk message hC v t f hacc hnA h1A huf hut hv ht =>
    subst hC; exact transferFromOk_inv F hacc hnA h1A huf hut hv ht hI
  | transferFromFee message hC v t f hacc hnA h1A huf hut huo hf hv ht ho =>
    subst hC; exact transferFromFee_inv F hacc hnA h1A huf hut huo hf hv ht ho hI
  | issue message hC hacc huo hT hB => subst hC; exact issue_inv F hacc huo hT hB hI
  | redeem message hC hacc huo hT hB => subst hC; exact redeem_inv F hacc huo hT hB hI
  | destroy message hC hacc hua => subst hC; exact destroy_inv F hacc hua hI

/-- A finite sequence of steps. -/
inductive Steps (C : Address) : State.TransactionState → State.TransactionState → Prop
  | refl (S : State.TransactionState) : Steps C S S
  | tail {S S' S'' : State.TransactionState} : Steps C S S' → Step C S' S'' → Steps C S S''

/-- The invariant holds after any finite sequence of steps from a state where it holds. -/
theorem steps_inv (F : FixedSep) {C : Address} {S S' : State.TransactionState}
    (h : Steps C S S') (hI : Inv C S) : Inv C S' := by
  induction h with
  | refl => exact hI
  | tail _ hs ih => exact step_inv F hs ih

theorem Steps.single {C : Address} {S S' : State.TransactionState} (h : Step C S S') :
    Steps C S S' := .tail (.refl S) h

theorem Steps.trans {C : Address} {S S' S'' : State.TransactionState} (h1 : Steps C S S')
    (h2 : Steps C S' S'') : Steps C S S'' := by
  induction h2 with
  | refl => exact h1
  | tail _ hs ih => exact .tail ih hs

/-! ## The end states of the success paths are reached by steps

For each success path that writes, its end state as its specification states it (over the start
state `state`) is reached from `state` by `Steps`, under that specification's hypotheses that the
steps need. With `steps_inv`, the invariant holds at the end of each of these paths when it holds
at the start. The read-only paths end in reads of `state` (`readSlot`, and `rdSt` for long
strings), single `Step.read` / `Step.rd` steps each. -/

section Keys

variable {fork : Fork} {S : State.TransactionState} {message : Message fork}

theorem SepOn.uniqCaller (K : SepOn (callKeys message S)) : UniqBal (callerKey message) := by
  have h : callerKey message = Owner.callerWord message := mask_mask _
  rw [h]; exact K.uniq _ (by simp [callKeys]) (mask_lt _)

theorem SepOn.uniqArg (K : SepOn (callKeys message S)) {i : Nat} (hi : i = 0 ∨ i = 1) :
    UniqBal (mkey (addrArg message.data i)) := by
  rw [mkey_addrArg]
  exact K.uniq _ (by rcases hi with rfl | rfl <;> simp [callKeys]) (addrArg_lt _ _)

theorem SepOn.uniqArg0 (K : SepOn (callKeys message S)) : UniqBal (addrArg message.data 0) := by
  have := K.uniqArg (i := 0) (.inl rfl); rwa [mkey_addrArg] at this

theorem SepOn.uniqOwner (K : SepOn (callKeys message S)) :
    UniqBal (Owner.ownerOf S message.currentTarget) :=
  K.uniq _ (by simp [callKeys]) (mask_lt _)

/-- The owner as the fee paths read it from slot 0 of a later state `X` with the same slot 0. -/
theorem SepOn.uniqOwnerAt (K : SepOn (callKeys message S)) {X : State.TransactionState}
    (hX : storageAt X message.currentTarget 0 = storageAt S message.currentTarget 0) :
    UniqBal (mkey (ownerKey (storageAt X message.currentTarget 0))) := by
  rw [Issue.mkey_owner, hX]; exact K.uniqOwner

theorem SepOn.listArg (K : SepOn (callKeys message S)) :
    NotBal (BlackList.listSlot (addrArg message.data 0)) ∧
      BlackList.listSlot (addrArg message.data 0) ≠ 1 := by
  simp only [BlackList.listSlot, mkey_addrArg]
  exact K.list _ (by simp [callKeys])

theorem SepOn.allowArg (K : SepOn (callKeys message S)) :
    NotBal (Approve.allowArg message) ∧ NotFixed (Approve.allowArg message) := by
  have h : mkey message.caller.toU256 = Owner.callerWord message := mask_mask _
  simp only [Approve.allowArg, Approve.allowSlot, mkey_addrArg, h]
  exact K.allow _ (by simp [callKeys]) _ (by simp [callKeys])

theorem SepOn.allowFromArg (K : SepOn (callKeys message S)) :
    NotBal (allowFrom message (fromArg message)) ∧ NotFixed (allowFrom message (fromArg message)) := by
  have h : mkey message.caller.toU256 = Owner.callerWord message := mask_mask _
  simp only [allowFrom, fromArg, mkey_addrArg, h]
  exact K.allow _ (by simp [callKeys]) _ (by simp [callKeys])

theorem storageAt_allowState_of_ne {X : State.TransactionState} {C : Address} {n A v m : U256}
    (hacc : hasAccount X C) (h : m ≠ n) : storageAt (allowState X C n A v) C m = storageAt X C m := by
  unfold allowState; split
  · rfl
  · exact storageAt_writeSlot_of_ne hacc h

/-- The transfer fee path writes two balance slots before it reads the owner: slot 0 is as at
the start. -/
theorem storageAt_creditedFee0 (F : FixedSep) (hacc : hasAccount S message.currentTarget)
    (v a : U256) : storageAt (creditedFee (shortState S message) message v a)
      message.currentTarget 0 = storageAt S message.currentTarget 0 := by
  simp only [creditedFee, debited, reads3, shortState, senderSlot, recipientSlot, callerKey, mkey]
  rw [storageAt_writeSlot_of_ne ?_ (Ne.symm (bal_ne_zero F (mask_lt _))), storageAt_readSlot,
    storageAt_writeSlot_of_ne ?_ (Ne.symm (bal_ne_zero F (mask_lt _)))]
  · simp only [storageAt_readSlot]
  all_goals acc

/-- The transferFrom fee path writes the allowance and two balance slots before it reads the
owner: slot 0 is as at the start. -/
theorem storageAt_creditedFeeF0 (F : FixedSep) (hacc : hasAccount S message.currentTarget)
    (hA : NotFixed (allowFrom message (fromArg message))) (v t : U256) :
    storageAt (creditedFeeF (checkState S message) message v t (fromArg message))
      message.currentTarget 0 = storageAt S message.currentTarget 0 := by
  have hA0 : (0 : U256) ≠ allowFrom message (fromArg message) := Ne.symm (hA 0 (by decide))
  simp only [creditedFeeF, debitedF, allowedF, readsF, checkState, recipientSlot, mkey] at *
  rw [storageAt_writeSlot_of_ne ?_ (Ne.symm (bal_ne_zero F (mask_lt _))), storageAt_readSlot,
    storageAt_writeSlot_of_ne ?_ (Ne.symm (bal_ne_zero F (mask_lt _))), storageAt_readSlot,
    storageAt_allowState_of_ne ?_ hA0]
  · simp only [storageAt_readSlot]
  all_goals accF

end Keys

section Reach

variable {fork : Fork} {state : State.TransactionState} {message : Message fork}

theorem reach_transfer_ok (K : SepOn (callKeys message state))
    (hacc : hasAccount state message.currentTarget)
    (hbal : (wordArg message.data 1).toNat ≤ (balS (shortState state message) message).toNat)
    (hto : (balT (shortState state message) message (wordArg message.data 1)
      (addrArg message.data 0)).toNat + (wordArg message.data 1).toNat < 2 ^ 256) :
    Steps message.currentTarget state (credited (shortState state message) message
      (wordArg message.data 1) (addrArg message.data 0)) :=
  .tail (.tail (.tail (.tail (.refl _) (.read _ _)) (.read _ _)) (.read _ _))
    (.transferOk message rfl _ _ (by acc) K.uniqCaller (K.uniqArg (.inl rfl)) hbal hto)

theorem reach_transfer_fee (K : SepOn (callKeys message state))
    (hacc : hasAccount state message.currentTarget)
    (hfv : (feeOf (shortState state message) message (wordArg message.data 1)).toNat ≤
      (wordArg message.data 1).toNat)
    (hbal : (wordArg message.data 1).toNat ≤ (balS (shortState state message) message).toNat)
    (hto : (balT (shortState state message) message (wordArg message.data 1)
      (addrArg message.data 0)).toNat +
      (sendOf (shortState state message) message (wordArg message.data 1)).toNat < 2 ^ 256)
    (hown : (balO (shortState state message) message (wordArg message.data 1)
      (addrArg message.data 0)).toNat +
      (feeOf (shortState state message) message (wordArg message.data 1)).toNat < 2 ^ 256) :
    Steps message.currentTarget state (feeState (shortState state message) message
      (wordArg message.data 1) (addrArg message.data 0)) :=
  .tail (.tail (.tail (.tail (.refl _) (.read _ _)) (.read _ _)) (.read _ _))
    (.transferFee message rfl _ _ (by acc) K.uniqCaller (K.uniqArg (.inl rfl))
      (K.uniqOwnerAt (storageAt_creditedFee0 K.fixed hacc _ _)) hfv hbal hto hown)

theorem reach_transferFrom_ok (K : SepOn (callKeys message state))
    (hacc : hasAccount state message.currentTarget)
    (hbal : (valArg message).toNat ≤
      (balFrom (checkState state message) message (valArg message) (fromArg message)).toNat)
    (hto : (balTo (checkState state message) message (valArg message) (toArg message)
      (fromArg message)).toNat + (valArg message).toNat < 2 ^ 256) :
    Steps message.currentTarget state (creditedF (checkState state message) message
      (valArg message) (toArg message) (fromArg message)) :=
  .tail (.tail (.tail (.tail (.refl _) (.read _ _)) (.read _ _)) (.read _ _))
    (.transferFromOk message rfl _ _ _ (by acc) K.allowFromArg.1 K.allowFromArg.2.ne_one
      (K.uniqArg (.inl rfl)) (K.uniqArg (.inr rfl)) hbal hto)

theorem reach_transferFrom_fee (K : SepOn (callKeys message state))
    (hacc : hasAccount state message.currentTarget)
    (hfv : (feeOf (checkState state message) message (valArg message)).toNat ≤
      (valArg message).toNat)
    (hbal : (valArg message).toNat ≤
      (balFrom (checkState state message) message (valArg message) (fromArg message)).toNat)
    (hto : (balTo (checkState state message) message (valArg message) (toArg message)
      (fromArg message)).toNat + (sendOf (checkState state message) message (valArg message)).toNat <
      2 ^ 256)
    (hown : (balOF (checkState state message) message (valArg message) (toArg message)
      (fromArg message)).toNat + (feeOf (checkState state message) message (valArg message)).toNat <
      2 ^ 256) :
    Steps message.currentTarget state (feeStateF (checkState state message) message
      (valArg message) (toArg message) (fromArg message)) :=
  .tail (.tail (.tail (.tail (.refl _) (.read _ _)) (.read _ _)) (.read _ _))
    (.transferFromFee message rfl _ _ _ (by acc) K.allowFromArg.1 K.allowFromArg.2.ne_one
      (K.uniqArg (.inl rfl)) (K.uniqArg (.inr rfl))
      (K.uniqOwnerAt (storageAt_creditedFeeF0 K.fixed hacc K.allowFromArg.2 _ _)) hfv hbal hto hown)

theorem reach_approve_zero (K : SepOn (callKeys message state))
    (hacc : hasAccount state message.currentTarget) :
    Steps message.currentTarget state (writeSlot (readSlot state message.currentTarget 10)
      message.currentTarget (Approve.allowArg message) 0) :=
  .tail (.tail (.refl _) (.read _ _))
    (.allowWrite (by acc) _ _ _ K.allowArg.1 K.allowArg.2.ne_one)

theorem reach_approve_set (K : SepOn (callKeys message state))
    (hacc : hasAccount state message.currentTarget) :
    Steps message.currentTarget state (writeSlot (readSlot (readSlot state message.currentTarget 10)
      message.currentTarget (Approve.allowArg message)) message.currentTarget
      (Approve.allowArg message) (wordArg message.data 1)) :=
  .tail (.tail (.tail (.refl _) (.read _ _)) (.read _ _))
    (.allowWrite (by acc) _ _ _ K.allowArg.1 K.allowArg.2.ne_one)

theorem reach_pause (hacc : hasAccount state message.currentTarget) (b : U256) :
    Steps message.currentTarget state (writeSlot state message.currentTarget 0
      (Pause.withPaused (storageAt state message.currentTarget 0) b)) :=
  .single (.fixedWrite hacc 0 (.inl rfl) _)

theorem reach_transferOwnership (hacc : hasAccount state message.currentTarget) :
    Steps message.currentTarget state (writeSlot state message.currentTarget 0
      (AddrWrite.withAddr (storageAt state message.currentTarget 0) (addrArg message.data 0))) :=
  .single (.fixedWrite hacc 0 (.inl rfl) _)

theorem reach_list (K : SepOn (callKeys message state))
    (hacc : hasAccount state message.currentTarget) (v : U256) :
    Steps message.currentTarget state (BlackListSpec.listState state message v) :=
  .tail (.tail (.refl _) (.read _ _)) (.listWrite (by acc) _ _ K.listArg.1 K.listArg.2)

theorem reach_setParams (hacc : hasAccount state message.currentTarget) :
    Steps message.currentTarget state (SetParamsSpec.paramsState state message) :=
  .tail (.tail (.tail (.tail (.tail (.tail (.refl _) (.read _ _))
    (.fixedWrite (by acc) 3 (.inr (.inl rfl)) _)) (.read _ _))
    (.fixedWrite (by acc) 4 (.inr (.inr (.inl rfl))) _)) (.read _ _)) (.read _ _)

theorem reach_deprecate (hacc : hasAccount state message.currentTarget) :
    Steps message.currentTarget state (AddrWriteSpec.depState state message) :=
  .tail (.tail (.tail (.refl _) (.read _ _)) (.fixedWrite (by acc) 10 (.inr (.inr (.inr rfl))) _))
    (.fixedWrite (by acc) 10 (.inr (.inr (.inr rfl))) _)

theorem reach_issue (K : SepOn (callKeys message state))
    (hacc : hasAccount state message.currentTarget)
    (hT : 0 < (wordArg message.data 0).toNat ∧
      (storageAt state message.currentTarget 1).toNat + (wordArg message.data 0).toNat < 2 ^ 256)
    (hB : (storageAt state message.currentTarget (Issue.ownerBal state message.currentTarget)).toNat +
        (wordArg message.data 0).toNat < 2 ^ 256) :
    Steps message.currentTarget state (IssueSpec.issueState state message) :=
  .single (.issue message rfl hacc K.uniqOwner hT.2 hB)

theorem reach_redeem (K : SepOn (callKeys message state))
    (hacc : hasAccount state message.currentTarget)
    (hT : (wordArg message.data 0).toNat ≤ (storageAt state message.currentTarget 1).toNat)
    (hB : (wordArg message.data 0).toNat ≤
      (storageAt state message.currentTarget (Issue.ownerBal state message.currentTarget)).toNat) :
    Steps message.currentTarget state (IssueSpec.redeemState state message) :=
  .single (.redeem message rfl hacc K.uniqOwner hT hB)

theorem reach_destroy (K : SepOn (callKeys message state))
    (hacc : hasAccount state message.currentTarget) :
    Steps message.currentTarget state (DestroySpec.destroyState state message) :=
  .single (.destroy message rfl hacc K.uniqArg0)

end Reach

/-- The invariant after a successful `transfer` with fee 0, as `transfer_ok` states its end:
`Inv` at the start (and `SepOn` of the call's keys) gives `Inv` at the end. The other paths
follow the same way from `reach_*` and `steps_inv`. -/
theorem transfer_ok_keeps {fork : Fork} {state : State.TransactionState}
    {message : Message fork} (K : SepOn (callKeys message state)) (hacc : hasAccount state message.currentTarget)
    (hbal : (wordArg message.data 1).toNat ≤ (balS (shortState state message) message).toNat)
    (hto : (balT (shortState state message) message (wordArg message.data 1)
      (addrArg message.data 0)).toNat + (wordArg message.data 1).toNat < 2 ^ 256)
    (hI : Inv message.currentTarget state) :
    Inv message.currentTarget (credited (shortState state message) message
      (wordArg message.data 1) (addrArg message.data 0)) :=
  steps_inv K.fixed (reach_transfer_ok K hacc hbal hto) hI

end UsdtVerify.Invariant
