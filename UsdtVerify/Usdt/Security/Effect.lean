import UsdtVerify.Usdt.Invariant.Seq
import UsdtVerify.Evm.Frame

/-!
# What a successful call does to the storage of the contract

`effect_call`: from Berlin (Glamsterdam included), a fresh frame of `CODE` at pc 0, static or
not, with any call data below 2^256 bytes, any value, any gas, any gas bound and any message
runner, when the contract is not deprecated (`hdep`) and slots 7 and 8 are of `StrForm` (`h7`,
`h8`, used by name() and symbol() only): every run that ends with no error ends in a state
described by one constructor of `Effect` (built from the completeness theorems `ok_X`):

- `same`: no slot of the contract changed (the 20 getters, name, symbol, and
  transferOwnership(0));
- `transferOk`, `transferFee`, `fromOk`, `fromFee`: the end state of transfer or transferFrom (fee
  0 or not), with the checks the run passed (not paused, the sender, or `_from`, not
  blacklisted; for transferFrom the allowance check) and the no-wrap facts;
- `approve`: only the slot `allowed[caller][spender]` may change;
- `ownerW`: a call by the owner (the low 160 bits of slot 0) that may change only slots 0, 3, 4,
  10 and slots of `isBlackListed` (pause, unpause, addBlackList, removeBlackList, setParams,
  deprecate, transferOwnership with a nonzero address);
- `issue`, `redeem`, `destroy`: by the owner, with the end state of the specification.

The slot classes: `BalSlot` (a slot of `balances`, `keccak(x ++ 2)` with `x < 2^160`),
`AllowSlot` (a slot of `allowed`), `ListSlot` (a slot of `isBlackListed`). `AllowSep` is the
keccak hypothesis (not proved) that the security theorems take beyond `KeccakSep`: a slot of
`allowed` is none of the slots 0..10 and no slot of `isBlackListed`.

`Seq C Q S S'`: a finite sequence of successful calls to `C` (each with a fresh frame of `CODE`,
as `effect_call` takes it, and meeting the predicate `Q` on its message and start state) and of
`Untouched` steps (any change that keeps every storage word of `C`). `seq_lift` lifts a reflexive
and transitive relation, with an invariant, from one step to the sequence.
-/

namespace UsdtVerify.Security

open EthLib.Base (Fork U256 Address)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open UsdtVerify.Gas
open Invariant Complete
open Transfer TransferOk TransferFee TransferFrom Owner Issue IssueSpec BlackList BlackListSpec
open SetParamsSpec AddrWriteSpec DestroySpec Pause AddrWrite Approve StringsGen

/-! ## Slot classes and the extra keccak hypothesis -/

/-- A slot of `balances`: `keccak(x ++ 2)` for an address word `x`. -/
def BalSlot (n : U256) : Prop := ∃ x : U256, x.toNat < 2 ^ 160 ∧ n = mapSlot x 2

/-- A slot of `allowed`: `keccak(y ++ keccak(z ++ 5))`. -/
def AllowSlot (n : U256) : Prop := ∃ y z : U256, n = mapSlot y (mapSlot z 5)

/-- A slot of `isBlackListed`: `keccak(y ++ 6)`. -/
def ListSlot (n : U256) : Prop := ∃ y : U256, n = mapSlot y 6

/-- The slots an owner function other than issue, redeem and destroyBlackFunds may write. -/
def OwnW (n : U256) : Prop := n = 0 ∨ n = 3 ∨ n = 4 ∨ n = 10 ∨ ListSlot n

/-- What the security theorems assume of keccak beyond `KeccakSep`, not proved. -/
structure AllowSep : Prop where
  /-- A slot of `allowed` is not one of the fixed slots 0..10. -/
  fixed : ∀ y z : U256, ∀ n : Nat, n < 11 → mapSlot y (mapSlot z 5) ≠ BitVec.ofNat 256 n
  /-- A slot of `allowed` is not a slot of `isBlackListed`. -/
  list : ∀ y z w : U256, mapSlot y (mapSlot z 5) ≠ mapSlot w 6

theorem bal_mk (x : U256) : BalSlot (mapSlot (bitwiseAnd ADDR_MASK x) 2) := ⟨_, mask_lt x, rfl⟩

theorem bal_arg (d : ByteArray) (i : Nat) : BalSlot (mapSlot (addrArg d i) 2) :=
  ⟨_, addrArg_lt d i, rfl⟩

theorem allow_mk (y z : U256) : AllowSlot (mapSlot y (mapSlot z 5)) := ⟨y, z, rfl⟩

theorem list_mk (y : U256) : ListSlot (mapSlot y 6) := ⟨y, rfl⟩

/-- A balance slot is no slot of `allowed`, of `isBlackListed`, nor slot 1. -/
theorem bal_not_allow (K : KeccakSep) {n : U256} (h : BalSlot n) : ¬ AllowSlot n := by
  rintro ⟨y, z, rfl⟩; obtain ⟨x, -, hx⟩ := h; exact K.allow x y z hx.symm

theorem bal_not_list (K : KeccakSep) {n : U256} (h : BalSlot n) : ¬ ListSlot n := by
  rintro ⟨y, rfl⟩; obtain ⟨x, -, hx⟩ := h; exact K.list x y hx.symm

theorem bal_not_fixed (K : KeccakSep) {n : U256} (h : BalSlot n) {m : Nat} (hm : m < 11) :
    n ≠ BitVec.ofNat 256 m := by
  obtain ⟨x, -, rfl⟩ := h; exact K.fixed x m hm

theorem bal_not_ownW (K : KeccakSep) {n : U256} (h : BalSlot n) : ¬ OwnW n := by
  rintro (e | e | e | e | hl)
  · exact bal_not_fixed K h (m := 0) (by decide) e
  · exact bal_not_fixed K h (m := 3) (by decide) e
  · exact bal_not_fixed K h (m := 4) (by decide) e
  · exact bal_not_fixed K h (m := 10) (by decide) e
  · exact bal_not_list K h hl

theorem allow_not_ownW (A : AllowSep) {n : U256} (h : AllowSlot n) : ¬ OwnW n := by
  obtain ⟨y, z, rfl⟩ := h
  rintro (e | e | e | e | ⟨w, e⟩)
  · exact A.fixed y z 0 (by decide) e
  · exact A.fixed y z 3 (by decide) e
  · exact A.fixed y z 4 (by decide) e
  · exact A.fixed y z 10 (by decide) e
  · exact A.list y z w e

theorem allow_ne_one (K : KeccakSep) {n : U256} (h : AllowSlot n) : n ≠ 1 := by
  obtain ⟨y, z, rfl⟩ := h; exact K.one_allow y z

theorem ownW_ne_one (K : KeccakSep) {n : U256} (h : OwnW n) : n ≠ 1 := by
  rcases h with rfl | rfl | rfl | rfl | ⟨y, rfl⟩
  · decide
  · decide
  · decide
  · decide
  · exact K.one_list y

/-! ## Chains of reads and writes -/

section Chain

variable {C : Address} {W : U256 → Prop} {S X : State.TransactionState}

theorem _root_.UsdtVerify.Writes.rd (h : Writes C W S X) (c : Address) (m : U256) : Writes C W S (readSlot X c m) :=
  h.trans (Writes.read c m)

theorem _root_.UsdtVerify.Writes.wr (h : Writes C W S X) (hacc : hasAccount X C) {m : U256} (hm : W m) (v : U256) :
    Writes C W S (writeSlot X C m v) :=
  h.trans (Writes.write hacc hm v)

theorem _root_.UsdtVerify.Writes.allow (h : Writes C W S X) (hacc : hasAccount X C) {n : U256} (hn : W n)
    (A v : U256) : Writes C W S (allowState X C n A v) := by
  unfold allowState; split
  · exact h
  · exact h.wr hacc hn _

theorem storageAt_rdSt (S : State.TransactionState) (c c' : Address) (h n : U256) :
    ∀ j, storageAt (rdSt S c h j) c' n = storageAt S c' n
  | 0 => rfl
  | j + 1 => by rw [rdSt, storageAt_readSlot, storageAt_rdSt S c c' h n j]

end Chain

/-- Builds a `Writes` chain over reads and writes, with the accounts and the slot classes. -/
macro "wchain" : tactic => `(tactic| repeat (first
  | with_reducible assumption
  | with_reducible exact Writes.refl _ _ _
  | with_reducible refine Writes.rd ?_ _ _
  | with_reducible refine Writes.wr ?_ ?_ ?_ _
  | with_reducible refine Writes.allow ?_ ?_ ?_ _ _
  | with_reducible apply hasAccount_readSlot
  | with_reducible apply hasAccount_writeSlot
  | with_reducible apply UsdtVerify.TransferFrom.hasAccount_allowState
  | with_reducible exact bal_mk _
  | with_reducible exact bal_arg _ _
  | with_reducible exact .inl (bal_mk _)
  | with_reducible exact .inr (allow_mk _ _)))

/-- `BalSlot` or `AllowSlot`. -/
abbrev BalOrAllow (n : U256) : Prop := BalSlot n ∨ AllowSlot n

/-- `BalSlot` or slot 1. -/
abbrev BalOrOne (n : U256) : Prop := BalSlot n ∨ n = 1

section States

variable {fork : Fork} {S : State.TransactionState} {message : Message fork}

theorem writes_credited (hacc : hasAccount S message.currentTarget) (v a : U256) :
    Writes message.currentTarget BalSlot S (credited (shortState S message) message v a) := by
  wchain

theorem writes_feeState (hacc : hasAccount S message.currentTarget) (v a : U256) :
    Writes message.currentTarget BalSlot S (feeState (shortState S message) message v a) := by
  wchain

theorem writes_debitedF (hacc : hasAccount S message.currentTarget) (v f : U256) :
    Writes message.currentTarget BalOrAllow S (debitedF (checkState S message) message v f) := by
  have h1 : Writes message.currentTarget BalOrAllow S (readsF (checkState S message) message f) := by
    wchain
  have h2 := h1.allow (by wchain) (n := allowFrom message f) (.inr (allow_mk _ _))
    (allowOf (checkState S message) message f) v
  exact (h2.rd _ _).wr (by wchain) (.inl (bal_mk _)) _

theorem hasAccount_debitedF (hacc : hasAccount S message.currentTarget) (v f : U256) :
    hasAccount (debitedF (checkState S message) message v f) message.currentTarget := by
  wchain

theorem writes_creditedF (hacc : hasAccount S message.currentTarget) (v t f : U256) :
    Writes message.currentTarget BalOrAllow S (creditedF (checkState S message) message v t f) := by
  have := writes_debitedF hacc v f
  have := hasAccount_debitedF hacc v f
  wchain

theorem writes_feeStateF (hacc : hasAccount S message.currentTarget) (v t f : U256) :
    Writes message.currentTarget BalOrAllow S (feeStateF (checkState S message) message v t f) := by
  have := writes_debitedF hacc v f
  have := hasAccount_debitedF hacc v f
  wchain

theorem writes_issue (hacc : hasAccount S message.currentTarget) :
    Writes message.currentTarget BalOrOne S (issueState S message) := by
  refine (Writes.wr ?_ ?_ (.inr rfl) _)
  · wchain
  · wchain

theorem writes_redeem (hacc : hasAccount S message.currentTarget) :
    Writes message.currentTarget BalOrOne S (redeemState S message) := by
  refine (Writes.wr (Writes.rd (Writes.wr ?_ ?_ (.inr rfl) _) _ _) ?_ (.inl (bal_mk _)) _)
  · wchain
  · wchain
  · wchain

theorem writes_destroy (hacc : hasAccount S message.currentTarget) :
    Writes message.currentTarget BalOrOne S (destroyState S message) := by
  refine (Writes.wr ?_ ?_ (.inr rfl) _)
  · refine Writes.wr ?_ ?_ (.inl (bal_arg _ _)) _
    · wchain
    · wchain
  · wchain

end States

/-! ## The effect of one successful call -/

/-- What a successful call (not deprecated) does to the storage of `C = message.currentTarget`,
from the start state `S` to the end state `S'`. -/
inductive Effect {fork : Fork} (message : Message fork) (S S' : State.TransactionState) : Prop
  /-- No slot of the contract changed. -/
  | same (h : ∀ n, storageAt S' message.currentTarget n = storageAt S message.currentTarget n)
  /-- transfer with fee 0. -/
  | transferOk (hsel : selector message.data = 0xa9059cbb)
      (hacc : hasAccount S message.currentTarget)
      (hpause : byte20 (storageAt S message.currentTarget 0) = 0)
      (hblack : (storageAt S message.currentTarget (blackSlot message)).toNat % 256 = 0)
      (hbal : (wordArg message.data 1).toNat ≤ (balS (shortState S message) message).toNat)
      (hto : (balT (shortState S message) message (wordArg message.data 1)
        (addrArg message.data 0)).toNat + (wordArg message.data 1).toNat < 2 ^ 256)
      (hst : S' = credited (shortState S message) message (wordArg message.data 1)
        (addrArg message.data 0))
  /-- transfer with a fee. -/
  | transferFee (hsel : selector message.data = 0xa9059cbb)
      (hacc : hasAccount S message.currentTarget)
      (hpause : byte20 (storageAt S message.currentTarget 0) = 0)
      (hblack : (storageAt S message.currentTarget (blackSlot message)).toNat % 256 = 0)
      (hfv : (feeOf (shortState S message) message (wordArg message.data 1)).toNat ≤
        (wordArg message.data 1).toNat)
      (hbal : (wordArg message.data 1).toNat ≤ (balS (shortState S message) message).toNat)
      (hto : (balT (shortState S message) message (wordArg message.data 1)
        (addrArg message.data 0)).toNat +
        (sendOf (shortState S message) message (wordArg message.data 1)).toNat < 2 ^ 256)
      (hown : (balO (shortState S message) message (wordArg message.data 1)
        (addrArg message.data 0)).toNat +
        (feeOf (shortState S message) message (wordArg message.data 1)).toNat < 2 ^ 256)
      (hst : S' = feeState (shortState S message) message (wordArg message.data 1)
        (addrArg message.data 0))
  /-- transferFrom with fee 0. -/
  | fromOk (hsel : selector message.data = 0x23b872dd)
      (hacc : hasAccount S message.currentTarget)
      (hpause : byte20 (storageAt S message.currentTarget 0) = 0)
      (hblack : (storageAt S message.currentTarget (blackFrom (fromArg message))).toNat % 256 = 0)
      (hallow : allowOf (checkState S message) message (fromArg message) = MAX_UINT ∨
        (valArg message).toNat ≤ (allowOf (checkState S message) message (fromArg message)).toNat)
      (hbal : (valArg message).toNat ≤
        (balFrom (checkState S message) message (valArg message) (fromArg message)).toNat)
      (hto : (balTo (checkState S message) message (valArg message) (toArg message)
        (fromArg message)).toNat + (valArg message).toNat < 2 ^ 256)
      (hst : S' = creditedF (checkState S message) message (valArg message) (toArg message)
        (fromArg message))
  /-- transferFrom with a fee. -/
  | fromFee (hsel : selector message.data = 0x23b872dd)
      (hacc : hasAccount S message.currentTarget)
      (hpause : byte20 (storageAt S message.currentTarget 0) = 0)
      (hblack : (storageAt S message.currentTarget (blackFrom (fromArg message))).toNat % 256 = 0)
      (hallow : allowOf (checkState S message) message (fromArg message) = MAX_UINT ∨
        (valArg message).toNat ≤ (allowOf (checkState S message) message (fromArg message)).toNat)
      (hfv : (feeOf (checkState S message) message (valArg message)).toNat ≤
        (valArg message).toNat)
      (hbal : (valArg message).toNat ≤
        (balFrom (checkState S message) message (valArg message) (fromArg message)).toNat)
      (hto : (balTo (checkState S message) message (valArg message) (toArg message)
        (fromArg message)).toNat +
        (sendOf (checkState S message) message (valArg message)).toNat < 2 ^ 256)
      (hown : (balOF (checkState S message) message (valArg message) (toArg message)
        (fromArg message)).toNat +
        (feeOf (checkState S message) message (valArg message)).toNat < 2 ^ 256)
      (hst : S' = feeStateF (checkState S message) message (valArg message) (toArg message)
        (fromArg message))
  /-- approve: only `allowed[caller][spender]` may change. -/
  | approve (hsel : selector message.data = 0x095ea7b3)
      (hw : Writes message.currentTarget (· = allowArg message) S S')
  /-- An owner function that writes only slots 0, 3, 4, 10 and slots of `isBlackListed`. -/
  | ownerW (howner : callerWord message = ownerOf S message.currentTarget)
      (hw : Writes message.currentTarget OwnW S S')
  /-- issue(v). -/
  | issue (hsel : selector message.data = 0xcc872b66)
      (howner : callerWord message = ownerOf S message.currentTarget)
      (hacc : hasAccount S message.currentTarget)
      (hT : (storageAt S message.currentTarget 1).toNat + (wordArg message.data 0).toNat < 2 ^ 256)
      (hB : (storageAt S message.currentTarget (ownerBal S message.currentTarget)).toNat +
        (wordArg message.data 0).toNat < 2 ^ 256)
      (hst : S' = issueState S message)
  /-- redeem(v). -/
  | redeem (hsel : selector message.data = 0xdb006a75)
      (howner : callerWord message = ownerOf S message.currentTarget)
      (hacc : hasAccount S message.currentTarget)
      (hT : (wordArg message.data 0).toNat ≤ (storageAt S message.currentTarget 1).toNat)
      (hB : (wordArg message.data 0).toNat ≤
        (storageAt S message.currentTarget (ownerBal S message.currentTarget)).toNat)
      (hst : S' = redeemState S message)
  /-- destroyBlackFunds(a), `a` blacklisted. -/
  | destroy (hsel : selector message.data = 0xf3bdc228)
      (howner : callerWord message = ownerOf S message.currentTarget)
      (hacc : hasAccount S message.currentTarget)
      (hlisted : (storageAt S message.currentTarget (listSlot (addrArg message.data 0))).toNat %
        256 ≠ 0)
      (hst : S' = destroyState S message)

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate} {bound : Nat} {runChild : MessageRunner fork Nat bound}
  {evm s : Evm fork Nat} {gas : Nat}

/-- The getters: the end state only records reads. -/
theorem same_reads {S' : State.TransactionState}
    (h : ∀ n, storageAt S' message.currentTarget n = storageAt state message.currentTarget n) :
    Effect message state S' := .same h

/-- **The effect of every successful call** (not deprecated): from Berlin (Glamsterdam included),
a fresh frame of `CODE` at pc 0, static or not, any call data below 2^256 bytes, any value, any
gas, any gas bound and any message runner, slots 7 and 8 of `StrForm`. -/
theorem effect_call (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    (h7 : StrForm (storageAt state message.currentTarget 7))
    (h8 : StrForm (storageAt state message.currentTarget 8))
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) : Effect message state s.state := by
  obtain ⟨-, -, i, hi⟩ := runFrame_ok_dispatch hfork hsize' start within hrun hok
  have rd : ∀ {X : State.TransactionState}, s.state = X →
      (∀ n, storageAt X message.currentTarget n = storageAt state message.currentTarget n) →
      Effect message state s.state := fun hst h => .same (fun n => by rw [hst]; exact h n)
  match i, hi with
  | ⟨0, _⟩, hi =>
    rcases ok_name hfork hsize' (hi.trans rfl) h7 start within hrun hok with
      ⟨-, -, -, hst, -⟩ | ⟨-, -, -, -, -, -, hst, -⟩ | ⟨-, -, -, -, hst, -⟩ <;>
    exact rd hst (fun n => by simp only [storageAt_readSlot, storageAt_rdSt])
  | ⟨1, _⟩, hi =>
    obtain ⟨-, hacc, howner, -, -, hst, -⟩ := ok_deprecate hfork hsize' (hi.trans rfl) rfl rfl
      start within hrun hok
    refine .ownerW howner ?_
    rw [hst]
    refine Writes.wr (Writes.wr (Writes.read _ _) ?_ (.inr (.inr (.inr (.inl rfl)))) _) ?_
      (.inr (.inr (.inr (.inl rfl)))) _
    · wchain
    · wchain
  | ⟨2, _⟩, hi =>
    obtain ⟨-, hacc, -, -, h⟩ := ok_approve hfork hsize' (hi.trans rfl) hdep rfl rfl start within
      hrun hok
    refine .approve (hi.trans rfl) ?_
    rcases h with ⟨-, -, hst, -⟩ | ⟨-, -, -, hst, -⟩ <;> rw [hst]
    · exact Writes.wr (W := (· = allowArg message)) (Writes.read _ _) (hasAccount_readSlot hacc)
        rfl _
    · exact Writes.wr (W := (· = allowArg message)) ((Writes.read _ _).rd _ _)
        (hasAccount_readSlot (hasAccount_readSlot hacc)) rfl _
  | ⟨3, _⟩, hi =>
    obtain ⟨-, -, hst, -⟩ := ok_deprecated hfork hsize' (hi.trans rfl) start within hrun hok
    exact rd hst (fun n => by simp only [storageAt_readSlot])
  | ⟨4, _⟩, hi =>
    obtain ⟨-, hacc, howner, -, -, hst, -⟩ := ok_addBlackList hfork hsize' (hi.trans rfl) rfl rfl
      start within hrun hok
    refine .ownerW howner ?_
    rw [hst]
    exact Writes.wr (Writes.read _ _) (hasAccount_readSlot hacc)
      (.inr (.inr (.inr (.inr (list_mk _))))) _
  | ⟨5, _⟩, hi =>
    obtain ⟨-, -, hst, -⟩ := ok_totalSupply hfork hsize' (hi.trans rfl) hdep start within hrun hok
    exact rd hst (fun n => by simp only [storageAt_readSlot])
  | ⟨6, _⟩, hi =>
    obtain ⟨-, hacc, -, hpause, hblack, -, hallow, hfv, hbal, hto, -, h⟩ := ok_transferFrom hfork
      hsize' (hi.trans rfl) hdep rfl rfl rfl rfl rfl rfl rfl rfl rfl start within hrun hok
    rcases h with ⟨hfee, -, hst, -⟩ | ⟨-, hown, -, hst, -⟩
    · rw [sendOf_zero hfee] at hto
      exact .fromOk (hi.trans rfl) hacc hpause hblack hallow hbal hto hst
    · exact .fromFee (hi.trans rfl) hacc hpause hblack hallow hfv hbal hto hown hst
  | ⟨7, _⟩, hi =>
    obtain ⟨-, -, hst, -⟩ := ok_upgradedAddress hfork hsize' (hi.trans rfl) start within hrun hok
    exact rd hst (fun n => by simp only [storageAt_readSlot])
  | ⟨8, _⟩, hi =>
    obtain ⟨-, -, hst, -⟩ := ok_balances hfork hsize' (hi.trans rfl) start within hrun hok
    exact rd hst (fun n => by simp only [storageAt_readSlot])
  | ⟨9, _⟩, hi =>
    obtain ⟨-, -, hst, -⟩ := ok_decimals hfork hsize' (hi.trans rfl) start within hrun hok
    exact rd hst (fun n => by simp only [storageAt_readSlot])
  | ⟨10, _⟩, hi =>
    obtain ⟨-, -, hst, -⟩ := ok_maximumFee hfork hsize' (hi.trans rfl) start within hrun hok
    exact rd hst (fun n => by simp only [storageAt_readSlot])
  | ⟨11, _⟩, hi =>
    obtain ⟨-, -, hst, -⟩ := ok_totalSupplyVar hfork hsize' (hi.trans rfl) start within hrun hok
    exact rd hst (fun n => by simp only [storageAt_readSlot])
  | ⟨12, _⟩, hi =>
    obtain ⟨-, hacc, howner, -, -, -, hst, -⟩ := ok_unpause hfork hsize' (hi.trans rfl) rfl start
      within hrun hok
    rw [hst]
    exact .ownerW howner (Writes.write hacc (.inl rfl) _)
  | ⟨13, _⟩, hi =>
    obtain ⟨-, -, hst, -⟩ := ok_getBlackListStatus hfork hsize' (hi.trans rfl) start within hrun hok
    exact rd hst (fun n => by simp only [storageAt_readSlot])
  | ⟨14, _⟩, hi =>
    obtain ⟨-, -, hst, -⟩ := ok_allowed hfork hsize' (hi.trans rfl) start within hrun hok
    exact rd hst (fun n => by simp only [storageAt_readSlot])
  | ⟨15, _⟩, hi =>
    obtain ⟨-, -, hst, -⟩ := ok_paused hfork hsize' (hi.trans rfl) start within hrun hok
    exact rd hst (fun n => by simp only [storageAt_readSlot])
  | ⟨16, _⟩, hi =>
    obtain ⟨-, -, hst, -⟩ := ok_balanceOf hfork hsize' (hi.trans rfl) hdep start within hrun hok
    exact rd hst (fun n => by simp only [storageAt_readSlot])
  | ⟨17, _⟩, hi =>
    obtain ⟨-, hacc, howner, -, -, -, hst, -⟩ := ok_pause hfork hsize' (hi.trans rfl) rfl start
      within hrun hok
    rw [hst]
    exact .ownerW howner (Writes.write hacc (.inl rfl) _)
  | ⟨18, _⟩, hi =>
    obtain ⟨-, -, hst, -⟩ := ok_getOwner hfork hsize' (hi.trans rfl) start within hrun hok
    exact rd hst (fun n => by simp only [storageAt_readSlot])
  | ⟨19, _⟩, hi =>
    obtain ⟨-, -, hst, -⟩ := ok_owner hfork hsize' (hi.trans rfl) start within hrun hok
    exact rd hst (fun n => by simp only [storageAt_readSlot])
  | ⟨20, _⟩, hi =>
    rcases ok_symbol hfork hsize' (hi.trans rfl) h8 start within hrun hok with
      ⟨-, -, -, hst, -⟩ | ⟨-, -, -, -, -, -, hst, -⟩ | ⟨-, -, -, -, hst, -⟩ <;>
    exact rd hst (fun n => by simp only [storageAt_readSlot, storageAt_rdSt])
  | ⟨21, _⟩, hi =>
    obtain ⟨-, hacc, -, hpause, hblack, -, hfv, hbal, hto, -, h⟩ := ok_transfer hfork hsize'
      (hi.trans rfl) hdep rfl rfl rfl rfl rfl rfl rfl rfl start within hrun hok
    rcases h with ⟨hfee, -, hst, -⟩ | ⟨-, hown, -, hst, -⟩
    · rw [sendOf_zero hfee] at hto
      exact .transferOk (hi.trans rfl) hacc hpause hblack hbal hto hst
    · exact .transferFee (hi.trans rfl) hacc hpause hblack hfv hbal hto hown hst
  | ⟨22, _⟩, hi =>
    obtain ⟨-, hacc, howner, -, -, -, -, -, hst, -⟩ := ok_setParams hfork hsize' (hi.trans rfl)
      rfl rfl rfl rfl start within hrun hok
    refine .ownerW howner ?_
    rw [hst]
    refine ((Writes.wr ((Writes.wr (Writes.read _ _) ?_ (.inr (.inl rfl)) _).rd _ _) ?_
      (.inr (.inr (.inl rfl))) _).rd _ _).rd _ _
    · wchain
    · wchain
  | ⟨23, _⟩, hi =>
    obtain ⟨-, hacc, howner, -, hT, hB, -, -, hst, -⟩ := ok_issue hfork hsize' (hi.trans rfl) rfl
      rfl rfl start within hrun hok
    exact .issue (hi.trans rfl) howner hacc hT hB hst
  | ⟨24, _⟩, hi =>
    obtain ⟨-, hacc, howner, hT, hB, -, -, hst, -⟩ := ok_redeem hfork hsize' (hi.trans rfl) rfl
      rfl rfl start within hrun hok
    exact .redeem (hi.trans rfl) howner hacc hT hB hst
  | ⟨25, _⟩, hi =>
    obtain ⟨-, -, hst, -⟩ := ok_allowance hfork hsize' (hi.trans rfl) hdep start within hrun hok
    exact rd hst (fun n => by simp only [storageAt_readSlot])
  | ⟨26, _⟩, hi =>
    obtain ⟨-, -, hst, -⟩ := ok_basisPointsRate hfork hsize' (hi.trans rfl) start within hrun hok
    exact rd hst (fun n => by simp only [storageAt_readSlot])
  | ⟨27, _⟩, hi =>
    obtain ⟨-, -, hst, -⟩ := ok_isBlackListed hfork hsize' (hi.trans rfl) start within hrun hok
    exact rd hst (fun n => by simp only [storageAt_readSlot])
  | ⟨28, _⟩, hi =>
    obtain ⟨-, hacc, howner, -, -, hst, -⟩ := ok_removeBlackList hfork hsize' (hi.trans rfl) rfl
      rfl start within hrun hok
    refine .ownerW howner ?_
    rw [hst]
    exact Writes.wr (Writes.read _ _) (hasAccount_readSlot hacc)
      (.inr (.inr (.inr (.inr (list_mk _))))) _
  | ⟨29, _⟩, hi =>
    obtain ⟨-, -, hst, -⟩ := ok_maxUint hfork hsize' (hi.trans rfl) start within hrun hok
    exact rd hst (fun _ => rfl)
  | ⟨30, _⟩, hi =>
    obtain ⟨howner, -, h⟩ := ok_transferOwnership hfork hsize' (hi.trans rfl) rfl start within
      hrun hok
    rcases h with ⟨-, -, hst, -⟩ | ⟨-, -, hacc, -, hst, -⟩
    · exact rd hst (fun n => by simp only [storageAt_readSlot])
    · rw [hst]
      exact .ownerW howner (Writes.write hacc (.inl rfl) _)
  | ⟨31, _⟩, hi =>
    obtain ⟨-, hacc, howner, hlisted, -, -, hst, -⟩ := ok_destroyBlackFunds hfork hsize'
      (hi.trans rfl) hdep rfl rfl rfl rfl rfl start within hrun hok
    exact .destroy (hi.trans rfl) howner hacc hlisted hst
  | ⟨n + 32, h⟩, _ => exact absurd h (by omega)

/-! ## Sequences of calls -/

/-- One successful run of `CODE` for a message to `C`, from `S` to `S'`, with the hypotheses
`effect_call` takes beyond "not deprecated" and the string slots. -/
def RunOk (C : Address) (S S' : State.TransactionState) {fork : Fork} (message : Message fork) :
    Prop :=
  ∃ (substate : Substate) (gas bound : Nat) (runChild : MessageRunner fork Nat bound)
    (evm s : Evm fork Nat) (within : GasMeter.gasHeld evm.gas ≤ bound),
    message.currentTarget = C ∧ .berlin ≤ fork ∧ message.data.size < 2 ^ 256 ∧
    At CODE message 0 [] .empty gas S substate evm ∧
    Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s ∧
    s.error = none ∧ S' = s.state

/-- `effect_call` for a `RunOk` step. -/
theorem RunOk.effect {C : Address} {S S' : State.TransactionState} (h : RunOk C S S' message)
    (hdep : byte20 (storageAt S C 10) = 0) (h7 : StrForm (storageAt S C 7))
    (h8 : StrForm (storageAt S C 8)) : message.currentTarget = C ∧ Effect message S S' := by
  obtain ⟨substate, gas, bound, runChild, evm, s, within, hC, hfork, hsize, start, hrun, hok, rfl⟩ :=
    h
  subst hC
  exact ⟨rfl, effect_call hfork hsize hdep h7 h8 start within hrun hok⟩

/-- A finite sequence of successful calls to `C`, each meeting `Q` on its message and its start
state, and of changes that keep every storage word of `C`. -/
inductive Seq (C : Address) (Q : ∀ {fork : Fork}, Message fork → State.TransactionState → Prop) :
    State.TransactionState → State.TransactionState → Prop
  | nil (S : State.TransactionState) : Seq C Q S S
  | call {S S' S'' : State.TransactionState} {fork : Fork} {message : Message fork} :
      RunOk C S S' message → Q message S → Seq C Q S' S'' → Seq C Q S S''
  | other {S S' S'' : State.TransactionState} : Untouched C S S' → Seq C Q S' S'' →
      Seq C Q S S''

/-- Lifts a reflexive and transitive relation `R`, with an invariant `I`, from each step to a
sequence: if every `Untouched` step and every call of the sequence from a state of `I` is an
`R` step to a state of `I`, then so is the whole sequence. -/
theorem seq_lift {C : Address} {Q : ∀ {fork : Fork}, Message fork → State.TransactionState → Prop}
    {I : State.TransactionState → Prop} {R : State.TransactionState → State.TransactionState → Prop}
    (hrefl : ∀ S, R S S) (htrans : ∀ {S S' S''}, R S S' → R S' S'' → R S S'')
    (hother : ∀ {S S'}, Untouched C S S' → I S → R S S' ∧ I S')
    (hcall : ∀ {S S'} {fork : Fork} {message : Message fork}, RunOk C S S' message →
      Q message S → I S → R S S' ∧ I S')
    {S S' : State.TransactionState} (h : Seq C Q S S') (hI : I S) : R S S' := by
  induction h with
  | nil S => exact hrefl S
  | call hr hq _ ih =>
    obtain ⟨hR, hI'⟩ := hcall hr hq hI
    exact htrans hR (ih hI')
  | other hu _ ih =>
    obtain ⟨hR, hI'⟩ := hother hu hI
    exact htrans hR (ih hI')

end UsdtVerify.Security
