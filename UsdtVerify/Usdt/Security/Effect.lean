import UsdtVerify.Usdt.Invariant.Seq
import UsdtVerify.Evm.Frame
import UsdtVerify.Evm.Route
import UsdtVerify.Evm.Shadow

/-!
# What a successful call does to the storage of the contract

`effect_call`: from Berlin (Glamsterdam included), a fresh frame of `CODE` at pc 0, static or
not, with any call data below 2^256 bytes, any value, any gas, any gas bound and any message
runner, when the contract is not deprecated (`hdep`) and slots 7 and 8 are of `StrForm` (`h7`,
`h8`, used by name() and symbol() only): every run that ends with no error ends in a state
described by one constructor of `Effect` (built from the completeness theorems `ok_X`):

- `same`: no slot of the contract changed (the 17 getters, name, symbol, and
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
`AllowSlot` (a slot of `allowed`), `ListSlot` (a slot of `isBlackListed` of an address word).
`SecSep A` (round 29) is the keccak hypothesis (not proved) of the security theorems, for the
finitely many slots keyed by the words of `A` (in the theorems, `callKeys message state`):
`SepOn A`, and the balance and allowance slots keyed by `A` are no slot of `isBlackListed`.
`KeyBA A`: the balance and allowance slots keyed by `A`, the slots that the writes of transfer,
transferFrom and approve fall in (`writes_*K`). Through round 28 the theorems assumed the global
`KeccakSep` and `AllowSep` instead (almost certainly false, docs/AUDIT.md finding 1); they imply
`SecSep A` for every `A` (`sepOn_of_global`).

Deprecated or not (round 23): `effect_local` is `effect_call` with `hdep` replaced by "not
deprecated, or a function other than the seven of `FlagFn`" (the six that forward when deprecated,
`FwdFn`, and destroyBlackFunds). `effect_all` (no `hdep`, no runner assumption): every successful
run ends in a state described by one constructor of `EffectD`: `loc` (an `Effect`), `fwd` (one of
the six forwarding functions, deprecated: the end state is the end state of the child of one call
from `C` to the upgraded address, sent from a state with the start storage of `C`; for transfer
and transferFrom, with the pause and blacklist checks the code makes before the call) or `dfwd`
(deprecated destroyBlackFunds by the owner, `a` blacklisted: the same call, then the two writes
`tailState` over the child's end state, with some word `d`). `effect_all` takes `StrForm` of
slots 7 and 8 (`h7`, `h8`). `FwdAt` (Evm/Route.lean) and EthLib's `KeepsOn` over its `SentVia` (a
runner assumption on the calls the code actually makes, round 29; EthLib's since round 49).

`Seq C Q S S'`: a finite sequence of successful calls to `C` (each with a fresh frame of `CODE`,
as `effect_call` takes it, and meeting the predicate `Q` on its message and start state) and of
`Untouched` steps (any change that keeps every storage word of `C`). `seq_lift` lifts a reflexive
and transitive relation, with an invariant, from one step to the sequence. `SeqR C R Q` and
`seqR_lift`: the same with steps `RunOkR C R`, deprecated or not, whose runner meets
`KeepsOn … (SentVia …) R` when `C` is deprecated at the step's start state.

Over the EIP-8037 meter (round 37): `effect_localE` is `effect_local` for a loop that ends
(`Gas.Ends`). `ends_any`: a run of the loop over `StateGasMeter` that ends with no error, at any
reservoir, refills allowed, gives such a loop of the meter `Nat` that ends in the same state
(`Shadow.shadow_ends`). `effect_local_any`, `effect_any`: `effect_local`, `effect_call` over
`StateGasMeter`. `SeqS C Q`: a sequence whose calls run over `Nat` (`RunOk`) or over
`StateGasMeter` (`RunOkS`); `seqS_lift`; `Seq.toS`.
-/

namespace UsdtVerify.Security

open EthLib.Base (Fork U256 Address)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open UsdtVerify.Gas
open Invariant Complete
open Transfer TransferOk TransferFee TransferFrom Owner Issue IssueSpec BlackList BlackListSpec
open SetParamsSpec AddrWriteSpec DestroySpec Pause AddrWrite Approve StringsGen Deprecated

/-! ## Slot classes and the keccak hypothesis of the security theorems -/

/-- A slot of `balances`: `keccak(x ++ 2)` for an address word `x`. -/
def BalSlot (n : U256) : Prop := ∃ x : U256, x.toNat < 2 ^ 160 ∧ n = mapSlot x 2

/-- A slot of `allowed`: `keccak(y ++ keccak(z ++ 5))`. -/
def AllowSlot (n : U256) : Prop := ∃ y z : U256, n = mapSlot y (mapSlot z 5)

/-- A slot of `isBlackListed` of an address word: `keccak(y ++ 6)`, `y < 2^160` (round 29; through
round 28 any word `y`). The code only uses address words as keys. -/
def ListSlot (n : U256) : Prop := ∃ y : U256, y.toNat < 2 ^ 160 ∧ n = mapSlot y 6

/-- The slots an owner function other than issue, redeem and destroyBlackFunds may write: slots
0, 3, 4, 10 and the slot of `isBlackListed` of the first address argument (round 29; through
round 28 any slot of `isBlackListed`). -/
def OwnW {fork : Fork} (message : Message fork) (n : U256) : Prop :=
  n = 0 ∨ n = 3 ∨ n = 4 ∨ n = 10 ∨ n = listSlot (addrArg message.data 0)

/-- No address word has `n` as its slot of `isBlackListed`. -/
def NotList (n : U256) : Prop := ∀ y : U256, y.toNat < 2 ^ 160 → n ≠ mapSlot y 6

/-- The keccak hypothesis of the security theorems (round 29), for the slots keyed by the words
of `A`: `SepOn A`, and moreover the balance slot of an address word of `A` and a slot of
`allowed` keyed by two words of `A` are no slot of `isBlackListed` of an address word. Finitely
many facts, each about one given slot against 2^160 others; not proved. -/
structure SecSep (A : List U256) : Prop extends SepOn A where
  balList : ∀ x ∈ A, x.toNat < 2 ^ 160 → NotList (mapSlot x 2)
  allowList : ∀ y ∈ A, ∀ z ∈ A, NotList (mapSlot y (mapSlot z 5))

theorem SecSep.mono {A B : List U256} (h : SecSep B) (hAB : ∀ x ∈ A, x ∈ B) : SecSep A :=
  ⟨h.toSepOn.mono hAB, fun x hx => h.balList x (hAB x hx),
    fun y hy z hz => h.allowList y (hAB y hy) z (hAB z hz)⟩

/-- Through round 28: what the security theorems assumed of keccak beyond `KeccakSep`, for all
keys at once. Almost certainly false (docs/AUDIT.md, finding 1); kept only for
`sepOn_of_global`. -/
structure AllowSep : Prop where
  /-- A slot of `allowed` is not one of the fixed slots 0..10. -/
  fixed : ∀ y z : U256, ∀ n : Nat, n < 11 → mapSlot y (mapSlot z 5) ≠ BitVec.ofNat 256 n
  /-- A slot of `allowed` is not a slot of `isBlackListed`. -/
  list : ∀ y z w : U256, mapSlot y (mapSlot z 5) ≠ mapSlot w 6

/-- The global hypotheses of rounds up to 28 give the local ones for every list of keys, so every
theorem stated with `SepOn` or `SecSep` implies its older form. -/
theorem sepOn_of_global (K : KeccakSep) (A' : AllowSep) (A : List U256) : SecSep A where
  fixed n hn x _ e := K.fixed x n hn e.symm
  uniq x _ hx y hy e := K.inj y x hy hx e
  list y _ := ⟨fun x _ e => K.list x y e.symm, K.one_list y⟩
  allow y _ z _ := ⟨fun x _ e => K.allow x y z e.symm, fun k hk => A'.fixed y z k hk⟩
  balList x _ _ y _ := K.list x y
  allowList y _ z _ w _ := A'.list y z w

theorem bal_mk (x : U256) : BalSlot (mapSlot (bitwiseAnd ADDR_MASK x) 2) := ⟨_, mask_lt x, rfl⟩

theorem bal_arg (d : ByteArray) (i : Nat) : BalSlot (mapSlot (addrArg d i) 2) :=
  ⟨_, addrArg_lt d i, rfl⟩

theorem allow_mk (y z : U256) : AllowSlot (mapSlot y (mapSlot z 5)) := ⟨y, z, rfl⟩

section Local

variable {fork : Fork} {S : State.TransactionState} {message : Message fork}

/-- A slot that an owner function writes is no balance slot. -/
theorem ownW_notBal (K : SepOn (callKeys message S)) {n : U256} (h : OwnW message n) :
    NotBal n := by
  rcases h with rfl | rfl | rfl | rfl | rfl
  · exact K.fixed 0 (by decide)
  · exact K.fixed 3 (by decide)
  · exact K.fixed 4 (by decide)
  · exact K.fixed 10 (by decide)
  · exact K.listArg.1

theorem ownW_ne_one (K : SepOn (callKeys message S)) {n : U256} (h : OwnW message n) : n ≠ 1 := by
  rcases h with rfl | rfl | rfl | rfl | rfl
  · decide
  · decide
  · decide
  · decide
  · exact K.listArg.2

/-- A slot that is no fixed slot and no slot of `isBlackListed` is no slot an owner function
writes. -/
theorem not_ownW {n : U256} (hf : NotFixed n) (hl : NotList n) : ¬ OwnW message n := by
  rintro (e | e | e | e | e)
  · exact hf 0 (by decide) e
  · exact hf 3 (by decide) e
  · exact hf 4 (by decide) e
  · exact hf 10 (by decide) e
  · rw [e] at hl
    simp only [listSlot, mkey_addrArg] at hl
    exact hl _ (addrArg_lt _ _) rfl

end Local

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

/-! ## The slots written, keyed by the call's words (round 29)

`KeyBA A n`: `n` is the balance slot of an address word of `A`, or the slot of `allowed` keyed by
two words of `A`. The writes of transfer, transferFrom and approve are of this class for
`A = callKeys message S`; with `SecSep A` none of them is a protected slot. -/

/-- The balance slot of an address word of `A`, or a slot of `allowed` keyed by two words of
`A`. -/
def KeyBA (A : List U256) (n : U256) : Prop :=
  (∃ x ∈ A, x.toNat < 2 ^ 160 ∧ n = mapSlot x 2) ∨ ∃ y ∈ A, ∃ z ∈ A, n = mapSlot y (mapSlot z 5)

section Keyed

variable {fork : Fork} {S : State.TransactionState} {message : Message fork}

theorem kba_sender : KeyBA (callKeys message S) (senderSlot message) :=
  .inl ⟨callerWord message, by simp [callKeys], mask_lt _, by
    simp only [senderSlot, callerKey, callerWord, mask_mask]⟩

theorem kba_rec {i : Nat} (hi : i = 0 ∨ i = 1) :
    KeyBA (callKeys message S) (recipientSlot (addrArg message.data i)) :=
  .inl ⟨addrArg message.data i, by rcases hi with rfl | rfl <;> simp [callKeys], addrArg_lt _ _,
    by simp only [recipientSlot, mkey_addrArg]⟩

theorem kba_allowArg : KeyBA (callKeys message S) (allowArg message) := by
  have h : mkey message.caller.toU256 = callerWord message := mask_mask _
  refine .inr ⟨addrArg message.data 0, by simp [callKeys], callerWord message, by simp [callKeys], ?_⟩
  simp only [allowArg, allowSlot, mkey_addrArg, h]

theorem kba_allowFrom : KeyBA (callKeys message S) (allowFrom message (fromArg message)) := by
  have h : mkey message.caller.toU256 = callerWord message := mask_mask _
  refine .inr ⟨callerWord message, by simp [callKeys], addrArg message.data 0, by simp [callKeys], ?_⟩
  simp only [allowFrom, fromArg, mkey_addrArg, h]

theorem kba_owner {X : State.TransactionState}
    (hX : storageAt X message.currentTarget 0 = storageAt S message.currentTarget 0) :
    KeyBA (callKeys message S) (ownerSlotOf X message.currentTarget) :=
  .inl ⟨ownerOf S message.currentTarget, by simp [callKeys], mask_lt _, by
    simp only [ownerSlotOf, ownerSlot]; rw [Issue.mkey_owner, hX]⟩

theorem writes_creditedK (hacc : hasAccount S message.currentTarget) :
    Writes message.currentTarget (KeyBA (callKeys message S)) S
      (credited (shortState S message) message (wordArg message.data 1) (addrArg message.data 0)) := by
  have := kba_sender (S := S) (message := message)
  have := kba_rec (S := S) (message := message) (i := 0) (.inl rfl)
  wchain

theorem writes_feeStateK (F : FixedSep) (hacc : hasAccount S message.currentTarget) :
    Writes message.currentTarget (KeyBA (callKeys message S)) S
      (feeState (shortState S message) message (wordArg message.data 1) (addrArg message.data 0)) := by
  have := kba_sender (S := S) (message := message)
  have := kba_rec (S := S) (message := message) (i := 0) (.inl rfl)
  have := kba_owner (S := S) (message := message) (storageAt_creditedFee0 F hacc (wordArg message.data 1) (addrArg message.data 0))
  wchain

theorem writes_creditedFK (hacc : hasAccount S message.currentTarget) :
    Writes message.currentTarget (KeyBA (callKeys message S)) S
      (creditedF (checkState S message) message (valArg message) (toArg message) (fromArg message)) := by
  have := kba_allowFrom (S := S) (message := message)
  have := kba_rec (S := S) (message := message) (i := 0) (.inl rfl)
  have := kba_rec (S := S) (message := message) (i := 1) (.inr rfl)
  wchain

theorem writes_feeStateFK (K : SepOn (callKeys message S)) (hacc : hasAccount S message.currentTarget) :
    Writes message.currentTarget (KeyBA (callKeys message S)) S
      (feeStateF (checkState S message) message (valArg message) (toArg message) (fromArg message)) := by
  have := kba_allowFrom (S := S) (message := message)
  have := kba_rec (S := S) (message := message) (i := 0) (.inl rfl)
  have := kba_rec (S := S) (message := message) (i := 1) (.inr rfl)
  have := kba_owner (S := S) (message := message)
    (storageAt_creditedFeeF0 K.fixed hacc K.allowFromArg.2 (valArg message) (toArg message))
  wchain

/-- A fixed slot is not of `KeyBA A`. -/
theorem fixed_not_kba {A : List U256} (K : SepOn A) {k : Nat} (hk : k < 11) :
    ¬ KeyBA A (BitVec.ofNat 256 k) := by
  rintro (⟨x, -, hx, e⟩ | ⟨y, hy, z, hz, e⟩)
  · exact K.fixed k hk x hx e
  · exact (K.allow y hy z hz).2 k hk e.symm

end Keyed

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
      (hw : Writes message.currentTarget (OwnW message) S S')
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

/-- The six functions that forward the call when deprecated: approve, totalSupply,
transferFrom, balanceOf, transfer, allowance. -/
def FwdFn (x : Nat) : Prop :=
  x = 0x095ea7b3 ∨ x = 0x18160ddd ∨ x = 0x23b872dd ∨ x = 0x70a08231 ∨ x = 0xa9059cbb ∨
    x = 0xdd62ed3e

/-- The seven functions whose code branches on the `deprecated` flag (byte 20 of slot 10): the
six of `FwdFn` and destroyBlackFunds (it asks the upgraded contract for the balance). -/
def FlagFn (x : Nat) : Prop := FwdFn x ∨ x = 0xf3bdc228

theorem flag_of {x : Nat} {b : U256} (h : byte20 b = 0 ∨ ¬ FlagFn x) (hx : FlagFn x) :
    byte20 b = 0 := h.resolve_right (fun hn => hn hx)

/-- **The effect of every successful call that runs locally**, for a loop that ends with no error
(`Ends`, round 37; it covers the loop of `runFrame` by `Ends.run`, and the shadow run of a loop over
`StateGasMeter` by `shadow_ends`): as `effect_call`, with `hdep` replaced by "not deprecated, or a
function other than the seven of `FlagFn`". The other 25 functions of the table do not branch on the
flag (their completeness theorems `ok_X` take no `hdep`). -/
theorem effect_localE (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (hdep : byte20 (storageAt state message.currentTarget 10) = 0 ∨
      ¬ FlagFn (selector message.data))
    (h7 : StrForm (storageAt state message.currentTarget 7))
    (h8 : StrForm (storageAt state message.currentTarget 8))
    (start : At CODE message 0 [] .empty gas state substate evm)
    (hrun : Ends fork evm s) (hok : s.error = none) : Effect message state s.state := by
  obtain ⟨-, -, i, hi⟩ := ends_ok_dispatch hfork hsize' start hrun hok
  have rd : ∀ {X : State.TransactionState}, s.state = X →
      (∀ n, storageAt X message.currentTarget n = storageAt state message.currentTarget n) →
      Effect message state s.state := fun hst h => .same (fun n => by rw [hst]; exact h n)
  match i, hi with
  | ⟨0, _⟩, hi =>
    rcases ok_name hfork hsize' (hi.trans rfl) h7 start hrun hok with
      ⟨-, -, -, hst, -⟩ | ⟨-, -, -, -, -, -, hst, -⟩ | ⟨-, -, -, -, hst, -⟩ <;>
    exact rd hst (fun n => by simp only [storageAt_readSlot, storageAt_rdSt])
  | ⟨1, _⟩, hi =>
    obtain ⟨-, hacc, howner, -, -, hst, -⟩ := ok_deprecate hfork hsize' (hi.trans rfl) rfl rfl
      start hrun hok
    refine .ownerW howner ?_
    rw [hst]
    refine Writes.wr (Writes.wr (Writes.read _ _) ?_ (.inr (.inr (.inr (.inl rfl)))) _) ?_
      (.inr (.inr (.inr (.inl rfl)))) _
    · wchain
    · wchain
  | ⟨2, _⟩, hi =>
    obtain ⟨-, hacc, -, -, h⟩ := ok_approve hfork hsize' (hi.trans rfl)
      (flag_of hdep (.inl (.inl (hi.trans rfl)))) rfl rfl start hrun hok
    refine .approve (hi.trans rfl) ?_
    rcases h with ⟨-, -, hst, -⟩ | ⟨-, -, -, hst, -⟩ <;> rw [hst]
    · exact Writes.wr (W := (· = allowArg message)) (Writes.read _ _) (hasAccount_readSlot hacc)
        rfl _
    · exact Writes.wr (W := (· = allowArg message)) ((Writes.read _ _).rd _ _)
        (hasAccount_readSlot (hasAccount_readSlot hacc)) rfl _
  | ⟨3, _⟩, hi =>
    obtain ⟨-, -, hst, -⟩ := ok_deprecated hfork hsize' (hi.trans rfl) start hrun hok
    exact rd hst (fun n => by simp only [storageAt_readSlot])
  | ⟨4, _⟩, hi =>
    obtain ⟨-, hacc, howner, -, -, hst, -⟩ := ok_addBlackList hfork hsize' (hi.trans rfl) rfl rfl
      start hrun hok
    refine .ownerW howner ?_
    rw [hst]
    exact Writes.wr (Writes.read _ _) (hasAccount_readSlot hacc)
      (.inr (.inr (.inr (.inr rfl)))) _
  | ⟨5, _⟩, hi =>
    obtain ⟨-, -, hst, -⟩ := ok_totalSupply hfork hsize' (hi.trans rfl)
      (flag_of hdep (.inl (.inr (.inl (hi.trans rfl))))) start hrun hok
    exact rd hst (fun n => by simp only [storageAt_readSlot])
  | ⟨6, _⟩, hi =>
    obtain ⟨-, hacc, -, hpause, hblack, -, hallow, hfv, hbal, hto, -, h⟩ := ok_transferFrom hfork
      hsize' (hi.trans rfl) (flag_of hdep (.inl (.inr (.inr (.inl (hi.trans rfl)))))) rfl rfl rfl rfl rfl rfl rfl rfl rfl start hrun hok
    rcases h with ⟨hfee, -, hst, -⟩ | ⟨-, hown, -, hst, -⟩
    · rw [sendOf_zero hfee] at hto
      exact .fromOk (hi.trans rfl) hacc hpause hblack hallow hbal hto hst
    · exact .fromFee (hi.trans rfl) hacc hpause hblack hallow hfv hbal hto hown hst
  | ⟨7, _⟩, hi =>
    obtain ⟨-, -, hst, -⟩ := ok_upgradedAddress hfork hsize' (hi.trans rfl) start hrun hok
    exact rd hst (fun n => by simp only [storageAt_readSlot])
  | ⟨8, _⟩, hi =>
    obtain ⟨-, -, hst, -⟩ := ok_balances hfork hsize' (hi.trans rfl) start hrun hok
    exact rd hst (fun n => by simp only [storageAt_readSlot])
  | ⟨9, _⟩, hi =>
    obtain ⟨-, -, hst, -⟩ := ok_decimals hfork hsize' (hi.trans rfl) start hrun hok
    exact rd hst (fun n => by simp only [storageAt_readSlot])
  | ⟨10, _⟩, hi =>
    obtain ⟨-, -, hst, -⟩ := ok_maximumFee hfork hsize' (hi.trans rfl) start hrun hok
    exact rd hst (fun n => by simp only [storageAt_readSlot])
  | ⟨11, _⟩, hi =>
    obtain ⟨-, -, hst, -⟩ := ok_totalSupplyVar hfork hsize' (hi.trans rfl) start hrun hok
    exact rd hst (fun n => by simp only [storageAt_readSlot])
  | ⟨12, _⟩, hi =>
    obtain ⟨-, hacc, howner, -, -, -, hst, -⟩ := ok_unpause hfork hsize' (hi.trans rfl) rfl start
      hrun hok
    rw [hst]
    exact .ownerW howner (Writes.write hacc (.inl rfl) _)
  | ⟨13, _⟩, hi =>
    obtain ⟨-, -, hst, -⟩ := ok_getBlackListStatus hfork hsize' (hi.trans rfl) start hrun hok
    exact rd hst (fun n => by simp only [storageAt_readSlot])
  | ⟨14, _⟩, hi =>
    obtain ⟨-, -, hst, -⟩ := ok_allowed hfork hsize' (hi.trans rfl) start hrun hok
    exact rd hst (fun n => by simp only [storageAt_readSlot])
  | ⟨15, _⟩, hi =>
    obtain ⟨-, -, hst, -⟩ := ok_paused hfork hsize' (hi.trans rfl) start hrun hok
    exact rd hst (fun n => by simp only [storageAt_readSlot])
  | ⟨16, _⟩, hi =>
    obtain ⟨-, -, hst, -⟩ := ok_balanceOf hfork hsize' (hi.trans rfl)
      (flag_of hdep (.inl (.inr (.inr (.inr (.inl (hi.trans rfl))))))) start hrun hok
    exact rd hst (fun n => by simp only [storageAt_readSlot])
  | ⟨17, _⟩, hi =>
    obtain ⟨-, hacc, howner, -, -, -, hst, -⟩ := ok_pause hfork hsize' (hi.trans rfl) rfl start
      hrun hok
    rw [hst]
    exact .ownerW howner (Writes.write hacc (.inl rfl) _)
  | ⟨18, _⟩, hi =>
    obtain ⟨-, -, hst, -⟩ := ok_getOwner hfork hsize' (hi.trans rfl) start hrun hok
    exact rd hst (fun n => by simp only [storageAt_readSlot])
  | ⟨19, _⟩, hi =>
    obtain ⟨-, -, hst, -⟩ := ok_owner hfork hsize' (hi.trans rfl) start hrun hok
    exact rd hst (fun n => by simp only [storageAt_readSlot])
  | ⟨20, _⟩, hi =>
    rcases ok_symbol hfork hsize' (hi.trans rfl) h8 start hrun hok with
      ⟨-, -, -, hst, -⟩ | ⟨-, -, -, -, -, -, hst, -⟩ | ⟨-, -, -, -, hst, -⟩ <;>
    exact rd hst (fun n => by simp only [storageAt_readSlot, storageAt_rdSt])
  | ⟨21, _⟩, hi =>
    obtain ⟨-, hacc, -, hpause, hblack, -, hfv, hbal, hto, -, h⟩ := ok_transfer hfork hsize'
      (hi.trans rfl) (flag_of hdep (.inl (.inr (.inr (.inr (.inr (.inl (hi.trans rfl)))))))) rfl rfl rfl rfl rfl rfl rfl rfl start hrun hok
    rcases h with ⟨hfee, -, hst, -⟩ | ⟨-, hown, -, hst, -⟩
    · rw [sendOf_zero hfee] at hto
      exact .transferOk (hi.trans rfl) hacc hpause hblack hbal hto hst
    · exact .transferFee (hi.trans rfl) hacc hpause hblack hfv hbal hto hown hst
  | ⟨22, _⟩, hi =>
    obtain ⟨-, hacc, howner, -, -, -, -, -, hst, -⟩ := ok_setParams hfork hsize' (hi.trans rfl)
      rfl rfl rfl rfl start hrun hok
    refine .ownerW howner ?_
    rw [hst]
    refine ((Writes.wr ((Writes.wr (Writes.read _ _) ?_ (.inr (.inl rfl)) _).rd _ _) ?_
      (.inr (.inr (.inl rfl))) _).rd _ _).rd _ _
    · wchain
    · wchain
  | ⟨23, _⟩, hi =>
    obtain ⟨-, hacc, howner, -, hT, hB, -, -, hst, -⟩ := ok_issue hfork hsize' (hi.trans rfl) rfl
      rfl rfl start hrun hok
    exact .issue (hi.trans rfl) howner hacc hT hB hst
  | ⟨24, _⟩, hi =>
    obtain ⟨-, hacc, howner, hT, hB, -, -, hst, -⟩ := ok_redeem hfork hsize' (hi.trans rfl) rfl
      rfl rfl start hrun hok
    exact .redeem (hi.trans rfl) howner hacc hT hB hst
  | ⟨25, _⟩, hi =>
    obtain ⟨-, -, hst, -⟩ := ok_allowance hfork hsize' (hi.trans rfl)
      (flag_of hdep (.inl (.inr (.inr (.inr (.inr (.inr (hi.trans rfl)))))))) start hrun hok
    exact rd hst (fun n => by simp only [storageAt_readSlot])
  | ⟨26, _⟩, hi =>
    obtain ⟨-, -, hst, -⟩ := ok_basisPointsRate hfork hsize' (hi.trans rfl) start hrun hok
    exact rd hst (fun n => by simp only [storageAt_readSlot])
  | ⟨27, _⟩, hi =>
    obtain ⟨-, -, hst, -⟩ := ok_isBlackListed hfork hsize' (hi.trans rfl) start hrun hok
    exact rd hst (fun n => by simp only [storageAt_readSlot])
  | ⟨28, _⟩, hi =>
    obtain ⟨-, hacc, howner, -, -, hst, -⟩ := ok_removeBlackList hfork hsize' (hi.trans rfl) rfl
      rfl start hrun hok
    refine .ownerW howner ?_
    rw [hst]
    exact Writes.wr (Writes.read _ _) (hasAccount_readSlot hacc)
      (.inr (.inr (.inr (.inr rfl)))) _
  | ⟨29, _⟩, hi =>
    obtain ⟨-, -, hst, -⟩ := ok_maxUint hfork hsize' (hi.trans rfl) start hrun hok
    exact rd hst (fun _ => rfl)
  | ⟨30, _⟩, hi =>
    obtain ⟨howner, -, h⟩ := ok_transferOwnership hfork hsize' (hi.trans rfl) rfl start hrun hok
    rcases h with ⟨-, -, hst, -⟩ | ⟨-, -, hacc, -, hst, -⟩
    · exact rd hst (fun n => by simp only [storageAt_readSlot])
    · rw [hst]
      exact .ownerW howner (Writes.write hacc (.inl rfl) _)
  | ⟨31, _⟩, hi =>
    obtain ⟨-, hacc, howner, hlisted, -, -, hst, -⟩ := ok_destroyBlackFunds hfork hsize'
      (hi.trans rfl) (flag_of hdep (.inr (hi.trans rfl))) rfl rfl rfl rfl rfl start hrun hok
    exact .destroy (hi.trans rfl) howner hacc hlisted hst
  | ⟨n + 32, h⟩, _ => exact absurd h (by omega)

/-- **The effect of every successful call that runs locally**: as `effect_call`, with `hdep`
replaced by "not deprecated, or a function other than the seven of `FlagFn`". The `runFrame`
form of `effect_localE`. -/
theorem effect_local (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (hdep : byte20 (storageAt state message.currentTarget 10) = 0 ∨
      ¬ FlagFn (selector message.data))
    (h7 : StrForm (storageAt state message.currentTarget 7))
    (h8 : StrForm (storageAt state message.currentTarget 8))
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) : Effect message state s.state :=
  effect_localE hfork hsize' hdep h7 h8 start (Ends.run hrun) hok

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
    (hok : s.error = none) : Effect message state s.state :=
  effect_local hfork hsize' (.inl hdep) h7 h8 start within hrun hok

/-! ## Over the EIP-8037 meter (round 37) -/

/-- **A successful run over `StateGasMeter`, as a loop of the meter `Nat` that ends** (round 37).
A run of the loop over `StateGasMeter`, for any gas bound and message runner, from a frame `m`
whose `toNat` is a fresh frame of `CODE`, that ends in `t` with no error: some fresh frame of
`CODE` of the meter `Nat` with the same message, state and substate (and more gas) has a loop that
ends (`Ends`) with no error in the state of `t`. No hypothesis on the reservoir, on refills or on
the gas limit (`Shadow.shadow_ends`). -/
theorem ends_any (hfork : .berlin ≤ fork)
    {runS : MessageRunner fork StateGasMeter bound} {m t : Evm fork StateGasMeter}
    (start : At CODE message 0 [] .empty gas state substate (Meter.toNat m))
    {within : GasMeter.gasHeld m.gas ≤ bound}
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runS m within = .ok t)
    (hok : t.error = none) :
    ∃ (g : Nat) (l e : Evm fork Nat), At CODE message 0 [] .empty g state substate l ∧
      Ends fork l e ∧ e.error = none ∧ e.state = t.state := by
  obtain ⟨G, hE⟩ := Shadow.shadow_ends hfork hrun hok
  exact ⟨_, _, _, at_addGas start (Shadow.budget m), hE, hok, rfl⟩

/-- **The effect of every successful call that runs locally, over `StateGasMeter`** (round 37):
`effect_local` for a run of the loop over `StateGasMeter`, for any gas bound and message runner,
from a frame `m` whose `toNat` is the fresh frame of `CODE`. No hypothesis on the reservoir of
`m`, on refills or on the gas limit. -/
theorem effect_local_any (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (hdep : byte20 (storageAt state message.currentTarget 10) = 0 ∨
      ¬ FlagFn (selector message.data))
    (h7 : StrForm (storageAt state message.currentTarget 7))
    (h8 : StrForm (storageAt state message.currentTarget 8))
    {runS : MessageRunner fork StateGasMeter bound} {m t : Evm fork StateGasMeter}
    (start : At CODE message 0 [] .empty gas state substate (Meter.toNat m))
    {within : GasMeter.gasHeld m.gas ≤ bound}
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runS m within = .ok t)
    (hok : t.error = none) : Effect message state t.state := by
  obtain ⟨_, _, e, start', hE, hok', hst⟩ := ends_any hfork start hrun hok
  rw [← hst]
  exact effect_localE hfork hsize' hdep h7 h8 start' hE hok'

/-- **The effect of every successful call over `StateGasMeter`** (round 37, not deprecated):
`effect_call` over `StateGasMeter`, any reservoir, refills allowed. -/
theorem effect_any (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    (h7 : StrForm (storageAt state message.currentTarget 7))
    (h8 : StrForm (storageAt state message.currentTarget 8))
    {runS : MessageRunner fork StateGasMeter bound} {m t : Evm fork StateGasMeter}
    (start : At CODE message 0 [] .empty gas state substate (Meter.toNat m))
    {within : GasMeter.gasHeld m.gas ≤ bound}
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runS m within = .ok t)
    (hok : t.error = none) : Effect message state t.state :=
  effect_local_any hfork hsize' (.inl hdep) h7 h8 start hrun hok

/-! ## Deprecated or not -/

/-- What a successful call does to the storage of `C = message.currentTarget`, deprecated or
not, from the start state `S` to the end state `S'`, for the runner `runChild`:

- `loc`: an `Effect` (every call when not deprecated, and the 25 functions outside `FlagFn`
  when deprecated);
- `fwd`: deprecated, one of the six forwarding functions (`FwdFn`): one call from `C` to the
  upgraded address, sent from a state `X` whose storage at `C` is that of `S`; the end state is
  the child's end state. transfer and transferFrom check, before the call, that `C` is not paused
  and that the sender (transfer) or `_from` (transferFrom) is not blacklisted (`hT`, `hF`);
- `dfwd`: deprecated destroyBlackFunds, by the owner, with `a` blacklisted: the same call (the
  forwarded `balanceOf(a)`), from `X` to `Y`, then `balances[a] := 0` and slot 1 `:= T - d`
  over `Y` (`tailState`), `d` some word (in the proof of `effect_all`, the word the call
  returned; this case does not record it). -/
inductive EffectD {fork : Fork} {bound : Nat} (runChild : MessageRunner fork Nat bound)
    (message : Message fork) (S S' : State.TransactionState) : Prop
  | loc (h : Effect message S S')
  | fwd (hdep : byte20 (storageAt S message.currentTarget 10) ≠ 0)
      (hsel : FwdFn (selector message.data))
      (hT : selector message.data = 0xa9059cbb →
        byte20 (storageAt S message.currentTarget 0) = 0 ∧
        (storageAt S message.currentTarget (blackSlot message)).toNat % 256 = 0)
      (hF : selector message.data = 0x23b872dd →
        byte20 (storageAt S message.currentTarget 0) = 0 ∧
        (storageAt S message.currentTarget (blackFrom (fromArg message))).toNat % 256 = 0)
      (X : State.TransactionState)
      (hX : ∀ n, storageAt X message.currentTarget n = storageAt S message.currentTarget n)
      (hf : FwdAt runChild message S (upAddr S message) X S')
  | dfwd (hdep : byte20 (storageAt S message.currentTarget 10) ≠ 0)
      (hsel : selector message.data = 0xf3bdc228)
      (howner : callerWord message = ownerOf S message.currentTarget)
      (hlisted : (storageAt S message.currentTarget (listSlot (addrArg message.data 0))).toNat %
        256 ≠ 0)
      (X Y : State.TransactionState) (d : U256)
      (hX : ∀ n, storageAt X message.currentTarget n = storageAt S message.currentTarget n)
      (hf : FwdAt runChild message S (upAddr S message) X Y)
      (hacc : hasAccount Y message.currentTarget)
      (hst : S' = DeprecatedDestroy.tailState Y message.currentTarget (addrArg message.data 0) d)

theorem fwd_of_local (h : LocalForward runChild message state s) :
    ∃ X, (∀ n, storageAt X message.currentTarget n = storageAt state message.currentTarget n) ∧
      FwdAt runChild message state (upAddr state message) X s.state := by
  obtain ⟨caller, msg, lt, child, hsv, hch, he, -, hst⟩ := h
  exact ⟨caller.state, fun n => storageAt_of_readsAs hsv.choose_spec.choose_spec.2.2.1 _ n,
    caller, msg, lt, child, hsv, hch, he, rfl, hst.symm⟩

/-- **The effect of every successful call, deprecated or not.** From Berlin (Glamsterdam
included), a fresh frame of `CODE` at pc 0, static or not, any call data below 2^256 bytes, any
value, any gas, any gas bound and any message runner, slots 7 and 8 of `StrForm`: every run that
ends with no error ends in a state described by `EffectD`. No assumption on the runner. -/
theorem effect_all (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (h7 : StrForm (storageAt state message.currentTarget 7))
    (h8 : StrForm (storageAt state message.currentTarget 8))
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) : EffectD runChild message state s.state := by
  by_cases hdep : byte20 (storageAt state message.currentTarget 10) = 0
  · exact .loc (effect_local hfork hsize' (.inl hdep) h7 h8 start within hrun hok)
  by_cases hf : FlagFn (selector message.data)
  case neg => exact .loc (effect_local hfork hsize' (.inr hf) h7 h8 start within hrun hok)
  have ne : ∀ {a b : Nat}, selector message.data = a → a ≠ b → selector message.data ≠ b :=
    fun h hab e => hab (h.symm.trans e)
  rcases hf with (h | h | h | h | h | h) | h
  · obtain ⟨X, hX, hF⟩ := fwd_of_local (dep_approve_local hfork hsize' h hdep start within hrun hok)
    exact .fwd hdep (.inl h) (fun e => absurd e (ne h (by decide)))
      (fun e => absurd e (ne h (by decide))) X hX hF
  · obtain ⟨X, hX, hF⟩ := fwd_of_local
      (dep_totalSupply_local hfork hsize' h hdep start within hrun hok)
    exact .fwd hdep (.inr (.inl h)) (fun e => absurd e (ne h (by decide)))
      (fun e => absurd e (ne h (by decide))) X hX hF
  · obtain ⟨X, hX, hF⟩ := fwd_of_local
      (dep_transferFrom_local hfork hsize' h hdep start within hrun hok)
    obtain ⟨_, _, -, -, hpause, hblack, -⟩ :=
      dep_transferFrom_complete hfork hsize' h hdep rfl rfl rfl rfl start within hrun hok
    exact .fwd hdep (.inr (.inr (.inl h))) (fun e => absurd e (ne h (by decide)))
      (fun _ => ⟨hpause, hblack⟩) X hX hF
  · obtain ⟨X, hX, hF⟩ := fwd_of_local
      (dep_balanceOf_local hfork hsize' h hdep start within hrun hok)
    exact .fwd hdep (.inr (.inr (.inr (.inl h)))) (fun e => absurd e (ne h (by decide)))
      (fun e => absurd e (ne h (by decide))) X hX hF
  · obtain ⟨X, hX, hF⟩ := fwd_of_local
      (dep_transfer_local hfork hsize' h hdep start within hrun hok)
    obtain ⟨_, _, -, -, hpause, hblack, -⟩ :=
      dep_transfer_complete hfork hsize' h hdep rfl rfl rfl rfl start within hrun hok
    exact .fwd hdep (.inr (.inr (.inr (.inr (.inl h))))) (fun _ => ⟨hpause, hblack⟩)
      (fun e => absurd e (ne h (by decide))) X hX hF
  · obtain ⟨X, hX, hF⟩ := fwd_of_local
      (dep_allowance_local hfork hsize' h hdep start within hrun hok)
    exact .fwd hdep (.inr (.inr (.inr (.inr (.inr h))))) (fun e => absurd e (ne h (by decide)))
      (fun e => absurd e (ne h (by decide))) X hX hF
  · obtain ⟨c, r, hcode, hroute, howner, hlisted, -, -, -, caller, msg, lt, child, hch, he, -, hacc',
        hfwd, -, hcs, -, -, -, -, -, hst, -⟩ :=
      dep_destroy_complete hfork hsize' h hdep rfl rfl rfl rfl start within hrun hok
    have hv : ReadsAs caller.state state := by
      rw [hcs]
      reads_as
    refine .dfwd hdep h howner hlisted caller.state child.1.state
      (resWord (DeprecatedBalance.outMemOf (DeprecatedDestroy.memD message) child.1.output))
      (fun n => ?_)
      ⟨caller, msg, lt, child, sentVia_of_sendsVia hcode hroute hfwd hv, hch, he, rfl, rfl⟩
      hacc' ?_
    · rw [hcs]
      simp only [DeprecatedDestroy.callStateD, DestroySpec.preState, storageAt_rec,
        storageAt_route, storageAt_readSlot]
    · rw [hst, state_incorporateChild]

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

/-! ## Sequences of calls, deprecated or not -/

/-- One successful run of `CODE` for a message to `C`, from `S` to `S'`, as `RunOk`, whose runner
meets `KeepsOn … (SentVia …) R` for the calls the code makes from `S` to the upgraded address when
`C` is deprecated at `S` (round 29; over every message before; EthLib's `KeepsOn` and `SentVia`
since round 49). -/
def RunOkR (C : Address) (R : State.TransactionState → State.TransactionState → Prop)
    (S S' : State.TransactionState) {fork : Fork} (message : Message fork) : Prop :=
  ∃ (substate : Substate) (gas bound : Nat) (runChild : MessageRunner fork Nat bound)
    (evm s : Evm fork Nat) (within : GasMeter.gasHeld evm.gas ≤ bound),
    message.currentTarget = C ∧ .berlin ≤ fork ∧ message.data.size < 2 ^ 256 ∧
    (byte20 (storageAt S C 10) ≠ 0 →
      KeepsOn runChild (SentVia message S (upAddr S message)) R) ∧
    At CODE message 0 [] .empty gas S substate evm ∧
    Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s ∧
    s.error = none ∧ S' = s.state

/-- `effect_all` for a `RunOkR` step, with the runner assumption. -/
theorem RunOkR.effect {C : Address} {R : State.TransactionState → State.TransactionState → Prop}
    {S S' : State.TransactionState} (h : RunOkR C R S S' message)
    (h7 : StrForm (storageAt S C 7)) (h8 : StrForm (storageAt S C 8)) :
    message.currentTarget = C ∧ ∃ (bound : Nat) (runChild : MessageRunner fork Nat bound),
      EffectD runChild message S S' ∧
      (byte20 (storageAt S C 10) ≠ 0 →
        KeepsOn runChild (SentVia message S (upAddr S message)) R) := by
  obtain ⟨substate, gas, bound, runChild, evm, s, within, hC, hfork, hsize, hk, start, hrun, hok,
    rfl⟩ := h
  subst hC
  exact ⟨rfl, bound, runChild, effect_all hfork hsize h7 h8 start within hrun hok, hk⟩

/-- A finite sequence of `RunOkR` calls to `C`, each meeting `Q` on its message and its start
state, and of changes that keep every storage word of `C`. -/
inductive SeqR (C : Address) (R : State.TransactionState → State.TransactionState → Prop)
    (Q : ∀ {fork : Fork}, Message fork → State.TransactionState → Prop) :
    State.TransactionState → State.TransactionState → Prop
  | nil (S : State.TransactionState) : SeqR C R Q S S
  | call {S S' S'' : State.TransactionState} {fork : Fork} {message : Message fork} :
      RunOkR C R S S' message → Q message S → SeqR C R Q S' S'' → SeqR C R Q S S''
  | other {S S' S'' : State.TransactionState} : Untouched C S S' → SeqR C R Q S' S'' →
      SeqR C R Q S S''

/-- `seq_lift` for `SeqR`. -/
theorem seqR_lift {C : Address} {R0 : State.TransactionState → State.TransactionState → Prop}
    {Q : ∀ {fork : Fork}, Message fork → State.TransactionState → Prop}
    {I : State.TransactionState → Prop} {R : State.TransactionState → State.TransactionState → Prop}
    (hrefl : ∀ S, R S S) (htrans : ∀ {S S' S''}, R S S' → R S' S'' → R S S'')
    (hother : ∀ {S S'}, Untouched C S S' → I S → R S S' ∧ I S')
    (hcall : ∀ {S S'} {fork : Fork} {message : Message fork}, RunOkR C R0 S S' message →
      Q message S → I S → R S S' ∧ I S')
    {S S' : State.TransactionState} (h : SeqR C R0 Q S S') (hI : I S) : R S S' := by
  induction h with
  | nil S => exact hrefl S
  | call hr hq _ ih =>
    obtain ⟨hR, hI'⟩ := hcall hr hq hI
    exact htrans hR (ih hI')
  | other hu _ ih =>
    obtain ⟨hR, hI'⟩ := hother hu hI
    exact htrans hR (ih hI')

/-- The predicate on each call of the sequences deprecated or not: slots 7 and 8 of `StrForm` at
its start state (they are read by name() and symbol() only). -/
def Strs {fork : Fork} (message : Message fork) (S : State.TransactionState) : Prop :=
  StrForm (storageAt S message.currentTarget 7) ∧ StrForm (storageAt S message.currentTarget 8)

/-! ## Sequences over the meter `Nat` and over `StateGasMeter` (round 37) -/

/-- One successful run of `CODE` over `StateGasMeter` for a message to `C`, from `S` to `S'`,
with the hypotheses `effect_any` takes beyond "not deprecated" and the string slots: any gas
bound, message runner and reservoir. -/
def RunOkS (C : Address) (S S' : State.TransactionState) {fork : Fork} (message : Message fork) :
    Prop :=
  ∃ (substate : Substate) (gas bound : Nat) (runChild : MessageRunner fork StateGasMeter bound)
    (m s : Evm fork StateGasMeter) (within : GasMeter.gasHeld m.gas ≤ bound),
    message.currentTarget = C ∧ .berlin ≤ fork ∧ message.data.size < 2 ^ 256 ∧
    At CODE message 0 [] .empty gas S substate (Meter.toNat m) ∧
    Evm.runFrame (step fork) (step_decreases fork) bound runChild m within = .ok s ∧
    s.error = none ∧ S' = s.state

/-- What the sequence theorems use of one call: its target is `C`, and when `C` is not
deprecated at `S` and slots 7 and 8 are of `StrForm` there, the call has an `Effect`. -/
def RunEff (C : Address) (S S' : State.TransactionState) {fork : Fork} (message : Message fork) :
    Prop :=
  message.currentTarget = C ∧ (byte20 (storageAt S C 10) = 0 → StrForm (storageAt S C 7) →
    StrForm (storageAt S C 8) → Effect message S S')

theorem RunOk.eff {C : Address} {S S' : State.TransactionState} (h : RunOk C S S' message) :
    RunEff C S S' message := by
  have hC : message.currentTarget = C := by obtain ⟨_, _, _, _, _, _, _, hC, -⟩ := h; exact hC
  exact ⟨hC, fun hdep h7 h8 => (h.effect hdep h7 h8).2⟩

theorem RunOkS.eff {C : Address} {S S' : State.TransactionState} (h : RunOkS C S S' message) :
    RunEff C S S' message := by
  obtain ⟨substate, gas, bound, runChild, m, s, within, hC, hfork, hsize, start, hrun, hok, rfl⟩ :=
    h
  subst hC
  exact ⟨rfl, fun hdep h7 h8 => effect_any hfork hsize hdep h7 h8 start hrun hok⟩

theorem RunEff.effect {C : Address} {S S' : State.TransactionState} (h : RunEff C S S' message)
    (hdep : byte20 (storageAt S C 10) = 0) (h7 : StrForm (storageAt S C 7))
    (h8 : StrForm (storageAt S C 8)) : message.currentTarget = C ∧ Effect message S S' :=
  ⟨h.1, h.2 hdep h7 h8⟩

/-- A finite sequence of successful calls to `C` over the meter `Nat` (`RunOk`) or over
`StateGasMeter` (`RunOkS`), each meeting `Q` on its message and its start state, and of changes
that keep every storage word of `C`. -/
inductive SeqS (C : Address) (Q : ∀ {fork : Fork}, Message fork → State.TransactionState → Prop) :
    State.TransactionState → State.TransactionState → Prop
  | nil (S : State.TransactionState) : SeqS C Q S S
  | call {S S' S'' : State.TransactionState} {fork : Fork} {message : Message fork} :
      RunOk C S S' message → Q message S → SeqS C Q S' S'' → SeqS C Q S S''
  | callS {S S' S'' : State.TransactionState} {fork : Fork} {message : Message fork} :
      RunOkS C S S' message → Q message S → SeqS C Q S' S'' → SeqS C Q S S''
  | other {S S' S'' : State.TransactionState} : Untouched C S S' → SeqS C Q S' S'' →
      SeqS C Q S S''

/-- Every `Seq` is a `SeqS`. -/
theorem Seq.toS {C : Address} {Q : ∀ {fork : Fork}, Message fork → State.TransactionState → Prop}
    {S S' : State.TransactionState} (h : Seq C Q S S') : SeqS C Q S S' := by
  induction h with
  | nil S => exact .nil S
  | call hr hq _ ih => exact .call hr hq ih
  | other hu _ ih => exact .other hu ih

/-- `seq_lift` for `SeqS`: the calls are given by `RunEff`. -/
theorem seqS_lift {C : Address} {Q : ∀ {fork : Fork}, Message fork → State.TransactionState → Prop}
    {I : State.TransactionState → Prop} {R : State.TransactionState → State.TransactionState → Prop}
    (hrefl : ∀ S, R S S) (htrans : ∀ {S S' S''}, R S S' → R S' S'' → R S S'')
    (hother : ∀ {S S'}, Untouched C S S' → I S → R S S' ∧ I S')
    (hcall : ∀ {S S'} {fork : Fork} {message : Message fork}, RunEff C S S' message →
      Q message S → I S → R S S' ∧ I S')
    {S S' : State.TransactionState} (h : SeqS C Q S S') (hI : I S) : R S S' := by
  induction h with
  | nil S => exact hrefl S
  | call hr hq _ ih =>
    obtain ⟨hR, hI'⟩ := hcall hr.eff hq hI
    exact htrans hR (ih hI')
  | callS hr hq _ ih =>
    obtain ⟨hR, hI'⟩ := hcall hr.eff hq hI
    exact htrans hR (ih hI')
  | other hu _ ih =>
    obtain ⟨hR, hI'⟩ := hother hu hI
    exact htrans hR (ih hI')

end UsdtVerify.Security
