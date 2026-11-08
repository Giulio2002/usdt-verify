import UsdtVerify.Usdt.Security.Effect

/-!
# Access control: what a caller other than the owner can change

The owner is the low 160 bits of slot 0 (`ownerOf`); the caller is compared with it as the code
does (`callerWord`, the caller masked to 160 bits).

- `Effect.nonOwner`: a successful call by a caller other than the owner (not deprecated) writes
  only slots of `balances` and of `allowed` (`BalOrAllow`): every other slot of the contract holds
  the same word at the end as at the start. No keccak hypothesis.
- `nonOwner_call`: so, over every successful call by such a caller (any call data below 2^256
  bytes, any value, any gas, static or not), and under `SecSep` of the call's keys, the
  `Protected` slots keep their words: slot 0 (owner and the `paused` flag, byte 20), slot 1
  (`_totalSupply`), slots 3 and 4 (`basisPointsRate`, `maximumFee`), slot 10 (`upgradedAddress`
  and the `deprecated` flag, byte 20), and the slot of `isBlackListed` of every address word.
- `nonOwner_seq`: the same over a finite sequence (`Seq`) of successful calls, each by a caller
  other than the owner of its start state, and of `Untouched` steps, when the contract is not
  deprecated and slots 7 and 8 are of `StrForm` at the start (both kept along the sequence, as is
  the owner).

Deprecated or not (round 23):
- `owner_only`: every successful run of one of the ten owner functions (`OwnerFn`) is a call by
  the owner, deprecated or not, with no assumption on the runner.
- `nonOwner_local`: `nonOwner_call` without `hdep` for every function outside the six that
  forward (`FwdFn`), with no assumption on the runner.
- `nonOwner_call_all`: every function, deprecated or not; when deprecated the runner meets
  `KeepsSlots` (a call from `C` to the upgraded address that ends with no error keeps every
  `Protected` slot of `C`). Conclusion: every `Protected` slot keeps its word (`ProtKept`).
- `nonOwner_seq_all`: the same over a `SeqR` sequence.

Hypotheses by name: `K : SecSep (callKeys message state)` (keccak separation of the finitely many
slots keyed by the call's words, not proved; round 29, replacing `KeccakSep` and `AllowSep`), `hdep` (not deprecated:
byte 20 of slot 10 is 0; deprecated paths call the upgraded contract), `h7`, `h8` (`StrForm`, for
name() and symbol()), `hno` (the caller is not the owner).
-/

namespace UsdtVerify.Security

open EthLib.Base (Fork U256 Address)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open Invariant Complete Owner Approve Deprecated
open Pause AddrWrite SetParamsSpec Issue IssueSpec BlackList BlackListSpec AddrWriteSpec DestroySpec

/-- Slots 0, 1, 3, 4, 10 and the slots of `isBlackListed`. -/
def Protected (n : U256) : Prop := n = 0 ∨ n = 1 ∨ n = 3 ∨ n = 4 ∨ n = 10 ∨ ListSlot n

/-- With `SecSep A`, no protected slot is of `KeyBA A`. -/
theorem protected_not_kba {A : List U256} (K : SecSep A) {n : U256} (h : Protected n) :
    ¬ KeyBA A n := by
  rcases h with rfl | rfl | rfl | rfl | rfl | ⟨w, hw, rfl⟩
  · exact fixed_not_kba K.toSepOn (k := 0) (by decide)
  · exact fixed_not_kba K.toSepOn (k := 1) (by decide)
  · exact fixed_not_kba K.toSepOn (k := 3) (by decide)
  · exact fixed_not_kba K.toSepOn (k := 4) (by decide)
  · exact fixed_not_kba K.toSepOn (k := 10) (by decide)
  · rintro (⟨x, hx, hxl, e⟩ | ⟨y, hy, z, hz, e⟩)
    · exact K.balList x hx hxl w hw e.symm
    · exact K.allowList y hy z hz w hw e.symm

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate} {bound : Nat} {runChild : MessageRunner fork Nat bound}
  {evm s : Evm fork Nat} {gas : Nat}

/-- A successful call by a caller other than the owner writes only slots of `balances` and of
`allowed`. -/
theorem Effect.nonOwner {S S' : State.TransactionState} (h : Effect message S S')
    (hno : callerWord message ≠ ownerOf S message.currentTarget) :
    Writes message.currentTarget BalOrAllow S S' := by
  cases h with
  | same h => exact .of_same h
  | transferOk _ hacc _ _ _ _ hst => rw [hst]; exact (writes_credited hacc _ _).mono fun _ h => .inl h
  | transferFee _ hacc _ _ _ _ _ _ hst =>
    rw [hst]; exact (writes_feeState hacc _ _).mono fun _ h => .inl h
  | fromOk _ hacc _ _ _ _ _ hst => rw [hst]; exact writes_creditedF hacc _ _ _
  | fromFee _ hacc _ _ _ _ _ _ _ hst => rw [hst]; exact writes_feeStateF hacc _ _ _
  | approve _ hw => exact hw.mono fun _ e => by subst e; exact .inr (allow_mk _ _)
  | ownerW howner _ => exact absurd howner hno
  | issue _ howner => exact absurd howner hno
  | redeem _ howner => exact absurd howner hno
  | destroy _ howner => exact absurd howner hno

/-- The same, with the slots keyed by the call's words (round 29): a successful call by a caller
other than the owner writes only balance slots of the words of `callKeys` and slots of `allowed`
keyed by them. -/
theorem Effect.nonOwnerK {S S' : State.TransactionState} (K : SepOn (callKeys message S))
    (h : Effect message S S') (hno : callerWord message ≠ ownerOf S message.currentTarget) :
    Writes message.currentTarget (KeyBA (callKeys message S)) S S' := by
  cases h with
  | same h => exact .of_same h
  | transferOk _ hacc _ _ _ _ hst => rw [hst]; exact writes_creditedK hacc
  | transferFee _ hacc _ _ _ _ _ _ hst => rw [hst]; exact writes_feeStateK K.fixed hacc
  | fromOk _ hacc _ _ _ _ _ hst => rw [hst]; exact writes_creditedFK hacc
  | fromFee _ hacc _ _ _ _ _ _ _ hst => rw [hst]; exact writes_feeStateFK K hacc
  | approve _ hw => exact hw.mono fun _ e => by subst e; exact kba_allowArg
  | ownerW howner _ => exact absurd howner hno
  | issue _ howner => exact absurd howner hno
  | redeem _ howner => exact absurd howner hno
  | destroy _ howner => exact absurd howner hno

/-- **Access control, one call.** From Berlin (Glamsterdam included), a fresh frame of `CODE` at
pc 0, static or not, any call data below 2^256 bytes, any value, any gas, any gas bound and any
message runner, not deprecated, slots 7 and 8 of `StrForm`: if the caller is not the owner and
the run ends with no error, only slots of `balances` and `allowed` change, and under `SecSep` of
the call's keys every `Protected` slot keeps its word. -/
theorem nonOwner_call (K : SecSep (callKeys message state)) (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    (h7 : StrForm (storageAt state message.currentTarget 7))
    (h8 : StrForm (storageAt state message.currentTarget 8))
    (hno : callerWord message ≠ ownerOf state message.currentTarget)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) :
    Writes message.currentTarget BalOrAllow state s.state ∧
      ∀ n, Protected n → storageAt s.state message.currentTarget n =
        storageAt state message.currentTarget n := by
  have he := effect_call hfork hsize' hdep h7 h8 start within hrun hok
  exact ⟨he.nonOwner hno, fun n hn => he.nonOwnerK K.toSepOn hno n (protected_not_kba K hn)⟩

/-- The caller is not the owner of the start state. -/
def NotOwner {fork : Fork} (message : Message fork) (S : State.TransactionState) : Prop :=
  callerWord message ≠ ownerOf S message.currentTarget

/-- The predicate of `nonOwner_seq` on each call: its caller is not the owner of its start
state, and `SecSep` holds for its keys there (round 29). -/
def NotOwnerK {fork : Fork} (message : Message fork) (S : State.TransactionState) : Prop :=
  NotOwner message S ∧ SecSep (callKeys message S)

/-- What `nonOwner_seq` keeps along the sequence: not deprecated, slots 7 and 8 of `StrForm`. -/
def Plain (C : Address) (S : State.TransactionState) : Prop :=
  byte20 (storageAt S C 10) = 0 ∧ StrForm (storageAt S C 7) ∧ StrForm (storageAt S C 8)

theorem plain_of_writes {A : List U256} (K : SepOn A) {C : Address}
    {S S' : State.TransactionState}
    (hw : Writes C (KeyBA A) S S') (hP : Plain C S) : Plain C S' := by
  obtain ⟨hdep, h7, h8⟩ := hP
  refine ⟨?_, ?_, ?_⟩
  · rw [hw 10 (fixed_not_kba K (k := 10) (by decide))]; exact hdep
  · rw [hw 7 (fixed_not_kba K (k := 7) (by decide))]; exact h7
  · rw [hw 8 (fixed_not_kba K (k := 8) (by decide))]; exact h8

theorem plain_of_untouched {C : Address} {S S' : State.TransactionState} (hu : Untouched C S S')
    (hP : Plain C S) : Plain C S' := by
  obtain ⟨hdep, h7, h8⟩ := hP
  exact ⟨by rw [hu]; exact hdep, by rw [hu]; exact h7, by rw [hu]; exact h8⟩

/-- **Access control over a sequence.** Along a finite sequence of successful calls to `C`, each
by a caller other than the owner of its start state, and of `Untouched` steps, from a state where
`C` is not deprecated and slots 7 and 8 are of `StrForm`, each call with `SecSep` of its keys at
its start state: only slots of `balances` and `allowed` change, and every `Protected` slot (the
owner, the `paused` and `deprecated` flags, `_totalSupply`, slots 3 and 4, `upgradedAddress`, the
blacklist flag of every address word) keeps its word. -/
theorem nonOwner_seq {C : Address} {S S' : State.TransactionState}
    (h : Seq C NotOwnerK S S') (hdep : byte20 (storageAt S C 10) = 0)
    (h7 : StrForm (storageAt S C 7)) (h8 : StrForm (storageAt S C 8)) :
    Writes C BalOrAllow S S' ∧ ∀ n, Protected n → storageAt S' C n = storageAt S C n := by
  refine seq_lift (I := Plain C)
    (R := fun X Y => Writes C BalOrAllow X Y ∧ ∀ n, Protected n → storageAt Y C n = storageAt X C n)
    (fun S => ⟨Writes.refl _ _ S, fun _ _ => rfl⟩)
    (fun h1 h2 => ⟨h1.1.trans h2.1, fun n hn => (h2.2 n hn).trans (h1.2 n hn)⟩)
    (fun hu hP => ⟨⟨.of_same hu, fun n _ => hu n⟩, plain_of_untouched hu hP⟩) ?_ h ⟨hdep, h7, h8⟩
  intro S S' fork message hr hq hP
  obtain ⟨hno, K⟩ := hq
  obtain ⟨hdep, h7, h8⟩ := hP
  obtain ⟨hC, he⟩ := hr.effect hdep h7 h8
  subst hC
  have hwK := he.nonOwnerK K.toSepOn hno
  exact ⟨⟨he.nonOwner hno, fun n hn => hwK n (protected_not_kba K hn)⟩,
    plain_of_writes K.toSepOn hwK ⟨hdep, h7, h8⟩⟩

/-! ## Deprecated or not -/

/-- Every `Protected` slot of `C` keeps its word from `S` to `S'`. -/
def ProtKept (C : Address) (S S' : State.TransactionState) : Prop :=
  ∀ n, Protected n → storageAt S' C n = storageAt S C n

/-- The runner assumption of access control when deprecated: every call from `C` to `ua` that the
runner ends with no error leaves every `Protected` slot of `C` as it was in the caller state. -/
def KeepsSlots {fork : Fork} {bound : Nat} (runChild : MessageRunner fork Nat bound)
    (C ua : Address) : Prop :=
  Keeps runChild C ua (ProtKept C)

theorem EffectD.protKept {S S' : State.TransactionState} (K : SecSep (callKeys message S))
    (h : EffectD runChild message S S')
    (hno : callerWord message ≠ ownerOf S message.currentTarget)
    (hk : byte20 (storageAt S message.currentTarget 10) ≠ 0 →
      KeepsSlots runChild message.currentTarget (upAddr S message)) :
    ProtKept message.currentTarget S S' := by
  cases h with
  | loc h => exact fun n hn => h.nonOwnerK K.toSepOn hno n (protected_not_kba K hn)
  | fwd hdep _ _ _ X hX hf => exact fun n hn => ((hk hdep).fwd hf n hn).trans (hX n)
  | dfwd _ _ howner => exact absurd howner hno

/-- **Access control, one call, deprecated or not.** As `nonOwner_call` without `hdep`: when
deprecated, the runner meets `KeepsSlots` for the calls to the upgraded address (`hkeeps`). If
the caller is not the owner and the run ends with no error, every `Protected` slot keeps its
word. -/
theorem nonOwner_call_all (K : SecSep (callKeys message state)) (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (h7 : StrForm (storageAt state message.currentTarget 7))
    (h8 : StrForm (storageAt state message.currentTarget 8))
    (hno : callerWord message ≠ ownerOf state message.currentTarget)
    (hkeeps : byte20 (storageAt state message.currentTarget 10) ≠ 0 →
      KeepsSlots runChild message.currentTarget (upAddr state message))
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) : ProtKept message.currentTarget state s.state :=
  (effect_all hfork hsize' h7 h8 start within hrun hok).protKept K hno hkeeps

/-- The selectors of the ten functions with the `onlyOwner` check: deprecate, addBlackList,
unpause, pause, setParams, issue, redeem, removeBlackList, transferOwnership,
destroyBlackFunds. -/
def OwnerFn (x : Nat) : Prop :=
  x = 0x0753c30c ∨ x = 0x0ecb93c0 ∨ x = 0x3f4ba83a ∨ x = 0x8456cb59 ∨ x = 0xc0324c77 ∨
    x = 0xcc872b66 ∨ x = 0xdb006a75 ∨ x = 0xe4997dc5 ∨ x = 0xf2fde38b ∨ x = 0xf3bdc228

/-- **Owner functions, deprecated or not.** From Berlin (Glamsterdam included), a fresh frame of
`CODE` at pc 0, static or not, any call data below 2^256 bytes, any value, any gas, any gas bound
and any message runner, deprecated or not, no assumption on the runner: every run of one of the
ten owner functions that ends with no error is a call by the owner (the low 160 bits of slot 0
at the start). destroyBlackFunds, when deprecated, checks the owner before its call. -/
theorem owner_only (hfork : .berlin ≤ fork) (hsize' : message.data.size < 2 ^ 256)
    (hsel : OwnerFn (selector message.data))
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) : callerWord message = ownerOf state message.currentTarget := by
  rcases hsel with h | h | h | h | h | h | h | h | h | h
  · exact (ok_deprecate hfork hsize' h rfl rfl start within hrun hok).2.2.1
  · exact (ok_addBlackList hfork hsize' h rfl rfl start within hrun hok).2.2.1
  · exact (ok_unpause hfork hsize' h rfl start within hrun hok).2.2.1
  · exact (ok_pause hfork hsize' h rfl start within hrun hok).2.2.1
  · exact (ok_setParams hfork hsize' h rfl rfl rfl rfl start within hrun hok).2.2.1
  · exact (ok_issue hfork hsize' h rfl rfl rfl start within hrun hok).2.2.1
  · exact (ok_redeem hfork hsize' h rfl rfl rfl start within hrun hok).2.2.1
  · exact (ok_removeBlackList hfork hsize' h rfl rfl start within hrun hok).2.2.1
  · exact (ok_transferOwnership hfork hsize' h rfl start within hrun hok).1
  · by_cases hdep : byte20 (storageAt state message.currentTarget 10) = 0
    · exact (ok_destroyBlackFunds hfork hsize' h hdep rfl rfl rfl rfl rfl start within hrun
        hok).2.2.1
    · obtain ⟨_, _, -, -, howner, -⟩ :=
        dep_destroy_complete hfork hsize' h hdep rfl rfl rfl rfl start within hrun hok
      exact howner

/-- **Access control without a runner assumption, deprecated or not.** As `nonOwner_call` without
`hdep`, for every function other than the six that forward when deprecated (`FwdFn`): if the
caller is not the owner and the run ends with no error, only slots of `balances` and `allowed`
change, and under `SecSep` of the call's keys every `Protected` slot keeps its word. -/
theorem nonOwner_local (K : SecSep (callKeys message state)) (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (hsel : ¬ FwdFn (selector message.data))
    (h7 : StrForm (storageAt state message.currentTarget 7))
    (h8 : StrForm (storageAt state message.currentTarget 8))
    (hno : callerWord message ≠ ownerOf state message.currentTarget)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) :
    Writes message.currentTarget BalOrAllow state s.state ∧
      ProtKept message.currentTarget state s.state := by
  by_cases hd : selector message.data = 0xf3bdc228
  · exact absurd (owner_only hfork hsize' (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr
      hd))))))))) start within hrun hok) hno
  have he := effect_local hfork hsize' (.inr (fun h => h.elim hsel hd)) h7 h8 start within hrun hok
  exact ⟨he.nonOwner hno, fun n hn => he.nonOwnerK K.toSepOn hno n (protected_not_kba K hn)⟩

/-- The predicate of the sequences of non-owner calls, deprecated or not: the caller is not the
owner of the call's start state, slots 7 and 8 are of `StrForm` there, and `SecSep` holds for the
call's keys there (round 29). -/
def NotOwnerS {fork : Fork} (message : Message fork) (S : State.TransactionState) : Prop :=
  NotOwner message S ∧ Strs message S ∧ SecSep (callKeys message S)

/-- **Access control over a sequence, deprecated or not.** Along a finite sequence of successful
calls to `C`, each by a caller other than the owner of its start state, with slots 7 and 8 of
`StrForm` there, and whose runner meets `KeepsSlots` when `C` is deprecated at that state, and of
`Untouched` steps, each call with `SecSep` of its keys: every `Protected` slot keeps its word. -/
theorem nonOwner_seq_all {C : Address}
    {S S' : State.TransactionState} (h : SeqR C (ProtKept C) NotOwnerS S S') :
    ProtKept C S S' := by
  refine seqR_lift (I := fun _ => True) (R := ProtKept C) (fun _ _ _ => rfl)
    (fun h1 h2 n hn => (h2 n hn).trans (h1 n hn)) (fun hu _ => ⟨fun n _ => hu n, trivial⟩) ?_ h
    trivial
  intro S S' fork message hr hq _
  obtain ⟨hno, ⟨h7, h8⟩, K⟩ := hq
  have hC : message.currentTarget = C := by obtain ⟨_, _, _, _, _, _, _, hC, -⟩ := hr; exact hC
  subst hC
  obtain ⟨-, bound, runChild, he, hk⟩ := hr.effect h7 h8
  exact ⟨he.protKept K hno hk, trivial⟩

end UsdtVerify.Security
