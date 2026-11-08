import UsdtVerify.Usdt.Security.DepMeter

/-!
# The security properties over sequences, deprecated or not, over the EIP-8037 meter (round 41)

The `_seq_all` theorems of Usdt/Security/ (sequences of `SeqR`, calls over the meter `Nat`,
deprecated or not) for sequences whose calls run over the meter `Nat` or over `StateGasMeter`.

- `EffectD.toF`: `EffectD` of a runner over `Nat` is `EffectDF` for its calls (`FwdAt`).
- `RunOkRS C R S S' message`: one successful run of `CODE` over `StateGasMeter` for a message to
  `C`, from `S` to `S'`, from a frame with reservoir 0 when `C` is deprecated at `S`, whose runner
  meets `KeepsAtS … R` when `C` is deprecated at `S`. `RunOkRS.effect` and `RunOkR.effectF`: each
  step ends as `EffectDF F` for a relation `F` that implies `R` when deprecated.
- `SeqRS C R Q`: finite sequences of `RunOkR` steps (meter `Nat`), `RunOkRS` steps
  (`StateGasMeter`), each meeting `Q` on its message and start state, and `Untouched` steps.
  `seqRS_lift`: a relation that is reflexive, transitive, kept by `Untouched` steps and by every
  step that ends as such an `EffectDF` holds along the sequence.
- `nonOwner_seq_allS`, `paused_seq_allS`, `listed_seq_allS`, `allowKept_seq_allS`,
  `supply_seq_allS`: the five `_seq_all` theorems over `SeqRS`, with the same predicates on each
  call and the same runner relations.
- `runOkRS_process`, `process_stepSecD`: from Paris, a top-level message to `C` (code `CODE`, no
  precompile, call data below 2^256 bytes) run by EthLib's `processMessage` over `StateGasMeter`
  from any starting meter, with reservoir 0 when `C` is deprecated, whose runner meets
  `KeepsAtS … R` when deprecated, is a `RunOkRS` step when it ends with no error and an
  `Untouched` step otherwise.

Usdt/Security/DepMeterR.lean (round 44) has the sequence forms with calls from any reservoir
(`SeqRSR`, `SeqRS.toRSR`).
-/

namespace UsdtVerify.Security

open EthLib.Base (Fork U256 Address)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open UsdtVerify.Meter (toNat)
open Invariant Complete Deprecated

/-- `EffectD` of a runner over `Nat` is `EffectDF` with the calls of that runner (`FwdAt`). -/
theorem EffectD.toF {fork : Fork} {bound : Nat} {runChild : MessageRunner fork Nat bound}
    {message : Message fork} {S S' : State.TransactionState}
    (h : EffectD runChild message S S') :
    EffectDF (FwdAt runChild message S (upAddr S message)) message S S' := by
  cases h with
  | loc h => exact .loc h
  | fwd hdep hsel hT hF X hX hf => exact .fwd hdep hsel hT hF X hX hf
  | dfwd hdep hsel howner hlisted X Y d hX hf hacc hst =>
    exact .dfwd hdep hsel howner hlisted X Y d hX hf hacc hst

/-- One successful run of `CODE` over `StateGasMeter` for a message to `C`, from `S` to `S'`, any
gas bound and runner, from a frame whose `toNat` is the fresh frame of `CODE`: when `C` is
deprecated at `S`, the frame has reservoir 0 and the runner meets `KeepsAtS … R` for the calls
the code makes from `S` to the upgraded address. -/
def RunOkRS (C : Address) (R : State.TransactionState → State.TransactionState → Prop)
    (S S' : State.TransactionState) {fork : Fork} (message : Message fork) : Prop :=
  ∃ (substate : Substate) (gas bound : Nat) (runS : MessageRunner fork StateGasMeter bound)
    (m s : Evm fork StateGasMeter) (within : GasMeter.gasHeld m.gas ≤ bound),
    message.currentTarget = C ∧ .berlin ≤ fork ∧ message.data.size < 2 ^ 256 ∧
    (byte20 (storageAt S C 10) ≠ 0 → KeepsAtS runS message S (upAddr S message) R) ∧
    (byte20 (storageAt S C 10) ≠ 0 → m.gas.reservoir = 0) ∧
    At CODE message 0 [] .empty gas S substate (toNat m) ∧
    Evm.runFrame (step fork) (step_decreases fork) bound runS m within = .ok s ∧
    s.error = none ∧ S' = s.state

/-- `effect_allS` for a `RunOkRS` step, with the runner assumption. -/
theorem RunOkRS.effect {C : Address} {R : State.TransactionState → State.TransactionState → Prop}
    {S S' : State.TransactionState} {fork : Fork} {message : Message fork}
    (h : RunOkRS C R S S' message)
    (h7 : StrForm (storageAt S message.currentTarget 7))
    (h8 : StrForm (storageAt S message.currentTarget 8)) :
    message.currentTarget = C ∧ ∃ F : State.TransactionState → State.TransactionState → Prop,
      EffectDF F message S S' ∧ (byte20 (storageAt S C 10) ≠ 0 → ∀ X Y, F X Y → R X Y) := by
  obtain ⟨substate, gas, bound, runS, m, s, within, hC, hfork, hsize, hk, hres, start, hrun, hok,
    rfl⟩ := h
  subst hC
  exact ⟨rfl, _, effect_allS hfork hsize h7 h8 start hres hrun hok,
    fun hd _ _ hf => (hk hd).fwd hf⟩

/-- `RunOkR.effect` in the form of `RunOkRS.effect`. -/
theorem RunOkR.effectF {C : Address} {R : State.TransactionState → State.TransactionState → Prop}
    {S S' : State.TransactionState} {fork : Fork} {message : Message fork}
    (h : RunOkR C R S S' message)
    (h7 : StrForm (storageAt S message.currentTarget 7))
    (h8 : StrForm (storageAt S message.currentTarget 8)) :
    message.currentTarget = C ∧ ∃ F : State.TransactionState → State.TransactionState → Prop,
      EffectDF F message S S' ∧ (byte20 (storageAt S C 10) ≠ 0 → ∀ X Y, F X Y → R X Y) := by
  have hC : message.currentTarget = C := by obtain ⟨_, _, _, _, _, _, _, hC, -⟩ := h; exact hC
  subst hC
  obtain ⟨-, _, _, he, hk⟩ := h.effect h7 h8
  exact ⟨rfl, _, he.toF, fun hd _ _ hf => (hk hd).fwd hf⟩

/-- A finite sequence of calls to `C` over the meter `Nat` (`RunOkR`) or over `StateGasMeter`
(`RunOkRS`), each meeting `Q` on its message and its start state, and of changes that keep every
storage word of `C`. -/
inductive SeqRS (C : Address) (R : State.TransactionState → State.TransactionState → Prop)
    (Q : ∀ {fork : Fork}, Message fork → State.TransactionState → Prop) :
    State.TransactionState → State.TransactionState → Prop
  | nil (S : State.TransactionState) : SeqRS C R Q S S
  | call {S S' S'' : State.TransactionState} {fork : Fork} {message : Message fork} :
      RunOkR C R S S' message → Q message S → SeqRS C R Q S' S'' → SeqRS C R Q S S''
  | callS {S S' S'' : State.TransactionState} {fork : Fork} {message : Message fork} :
      RunOkRS C R S S' message → Q message S → SeqRS C R Q S' S'' → SeqRS C R Q S S''
  | other {S S' S'' : State.TransactionState} : Untouched C S S' → SeqRS C R Q S' S'' →
      SeqRS C R Q S S''

/-- Every `SeqR` sequence is a `SeqRS` sequence. -/
theorem SeqR.toRS {C : Address} {R : State.TransactionState → State.TransactionState → Prop}
    {Q : ∀ {fork : Fork}, Message fork → State.TransactionState → Prop}
    {S S' : State.TransactionState} (h : SeqR C R Q S S') : SeqRS C R Q S S' := by
  induction h with
  | nil S => exact .nil S
  | call hr hq _ ih => exact .call hr hq ih
  | other hu _ ih => exact .other hu ih

/-- `seqR_lift` for `SeqRS`: each call is given by the `EffectDF` it ends as. The predicate `Q`
of each call gives the string slots of its start state (`Strs`). -/
theorem seqRS_lift {C : Address} {R0 : State.TransactionState → State.TransactionState → Prop}
    {Q : ∀ {fork : Fork}, Message fork → State.TransactionState → Prop}
    {I : State.TransactionState → Prop} {R : State.TransactionState → State.TransactionState → Prop}
    (hQ : ∀ {fork : Fork} {message : Message fork} {S : State.TransactionState}, Q message S →
      Strs message S)
    (hrefl : ∀ S, R S S) (htrans : ∀ {S S' S''}, R S S' → R S' S'' → R S S'')
    (hother : ∀ {S S'}, Untouched C S S' → I S → R S S' ∧ I S')
    (hcall : ∀ {S S'} {fork : Fork} {message : Message fork}
      (F : State.TransactionState → State.TransactionState → Prop),
      message.currentTarget = C → EffectDF F message S S' →
      (byte20 (storageAt S C 10) ≠ 0 → ∀ X Y, F X Y → R0 X Y) →
      Q message S → I S → R S S' ∧ I S')
    {S S' : State.TransactionState} (h : SeqRS C R0 Q S S') (hI : I S) : R S S' := by
  induction h with
  | nil S => exact hrefl S
  | call hr hq _ ih =>
    obtain ⟨hC, F, he, hk⟩ := hr.effectF (hQ hq).1 (hQ hq).2
    obtain ⟨hR, hI'⟩ := hcall F hC he hk hq hI
    exact htrans hR (ih hI')
  | callS hr hq _ ih =>
    obtain ⟨hC, F, he, hk⟩ := hr.effect (hQ hq).1 (hQ hq).2
    obtain ⟨hR, hI'⟩ := hcall F hC he hk hq hI
    exact htrans hR (ih hI')
  | other hu _ ih =>
    obtain ⟨hR, hI'⟩ := hother hu hI
    exact htrans hR (ih hI')

/-- **Access control over a sequence over both meters, deprecated or not.** `nonOwner_seq_all`
for `SeqRS`: along a finite sequence of successful calls to `C` over the meter `Nat` or over
`StateGasMeter` (reservoir 0 when deprecated), each by a caller other than the owner of its start
state, with slots 7 and 8 of `StrForm` and `SecSep` of its keys there, whose runner meets
`KeepsAt` (or `KeepsAtS`) for `ProtKept C` when `C` is deprecated at that state, and of `Untouched`
steps: every `Protected` slot keeps its word. -/
theorem nonOwner_seq_allS {C : Address} {S S' : State.TransactionState}
    (h : SeqRS C (ProtKept C) NotOwnerS S S') : ProtKept C S S' := by
  refine seqRS_lift (I := fun _ => True) (R := ProtKept C) (fun hq => hq.2.1) (fun _ _ _ => rfl)
    (fun h1 h2 n hn => (h2 n hn).trans (h1 n hn)) (fun hu _ => ⟨fun n _ => hu n, trivial⟩) ?_ h
    trivial
  intro S S' fork message F hC he hk hq _
  obtain ⟨hno, -, K⟩ := hq
  subst hC
  exact ⟨he.protKept K hno hk, trivial⟩

/-- **Pause over a sequence over both meters, deprecated or not.** `paused_seq_all` for `SeqRS`:
along a finite sequence of successful calls to `C` over the meter `Nat` or over `StateGasMeter`
(reservoir 0 when deprecated) by callers other than the owner (of each call's start state, with
slots 7 and 8 of `StrForm` and `SecSep` of its keys there), whose runner, when `C` is deprecated
at that state, meets `KeepsAt` (or `KeepsAtS`) for both `ProtKept C` and `BalKept C`, and of
`Untouched` steps, from a state where `C` is paused: every balance keeps its word. -/
theorem paused_seq_allS {C : Address} {S S' : State.TransactionState}
    (h : SeqRS C (fun X Y => ProtKept C X Y ∧ BalKept C X Y) NotOwnerS S S')
    (hpaused : byte20 (storageAt S C 0) ≠ 0) : BalKept C S S' := by
  refine seqRS_lift (I := fun X => byte20 (storageAt X C 0) ≠ 0) (R := BalKept C)
    (fun hq => hq.2.1) (fun _ _ _ => rfl) (fun h1 h2 x hx => (h2 x hx).trans (h1 x hx))
    (fun hu hI => ⟨fun _ _ => hu _, by rw [hu]; exact hI⟩) ?_ h hpaused
  intro S S' fork message F hC he hk hq hp
  obtain ⟨hno, -, K⟩ := hq
  subst hC
  have hprot := he.protKept K hno (fun hd X Y hf => (hk hd X Y hf).1)
  refine ⟨?_, by rw [hprot 0 (.inl rfl)]; exact hp⟩
  rcases he.paused K.toSepOn hp (fun hd X Y hf => (hk hd X Y hf).2) with hb | ⟨howner, -⟩
  · exact hb
  · exact absurd howner hno

/-- **Blacklist over a sequence over both meters, deprecated or not.** `listed_seq_all` for
`SeqRS`: along a finite sequence of successful calls to `C` over the meter `Nat` or over
`StateGasMeter` (reservoir 0 when deprecated) by callers other than the owner (of each call's
start state, with slots 7 and 8 of `StrForm` and `SecSep` of its keys there), whose runner, when
`C` is deprecated at that state, meets `KeepsAt` (or `KeepsAtS`) for both `ProtKept C` and
`ListedNoDec C`, and of `Untouched` steps, from a state where the address word `a < 2^160` is
blacklisted: `balances[a]` is not lower at the end. -/
theorem listed_seq_allS {C : Address} {S S' : State.TransactionState}
    (h : SeqRS C (fun X Y => ProtKept C X Y ∧ ListedNoDec C X Y) NotOwnerS S S')
    {a : U256} (ha : a.toNat < 2 ^ 160) (hl : Listed C S a) : NoDec C (mapSlot a 2) S S' := by
  refine seqRS_lift (I := fun X => Listed C X a) (R := NoDec C (mapSlot a 2))
    (fun hq => hq.2.1) (fun _ => NoDec.refl _ _ _) (fun h1 h2 => h1.trans h2)
    (fun hu hI => ⟨NoDec.of_writes (W := fun _ => False) (.of_same hu) id,
      by unfold Listed; rw [hu]; exact hI⟩) ?_ h hl
  intro S S' fork message F hC he hk hq hl
  obtain ⟨hno, -, K⟩ := hq
  subst hC
  have hprot := he.protKept K hno (fun hd X Y hf => (hk hd X Y hf).1)
  refine ⟨he.listed K.toSepOn ha hl (.inr hno) (fun hd X Y hf => (hk hd X Y hf).2), ?_⟩
  unfold Listed
  rw [hprot _ (.inr (.inr (.inr (.inr (.inr ⟨a, ha, rfl⟩)))))]
  exact hl

/-- **Allowances over a sequence over both meters, deprecated or not.** `allowKept_seq_all` for
`SeqRS`: along a finite sequence of successful calls to `C` over the meter `Nat` or over
`StateGasMeter` (reservoir 0 when deprecated) that are neither approve nor transferFrom (with
slots 7 and 8 of `StrForm` and `SecSep` of its keys and `y`, `z` at each call's start state),
whose runner meets `KeepsAt` (or `KeepsAtS`) for `AllowKept C` when `C` is deprecated at that
state, and of `Untouched` steps: the slot of `allowed` keyed by `y` and `z` keeps its word.
Callers may be the owner. -/
theorem allowKept_seq_allS {y z : U256} {C : Address} {S S' : State.TransactionState}
    (h : SeqRS C (AllowKept C) (@NoAllowFnS y z) S S') : AllowKeptAt y z C S S' := by
  refine seqRS_lift (I := fun _ => True) (R := AllowKeptAt y z C) (fun hq => hq.2.2.1)
    (fun _ => rfl) (fun h1 h2 => h2.trans h1) (fun hu _ => ⟨hu _, trivial⟩) ?_ h trivial
  intro S S' fork message F hC he hk hq _
  obtain ⟨ha, hf, -, K⟩ := hq
  subst hC
  exact ⟨he.allowKept K ⟨ha, hf⟩ hk, trivial⟩

/-- **Supply over a sequence over both meters, deprecated or not.** `supply_seq_all` for `SeqRS`:
along a finite sequence of successful calls to `C` over the meter `Nat` or over `StateGasMeter`
(reservoir 0 when deprecated) that are none of issue, redeem and destroyBlackFunds (with slots 7
and 8 of `StrForm` and `SepOn` of its keys at each call's start state), whose runner meets
`KeepsAt` (or `KeepsAtS`) for `SupplyKept C` when `C` is deprecated at that state, and of
`Untouched` steps: slot 1 keeps its word. Callers may be the owner. -/
theorem supply_seq_allS {C : Address} {S S' : State.TransactionState}
    (h : SeqRS C (SupplyKept C) NoSupplyFnS S S') : storageAt S' C 1 = storageAt S C 1 := by
  refine seqRS_lift (I := fun _ => True) (R := fun X Y => storageAt Y C 1 = storageAt X C 1)
    (fun hq => hq.2.2.2.1) (fun _ => rfl) (fun h1 h2 => h2.trans h1)
    (fun hu _ => ⟨hu 1, trivial⟩) ?_ h trivial
  intro S S' fork message F hC he hk hq _
  obtain ⟨hi, hr', hd, -, K⟩ := hq
  subst hC
  refine ⟨?_, trivial⟩
  rcases he.supply K hk with (h1 | ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩) | ⟨e, -⟩
  · exact h1
  · exact absurd e hi
  · exact absurd e hr'
  · exact absurd e hd
  · exact absurd e hd

/-! ## Top-level messages -/

/-- From Paris, a top-level message whose code is `CODE` (no value moved, no precompile, call data
below 2^256 bytes), run by EthLib's `processMessage` over `StateGasMeter` from a starting meter
with reservoir 0 when `C` is deprecated, whose runner `processRunnerM` meets `KeepsAtS … R` when
`C` is deprecated, that ends with no error, is a `RunOkRS` step. -/
theorem runOkRS_process {fork : Fork} (hparis : .paris ≤ fork)
    {message : Message fork} {state : State.TransactionState} {substate : Substate}
    {R : State.TransactionState → State.TransactionState → Prop}
    (hmc : message.code = CODE)
    (noValue : ¬(message.shouldTransferValue = true ∧ message.value ≠ 0))
    (noPrecompile : precompileAddress fork message = none)
    (hsize : message.data.size < 2 ^ 256)
    (hkeeps : byte20 (storageAt state message.currentTarget 10) ≠ 0 →
      KeepsAtS (ProcessMeter.processRunnerM fork message.gas) message state
        (upAddr state message) R)
    {meter : StateGasMeter} {held : GasMeter.gasHeld meter ≤ message.gas}
    (hres : byte20 (storageAt state message.currentTarget 10) ≠ 0 → meter.reservoir = 0)
    {ended : { evm : Evm fork StateGasMeter // GasMeter.gasHeld evm.gas ≤ message.gas }}
    (hproc : processMessage fork message state substate meter held = .ok ended)
    (hok : ended.val.error = none) :
    RunOkRS message.currentTarget R state ended.val.state message := by
  have hst : startState fork message state = state := by
    simp only [startState, show ¬fork < Fork.paris from Nat.not_lt.mpr hparis, ite_false]
  have hberlin : Fork.berlin ≤ fork := Nat.le_trans (by decide) hparis
  generalize hr : runFrame (step fork) (step_decreases fork) message.gas
    (ProcessMeter.processRunnerM fork message.gas)
    (startFrame message (startState fork message state) substate meter) held = result
  have hmap := ProcessMeter.processMessage_map_valM noValue noPrecompile hr
  rw [hproc] at hmap
  rcases result with e | s
  · cases hmap
  · simp only [Except.map, Except.ok.injEq] at hmap
    have hse : s.error = none := by
      rw [← hok, hmap]
      unfold rollbackOnError
      split <;> rfl
    have hend : ended.val = s := by
      rw [hmap]
      unfold rollbackOnError
      simp [hse]
    have start := ProcessMeter.at_startFrameS hmc (startState fork message state) substate meter
    rw [hst] at start hr
    exact ⟨substate, _, message.gas, ProcessMeter.processRunnerM fork message.gas, _, s, _, rfl,
      hberlin, hsize, hkeeps, hres, start, hr, hse, by rw [hend]⟩

/-- **Top-level messages over the EIP-8037 meter, deprecated or not, as steps of `SeqRS`.** From
Paris, every top-level message whose code is `CODE` (no precompile, call data below 2^256 bytes,
any value), run by EthLib's `processMessage` over `StateGasMeter` to the end, from a starting
meter with reservoir 0 when `C` is deprecated, whose runner `processRunnerM` meets `KeepsAtS … R`
when `C` is deprecated, is a `RunOkRS` step when it ends with no error and an `Untouched` step
when it ends with an error. -/
theorem process_stepSecD {fork : Fork} (hparis : .paris ≤ fork)
    {message : Message fork} {state : State.TransactionState} {substate : Substate}
    {R : State.TransactionState → State.TransactionState → Prop}
    (hmc : message.code = CODE)
    (noPrecompile : precompileAddress fork message = none)
    (hsize : message.data.size < 2 ^ 256)
    (hkeeps : byte20 (storageAt state message.currentTarget 10) ≠ 0 →
      KeepsAtS (ProcessMeter.processRunnerM fork message.gas) message state
        (upAddr state message) R)
    {meter : StateGasMeter} {held : GasMeter.gasHeld meter ≤ message.gas}
    (hres : byte20 (storageAt state message.currentTarget 10) ≠ 0 → meter.reservoir = 0)
    {ended : { evm : Evm fork StateGasMeter // GasMeter.gasHeld evm.gas ≤ message.gas }}
    (hproc : processMessage fork message state substate meter held = .ok ended) :
    RunOkRS message.currentTarget R state ended.val.state message ∨
      Untouched message.currentTarget state ended.val.state := by
  by_cases herr : ended.val.error = none
  · by_cases ht : message.shouldTransferValue = true ∧ message.value ≠ 0
    · exact absurd herr (process_value_failsS (Nat.le_trans (by decide) hparis) hmc noPrecompile
        hsize ht.2 hproc)
    · exact .inl (runOkRS_process hparis hmc ht noPrecompile hsize hkeeps hres hproc herr)
  · exact .inr (fun _ => Local.processMessage_failed_getStorage hproc herr _ _)

end UsdtVerify.Security
