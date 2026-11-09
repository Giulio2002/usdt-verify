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
- `runOkRS_process`, `process_stepSecD`: from Paris, a top-level message to `C` (code `CODE`, no
  precompile, call data below 2^256 bytes) run by EthLib's `processMessage` over `StateGasMeter`
  from any starting meter, with reservoir 0 when `C` is deprecated, whose runner meets
  `KeepsAtS … R` when deprecated, is a `RunOkRS` step when it ends with no error and an
  `Untouched` step otherwise.

Usdt/Security/DepMeterR.lean (round 44) has the five `_seq_all` theorems over `SeqRSR`, whose
calls start from any reservoir (`X_seq_allSR`); every `SeqRS` sequence is a `SeqRSR` sequence
(`SeqRS.toRSR`).
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
  exact ⟨rfl, _, he.toF, fun hd _ _ hf => hf.keeps (hk hd)⟩

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

/-! ## Top-level messages -/

/-- From Paris, a top-level message whose code is `CODE` (no value moved, no precompile, call data
below 2^256 bytes), run by EthLib's `processMessage` over `StateGasMeter` from a starting meter
with reservoir 0 when `C` is deprecated, whose runner `processRunner` meets `KeepsAtS … R` when
`C` is deprecated, that ends with no error, is a `RunOkRS` step. -/
theorem runOkRS_process {fork : Fork} (hparis : .paris ≤ fork)
    {message : Message fork} {state : State.TransactionState} {substate : Substate}
    {R : State.TransactionState → State.TransactionState → Prop}
    (hmc : message.code = CODE)
    (noValue : ¬(message.shouldTransferValue = true ∧ message.value ≠ 0))
    (noPrecompile : precompileAddress fork message = none)
    (hsize : message.data.size < 2 ^ 256)
    (hkeeps : byte20 (storageAt state message.currentTarget 10) ≠ 0 →
      KeepsAtS (processRunner fork message.gas) message state
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
    (processRunner fork message.gas)
    (startFrame message (startState fork message state) substate meter) held = result
  have hmap := processMessage_map_val noValue noPrecompile hr
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
    have start := Meter.at_startFrameS hmc (startState fork message state) substate meter
    rw [hst] at start hr
    exact ⟨substate, _, message.gas, processRunner fork message.gas, _, s, _, rfl,
      hberlin, hsize, hkeeps, hres, start, hr, hse, by rw [hend]⟩

/-- **Top-level messages over the EIP-8037 meter, deprecated or not, as steps of `SeqRS`.** From
Paris, every top-level message whose code is `CODE` (no precompile, call data below 2^256 bytes,
any value), run by EthLib's `processMessage` over `StateGasMeter` to the end, from a starting
meter with reservoir 0 when `C` is deprecated, whose runner `processRunner` meets `KeepsAtS … R`
when `C` is deprecated, is a `RunOkRS` step when it ends with no error and an `Untouched` step
when it ends with an error. -/
theorem process_stepSecD {fork : Fork} (hparis : .paris ≤ fork)
    {message : Message fork} {state : State.TransactionState} {substate : Substate}
    {R : State.TransactionState → State.TransactionState → Prop}
    (hmc : message.code = CODE)
    (noPrecompile : precompileAddress fork message = none)
    (hsize : message.data.size < 2 ^ 256)
    (hkeeps : byte20 (storageAt state message.currentTarget 10) ≠ 0 →
      KeepsAtS (processRunner fork message.gas) message state
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
  · exact .inr fun _ =>
      getStorage_processMessage_of_error hproc (Option.isSome_iff_ne_none.mpr herr) _ _


/-! ## One top-level message, to each security property (round 49) -/

end UsdtVerify.Security
