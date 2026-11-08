import UsdtVerify.Usdt.Security.Supply
import UsdtVerify.Usdt.Invariant.SeqMeter

/-!
# The steps of the security sequences from EthLib's `processMessage` over `StateGasMeter`

Round 37. The sequence theorems `nonOwner_seqS`, `paused_seqS`, `listed_seqS`, `allowKept_seqS`
and `supply_seqS` take a `SeqS`, whose calls are `RunOk` (meter `Nat`) or `RunOkS` (meter
`StateGasMeter`) steps.

- `runOkS_process`: from Paris, a top-level message to `C` (code `CODE`, no value moved, no
  precompile, call data below 2^256 bytes) run by `processMessage` over `StateGasMeter`, from any
  starting meter, that ends with no error is a `RunOkS` step from its start state to its end
  state. No hypothesis on the starting meter, on the reservoir, on refills or on the gas limit.
- `process_stepSec`: from Paris, every such message (any value) that `processMessage` ends over
  `StateGasMeter`, from any starting meter, is a `RunOkS` step or an `Untouched` step.
- `runOkS_process_start`, `process_stepSec_start`: the same for the fresh meter of the message,
  which `processMessage` takes by default.
-/

namespace UsdtVerify.Security

open EthLib.Base (Fork U256 Address)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open UsdtVerify.Meter
open UsdtVerify.ProcessMeter
open Invariant Complete

/-- From Paris, a top-level message whose code is `CODE` (no value moved, no precompile, call data
below 2^256 bytes), run by EthLib's `processMessage` over `StateGasMeter` from any starting meter,
that ends with no error, is a `RunOkS` step from its start state to its end state. -/
theorem runOkS_process {fork : Fork} (hparis : .paris ≤ fork)
    {message : Message fork} {state : State.TransactionState} {substate : Substate}
    (hmc : message.code = CODE)
    (noValue : ¬(message.shouldTransferValue = true ∧ message.value ≠ 0))
    (noPrecompile : precompileAddress fork message = none)
    (hsize : message.data.size < 2 ^ 256)
    {meter : StateGasMeter} {held : GasMeter.gasHeld meter ≤ message.gas}
    {ended : { evm : Evm fork StateGasMeter // GasMeter.gasHeld evm.gas ≤ message.gas }}
    (hproc : processMessage fork message state substate meter held = .ok ended)
    (hok : ended.val.error = none) :
    RunOkS message.currentTarget state ended.val.state message := by
  have hst : startState fork message state = state := by
    simp only [startState, show ¬fork < Fork.paris from Nat.not_lt.mpr hparis, ite_false]
  have hberlin : Fork.berlin ≤ fork := Nat.le_trans (by decide) hparis
  generalize hres : runFrame (step fork) (step_decreases fork) message.gas
    (processRunnerM fork message.gas)
    (startFrame message (startState fork message state) substate meter) held = result
  have hmap := processMessage_map_valM noValue noPrecompile hres
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
    have start := at_startFrameS hmc (startState fork message state) substate meter
    rw [hst] at start hres
    exact ⟨substate, _, message.gas, processRunnerM fork message.gas, _, s, _, rfl, hberlin, hsize,
      start, hres, hse, by rw [hend]⟩

/-- From Paris, every top-level message whose code is `CODE` (no precompile, call data below 2^256
bytes, any value), run by EthLib's `processMessage` over `StateGasMeter` from any starting meter
to the end, is a step of
a `SeqS` sequence of `C = message.currentTarget`: a `RunOkS` step when it ends with no error (its
value is then 0 or not moved, `process_value_failsS`), and an `Untouched` step when it ends with
an error. -/
theorem process_stepSec {fork : Fork} (hparis : .paris ≤ fork)
    {message : Message fork} {state : State.TransactionState} {substate : Substate}
    (hmc : message.code = CODE)
    (noPrecompile : precompileAddress fork message = none)
    (hsize : message.data.size < 2 ^ 256)
    {meter : StateGasMeter} {held : GasMeter.gasHeld meter ≤ message.gas}
    {ended : { evm : Evm fork StateGasMeter // GasMeter.gasHeld evm.gas ≤ message.gas }}
    (hproc : processMessage fork message state substate meter held = .ok ended) :
    RunOkS message.currentTarget state ended.val.state message ∨
      Untouched message.currentTarget state ended.val.state := by
  by_cases herr : ended.val.error = none
  · by_cases ht : message.shouldTransferValue = true ∧ message.value ≠ 0
    · exact absurd herr (process_value_failsS (Nat.le_trans (by decide) hparis) hmc noPrecompile
        hsize ht.2 hproc)
    · exact .inl (runOkS_process hparis hmc ht noPrecompile hsize hproc herr)
  · exact .inr (fun _ => Local.processMessage_failed_getStorage hproc herr _ _)

/-- `runOkS_process` for the fresh meter of the message. -/
theorem runOkS_process_start {fork : Fork} (hparis : .paris ≤ fork)
    {message : Message fork} {state : State.TransactionState} {substate : Substate}
    (hmc : message.code = CODE)
    (noValue : ¬(message.shouldTransferValue = true ∧ message.value ≠ 0))
    (noPrecompile : precompileAddress fork message = none)
    (hsize : message.data.size < 2 ^ 256)
    {ended : { evm : Evm fork StateGasMeter // GasMeter.gasHeld evm.gas ≤ message.gas }}
    (hproc : processMessage fork message state substate = .ok ended)
    (hok : ended.val.error = none) :
    RunOkS message.currentTarget state ended.val.state message :=
  runOkS_process hparis hmc noValue noPrecompile hsize hproc hok

/-- `process_stepSec` for the fresh meter of the message. -/
theorem process_stepSec_start {fork : Fork} (hparis : .paris ≤ fork)
    {message : Message fork} {state : State.TransactionState} {substate : Substate}
    (hmc : message.code = CODE)
    (noPrecompile : precompileAddress fork message = none)
    (hsize : message.data.size < 2 ^ 256)
    {ended : { evm : Evm fork StateGasMeter // GasMeter.gasHeld evm.gas ≤ message.gas }}
    (hproc : processMessage fork message state substate = .ok ended) :
    RunOkS message.currentTarget state ended.val.state message ∨
      Untouched message.currentTarget state ended.val.state :=
  process_stepSec hparis hmc noPrecompile hsize hproc

end UsdtVerify.Security
