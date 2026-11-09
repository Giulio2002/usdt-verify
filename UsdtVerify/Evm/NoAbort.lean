import UsdtVerify.Evm.GasRules
import EthLib.Execution.Proofs.Evm.Logic.NoAbort

/-!
# GENERIC: runs that never abort, at any gas

The loop of the interpreter (`runFrame`) returns an error only for an error that aborts the whole
run (`EvmError.aborts`: an error of the state, an opcode with no instruction, ...), or when the
runner of messages returns one. A run that halts with out of gas is a frame with an error, not
an error of the loop. The triples over `StepG` (Evm/Gas.lean) say how a run with more gas ends,
and with less gas the step may fail with any error. Here the failures with less gas are shown
to halt the frame.

EthLib's Logic/NoAbort.lean (#1616) gives `NoAbort r` (the result `r` is no error that aborts),
the facts `noAbort_pushN`, `noAbort_mstore`, ... (these instructions fail, on any frame, only
with errors that halt the frame) and `NoAbortLow x` (from every frame with less gas than `x`, the
step is no error that aborts). Round 48: the local copies of these are removed.

- In Evm/GasRules.lean (moved there in round 50): `StepGA`, a step of `StepG` (Evm/Gas.lean:
  EthLib's `Logic.StepG` with `SimAt`) from a frame that is `NoAbortLow`, which is EthLib's
  `Logic.StepGA` with `SimAt`. `HoareGA`, `SpecGA`: triples over it; they imply the triples over
  `StepG` (`SpecGA.toG`) and EthLib's `SpecGA` (`SpecGA.toLogic`). `At.ruleGA`: the rule of one
  opcode over `StepGA`, for an instruction that is `RunMono` and fails only with errors that
  halt. `pushGA`, `calldataloadGA`, `mstoreGA`, `keccak256GA`, `sloadGA`, `returnGA`: rules over
  `StepGA`, from which the rules of the same opcodes over `StepG` follow.
- `no_error_of_reaches`: EthLib's `no_error_of_reaches`, for `StepGA`.
- `no_error_ga`: if, with every gas from a bound `B` on, a `SpecGA` holds from a frame, then the
  loop run from that frame with ANY gas (also below `B`) returns a frame, never an error.
-/

namespace UsdtVerify.Gas

open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts

variable {fork : Fork}

/-! ## The loop never returns an error -/

section Loop

variable {bound : Nat} {runChild : MessageRunner fork Nat bound}

/-- Along a chain of `StepGA` from `addGas k l` to a stopped frame, the loop run from `l`
returns a frame, never an error: EthLib's `no_error_of_reaches`, for `StepGA`. -/
theorem no_error_of_reaches {hi z : Evm fork Nat} (hr : Reaches (StepGA fork) hi z)
    (hz : z.running = false) :
    ∀ (k : Nat) (l : Evm fork Nat), hi = addGas k l →
      ∀ (within : GasMeter.gasHeld l.gas ≤ bound) (e : EvmError),
        Evm.runFrame (step fork) (step_decreases fork) bound runChild l within ≠ .error e :=
  Logic.no_error_of_reaches (hr.mono fun hs => ⟨⟨hs.1.1, hs.1.2.2⟩, hs.2⟩) hz

/-- If, with every gas from `B` on, a `SpecGA` holds from a frame, then the loop run from that
frame with any gas returns a frame, never an error. -/
theorem no_error_ga {code : ByteArray} {message : Message fork} {pc : Nat} {stack : List U256}
    {memory : ByteArray} {state : State.TransactionState} {substate : Substate} {B : Nat}
    {Q : Nat → Evm fork Nat → Prop}
    (h : ∀ g, B ≤ g → SpecGA fork (At code message pc stack memory g state substate) (Q g))
    {gas : Nat} {evm : Evm fork Nat} (start : At code message pc stack memory gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) (e : EvmError) :
    Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within ≠ .error e := by
  obtain ⟨z, hr, hz, -⟩ := h (gas + B) (by omega) _ (at_addGas start B)
  exact no_error_of_reaches hr hz B evm rfl within e

end Loop

end UsdtVerify.Gas
