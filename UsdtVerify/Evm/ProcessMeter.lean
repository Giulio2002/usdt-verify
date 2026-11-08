import UsdtVerify.Evm.Meter
import UsdtVerify.Evm.Local.Parent

/-!
# EthLib's `processMessage` over any meter

EthLib's `processRunner`, `processMessage_map_val` and `processMessage_map_val_value`
(Execution/Proofs/Evm/Logic/Callee.lean) are stated for the meter `Nat`. Here they are stated for
any lawful meter, with the same proofs: `processRunnerM`, `processMessage_map_valM`,
`processMessage_map_val_valueM`, for a message whose frame starts with any meter `meter` (EthLib's
`processMessageCall` passes the meter left by the preparation of the first frame, which differs
from a fresh meter when the authorizations of the transaction pay state gas). `at_startFrameS` is
`at_startFrame` for the frame of `StateGasMeter` seen through `toNat`, for any starting meter.
-/

namespace UsdtVerify.ProcessMeter

open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open EthLib.Execution.State (TransactionState)

variable {fork : Fork} {Meter : Type} [GasMeter Meter] [LawfulGasMeter Meter]

/-- The runner of the messages of the code of a message, at the gas of that message, over the
meter `Meter`. -/
abbrev processRunnerM (fork : Fork) (bound : Nat) : MessageRunner fork Meter bound :=
  fun caller child _ =>
    match child.target with
    | some _ => processMessage fork child caller.state caller.substate.child
    | none => processCreateMessage fork child caller.state caller.substate.child

/-- A message with no value and no precompile ends as the run of its code from its frame ends.

The frame that ends the message is the stopped frame of that run, rolled back on a failure.

A run that fails makes the message fail with the same error. -/
theorem processMessage_map_valM {message : Message fork} {state : TransactionState}
    {substate : Substate} {meter : Meter} {held : GasMeter.gasHeld meter ≤ message.gas}
    {result : Except EvmError (Evm fork Meter)}
    (noValue : ¬(message.shouldTransferValue = true ∧ message.value ≠ 0))
    (noPrecompile : precompileAddress fork message = none)
    (ran : runFrame (step fork) (step_decreases fork) message.gas (processRunnerM (Meter := Meter) fork message.gas)
      (startFrame message (startState fork message state) substate
        meter) held = result) :
    (processMessage fork message state substate meter held).map Subtype.val =
      result.map (rollbackOnError state) := by
  have ran' : ∀ within, runFrame (step fork) (step_decreases fork) message.gas
      (processRunnerM (Meter := Meter) fork message.gas)
      (startFrame message (startState fork message state)
        (if message.shouldTransferValue = true ∧ message.value ≠ 0 then
          { substate with
            logs := pushTransferLog fork substate.logs message.caller message.currentTarget
              message.value } else substate)
        meter) within = result := by
    intro within
    simp only [noValue, ite_false]
    exact ran
  rw [processMessage]
  simp only [Except.map, noPrecompile, noValue, ite_false, bind, pure, Except.bind, Except.pure]
  split <;> rename_i heq
  · split at heq <;> rename_i heq'
    · split at heq' <;> rename_i h3
      · cases heq'
        cases heq
        have hr := (ran' _).symm.trans h3
        subst hr
        rfl
      · cases heq'
    · cases heq
  · split at heq <;> rename_i heq'
    · cases heq
    · split at heq' <;> rename_i h3
      · cases heq'
      · cases heq'
        cases heq
        have hr := (ran' _).symm.trans h3
        subst hr
        rfl

/-- A message with value and no precompile ends as the run of its code from its frame ends.

The value moves from the caller to the target first, and the frame starts from that state. -/
theorem processMessage_map_val_valueM {message : Message fork} {state movedState : TransactionState}
    {substate : Substate} {meter : Meter} {held : GasMeter.gasHeld meter ≤ message.gas}
    {result : Except EvmError (Evm fork Meter)}
    (transfers : message.shouldTransferValue = true ∧ message.value ≠ 0)
    (moved : (startState fork message state).moveEther fork message.caller message.currentTarget
      message.value = .ok movedState)
    (noPrecompile : precompileAddress fork message = none)
    (ran : runFrame (step fork) (step_decreases fork) message.gas (processRunnerM (Meter := Meter) fork message.gas)
      (startFrame message movedState
        { substate with
          logs := pushTransferLog fork substate.logs message.caller message.currentTarget
            message.value }
        meter) held = result) :
    (processMessage fork message state substate meter held).map Subtype.val =
      result.map (rollbackOnError state) := by
  have ran' : ∀ within, runFrame (step fork) (step_decreases fork) message.gas
      (processRunnerM (Meter := Meter) fork message.gas)
      (startFrame message movedState
        (if message.shouldTransferValue = true ∧ message.value ≠ 0 then
          { substate with
            logs := pushTransferLog fork substate.logs message.caller message.currentTarget
              message.value } else substate)
        meter) within = result := by
    intro within
    simp only [transfers, ne_eq, not_false_eq_true, and_self, ite_true]
    exact ran
  rw [processMessage]
  simp only [Except.map, noPrecompile, transfers, ne_eq, not_false_eq_true, and_self, ite_true,
    bind, pure, Except.bind, Except.pure, Except.mapError, moved]
  split <;> rename_i heq
  · split at heq <;> rename_i heq'
    · split at heq' <;> rename_i h3
      · cases heq'
        cases heq
        have hr := (ran' _).symm.trans h3
        subst hr
        rfl
      · cases heq'
    · cases heq
  · split at heq <;> rename_i heq'
    · cases heq
    · split at heq' <;> rename_i h3
      · cases heq'
      · cases heq'
        cases heq
        have hr := (ran' _).symm.trans h3
        subst hr
        rfl

/-- The frame at the start of a message over `StateGasMeter` with the meter `meter`, seen through
`toNat`, is the fresh frame of its code with the execution gas left of `meter`. -/
theorem at_startFrameS {code : ByteArray} {message : Message fork} (hcode : message.code = code)
    (state : TransactionState) (substate : Substate) (meter : StateGasMeter) :
    At code message 0 [] .empty (GasMeter.gasLeft meter) state substate
      (UsdtVerify.Meter.toNat (startFrame message state substate meter)) := by
  subst hcode
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end UsdtVerify.ProcessMeter
