import EthLib.Execution.Proofs.Evm.Logic.Rules

/-!
# LOCAL: a rule for STOP

GENERIC GAP. Nothing here is specific to USDT; the rule holds for every code.

EthLib's program logic has no rule for STOP at the pinned commit.

STOP halts the frame with no error, at no price, and leaves its output as it was.

The frame predicate `At` of the logic does not name the output, so the rule cannot say what the
output is: `Stopped` names everything that `Halted` names but the output. (A fresh frame starts
with an empty output and no opcode but RETURN and REVERT writes it, but stating that needs the
output in `At`, which is a second generic gap.)
-/

namespace UsdtVerify.Local

open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic

variable {fork : Fork}

/-- A frame that stopped normally, with its gas, state and substate; the output is not named. -/
def Stopped (gas : Nat) (state : State.TransactionState) (substate : Substate)
    (evm : Evm fork Nat) : Prop :=
  evm.running = false ∧ evm.error = none ∧ evm.gas = gas ∧ evm.state = state ∧
    evm.substate = substate

theorem instruction_stop {Meter : Type} [GasMeter Meter] :
    instruction (Meter := Meter) fork .stop = some stopStep := by
  simp [instruction, stackOnlyStep, controlFlowStep, HOrElse.hOrElse, OrElse.orElse,
    Option.orElse]

variable {code : ByteArray} {message : Message fork} {pc : Nat} {stack : List U256}
  {memory : ByteArray} {gas : Nat} {state : State.TransactionState} {substate : Substate}

/-- STOP halts the frame with no error, at no price. -/
theorem stop (hlt : pc < code.size) (hbyte : code[pc] = 0x00) :
    Spec fork (At code message pc stack memory gas state substate)
      (Stopped gas state substate) := by
  apply At.rule hlt hbyte (ofByte_of_decode (op := .stop) rfl (Fork.frontier_le _))
    instruction_stop
  rintro evm ⟨hcode, hj, hm, hpc, hst, hmem, hg, hrun, herr, hs, hss⟩
  exact ⟨_, rfl, rfl, rfl, herr, hg, hs, hss⟩

end UsdtVerify.Local
