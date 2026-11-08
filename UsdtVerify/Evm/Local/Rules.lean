import EthLib.Execution.Proofs.Evm.Logic.Branch
import EthLib.Execution.Proofs.Evm.Logic.Stack

/-!
# LOCAL: generic opcode rules missing from EthLib at the pinned commit

GENERIC GAP. Nothing here is specific to USDT; each rule holds for every code.

They belong in EthLib's program logic and are kept here only until it has them.

The opcodes LT, GT, DIV, AND, OR, SUB, MUL, NOT: their entries of the instruction table.
(EXP with its price from Spurious Dragon worked out is `Gas.expLG`, over `StepG`.)

The proofs follow the rules of `Logic/Rules.lean` line for line.

Checked again at the re-pin to fd3457dbf (#1300, after #1292 and #1299): EthLib has STOP
(`Logic.stop`, `Halted false .empty`), GAS (`gas_rule`) and EXTCODESIZE (`extcodesize`), which
replaced the local Halt.lean and Account.lean; it still has no named instruction-table lemmas for
the opcodes below and no EXP rule with the price of a fork worked out.

Removed at the re-pin to d4d422780: the frame-read rules (CALLVALUE, CALLDATASIZE; EthLib
`push_of_readFrame`, #1258) and JUMPI on a condition proved 0 (EthLib `jumpi_of_eq_zero`).
-/

namespace UsdtVerify.Local

open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts

variable {fork : Fork}

section Table

variable {Meter : Type} [GasMeter Meter]

theorem instruction_lt :
    instruction (Meter := Meter) fork .lt = some (binaryOp OPCODE_LT lessThan) :=
  Logic.instruction_of_stackOnlyStep rfl

theorem instruction_gt :
    instruction (Meter := Meter) fork .gt = some (binaryOp OPCODE_GT greaterThan) :=
  Logic.instruction_of_stackOnlyStep rfl

theorem instruction_div :
    instruction (Meter := Meter) fork .div = some (binaryOp OPCODE_DIV div) :=
  Logic.instruction_of_stackOnlyStep rfl

theorem instruction_and :
    instruction (Meter := Meter) fork .and = some (binaryOp OPCODE_AND bitwiseAnd) :=
  Logic.instruction_of_stackOnlyStep rfl

theorem instruction_or :
    instruction (Meter := Meter) fork .or = some (binaryOp OPCODE_OR bitwiseOr) :=
  Logic.instruction_of_stackOnlyStep rfl

theorem instruction_sub :
    instruction (Meter := Meter) fork .sub = some (binaryOp OPCODE_SUB sub) :=
  Logic.instruction_of_stackOnlyStep rfl

theorem instruction_mul :
    instruction (Meter := Meter) fork .mul = some (binaryOp OPCODE_MUL mul) :=
  Logic.instruction_of_stackOnlyStep rfl

theorem instruction_not :
    instruction (Meter := Meter) fork .not = some (unaryOp OPCODE_NOT bitwiseNot) :=
  Logic.instruction_of_stackOnlyStep rfl

end Table

end UsdtVerify.Local
