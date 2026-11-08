import EthLib.Execution.Proofs.Evm.Logic.Branch
import EthLib.Execution.Proofs.Evm.Logic.Stack

/-!
# LOCAL: generic opcode rules missing from EthLib at the pinned commit

GENERIC GAP. Nothing here is specific to USDT; each rule holds for every code.

They belong in EthLib's program logic and are kept here only until it has them.

- EXP with its price from Spurious Dragon worked out (a corollary of EthLib's `exp`).
- The opcodes LT, GT, DIV, AND, OR, SUB, MUL, NOT: their entries of the instruction table.

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

variable {code : ByteArray} {message : Message fork} {pc : Nat} {stack : List U256}
  {memory : ByteArray} {gas : Nat} {state : State.TransactionState} {substate : Substate}

/-- From Spurious Dragon, EXP costs 10 and 50 per byte of the exponent, by EIP-160.

A corollary of EthLib's `exp`, with the price of the fork worked out. -/
theorem exp (hfork : .spuriousDragon ≤ fork) {base exponent : U256} {rest : List U256}
    (hlt : pc < code.size) (hbyte : code[pc] = 0x0a)
    (hgas : 10 + 50 * exponentBytes exponent ≤ gas) :
    Hoare fork (At code message pc (base :: exponent :: rest) memory gas state substate)
      (At code message (pc + 1) (Evm.exp base exponent :: rest) memory
        (gas - (10 + 50 * exponentBytes exponent)) state substate) := by
  have price : OPCODE_EXP_BASE + (gasSchedule fork).OPCODE_EXP_PER_BYTE *
      exponentBytes exponent = 10 + 50 * exponentBytes exponent := by
    simp [OPCODE_EXP_BASE, gasSchedule, hfork]
  have h := Logic.exp (fork := fork) (code := code) (message := message) (memory := memory)
    (state := state) (substate := substate) (base := base) (exponent := exponent) (rest := rest)
    hlt hbyte (by rw [price]; exact hgas)
  rw [price] at h
  exact h

end UsdtVerify.Local
