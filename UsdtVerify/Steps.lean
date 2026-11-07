import UsdtVerify.Code
import UsdtVerify.Local.Rules
import EthLib.Execution.Proofs.Evm.Logic.Steps

/-!
# Helpers for stepping through `CODE`

- `pushData_CODE`: the data of a PUSH at `pc`, read through `codeByte`.
- `reshape` (now EthLib's `Logic.reshape`, #1238): equal stack, memory and gas.
- `code_fact`: closes `pc < CODE.size`, `CODE[pc] = b` and `pushData CODE pc n = w`.
- `valid_dest`: closes `isValidJumpDest (validJumpDestinations CODE) d = true`.
-/

namespace UsdtVerify

open EthLib.Base (Fork U256 bytesToNat)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic

theorem pushData_CODE (pc n : Nat) : pushData CODE pc n =
    BitVec.ofNat 256 (bytesToNat ((List.range n).map fun i => codeByte (pc + 1 + i))) := by
  simp only [pushData, bufferRead, byteAt_CODE]

variable {fork : Fork}

/-- A frame is also a frame at an equal program counter. -/
theorem repc {code : ByteArray} {message : Message fork} {pc pc' : Nat} {s : List U256}
    {m : ByteArray} {g : Nat} {st : State.TransactionState} {ss : Substate} (h : pc = pc') :
    Hoare fork (At code message pc s m g st ss) (At code message pc' s m g st ss) := by
  subst h
  exact Triple.of_imp fun _ h => h

/-- A frame is also a frame with equal parts, the state and substate included. -/
theorem restate {code : ByteArray} {message : Message fork} {pc pc' : Nat} {s s' : List U256}
    {m m' : ByteArray} {g g' : Nat} {st st' : State.TransactionState} {ss ss' : Substate}
    (hpc : pc = pc') (hs : s = s') (hm : m = m') (hg : g = g') (hst : st = st') (hss : ss = ss') :
    Hoare fork (At code message pc s m g st ss) (At code message pc' s' m' g' st' ss') := by
  subst hpc hs hm hg hst hss
  exact Triple.of_imp fun _ h => h

/-- The order matters: a byte goal also mentions `CODE.size` in its bound, and running `decide`
on `CODE` itself hits the recursion limit, an error that `first` does not catch. -/
macro "code_fact" : tactic => `(tactic| first
  | (rw [getElem_CODE]; decide)
  | (rw [pushData_CODE]; decide)
  | (rw [size_CODE]; decide))

macro "valid_dest" : tactic =>
  `(tactic| exact valid_CODE (by decide) (by decide +kernel) (by decide))

/-- The price of SLOAD from Berlin, by EIP-2929: 2100 for a cold slot and 100 for a warm one. -/
abbrev slotCost (cold : Bool) : Nat := if cold then 2100 else 100

/-- Gas side goals: unfold the named prices, then linear arithmetic. -/
macro "gas_ok" : tactic => `(tactic| ((try simp only [GasCosts.OPCODE_ADD, GasCosts.OPCODE_SUB,
    GasCosts.OPCODE_MUL, GasCosts.OPCODE_DIV, GasCosts.OPCODE_LT, GasCosts.OPCODE_GT,
    GasCosts.OPCODE_EQ, GasCosts.OPCODE_ISZERO, GasCosts.OPCODE_AND, GasCosts.OPCODE_OR,
    GasCosts.OPCODE_NOT, GasCosts.VERY_LOW, GasCosts.LOW, slotCost, Bool.false_eq_true,
    ↓reduceIte] at *) <;> omega))

/-- Stack room side goals. -/
macro "stk_ok" : tactic => `(tactic| (simp [STACK_LIMIT] <;> omega))

/-- Run one rule `r` at the head of the goal. -/
macro "step " r:term : tactic => `(tactic| refine Triple.seq $r ?_)

/-- PUSH1 of the byte `b`. -/
macro "push1R " b:term : term =>
  `(push1 (byte := $b) (by code_fact) (by code_fact) (by code_fact) (by gas_ok) (by stk_ok))

/-- PUSHn of the word `w`. -/
macro "pushR " n:term:max w:term:max : term =>
  `(push (n := $n) (word := $w) (by decide) (by code_fact) (by code_fact)
    (decode_push $n (by decide)) (by code_fact) (by gas_ok) (by stk_ok))

/-- PUSHn of whatever word the code holds (the word stays as an unevaluated read of `codeByte`). -/
macro "pushAnyR " n:term:max : term =>
  `(push (n := $n) (by decide) (by code_fact) (by code_fact)
    (decode_push $n (by decide)) (by rw [pushData_CODE]) (by gas_ok) (by stk_ok))

/-- A two-operand opcode with byte `b` and instruction-table lemma `i`. -/
macro "binR " b:term:max i:term:max : term =>
  `(binary (byte := $b) (by code_fact) (by code_fact) (ofByte_of_decode rfl (Fork.frontier_le _))
    $i (by gas_ok))

/-- A one-operand opcode with byte `b` and instruction-table lemma `i`. -/
macro "unR " b:term:max i:term:max : term =>
  `(unary (byte := $b) (by code_fact) (by code_fact) (ofByte_of_decode rfl (Fork.frontier_le _))
    $i (by gas_ok))

macro "swapR " n:term:max : term =>
  `(EthLib.Execution.Evm.Logic.swap $n (by code_fact) (by code_fact) rfl (by gas_ok))

macro "dupR " n:term:max : term =>
  `(EthLib.Execution.Evm.Logic.dup $n (by code_fact) (by code_fact) rfl (by gas_ok) (by stk_ok))

macro "popR" : term => `(EthLib.Execution.Evm.Logic.pop (by code_fact) (by code_fact) (by gas_ok))

macro "jumpdestR" : term => `(jumpdest (by code_fact) (by code_fact) (by gas_ok))

macro "jumpR" : term => `(jump (by code_fact) (by code_fact) (by gas_ok) (by valid_dest))

/-- JUMPI on a condition proved nonzero by `h`. -/
macro "jumpiR " h:term:max : term =>
  `(jumpi_taken (by code_fact) (by code_fact) (by gas_ok) $h (by valid_dest))

/-- JUMPI on a condition proved zero by `h`. -/
macro "jumpi0R " h:term:max : term =>
  `(Logic.jumpi_of_eq_zero (by code_fact) (by code_fact) (by gas_ok) $h)

/-- Normalize the program counter to the numeral `n`. -/
macro "at_pc " n:term : tactic => `(tactic| refine Triple.seq (repc (pc' := $n) (by decide)) ?_)

end UsdtVerify
