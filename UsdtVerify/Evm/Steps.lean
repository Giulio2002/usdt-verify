import UsdtVerify.Evm.GasRules
import UsdtVerify.Evm.Local.Rules
import EthLib.Execution.Proofs.Evm.Logic.Steps

/-!
# Helpers for stepping through any code

- `repc`, `restate` (and `repcH`, `restateH` over `Step`): a frame is also a frame at an equal
  program counter, or with equal parts.
- `slotCost`: the price of SLOAD from Berlin.
- `gas_ok`, `stk_ok`: close gas and stack-room side goals; `step r`: run one rule at the head of
  the goal; `at_pc n`: normalize the program counter.
- `reshape` (now EthLib's `Logic.reshape`, #1238): equal stack, memory and gas.
-/

namespace UsdtVerify

open EthLib.Base (Fork U256 bytesToNat)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic

variable {fork : Fork}

/-- A frame is also a frame at an equal program counter (over `StepG`). -/
theorem repc {code : ByteArray} {message : Message fork} {pc pc' : Nat} {s : List U256}
    {m : ByteArray} {g : Nat} {st : State.TransactionState} {ss : Substate} (h : pc = pc') :
    Gas.HoareG fork (At code message pc s m g st ss) (At code message pc' s m g st ss) := by
  subst h
  exact Triple.of_imp fun _ h => h

/-- A frame is also a frame with equal parts, the state and substate included (over `StepG`). -/
theorem restate {code : ByteArray} {message : Message fork} {pc pc' : Nat} {s s' : List U256}
    {m m' : ByteArray} {g g' : Nat} {st st' : State.TransactionState} {ss ss' : Substate}
    (hpc : pc = pc') (hs : s = s') (hm : m = m') (hg : g = g') (hst : st = st') (hss : ss = ss') :
    Gas.HoareG fork (At code message pc s m g st ss) (At code message pc' s' m' g' st' ss') := by
  subst hpc hs hm hg hst hss
  exact Triple.of_imp fun _ h => h

/-- `repc` over `Step`. -/
theorem repcH {code : ByteArray} {message : Message fork} {pc pc' : Nat} {s : List U256}
    {m : ByteArray} {g : Nat} {st : State.TransactionState} {ss : Substate} (h : pc = pc') :
    Hoare fork (At code message pc s m g st ss) (At code message pc' s m g st ss) :=
  Gas.HoareG.toHoare (repc h)

/-- `restate` over `Step`. -/
theorem restateH {code : ByteArray} {message : Message fork} {pc pc' : Nat} {s s' : List U256}
    {m m' : ByteArray} {g g' : Nat} {st st' : State.TransactionState} {ss ss' : Substate}
    (hpc : pc = pc') (hs : s = s') (hm : m = m') (hg : g = g') (hst : st = st') (hss : ss = ss') :
    Hoare fork (At code message pc s m g st ss) (At code message pc' s' m' g' st' ss') :=
  Gas.HoareG.toHoare (restate hpc hs hm hg hst hss)

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

/-- Run one rule `r` at the head of the goal. A rule over `StepG` also runs in a goal over
`Step` (`Gas.Triple.seqL`). -/
macro "step " r:term : tactic => `(tactic| refine Gas.Triple.seqL $r ?_)
/-- Normalize the program counter to the numeral `n`. -/
macro "at_pc " n:term : tactic =>
  `(tactic| refine Gas.Triple.seqL (repc (pc' := $n) (by decide)) ?_)

end UsdtVerify
