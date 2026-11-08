import UsdtVerify.Usdt.Proofs.Common

/-!
# The SafeMath functions of the bytecode

Internal functions, each called with `[b, a, ret, ...]` (top first) and returning to `ret`
with its result in place of the three words.

- 10755 (0x2a03) `mul(a, b)`: 0 when `a = 0`; else `a * b`, after `assert(c / a == b)`.
- 10949 (0x2ac5) `div(a, b)`: `a / b`, after the compiler's check that `b ≠ 0`.
- 10976 (0x2ae0) `sub(a, b)`: `a - b`, after `assert(b <= a)`.
- 11001 (0x2af9) `add(a, b)`: `a + b`, after `assert(c >= a)`.

Each assert that fails runs INVALID (0xfe); those paths are not covered here (no rule for an
exceptional halt). The lemmas take the hypotheses under which no assert fails.
-/

namespace UsdtVerify.SafeMath

open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate}

/-- The gas of `mul(a, b)`: the early return when `a = 0` is cheaper. -/
abbrev mulCost (a : U256) : Nat := if a = 0 then 72 else 138

theorem mul_zero_left (b : U256) : mul 0 b = 0 := by simp [mul]

/-- Without overflow, the product divided by a nonzero factor is the other factor. -/
theorem div_mul_self {a b : U256} (ha : a ≠ 0) (hov : a.toNat * b.toNat < 2 ^ 256) :
    div (mul a b) a = b := by
  have hpos : 0 < a.toNat := by
    rcases Nat.eq_zero_or_pos a.toNat with h | h
    · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h)) ha
    · exact h
  apply BitVec.eq_of_toNat_eq
  simp only [div, ha, ite_false, mul, BitVec.toNat_mul, Nat.mod_eq_of_lt hov,
    Nat.mul_div_cancel_left _ hpos, BitVec.toNat_ofNat, Nat.mod_eq_of_lt b.isLt]

/-- `mul(a, b)` at 10755, without overflow, returns `a * b` to `ret`. -/
theorem mulBlock {a b ret : U256} {rest : List U256} (hrest : rest.length ≤ 20)
    (hret : isValidJumpDest (validJumpDestinations CODE) ret.toNat = true)
    (hov : a.toNat * b.toNat < 2 ^ 256) {gas : Nat} (hg : mulCost a ≤ gas) {M : ByteArray} :
    Gas.HoareG fork (At CODE message 10755 (b :: a :: ret :: rest) M gas state substate)
      (At CODE message ret.toNat (mul a b :: rest) M (gas - mulCost a) state substate) := by
  by_cases ha : a = 0
  · simp only [mulCost, ha, ite_true] at hg ⊢
    subst ha
    step jumpdestR
    step pushR 1 (0 : U256)
    step dupR 0
    step pushR 1 (0 : U256)
    step dupR 4
    step binR 0x14 instruction_eq
    step unR 0x15 instruction_iszero
    step pushR 2 (0x2a18 : U256)
    step jumpi0R (by decide)
    step pushR 1 (0 : U256)
    step swapR 1
    norm
    step popR
    step pushR 2 (0x2a37 : U256)
    step jumpR
    at_pc 10807
    step jumpdestR
    step popR
    step swapR 2
    norm
    step swapR 1
    norm
    step popR
    step popR
    step Gas.jumpG (by code_fact) (by code_fact) (by gas_ok) hret
    exact Gas.reshapeG (by simp; exact (mul_zero_left b).symm) rfl (by gas_ok)
  · simp only [mulCost, ha, ite_false] at hg ⊢
    have hq := div_mul_self ha hov
    step jumpdestR
    step pushR 1 (0 : U256)
    step dupR 0
    step pushR 1 (0 : U256)
    step dupR 4
    step binR 0x14 instruction_eq
    step unR 0x15 instruction_iszero
    step pushR 2 (0x2a18 : U256)
    step jumpiR (by simp [equal, isZero]; exact ha)
    at_pc 10776
    step jumpdestR
    step dupR 2
    step dupR 4
    step binR 0x02 Local.instruction_mul
    step swapR 0
    norm
    step popR
    step dupR 2
    step dupR 4
    step dupR 2
    step dupR 1
    step unR 0x15 instruction_iszero
    step unR 0x15 instruction_iszero
    step pushR 2 (0x2a29 : U256)
    step jumpiR (by simp [isZero]; exact ha)
    at_pc 10793
    step jumpdestR
    step binR 0x04 Local.instruction_div
    step binR 0x14 instruction_eq
    step unR 0x15 instruction_iszero
    step unR 0x15 instruction_iszero
    step pushR 2 (0x2a33 : U256)
    step jumpiR (by simp [hq, equal, isZero])
    at_pc 10803
    step jumpdestR
    step dupR 0
    step swapR 1
    norm
    step popR
    step jumpdestR
    step popR
    step swapR 2
    norm
    step swapR 1
    norm
    step popR
    step popR
    step Gas.jumpG (by code_fact) (by code_fact) (by gas_ok) hret
    exact Gas.reshapeG rfl rfl (by gas_ok)

/-- `div(a, b)` at 10949, for `b ≠ 0`, returns `a / b` to `ret`. -/
theorem divBlock {a b ret : U256} {rest : List U256} (hrest : rest.length ≤ 20)
    (hret : isValidJumpDest (validJumpDestinations CODE) ret.toNat = true) (hb : b ≠ 0)
    {gas : Nat} (hg : 74 ≤ gas) {M : ByteArray} :
    Gas.HoareG fork (At CODE message 10949 (b :: a :: ret :: rest) M gas state substate)
      (At CODE message ret.toNat (div a b :: rest) M (gas - 74) state substate) := by
  step jumpdestR
  step pushR 1 (0 : U256)
  step dupR 0
  step dupR 2
  step dupR 4
  step dupR 1
  step unR 0x15 instruction_iszero
  step unR 0x15 instruction_iszero
  step pushR 2 (0x2ad3 : U256)
  step jumpiR (by simp [isZero]; exact hb)
  at_pc 10963
  step jumpdestR
  step binR 0x04 Local.instruction_div
  step swapR 0
  norm
  step popR
  step dupR 0
  step swapR 1
  norm
  step popR
  step popR
  step swapR 2
  norm
  step swapR 1
  norm
  step popR
  step popR
  step Gas.jumpG (by code_fact) (by code_fact) (by gas_ok) hret
  exact Gas.reshapeG rfl rfl (by gas_ok)

/-- `sub(a, b)` at 10976, for `b ≤ a`, returns `a - b` to `ret`. -/
theorem subBlock {a b ret : U256} {rest : List U256} (hrest : rest.length ≤ 20)
    (hret : isValidJumpDest (validJumpDestinations CODE) ret.toNat = true)
    (hle : b.toNat ≤ a.toNat) {gas : Nat} (hg : 68 ≤ gas) {M : ByteArray} :
    Gas.HoareG fork (At CODE message 10976 (b :: a :: ret :: rest) M gas state substate)
      (At CODE message ret.toNat (sub a b :: rest) M (gas - 68) state substate) := by
  have hgt : greaterThan b a = 0 := by simp [greaterThan, Nat.not_lt.mpr hle]
  step jumpdestR
  step pushR 1 (0 : U256)
  step dupR 2
  step dupR 2
  step binR 0x11 Local.instruction_gt
  step unR 0x15 instruction_iszero
  step unR 0x15 instruction_iszero
  step unR 0x15 instruction_iszero
  step pushR 2 (0x2aee : U256)
  step jumpiR (by simp [hgt, isZero])
  at_pc 10990
  step jumpdestR
  step dupR 1
  step dupR 3
  step binR 0x03 Local.instruction_sub
  step swapR 0
  norm
  step popR
  step swapR 2
  norm
  step swapR 1
  norm
  step popR
  step popR
  step Gas.jumpG (by code_fact) (by code_fact) (by gas_ok) hret
  exact Gas.reshapeG rfl rfl (by gas_ok)

/-- `add(a, b)` at 11001, without overflow, returns `a + b` to `ret`. -/
theorem addBlock {a b ret : U256} {rest : List U256} (hrest : rest.length ≤ 20)
    (hret : isValidJumpDest (validJumpDestinations CODE) ret.toNat = true)
    (hov : a.toNat + b.toNat < 2 ^ 256) {gas : Nat} (hg : 81 ≤ gas) {M : ByteArray} :
    Gas.HoareG fork (At CODE message 11001 (b :: a :: ret :: rest) M gas state substate)
      (At CODE message ret.toNat (add a b :: rest) M (gas - 81) state substate) := by
  have hlt : lessThan (add a b) a = 0 := by
    have : (add a b).toNat = a.toNat + b.toNat := by
      simp [add, BitVec.toNat_add, Nat.mod_eq_of_lt hov]
    simp [lessThan, this]
  step jumpdestR
  step pushR 1 (0 : U256)
  step dupR 0
  step dupR 2
  step dupR 4
  step binR 0x01 instruction_add
  step swapR 0
  norm
  step popR
  step dupR 3
  step dupR 1
  step binR 0x10 Local.instruction_lt
  step unR 0x15 instruction_iszero
  step unR 0x15 instruction_iszero
  step unR 0x15 instruction_iszero
  step pushR 2 (0x2b0d : U256)
  step jumpiR (by simp [hlt, isZero])
  at_pc 11021
  step jumpdestR
  step dupR 0
  step swapR 1
  norm
  step popR
  step popR
  step swapR 2
  norm
  step swapR 1
  norm
  step popR
  step popR
  step Gas.jumpG (by code_fact) (by code_fact) (by gas_ok) hret
  exact Gas.reshapeG rfl rfl (by gas_ok)

end UsdtVerify.SafeMath
