import UsdtVerify.Evm.Runners
import UsdtVerify.Evm.Iff

/-!
# Sanity: runners that meet the runner hypotheses of the deprecated exact conditions

The theorems `*_dep_ok_iff` of `Usdt/Exact/Deprecated.lean` take a runner that never fails
(`NoFail`) and that ends each forwarded message with no error exactly when a condition `A` holds.

- `answerRunner_noFail`: every `answerRunner` (Evm/Runners.lean: it ends each message at once with
  no error, the caller's state and the answer `f caller msg`) never fails.
- `answerRunner_ans`: it ends every message with no error, so its condition `A` is `True`.
- `answerRunner_ans_acc`: it ends every message with no error in the caller's state, so the
  condition of deprecated destroyBlackFunds is that the contract has an account in that state.
-/

namespace UsdtVerify.Sanity

open EthLib.Base (Fork Address)
open EthLib.Execution
open EthLib.Execution.Evm
open Exact

variable {fork : Fork} {bound : Nat} {f : Evm fork Nat → Message fork → ByteArray}

theorem answerRunner_noFail : NoFail (answerRunner (bound := bound) f) :=
  fun _ _ _ _ h => by cases h

theorem answerRunner_ans (caller : Evm fork Nat) (msg : Message fork) (lt : msg.gas < bound)
    (child : { c : Evm fork Nat // GasMeter.gasHeld c.gas ≤ msg.gas })
    (h : answerRunner f caller msg lt = .ok child) : child.1.error = none ↔ True :=
  iff_true_intro (answerRunner_ok h).1

theorem answerRunner_ans_acc {C : Address} (caller : Evm fork Nat) (msg : Message fork)
    (lt : msg.gas < bound) (child : { c : Evm fork Nat // GasMeter.gasHeld c.gas ≤ msg.gas })
    (h : answerRunner f caller msg lt = .ok child) :
    child.1.error = none ∧ hasAccount child.1.state C ↔ hasAccount caller.state C := by
  obtain ⟨he, hs, -⟩ := answerRunner_ok h
  rw [hs]
  exact ⟨fun h => h.2, fun h => ⟨he, h⟩⟩

end UsdtVerify.Sanity
