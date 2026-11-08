import UsdtVerify.Evm.Runners
import UsdtVerify.Evm.Iff
import UsdtVerify.Evm.Sample

/-!
# Sanity: runners that meet the runner hypotheses of the deprecated exact conditions

The theorems `*_dep_ok_iff` of `Usdt/Exact/Deprecated.lean` take a runner that never fails
(`NoFail`), and, for all but destroyBlackFunds, that ends each forwarded message with no error
exactly when a condition `A` holds.

- `answerRunner_noFail`: every `answerRunner` (Evm/Runners.lean: it ends each message at once with
  no error, the caller's state and the answer `f caller msg`) never fails.
- `answerRunner_ans`: it ends every message with no error, so its condition `A` is `True`.
- `answerRunner_ans_acc`: it ends every message with no error in the caller's state, so it ends a
  message with no error and an account of `C` exactly when the caller's state has an account of
  `C` (this condition depends on the caller, so it is not the `hans` of destroyBlackFunds).
- `answerRunnerAt_noFail`, `answerRunnerAt_ans_acc` (round 26): `answerRunnerAt S f` (each message
  ends at once with no error in the state `S`) never fails, and when `S` has an account of `C` it
  ends every message with no error and an account of `C`: it meets the `hans` of deprecated
  destroyBlackFunds (`destroyBlackFunds_dep_ok_iff`) with `A = True`, for every route and data.
  `answerRunnerAt_hans`: that `hans` in the exact form of the theorem, for `S = sState C kvs`
  (Evm/Sample.lean), which has an account of `C`.
- `answerRunnerAt_ans_gas` (round 26): the runner hypothesis of the `*_dep_ok_iff_gas` theorems
  holds for `answerRunnerAt S f` with `A` the bound on the gas the CALL keeps (the ended frames
  have gas 0).
- `answerRunnerAt_ans_gasD` (round 26): the same for the runner hypothesis of
  `destroyBlackFunds_dep_ok_iff_gas`, when `S` has an account of `C`: the ended frame has no
  error, an account of `C` and gas 0, so the condition reduces to the bound `T ≤ R`. Stated per
  frame: `T` (the tail's cost and stipend bound) depends on the caller's frame.
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

theorem answerRunnerAt_noFail {S : State.TransactionState} :
    NoFail (answerRunnerAt (bound := bound) S f) :=
  fun _ _ _ _ h => by cases h

theorem answerRunnerAt_ans_acc {S : State.TransactionState} {C : Address} (hS : hasAccount S C)
    (caller : Evm fork Nat) (msg : Message fork) (lt : msg.gas < bound)
    (child : { c : Evm fork Nat // GasMeter.gasHeld c.gas ≤ msg.gas })
    (h : answerRunnerAt S f caller msg lt = .ok child) :
    child.1.error = none ∧ hasAccount child.1.state C ↔ True := by
  obtain ⟨he, hs, -⟩ := answerRunnerAt_ok h
  rw [hs]
  exact iff_true_intro ⟨he, hS⟩

/-- The runner hypothesis `hans` of deprecated destroyBlackFunds, with `A = True`, holds for
`answerRunnerAt (sState C kvs) f`, for every message `M` whose current target is `C`, upgraded
address `ua`, code `c`, route `r` and data `d`. -/
theorem answerRunnerAt_hans (M : Message fork) {C : Address} (hC : M.currentTarget = C)
    (kvs : List (EthLib.Base.U256 × EthLib.Base.U256)) (ua : Address) (c : ByteArray)
    (r : Complete.Route) (d : ByteArray) :
    ∀ caller msg lt child, answerRunnerAt (bound := bound) (sState C kvs) f caller msg lt =
      .ok child → Complete.SendsVia M ua c r d msg →
        (child.1.error = none ∧ hasAccount child.1.state M.currentTarget ↔ True) :=
  fun caller msg lt child h _ => by
    rw [hC]
    exact answerRunnerAt_ans_acc (hasAccount_sState C kvs) caller msg lt child h

/-- `answerRunnerAt S f` ends each message with no error and gas 0: the runner hypothesis of the
`*_dep_ok_iff_gas` theorems holds for it with `A` the bound `T ≤ R` on the gas kept by the CALL,
for every `T` and `R`. -/
theorem answerRunnerAt_ans_gas {S : State.TransactionState} (T R : Nat)
    (caller : Evm fork Nat) (msg : Message fork) (lt : msg.gas < bound)
    (child : { c : Evm fork Nat // GasMeter.gasHeld c.gas ≤ msg.gas })
    (h : answerRunnerAt S f caller msg lt = .ok child) :
    child.1.error = none ∧ T ≤ R + child.1.gas ↔ T ≤ R := by
  obtain ⟨he, -, -, hg⟩ := answerRunnerAt_ok h
  rw [hg, Nat.add_zero]
  exact ⟨fun h => h.2, fun h => ⟨he, h⟩⟩

/-- `answerRunnerAt S f`, with `S` an account of `C`, ends each message with no error, an
account of `C` and gas 0: the condition of the runner hypothesis of
`destroyBlackFunds_dep_ok_iff_gas` holds of its ended frame exactly when `T ≤ R`. -/
theorem answerRunnerAt_ans_gasD {S : State.TransactionState} {C : Address} (hS : hasAccount S C)
    (T R : Nat) (caller : Evm fork Nat) (msg : Message fork) (lt : msg.gas < bound)
    (child : { c : Evm fork Nat // GasMeter.gasHeld c.gas ≤ msg.gas })
    (h : answerRunnerAt S f caller msg lt = .ok child) :
    child.1.error = none ∧ hasAccount child.1.state C ∧ T ≤ R + child.1.gas ↔ T ≤ R := by
  obtain ⟨he, hs, -, hg⟩ := answerRunnerAt_ok h
  rw [hg, Nat.add_zero, hs]
  exact ⟨fun h => h.2.2, fun h => ⟨he, hS, h⟩⟩

end UsdtVerify.Sanity
