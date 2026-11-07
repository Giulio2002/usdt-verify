import UsdtVerify.Complete.Dispatch

/-!
# From a specification over `StepG` to the end of every successful run

- `ok_exact`: a specification to a normal halt that pays `cost`, proved for every gas from a bound
  `B ≥ cost` on. A run of the interpreter loop from the same frame with any gas that ends with no
  error ends in that halt: `cost ≤ gas`, the output, gas `gas - cost`, the state and the substate
  are those of the specification.
- `no_ok`: a specification to a frame with an error, proved for every gas from a bound on. No run
  of the interpreter loop from the same frame ends with no error, whatever the gas.
-/

namespace UsdtVerify.Complete

open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open UsdtVerify.Gas

variable {fork : Fork} {code : ByteArray} {message : Message fork} {pc : Nat}
  {stack : List U256} {memory : ByteArray} {state : State.TransactionState}
  {substate : Substate} {bound : Nat} {runChild : MessageRunner fork Nat bound}
  {evm s : Evm fork Nat}

/-- A successful run ends as a specification to a normal halt states, with the exact gas. -/
theorem ok_exact {B cost : Nat} (hB : cost ≤ B) {out : ByteArray}
    {st' : State.TransactionState} {ss' : Substate}
    (h : ∀ g, B ≤ g → SpecG fork (At code message pc stack memory g state substate)
      (Halted false out (g - cost) st' ss'))
    {gas : Nat} (start : At code message pc stack memory gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) :
    cost ≤ gas ∧ s.running = false ∧ s.output = out ∧ s.gas = gas - cost ∧ s.state = st' ∧
      s.substate = ss' := by
  obtain ⟨hr, ho, hg, hst, hss⟩ :=
    SpecG.halted (h (gas + B) (by omega)) start within hrun hok
  exact ⟨by omega, hr, ho, by omega, hst, hss⟩

/-- No successful run from a frame where a specification to an error holds. -/
theorem no_ok {B : Nat} {Q : Nat → Evm fork Nat → Prop}
    (h : ∀ g, B ≤ g → SpecG fork (At code message pc stack memory g state substate) (Q g))
    (herr : ∀ g e, Q g e → e.error ≠ none)
    {gas : Nat} (start : At code message pc stack memory gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) : False :=
  SpecG.not_ok (h (gas + B) (by omega)) (herr (gas + B)) (at_sh start B) within hrun hok

theorem le_l {a b g : Nat} (h : a + b ≤ g) : a ≤ g := Nat.le_trans (Nat.le_add_right a b) h

theorem le_r {a b g : Nat} (h : a + b ≤ g) : b ≤ g := Nat.le_trans (Nat.le_add_left b a) h

theorem faulted_error {err : EvmError} {st : State.TransactionState} {ss : Substate}
    (e : Evm fork Nat) (h : Faulted err st ss e) : e.error ≠ none := by
  rw [h.2.1]; simp

/-- `no_ok` for a specification with two gas bounds (the bounds are found by unification). -/
theorem no_ok2 {B1 B2 : Nat} {Q : Nat → Evm fork Nat → Prop}
    (h : ∀ g, B1 ≤ g → B2 ≤ g → SpecG fork (At code message pc stack memory g state substate) (Q g))
    (herr : ∀ g e, Q g e → e.error ≠ none)
    {gas : Nat} (start : At code message pc stack memory gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) : False :=
  no_ok (B := B1 + B2) (fun g hg => h g (le_l hg) (le_r hg)) herr start within hrun hok

/-- `ok_exact` for a specification with two gas bounds, the second one the cost. -/
theorem ok_exact2 {B1 cost : Nat} {out : ByteArray}
    {st' : State.TransactionState} {ss' : Substate}
    (h : ∀ g, B1 ≤ g → cost ≤ g → SpecG fork (At code message pc stack memory g state substate)
      (Halted false out (g - cost) st' ss'))
    {gas : Nat} (start : At code message pc stack memory gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) :
    cost ≤ gas ∧ s.running = false ∧ s.output = out ∧ s.gas = gas - cost ∧ s.state = st' ∧
      s.substate = ss' :=
  ok_exact (B := B1 + cost) (Nat.le_add_left _ _) (fun g hg => h g (le_l hg) (le_r hg))
    start within hrun hok

/-- `ok_exact` for a specification with three gas bounds, the third one the cost. -/
theorem ok_exact3 {B1 B2 cost : Nat} {out : ByteArray}
    {st' : State.TransactionState} {ss' : Substate}
    (h : ∀ g, B1 ≤ g → B2 ≤ g → cost ≤ g →
      SpecG fork (At code message pc stack memory g state substate)
        (Halted false out (g - cost) st' ss'))
    {gas : Nat} (start : At code message pc stack memory gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) :
    cost ≤ gas ∧ s.running = false ∧ s.output = out ∧ s.gas = gas - cost ∧ s.state = st' ∧
      s.substate = ss' :=
  ok_exact2 (B1 := B1 + B2) (fun g h1 h2 => h g (le_l h1) (le_r h1) h2) start within hrun hok

end UsdtVerify.Complete
