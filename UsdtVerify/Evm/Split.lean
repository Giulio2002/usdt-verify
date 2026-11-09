import UsdtVerify.Evm.Exact

/-!
# Splitting a successful run at a running frame (towards the deprecated paths)

`SpecG.low` follows a run with less gas to a stopped frame. Here the same argument stops at a
running frame:

- `low_to_running`: along a chain of `StepG` from `addGas k l` to a frame `z`, a run of the loop from
  `l` that ends with no error in `s` passes through a frame `z'` with `z = addGas k z'`: the run from
  `z'` ends in the same `s`.
- `HoareG.low`, `ok_split`: for a `HoareG` from `At ... gas` to `At ... (gas - c)` proved for every
  gas from a bound on, a successful run from the start frame with ANY gas has `c ≤ gas` and runs
  through a frame `At ... (gas - c)` from which the loop ends in the same `s`.

Used for the deprecated paths of USDT, whose prefix up to the GAS instruction is over `StepG`
but whose GAS and CALL are not `RunMono`.
-/


namespace UsdtVerify.Complete

open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic hiding HoareG SpecG SpecG.low StepG
open UsdtVerify.Gas

variable {fork : Fork} {bound : Nat} {runChild : MessageRunner fork Nat bound}

/-- A run from `l` with no error passes through the low copy of every frame that `addGas k l`
reaches by `StepG`. -/
theorem low_to_running {hi z : Evm fork Nat} (hr : Reaches (StepG fork) hi z) :
    ∀ (k : Nat) (l : Evm fork Nat), hi = addGas k l →
      ∀ (within : GasMeter.gasHeld l.gas ≤ bound) {s : Evm fork Nat},
        Evm.runFrame (step fork) (step_decreases fork) bound runChild l within = .ok s →
        s.error = none →
        ∃ z' w, z = addGas k z' ∧
          Evm.runFrame (step fork) (step_decreases fork) bound runChild z' w = .ok s := by
  induction hr with
  | refl =>
    rintro k l rfl within s hs _
    exact ⟨l, within, rfl, hs⟩
  | step hs _ ih =>
    rintro k l rfl within s hrun hok
    obtain ⟨hstep, -, hmono⟩ := hs
    have hr : l.running = true := hstep.running
    rcases hmono k l rfl with (⟨e, he⟩ | ⟨b, hb, hbr, hbe⟩) | ⟨b, hb, hh⟩
    · by_cases ab : e.aborts = true
      · rw [runFrame_of_step_eq_abort hr he ab] at hrun
        cases hrun
      · rw [runFrame_of_step_eq_error hr he (by simpa using ab)] at hrun
        cases hrun
        simp [exceptionalHalt] at hok
    · rw [runFrame_of_step_eq_next hr hb, runFrame_stopped hbr] at hrun
      cases hrun
      exact absurd hok hbe
    · rw [runFrame_of_step_eq_next hr hb] at hrun
      cases hstep with
      | next _ hn =>
        rw [hh] at hn
        cases hn
        exact ih k b rfl _ hrun hok
      | halt _ hn _ =>
        rw [hh] at hn
        cases hn

/-- `low_to_running` for a `HoareG`. -/
theorem HoareG.low {P Q : Evm fork Nat → Prop} (h : HoareG fork P Q) {k : Nat}
    {l : Evm fork Nat} (hp : P (addGas k l)) (within : GasMeter.gasHeld l.gas ≤ bound)
    {s : Evm fork Nat}
    (hs : Evm.runFrame (step fork) (step_decreases fork) bound runChild l within = .ok s)
    (hok : s.error = none) :
    ∃ z' w, Q (addGas k z') ∧
      Evm.runFrame (step fork) (step_decreases fork) bound runChild z' w = .ok s := by
  obtain ⟨z, hr, hq⟩ := h _ hp
  obtain ⟨z', w, rfl, hz⟩ := low_to_running hr k l rfl within hs hok
  exact ⟨z', w, hq, hz⟩

/-- A frame `At` some gas that is `addGas k` of `z'`: `z'` is `At` that gas minus `k`. -/
theorem at_unsh {code : ByteArray} {message : Message fork} {pc : Nat} {stack : List U256}
    {memory : ByteArray} {gas : Nat} {state : State.TransactionState} {substate : Substate}
    {k : Nat} {z' : Evm fork Nat} (h : At code message pc stack memory gas state substate (addGas k z')) :
    k ≤ gas ∧ At code message pc stack memory (gas - k) state substate z' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := h
  simp only [gas_addGas] at h7
  exact ⟨by omega, h1, h2, h3, h4, h5, h6, by omega, h8, h9, h10, h11, h12⟩

/-- A successful run, for any gas, from a frame where a `HoareG` to a running frame paying `c`
holds for every gas from `B ≥ c` on: `c ≤ gas`, and the run goes through that frame with
`gas - c`. -/
theorem ok_split {code : ByteArray} {message : Message fork} {pc pc' : Nat}
    {stack stack' : List U256} {memory memory' : ByteArray} {state state' : State.TransactionState}
    {substate substate' : Substate} {B c : Nat} (hB : c ≤ B)
    (h : ∀ g, B ≤ g → HoareG fork (At code message pc stack memory g state substate)
      (At code message pc' stack' memory' (g - c) state' substate'))
    {gas : Nat} {evm s : Evm fork Nat}
    (start : At code message pc stack memory gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) :
    c ≤ gas ∧ ∃ z' w, At code message pc' stack' memory' (gas - c) state' substate' z' ∧
      Evm.runFrame (step fork) (step_decreases fork) bound runChild z' w = .ok s := by
  obtain ⟨z', w, hq, hz⟩ := HoareG.low (h (gas + B) (by omega)) (at_addGas start B) within hrun hok
  obtain ⟨hk, hat⟩ := at_unsh hq
  refine ⟨by omega, z', w, ?_, hz⟩
  have : gas + B - c - B = gas - c := by omega
  rw [this] at hat
  exact hat

end UsdtVerify.Complete
