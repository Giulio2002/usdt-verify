import UsdtVerify.Evm.RunCR

/-!
# Splitting a run over the EIP-8037 meter at any reservoir (round 42)

`ok_splitC` splits a run of the meter `Nat` with an abstract child. Here the same over
`StateGasMeter` itself, at any reservoir: a run over `StateGasMeter` that ends with no error,
from a frame whose `toNat` meets the precondition of a triple over `StepJ` (steps from frames
whose SSTORE neither refills nor charges state gas), goes through a frame whose `toNat` meets the
postcondition and whose meter is the meter of the first frame but for its execution gas left
(`low_to_runningS`, `ok_splitS`). And forward: a `StepJ` chain from the `toNat` of a frame is
followed by the run over `StateGasMeter` with the same meter (`fwd_reachesJ`).

These are the steps of a path where both meters charge the same execution gas, so the exact
gas of a path over `StateGasMeter` can be computed piece by piece, with the SSTOREs that refill
or charge state gas (where the meters differ) handled one at a time.
-/

namespace UsdtVerify.Complete

open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open UsdtVerify.Gas
open UsdtVerify.Meter
open UsdtVerify.Refill (StepJ HoareJ NoRefillAtN NoStateAtN)

variable {fork : Fork}

/-- **A successful run over `StateGasMeter` follows a `StepJ` chain.** Along a chain of `StepJ`
from `sh k (toNat m)` to `z`, a run over `StateGasMeter` from `m` (any reservoir) that ends with
no error goes through a frame `m'` with `z = sh k (toNat m')`, the meter of `m` but for its
execution gas left, and the same end. -/
theorem low_to_runningS {hi z : Evm fork Nat} (hr : Reaches (StepJ fork) hi z) :
    ∀ (k : Nat) (m : Evm fork StateGasMeter), hi = sh k (toNat m) →
    ∀ {bound : Nat} {runChild : MessageRunner fork StateGasMeter bound}
      {within : GasMeter.gasHeld m.gas ≤ bound} {s : Evm fork StateGasMeter},
      Evm.runFrame (step fork) (step_decreases fork) bound runChild m within = .ok s →
      s.error = none →
      ∃ m', z = sh k (toNat m') ∧ m'.gas = { m.gas with gasLeft := m'.gas.gasLeft } ∧
        ∃ w', Evm.runFrame (step fork) (step_decreases fork) bound runChild m' w' = .ok s := by
  induction hr with
  | refl =>
    rintro k m rfl bound runChild within s h hok
    exact ⟨m, rfl, rfl, within, h⟩
  | step hs _ ih =>
    rintro k m rfl bound runChild within s h hok
    have hrun : m.running = true := hs.1.1.running
    have hp : SimAtX (toNat m) := .inl hs.1.2.1
    have hnr : NoRefillAt m := Refill.noRefillAtN_sh k hs.2.1
    have hns : NoStateAtN (toNat m) := Refill.noStateAtN_sh k hs.2.2
    have hc := step_simXR hp hnr hns
    rcases hs.1.2.2 k (toNat m) rfl with ⟨e, he⟩ | ⟨b, hb, hbr, hbe⟩ | ⟨b, hb, hhi⟩
    · rcases hc with ⟨e', hS, -⟩ | ⟨m', -, hN, -⟩
      · exact absurd hok (sgm_step_error hrun hS h)
      · rw [he] at hN; cases hN
    · rcases hc with ⟨e', -, hN⟩ | ⟨m', hS, hN, -⟩
      · rw [hb] at hN; cases hN
      · rw [hb] at hN
        cases hN
        have hbr' : m'.running = false := hbr
        rw [runFrame_of_step_eq_next hrun hS, runFrame_of_running_eq_false hbr'] at h
        cases h
        exact absurd hok hbe
    · rcases hc with ⟨e', -, hN⟩ | ⟨m', hS, hN, hm'⟩
      · rw [hb] at hN; cases hN
      · rw [hb] at hN
        cases hN
        have hy := Step.deterministic hs.1.1 (.next (by rw [running_sh]; exact hrun) hhi)
        subst hy
        rw [runFrame_of_step_eq_next hrun hS] at h
        rcases hm' with hm' | ⟨hr', he'⟩
        · obtain ⟨m'', h1, h2, w', h3⟩ := ih k m' rfl h hok
          exact ⟨m'', h1, h2.trans (by rw [hm']), w', h3⟩
        · rw [runFrame_of_running_eq_false hr'] at h
          cases h
          exact absurd hok he'

/-- **`ok_split` over `StateGasMeter`, any reservoir.** A run over `StateGasMeter` from `m` that
ends with no error, where `toNat m` is an `At` frame with `gas` from which, for every gas from
`B ≥ c` on, a triple over `StepJ` reaches an `At` frame with `c` less: `c ≤ gas`, and the run
goes through a frame `m'` whose `toNat` is that frame with `gas - c`, whose meter is the meter of
`m` but for its execution gas left, and from which the run ends in the same frame. -/
theorem ok_splitS {code : ByteArray} {message : Message fork} {pc pc' : Nat}
    {stack stack' : List U256} {memory memory' : ByteArray} {state state' : State.TransactionState}
    {substate substate' : Substate} {B c : Nat} (hB : c ≤ B)
    (h : ∀ g, B ≤ g → HoareJ fork (At code message pc stack memory g state substate)
      (At code message pc' stack' memory' (g - c) state' substate'))
    {gas : Nat} {m s : Evm fork StateGasMeter}
    (start : At code message pc stack memory gas state substate (toNat m))
    {bound : Nat} {runChild : MessageRunner fork StateGasMeter bound}
    {within : GasMeter.gasHeld m.gas ≤ bound}
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild m within = .ok s)
    (hok : s.error = none) :
    c ≤ gas ∧ ∃ m', At code message pc' stack' memory' (gas - c) state' substate' (toNat m') ∧
      m'.gas = { m.gas with gasLeft := m'.gas.gasLeft } ∧
      ∃ w', Evm.runFrame (step fork) (step_decreases fork) bound runChild m' w' = .ok s := by
  obtain ⟨z, hr, hq⟩ := h (gas + B) (by omega) _ (at_sh start B)
  obtain ⟨m', rfl, hg, w', h'⟩ := low_to_runningS hr B m rfl hrun hok
  obtain ⟨hk, hat⟩ := at_unsh hq
  refine ⟨by omega, m', ?_, hg, w', h'⟩
  have : gas + B - c - B = gas - c := by omega
  rw [this] at hat
  exact hat

/-- `ok_splitS` for a triple over `StepG` between `At` frames whose storage reads the same, with
less than 97,920 gas paid (`HoareG.toJA`). -/
theorem ok_splitSA {code : ByteArray} {message : Message fork} {pc pc' : Nat}
    {stack stack' : List U256} {memory memory' : ByteArray} {state state' : State.TransactionState}
    {substate substate' : Substate} {B c : Nat} (hB : c ≤ B)
    (h : ∀ g, B ≤ g → HoareG fork (At code message pc stack memory g state substate)
      (At code message pc' stack' memory' (g - c) state' substate'))
    (hc : c < 97920) (hst : ∀ a k, state'.getStorage a k = state.getStorage a k)
    {gas : Nat} {m s : Evm fork StateGasMeter}
    (start : At code message pc stack memory gas state substate (toNat m))
    {bound : Nat} {runChild : MessageRunner fork StateGasMeter bound}
    {within : GasMeter.gasHeld m.gas ≤ bound}
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild m within = .ok s)
    (hok : s.error = none) :
    c ≤ gas ∧ ∃ m', At code message pc' stack' memory' (gas - c) state' substate' (toNat m') ∧
      m'.gas = { m.gas with gasLeft := m'.gas.gasLeft } ∧
      ∃ w', Evm.runFrame (step fork) (step_decreases fork) bound runChild m' w' = .ok s :=
  ok_splitS hB (fun g hg => Refill.HoareG.toJA (h g hg) (by omega) hst) start hrun hok

/-- **A `StepJ` chain run forward over `StateGasMeter`.** A `StepJ` chain from `toNat m` to a
frame `z` that runs or has no error is followed by the run over `StateGasMeter` from `m` (any
reservoir): there is a frame `m'` with `toNat m' = z` and the meter of `m` but for its execution
gas left, and the run from `m` is the run from `m'`. -/
theorem fwd_reachesJ {x z : Evm fork Nat} (hr : Reaches (StepJ fork) x z)
    (hz : z.running = true ∨ z.error = none) :
    ∀ (m : Evm fork StateGasMeter), toNat m = x →
      ∃ m', toNat m' = z ∧ m'.gas = { m.gas with gasLeft := m'.gas.gasLeft } ∧
        ∀ {bound : Nat} {runChild : MessageRunner fork StateGasMeter bound}
          (within : GasMeter.gasHeld m.gas ≤ bound), ∃ w',
          Evm.runFrame (step fork) (step_decreases fork) bound runChild m within =
            Evm.runFrame (step fork) (step_decreases fork) bound runChild m' w' := by
  induction hr with
  | refl =>
    rintro m rfl
    exact ⟨m, rfl, rfl, fun within => ⟨within, rfl⟩⟩
  | step hs hr' ih =>
    rename_i x x1 z
    rintro m rfl
    have hrun : m.running = true := hs.1.1.running
    have hp : SimAtX (toNat m) := .inl hs.1.2.1
    have hc := step_simXR hp hs.2.1 hs.2.2
    cases hs1 : hs.1.1 with
    | next _ hN =>
      rcases hc with ⟨e, -, he⟩ | ⟨m', hS, hN', hm'⟩
      · rw [hN] at he; cases he
      · rw [hN] at hN'
        cases hN'
        have hm'' : m'.gas = { m.gas with gasLeft := m'.gas.gasLeft } := by
          rcases hm' with hm' | ⟨hr1, he1⟩
          · exact hm'
          · exfalso
            have := reaches_stopped (reaches_toStep (hr'.mono fun h => h.1)) hr1
            rw [this] at hz
            rcases hz with h | h
            · have h' : m'.running = true := h
              rw [hr1] at h'; cases h'
            · exact he1 h
        obtain ⟨m'', h1, h2, h3⟩ := ih hz m' rfl
        refine ⟨m'', h1, h2.trans (by rw [hm'']), fun within => ?_⟩
        rw [runFrame_of_step_eq_next hrun hS]
        exact h3 _
    | halt _ hN hab =>
      exfalso
      have := reaches_stopped (reaches_toStep (hr'.mono fun h => h.1)) rfl
      rw [this] at hz
      rcases hz with h | h
      · simp [exceptionalHalt] at h
      · simp [exceptionalHalt] at h

end UsdtVerify.Complete
