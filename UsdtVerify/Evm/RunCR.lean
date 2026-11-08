import UsdtVerify.Evm.RunCS
import UsdtVerify.Evm.StepSimR

/-!
# A run over the EIP-8037 meter at any reservoir gives `RunC`, with the gas after the CALL (round 42)

`runC_of_sgm` starts from reservoir 0 and leaves the gas after the CALL free. Here, from a frame of
`StateGasMeter` with any meter `g0`:

- before the CALL, step by step and exactly at any reservoir (`Meter.step_simXR`,
  `Meter.step_callXR`): each `Fwd` frame keeps the meter `g0` but for its execution gas left. A
  `Fwd` frame has no SSTORE that refills or charges state gas, so the reservoir does not move;
- at the CALL, the message run over `StateGasMeter` is the message over `Nat` with the reservoir
  of `g0`, and the caller has the meter `g0` with reservoir 0 (`RunSR`). The child over `Nat` is
  the `toNat` of the child over `StateGasMeter` with as gas its execution gas left plus its
  reservoir plus a constant `E`;
- after the CALL, `Shadow.shadow_runQ` from the frame after the resume, whose gas is its execution
  gas left plus its reservoir plus `E`. So the gas `G` of the end frame over `Nat` is at most the
  execution gas left plus the reservoir of the end over `StateGasMeter` plus `E`, and equal to it
  when no frame of the run of the meter `Nat` after the CALL refills at an SSTORE (`TailQ`).

`runC_of_sgmR` states it. The constant `E` is 97,920 times the measure of the first frame.
-/

namespace UsdtVerify.Complete

open EthLib.Base (Fork U256 toAddressMasked Address)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open UsdtVerify.Gas
open UsdtVerify.Meter
open UsdtVerify.Shadow (budget)
open GasCosts

variable {fork : Fork}

/-- The runs of a message runner over `StateGasMeter` from the meter `g0`, seen over `Nat`: the
runner ran the message `msg` with the reservoir of `g0` from a caller whose `toNat` is `cN` and
whose meter is `g0` with reservoir 0 but for its execution gas left, and gave a child whose
`toNat`, with as gas its execution gas left plus its reservoir plus `E`, is `chN`. -/
def RunSR {bound : Nat} (runChild : MessageRunner fork StateGasMeter bound) (g0 : StateGasMeter)
    (E : Nat) (cN : Evm fork Nat) (msg : Message fork) (chN : Evm fork Nat) : Prop :=
  ∃ cS msgS lt chS, runChild cS msgS lt = .ok chS ∧ msgS = { msg with reservoir := g0.reservoir } ∧
    toNat cS = cN ∧
    chN = { toNat chS.1 with gas := chS.1.gas.gasLeft + chS.1.gas.reservoir + E } ∧
    cS.gas = { g0 with reservoir := 0, gasLeft := cS.gas.gasLeft }

/-- The gas `G` of the end over `Nat` against the execution gas left plus the reservoir `Q` of the
end over `StateGasMeter`: at most `Q + E`, and equal to it when no running frame that the run from
`b` reaches refills at an SSTORE. -/
def TailQ (G Q E : Nat) (b : Evm fork Nat) : Prop :=
  G ≤ Q + E ∧
    ((∀ y, Reaches (Step fork) b y → y.running = true → Refill.NoRefillAtN y) → G = Q + E)

/-- **A run over `StateGasMeter` at any reservoir gives `RunC`, with the gas after the CALL.**
From Berlin, from a frame `m` of `StateGasMeter` with the meter `g0` but for its execution gas
left (or stopped), a run of the loop, for any gas bound and message runner, that ends in `s` with
no error, gives, for every `E` of at least 97,920 times the measure of `m`, `RunC` with the
relation `RunSR` and the predicate `TailQ` from `toNat m` to a frame with the fields of `s` and
some gas `G`. -/
theorem runC_of_sgmR (hfork : .berlin ≤ fork) {bound : Nat}
    {runChild : MessageRunner fork StateGasMeter bound} {g0 : StateGasMeter} {E : Nat}
    {m s : Evm fork StateGasMeter} {within : GasMeter.gasHeld m.gas ≤ bound}
    (h : Evm.runFrame (step fork) (step_decreases fork) bound runChild m within = .ok s)
    (hok : s.error = none)
    (hg : m.gas = { g0 with gasLeft := m.gas.gasLeft } ∨ m.running = false)
    (hE : STORAGE_SET_STATE_GAS * measure m ≤ E) :
    ∃ G, RunC fork (RunSR runChild g0 E) (TailQ G (s.gas.gasLeft + s.gas.reservoir) E)
      (toNat m) { toNat s with gas := G } := by
  by_cases hrun : m.running = true
  · have hm : m.gas = { g0 with gasLeft := m.gas.gasLeft } := by
      rcases hg with h | h
      · exact h
      · rw [h] at hrun; cases hrun
    have hrn : (toNat m).running = true := hrun
    have hcorr : CorrSR m.gas (step fork m) (step fork (toNat m)) →
        ∃ G, RunC fork (RunSR runChild g0 E) (TailQ G (s.gas.gasLeft + s.gas.reservoir) E)
          (toNat m) { toNat s with gas := G } := by
      rintro (⟨e, he, -⟩ | ⟨m', hS, hN, hb⟩)
      · exact absurd hok (sgm_step_error hrun he h)
      · rw [runFrame_of_step_eq_next hrun hS] at h
        have hlt : measure m' < measure m := step_decreases fork hrun hS
        have hb' : m'.gas = { g0 with gasLeft := m'.gas.gasLeft } ∨ m'.running = false := by
          rcases hb with hb | ⟨hr', -⟩
          · exact .inl (hb.trans (by rw [hm]))
          · exact .inr hr'
        have hE' : STORAGE_SET_STATE_GAS * measure m' ≤ E :=
          Nat.le_trans (Nat.mul_le_mul_left _ (Nat.le_of_lt hlt)) hE
        obtain ⟨G, hG⟩ := runC_of_sgmR hfork h hok hb' hE'
        exact ⟨G, .step (.next hrn hN) hG⟩
    by_cases hF : Fwd (toNat m)
    · rcases hF with ⟨hp, hnr, hns⟩ | hc
      · exact hcorr (step_simXR hp hnr hns)
      · rcases step_callXR hfork hc with hbad | hc' | ⟨caller, msg, o, osz, hS, hN, hcg⟩
        · rcases hbad with ⟨e, he⟩ | ⟨b, hb, hbr, hbe⟩
          · exact absurd hok (sgm_step_error hrun he h)
          · rw [runFrame_of_step_eq_next hrun hb, runFrame_of_running_eq_false hbr] at h
            cases h
            exact absurd hok hbe
        · exact hcorr hc'
        · have hdec := step_decreases fork hrun hS
          have lt : msg.gas < bound := Nat.lt_of_lt_of_le hdec.1 within
          rcases hch : runChild caller { msg with reservoir := m.gas.reservoir } lt with e | chS
          · rw [runFrame_of_runChild_eq_error hrun hS lt hch] at h
            cases h
          rcases hy : resumeCall fork caller 0 o osz chS.1 with e | y
          · by_cases ab : e.aborts = true
            · rw [runFrame_of_child_abort hrun hS lt hch hy ab] at h
              cases h
            · rw [runFrame_of_step_eq_child_error hrun hS lt hch hy (by simpa using ab)] at h
              cases h
              simp [exceptionalHalt] at hok
          rw [runFrame_of_step_eq_child hrun hS lt hch hy] at h
          have hmy : measure y < measure m := hdec.2 chS.1 y chS.2 hy
          obtain ⟨y', hy', hty, -, hQ⟩ := resumeCall_sgm hy
          have hcr : caller.gas.reservoir = 0 := by rw [hcg]
          have hres' := resumeCall_withGas hy'
            (chS.1.gas.gasLeft + chS.1.gas.reservoir + E)
          have hbud : budget y ≤ (toNat caller).gas + (chS.1.gas.gasLeft + chS.1.gas.reservoir + E) := by
            have hmul : STORAGE_SET_STATE_GAS * measure y ≤ E :=
              Nat.le_trans (Nat.mul_le_mul_left _ (Nat.le_of_lt hmy)) hE
            show y.gas.gasLeft + y.gas.reservoir + _ ≤ caller.gas.gasLeft + _
            omega
          obtain ⟨G, hEnd, hle, heq⟩ := Shadow.shadow_runQ hfork h hok
            (n := { y' with gas := (toNat caller).gas +
              (chS.1.gas.gasLeft + chS.1.gas.reservoir + E) })
            (by rw [hty]) hbud
          have hQ' : y.gas.gasLeft + y.gas.reservoir =
              (toNat caller).gas + chS.1.gas.gasLeft + chS.1.gas.reservoir := by
            show _ = caller.gas.gasLeft + _ + _
            omega
          refine ⟨G, .call hrn hN ⟨caller, { msg with reservoir := m.gas.reservoir }, lt, chS, hch,
            by rw [hm], rfl, rfl, by rw [hcg, hm]⟩
            hres' ⟨?_, fun hnr => ?_⟩ hEnd⟩
          · simp only at hle
            omega
          · have := heq hnr
            simp only at this
            omega
    · exact ⟨0, .out hrn hF⟩
  · have hl : m.running = false := by simpa using hrun
    rw [runFrame_of_running_eq_false hl] at h
    cases h
    exact ⟨m.gas.gasLeft, .stop hl⟩
termination_by measure m

end UsdtVerify.Complete
