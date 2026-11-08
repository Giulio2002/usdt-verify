import UsdtVerify.Evm.Shadow
import UsdtVerify.Evm.Iff

/-!
# A run over the EIP-8037 meter with at least the gas of a run of the meter `Nat` (round 42)

`Shadow.shadow_run` goes from a run over `StateGasMeter` to a run of the meter `Nat` with more
gas. Here is the other direction, at any reservoir and with refills allowed: a run of the meter
`Nat` along `StepG` from a frame with the fields of a frame `m` of `StateGasMeter` and at most its
execution gas left is followed by the run over `StateGasMeter` from `m`, and at each frame the
execution gas left over `StateGasMeter` is at least the gas over `Nat`.

The step at an SSTORE is where the meters differ: over `StateGasMeter` a refill first credits the
execution gas up to the spill and the reservoir with the rest, and the state gas comes from the
reservoir first. Each of these leaves at least as much execution gas as the meter `Nat`, which
charges the state gas from its one counter and never refills. The other opcodes of `simulated`
charge only execution gas (`Lifts`), and with more gas they give the same frame with more gas
(`RunMono`). The opcodes that read the gas (GAS) or call (CALL) are not `simulated`.

- `sgm_charges_dom`: the charges of an SSTORE over `StateGasMeter`, from at least the execution
  gas of the meter `Nat`, succeed and leave at least what they leave over `Nat`.
- `dom_step`: one step.
- `dom_run`: a `StepG` chain to a stopped frame with no error gives a run of the loop over
  `StateGasMeter`, for any gas bound and message runner, that ends in a frame with the fields of
  the end of the chain and at least its gas as execution gas left.
- `runsOkS_of_specG`: a specification over `StepG` to frames with no error, from the `toNat` of
  `m`, gives a run over `StateGasMeter` from `m` that ends with no error.
-/

namespace UsdtVerify.Shadow

open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open UsdtVerify.Gas
open UsdtVerify.Meter
open GasCosts

variable {fork : Fork}

/-- The charges of an SSTORE over `StateGasMeter` (a refill of `r`, `c` execution gas, `s` state
gas), from a meter with at least `x` execution gas left, where `c + s ≤ x`: both charges succeed,
and the execution gas left after them is at least `x - c - s`. -/
theorem sgm_charges_dom {g : StateGasMeter} {x r c s : Nat} (hx : x ≤ g.gasLeft)
    (hc : c ≤ x) (hs : s ≤ x - c) :
    ∃ g2, GasMeter.charge (GasMeter.refill g r) c = .ok g2 ∧
      ∃ g3, GasMeter.chargeState g2 s = .ok g3 ∧ x - c - s ≤ g3.gasLeft := by
  simp only [GasMeter.charge, StateGasMeter.charge, GasMeter.refill, StateGasMeter.refill,
    GasMeter.chargeState, StateGasMeter.chargeState]
  have h1 : ¬ g.gasLeft + min r g.spill < c := by omega
  simp only [h1, ↓reduceIte]
  refine ⟨_, rfl, ?_⟩
  split
  · exact ⟨_, rfl, by simp only; omega⟩
  · split
    · exact ⟨_, rfl, by simp only; omega⟩
    · rename_i h2 h3
      exfalso
      simp only at h3
      omega

/-- **One step, with at least the gas.** A step of the meter `Nat` from a running `SimAt` frame
`n` with the fields of `m` and at most its execution gas left, to a next frame that runs or has no
error, is followed by the step over `StateGasMeter` from `m`, at any reservoir: it gives a next
frame with the fields of the next frame over `Nat` and at least its gas as execution gas left. -/
theorem dom_step (hfork : .berlin ≤ fork) {m : Evm fork StateGasMeter} {n n' : Evm fork Nat}
    (hp : SimAt n) (hs : step fork n = .ok (.next n'))
    (hn' : n'.running = true ∨ n'.error = none) (hn : n = { toNat m with gas := n.gas })
    (hle : n.gas ≤ m.gas.gasLeft) :
    ∃ m', step fork m = .ok (.next m') ∧ n' = { toNat m' with gas := n'.gas } ∧
      n'.gas ≤ m'.gas.gasLeft := by
  generalize hG : n.gas = G at hn hle
  subst hn
  by_cases hlt : m.pc < m.code.size
  · have hlt' : ({ toNat m with gas := G } : Evm fork Nat).pc <
        ({ toNat m with gas := G } : Evm fork Nat).code.size := hlt
    rcases hop : Op.ofByte fork m.code[m.pc] with _ | op
    · rw [step_of_ofByte_eq_none hlt' hop] at hs; cases hs
    obtain ⟨hsim, hi⟩ := hp hlt' op hop
    obtain ⟨runN, hN⟩ := Option.isSome_iff_exists.mp hi
    by_cases hss : op = .sstore
    · subst hss
      rw [step_of_instruction hlt' hop instruction_sstoreM] at hs
      rcases hx : sstoreStep ({ toNat m with gas := G } : Evm fork Nat) with e | b
      · rw [hx] at hs; cases hs
      rw [hx] at hs
      cases hs
      obtain ⟨key, new, st2, g2, g3, st, hok, rfl⟩ := sstoreOk_of_step hfork hx hn'
      have hc := hok.charge
      have hcs := hok.chargeState
      simp only [GasMeter.charge, GasMeter.refill, GasMeter.chargeState] at hc hcs
      split at hc
      · cases hc
      cases hc
      split at hcs
      · cases hcs
      cases hcs
      rename_i hc1 hc2
      obtain ⟨g2S, hcS, g3S, hcsS, hge⟩ := sgm_charges_dom (g := m.gas)
        (r := sstoreStateRefill fork
          (m.state.getStorageOriginal m.message.currentTarget (U256.toBeBytes key))
          (m.state.getStorage m.message.currentTarget (U256.toBeBytes key)) new)
        hle (Nat.le_of_not_lt hc1) (Nat.le_of_not_lt hc2)
      have hokS : SstoreOk m key new st2 g2S g3S st := by
        refine ⟨hok.stack, fun h => hok.stipend ⟨h.1, ?_⟩, hcS, hcsS, hok.static, hok.set⟩
        have := h.2
        change m.gas.gasLeft ≤ CALL_STIPEND at this
        change G ≤ CALL_STIPEND
        omega
      refine ⟨sstoreAfter m key new st2 g3S st, ?_, rfl, hge⟩
      rw [step_of_instruction hlt hop instruction_sstoreM, sstoreStep_of_ok hfork hokS]
      rfl
    · obtain ⟨runS, hS, hL⟩ := lifts_of_simulated hsim hss hN
      rw [step_of_instruction hlt' hop hN] at hs
      rcases hb' : runN ({ toNat m with gas := G } : Evm fork Nat) with err | b
      · rw [hb'] at hs; cases hs
      rw [hb'] at hs
      cases hs
      have hk : toNat m = sh (m.gas.gasLeft - G) ({ toNat m with gas := G } : Evm fork Nat) := by
        simp only [sh, toNat]
        congr 1
        omega
      rcases runMono_of_simulated hsim hN ({ toNat m with gas := G } : Evm fork Nat)
          (m.gas.gasLeft - G) with (⟨err, he⟩ | ⟨b', he, hbr, hbe⟩) | ⟨b', he, hhi⟩
      · rw [hb'] at he; cases he
      · rw [hb'] at he
        cases he
        rcases hn' with h | h
        · rw [hbr] at h; cases h
        · exact absurd h hbe
      · rw [hb'] at he
        cases he
        have e := hL m.gas (toNat m)
        rw [lift_toNat, hk, hhi] at e
        refine ⟨lift m.gas (sh (m.gas.gasLeft - G) _), ?_, rfl, ?_⟩
        · rw [step_of_instruction hlt hop hS, e]
          rfl
        · exact Nat.le_add_right _ _
  · rw [step_of_size_le (evm := ({ toNat m with gas := G } : Evm fork Nat))
      (by simp only [toNat]; omega)] at hs
    cases hs
    refine ⟨_, step_of_size_le (by omega), rfl, ?_⟩
    show G ≤ m.gas.gasLeft
    exact hle

/-- **A run with at least the gas.** A `StepG` chain from `x` to a stopped frame `z` with no
error is followed, from every frame `m` of `StateGasMeter` with the fields of `x` and at least its
gas as execution gas left (any reservoir), by the loop over `StateGasMeter`, for any gas bound and
message runner: it ends in a frame with the fields of `z` and at least its gas as execution gas
left. -/
theorem dom_run (hfork : .berlin ≤ fork) {bound : Nat}
    {runChild : MessageRunner fork StateGasMeter bound}
    {x z : Evm fork Nat} (hc : Reaches (StepG fork) x z) (hz : z.running = false)
    (hze : z.error = none) :
    ∀ (m : Evm fork StateGasMeter), x = { toNat m with gas := x.gas } → x.gas ≤ m.gas.gasLeft →
      ∀ (within : GasMeter.gasHeld m.gas ≤ bound),
      ∃ s, Evm.runFrame (step fork) (step_decreases fork) bound runChild m within = .ok s ∧
        z = { toNat s with gas := z.gas } ∧ z.gas ≤ s.gas.gasLeft := by
  induction hc with
  | refl =>
    intro m hm hle within
    have hmr : m.running = false := by rw [hm] at hz; exact hz
    exact ⟨m, runFrame_of_running_eq_false hmr, hm, hle⟩
  | step hs hr ih =>
    rename_i x x1 z
    intro m hm hle within
    have hrun : m.running = true := by
      have h := hs.1.running
      rw [hm] at h
      exact h
    cases hs1 : hs.1 with
    | next _ hN =>
      have hn' : x1.running = true ∨ x1.error = none := by
        by_cases h : x1.running = true
        · exact .inl h
        · have := reaches_stopped (reaches_toStep hr) (by simpa using h)
          rw [← this]; exact .inr hze
      obtain ⟨m', hS, hm', hle'⟩ := dom_step hfork hs.2.1 hN hn' hm hle
      rw [runFrame_of_step_eq_next hrun hS]
      exact ih hz hze m' hm' hle' _
    | halt _ hN hab =>
      have := reaches_stopped (reaches_toStep hr) rfl
      rw [this] at hze
      simp [exceptionalHalt] at hze

/-- **A specification over `StepG` run over `StateGasMeter`, at any reservoir.** From a frame
`m` of `StateGasMeter` whose `toNat` meets the precondition of a specification over `StepG` to
frames with no error, the loop over `StateGasMeter`, for any gas bound and message runner, ends
with no error. Any reservoir, and SSTORE may refill. -/
theorem runsOkS_of_specG (hfork : .berlin ≤ fork) {bound : Nat}
    {runChild : MessageRunner fork StateGasMeter bound} {P Q : Evm fork Nat → Prop}
    (h : SpecG fork P Q) (hQ : ∀ e, Q e → e.error = none) {m : Evm fork StateGasMeter}
    (hp : P (toNat m)) (within : GasMeter.gasHeld m.gas ≤ bound) :
    RunsOkS fork bound runChild m within := by
  obtain ⟨z, hr, hz, hq⟩ := h _ hp
  obtain ⟨s, hs, hzs, -⟩ := dom_run hfork hr hz (hQ z hq) m rfl (Nat.le_refl _) within
  refine ⟨s, hs, ?_⟩
  have : z.error = s.error := by rw [hzs]; rfl
  rw [← this]
  exact hQ z hq

end UsdtVerify.Shadow
