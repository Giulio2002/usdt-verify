import UsdtVerify.Evm.RunC

/-!
# A run over the EIP-8037 meter gives `RunC` (round 39)

From a frame of `StateGasMeter` with reservoir 0, a run of the loop of the interpreter that ends
with no error gives a `RunC` of the meter `Nat` from the `toNat` frame, for the relation `RunS` of
its message runner:

- before the CALL, step by step and exactly (`Meter.step_simX`, `Meter.step_callX`): every frame
  that is `Fwd` gives the same step over both meters, and a frame that is not `Fwd` ends the
  `RunC` (`RunC.out`);
- at the CALL, both meters send the same message from corresponding callers (`Meter.CallCorr`).
  The child over `Nat` is the `toNat` of the child over `StateGasMeter` with a gas chosen large
  (`RunS` leaves the gas of the child free), and the run after the CALL is the run of the meter
  `Nat` with more gas of `Shadow.shadow_run` (`Ends`).

So the end frame of the `RunC` has the fields of the end of the run over `StateGasMeter`, with
some gas (`runC_of_sgm`). `endsOk_of_sgm`: from any reservoir, the run gives `EndsOk`.
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

/-- The runs of a message runner over `StateGasMeter`, seen over `Nat`: the runner ran the
message from a caller whose `toNat` is `cN` and gave a child whose `toNat` is `chN` with some
gas. The caller and the message have reservoir 0, as at the CALL from reservoir 0
(`Meter.CallCorr`). -/
def RunS {bound : Nat} (runChild : MessageRunner fork StateGasMeter bound) (cN : Evm fork Nat)
    (msg : Message fork) (chN : Evm fork Nat) : Prop :=
  ∃ cS lt chS, runChild cS msg lt = .ok chS ∧ toNat cS = cN ∧
    chN = { toNat chS.1 with gas := chN.gas } ∧ cS.gas.reservoir = 0 ∧ msg.reservoir = 0

/-- The resume after a CALL over `Nat` from a child with other gas: the same frame, whose gas is
the caller's plus the child's. -/
theorem resumeCall_withGas {c ch y : Evm fork Nat} {o osz : U256}
    (h : resumeCall fork c 0 o osz ch = .ok y) (K : Nat) :
    resumeCall fork c 0 o osz { ch with gas := K } = .ok { y with gas := c.gas + K } := by
  rcases hce : ch.error with _ | err
  · simp only [resumeCall, incorporateChild, refillStateGas, pushWord, bind, Except.bind, pure,
      Except.pure, hce, Option.isNone_none, ite_true] at h ⊢
    rcases hp : c.stack.push 1 with e | st <;> simp only [hp] at h ⊢
    · cases h
    · cases h
      rfl
  · simp only [resumeCall, incorporateChild, refillStateGas, pushWord, bind, Except.bind, pure,
      Except.pure, hce, Option.isNone_some, Bool.false_eq_true, ite_false] at h ⊢
    rcases hp : c.stack.push 0 with e | st <;> simp only [hp] at h ⊢
    · cases h
    · cases h
      rfl

/-- A run that ends with an error from a step that fails. -/
theorem sgm_step_error {bound : Nat} {runChild : MessageRunner fork StateGasMeter bound}
    {m s : Evm fork StateGasMeter} {within : GasMeter.gasHeld m.gas ≤ bound} {e : EvmError}
    (hrun : m.running = true) (hs : step fork m = .error e)
    (h : Evm.runFrame (step fork) (step_decreases fork) bound runChild m within = .ok s) :
    s.error ≠ none := by
  by_cases ab : e.aborts = true
  · rw [runFrame_of_step_eq_abort hrun hs ab] at h
    cases h
  · rw [runFrame_of_step_eq_error hrun hs (by simpa using ab)] at h
    cases h
    simp [exceptionalHalt]

/-- **A run over `StateGasMeter` gives `RunC`.** From Berlin, from a frame `m` of
`StateGasMeter` with reservoir 0 (or stopped), a run of the loop of the interpreter, for any gas
bound and message runner, that ends in `s` with no error, gives `RunC` with the relation `RunS` of
the runner from `toNat m` to a frame with the fields of `s` and some gas. -/
theorem runC_of_sgm (hfork : .berlin ≤ fork) {bound : Nat}
    {runChild : MessageRunner fork StateGasMeter bound} {m s : Evm fork StateGasMeter}
    {within : GasMeter.gasHeld m.gas ≤ bound}
    (h : Evm.runFrame (step fork) (step_decreases fork) bound runChild m within = .ok s)
    (hok : s.error = none) (hres : m.gas.reservoir = 0 ∨ m.running = false) :
    ∃ G, RunC fork (RunS runChild) (toNat m) { toNat s with gas := G } := by
  by_cases hrun : m.running = true
  · have hr : m.gas.reservoir = 0 := by
      rcases hres with h | h
      · exact h
      · rw [h] at hrun; cases hrun
    have hrn : (toNat m).running = true := hrun
    -- the step over `StateGasMeter` and the step over `Nat`, when they correspond
    have hcorr : CorrS (step fork m) (step fork (toNat m)) →
        ∃ G, RunC fork (RunS runChild) (toNat m) { toNat s with gas := G } := by
      rintro (⟨e, he, -⟩ | ⟨m', hS, hN, hb⟩)
      · exact absurd hok (sgm_step_error hrun he h)
      · rw [runFrame_of_step_eq_next hrun hS] at h
        have hlt : measure m' < measure m := step_decreases fork hrun hS
        obtain ⟨G, hG⟩ := runC_of_sgm hfork h hok hb
        exact ⟨G, .step (.next hrn hN) hG⟩
    by_cases hF : Fwd (toNat m)
    · rcases hF with ⟨hp, hnr⟩ | hc
      · exact hcorr (step_simX hr hp hnr)
      · rcases step_callX hfork hr hc with hbad | hc' | ⟨caller, msg, o, osz, hS, hN, hcr, hmr⟩
        · rcases hbad with ⟨e, he⟩ | ⟨b, hb, hbr, hbe⟩
          · exact absurd hok (sgm_step_error hrun he h)
          · rw [runFrame_of_step_eq_next hrun hb, runFrame_of_running_eq_false hbr] at h
            cases h
            exact absurd hok hbe
        · exact hcorr hc'
        · have lt : msg.gas < bound := Nat.lt_of_lt_of_le (step_decreases fork hrun hS).1 within
          rcases hch : runChild caller msg lt with e | chS
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
          obtain ⟨y', hy', hty, -, -⟩ := resumeCall_sgm hy
          have hres' := resumeCall_withGas hy' (budget y)
          obtain ⟨G, hE⟩ := Shadow.shadow_run hfork h hok
            (n := { y' with gas := (toNat caller).gas + budget y })
            (by rw [hty]) (Nat.le_add_left _ _)
          exact ⟨G, .call hrn hN ⟨caller, lt, chS, hch, rfl, rfl, hcr, hmr⟩ hres' hE⟩
    · exact ⟨0, .out hrn hF⟩
  · have hl : m.running = false := by simpa using hrun
    rw [runFrame_of_running_eq_false hl] at h
    cases h
    exact ⟨m.gas.gasLeft, .stop hl⟩
termination_by measure m

/-- From any frame of `StateGasMeter`, a run of the loop that ends with no error gives `EndsOk`
from the `toNat` frame (`Shadow.shadow_ends`). -/
theorem endsOk_of_sgm (hfork : .berlin ≤ fork) {bound : Nat}
    {runChild : MessageRunner fork StateGasMeter bound} {m s : Evm fork StateGasMeter}
    {within : GasMeter.gasHeld m.gas ≤ bound}
    (h : Evm.runFrame (step fork) (step_decreases fork) bound runChild m within = .ok s)
    (hok : s.error = none) : EndsOk fork (toNat m) :=
  let ⟨_, hE⟩ := Shadow.shadow_ends hfork h hok
  ⟨budget m, _, hE, hok⟩

end UsdtVerify.Complete
