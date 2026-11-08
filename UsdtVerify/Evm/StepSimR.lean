import UsdtVerify.Evm.StepSim
import UsdtVerify.Evm.NoState

/-!
# One step over the two meters at any reservoir (round 42)

`Meter.step_simX` relates a step over `StateGasMeter` to a step over `Nat` from a frame with
reservoir 0. With a reservoir above 0, a charge of state gas comes from the reservoir, so the
execution gas left no longer follows the gas of the meter `Nat`. Every other charge is a charge of
execution gas, and GAS pushes the execution gas left on both meters. So the step is the same at
any reservoir when an SSTORE neither refills nor charges state gas:

- `CorrR g rS rN`: the same error, or a frame `m'` and its `toNat`, where `m'` has the meter `g`
  but for its execution gas left, or `m'` is stopped with an error.
- `Lifts.corrR`, `sim_sstoreStepR` (SSTORE with no refill and no state gas),
  `sim_of_simulatedR`.
- `step_simXR`: `step_simX` at any reservoir, for a frame whose SSTORE, if any, charges no state
  gas (`Refill.NoStateAtN`). The next frame keeps the meter but for its execution gas left.
- `step_callXR`: `step_callX` at any reservoir. When both steps send a message, the message over
  `StateGasMeter` is the message over `Nat` with the reservoir of the frame, and the caller keeps
  the meter of the frame with reservoir 0 (`CallCorrR`).
-/

namespace UsdtVerify.Meter

open EthLib.Base (Fork U256 toAddressMasked Address)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open UsdtVerify.Gas
open UsdtVerify.Complete
open GasCosts

variable {fork : Fork}

/-- Results of an instruction over the two meters that correspond at the meter `g`: the same
error, or a frame and its `toNat`, where the frame has the meter `g` but for its execution gas
left, or is stopped with an error. -/
def CorrR (g : StateGasMeter) (rS : Except EvmError (Evm fork StateGasMeter))
    (rN : Except EvmError (Evm fork Nat)) : Prop :=
  (∃ e, rS = .error e ∧ rN = .error e) ∨
    ∃ m', rS = .ok m' ∧ rN = .ok (toNat m') ∧
      (m'.gas = { g with gasLeft := m'.gas.gasLeft } ∨ (m'.running = false ∧ m'.error ≠ none))

theorem Lifts.corrR {runS : Evm fork StateGasMeter → Except EvmError (Evm fork StateGasMeter)}
    {runN : Evm fork Nat → Except EvmError (Evm fork Nat)} (h : Lifts runS runN)
    (m : Evm fork StateGasMeter) : CorrR m.gas (runS m) (runN (toNat m)) := by
  have e := h m.gas (toNat m)
  rw [lift_toNat] at e
  rw [e]
  rcases runN (toNat m) with e | n
  · exact .inl ⟨e, rfl, rfl⟩
  · exact .inr ⟨lift m.gas n, rfl, rfl, .inl rfl⟩

theorem keepReads_corrR {g : StateGasMeter} {b : Evm fork Nat}
    {rS : Except EvmError (Evm fork StateGasMeter)} {rN : Except EvmError (Evm fork Nat)}
    (h : rS = rN.map (lift g)) : CorrR g (keepReads (lift g b) id rS) (keepReads b id rN) := by
  subst h
  rcases rN with e | r
  · simp only [keepReads, Except.map]
    split
    · exact .inl ⟨e, rfl, rfl⟩
    · exact .inr ⟨_, rfl, rfl, .inr ⟨rfl, by simp [exceptionalHalt]⟩⟩
  · exact .inr ⟨lift g r, rfl, rfl, .inl rfl⟩

theorem chargeStateGas_lift0 (g : StateGasMeter) (n : Evm fork Nat) :
    chargeStateGas (lift g n) 0 = (chargeStateGas n 0).map (lift g) := by
  rcases g with ⟨gl, res, base, sp, com, gr⟩
  simp [chargeStateGas, GasMeter.chargeState, StateGasMeter.chargeState, lift, bind,
    Except.bind, Except.map, pure, Except.pure]

/-- An SSTORE from `m` charges no state gas (`Refill.NoStateN` of `toNat m`). -/
def NoState (m : Evm fork StateGasMeter) : Prop :=
  ∀ key new rest, m.stack.val = key :: new :: rest →
    sstoreStateGas fork (m.state.getStorageOriginal m.message.currentTarget key.toBeBytes)
      (m.state.getStorage m.message.currentTarget key.toBeBytes) new = 0

/-- **SSTORE at any reservoir.** From a frame where the SSTORE neither refills nor charges state
gas, SSTORE over the two meters gives corresponding results at the meter of the frame. -/
theorem sim_sstoreStepR (m : Evm fork StateGasMeter) (hnr : NoRefill m) (hns : NoState m) :
    CorrR m.gas (sstoreStep m) (sstoreStep (toNat m)) := by
  obtain ⟨g, n, rfl⟩ : ∃ g n, m = lift g n := ⟨m.gas, toNat m, rfl⟩
  show CorrR g (sstoreStep (lift g n)) (sstoreStep n)
  unfold sstoreStep
  rw [show (lift g n).message = n.message from rfl]
  split
  · exact .inl ⟨_, rfl, rfl⟩
  simp only [bind, Except.bind]
  rw [popWord_lift]
  rcases h1 : popWord n with e | ⟨word, a1⟩
  · exact .inl ⟨e, rfl, rfl⟩
  simp only [Except.map]
  rw [popWord_lift]
  rcases h2 : popWord a1 with e | ⟨new, a2⟩
  · exact .inl ⟨e, rfl, rfl⟩
  simp only [Except.map]
  obtain ⟨s1, t1, m1⟩ := popWord_ok h1
  obtain ⟨s2, t2, m2⟩ := popWord_ok h2
  have hR := hnr word new a2.stack.val (by show n.stack.val = _; rw [s1, s2])
  have hS := hns word new a2.stack.val (by show n.stack.val = _; rw [s1, s2])
  change sstoreStateRefill fork (n.state.getStorageOriginal n.message.currentTarget _)
    (n.state.getStorage n.message.currentTarget _) new = 0 at hR
  change sstoreStateGas fork (n.state.getStorageOriginal n.message.currentTarget _)
    (n.state.getStorage n.message.currentTarget _) new = 0 at hS
  rw [← t1, ← t2, ← m1, ← m2] at hR hS
  rw [show GasMeter.gasLeft (lift g a2).gas = GasMeter.gasLeft a2.gas from rfl]
  split
  · exact .inl ⟨_, rfl, rfl⟩
  rw [show (lift g a2).state = a2.state from rfl, show (lift g a2).message = a2.message from rfl,
    accessStorageKey_lift]
  generalize accessStorageKey a2 a2.message.currentTarget word.toBeBytes = p
  rcases p with ⟨cold, b0⟩
  simp only []
  rw [show recordStorageRead (lift g b0) a2.message.currentTarget word.toBeBytes =
    lift g (recordStorageRead b0 a2.message.currentTarget word.toBeBytes) from rfl]
  generalize recordStorageRead b0 a2.message.currentTarget word.toBeBytes = b
  rw [hR, hS]
  have hz : refillStateGas (lift g b) 0 = lift g b := by
    simp only [refillStateGas, GasMeter.refill, refill_zero]
  rw [hz]
  have hz' : refillStateGas b 0 = b := rfl
  rw [hz', chargeGas_lift]
  rcases chargeGas b _ with e | c1
  · exact keepReads_corrR rfl
  simp only [Except.map]
  rw [chargeStateGas_lift0]
  rcases chargeStateGas c1 0 with e | c2
  · exact keepReads_corrR rfl
  simp only [Except.map]
  rw [show (lift g c2).message = c2.message from rfl, show (lift g c2).state = c2.state from rfl]
  split
  · exact keepReads_corrR rfl
  rcases (c2.state.setStorage a2.message.currentTarget word.toBeBytes new).mapError EvmError.state
    with e | st
  · exact keepReads_corrR rfl
  · exact keepReads_corrR rfl

/-- The instruction of a `simulated` opcode gives, over the two meters, corresponding results at
the meter of the frame, at any reservoir, provided an SSTORE neither refills nor charges state
gas. -/
theorem sim_of_simulatedR {op : Op} (hs : simulated op = true)
    {runN : Evm fork Nat → Except EvmError (Evm fork Nat)}
    (hN : instruction (Meter := Nat) fork op = some runN) :
    ∃ runS, instruction (Meter := StateGasMeter) fork op = some runS ∧
      ∀ m : Evm fork StateGasMeter, (op = .sstore → NoRefill m ∧ NoState m) →
        CorrR m.gas (runS m) (runN (toNat m)) := by
  cases op <;> simp only [simulated, Bool.false_eq_true] at hs
  all_goals simp only [instruction, stackOnlyStep, controlFlowStep, memoryDataStep, returnOpStep,
    environmentStep, accountStep, storageStep, transientStorageStep, logOpStep, selfdestructOpStep,
    HOrElse.hOrElse, OrElse.orElse, Option.orElse, Option.some.injEq] at hN ⊢
  case revert =>
    by_cases hb : Fork.byzantium ≤ fork
    · simp only [hb, ↓reduceIte, Option.some.injEq] at hN ⊢
      subst hN
      exact ⟨_, rfl, fun m _ => lifts_revertStep.corrR m⟩
    · simp only [hb, ↓reduceIte, reduceCtorEq] at hN
  case sstore =>
    subst hN
    exact ⟨_, rfl, fun m hn => sim_sstoreStepR m (hn trivial).1 (hn trivial).2⟩
  all_goals subst hN
  all_goals refine ⟨_, rfl, fun m _ => ?_⟩
  all_goals first
    | with_reducible exact (lifts_binaryOp _ _).corrR m
    | with_reducible exact (lifts_unaryOp _ _).corrR m
    | with_reducible exact lifts_expStep.corrR m
    | with_reducible exact lifts_keccak256Step.corrR m
    | with_reducible exact (lifts_readFrame _ _ _ (fun _ _ => rfl)).corrR m
    | with_reducible exact lifts_calldataloadStep.corrR m
    | with_reducible exact lifts_popStep.corrR m
    | with_reducible exact lifts_mloadStep.corrR m
    | with_reducible exact lifts_mstoreStep.corrR m
    | with_reducible exact lifts_sloadStep.corrR m
    | with_reducible exact lifts_jumpStep.corrR m
    | with_reducible exact lifts_jumpiStep.corrR m
    | with_reducible exact lifts_jumpdestStep.corrR m
    | with_reducible exact lifts_stopStep.corrR m
    | with_reducible exact lifts_returnStep.corrR m
    | with_reducible exact (lifts_pushN _).corrR m
    | with_reducible exact (lifts_dupN _).corrR m
    | with_reducible exact (lifts_swapN _).corrR m
    | with_reducible exact (lifts_logStep _).corrR m

/-- Results of a step over the two meters that correspond at the meter `g`: the same error, or a
next frame and its `toNat`, where the next frame has the meter `g` but for its execution gas left,
or is stopped with an error. -/
def CorrSR (g : StateGasMeter) (rS : Except EvmError (StepResult fork StateGasMeter))
    (rN : Except EvmError (StepResult fork Nat)) : Prop :=
  (∃ e, rS = .error e ∧ rN = .error e) ∨
    ∃ m', rS = .ok (.next m') ∧ rN = .ok (.next (toNat m')) ∧
      (m'.gas = { g with gasLeft := m'.gas.gasLeft } ∨ (m'.running = false ∧ m'.error ≠ none))

theorem corrSR_map {g : StateGasMeter} {rS : Except EvmError (Evm fork StateGasMeter)}
    {rN : Except EvmError (Evm fork Nat)} (h : CorrR g rS rN) :
    CorrSR g (.next <$> rS) (.next <$> rN) := by
  rcases h with ⟨e, rfl, rfl⟩ | ⟨m, rfl, rfl, hm⟩
  · exact .inl ⟨e, rfl, rfl⟩
  · exact .inr ⟨m, rfl, rfl, hm⟩

/-- **One step at any reservoir.** From a frame of `StateGasMeter` with any reservoir whose
`toNat` is `SimAtX`, where an SSTORE neither refills nor charges state gas, the step and the step
of the meter `Nat` from its `toNat` give the same error, or a next frame and its `toNat`, where the
next frame keeps the meter of the frame but for its execution gas left, or is stopped with an
error. -/
theorem step_simXR {m : Evm fork StateGasMeter} (hp : SimAtX (toNat m)) (hnr : NoRefillAt m)
    (hns : Refill.NoStateAtN (toNat m)) :
    CorrSR m.gas (step fork m) (step fork (toNat m)) := by
  rcases hp with hp | ⟨hlt, hop | hop⟩
  · by_cases hlt : m.pc < m.code.size
    · have hlt' : (toNat m).pc < (toNat m).code.size := hlt
      rcases hop : Op.ofByte fork m.code[m.pc] with _ | op
      · rw [step_of_ofByte_eq_none hlt hop, step_of_ofByte_eq_none hlt' hop]
        exact .inl ⟨_, rfl, rfl⟩
      · obtain ⟨hs, hi⟩ := hp hlt' op hop
        obtain ⟨runN, hN⟩ := Option.isSome_iff_exists.mp hi
        obtain ⟨runS, hS, hsim⟩ := sim_of_simulatedR hs hN
        rw [step_of_instruction hlt hop hS, step_of_instruction hlt' hop hN]
        exact corrSR_map (hsim m (fun h => ⟨hnr hlt (h ▸ hop), hns hlt (h ▸ hop)⟩))
    · rw [step_of_size_le (by omega),
        step_of_size_le (evm := toNat m) (by simp only [toNat]; omega)]
      exact .inr ⟨_, rfl, rfl, .inl rfl⟩
  · rw [step_of_instruction (evm := m) hlt hop instruction_extcodesizeS,
      step_of_instruction hlt hop instruction_extcodesizeN]
    exact corrSR_map (lifts_extcodesizeStep.corrR m)
  · rw [step_of_instruction (evm := m) hlt hop instruction_gasS,
      step_of_instruction hlt hop instruction_gasN]
    exact corrSR_map (lifts_gasStep.corrR m)

/-- Two steps that send a message at the meter `g`: the caller over `Nat` is the `toNat` of the
caller over `StateGasMeter`, which has the meter `g` with reservoir 0 but for its execution gas
left, the message over `StateGasMeter` is the message over `Nat` with the reservoir of `g`, and
both resume through `resumeCall`. -/
def CallCorrR (g : StateGasMeter) (rS : Except EvmError (StepResult fork StateGasMeter))
    (rN : Except EvmError (StepResult fork Nat)) : Prop :=
  ∃ caller msg o osz,
    rS = .ok (.child caller { msg with reservoir := g.reservoir } (resumeCall fork caller 0 o osz)) ∧
    rN = .ok (.child (toNat caller) msg (resumeCall fork (toNat caller) 0 o osz)) ∧
    caller.gas = { g with reservoir := 0, gasLeft := caller.gas.gasLeft }

/-- **The step of a CALL at any reservoir.** From Berlin, from a frame of `StateGasMeter` with any
reservoir whose `toNat` is `CallX`: the step fails or halts the frame with an error, or the two
steps give the same error or corresponding next frames at the meter of the frame, or they send a
message (`CallCorrR`). -/
theorem step_callXR (hfork : .berlin ≤ fork) {m : Evm fork StateGasMeter}
    (hc : CallX (toNat m)) :
    StepBadS (step fork m) ∨ CorrSR m.gas (step fork m) (step fork (toNat m)) ∨
      CallCorrR m.gas (step fork m) (step fork (toNat m)) := by
  obtain ⟨hlt, hop, g, a, i, isz, o, osz, rest, c, hst, hcode⟩ := hc
  have hS : step fork m = callStep .call m :=
    step_of_messageInstruction (Meter := StateGasMeter) hlt hop rfl rfl
  have hN : step fork (toNat m) = callStep .call (toNat m) :=
    step_of_messageInstruction hlt hop instruction_call messageInstruction_call
  rw [hS, hN]
  change m.stack.val = _ at hst
  change m.state.getCode (m.state.getAccount (toAddressMasked a)).codeHash = .ok c at hcode
  rcases routes_or_missing (fork := fork) m.state c with ⟨r, hroute⟩ | ⟨d, e, hpec, hd, hmiss⟩
  · by_cases hlow : m.gas.gasLeft <
        callBaseCost fork (decide (toAddressMasked a ∉ m.substate.accessedAddresses)) +
        routeCost fork (m.substate.accessedAddresses.insert (toAddressMasked a)) r +
        (extendMemory m.memory.size [(i, isz), (o, osz)]).cost
    · exact .inl (callStep_low_rS hfork hst hcode hroute hlow)
    have hgas := Nat.le_of_not_lt hlow
    by_cases hdeep : STACK_DEPTH_LIMIT < m.message.depth + 1
    · obtain ⟨after, h1, h2, h3⟩ := callStep_deep_simR hfork hst hcode hroute hdeep hgas
      exact .inr (.inl (.inr ⟨after, h1, h2, .inl h3⟩))
    · obtain ⟨caller, msgS, msg, h1, h2, h3, h4⟩ :=
        callStep_child_simR hfork hst hcode hroute (by omega) hgas
      subst h3
      exact .inr (.inr ⟨caller, msg, o, osz, h1, h2, h4⟩)
  · exact .inl (callStep_missingS hfork hst hcode hpec hd hmiss)

end UsdtVerify.Meter
