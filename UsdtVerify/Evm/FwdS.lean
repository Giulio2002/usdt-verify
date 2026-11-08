import UsdtVerify.Evm.SgmSplit
import UsdtVerify.Evm.CallMeter

/-!
# A path run forward over the EIP-8037 meter, through a CALL (round 44)

`fwd_reachesJ` (round 42) follows a `StepJ` chain forward over `StateGasMeter`. Here the pieces
to follow a whole path that sends one message, from any reservoir:

- `fwd_splitS`: a triple over `StepG` between two `At` frames, cheap (below 97,920 gas) and
  reading the storage as at its start, is followed forward from every frame whose `toNat` meets
  its precondition with enough execution gas. The frame reached keeps the meter but for its
  execution gas left, and the run from the first frame is the run from it.
- `fwd_stepS`: one step of an opcode other than SSTORE, from a frame whose `toNat` is `SimAtX`, is
  followed forward the same way.
- `step_callS`: CALL over `StateGasMeter` (EthLib's `callStep`), as `callStep_child_rS` states it.
- `resumeCall_okS`: the resume over `StateGasMeter` from a child with no error. The frame pushes
  1, writes the start of the output, takes the state and substate of the child, and its meter is
  `GasMeter.absorb` of the caller's and the child's meters for a child that succeeded, which holds
  their execution gas left and reservoirs (`absorb_sum`).
- `runFrame_childS`: a run that ends after a step that sends a message went through the runner
  and the resume, and goes on from the resumed frame. `runFrame_child_fwdS` is the converse.
-/

namespace UsdtVerify.Complete

open EthLib.Base (Fork U256 toAddressMasked)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open UsdtVerify.Gas
open UsdtVerify.Meter
open UsdtVerify.Refill (StepJ HoareJ NoRefillAtN NoStateAtN)
open GasCosts

variable {fork : Fork}

/-- **A cheap stretch followed forward over `StateGasMeter`.** -/
theorem fwd_splitS {code : ByteArray} {message : Message fork} {pc pc' : Nat}
    {stack stack' : List U256} {memory memory' : ByteArray} {state state' : State.TransactionState}
    {substate substate' : Substate} {B c : Nat}
    (h : ∀ g, B ≤ g → HoareG fork (At code message pc stack memory g state substate)
      (At code message pc' stack' memory' (g - c) state' substate'))
    (hc : c < 97920) (hst : ∀ a k, state'.getStorage a k = state.getStorage a k)
    {gas : Nat} (hB : B ≤ gas) {m : Evm fork StateGasMeter}
    (start : At code message pc stack memory gas state substate (toNat m)) :
    ∃ m', At code message pc' stack' memory' (gas - c) state' substate' (toNat m') ∧
      m'.gas = { m.gas with gasLeft := m'.gas.gasLeft } ∧
      ∀ {bound : Nat} {runChild : MessageRunner fork StateGasMeter bound}
        (within : GasMeter.gasHeld m.gas ≤ bound), ∃ w',
        Evm.runFrame (step fork) (step_decreases fork) bound runChild m within =
          Evm.runFrame (step fork) (step_decreases fork) bound runChild m' w' := by
  have hJ : HoareJ fork (At code message pc stack memory gas state substate)
      (At code message pc' stack' memory' (gas - c) state' substate') :=
    Refill.HoareG.toJA (h gas hB) (by omega) hst
  obtain ⟨z, hr, hz⟩ := hJ _ start
  obtain ⟨m', hm', hg, hrun⟩ := fwd_reachesJ hr (.inl hz.2.2.2.2.2.2.2.1) m rfl
  exact ⟨m', hm' ▸ hz, hg, hrun⟩

/-- **One step of an opcode other than SSTORE, followed forward over `StateGasMeter`.** -/
theorem fwd_stepS {m : Evm fork StateGasMeter} {y : Evm fork Nat} {op : Op}
    (hp : SimAtX (toNat m)) (hlt : (toNat m).pc < (toNat m).code.size)
    (hop : Op.ofByte fork (toNat m).code[(toNat m).pc] = some op) (hne : op ≠ .sstore)
    (hrun : m.running = true) (hN : step fork (toNat m) = .ok (.next y))
    (hy : y.running = true) :
    ∃ m', toNat m' = y ∧ m'.gas = { m.gas with gasLeft := m'.gas.gasLeft } ∧
      ∀ {bound : Nat} {runChild : MessageRunner fork StateGasMeter bound}
        (within : GasMeter.gasHeld m.gas ≤ bound), ∃ w',
        Evm.runFrame (step fork) (step_decreases fork) bound runChild m within =
          Evm.runFrame (step fork) (step_decreases fork) bound runChild m' w' := by
  have hnr : NoRefillAt m := fun h h' => absurd (hop.symm.trans h') (by
    intro e; exact hne (Option.some.inj e))
  have hns : NoStateAtN (toNat m) := fun h h' => absurd (hop.symm.trans h') (by
    intro e; exact hne (Option.some.inj e))
  rcases step_simXR hp hnr hns with ⟨e, -, he⟩ | ⟨m', hS, hN', hm'⟩
  · rw [hN] at he; cases he
  · rw [hN] at hN'
    cases hN'
    have hm'' : m'.gas = { m.gas with gasLeft := m'.gas.gasLeft } := by
      rcases hm' with hm' | ⟨hr1, -⟩
      · exact hm'
      · exfalso
        have h' : m'.running = true := hy
        rw [hr1] at h'; cases h'
    exact ⟨m', rfl, hm'', fun within => ⟨_, runFrame_of_step_eq_next hrun hS⟩⟩

/-- CALL over `StateGasMeter` is EthLib's `callStep` of a CALL. -/
theorem step_callS {m : Evm fork StateGasMeter} (hlt : m.pc < m.code.size)
    (hop : Op.ofByte fork m.code[m.pc] = some .call) : step fork m = callStep .call m :=
  step_of_messageInstruction (Meter := StateGasMeter) hlt hop rfl rfl

/-- **The resume over `StateGasMeter` from a child with no error.** -/
theorem resumeCall_okS {caller child : Evm fork StateGasMeter} {o osz : U256}
    (hlen : caller.stack.val.length < STACK_LIMIT) (he : child.error = none) :
    ∃ after, resumeCall fork caller 0 o osz child = .ok after ∧
      after.code = caller.code ∧ after.validJumpDestinations = caller.validJumpDestinations ∧
      after.message = caller.message ∧ after.pc = caller.pc + 1 ∧
      after.stack.val = 1 :: caller.stack.val ∧
      after.memory = memoryWrite caller.memory o.toNat
        (child.output.extract 0 (min osz.toNat child.output.size)) ∧
      after.gas = GasMeter.absorb caller.gas child.gas true ∧
      after.running = caller.running ∧ after.error = caller.error ∧ after.output = caller.output ∧
      after.state = child.state ∧ after.substate = (incorporateChild fork caller child).substate := by
  have hne : caller.stack.val.length ≠ STACK_LIMIT := Nat.ne_of_lt hlen
  unfold resumeCall incorporateChild
  simp only [he, Option.isNone_none, ite_true]
  simp [pushWord, Stack.push, bind, Except.bind, pure, Except.pure, advance, hne]

/-- The meter after a CALL whose child succeeded holds, as execution gas left and reservoir, the
caller's and the child's. -/
theorem absorb_sum (c ch : StateGasMeter) :
    (GasMeter.absorb c ch true).gasLeft + (GasMeter.absorb c ch true).reservoir =
      c.gasLeft + c.reservoir + ch.gasLeft + ch.reservoir := by
  show (StateGasMeter.absorb c ch true).gasLeft + (StateGasMeter.absorb c ch true).reservoir = _
  simp only [StateGasMeter.absorb, StateGasMeter.repay, ite_true]
  omega

/-- **A run through a step that sends a message.** A run over `StateGasMeter` from a running frame
whose step sends a message, that ends in `s` with no error, ran the message to a frame, resumed
from it, and goes on from the resumed frame. -/
theorem runFrame_childS {bound : Nat} {runChild : MessageRunner fork StateGasMeter bound}
    {m c s : Evm fork StateGasMeter} {msg : Message fork}
    {resume : Evm fork StateGasMeter → Except EvmError (Evm fork StateGasMeter)}
    {within : GasMeter.gasHeld m.gas ≤ bound} (hrun : m.running = true)
    (hS : step fork m = .ok (.child c msg resume))
    (h : Evm.runFrame (step fork) (step_decreases fork) bound runChild m within = .ok s)
    (hok : s.error = none) :
    ∃ (lt : msg.gas < bound) (chS : { child : Evm fork StateGasMeter //
        GasMeter.gasHeld child.gas ≤ msg.gas }) (y : Evm fork StateGasMeter),
      runChild c msg lt = .ok chS ∧ resume chS.1 = .ok y ∧
      ∃ w, Evm.runFrame (step fork) (step_decreases fork) bound runChild y w = .ok s := by
  have hdec := step_decreases fork hrun hS
  have lt : msg.gas < bound := Nat.lt_of_lt_of_le hdec.1 within
  rcases hch : runChild c msg lt with e | chS
  · rw [runFrame_of_runChild_eq_error hrun hS lt hch] at h
    cases h
  rcases hy : resume chS.1 with e | y
  · by_cases ab : e.aborts = true
    · rw [runFrame_of_child_abort hrun hS lt hch hy ab] at h
      cases h
    · rw [runFrame_of_step_eq_child_error hrun hS lt hch hy (by simpa using ab)] at h
      cases h
      simp [exceptionalHalt] at hok
  rw [runFrame_of_step_eq_child hrun hS lt hch hy] at h
  exact ⟨lt, chS, y, hch, hy, _, h⟩

/-- **A run through a step that sends a message, forward.** When the runner ends the message in a
frame and the resume from it gives a frame, the run from the sender is the run from that frame. -/
theorem runFrame_child_fwdS {bound : Nat} {runChild : MessageRunner fork StateGasMeter bound}
    {m c y : Evm fork StateGasMeter} {msg : Message fork}
    {resume : Evm fork StateGasMeter → Except EvmError (Evm fork StateGasMeter)}
    {within : GasMeter.gasHeld m.gas ≤ bound} (hrun : m.running = true)
    (hS : step fork m = .ok (.child c msg resume)) (lt : msg.gas < bound)
    {chS : { child : Evm fork StateGasMeter // GasMeter.gasHeld child.gas ≤ msg.gas }}
    (hch : runChild c msg lt = .ok chS) (hy : resume chS.1 = .ok y) :
    ∃ w, Evm.runFrame (step fork) (step_decreases fork) bound runChild m within =
      Evm.runFrame (step fork) (step_decreases fork) bound runChild y w :=
  ⟨_, runFrame_of_step_eq_child hrun hS lt hch hy⟩

end UsdtVerify.Complete
