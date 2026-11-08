import UsdtVerify.Evm.Route
import UsdtVerify.Evm.Meter

/-!
# CALL over EthLib's EIP-8037 meter

Round 37. `callStep_child_rS`: `callStep_child_r` for a frame over `StateGasMeter`. CALL with no
value, below the greatest depth, with the gas of both accesses and the memory in the execution
gas left, sends the message. The caller pays the same execution gas as over the meter `Nat`, and
passes on its whole reservoir: the message carries the reservoir of the frame, and the caller
keeps a reservoir of 0 (EthLib's `finishCall`, `GasMeter.drain`). The other fields of the meter
are kept. `resumeCall_sgm`: the resume after the child. `lifts_gasStep`, `lifts_extcodesizeStep`:
GAS and EXTCODESIZE, the two other opcodes of the deprecated paths outside `simulated`, are
`Lifts` of their instruction over `Nat`.
-/

namespace UsdtVerify.Complete

open EthLib.Base (Fork U256 toAddressMasked Address)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts
open Deprecated

variable {fork : Fork}

/-- `callStep_child_r` over `StateGasMeter`: CALL (no value) below the greatest depth, with the gas
of both accesses and the memory in the execution gas left, along any route, sends the message,
which carries the reservoir of the frame; the caller keeps a reservoir of 0. -/
theorem callStep_child_rS (hfork : .berlin ≤ fork)
    {evm : Evm fork StateGasMeter} {g a i isz o osz : U256} {rest : List U256} {calleeCode : ByteArray}
    {r : Route}
    (hst : evm.stack.val = g :: a :: 0 :: i :: isz :: o :: osz :: rest)
    (hcode : evm.state.getCode (evm.state.getAccount (toAddressMasked a)).codeHash = .ok calleeCode)
    (hroute : Routes fork evm.state calleeCode r)
    (hdepth : evm.message.depth + 1 ≤ STACK_DEPTH_LIMIT)
    (hgas : callBaseCost fork (decide (toAddressMasked a ∉ evm.substate.accessedAddresses)) +
      routeCost fork (evm.substate.accessedAddresses.insert (toAddressMasked a)) r +
      (extendMemory evm.memory.size [(i, isz), (o, osz)]).cost ≤ evm.gas.gasLeft) :
    ∃ caller msg, callStep .call evm = .ok (.child caller msg (resumeCall fork caller 0 o osz)) ∧
      caller.code = evm.code ∧ caller.validJumpDestinations = evm.validJumpDestinations ∧
      caller.message = evm.message ∧ caller.pc = evm.pc ∧ caller.stack.val = rest ∧
      caller.memory = memoryExtend evm.memory
        (extendMemory evm.memory.size [(i, isz), (o, osz)]).expandBy ∧
      caller.gas = { evm.gas with reservoir := 0, gasLeft := evm.gas.gasLeft - ((messageCallGas fork 0 g.toNat evm.gas.gasLeft
        (extendMemory evm.memory.size [(i, isz), (o, osz)]).cost
        (callBaseCost fork (decide (toAddressMasked a ∉ evm.substate.accessedAddresses)) +
          routeCost fork (evm.substate.accessedAddresses.insert (toAddressMasked a)) r)).cost +
        (extendMemory evm.memory.size [(i, isz), (o, osz)]).cost) } ∧
      caller.running = evm.running ∧ caller.error = evm.error ∧ caller.output = evm.output ∧
      caller.state = (routeState (evm.state.recordAccountRead (toAddressMasked a)) r).recordAccountRead
        evm.message.currentTarget ∧
      caller.substate = routeSub { evm.substate with
        accessedAddresses := evm.substate.accessedAddresses.insert (toAddressMasked a) } r ∧
      msg.reservoir = evm.gas.reservoir ∧
      msg.gas = (messageCallGas fork 0 g.toNat evm.gas.gasLeft
        (extendMemory evm.memory.size [(i, isz), (o, osz)]).cost
        (callBaseCost fork (decide (toAddressMasked a ∉ evm.substate.accessedAddresses)) +
          routeCost fork (evm.substate.accessedAddresses.insert (toAddressMasked a)) r)).subCall ∧
      msg.caller = evm.message.currentTarget ∧ msg.currentTarget = toAddressMasked a ∧
      msg.target = some (toAddressMasked a) ∧
      msg.codeAddress = some (routeAddr (toAddressMasked a) r) ∧
      msg.code = routeCode calleeCode r ∧ msg.disablePrecompiles = r.isSome ∧
      msg.data = memoryReadBytes (memoryExtend evm.memory
        (extendMemory evm.memory.size [(i, isz), (o, osz)]).expandBy) i.toNat isz.toNat ∧
      msg.value = 0 ∧ msg.depth = evm.message.depth + 1 ∧
      msg.isStatic = evm.message.isStatic ∧ msg.blockEnv = evm.message.blockEnv ∧
      msg.txEnv = evm.message.txEnv ∧ msg.shouldTransferValue = true := by
  rcases evm with ⟨pc, ⟨l, hl⟩, memory, code, valid, ⟨gas, res, base, spill, comm, grant⟩, running,
    message, output, returnData, state, substate, error⟩
  simp only at hst
  subst hst
  have hgc : ∀ (tx : State.TransactionState) (x : Address) h,
      (tx.recordAccountRead x).getCode h = tx.getCode h := fun _ _ _ => rfl
  have hga : ∀ (tx : State.TransactionState) (x y : Address),
      (tx.recordAccountRead x).getAccount y = tx.getAccount y := fun _ _ _ => rfl
  have hal : ∀ (tx : State.TransactionState) (x y : Address),
      (tx.recordAccountRead x).isAccountAlive y = tx.isAccountAlive y := fun _ _ _ => rfl
  simp only at hcode hgas hdepth hroute ⊢
  have htw : Fork.tangerineWhistle ≤ fork := Nat.le_trans (by decide) hfork
  have hsd : Fork.spuriousDragon ≤ fork := Nat.le_trans (by decide) hfork
  generalize hcb : callBaseCost fork (decide (toAddressMasked a ∉ substate.accessedAddresses)) =
    cb at hgas ⊢
  have hcb' : callBaseCost fork (!decide (toAddressMasked a ∈ substate.accessedAddresses)) = cb :=
    by simpa using hcb
  generalize hdc : routeCost fork (substate.accessedAddresses.insert (toAddressMasked a)) r = dc
    at hgas ⊢
  generalize hM : (extendMemory memory.size [(i, isz), (o, osz)]).cost = M at hgas ⊢
  have hmx : maxMessageCallGas (gas - (cb + dc + M)) ≤ gas - (cb + dc + M) := Nat.sub_le _ _
  have hx : gas - M - (cb + dc) = gas - (cb + dc + M) := by omega
  have hmin : min g.toNat (maxMessageCallGas (gas - (cb + dc + M))) + (cb + dc) + M ≤ gas := by
    omega
  have hmin' : ¬ gas - (cb + dc + M) < min g.toNat (maxMessageCallGas (gas - (cb + dc + M))) := by
    omega
  have hk1 : ¬ gas < cb + M := by omega
  have hk2 : ¬ gas < cb + M + dc := by omega
  have hdel' : (if Fork.pectra ≤ fork then delegatedAddress calleeCode else none) =
      r.map Prod.fst := by
    rcases r with _ | ⟨d, dCode⟩
    · split
      · exact hroute ‹_›
      · rfl
    · simp [hroute.1, hroute.2.1]
  have hdcode : ∀ d dCode, r = some (d, dCode) → state.getCode (state.getAccount d).codeHash = .ok dCode := by
    rintro d dCode rfl; exact hroute.2.2
  have hdc' : ∀ d dCode, r = some (d, dCode) → accountAccessCost fork
      (!decide (toAddressMasked a = d) && !decide (d ∈ substate.accessedAddresses)) = dc := by
    rintro d dCode rfl
    rw [← hdc, routeCost, accCost]
    simp
  by_cases hG : fork ≥ .glamsterdam
  · rcases r with _ | ⟨d, dCode⟩
    · simp only [routeCost] at hdc
      subst hdc
      simp only [Nat.add_zero] at hgas hmin hmin' hx hk2 hmx ⊢
      simp [callStep, popCallOperands, popCallValue, CallKind.sendsValue, popWord, Stack.pop, bind,
        Except.bind, pure, Except.pure, accessAddress, hfork, checkGas, hG, accessDelegation,
        accountCode, recordAccountRead, hgc, hga, hal, hcode, hdel', htw, Except.mapError,
        callExtraGas, callNewAccountCost, callNewAccountStateGas, callValueCost,
        payCall, messageCallGas, chargeGas, GasMeter.charge, finishCall, genericCall, keepReads,
        GasMeter.gasLeft, GasMeter.drain, GasMeter.reservoir, StateGasMeter.charge,
        StateGasMeter.drain, StateGasMeter.chargeState, hcb', Nat.not_lt.mpr hdepth, hM,
        chargeStateGas, GasMeter.chargeState, hgas, hk1, hmin', hx, routeState, routeSub, routeAddr,
        routeCode]
      refine ⟨_, _, ⟨rfl, rfl, rfl⟩, ?_⟩
      and_intros
      all_goals first | rfl | (dsimp only; omega) | (dsimp only; congr 1; omega) | skip
    · simp [callStep, popCallOperands, popCallValue, CallKind.sendsValue, popWord, Stack.pop, bind,
        Except.bind, pure, Except.pure, accessAddress, hfork, checkGas, hG, accessDelegation,
        accountCode, recordAccountRead, hgc, hga, hal, hcode, hdel', hdcode d dCode rfl, htw,
        Except.mapError, callExtraGas, callNewAccountCost, callNewAccountStateGas, callValueCost,
        payCall, messageCallGas, chargeGas, GasMeter.charge, finishCall, genericCall, keepReads,
        GasMeter.gasLeft, GasMeter.drain, GasMeter.reservoir, StateGasMeter.charge,
        StateGasMeter.drain, StateGasMeter.chargeState, hcb', hdc' d dCode rfl,
        Nat.not_lt.mpr hdepth, hM, chargeStateGas, GasMeter.chargeState, hgas, Nat.not_lt.mpr hgas, hk1, hk2, hmin', hx,
        routeState, routeSub, routeAddr, routeCode]
      refine ⟨_, _, ⟨rfl, rfl, rfl⟩, ?_⟩
      and_intros
      all_goals first | rfl | (dsimp only; omega) | (dsimp only; congr 1; omega) | skip
  · have hmin2 : ¬ gas < min g.toNat (maxMessageCallGas (gas - M - (cb + dc))) + (cb + dc) + M := by
      rw [hx]; omega
    rcases r with _ | ⟨d, dCode⟩
    · simp only [routeCost] at hdc
      subst hdc
      simp only [Nat.add_zero] at hgas hmin2 ⊢
      simp [callStep, popCallOperands, popCallValue, CallKind.sendsValue, popWord, Stack.pop, bind,
        Except.bind, pure, Except.pure, accessAddress, hfork, checkGas, hG, accessDelegation,
        accountCode, recordAccountRead, hgc, hga, hal, hcode, hdel', htw, Except.mapError,
        callExtraGas, callNewAccountCost, callNewAccountStateGas, callValueCost,
        payCall, messageCallGas, chargeGas, GasMeter.charge, finishCall, genericCall, keepReads,
        GasMeter.gasLeft, GasMeter.drain, GasMeter.reservoir, StateGasMeter.charge,
        StateGasMeter.drain, hcb', Nat.not_lt.mpr hdepth, hM, hgas,
        hmin2, hsd, routeState, routeSub, routeAddr, routeCode]
      refine ⟨_, _, ⟨rfl, rfl, rfl⟩, ?_⟩
      and_intros
      all_goals first | rfl | (dsimp only; omega) | (dsimp only; congr 1; omega) | skip
    · simp [callStep, popCallOperands, popCallValue, CallKind.sendsValue, popWord, Stack.pop, bind,
        Except.bind, pure, Except.pure, accessAddress, hfork, checkGas, hG, accessDelegation,
        accountCode, recordAccountRead, hgc, hga, hal, hcode, hdel', hdcode d dCode rfl, htw,
        Except.mapError, callExtraGas, callNewAccountCost, callNewAccountStateGas, callValueCost,
        payCall, messageCallGas, chargeGas, GasMeter.charge, finishCall, genericCall, keepReads,
        GasMeter.gasLeft, GasMeter.drain, GasMeter.reservoir, StateGasMeter.charge,
        StateGasMeter.drain, hcb', hdc' d dCode rfl,
        Nat.not_lt.mpr hdepth, hM, hgas, hmin2, hsd, routeState, routeSub, routeAddr, routeCode]
      refine ⟨_, _, ⟨rfl, rfl, rfl⟩, ?_⟩
      and_intros
      all_goals first | rfl | (dsimp only; omega) | (dsimp only; congr 1; omega) | skip

/-- **The frame after the CALL over `StateGasMeter`** (round 37). When the caller frame resumes
from the child frame over `StateGasMeter` (EthLib's `resumeCall`, with no state gas of a new
account to give back), the same resume over the meter `Nat`, from the `toNat` frames, also
succeeds, and the two frames have the same fields but the gas. Over `Nat` the gas left is the
caller's plus the child's. Over `StateGasMeter` the execution gas left and the reservoir add up
to those of the caller and of the child. -/
theorem resumeCall_sgm {caller child y : Evm fork StateGasMeter} {o osz : U256}
    (h : resumeCall fork caller 0 o osz child = .ok y) :
    ∃ y', resumeCall fork (Meter.toNat caller) 0 o osz (Meter.toNat child) = .ok y' ∧
      Meter.toNat y = { y' with gas := y.gas.gasLeft } ∧
      y'.gas = caller.gas.gasLeft + child.gas.gasLeft ∧
      y.gas.gasLeft + y.gas.reservoir =
        caller.gas.gasLeft + caller.gas.reservoir + child.gas.gasLeft + child.gas.reservoir := by
  have hst : (Meter.toNat caller).stack = caller.stack := rfl
  have hc' : (Meter.toNat child).error = child.error := rfl
  rcases hc : child.error with _ | err
  · simp only [resumeCall, incorporateChild, refillStateGas, pushWord, bind, Except.bind, pure,
      Except.pure, hst, hc, hc', Option.isNone_none, ite_true] at h ⊢
    rcases hp : caller.stack.push 1 with e | st <;> simp only [hp] at h ⊢
    · cases h
    · cases h
      refine ⟨_, rfl, rfl, rfl, ?_⟩
      simp only [advance, GasMeter.absorb, StateGasMeter.absorb, StateGasMeter.repay, ite_true]
      omega
  · simp only [resumeCall, incorporateChild, refillStateGas, pushWord, bind, Except.bind, pure,
      Except.pure, hst, hc, hc', Option.isNone_some, Bool.false_eq_true, ite_false] at h ⊢
    rcases hp : caller.stack.push 0 with e | st <;> simp only [hp] at h ⊢
    · cases h
    · cases h
      refine ⟨_, rfl, rfl, rfl, ?_⟩
      simp only [advance, GasMeter.absorb, GasMeter.refill, StateGasMeter.absorb,
        StateGasMeter.refill, Bool.false_eq_true, ite_false]
      omega

/-- GAS over `StateGasMeter` is GAS over `Nat` on the execution gas: it charges only execution
gas and pushes the execution gas left (round 37). -/
theorem lifts_gasStep : Meter.Lifts (fork := fork)
    (readFrame OPCODE_GAS fun evm => BitVec.ofNat 256 (GasMeter.gasLeft evm.gas))
    (readFrame OPCODE_GAS fun evm => BitVec.ofNat 256 (GasMeter.gasLeft evm.gas)) :=
  Meter.lifts_readFrame _ _ _ fun _ _ => rfl

/-- EXTCODESIZE over `StateGasMeter` is EXTCODESIZE over `Nat` on the execution gas: it charges
only execution gas (round 37). -/
theorem lifts_extcodesizeStep : Meter.Lifts (fork := fork) extcodesizeStep extcodesizeStep := by
  intro g n
  unfold extcodesizeStep
  rw [Meter.popWord_lift]
  rcases popWord n with e | ⟨x, a⟩
  · rfl
  simp only [Except.map, bind, Except.bind]
  have hacc : ∀ (u : Address), accessAddress (Meter.lift g a) u =
      ((accessAddress a u).1, Meter.lift g (accessAddress a u).2) := by
    intro u
    unfold accessAddress
    split <;> rfl
  rw [hacc]
  rw [Meter.chargeGas_lift]
  rcases chargeGas (accessAddress a (toAddressMasked x)).2 _ with e | c
  · rfl
  simp only [Except.map]
  have hrec : ∀ (u : Address), recordAccountRead (Meter.lift g c) u =
      Meter.lift g (recordAccountRead c u) := fun _ => rfl
  have hcode : ∀ (u : Address) (b : Evm fork Nat),
      accountCode (Meter.lift g b) u = accountCode b u := fun _ _ => rfl
  rw [hrec, hcode]
  rcases accountCode (recordAccountRead c (toAddressMasked x)) (toAddressMasked x) with e | code
  · rfl
  simp only
  rw [Meter.pushWord_lift]
  rcases pushWord (recordAccountRead c (toAddressMasked x)) _ with e | d
  · rfl
  rfl

end UsdtVerify.Complete
