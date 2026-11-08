import UsdtVerify.Evm.CallMeter

/-!
# CALL over the two meters, step by step (round 38)

`Evm/Meter.lean` relates one step over `StateGasMeter` to one step over `Nat` for the opcodes of
`simulated`, and Evm/CallMeter.lean shows that GAS and EXTCODESIZE are `Lifts`. Here the CALL of
the deprecated paths (no value, along a route), from a frame of the meter `StateGasMeter` with
reservoir 0:

- `callStep_child_sim`: below the greatest depth, with the gas of the accesses and the memory,
  both meters send the same message, and the caller over `Nat` is the `toNat` of the caller over
  `StateGasMeter`, whose reservoir is 0.
- `callStep_deep_sim`: at the greatest depth, both steps give a next frame, the one over `Nat`
  the `toNat` of the one over `StateGasMeter`, whose reservoir is 0.
- `callStep_low_rS`, `callStep_missingS`: `callStep_low_r` and `callStep_missing` over
  `StateGasMeter`: the step fails or halts the frame with an error (`StepBadS`).
- `callStep_child_simR`, `callStep_deep_simR` (round 42): the first two at any reservoir. The
  message over `StateGasMeter` is the message over `Nat` with the reservoir of the frame.
-/

namespace UsdtVerify.Complete

open EthLib.Base (Fork U256 toAddressMasked Address)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts
open Deprecated

variable {fork : Fork}

/-- `StepBad` over `StateGasMeter`: the step fails, or halts the frame with an error. -/
def StepBadS (r : Except EvmError (StepResult fork StateGasMeter)) : Prop :=
  (∃ e, r = .error e) ∨ ∃ b, r = .ok (.next b) ∧ b.running = false ∧ b.error ≠ none

/-- **CALL below the greatest depth, over both meters.** From a frame of `StateGasMeter` with
reservoir 0, CALL (no value) below the greatest depth, with the gas of both accesses and the memory
in the execution gas left, along any route: the step sends a message, and the step over `Nat` from
the `toNat` frame sends the same message from the `toNat` of the caller. The caller has reservoir
0. -/
theorem callStep_child_sim (hfork : .berlin ≤ fork)
    {m : Evm fork StateGasMeter} (hr : m.gas.reservoir = 0) {g a i isz o osz : U256}
    {rest : List U256} {calleeCode : ByteArray} {r : Route}
    (hst : m.stack.val = g :: a :: 0 :: i :: isz :: o :: osz :: rest)
    (hcode : m.state.getCode (m.state.getAccount (toAddressMasked a)).codeHash = .ok calleeCode)
    (hroute : Routes fork m.state calleeCode r)
    (hdepth : m.message.depth + 1 ≤ STACK_DEPTH_LIMIT)
    (hgas : callBaseCost fork (decide (toAddressMasked a ∉ m.substate.accessedAddresses)) +
      routeCost fork (m.substate.accessedAddresses.insert (toAddressMasked a)) r +
      (extendMemory m.memory.size [(i, isz), (o, osz)]).cost ≤ m.gas.gasLeft) :
    ∃ caller msg, callStep .call m = .ok (.child caller msg (resumeCall fork caller 0 o osz)) ∧
      callStep .call (Meter.toNat m) =
        .ok (.child (Meter.toNat caller) msg (resumeCall fork (Meter.toNat caller) 0 o osz)) ∧
      caller.gas.reservoir = 0 := by
  rcases m with ⟨pc, ⟨l, hl⟩, memory, code, valid, ⟨gas, res, base, spill, comm, grant⟩, running,
    message, output, returnData, state, substate, error⟩
  simp only at hst hr
  subst hst hr
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
  have hmin' : ¬ gas - (cb + dc + M) < min g.toNat (maxMessageCallGas (gas - (cb + dc + M))) := by
    omega
  have hk1 : ¬ gas < cb + M := by omega
  have hk2 : ¬ gas < cb + M + dc := by omega
  have hmin2 : ¬ gas < min g.toNat (maxMessageCallGas (gas - M - (cb + dc))) + (cb + dc) + M := by
    rw [hx]; omega
  have hmin3 : ¬ gas < min g.toNat (maxMessageCallGas (gas - (cb + dc + M))) + (cb + dc) + M := by
    omega
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
  rcases r with _ | ⟨d, dCode⟩
  · simp only [routeCost] at hdc
    subst hdc
    simp only [Nat.add_zero] at hgas hmin' hx hk2 hmx hmin2 hmin3 ⊢
    by_cases hG : fork ≥ .glamsterdam <;>
    simp [callStep, popCallOperands, popCallValue, CallKind.sendsValue, popWord, Stack.pop, bind,
      Except.bind, pure, Except.pure, accessAddress, hfork, checkGas, hG, accessDelegation,
      accountCode, recordAccountRead, hgc, hga, hal, hcode, hdel', htw, hsd, Except.mapError,
      callExtraGas, callNewAccountCost, callNewAccountStateGas, callValueCost,
      payCall, messageCallGas, chargeGas, GasMeter.charge, finishCall, genericCall, keepReads,
      GasMeter.gasLeft, GasMeter.drain, GasMeter.reservoir, StateGasMeter.charge,
      StateGasMeter.drain, StateGasMeter.chargeState, hcb', Nat.not_lt.mpr hdepth, hM,
      chargeStateGas, GasMeter.chargeState, hgas, Nat.not_lt.mpr hgas, hk1, hmin', hmin2, hmin3, hx,
      routeState, routeSub, routeAddr, routeCode, Meter.toNat]
    all_goals first
      | (simp only [and_assoc, exists_eq_left', exists_and_left, and_true]; done)
      | (simp only [and_assoc, exists_eq_left', exists_and_left, and_true]; and_intros <;> rfl)
  · by_cases hG : fork ≥ .glamsterdam <;>
    simp [callStep, popCallOperands, popCallValue, CallKind.sendsValue, popWord, Stack.pop, bind,
      Except.bind, pure, Except.pure, accessAddress, hfork, checkGas, hG, accessDelegation,
      accountCode, recordAccountRead, hgc, hga, hal, hcode, hdel', hdcode d dCode rfl, htw, hsd,
      Except.mapError, callExtraGas, callNewAccountCost, callNewAccountStateGas, callValueCost,
      payCall, messageCallGas, chargeGas, GasMeter.charge, finishCall, genericCall, keepReads,
      GasMeter.gasLeft, GasMeter.drain, GasMeter.reservoir, StateGasMeter.charge,
      StateGasMeter.drain, StateGasMeter.chargeState, hcb', hdc' d dCode rfl,
      Nat.not_lt.mpr hdepth, hM, chargeStateGas, GasMeter.chargeState, hgas, Nat.not_lt.mpr hgas,
      hk1, hk2, hmin', hmin2, hmin3, hx, routeState, routeSub, routeAddr, routeCode, Meter.toNat]
    all_goals first
      | (simp only [and_assoc, exists_eq_left', exists_and_left, and_true]; done)
      | (simp only [and_assoc, exists_eq_left', exists_and_left, and_true]; and_intros <;> rfl)

/-- **CALL at the greatest depth, over both meters.** From a frame of `StateGasMeter` with
reservoir 0, CALL (no value) at the greatest depth, with the gas of both accesses and the memory,
along any route: no message runs, both steps give a next frame, the one over `Nat` the `toNat` of
the one over `StateGasMeter`, whose reservoir is 0. -/
theorem callStep_deep_sim (hfork : .berlin ≤ fork)
    {m : Evm fork StateGasMeter} (hr : m.gas.reservoir = 0) {g a i isz o osz : U256}
    {rest : List U256} {calleeCode : ByteArray} {r : Route}
    (hst : m.stack.val = g :: a :: 0 :: i :: isz :: o :: osz :: rest)
    (hcode : m.state.getCode (m.state.getAccount (toAddressMasked a)).codeHash = .ok calleeCode)
    (hroute : Routes fork m.state calleeCode r)
    (hdeep : STACK_DEPTH_LIMIT < m.message.depth + 1)
    (hgas : callBaseCost fork (decide (toAddressMasked a ∉ m.substate.accessedAddresses)) +
      routeCost fork (m.substate.accessedAddresses.insert (toAddressMasked a)) r +
      (extendMemory m.memory.size [(i, isz), (o, osz)]).cost ≤ m.gas.gasLeft) :
    ∃ after, callStep .call m = .ok (.next after) ∧
      callStep .call (Meter.toNat m) = .ok (.next (Meter.toNat after)) ∧
      after.gas.reservoir = 0 := by
  rcases m with ⟨pc, ⟨l, hl⟩, memory, code, valid, ⟨gas, res, base, spill, comm, grant⟩, running,
    message, output, returnData, state, substate, error⟩
  simp only at hst hr
  subst hst hr
  have hgc : ∀ (tx : State.TransactionState) (x : Address) h,
      (tx.recordAccountRead x).getCode h = tx.getCode h := fun _ _ _ => rfl
  have hga : ∀ (tx : State.TransactionState) (x y : Address),
      (tx.recordAccountRead x).getAccount y = tx.getAccount y := fun _ _ _ => rfl
  have hal : ∀ (tx : State.TransactionState) (x y : Address),
      (tx.recordAccountRead x).isAccountAlive y = tx.isAccountAlive y := fun _ _ _ => rfl
  simp only at hcode hgas hdeep hroute ⊢
  have htw : Fork.tangerineWhistle ≤ fork := Nat.le_trans (by decide) hfork
  have hsd : Fork.spuriousDragon ≤ fork := Nat.le_trans (by decide) hfork
  generalize hcb : callBaseCost fork (decide (toAddressMasked a ∉ substate.accessedAddresses)) =
    cb at hgas
  have hcb' : callBaseCost fork (!decide (toAddressMasked a ∈ substate.accessedAddresses)) = cb :=
    by simpa using hcb
  generalize hdc : routeCost fork (substate.accessedAddresses.insert (toAddressMasked a)) r = dc
    at hgas
  generalize hM : (extendMemory memory.size [(i, isz), (o, osz)]).cost = M at hgas
  have hmx : maxMessageCallGas (gas - (cb + dc + M)) ≤ gas - (cb + dc + M) := Nat.sub_le _ _
  have hmx' : maxMessageCallGas (gas - M - (cb + dc)) ≤ gas - M - (cb + dc) := Nat.sub_le _ _
  have hmin : ¬ gas - (cb + dc + M) < min g.toNat (maxMessageCallGas (gas - (cb + dc + M))) := by
    omega
  have hmin2 : ¬ gas < min g.toNat (maxMessageCallGas (gas - M - (cb + dc))) + (cb + dc) + M := by
    omega
  have hmin3 : ¬ gas < min g.toNat (maxMessageCallGas (gas - (cb + dc + M))) + (cb + dc) + M := by
    omega
  have hk1 : ¬ gas < cb + M := by omega
  have hk2 : ¬ gas < cb + M + dc := by omega
  have hlen : rest.length ≠ STACK_LIMIT := by simp at hl; omega
  have hdel' : (if Fork.pectra ≤ fork then delegatedAddress calleeCode else none) =
      r.map Prod.fst := by
    rcases r with _ | ⟨d, dCode⟩
    · split
      · exact hroute ‹_›
      · rfl
    · simp [hroute.1, hroute.2.1]
  have hdcode : ∀ d dCode, r = some (d, dCode) →
      state.getCode (state.getAccount d).codeHash = .ok dCode := by
    rintro d dCode rfl; exact hroute.2.2
  have hdc' : ∀ d dCode, r = some (d, dCode) → accountAccessCost fork
      (!decide (toAddressMasked a = d) && !decide (d ∈ substate.accessedAddresses)) = dc := by
    rintro d dCode rfl
    rw [← hdc, routeCost, accCost]
    simp
  rcases r with _ | ⟨d, dCode⟩
  · simp only [routeCost] at hdc
    subst hdc
    simp only [Nat.add_zero] at hgas hmin hmin2 hmin3 hk2 ⊢
    by_cases hG : fork ≥ .glamsterdam <;>
    simp [callStep, popCallOperands, popCallValue, CallKind.sendsValue, popWord, Stack.pop, bind,
      Except.bind, pure, Except.pure, accessAddress, hfork, checkGas, hG, accessDelegation,
      accountCode, recordAccountRead, hgc, hga, hal, hcode, hdel', htw, hsd, Except.mapError,
      callExtraGas, callNewAccountCost, callNewAccountStateGas, callValueCost,
      payCall, messageCallGas, chargeGas, GasMeter.charge, finishCall, genericCall, keepReads,
      GasMeter.gasLeft, GasMeter.drain, GasMeter.reservoir, StateGasMeter.charge,
      StateGasMeter.drain, StateGasMeter.chargeState, hcb', hM, hgas, Nat.not_lt.mpr hgas,
      hmin, hmin2, hmin3, hk1, hdeep, chargeStateGas, GasMeter.chargeState,
      skipCall, refillStateGas, GasMeter.refill, GasMeter.credit, StateGasMeter.cancel,
      StateGasMeter.start, StateGasMeter.refill, pushWord, Stack.push, hlen,
      advance, Functor.map, Except.map, Meter.toNat]
    all_goals first
      | (simp only [and_assoc, exists_eq_left', exists_and_left, and_true]; done)
      | (simp only [and_assoc, exists_eq_left', exists_and_left, and_true]; and_intros <;> rfl)
  · by_cases hG : fork ≥ .glamsterdam <;>
    simp [callStep, popCallOperands, popCallValue, CallKind.sendsValue, popWord, Stack.pop, bind,
      Except.bind, pure, Except.pure, accessAddress, hfork, checkGas, hG, accessDelegation,
      accountCode, recordAccountRead, hgc, hga, hal, hcode, hdel', hdcode d dCode rfl, htw, hsd,
      Except.mapError, callExtraGas, callNewAccountCost, callNewAccountStateGas, callValueCost,
      payCall, messageCallGas, chargeGas, GasMeter.charge, finishCall, genericCall, keepReads,
      GasMeter.gasLeft, GasMeter.drain, GasMeter.reservoir, StateGasMeter.charge,
      StateGasMeter.drain, StateGasMeter.chargeState, hcb', hdc' d dCode rfl, hM, hgas,
      Nat.not_lt.mpr hgas, hmin, hmin2, hmin3, hk1, hk2, hdeep, chargeStateGas,
      GasMeter.chargeState, skipCall, refillStateGas, GasMeter.refill, GasMeter.credit,
      StateGasMeter.cancel, StateGasMeter.start, StateGasMeter.refill, pushWord, Stack.push, hlen,
      advance, Functor.map, Except.map, Meter.toNat]
    all_goals first
      | (simp only [and_assoc, exists_eq_left', exists_and_left, and_true]; done)
      | (simp only [and_assoc, exists_eq_left', exists_and_left, and_true]; and_intros <;> rfl)

/-- `callStep_low_r` over `StateGasMeter`: CALL (no value) with less execution gas than both
accesses and the memory growth, along any route, at any fork from Berlin: the step fails or halts
the frame with an error. -/
theorem callStep_low_rS (hfork : .berlin ≤ fork)
    {evm : Evm fork StateGasMeter} {g a i isz o osz : U256} {rest : List U256}
    {calleeCode : ByteArray} {r : Route}
    (hst : evm.stack.val = g :: a :: 0 :: i :: isz :: o :: osz :: rest)
    (hcode : evm.state.getCode (evm.state.getAccount (toAddressMasked a)).codeHash = .ok calleeCode)
    (hroute : Routes fork evm.state calleeCode r)
    (hgas : evm.gas.gasLeft <
      callBaseCost fork (decide (toAddressMasked a ∉ evm.substate.accessedAddresses)) +
      routeCost fork (evm.substate.accessedAddresses.insert (toAddressMasked a)) r +
      (extendMemory evm.memory.size [(i, isz), (o, osz)]).cost) :
    StepBadS (callStep .call evm) := by
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
  simp only at hcode hgas hroute ⊢
  have htw : Fork.tangerineWhistle ≤ fork := Nat.le_trans (by decide) hfork
  have hsd : Fork.spuriousDragon ≤ fork := Nat.le_trans (by decide) hfork
  generalize hcb : callBaseCost fork (decide (toAddressMasked a ∉ substate.accessedAddresses)) =
    cb at hgas
  have hcb' : callBaseCost fork (!decide (toAddressMasked a ∈ substate.accessedAddresses)) = cb :=
    by simpa using hcb
  generalize hdc : routeCost fork (substate.accessedAddresses.insert (toAddressMasked a)) r = dc
    at hgas
  generalize hM : (extendMemory memory.size [(i, isz), (o, osz)]).cost = M at hgas
  have hab : EvmError.outOfGas.aborts = false := rfl
  by_cases hG : fork ≥ .glamsterdam
  · by_cases hk : gas < cb + M
    · refine .inl ⟨.outOfGas, ?_⟩
      simp [callStep, popCallOperands, popCallValue, CallKind.sendsValue, popWord, Stack.pop, bind,
        Except.bind, pure, Except.pure, accessAddress, hfork, checkGas, hG, callValueCost, hcb', hM,
        hk, GasMeter.gasLeft, throw, throwThe, MonadExceptOf.throw]
    · refine .inr ?_
      rcases r with _ | ⟨d, dCode⟩
      · simp only [routeCost] at hdc
        omega
      obtain ⟨hpec, hdel, hdcode⟩ := hroute
      have hdel' : (if Fork.pectra ≤ fork then delegatedAddress calleeCode else none) = some d := by
        simp [hpec, hdel]
      have hdc' : accountAccessCost fork
          (!decide (toAddressMasked a = d) && !decide (d ∈ substate.accessedAddresses)) = dc := by
        rw [← hdc, routeCost, accCost]
        simp
      have hk2 : gas < cb + M + dc := by omega
      simp [hab, callStep, popCallOperands, popCallValue, CallKind.sendsValue, popWord, Stack.pop,
        bind, Except.bind, pure, Except.pure, accessAddress, hfork, checkGas, hG, accessDelegation,
        accountCode, recordAccountRead, hgc, hga, hcode, hdel', Except.mapError, callValueCost,
        keepReads, GasMeter.gasLeft, hcb', hdc', hM, hk, hk2, exceptionalHalt, throw, throwThe,
        MonadExceptOf.throw]
  · refine .inr ?_
    have h1 : ¬ (cb + dc + M ≤ gas) := by omega
    have h2 : gas < g.toNat + (cb + dc) + M := by omega
    rcases r with _ | ⟨d, dCode⟩
    · have hdel' : (if Fork.pectra ≤ fork then delegatedAddress calleeCode else none) = none := by
        split
        · exact hroute ‹_›
        · rfl
      simp only [routeCost] at hdc
      subst hdc
      simp only [Nat.add_zero] at h1 h2
      simp [hab, callStep, popCallOperands, popCallValue, CallKind.sendsValue, popWord, Stack.pop,
        bind, Except.bind, pure, Except.pure, accessAddress, hfork, checkGas, hG, accessDelegation,
        accountCode, recordAccountRead, hgc, hga, hal, hcode, hdel', htw, hsd, Except.mapError,
        callExtraGas, callNewAccountCost, callValueCost,
        payCall, messageCallGas, chargeGas, GasMeter.charge, StateGasMeter.charge, keepReads,
        GasMeter.gasLeft, hcb', hM, h1, h2, exceptionalHalt]
    · obtain ⟨hpec, hdel, hdcode⟩ := hroute
      have hdel' : (if Fork.pectra ≤ fork then delegatedAddress calleeCode else none) = some d := by
        simp [hpec, hdel]
      have hdc' : accountAccessCost fork
          (!decide (toAddressMasked a = d) && !decide (d ∈ substate.accessedAddresses)) = dc := by
        rw [← hdc, routeCost, accCost]
        simp
      simp [hab, callStep, popCallOperands, popCallValue, CallKind.sendsValue, popWord, Stack.pop,
        bind, Except.bind, pure, Except.pure, accessAddress, hfork, checkGas, hG, accessDelegation,
        accountCode, recordAccountRead, hgc, hga, hal, hcode, hdel', hdcode, htw, hsd,
        Except.mapError, callExtraGas, callNewAccountCost, callValueCost,
        payCall, messageCallGas, chargeGas, GasMeter.charge, StateGasMeter.charge, keepReads,
        GasMeter.gasLeft, hcb', hdc', hM, h1, h2, exceptionalHalt]

/-- `callStep_missing` over `StateGasMeter`: CALL (no value) when, from Pectra, the code of the
address delegates to `d` and the lookup of the code of `d` fails: the step fails or halts the
frame with an error. -/
theorem callStep_missingS (hfork : .berlin ≤ fork)
    {evm : Evm fork StateGasMeter} {g a i isz o osz : U256} {rest : List U256}
    {calleeCode : ByteArray} {d : Address} {e : State.StateError}
    (hst : evm.stack.val = g :: a :: 0 :: i :: isz :: o :: osz :: rest)
    (hcode : evm.state.getCode (evm.state.getAccount (toAddressMasked a)).codeHash = .ok calleeCode)
    (hpec : .pectra ≤ fork) (hdel : delegatedAddress calleeCode = some d)
    (hmiss : evm.state.getCode (evm.state.getAccount d).codeHash = .error e) :
    StepBadS (callStep .call evm) := by
  rcases evm with ⟨pc, ⟨l, hl⟩, memory, code, valid, ⟨gas, res, base, spill, comm, grant⟩, running,
    message, output, returnData, state, substate, error⟩
  simp only at hst
  subst hst
  have hgc : ∀ (tx : State.TransactionState) (x : Address) h,
      (tx.recordAccountRead x).getCode h = tx.getCode h := fun _ _ _ => rfl
  have hga : ∀ (tx : State.TransactionState) (x y : Address),
      (tx.recordAccountRead x).getAccount y = tx.getAccount y := fun _ _ _ => rfl
  simp only at hcode hmiss ⊢
  have hdel' : (if Fork.pectra ≤ fork then delegatedAddress calleeCode else none) = some d := by
    simp [hpec, hdel]
  have hab : (EvmError.state e).aborts = true := rfl
  have hab' : EvmError.outOfGas.aborts = false := rfl
  by_cases hG : fork ≥ .glamsterdam
  · by_cases hk1 : gas < callBaseCost fork (!decide (toAddressMasked a ∈ substate.accessedAddresses)) +
        (extendMemory memory.size [(i, isz), (o, osz)]).cost
    · refine .inl ⟨.outOfGas, ?_⟩
      simp [callStep, popCallOperands, popCallValue, CallKind.sendsValue, popWord, Stack.pop, bind,
        Except.bind, pure, Except.pure, accessAddress, hfork, checkGas, hG, callValueCost, hk1,
        GasMeter.gasLeft, throw, throwThe, MonadExceptOf.throw]
    · by_cases hk2 : gas < callBaseCost fork (!decide (toAddressMasked a ∈ substate.accessedAddresses)) +
          (extendMemory memory.size [(i, isz), (o, osz)]).cost +
          accountAccessCost fork
            (!decide (toAddressMasked a = d) && !decide (d ∈ substate.accessedAddresses))
      · refine .inr ?_
        simp [hab', callStep, popCallOperands, popCallValue, CallKind.sendsValue, popWord,
          Stack.pop, bind, Except.bind, pure, Except.pure, accessAddress, hfork, checkGas, hG,
          accessDelegation, accountCode, recordAccountRead, hgc, hga, hcode, hdel',
          Except.mapError, keepReads, callValueCost, hk1, hk2, GasMeter.gasLeft, exceptionalHalt,
          throw, throwThe, MonadExceptOf.throw]
      · refine .inl ⟨.state e, ?_⟩
        simp [hab, callStep, popCallOperands, popCallValue, CallKind.sendsValue, popWord,
          Stack.pop, bind, Except.bind, pure, Except.pure, accessAddress, hfork, checkGas, hG,
          accessDelegation, accountCode, recordAccountRead, hgc, hga, hcode, hdel', hmiss,
          Except.mapError, keepReads, callValueCost, hk1, hk2, GasMeter.gasLeft]
  · refine .inl ⟨.state e, ?_⟩
    simp [hab, callStep, popCallOperands, popCallValue, CallKind.sendsValue, popWord, Stack.pop,
      bind, Except.bind, pure, Except.pure, accessAddress, hfork, checkGas, hG, accessDelegation,
      accountCode, recordAccountRead, hgc, hga, hcode, hdel', hmiss, Except.mapError, keepReads]

/-- **CALL below the greatest depth, over both meters, at any reservoir** (round 42). From a frame
of `StateGasMeter` with any reservoir, CALL (no value) below the greatest depth, with the gas of both accesses and the memory
in the execution gas left, along any route: the step sends a message, and the step over `Nat` from
the `toNat` frame sends a message from the `toNat` of the caller. The message over
`StateGasMeter` is that message with the reservoir of the frame. The caller keeps the meter of the
frame with reservoir 0. -/
theorem callStep_child_simR (hfork : .berlin ≤ fork)
    {m : Evm fork StateGasMeter} {g a i isz o osz : U256}
    {rest : List U256} {calleeCode : ByteArray} {r : Route}
    (hst : m.stack.val = g :: a :: 0 :: i :: isz :: o :: osz :: rest)
    (hcode : m.state.getCode (m.state.getAccount (toAddressMasked a)).codeHash = .ok calleeCode)
    (hroute : Routes fork m.state calleeCode r)
    (hdepth : m.message.depth + 1 ≤ STACK_DEPTH_LIMIT)
    (hgas : callBaseCost fork (decide (toAddressMasked a ∉ m.substate.accessedAddresses)) +
      routeCost fork (m.substate.accessedAddresses.insert (toAddressMasked a)) r +
      (extendMemory m.memory.size [(i, isz), (o, osz)]).cost ≤ m.gas.gasLeft) :
    ∃ caller msgS msg, callStep .call m = .ok (.child caller msgS (resumeCall fork caller 0 o osz)) ∧
      callStep .call (Meter.toNat m) =
        .ok (.child (Meter.toNat caller) msg (resumeCall fork (Meter.toNat caller) 0 o osz)) ∧
      msgS = { msg with reservoir := m.gas.reservoir } ∧
      caller.gas = { m.gas with reservoir := 0, gasLeft := caller.gas.gasLeft } := by
  rcases m with ⟨pc, ⟨l, hl⟩, memory, code, valid, ⟨gas, res, base, spill, comm, grant⟩, running,
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
  have hmin' : ¬ gas - (cb + dc + M) < min g.toNat (maxMessageCallGas (gas - (cb + dc + M))) := by
    omega
  have hk1 : ¬ gas < cb + M := by omega
  have hk2 : ¬ gas < cb + M + dc := by omega
  have hmin2 : ¬ gas < min g.toNat (maxMessageCallGas (gas - M - (cb + dc))) + (cb + dc) + M := by
    rw [hx]; omega
  have hmin3 : ¬ gas < min g.toNat (maxMessageCallGas (gas - (cb + dc + M))) + (cb + dc) + M := by
    omega
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
  rcases r with _ | ⟨d, dCode⟩
  · simp only [routeCost] at hdc
    subst hdc
    simp only [Nat.add_zero] at hgas hmin' hx hk2 hmx hmin2 hmin3 ⊢
    by_cases hG : fork ≥ .glamsterdam <;>
    simp [callStep, popCallOperands, popCallValue, CallKind.sendsValue, popWord, Stack.pop, bind,
      Except.bind, pure, Except.pure, accessAddress, hfork, checkGas, hG, accessDelegation,
      accountCode, recordAccountRead, hgc, hga, hal, hcode, hdel', htw, hsd, Except.mapError,
      callExtraGas, callNewAccountCost, callNewAccountStateGas, callValueCost,
      payCall, messageCallGas, chargeGas, GasMeter.charge, finishCall, genericCall, keepReads,
      GasMeter.gasLeft, GasMeter.drain, GasMeter.reservoir, StateGasMeter.charge,
      StateGasMeter.drain, StateGasMeter.chargeState, hcb', Nat.not_lt.mpr hdepth, hM,
      chargeStateGas, GasMeter.chargeState, hgas, Nat.not_lt.mpr hgas, hk1, hmin', hmin2, hmin3, hx,
      routeState, routeSub, routeAddr, routeCode, Meter.toNat]
    all_goals first
      | (simp only [and_assoc, exists_eq_left', exists_eq_left, exists_and_left, and_true]; done)
      | (simp only [and_assoc, exists_eq_left', exists_eq_left, exists_and_left, and_true]; and_intros <;> rfl)
  · by_cases hG : fork ≥ .glamsterdam <;>
    simp [callStep, popCallOperands, popCallValue, CallKind.sendsValue, popWord, Stack.pop, bind,
      Except.bind, pure, Except.pure, accessAddress, hfork, checkGas, hG, accessDelegation,
      accountCode, recordAccountRead, hgc, hga, hal, hcode, hdel', hdcode d dCode rfl, htw, hsd,
      Except.mapError, callExtraGas, callNewAccountCost, callNewAccountStateGas, callValueCost,
      payCall, messageCallGas, chargeGas, GasMeter.charge, finishCall, genericCall, keepReads,
      GasMeter.gasLeft, GasMeter.drain, GasMeter.reservoir, StateGasMeter.charge,
      StateGasMeter.drain, StateGasMeter.chargeState, hcb', hdc' d dCode rfl,
      Nat.not_lt.mpr hdepth, hM, chargeStateGas, GasMeter.chargeState, hgas, Nat.not_lt.mpr hgas,
      hk1, hk2, hmin', hmin2, hmin3, hx, routeState, routeSub, routeAddr, routeCode, Meter.toNat]
    all_goals first
      | (simp only [and_assoc, exists_eq_left', exists_eq_left, exists_and_left, and_true]; done)
      | (simp only [and_assoc, exists_eq_left', exists_eq_left, exists_and_left, and_true]; and_intros <;> rfl)


/-- **CALL at the greatest depth, over both meters, at any reservoir** (round 42). From a frame
of `StateGasMeter` with any reservoir, CALL (no value) at the greatest depth, with the gas of both accesses and the memory,
along any route: no message runs, both steps give a next frame, the one over `Nat` the `toNat` of
the one over `StateGasMeter`, which keeps the meter of the frame but the execution gas left. -/
theorem callStep_deep_simR (hfork : .berlin ≤ fork)
    {m : Evm fork StateGasMeter} {g a i isz o osz : U256}
    {rest : List U256} {calleeCode : ByteArray} {r : Route}
    (hst : m.stack.val = g :: a :: 0 :: i :: isz :: o :: osz :: rest)
    (hcode : m.state.getCode (m.state.getAccount (toAddressMasked a)).codeHash = .ok calleeCode)
    (hroute : Routes fork m.state calleeCode r)
    (hdeep : STACK_DEPTH_LIMIT < m.message.depth + 1)
    (hgas : callBaseCost fork (decide (toAddressMasked a ∉ m.substate.accessedAddresses)) +
      routeCost fork (m.substate.accessedAddresses.insert (toAddressMasked a)) r +
      (extendMemory m.memory.size [(i, isz), (o, osz)]).cost ≤ m.gas.gasLeft) :
    ∃ after, callStep .call m = .ok (.next after) ∧
      callStep .call (Meter.toNat m) = .ok (.next (Meter.toNat after)) ∧
      after.gas = { m.gas with gasLeft := after.gas.gasLeft } := by
  rcases m with ⟨pc, ⟨l, hl⟩, memory, code, valid, ⟨gas, res, base, spill, comm, grant⟩, running,
    message, output, returnData, state, substate, error⟩
  simp only at hst
  subst hst
  have hgc : ∀ (tx : State.TransactionState) (x : Address) h,
      (tx.recordAccountRead x).getCode h = tx.getCode h := fun _ _ _ => rfl
  have hga : ∀ (tx : State.TransactionState) (x y : Address),
      (tx.recordAccountRead x).getAccount y = tx.getAccount y := fun _ _ _ => rfl
  have hal : ∀ (tx : State.TransactionState) (x y : Address),
      (tx.recordAccountRead x).isAccountAlive y = tx.isAccountAlive y := fun _ _ _ => rfl
  simp only at hcode hgas hdeep hroute ⊢
  have htw : Fork.tangerineWhistle ≤ fork := Nat.le_trans (by decide) hfork
  have hsd : Fork.spuriousDragon ≤ fork := Nat.le_trans (by decide) hfork
  generalize hcb : callBaseCost fork (decide (toAddressMasked a ∉ substate.accessedAddresses)) =
    cb at hgas
  have hcb' : callBaseCost fork (!decide (toAddressMasked a ∈ substate.accessedAddresses)) = cb :=
    by simpa using hcb
  generalize hdc : routeCost fork (substate.accessedAddresses.insert (toAddressMasked a)) r = dc
    at hgas
  generalize hM : (extendMemory memory.size [(i, isz), (o, osz)]).cost = M at hgas
  have hmx : maxMessageCallGas (gas - (cb + dc + M)) ≤ gas - (cb + dc + M) := Nat.sub_le _ _
  have hmx' : maxMessageCallGas (gas - M - (cb + dc)) ≤ gas - M - (cb + dc) := Nat.sub_le _ _
  have hmin : ¬ gas - (cb + dc + M) < min g.toNat (maxMessageCallGas (gas - (cb + dc + M))) := by
    omega
  have hmin2 : ¬ gas < min g.toNat (maxMessageCallGas (gas - M - (cb + dc))) + (cb + dc) + M := by
    omega
  have hmin3 : ¬ gas < min g.toNat (maxMessageCallGas (gas - (cb + dc + M))) + (cb + dc) + M := by
    omega
  have hk1 : ¬ gas < cb + M := by omega
  have hk2 : ¬ gas < cb + M + dc := by omega
  have hlen : rest.length ≠ STACK_LIMIT := by simp at hl; omega
  have hdel' : (if Fork.pectra ≤ fork then delegatedAddress calleeCode else none) =
      r.map Prod.fst := by
    rcases r with _ | ⟨d, dCode⟩
    · split
      · exact hroute ‹_›
      · rfl
    · simp [hroute.1, hroute.2.1]
  have hdcode : ∀ d dCode, r = some (d, dCode) →
      state.getCode (state.getAccount d).codeHash = .ok dCode := by
    rintro d dCode rfl; exact hroute.2.2
  have hdc' : ∀ d dCode, r = some (d, dCode) → accountAccessCost fork
      (!decide (toAddressMasked a = d) && !decide (d ∈ substate.accessedAddresses)) = dc := by
    rintro d dCode rfl
    rw [← hdc, routeCost, accCost]
    simp
  rcases r with _ | ⟨d, dCode⟩
  · simp only [routeCost] at hdc
    subst hdc
    simp only [Nat.add_zero] at hgas hmin hmin2 hmin3 hk2 ⊢
    by_cases hG : fork ≥ .glamsterdam <;>
    simp [callStep, popCallOperands, popCallValue, CallKind.sendsValue, popWord, Stack.pop, bind,
      Except.bind, pure, Except.pure, accessAddress, hfork, checkGas, hG, accessDelegation,
      accountCode, recordAccountRead, hgc, hga, hal, hcode, hdel', htw, hsd, Except.mapError,
      callExtraGas, callNewAccountCost, callNewAccountStateGas, callValueCost,
      payCall, messageCallGas, chargeGas, GasMeter.charge, finishCall, genericCall, keepReads,
      GasMeter.gasLeft, GasMeter.drain, GasMeter.reservoir, StateGasMeter.charge,
      StateGasMeter.drain, StateGasMeter.chargeState, hcb', hM, hgas, Nat.not_lt.mpr hgas,
      hmin, hmin2, hmin3, hk1, hdeep, chargeStateGas, GasMeter.chargeState,
      skipCall, refillStateGas, GasMeter.refill, GasMeter.credit, StateGasMeter.cancel,
      StateGasMeter.start, StateGasMeter.refill, pushWord, Stack.push, hlen,
      advance, Functor.map, Except.map, Meter.toNat]
    all_goals first
      | (simp only [and_assoc, exists_eq_left', exists_and_left, and_true]; done)
      | (simp only [and_assoc, exists_eq_left', exists_and_left, and_true]; and_intros <;> rfl)
  · by_cases hG : fork ≥ .glamsterdam <;>
    simp [callStep, popCallOperands, popCallValue, CallKind.sendsValue, popWord, Stack.pop, bind,
      Except.bind, pure, Except.pure, accessAddress, hfork, checkGas, hG, accessDelegation,
      accountCode, recordAccountRead, hgc, hga, hal, hcode, hdel', hdcode d dCode rfl, htw, hsd,
      Except.mapError, callExtraGas, callNewAccountCost, callNewAccountStateGas, callValueCost,
      payCall, messageCallGas, chargeGas, GasMeter.charge, finishCall, genericCall, keepReads,
      GasMeter.gasLeft, GasMeter.drain, GasMeter.reservoir, StateGasMeter.charge,
      StateGasMeter.drain, StateGasMeter.chargeState, hcb', hdc' d dCode rfl, hM, hgas,
      Nat.not_lt.mpr hgas, hmin, hmin2, hmin3, hk1, hk2, hdeep, chargeStateGas,
      GasMeter.chargeState, skipCall, refillStateGas, GasMeter.refill, GasMeter.credit,
      StateGasMeter.cancel, StateGasMeter.start, StateGasMeter.refill, pushWord, Stack.push, hlen,
      advance, Functor.map, Except.map, Meter.toNat]
    all_goals first
      | (simp only [and_assoc, exists_eq_left', exists_and_left, and_true]; done)
      | (simp only [and_assoc, exists_eq_left', exists_and_left, and_true]; and_intros <;> rfl)


end UsdtVerify.Complete
