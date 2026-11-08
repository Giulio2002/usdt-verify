import UsdtVerify.Evm.Split
import UsdtVerify.Evm.Route

/-!
# EXTCODESIZE, GAS, SUB and CALL for any gas and any runner

The deprecated paths do EXTCODESIZE of the upgraded address, a JUMPI on the size (no code:
revert), GAS, SUB and CALL. GAS and CALL are not `RunMono`, so the gas-shift argument does not go
through them; here each step is taken directly, for every gas, at every fork from Berlin
(Glamsterdam included):

- the steps that fail with too little gas: EXTCODESIZE (`extcodesize_low`, price `extCost`), GAS
  (`step_gas_low`), SUB (`step_sub_low`) and CALL (`callStep_low_r`: `StepBad`, the step fails or
  halts the frame with an error; before Glamsterdam the charge fails and the frame halts, from
  Glamsterdam the check of the price known before the reads fails first, or the check of the
  access to the delegate);
- CALL at the greatest depth (`callStep_deep_r`): no message is run, 0 is pushed;
- CALL under ANY runner (`call_ok`): the step sends a message, the runner either fails (then the
  run fails) or gives a frame `child`; the loop goes on from the frame that resumes from `child`.
  No assumption on the runner.
- `ok_step_error`, `ok_step_halt`, `ok_step_bad`, `ok_hoare`: how a successful run of the loop
  goes through such steps.

The CALL follows a route (`Route`, `Routes`): the code of the address itself, or, from Pectra,
when that code is an EIP-7702 delegation indicator to `d`, the code of `d` (EthLib's
`accessDelegation`). The delegated case adds a lookup of the code of `d` (a failed lookup makes the
step fail or halt, `callStep_missing`), an access to `d` (`accCost`: 100 warm, 2600 cold, 3000
cold from Glamsterdam; `routeCost`, in the extra price of the CALL), and the read and access of `d`
in the state and substate (`routeState`, `routeSub`; these, and `callStep_child_r`, are in
Evm/Route.lean). `callStep_low_r`, `callStep_deep_r`, `callStep_child_r` cover both routes
(`callStep_low`, `callStep_deep` are their `none` case); `call_ok` and `CallEnd` (and `fromExt`, in
Usdt/Complete/Deprecated/Call.lean) take the route. The message of a delegated CALL keeps the upgraded address as its current target and
runs the code of `d` with the precompiles disabled.
-/

namespace UsdtVerify.Complete

open EthLib.Base (Fork U256 toAddressMasked Address)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open UsdtVerify.Gas
open GasCosts
open Deprecated

variable {fork : Fork} {bound : Nat} {runChild : MessageRunner fork Nat bound}

/-! ## The loop through one step -/

/-- A step that fails: no successful run. -/
theorem ok_step_error {evm s : Evm fork Nat} {e : EvmError} (hr : evm.running = true)
    (hs : step fork evm = .error e) {within : GasMeter.gasHeld evm.gas ≤ bound}
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s) :
    s.error ≠ none := by
  by_cases ab : e.aborts = true
  · rw [runFrame_of_step_eq_abort hr hs ab] at hrun
    cases hrun
  · rw [runFrame_of_step_eq_error hr hs (by simpa using ab)] at hrun
    cases hrun
    simp [exceptionalHalt]

/-- A step to a stopped frame with an error: no successful run. -/
theorem ok_step_halt {evm b s : Evm fork Nat} (hr : evm.running = true)
    (hs : step fork evm = .ok (.next b)) (hbr : b.running = false) (hbe : b.error ≠ none)
    {within : GasMeter.gasHeld evm.gas ≤ bound}
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s) :
    s.error ≠ none := by
  rw [runFrame_of_step_eq_next hr hs, runFrame_stopped hbr] at hrun
  cases hrun
  exact hbe

/-- A successful run through a `Hoare` triple goes on from a frame of its postcondition. -/
theorem ok_hoare {P Q : Evm fork Nat → Prop} (h : Hoare fork P Q) {evm s : Evm fork Nat}
    (hp : P evm) (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s) :
    ∃ z w, Q z ∧ Evm.runFrame (step fork) (step_decreases fork) bound runChild z w = .ok s := by
  obtain ⟨z, hr, hq⟩ := h evm hp
  exact ⟨z, _, hq,
    (runFrame_eq_of_reaches Step.gasHeld_le Step.runFrame_eq hr within).symm.trans hrun⟩

/-! ## Steps with too little gas -/

theorem instruction_gas' : instruction (Meter := Nat) fork .gas =
    some (readFrame OPCODE_GAS fun evm => BitVec.ofNat 256 (GasMeter.gasLeft evm.gas)) := rfl

theorem instruction_extcodesize' :
    instruction (Meter := Nat) fork .extcodesize = some extcodesizeStep := rfl

variable {code : ByteArray} {message : Message fork} {pc : Nat} {memory : ByteArray} {gas : Nat}
  {state : State.TransactionState} {substate : Substate}

/-- GAS with less than 2 gas fails. -/
theorem step_gas_low {stack : List U256} (hlt : pc < code.size) (hbyte : code[pc] = 0x5a)
    (hg : gas < 2) {evm : Evm fork Nat}
    (h : At code message pc stack memory gas state substate evm) :
    step fork evm = .error .outOfGas := by
  obtain ⟨hc, -, -, hpc, -, -, hgas, -⟩ := h
  subst hc hpc hgas
  rw [step_of_instruction hlt (by rw [hbyte]; exact ofByte_of_decode (op := .gas) rfl (Fork.frontier_le _)) instruction_gas']
  simp [readFrame, chargeGas, GasMeter.charge, bind, Except.bind, show OPCODE_GAS = 2 from rfl,
    hg, Functor.map, Except.map]

/-- SUB with less than 3 gas fails. -/
theorem step_sub_low {x y : U256} {rest : List U256} (hlt : pc < code.size)
    (hbyte : code[pc] = 0x03) (hg : gas < 3) {evm : Evm fork Nat}
    (h : At code message pc (x :: y :: rest) memory gas state substate evm) :
    step fork evm = .error .outOfGas := by
  obtain ⟨hc, -, -, hpc, hst, -, hgas, -⟩ := h
  subst hc hpc hgas
  rw [step_of_instruction hlt (by rw [hbyte]; exact ofByte_of_decode (op := .sub) rfl (Fork.frontier_le _)) Local.instruction_sub, binaryOp_cons hst]
  simp [GasMeter.charge, show OPCODE_SUB = 3 from rfl, hg, Functor.map, Except.map]

/-- EXTCODESIZE with less gas than its price fails (the code is found). -/
theorem extcodesize_low (hfork : .berlin ≤ fork) {U : U256}
    {rest : List U256} {c : ByteArray} (hlt : pc < code.size) (hbyte : code[pc] = 0x3b)
    (hcode : state.getCode (state.getAccount (toAddressMasked U)).codeHash = .ok c)
    (hg : gas < extCost fork (decide (toAddressMasked U ∉ substate.accessedAddresses)))
    {evm : Evm fork Nat} (h : At code message pc (U :: rest) memory gas state substate evm) :
    step fork evm = .error .outOfGas := by
  obtain ⟨hc, -, -, hpc, hst, -, hgas, -, -, -, hs, hss⟩ := h
  subst hc hpc hgas hs hss
  have found : accountCode evm (toAddressMasked U) = .ok c := by
    simp [accountCode, hcode, Except.mapError]
  rw [step_of_instruction hlt (by rw [hbyte]; exact ofByte_of_decode (op := .extcodesize) rfl (Fork.frontier_le _)) instruction_extcodesize', extcodesizeStep_of_accountCode hst found]
  simp only [accessAddress, hfork, ↓reduceIte]
  simp only [extCost] at hg
  by_cases hm : toAddressMasked U ∈ evm.substate.accessedAddresses
  · have h' : evm.gas < externalBaseCost fork false := by simpa [hm] using hg
    simp [hm, h', GasMeter.charge, Functor.map, Except.map]
  · have h' : evm.gas < externalBaseCost fork true := by simpa [hm] using hg
    simp [hm, h', GasMeter.charge, Functor.map, Except.map]

/-- A step that fails, or that halts the frame with an error. -/
def StepBad (r : Except EvmError (StepResult fork Nat)) : Prop :=
  (∃ e, r = .error e) ∨ ∃ b, r = .ok (.next b) ∧ b.running = false ∧ b.error ≠ none

/-- A step that fails or halts with an error: no successful run. -/
theorem ok_step_bad {evm s : Evm fork Nat} (hr : evm.running = true) (hs : StepBad (step fork evm))
    {within : GasMeter.gasHeld evm.gas ≤ bound}
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s) :
    s.error ≠ none := by
  rcases hs with ⟨e, he⟩ | ⟨b, hb, hbr, hbe⟩
  · exact ok_step_error hr he hrun
  · exact ok_step_halt hr hb hbr hbe hrun

/-- CALL (no value) with less gas than both accesses and the memory growth, along any route, at
any fork from Berlin: the step fails or halts the frame with an error. Before Glamsterdam the
charge of `payCall` fails and the frame halts. From Glamsterdam the check of the known price (the
access and the memory) fails first, or the check of the access to the delegate. -/
theorem callStep_low_r (hfork : .berlin ≤ fork)
    {evm : Evm fork Nat} {g a i isz o osz : U256} {rest : List U256} {calleeCode : ByteArray}
    {r : Route}
    (hst : evm.stack.val = g :: a :: 0 :: i :: isz :: o :: osz :: rest)
    (hcode : evm.state.getCode (evm.state.getAccount (toAddressMasked a)).codeHash = .ok calleeCode)
    (hroute : Routes fork evm.state calleeCode r)
    (hgas : evm.gas < callBaseCost fork (decide (toAddressMasked a ∉ evm.substate.accessedAddresses)) +
      routeCost fork (evm.substate.accessedAddresses.insert (toAddressMasked a)) r +
      (extendMemory evm.memory.size [(i, isz), (o, osz)]).cost) :
    StepBad (callStep .call evm) := by
  rcases evm with ⟨pc, ⟨l, hl⟩, memory, code, valid, gas, running, message, output, returnData,
    state, substate, error⟩
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
        payCall, messageCallGas, chargeGas, GasMeter.charge, keepReads, GasMeter.gasLeft, hcb', hM,
        h1, h2, exceptionalHalt]
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
        payCall, messageCallGas, chargeGas, GasMeter.charge, keepReads, GasMeter.gasLeft, hcb', hdc',
        hM, h1, h2, exceptionalHalt]

/-- CALL (no value) with less gas than the access and the memory growth, no delegation: the step
fails or halts the frame with an error (the `none` case of `callStep_low_r`). -/
theorem callStep_low (hfork : .berlin ≤ fork)
    {evm : Evm fork Nat} {g a i isz o osz : U256} {rest : List U256} {calleeCode : ByteArray}
    (hst : evm.stack.val = g :: a :: 0 :: i :: isz :: o :: osz :: rest)
    (hcode : evm.state.getCode (evm.state.getAccount (toAddressMasked a)).codeHash = .ok calleeCode)
    (hdel : Routes fork evm.state calleeCode none)
    (hgas : evm.gas < callBaseCost fork (decide (toAddressMasked a ∉ evm.substate.accessedAddresses)) +
      (extendMemory evm.memory.size [(i, isz), (o, osz)]).cost) :
    StepBad (callStep .call evm) :=
  callStep_low_r hfork hst hcode hdel (by simpa [routeCost] using hgas)

/-- CALL (no value) at the greatest depth, with the gas of both accesses and the memory growth,
along any route, at any fork from Berlin: no message runs, the frame pushes 0 and goes on. -/
theorem callStep_deep_r (hfork : .berlin ≤ fork)
    {evm : Evm fork Nat} {g a i isz o osz : U256} {rest : List U256} {calleeCode : ByteArray}
    {r : Route}
    (hst : evm.stack.val = g :: a :: 0 :: i :: isz :: o :: osz :: rest)
    (hcode : evm.state.getCode (evm.state.getAccount (toAddressMasked a)).codeHash = .ok calleeCode)
    (hroute : Routes fork evm.state calleeCode r)
    (hdeep : STACK_DEPTH_LIMIT < evm.message.depth + 1)
    (hgas : callBaseCost fork (decide (toAddressMasked a ∉ evm.substate.accessedAddresses)) +
      routeCost fork (evm.substate.accessedAddresses.insert (toAddressMasked a)) r +
      (extendMemory evm.memory.size [(i, isz), (o, osz)]).cost ≤ evm.gas) :
    ∃ after, callStep .call evm = .ok (.next after) ∧
      after.code = evm.code ∧ after.validJumpDestinations = evm.validJumpDestinations ∧
      after.message = evm.message ∧ after.pc = evm.pc + 1 ∧ after.stack.val = 0 :: rest ∧
      after.running = evm.running ∧ after.error = evm.error ∧ after.output = evm.output := by
  rcases evm with ⟨pc, ⟨l, hl⟩, memory, code, valid, gas, running, message, output, returnData,
    state, substate, error⟩
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
    simp only [Nat.add_zero] at hgas hmin hmin2 hk2 ⊢
    by_cases hG : fork ≥ .glamsterdam <;>
    simp [callStep, popCallOperands, popCallValue, CallKind.sendsValue, popWord, Stack.pop, bind,
      Except.bind, pure, Except.pure, accessAddress, hfork, checkGas, hG, accessDelegation,
      accountCode, recordAccountRead, hgc, hga, hal, hcode, hdel', htw, hsd, Except.mapError,
      callExtraGas, callNewAccountCost, callNewAccountStateGas, callValueCost,
      payCall, messageCallGas, chargeGas, GasMeter.charge, finishCall, genericCall, keepReads,
      GasMeter.gasLeft, GasMeter.drain, hcb', hM, hgas, Nat.not_lt.mpr hgas,
      hmin, hmin2, hdeep, chargeStateGas, GasMeter.chargeState,
      skipCall, refillStateGas, GasMeter.refill, GasMeter.credit, pushWord, Stack.push, hlen,
      advance, Functor.map, Except.map]
  · by_cases hG : fork ≥ .glamsterdam <;>
    simp [callStep, popCallOperands, popCallValue, CallKind.sendsValue, popWord, Stack.pop, bind,
      Except.bind, pure, Except.pure, accessAddress, hfork, checkGas, hG, accessDelegation,
      accountCode, recordAccountRead, hgc, hga, hal, hcode, hdel', hdcode d dCode rfl, htw, hsd,
      Except.mapError, callExtraGas, callNewAccountCost, callNewAccountStateGas, callValueCost,
      payCall, messageCallGas, chargeGas, GasMeter.charge, finishCall, genericCall, keepReads,
      GasMeter.gasLeft, GasMeter.drain, hcb', hdc' d dCode rfl, hM, hgas,
      Nat.not_lt.mpr hgas, hmin, hmin2, hk1, hk2, hdeep, chargeStateGas, GasMeter.chargeState,
      skipCall, refillStateGas, GasMeter.refill, GasMeter.credit, pushWord, Stack.push, hlen,
      advance, Functor.map, Except.map]

/-- CALL (no value) at the greatest depth, with the gas of the access and the memory growth, no
delegation: no message runs, the frame pushes 0 and goes on (the `none` case of
`callStep_deep_r`). -/
theorem callStep_deep (hfork : .berlin ≤ fork)
    {evm : Evm fork Nat} {g a i isz o osz : U256} {rest : List U256} {calleeCode : ByteArray}
    (hst : evm.stack.val = g :: a :: 0 :: i :: isz :: o :: osz :: rest)
    (hcode : evm.state.getCode (evm.state.getAccount (toAddressMasked a)).codeHash = .ok calleeCode)
    (hdel : Routes fork evm.state calleeCode none)
    (hdeep : STACK_DEPTH_LIMIT < evm.message.depth + 1)
    (hgas : callBaseCost fork (decide (toAddressMasked a ∉ evm.substate.accessedAddresses)) +
      (extendMemory evm.memory.size [(i, isz), (o, osz)]).cost ≤ evm.gas) :
    ∃ after, callStep .call evm = .ok (.next after) ∧
      after.code = evm.code ∧ after.validJumpDestinations = evm.validJumpDestinations ∧
      after.message = evm.message ∧ after.pc = evm.pc + 1 ∧ after.stack.val = 0 :: rest ∧
      after.running = evm.running ∧ after.error = evm.error ∧ after.output = evm.output :=
  callStep_deep_r hfork hst hcode hdel hdeep (by simpa [routeCost] using hgas)

/-- CALL (no value) when, from Pectra, the code of the address delegates to `d` and the lookup of
the code of `d` fails with a state error: the step fails or halts the frame with an error (from
Glamsterdam, a check of the gas may halt the frame before the lookup). -/
theorem callStep_missing (hfork : .berlin ≤ fork)
    {evm : Evm fork Nat} {g a i isz o osz : U256} {rest : List U256} {calleeCode : ByteArray}
    {d : Address} {e : State.StateError}
    (hst : evm.stack.val = g :: a :: 0 :: i :: isz :: o :: osz :: rest)
    (hcode : evm.state.getCode (evm.state.getAccount (toAddressMasked a)).codeHash = .ok calleeCode)
    (hpec : .pectra ≤ fork) (hdel : delegatedAddress calleeCode = some d)
    (hmiss : evm.state.getCode (evm.state.getAccount d).codeHash = .error e) :
    StepBad (callStep .call evm) := by
  rcases evm with ⟨pc, ⟨l, hl⟩, memory, code, valid, gas, running, message, output, returnData,
    state, substate, error⟩
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
          Except.mapError, keepReads, callValueCost, hk1, hk2, GasMeter.gasLeft, exceptionalHalt, throw,
          throwThe, MonadExceptOf.throw]
      · refine .inl ⟨.state e, ?_⟩
        simp [hab, callStep, popCallOperands, popCallValue, CallKind.sendsValue, popWord,
          Stack.pop, bind, Except.bind, pure, Except.pure, accessAddress, hfork, checkGas, hG,
          accessDelegation, accountCode, recordAccountRead, hgc, hga, hcode, hdel', hmiss,
          Except.mapError, keepReads, callValueCost, hk1, hk2, GasMeter.gasLeft]
  · refine .inl ⟨.state e, ?_⟩
    simp [hab, callStep, popCallOperands, popCallValue, CallKind.sendsValue, popWord, Stack.pop,
      bind, Except.bind, pure, Except.pure, accessAddress, hfork, checkGas, hG, accessDelegation,
      accountCode, recordAccountRead, hgc, hga, hcode, hdel', hmiss, Except.mapError, keepReads]

/-! ## CALL under any runner -/

/-- What a successful run through a CALL (no value) gives, under the runner `runChild`, along the
route `r` (no delegation, or a delegate and its code): the runner ran the message `msg` from the
frame `caller` to the frame `child`, and the loop goes on, with the same end `s`, from the frame
that resumes from `child` (the flag `1` for no error, the output written, the gas back, the state
and substate of `child`). The message is the one of EthLib's `callStep`: it runs the code of the
route, at the address of the route, with the precompiles disabled when delegated. -/
def CallEnd (runChild : MessageRunner fork Nat bound) (code : ByteArray) (message : Message fork)
    (pc : Nat) (asked to i isz o osz : U256) (rest : List U256) (memory : ByteArray) (gas : Nat)
    (state : State.TransactionState) (substate : Substate) (cold : Bool) (calleeCode : ByteArray)
    (r : Route) (s : Evm fork Nat) : Prop :=
  ∃ caller msg lt child, runChild caller msg lt = .ok child ∧
    caller.state = (routeState (state.recordAccountRead (toAddressMasked to)) r).recordAccountRead
      message.currentTarget ∧
    caller.substate = routeSub { substate with
      accessedAddresses := substate.accessedAddresses.insert (toAddressMasked to) } r ∧
    msg.gas = (messageCallGas fork 0 asked.toNat gas
      (extendMemory memory.size [(i, isz), (o, osz)]).cost
      (accCost fork cold +
        routeCost fork (substate.accessedAddresses.insert (toAddressMasked to)) r)).subCall ∧
    msg.caller = message.currentTarget ∧ msg.currentTarget = toAddressMasked to ∧
    msg.target = some (toAddressMasked to) ∧
    msg.codeAddress = some (routeAddr (toAddressMasked to) r) ∧
    msg.code = routeCode calleeCode r ∧ msg.disablePrecompiles = r.isSome ∧
    msg.data = memoryReadBytes (memoryExtend memory
      (extendMemory memory.size [(i, isz), (o, osz)]).expandBy) i.toNat isz.toNat ∧
    msg.value = 0 ∧ msg.depth = message.depth + 1 ∧
    (msg.isStatic = message.isStatic ∧ msg.blockEnv = message.blockEnv ∧
      msg.txEnv = message.txEnv ∧ msg.shouldTransferValue = true) ∧
    ∃ after w, At code message (pc + 1) ((if child.1.error.isNone then 1 else 0) :: rest)
      (memoryWrite (memoryExtend memory
        (extendMemory memory.size [(i, isz), (o, osz)]).expandBy)
        o.toNat (child.1.output.extract 0 (min osz.toNat child.1.output.size)))
      (gas - ((messageCallGas fork 0 asked.toNat gas
        (extendMemory memory.size [(i, isz), (o, osz)]).cost
        (accCost fork cold +
          routeCost fork (substate.accessedAddresses.insert (toAddressMasked to)) r)).cost +
        (extendMemory memory.size [(i, isz), (o, osz)]).cost) + child.1.gas)
      (incorporateChild fork caller child.1).state (incorporateChild fork caller child.1).substate
      after ∧
    Evm.runFrame (step fork) (step_decreases fork) bound runChild after w = .ok s

theorem step_call {evm : Evm fork Nat} (hlt : evm.pc < evm.code.size)
    (hbyte : evm.code[evm.pc] = 0xf1) : step fork evm = callStep .call evm :=
  step_of_messageInstruction hlt
    (by rw [hbyte]; exact ofByte_of_decode (op := .call) rfl (Fork.frontier_le _))
    instruction_call messageInstruction_call

/-- A successful run through a CALL (no value) with the gas of the accesses and the memory, below
the greatest depth, along the route `r`, under ANY runner: the run goes through `CallEnd`. -/
theorem call_ok (hfork : .berlin ≤ fork)
    {asked to i isz o osz : U256} {rest : List U256} {cold : Bool} {calleeCode : ByteArray}
    {r : Route} (hlt : pc < code.size) (hbyte : code[pc] = 0xf1)
    (hcode : state.getCode (state.getAccount (toAddressMasked to)).codeHash = .ok calleeCode)
    (hroute : Routes fork state calleeCode r)
    (hdepth : message.depth + 1 ≤ STACK_DEPTH_LIMIT)
    (hcold : decide (toAddressMasked to ∉ substate.accessedAddresses) = cold)
    (hgas : accCost fork cold +
      routeCost fork (substate.accessedAddresses.insert (toAddressMasked to)) r +
      (extendMemory memory.size [(i, isz), (o, osz)]).cost ≤ gas)
    {evm s : Evm fork Nat}
    (start : At code message pc (asked :: to :: 0 :: i :: isz :: o :: osz :: rest) memory gas
      state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s) :
    CallEnd runChild code message pc asked to i isz o osz rest memory gas state substate cold
      calleeCode r s := by
  have hcost := callBaseCost_eq hfork cold
  obtain ⟨hc, hj, hm, hpc, hst, hmem, hg, hr, herr, hout, hs, hss⟩ := start
  subst hm hg hs hss hcold hmem
  obtain ⟨caller, msg, hstep, c1, c2, c3, c4, c5, c6, c7, c8, c9, co, c10, c11, m1, m2, m3, mt,
      mca, m4, mdp, md, m5, m6, m7, m8, m9, m10⟩ :=
    callStep_child_r hfork hst hcode hroute hdepth
      (by rw [hcost]; omega)
  have hsent : step fork evm = .ok (.child caller msg (resumeCall fork caller 0 o osz)) := by
    rw [step_call (by rw [hc, hpc]; exact hlt) (by simp only [hc, hpc, hbyte])]
    exact hstep
  have lt : msg.gas < bound := by
    have := (step_decreases fork hr hsent).1
    omega
  rcases hch : runChild caller msg lt with e | child
  · rw [runFrame_of_runChild_eq_error hr hsent lt hch] at hrun
    cases hrun
  · have hlen : caller.stack.val.length < STACK_LIMIT := by
      have := evm.stack.property
      rw [hst] at this
      rw [c5]
      simp at this
      omega
    obtain ⟨after, hres, a1, a2, a3, a4, a5, a6, a7, a8, a9, ao, a10, a11⟩ :=
      resumeCall_eq (child := child.1) (o := o) (osz := osz) hlen
    rw [runFrame_of_step_eq_child hr hsent lt hch hres] at hrun
    refine ⟨caller, msg, lt, child, hch, c10, c11, by rw [m1, hcost], m2, m3, mt, mca, m4, mdp,
      md, m5, m6, ⟨m7, m8, m9, m10⟩, after, _, ?_, hrun⟩
    refine ⟨by rw [a1, c1, hc], by rw [a2, c2, hj], by rw [a3, c3], by rw [a4, c4, hpc],
      by rw [a5, c5], by rw [a6, c6], ?_, by rw [a8, c8, hr], by rw [a9, c9, herr],
      by rw [ao, co, hout], a10, a11⟩
    rw [a7, c7, hcost]

/-! ## EXTCODESIZE when the code is not found -/

/-- EXTCODESIZE when the lookup of the code fails with a state error: the step fails. -/
theorem extcodesizeStep_notFound {evm : Evm fork Nat} {word : U256} {rest : List U256}
    {e : EvmError} (h : evm.stack.val = word :: rest)
    (missing : accountCode evm (toAddressMasked word) = .error e) :
    ∃ e', extcodesizeStep evm = .error e' := by
  have hstack : evm.stack = ⟨word :: rest, h ▸ evm.stack.property⟩ := Subtype.ext h
  obtain ⟨accessed, hacc⟩ := accessAddress_snd
    { evm with stack := ⟨rest, by have := evm.stack.property; rw [h] at this; simp at this; omega⟩ }
    (toAddressMasked word)
  simp only [extcodesizeStep, popWord, chargeGas, recordAccountRead, pushWord, advance, hstack,
    Stack.pop]
  simp only [bind, Except.bind, pure, Except.pure, hacc]
  have recorded : Except.mapError EvmError.state
      ((evm.state.recordAccountRead (toAddressMasked word)).getCode
        ((evm.state.recordAccountRead (toAddressMasked word)).getAccount
          (toAddressMasked word)).codeHash) = Except.error e := missing
  have recorded' : Except.mapError EvmError.state
      ((evm.state.recordAccountRead (toAddressMasked word)).getCode
        (evm.state.getAccount (toAddressMasked word)).codeHash) = Except.error e := missing
  rcases hc : GasMeter.charge _ _ with _ | _ <;>
    simp [accountCode, recorded']

end UsdtVerify.Complete
