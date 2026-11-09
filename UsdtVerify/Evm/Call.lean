import UsdtVerify.Evm.Split
import UsdtVerify.Evm.Route
import EthLib.Execution.Proofs.Evm.Logic.CallSteps

/-!
# EXTCODESIZE, GAS, SUB and CALL for any gas and any runner

The deprecated paths do EXTCODESIZE of the upgraded address, a JUMPI on the size (no code:
revert), GAS, SUB and CALL. GAS and CALL are not `RunMono`, so the gas-shift argument does not go
through them; here each step is taken directly, for every gas, at every fork from Berlin
(Glamsterdam included):

- the steps that fail with too little gas: EXTCODESIZE (`extcodesize_low`, price `extCost`), GAS
  (`step_gas_low`) and SUB (`step_sub_low`);
- CALL under ANY runner (`call_ok`): the step sends a message, the runner either fails (then the
  run fails) or gives a frame `child`; the loop goes on from the frame that resumes from `child`
  (`CallEnd`). No assumption on the runner.

Round 52 (EthLib #1634): the CALL that fails with too little gas, at the greatest depth, and with
a delegate whose code is missing are EthLib's `callStep_fails_of_routes`,
`callStep_deep_of_routes` and `callStep_fails_of_missing` (any call kind that sends no value; the
deep form also states the gas, the memory and the return data). The local `callStep_low_r`,
`callStep_deep_r`, `callStep_missing`, their `none` cases, `StepBad` (EthLib's `StepFails`, the
same definition), `ok_step_error`, `ok_step_halt`, `ok_step_bad` (EthLib's
`error_ne_none_of_stepFails`) and `ok_hoare` (EthLib's `Hoare.runFrame_of_ok`) are removed.
`call_ok` is now proved from EthLib's `callKindRoute` and `HoareOn.runFrame_of_ok`. `CallEnd`
stays: it is stated over the local `At` (Evm/At.lean) and names the frame that the runner gave,
which the deprecated paths use.

The CALL follows a route (`Route`, `Routes`): the code of the address itself, or, from Pectra,
when that code is an EIP-7702 delegation indicator to `d`, the code of `d` (EthLib's
`accessDelegation`). The message of a delegated CALL keeps the upgraded address as its current
target and runs the code of `d` with the precompiles disabled.
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
  rw [step_of_instruction hlt (by rw [hbyte]; exact ofByte_of_decode (op := .sub) rfl (Fork.frontier_le _)) instruction_sub, binaryOp_cons hst]
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
the greatest depth, along the route `r`, under ANY runner: the run goes through `CallEnd`.
Round 52: from EthLib's `callKindRoute` (the rule of a call along a route, #1611) and
`HoareOn.runFrame_of_ok` (#1634), with the assumption on the callee that it is the frame the
runner gave. -/
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
  subst hcold
  obtain ⟨after, ⟨caller, msg, child, sends, ⟨lt, c, hch, rfl⟩, -, hat⟩, w, hrun'⟩ :=
    HoareOn.runFrame_of_ok
      (callKindRoute (kind := .call) (rest := rest) (returnData := evm.returnData)
        (callee := fun caller msg child =>
          ∃ lt c, runChild caller msg lt = .ok c ∧ c.1 = child)
        hfork hlt hbyte (ofByte_of_decode (op := .call) rfl (Fork.frontier_le _))
        instruction_call messageInstruction_call hcode hroute hdepth (by rw [hcost]; exact hgas))
      (fun _ _ lt c h => ⟨lt, c, h, rfl⟩) start.toLogic within hrun
  obtain ⟨c1, c2, m1, -, m2, m3, mt, mca, m4, mdp, md, m5, mtv, mdep, mst, mb, mtx⟩ := sends
  rw [hcost] at m1 hat
  refine ⟨caller, msg, lt, c, hch, c1, c2, m1, by simpa using m2, by simpa using m3,
    by simpa using mt, mca, m4, mdp, md, by simpa using m5, mdep,
    ⟨by rw [mst]; rfl, mb, mtx, by rw [mtv]; rfl⟩, after, w, At.ofLogic hat, hrun'⟩

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
