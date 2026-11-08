import EthLib.Execution.Proofs.Evm.Logic.Call
import EthLib.Execution.Proofs.Evm.Logic.Callee
import UsdtVerify.Evm.Local.Extcodesize
import UsdtVerify.Evm.Sends

/-!
# The route of a CALL to the upgraded address

A CALL runs the code of the called address, or, from Pectra, when that code is an EIP-7702
delegation indicator to an address `d`, the code of `d` (EthLib's `accessDelegation`). This file
names the two cases (`Route`, `Routes`), what the delegated case adds (`routeCost`, `routeState`,
`routeSub`, `routeAddr`, `routeCode`), the step of a CALL along a route (`callStep_child_r`) and
the CALL rule under a callee assumption along a route (`callWithR`, EthLib's `callWith` without
its hypothesis of no delegation; round 26: `callWithRS`, the same as a `Sends.HoareOn`: the
runner may fail with any error, and the run ends at the step after the CALL or at a failure of the
runner on the message the CALL sends; `callWithR` follows from it). The forward specifications of the deprecated paths
(Usdt/Spec/Deprecated/) and their completeness (Usdt/Complete/Deprecated/) use it.
-/

namespace UsdtVerify.Deprecated

open EthLib.Base (Fork)
open EthLib.Execution.Evm

/-- The price of an access to an account at `fork` from Berlin (EthLib's `accountAccessCost`):
100 for a warm address; for a cold one 2600 (EIP-2929), 3000 from Glamsterdam (EIP-8038). -/
def accCost (fork : Fork) (cold : Bool) : Nat := accountAccessCost fork cold

/-- The price of EXTCODESIZE at `fork` from Berlin (EthLib's `externalBaseCost`): the access, plus
a warm access (100) from Glamsterdam (EIP-8038). -/
def extCost (fork : Fork) (cold : Bool) : Nat := externalBaseCost fork cold

/-- Before Glamsterdam, an access costs 2600 cold and 100 warm. -/
theorem accCost_of_lt {fork : Fork} (hglam : fork < .glamsterdam) (cold : Bool) :
    accCost fork cold = if cold then 2600 else 100 := by
  have hng : ¬fork ≥ .glamsterdam := Nat.not_le_of_lt hglam
  simp [accCost, accountAccessCost, gasSchedule, hng, GasCosts.WARM_ACCESS]

/-- From Berlin to before Glamsterdam, EXTCODESIZE costs the access: 2600 cold and 100 warm. -/
theorem extCost_of_lt {fork : Fork} (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    (cold : Bool) : extCost fork cold = if cold then 2600 else 100 :=
  Logic.externalBaseCost_of_berlin hfork hglam cold

/-- A warm access costs 100 at every fork. -/
theorem accCost_false (fork : Fork) : accCost fork false = 100 := rfl

/-- From Berlin, CALL pays the access to the address. -/
theorem callBaseCost_eq {fork : Fork} (hfork : .berlin ≤ fork) (cold : Bool) :
    callBaseCost fork cold = accCost fork cold :=
  callBaseCost_of_berlin_le hfork cold

/-- From Berlin, EXTCODESIZE costs at least 100. -/
theorem extCost_ge {fork : Fork} (hfork : .berlin ≤ fork) (cold : Bool) : 100 ≤ extCost fork cold := by
  unfold extCost externalBaseCost accountAccessCost
  by_cases hg : fork ≥ .glamsterdam <;> cases cold <;>
    simp [hg, hfork, gasSchedule, GasCosts.WARM_ACCESS]

end UsdtVerify.Deprecated

namespace UsdtVerify.Complete

open EthLib.Base (Fork U256 toAddressMasked Address)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts
open Deprecated

variable {fork : Fork}

/-! ## The route of a CALL: no delegation, or an EIP-7702 delegate -/

/-- How a CALL to an address reaches the code that it runs. `none`: the code of the address
itself. `some (d, c')`: the code of the address is a delegation indicator to `d`, and the CALL
runs `c'`, the code of `d`. -/
abbrev Route := Option (Address × ByteArray)

/-- The route of a CALL to an account with code `c`, in the state `st`. With no delegation (before
Pectra, or `c` no indicator), the route is `none`. From Pectra, when `c` delegates to `d`, the
route is `some (d, c')` with `c'` the code of `d` found in `st`. -/
def Routes (fork : Fork) (st : State.TransactionState) (c : ByteArray) : Route → Prop
  | none => .pectra ≤ fork → delegatedAddress c = none
  | some (d, c') => .pectra ≤ fork ∧ delegatedAddress c = some d ∧
      st.getCode (st.getAccount d).codeHash = .ok c'

/-- The account whose code the CALL runs. -/
def routeAddr (a : Address) : Route → Address
  | none => a
  | some (d, _) => d

/-- The code that the CALL runs. -/
def routeCode (c : ByteArray) : Route → ByteArray
  | none => c
  | some (_, c') => c'

/-- The extra price of the route at `fork`: the access to the delegate (`accCost`, cold when it is
not in the set of accessed addresses `acc`), or 0. -/
def routeCost (fork : Fork) (acc : Std.ExtTreeSet Address) : Route → Nat
  | none => 0
  | some (d, _) => accCost fork (decide (d ∉ acc))

/-- The state once the route is followed: the read of the delegate recorded. -/
def routeState (st : State.TransactionState) : Route → State.TransactionState
  | none => st
  | some (d, _) => st.recordAccountRead d

/-- The substate once the route is followed: the delegate accessed. -/
def routeSub (ss : Substate) : Route → Substate
  | none => ss
  | some (d, _) => { ss with accessedAddresses := ss.accessedAddresses.insert d }

/-- The route depends on the state only through the code that it finds at each address. -/
theorem routes_congr {st st' : State.TransactionState} {c : ByteArray} {r : Route}
    (hst : ∀ a, st'.getCode (st'.getAccount a).codeHash = st.getCode (st.getAccount a).codeHash)
    (h : Routes fork st c r) : Routes fork st' c r := by
  rcases r with _ | ⟨d, c'⟩
  · exact h
  · exact ⟨h.1, h.2.1, (hst d).trans h.2.2⟩

/-- The route does not depend on the reads recorded in the state. -/
theorem routes_rec {st : State.TransactionState} {u : Address} {c : ByteArray} {r : Route}
    (h : Routes fork st c r) : Routes fork (st.recordAccountRead u) c r :=
  routes_congr (fun _ => rfl) h

/-- What the CALL of a deprecated path pays and passes on (EIP-150, EIP-2929), when the code asks
for `asked` with `left` gas: the warm access to the upgraded address (100), plus `R`, the price of
the route. -/
abbrev depCallGas (fork : Fork) (asked : U256) (left R : Nat) : MessageCallGas :=
  messageCallGas fork 0 asked.toNat left 0 (100 + R)

/-- The message that a deprecated path sends along the route `r`: from the contract to `ua`, with
the code and the code address of the route, the precompiles disabled when delegated, the data `d`
and no value. -/
def SendsVia (message : Message fork) (ua : Address) (c : ByteArray) (r : Route) (d : ByteArray)
    (msg : Message fork) : Prop :=
  msg.caller = message.currentTarget ∧ msg.currentTarget = ua ∧ msg.target = some ua ∧
    msg.codeAddress = some (routeAddr ua r) ∧ msg.code = routeCode c r ∧
    msg.disablePrecompiles = r.isSome ∧ msg.data = d ∧ msg.value = 0 ∧
    msg.depth = message.depth + 1 ∧ msg.isStatic = message.isStatic

/-- The state of the caller frame at a CALL from `C` to `ua` along the route `r`, from the state
`st` before the CALL: the reads of `ua`, of the delegate and of `C` recorded. -/
abbrev atCallState (st : State.TransactionState) (ua : Address) (r : Route) (C : Address) :
    State.TransactionState :=
  (routeState (st.recordAccountRead ua) r).recordAccountRead C

/-- The substate of the caller frame at a CALL to `ua` along the route `r`, from the substate
`ss` before the CALL: `ua` and the delegate accessed. -/
abbrev atCallSub (ss : Substate) (ua : Address) (r : Route) : Substate :=
  routeSub { ss with accessedAddresses := ss.accessedAddresses.insert ua } r

/-- Round 30 (docs/AUDIT.md, finding 3): the message `msg` has the gas `g`, and the caller frame
has the state `st` and the substate `ss`. The exact theorems of the deprecated paths ask their
callee assumption (`hans`) only of the message their CALL sends (`SendsVia`) with the gas, from
the caller frame, that the CALL gives (`CallFrom`), so the answer `A` can depend on that gas. -/
def CallFrom (g : Nat) (st : State.TransactionState) (ss : Substate) (caller : Evm fork Nat)
    (msg : Message fork) : Prop :=
  msg.gas = g ∧ caller.state = st ∧ caller.substate = ss

/-- Accessing an address twice is accessing it once, for the price of the route. -/
theorem routeCost_insert_insert (acc : Std.ExtTreeSet Address) (u : Address) (r : Route) :
    routeCost fork ((acc.insert u).insert u) r = routeCost fork (acc.insert u) r := by
  rcases r with _ | ⟨d, c'⟩
  · rfl
  · simp [routeCost]

/-- CALL (no value) below the greatest depth, with the gas of both accesses and the memory, along
any route: the step sends the message. -/
theorem callStep_child_r (hfork : .berlin ≤ fork)
    {evm : Evm fork Nat} {g a i isz o osz : U256} {rest : List U256} {calleeCode : ByteArray}
    {r : Route}
    (hst : evm.stack.val = g :: a :: 0 :: i :: isz :: o :: osz :: rest)
    (hcode : evm.state.getCode (evm.state.getAccount (toAddressMasked a)).codeHash = .ok calleeCode)
    (hroute : Routes fork evm.state calleeCode r)
    (hdepth : evm.message.depth + 1 ≤ STACK_DEPTH_LIMIT)
    (hgas : callBaseCost fork (decide (toAddressMasked a ∉ evm.substate.accessedAddresses)) +
      routeCost fork (evm.substate.accessedAddresses.insert (toAddressMasked a)) r +
      (extendMemory evm.memory.size [(i, isz), (o, osz)]).cost ≤ evm.gas) :
    ∃ caller msg, callStep .call evm = .ok (.child caller msg (resumeCall fork caller 0 o osz)) ∧
      caller.code = evm.code ∧ caller.validJumpDestinations = evm.validJumpDestinations ∧
      caller.message = evm.message ∧ caller.pc = evm.pc ∧ caller.stack.val = rest ∧
      caller.memory = memoryExtend evm.memory
        (extendMemory evm.memory.size [(i, isz), (o, osz)]).expandBy ∧
      caller.gas = evm.gas - ((messageCallGas fork 0 g.toNat evm.gas
        (extendMemory evm.memory.size [(i, isz), (o, osz)]).cost
        (callBaseCost fork (decide (toAddressMasked a ∉ evm.substate.accessedAddresses)) +
          routeCost fork (evm.substate.accessedAddresses.insert (toAddressMasked a)) r)).cost +
        (extendMemory evm.memory.size [(i, isz), (o, osz)]).cost) ∧
      caller.running = evm.running ∧ caller.error = evm.error ∧ caller.output = evm.output ∧
      caller.state = (routeState (evm.state.recordAccountRead (toAddressMasked a)) r).recordAccountRead
        evm.message.currentTarget ∧
      caller.substate = routeSub { evm.substate with
        accessedAddresses := evm.substate.accessedAddresses.insert (toAddressMasked a) } r ∧
      msg.gas = (messageCallGas fork 0 g.toNat evm.gas
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
      msg.isStatic = evm.message.isStatic := by
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
        GasMeter.gasLeft, GasMeter.drain, GasMeter.reservoir, hcb', Nat.not_lt.mpr hdepth, hM,
        chargeStateGas, GasMeter.chargeState, hgas, hk1, hmin', hx, routeState, routeSub, routeAddr,
        routeCode]
      exact ⟨_, _, ⟨rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, by dsimp only; omega, rfl, rfl, rfl,
        rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · simp [callStep, popCallOperands, popCallValue, CallKind.sendsValue, popWord, Stack.pop, bind,
        Except.bind, pure, Except.pure, accessAddress, hfork, checkGas, hG, accessDelegation,
        accountCode, recordAccountRead, hgc, hga, hal, hcode, hdel', hdcode d dCode rfl, htw,
        Except.mapError, callExtraGas, callNewAccountCost, callNewAccountStateGas, callValueCost,
        payCall, messageCallGas, chargeGas, GasMeter.charge, finishCall, genericCall, keepReads,
        GasMeter.gasLeft, GasMeter.drain, GasMeter.reservoir, hcb', hdc' d dCode rfl,
        Nat.not_lt.mpr hdepth, hM, chargeStateGas, GasMeter.chargeState, hgas, Nat.not_lt.mpr hgas, hk1, hk2, hmin', hx,
        routeState, routeSub, routeAddr, routeCode]
      exact ⟨_, _, ⟨rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, by dsimp only; omega, rfl, rfl, rfl,
        rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
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
        GasMeter.gasLeft, GasMeter.drain, GasMeter.reservoir, hcb', Nat.not_lt.mpr hdepth, hM, hgas,
        hmin2, hsd, routeState, routeSub, routeAddr, routeCode]
      exact ⟨_, _, ⟨rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
        rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · simp [callStep, popCallOperands, popCallValue, CallKind.sendsValue, popWord, Stack.pop, bind,
        Except.bind, pure, Except.pure, accessAddress, hfork, checkGas, hG, accessDelegation,
        accountCode, recordAccountRead, hgc, hga, hal, hcode, hdel', hdcode d dCode rfl, htw,
        Except.mapError, callExtraGas, callNewAccountCost, callNewAccountStateGas, callValueCost,
        payCall, messageCallGas, chargeGas, GasMeter.charge, finishCall, genericCall, keepReads,
        GasMeter.gasLeft, GasMeter.drain, GasMeter.reservoir, hcb', hdc' d dCode rfl,
        Nat.not_lt.mpr hdepth, hM, hgas, hmin2, hsd, routeState, routeSub, routeAddr, routeCode]
      exact ⟨_, _, ⟨rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
        rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩


/-- CALL with no value along the route `r`, under a callee assumption, for a runner that may fail
with any error: the run ends at the step after the CALL or at a failure of the runner on the
message the CALL sends (`SendsVia` with the data read from memory): EthLib's `callWith`, for
the code of the address itself or, from Pectra, the code of its delegate. The price adds the
access to the delegate (`routeCost`); the message runs the code of the route at the address of
the route, with the precompiles disabled when delegated, and keeps `to` as its current target;
the caller's state and substate record the read and the access of the delegate. -/
theorem callWithRS (hfork : .berlin ≤ fork)
    {code : ByteArray} {message : Message fork} {pc : Nat} {memory : ByteArray} {gas : Nat}
    {state : State.TransactionState} {substate : Substate}
    {callee : Evm fork Nat → Message fork → Evm fork Nat → Prop}
    {asked to i isz o osz : U256} {rest : List U256}
    {cold : Bool} {calleeCode : ByteArray} {r : Route} (hlt : pc < code.size)
    (hbyte : code[pc] = 0xf1)
    (hcode : state.getCode (state.getAccount (toAddressMasked to)).codeHash = .ok calleeCode)
    (hroute : Routes fork state calleeCode r)
    (hdepth : message.depth + 1 ≤ STACK_DEPTH_LIMIT)
    (hcold : decide (toAddressMasked to ∉ substate.accessedAddresses) = cold)
    (hgas : accCost fork cold +
      routeCost fork (substate.accessedAddresses.insert (toAddressMasked to)) r +
      (extendMemory memory.size [(i, isz), (o, osz)]).cost ≤ gas) :
    Sends.HoareOn fork callee
      (SendsVia message (toAddressMasked to) calleeCode r (memoryReadBytes (memoryExtend memory
        (extendMemory memory.size [(i, isz), (o, osz)]).expandBy) i.toNat isz.toNat))
      (At code message pc (asked :: to :: 0 :: i :: isz :: o :: osz :: rest) memory gas state
        substate)
      fun after => ∃ caller msg child, callee caller msg child ∧
        child.gas ≤ msg.gas ∧
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
        msg.value = 0 ∧ msg.depth = message.depth + 1 ∧ msg.isStatic = message.isStatic ∧
        At code message (pc + 1) ((if child.error.isNone then 1 else 0) :: rest)
          (memoryWrite (memoryExtend memory
            (extendMemory memory.size [(i, isz), (o, osz)]).expandBy)
            o.toNat (child.output.extract 0 (min osz.toNat child.output.size)))
          (gas - ((messageCallGas fork 0 asked.toNat gas
            (extendMemory memory.size [(i, isz), (o, osz)]).cost
            (accCost fork cold +
              routeCost fork (substate.accessedAddresses.insert (toAddressMasked to)) r)).cost +
            (extendMemory memory.size [(i, isz), (o, osz)]).cost) + child.gas)
          (incorporateChild fork caller child).state (incorporateChild fork caller child).substate
          after := by
  apply Sends.HoareOn.of_child
  rintro evm ⟨hc, hj, hm, hpc, hst, hmem, hg, hrun', herr, hout, hs, hss⟩
  have hcost := callBaseCost_eq hfork cold
  subst hm hg hs hss hcold hmem
  obtain ⟨caller, msg, hstep, c1, c2, c3, c4, c5, c6, c7, c8, c9, co, c10, c11, m1, m2, m3, mt,
      mca, m4, mdp, md, m5, m6, m7⟩ :=
    callStep_child_r hfork hst hcode hroute hdepth (by rw [hcost]; omega)
  refine ⟨hrun', caller, msg, resumeCall fork caller 0 o osz, ?_,
    ⟨m2, m3, mt, mca, m4, mdp, md, m5, m6, m7⟩, ?_⟩
  · rw [step_of_messageInstruction (by rw [hc, hpc]; exact hlt)
      (by simp only [hc, hpc, hbyte]; exact ofByte_of_decode (op := .call) rfl (Fork.frontier_le _))
      instruction_call messageInstruction_call]
    exact hstep
  · intro child hchild hcallee
    have hlen : caller.stack.val.length < STACK_LIMIT := by
      have := evm.stack.property
      rw [hst] at this
      rw [c5]
      simp at this
      omega
    obtain ⟨after, hres, a1, a2, a3, a4, a5, a6, a7, a8, a9, ao, a10, a11⟩ :=
      resumeCall_eq (child := child) (o := o) (osz := osz) hlen
    refine .inl ⟨after, hres, caller, msg, child, hcallee, hchild, c10, c11, ?_, m2, m3, mt, mca,
      m4, mdp, md, m5, m6, m7, ?_⟩
    · rw [m1, hcost]
    · refine ⟨by rw [a1, c1, hc], by rw [a2, c2, hj], by rw [a3, c3], by rw [a4, c4, hpc],
        by rw [a5, c5], by rw [a6, c6], ?_, by rw [a8, c8, hrun'], by rw [a9, c9, herr],
        by rw [ao, co, hout], a10, a11⟩
      rw [a7, c7, hcost]

/-- CALL with no value along the route `r`, under a callee assumption: EthLib's `callWith`, for
the code of the address itself or, from Pectra, the code of its delegate. The price adds the
access to the delegate (`routeCost`); the message runs the code of the route at the address of
the route, with the precompiles disabled when delegated, and keeps `to` as its current target;
the caller's state and substate record the read and the access of the delegate. -/
theorem callWithR (hfork : .berlin ≤ fork)
    {code : ByteArray} {message : Message fork} {pc : Nat} {memory : ByteArray} {gas : Nat}
    {state : State.TransactionState} {substate : Substate}
    {callee : Evm fork Nat → Message fork → Evm fork Nat → Prop}
    {asked to i isz o osz : U256} {rest : List U256}
    {cold : Bool} {calleeCode : ByteArray} {r : Route} (hlt : pc < code.size)
    (hbyte : code[pc] = 0xf1)
    (hcode : state.getCode (state.getAccount (toAddressMasked to)).codeHash = .ok calleeCode)
    (hroute : Routes fork state calleeCode r)
    (hdepth : message.depth + 1 ≤ STACK_DEPTH_LIMIT)
    (hcold : decide (toAddressMasked to ∉ substate.accessedAddresses) = cold)
    (hgas : accCost fork cold +
      routeCost fork (substate.accessedAddresses.insert (toAddressMasked to)) r +
      (extendMemory memory.size [(i, isz), (o, osz)]).cost ≤ gas) :
    HoareUnder fork callee
      (At code message pc (asked :: to :: 0 :: i :: isz :: o :: osz :: rest) memory gas state
        substate)
      fun after => ∃ caller msg child, callee caller msg child ∧
        child.gas ≤ msg.gas ∧
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
        msg.value = 0 ∧ msg.depth = message.depth + 1 ∧ msg.isStatic = message.isStatic ∧
        At code message (pc + 1) ((if child.error.isNone then 1 else 0) :: rest)
          (memoryWrite (memoryExtend memory
            (extendMemory memory.size [(i, isz), (o, osz)]).expandBy)
            o.toNat (child.output.extract 0 (min osz.toNat child.output.size)))
          (gas - ((messageCallGas fork 0 asked.toNat gas
            (extendMemory memory.size [(i, isz), (o, osz)]).cost
            (accCost fork cold +
              routeCost fork (substate.accessedAddresses.insert (toAddressMasked to)) r)).cost +
            (extendMemory memory.size [(i, isz), (o, osz)]).cost) + child.gas)
          (incorporateChild fork caller child).state (incorporateChild fork caller child).substate
          after :=
  (callWithRS hfork hlt hbyte hcode hroute hdepth hcold hgas).toUnder

end UsdtVerify.Complete
