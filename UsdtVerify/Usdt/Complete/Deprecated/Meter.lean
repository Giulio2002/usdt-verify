import UsdtVerify.Evm.RunCS
import UsdtVerify.Usdt.Complete.Deprecated.TotalSupply
import UsdtVerify.Usdt.Complete.Deprecated.BalanceOf
import UsdtVerify.Usdt.Complete.Deprecated.Allowance
import UsdtVerify.Usdt.Complete.Deprecated.Transfer
import UsdtVerify.Usdt.Complete.Deprecated.Destroy

/-!
# The deprecated paths over EthLib's EIP-8037 meter (round 39)

The completeness theorems of the deprecated paths, for a run of the loop of the interpreter over
`StateGasMeter` from a frame with reservoir 0, for any gas bound and any message runner over
`StateGasMeter`. Each one follows from its form over `RunC` (`dep_X_completeC`), through
`runC_of_sgm` (the run gives `RunC` with the relation `RunS` of the runner, step by step up to
the CALL, then the run of the meter `Nat` with more gas of `Shadow.shadow_run`) and
`endsOk_of_sgm` (for the dispatcher and the guards).

Each conclusion is the one of the theorem over `Nat` without the gas after the CALL: the frames
`caller` and `child` and the message are those of the run over `StateGasMeter`, the code found,
the route, the gas before the CALL, the gas of the message, the output, the state and the
substate at the end are exact. The gas left at the end is not stated: after the CALL the child may
give back a reservoir. Since round 41 each conclusion also states that the caller frame and the
message of the CALL have reservoir 0.

- `incorporateChild_toNat`: the state and substate of `incorporateChild` read no gas.
- `dep_totalSupply_completeS`, `dep_balanceOf_completeS`, `dep_allowance_completeS`,
  `dep_transfer_completeS`, `dep_approve_completeS`, `dep_transferFrom_completeS`,
  `dep_destroy_completeS` (for destroyBlackFunds also without the two facts on the gas of its tail).
-/

namespace UsdtVerify.Complete

open EthLib.Base (Fork U256 toAddressMasked)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open UsdtVerify.Gas
open UsdtVerify.Meter
open GasCosts
open Deprecated DeprecatedBalance DeprecatedAllowance DeprecatedTransfer DeprecatedTransferFrom
  DeprecatedDestroy Owner Admin Destroy BlackList Transfer TransferOk TransferFrom DestroySpec

/- The closing `simp only` calls of this file name every rewrite they may need. -/
set_option linter.unusedSimpArgs false

variable {fork : Fork}

/-- The state and the substate of `incorporateChild` over `Nat`, from the `toNat` of the caller
and a child with the state, substate, error and message of the child over `StateGasMeter`, are
those over `StateGasMeter`: they read no gas. -/
theorem incorporateChild_toNat (c ch : Evm fork StateGasMeter) (ch' : Evm fork Nat)
    (hs : ch'.state = ch.state) (hss : ch'.substate = ch.substate) (he : ch'.error = ch.error)
    (hm : ch'.message = ch.message) :
    (incorporateChild fork (toNat c) ch').state = (incorporateChild fork c ch).state ∧
    (incorporateChild fork (toNat c) ch').substate = (incorporateChild fork c ch).substate := by
  rcases ch' with ⟨pc, stack, memory, code, valid, gas, running, message, output, returnData,
    state, substate, error⟩
  simp only at hs hss he hm
  subst hs hss he hm
  unfold incorporateChild
  cases ch.error <;>
    simp only [Option.isNone_none, Option.isNone_some, ite_true, ite_false,
      Bool.false_eq_true] <;> first | exact ⟨rfl, rfl⟩ | exact ⟨trivial, rfl⟩ | exact ⟨rfl, trivial⟩ | exact ⟨trivial, trivial⟩

variable {bound : Nat} {runChild : MessageRunner fork StateGasMeter bound}
  {message : Message fork} {state : State.TransactionState} {substate : Substate}

/-- **Deprecated totalSupply() over the EIP-8037 meter.** From Berlin, from a frame `m` of
`StateGasMeter` with reservoir 0 whose `toNat` is the fresh frame of `CODE` at pc 0 with selector
0x18160ddd, deprecated, any gas: if the loop of the interpreter, for any gas bound and message
runner over `StateGasMeter`, ends with no error, then the conclusion of
`dep_totalSupply_complete` holds without its two facts on the gas after the CALL. -/
theorem dep_totalSupply_completeS (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x18160ddd)
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0)
    {gas : Nat} {m s : Evm fork StateGasMeter}
    (start : At CODE message 0 [] .empty gas state substate (toNat m))
    (hres : m.gas.reservoir = 0) {within : GasMeter.gasHeld m.gas ≤ bound}
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild m within = .ok s)
    (hok : s.error = none) :
    ∃ c r, state.getCode (state.getAccount (upAddr state message)).codeHash = .ok c ∧
    Routes fork state c r ∧
    BitVec.ofNat 256 c.size ≠ 0 ∧
    preCost fork (coldIn substate message.currentTarget 10)
      (decide (upAddr state message ∉ substate.accessedAddresses)) + 100 +
      routeCost fork (callSub substate state message).accessedAddresses r ≤ gas ∧
    message.depth + 1 ≤ STACK_DEPTH_LIMIT ∧
    ∃ caller msg lt child, runChild caller msg lt = .ok child ∧ child.1.error = none ∧
      caller.gas.reservoir = 0 ∧ msg.reservoir = 0 ∧
      SendsVia message (upAddr state message) c r SEL_TS msg ∧
      msg.gas = (depCallGas fork (askedOf fork gas (coldIn substate message.currentTarget 10)
          (decide (upAddr state message ∉ substate.accessedAddresses)))
        (gas - preCost fork (coldIn substate message.currentTarget 10)
          (decide (upAddr state message ∉ substate.accessedAddresses)))
        (routeCost fork (callSub substate state message).accessedAddresses r)).subCall ∧
      caller.state = (routeState ((callState state message).recordAccountRead
        (upAddr state message)) r).recordAccountRead message.currentTarget ∧
      caller.substate = routeSub { callSub substate state message with
        accessedAddresses :=
          (callSub substate state message).accessedAddresses.insert (upAddr state message) } r ∧
      s.running = false ∧ s.output = wordBytes (resWord (outMem child.1.output)) ∧
      s.state = (incorporateChild fork caller child.1).state ∧
      s.substate = (incorporateChild fork caller child.1).substate := by
  obtain ⟨G, hC⟩ := runC_of_sgm hfork hrun hok (.inl hres)
  obtain ⟨c, r, h1, h2, h3, h4, h5, caller, msg, child, ⟨cS, lt, chS, hch, rfl, hchN, hcr, hmr⟩, he, hfwd,
    hmg, hcs, hcss, -, hr, ho, -, hst, hss⟩ :=
    dep_totalSupply_completeC hfork hsize' hsel hdep start hC (endsOk_of_sgm hfork hrun hok) hok
  have cs : child.state = chS.1.state := by rw [hchN]; rfl
  have css : child.substate = chS.1.substate := by rw [hchN]; rfl
  have ce : child.error = chS.1.error := by rw [hchN]; rfl
  have co : child.output = chS.1.output := by rw [hchN]; rfl
  obtain ⟨i1, i2⟩ := incorporateChild_toNat cS chS.1 child cs css ce (by rw [hchN]; rfl)
  simp only [i1, i2, cs, css, ce, co] at he ho hst hss
  exact ⟨c, r, h1, h2, h3, h4, h5, cS, msg, lt, chS, hch, he, hcr, hmr, hfwd, hmg, hcs, hcss, hr, ho, hst, hss⟩

/-- **Deprecated balanceOf(a) over the EIP-8037 meter.** `dep_balanceOf_complete` for a run of the loop over
`StateGasMeter`, for any gas bound and message runner, from a frame `m` with reservoir 0 whose
`toNat` is the fresh frame: its conclusion without the gas left at the end and the bound on the gas
after the CALL. -/
theorem dep_balanceOf_completeS (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x70a08231)
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0)
    {gas : Nat} {m s : Evm fork StateGasMeter}
    (start : At CODE message 0 [] .empty gas state substate (toNat m))
    (hres : m.gas.reservoir = 0)
    {within : GasMeter.gasHeld m.gas ≤ bound}
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild m within = .ok s)
    (hok : s.error = none) :
    ∃ c r, state.getCode (state.getAccount (upAddr state message)).codeHash = .ok c ∧
    Routes fork state c r ∧
    BitVec.ofNat 256 c.size ≠ 0 ∧
    preCostB fork (coldIn substate message.currentTarget 10)
      (decide (upAddr state message ∉ substate.accessedAddresses)) + 100 +
      routeCost fork (callSub substate state message).accessedAddresses r ≤ gas ∧
    message.depth + 1 ≤ STACK_DEPTH_LIMIT ∧
    ∃ caller msg lt child, runChild caller msg lt = .ok child ∧ child.1.error = none ∧
      caller.gas.reservoir = 0 ∧ msg.reservoir = 0 ∧
      SendsVia message (upAddr state message) c r (dataB message) msg ∧
      msg.gas = (depCallGas fork (askedOfB fork gas (coldIn substate message.currentTarget 10)
          (decide (upAddr state message ∉ substate.accessedAddresses)))
        (gas - preCostB fork (coldIn substate message.currentTarget 10)
          (decide (upAddr state message ∉ substate.accessedAddresses)))
        (routeCost fork (callSub substate state message).accessedAddresses r)).subCall ∧
      caller.state = (routeState ((callState state message).recordAccountRead
        (upAddr state message)) r).recordAccountRead message.currentTarget ∧
      caller.substate = routeSub { callSub substate state message with
        accessedAddresses :=
          (callSub substate state message).accessedAddresses.insert (upAddr state message) } r ∧
      s.running = false ∧
      s.output = wordBytes (resWord (outMemOf (M2B (addrArg message.data 0)) child.1.output)) ∧
      s.state = (incorporateChild fork caller child.1).state ∧
      s.substate = (incorporateChild fork caller child.1).substate := by
  obtain ⟨G, hC⟩ := runC_of_sgm hfork hrun hok (.inl hres)
  obtain ⟨c, r, h1, h2, h3, h4, h5, caller, msg, child, ⟨cS, lt, chS, hch, rfl, hchN, hcr, hmr⟩, f0, q1, q2, q3, q4, -, q5, q6, -, q7, q8⟩ :=
    dep_balanceOf_completeC hfork hsize' hsel hdep start hC (endsOk_of_sgm hfork hrun hok) hok
  have cs : child.state = chS.1.state := by rw [hchN]; rfl
  have css : child.substate = chS.1.substate := by rw [hchN]; rfl
  have ce : child.error = chS.1.error := by rw [hchN]; rfl
  have co : child.output = chS.1.output := by rw [hchN]; rfl
  obtain ⟨i1, i2⟩ := incorporateChild_toNat cS chS.1 child cs css ce (by rw [hchN]; rfl)
  exact ⟨c, r, h1, h2, h3, h4, h5, cS, msg, lt, chS, hch, (by first | (simp only [i1, i2, cs, css, ce, co] at f0; exact f0) | exact f0), hcr, hmr, (by first | (simp only [i1, i2, cs, css, ce, co] at q1; exact q1) | exact q1), (by first | (simp only [i1, i2, cs, css, ce, co] at q2; exact q2) | exact q2), (by first | (simp only [i1, i2, cs, css, ce, co] at q3; exact q3) | exact q3), (by first | (simp only [i1, i2, cs, css, ce, co] at q4; exact q4) | exact q4), (by first | (simp only [i1, i2, cs, css, ce, co] at q5; exact q5) | exact q5), (by first | (simp only [i1, i2, cs, css, ce, co] at q6; exact q6) | exact q6), (by first | (simp only [i1, i2, cs, css, ce, co] at q7; exact q7) | exact q7), (by first | (simp only [i1, i2, cs, css, ce, co] at q8; exact q8) | exact q8)⟩

/-- **Deprecated allowance(a, b) over the EIP-8037 meter.** `dep_allowance_complete` for a run of the loop over
`StateGasMeter`, for any gas bound and message runner, from a frame `m` with reservoir 0 whose
`toNat` is the fresh frame: its conclusion without the gas left at the end and the bound on the gas
after the CALL. -/
theorem dep_allowance_completeS (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xdd62ed3e)
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0)
    {c10 cU : Bool} (hc10 : coldIn substate message.currentTarget 10 = c10)
    (hcU : decide (upAddr state message ∉ substate.accessedAddresses) = cU)
    {gas : Nat} {m s : Evm fork StateGasMeter}
    (start : At CODE message 0 [] .empty gas state substate (toNat m))
    (hres : m.gas.reservoir = 0)
    {within : GasMeter.gasHeld m.gas ≤ bound}
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild m within = .ok s)
    (hok : s.error = none) :
    ∃ c r, state.getCode (state.getAccount (upAddr state message)).codeHash = .ok c ∧
    Routes fork state c r ∧
    BitVec.ofNat 256 c.size ≠ 0 ∧
    preCostAl fork c10 cU + 100 + routeCost fork (callSub substate state message).accessedAddresses r ≤ gas ∧
    message.depth + 1 ≤ STACK_DEPTH_LIMIT ∧
    ∃ caller msg lt child, runChild caller msg lt = .ok child ∧ child.1.error = none ∧
      caller.gas.reservoir = 0 ∧ msg.reservoir = 0 ∧
      SendsVia message (upAddr state message) c r (dataAl message) msg ∧
      msg.gas = (depCallGas fork (askedOfAl fork gas c10 cU) (gas - preCostAl fork c10 cU)
        (routeCost fork (callSub substate state message).accessedAddresses r)).subCall ∧
      caller.state = (routeState ((callState state message).recordAccountRead
        (upAddr state message)) r).recordAccountRead message.currentTarget ∧
      caller.substate = routeSub { callSub substate state message with
        accessedAddresses :=
          (callSub substate state message).accessedAddresses.insert (upAddr state message) } r ∧
      s.running = false ∧
      s.output = wordBytes (resWord (outMemOf (memAl message) child.1.output)) ∧
      s.state = (incorporateChild fork caller child.1).state ∧
      s.substate = (incorporateChild fork caller child.1).substate := by
  obtain ⟨G, hC⟩ := runC_of_sgm hfork hrun hok (.inl hres)
  obtain ⟨c, r, h1, h2, h3, h4, h5, caller, msg, child, ⟨cS, lt, chS, hch, rfl, hchN, hcr, hmr⟩, f0, q1, q2, q3, q4, -, q5, q6, -, q7, q8⟩ :=
    dep_allowance_completeC hfork hsize' hsel hdep hc10 hcU start hC (endsOk_of_sgm hfork hrun hok) hok
  have cs : child.state = chS.1.state := by rw [hchN]; rfl
  have css : child.substate = chS.1.substate := by rw [hchN]; rfl
  have ce : child.error = chS.1.error := by rw [hchN]; rfl
  have co : child.output = chS.1.output := by rw [hchN]; rfl
  obtain ⟨i1, i2⟩ := incorporateChild_toNat cS chS.1 child cs css ce (by rw [hchN]; rfl)
  exact ⟨c, r, h1, h2, h3, h4, h5, cS, msg, lt, chS, hch, (by first | (simp only [i1, i2, cs, css, ce, co] at f0; exact f0) | exact f0), hcr, hmr, (by first | (simp only [i1, i2, cs, css, ce, co] at q1; exact q1) | exact q1), (by first | (simp only [i1, i2, cs, css, ce, co] at q2; exact q2) | exact q2), (by first | (simp only [i1, i2, cs, css, ce, co] at q3; exact q3) | exact q3), (by first | (simp only [i1, i2, cs, css, ce, co] at q4; exact q4) | exact q4), (by first | (simp only [i1, i2, cs, css, ce, co] at q5; exact q5) | exact q5), (by first | (simp only [i1, i2, cs, css, ce, co] at q6; exact q6) | exact q6), (by first | (simp only [i1, i2, cs, css, ce, co] at q7; exact q7) | exact q7), (by first | (simp only [i1, i2, cs, css, ce, co] at q8; exact q8) | exact q8)⟩

/-- **Deprecated transfer(to, value) over the EIP-8037 meter.** `dep_transfer_complete` for a run of the loop over
`StateGasMeter`, for any gas bound and message runner, from a frame `m` with reservoir 0 whose
`toNat` is the fresh frame: its conclusion without the gas left at the end and the bound on the gas
after the CALL. -/
theorem dep_transfer_completeS (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xa9059cbb)
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0)
    {c0 cB c10 cU : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hcB : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget
      (blackSlot message) = cB)
    (hc10 : coldIn (accessSlot (accessSlot substate message.currentTarget 0) message.currentTarget
      (blackSlot message)) message.currentTarget 10 = c10)
    (hcU : decide (upAddr state message ∉ substate.accessedAddresses) = cU)
    {gas : Nat} {m s : Evm fork StateGasMeter}
    (start : At CODE message 0 [] .empty gas state substate (toNat m))
    (hres : m.gas.reservoir = 0)
    {within : GasMeter.gasHeld m.gas ≤ bound}
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild m within = .ok s)
    (hok : s.error = none) :
    ∃ c r, state.getCode (state.getAccount (upAddr state message)).codeHash = .ok c ∧
    Routes fork state c r ∧
    byte20 (storageAt state message.currentTarget 0) = 0 ∧
    (storageAt state message.currentTarget (blackSlot message)).toNat % 256 = 0 ∧
    BitVec.ofNat 256 c.size ≠ 0 ∧
    preCostT fork c0 cB c10 cU + 100 + routeCost fork (callSubT substate state message).accessedAddresses r ≤ gas ∧
    message.depth + 1 ≤ STACK_DEPTH_LIMIT ∧
    ∃ caller msg lt child, runChild caller msg lt = .ok child ∧ child.1.error = none ∧
      caller.gas.reservoir = 0 ∧ msg.reservoir = 0 ∧
      SendsVia message (upAddr state message) c r (dataT message) msg ∧
      msg.gas = (depCallGas fork (askedOfT fork gas c0 cB c10 cU) (gas - preCostT fork c0 cB c10 cU)
        (routeCost fork (callSubT substate state message).accessedAddresses r)).subCall ∧
      caller.state = (routeState ((callStateT state message).recordAccountRead
        (upAddr state message)) r).recordAccountRead message.currentTarget ∧
      caller.substate = routeSub { callSubT substate state message with
        accessedAddresses :=
          (callSubT substate state message).accessedAddresses.insert (upAddr state message) } r ∧
      s.running = false ∧ s.output = .empty ∧
      s.state = (incorporateChild fork caller child.1).state ∧
      s.substate = (incorporateChild fork caller child.1).substate := by
  obtain ⟨G, hC⟩ := runC_of_sgm hfork hrun hok (.inl hres)
  obtain ⟨c, r, h1, h2, h3, h4, h5, h6, h7, caller, msg, child, ⟨cS, lt, chS, hch, rfl, hchN, hcr, hmr⟩, f0, q1, q2, q3, q4, -, q5, q6, -, q7, q8⟩ :=
    dep_transfer_completeC hfork hsize' hsel hdep hc0 hcB hc10 hcU start hC (endsOk_of_sgm hfork hrun hok) hok
  have cs : child.state = chS.1.state := by rw [hchN]; rfl
  have css : child.substate = chS.1.substate := by rw [hchN]; rfl
  have ce : child.error = chS.1.error := by rw [hchN]; rfl
  have co : child.output = chS.1.output := by rw [hchN]; rfl
  obtain ⟨i1, i2⟩ := incorporateChild_toNat cS chS.1 child cs css ce (by rw [hchN]; rfl)
  exact ⟨c, r, h1, h2, h3, h4, h5, h6, h7, cS, msg, lt, chS, hch, (by first | (simp only [i1, i2, cs, css, ce, co] at f0; exact f0) | exact f0), hcr, hmr, (by first | (simp only [i1, i2, cs, css, ce, co] at q1; exact q1) | exact q1), (by first | (simp only [i1, i2, cs, css, ce, co] at q2; exact q2) | exact q2), (by first | (simp only [i1, i2, cs, css, ce, co] at q3; exact q3) | exact q3), (by first | (simp only [i1, i2, cs, css, ce, co] at q4; exact q4) | exact q4), (by first | (simp only [i1, i2, cs, css, ce, co] at q5; exact q5) | exact q5), (by first | (simp only [i1, i2, cs, css, ce, co] at q6; exact q6) | exact q6), (by first | (simp only [i1, i2, cs, css, ce, co] at q7; exact q7) | exact q7), (by first | (simp only [i1, i2, cs, css, ce, co] at q8; exact q8) | exact q8)⟩

/-- **Deprecated approve(spender, value) over the EIP-8037 meter.** `dep_approve_complete` for a run of the loop over
`StateGasMeter`, for any gas bound and message runner, from a frame `m` with reservoir 0 whose
`toNat` is the fresh frame: its conclusion without the gas left at the end and the bound on the gas
after the CALL. -/
theorem dep_approve_completeS (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x095ea7b3)
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0)
    {c10 cU : Bool} (hc10 : coldIn substate message.currentTarget 10 = c10)
    (hcU : decide (upAddr state message ∉ substate.accessedAddresses) = cU)
    {gas : Nat} {m s : Evm fork StateGasMeter}
    (start : At CODE message 0 [] .empty gas state substate (toNat m))
    (hres : m.gas.reservoir = 0)
    {within : GasMeter.gasHeld m.gas ≤ bound}
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild m within = .ok s)
    (hok : s.error = none) :
    ∃ c r, state.getCode (state.getAccount (upAddr state message)).codeHash = .ok c ∧
    Routes fork state c r ∧
    68 ≤ message.data.size ∧
    BitVec.ofNat 256 c.size ≠ 0 ∧
    preCostA fork c10 cU + 100 + routeCost fork (callSub substate state message).accessedAddresses r ≤ gas ∧
    message.depth + 1 ≤ STACK_DEPTH_LIMIT ∧
    ∃ caller msg lt child, runChild caller msg lt = .ok child ∧ child.1.error = none ∧
      caller.gas.reservoir = 0 ∧ msg.reservoir = 0 ∧
      SendsVia message (upAddr state message) c r (dataA message) msg ∧
      msg.gas = (depCallGas fork (askedOfA fork gas c10 cU) (gas - preCostA fork c10 cU)
        (routeCost fork (callSub substate state message).accessedAddresses r)).subCall ∧
      caller.state = (routeState ((callState state message).recordAccountRead
        (upAddr state message)) r).recordAccountRead message.currentTarget ∧
      caller.substate = routeSub { callSub substate state message with
        accessedAddresses :=
          (callSub substate state message).accessedAddresses.insert (upAddr state message) } r ∧
      s.running = false ∧ s.output = .empty ∧
      s.state = (incorporateChild fork caller child.1).state ∧
      s.substate = (incorporateChild fork caller child.1).substate := by
  obtain ⟨G, hC⟩ := runC_of_sgm hfork hrun hok (.inl hres)
  obtain ⟨c, r, h1, h2, h3, h4, h5, h6, caller, msg, child, ⟨cS, lt, chS, hch, rfl, hchN, hcr, hmr⟩, f0, q1, q2, q3, q4, -, q5, q6, -, q7, q8⟩ :=
    dep_approve_completeC hfork hsize' hsel hdep hc10 hcU start hC (endsOk_of_sgm hfork hrun hok) hok
  have cs : child.state = chS.1.state := by rw [hchN]; rfl
  have css : child.substate = chS.1.substate := by rw [hchN]; rfl
  have ce : child.error = chS.1.error := by rw [hchN]; rfl
  have co : child.output = chS.1.output := by rw [hchN]; rfl
  obtain ⟨i1, i2⟩ := incorporateChild_toNat cS chS.1 child cs css ce (by rw [hchN]; rfl)
  exact ⟨c, r, h1, h2, h3, h4, h5, h6, cS, msg, lt, chS, hch, (by first | (simp only [i1, i2, cs, css, ce, co] at f0; exact f0) | exact f0), hcr, hmr, (by first | (simp only [i1, i2, cs, css, ce, co] at q1; exact q1) | exact q1), (by first | (simp only [i1, i2, cs, css, ce, co] at q2; exact q2) | exact q2), (by first | (simp only [i1, i2, cs, css, ce, co] at q3; exact q3) | exact q3), (by first | (simp only [i1, i2, cs, css, ce, co] at q4; exact q4) | exact q4), (by first | (simp only [i1, i2, cs, css, ce, co] at q5; exact q5) | exact q5), (by first | (simp only [i1, i2, cs, css, ce, co] at q6; exact q6) | exact q6), (by first | (simp only [i1, i2, cs, css, ce, co] at q7; exact q7) | exact q7), (by first | (simp only [i1, i2, cs, css, ce, co] at q8; exact q8) | exact q8)⟩

/-- **Deprecated transferFrom(from, to, value) over the EIP-8037 meter.** `dep_transferFrom_complete` for a run of the loop over
`StateGasMeter`, for any gas bound and message runner, from a frame `m` with reservoir 0 whose
`toNat` is the fresh frame: its conclusion without the gas left at the end and the bound on the gas
after the CALL. -/
theorem dep_transferFrom_completeS (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x23b872dd)
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0)
    {c0 cB c10 cU : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hcB : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget
      (blackFrom (fromArg message)) = cB)
    (hc10 : coldIn (accessSlot (accessSlot substate message.currentTarget 0) message.currentTarget
      (blackFrom (fromArg message))) message.currentTarget 10 = c10)
    (hcU : decide (upAddr state message ∉ substate.accessedAddresses) = cU)
    {gas : Nat} {m s : Evm fork StateGasMeter}
    (start : At CODE message 0 [] .empty gas state substate (toNat m))
    (hres : m.gas.reservoir = 0)
    {within : GasMeter.gasHeld m.gas ≤ bound}
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild m within = .ok s)
    (hok : s.error = none) :
    ∃ c r, state.getCode (state.getAccount (upAddr state message)).codeHash = .ok c ∧
    Routes fork state c r ∧
    byte20 (storageAt state message.currentTarget 0) = 0 ∧
    (storageAt state message.currentTarget (blackFrom (fromArg message))).toNat % 256 = 0 ∧
    BitVec.ofNat 256 c.size ≠ 0 ∧
    DeprecatedTransferFrom.preCostF fork c0 cB c10 cU + 100 + routeCost fork (callSubF substate state message).accessedAddresses r ≤ gas ∧
    message.depth + 1 ≤ STACK_DEPTH_LIMIT ∧
    ∃ caller msg lt child, runChild caller msg lt = .ok child ∧ child.1.error = none ∧
      caller.gas.reservoir = 0 ∧ msg.reservoir = 0 ∧
      SendsVia message (upAddr state message) c r (dataF message) msg ∧
      msg.gas = (depCallGas fork (askedOfF fork gas c0 cB c10 cU) (gas - DeprecatedTransferFrom.preCostF fork c0 cB c10 cU)
        (routeCost fork (callSubF substate state message).accessedAddresses r)).subCall ∧
      caller.state = (routeState ((callStateF state message).recordAccountRead
        (upAddr state message)) r).recordAccountRead message.currentTarget ∧
      caller.substate = routeSub { callSubF substate state message with
        accessedAddresses :=
          (callSubF substate state message).accessedAddresses.insert (upAddr state message) } r ∧
      s.running = false ∧ s.output = .empty ∧
      s.state = (incorporateChild fork caller child.1).state ∧
      s.substate = (incorporateChild fork caller child.1).substate := by
  obtain ⟨G, hC⟩ := runC_of_sgm hfork hrun hok (.inl hres)
  obtain ⟨c, r, h1, h2, h3, h4, h5, h6, h7, caller, msg, child, ⟨cS, lt, chS, hch, rfl, hchN, hcr, hmr⟩, f0, q1, q2, q3, q4, -, q5, q6, -, q7, q8⟩ :=
    dep_transferFrom_completeC hfork hsize' hsel hdep hc0 hcB hc10 hcU start hC (endsOk_of_sgm hfork hrun hok) hok
  have cs : child.state = chS.1.state := by rw [hchN]; rfl
  have css : child.substate = chS.1.substate := by rw [hchN]; rfl
  have ce : child.error = chS.1.error := by rw [hchN]; rfl
  have co : child.output = chS.1.output := by rw [hchN]; rfl
  obtain ⟨i1, i2⟩ := incorporateChild_toNat cS chS.1 child cs css ce (by rw [hchN]; rfl)
  exact ⟨c, r, h1, h2, h3, h4, h5, h6, h7, cS, msg, lt, chS, hch, (by first | (simp only [i1, i2, cs, css, ce, co] at f0; exact f0) | exact f0), hcr, hmr, (by first | (simp only [i1, i2, cs, css, ce, co] at q1; exact q1) | exact q1), (by first | (simp only [i1, i2, cs, css, ce, co] at q2; exact q2) | exact q2), (by first | (simp only [i1, i2, cs, css, ce, co] at q3; exact q3) | exact q3), (by first | (simp only [i1, i2, cs, css, ce, co] at q4; exact q4) | exact q4), (by first | (simp only [i1, i2, cs, css, ce, co] at q5; exact q5) | exact q5), (by first | (simp only [i1, i2, cs, css, ce, co] at q6; exact q6) | exact q6), (by first | (simp only [i1, i2, cs, css, ce, co] at q7; exact q7) | exact q7), (by first | (simp only [i1, i2, cs, css, ce, co] at q8; exact q8) | exact q8)⟩

/-- **Deprecated destroyBlackFunds(a) over the EIP-8037 meter.** `dep_destroy_complete` for a run of the loop over
`StateGasMeter`, for any gas bound and message runner, from a frame `m` with reservoir 0 whose
`toNat` is the fresh frame: its conclusion without the gas left at the end and the bound on the gas
after the CALL and the two facts on the gas of the tail (`tailCost`, `tailStip`). -/
theorem dep_destroy_completeS (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xf3bdc228)
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0)
    {c0 cL c10 cU : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hcL : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget
      (listSlot (addrArg message.data 0)) = cL)
    (hc10 : coldIn (preSub substate message) message.currentTarget 10 = c10)
    (hcU : decide (upAddr state message ∉ substate.accessedAddresses) = cU)
    {gas : Nat} {m s : Evm fork StateGasMeter}
    (start : At CODE message 0 [] .empty gas state substate (toNat m))
    (hres : m.gas.reservoir = 0)
    {within : GasMeter.gasHeld m.gas ≤ bound}
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild m within = .ok s)
    (hok : s.error = none) :
    ∃ c r, state.getCode (state.getAccount (upAddr state message)).codeHash = .ok c ∧
    Routes fork state c r ∧
    callerWord message = ownerOf state message.currentTarget ∧
    (storageAt state message.currentTarget (listSlot (addrArg message.data 0))).toNat % 256 ≠ 0 ∧
    BitVec.ofNat 256 c.size ≠ 0 ∧
    preCostD fork c0 cL c10 cU + 100 + routeCost fork (callSubD substate state message).accessedAddresses r ≤ gas ∧
    message.depth + 1 ≤ STACK_DEPTH_LIMIT ∧
    ∃ caller msg lt child, runChild caller msg lt = .ok child ∧ child.1.error = none ∧
      caller.gas.reservoir = 0 ∧ msg.reservoir = 0 ∧
      message.isStatic = false ∧ hasAccount child.1.state message.currentTarget ∧
      SendsVia message (upAddr state message) c r (dataB message) msg ∧
      msg.gas = (depCallGas fork (askedOfD fork gas c0 cL c10 cU) (gas - preCostD fork c0 cL c10 cU)
        (routeCost fork (callSubD substate state message).accessedAddresses r)).subCall ∧
      caller.state = (routeState ((callStateD state message).recordAccountRead
        (upAddr state message)) r).recordAccountRead message.currentTarget ∧
      caller.substate = routeSub { callSubD substate state message with
        accessedAddresses :=
          (callSubD substate state message).accessedAddresses.insert (upAddr state message) } r ∧
      s.running = false ∧ s.output = .empty ∧
      s.state = tailState (incorporateChild fork caller child.1).state message.currentTarget
        (addrArg message.data 0) (resWord (outMemOf (memD message) child.1.output)) ∧
      s.substate = tailSub fork (incorporateChild fork caller child.1).substate
        (incorporateChild fork caller child.1).state message.currentTarget
        (addrArg message.data 0) (resWord (outMemOf (memD message) child.1.output)) := by
  obtain ⟨G, hC⟩ := runC_of_sgm hfork hrun hok (.inl hres)
  obtain ⟨c, r, h1, h2, h3, h4, h5, h6, h7, caller, msg, child, ⟨cS, lt, chS, hch, rfl, hchN, hcr, hmr⟩, f0, q1, q2, q3, q4, q5, q6, -, q7, q8, -, q9, q10, -⟩ :=
    dep_destroy_completeC hfork hsize' hsel hdep hc0 hcL hc10 hcU start hC (endsOk_of_sgm hfork hrun hok) hok
  have cs : child.state = chS.1.state := by rw [hchN]; rfl
  have css : child.substate = chS.1.substate := by rw [hchN]; rfl
  have ce : child.error = chS.1.error := by rw [hchN]; rfl
  have co : child.output = chS.1.output := by rw [hchN]; rfl
  obtain ⟨i1, i2⟩ := incorporateChild_toNat cS chS.1 child cs css ce (by rw [hchN]; rfl)
  exact ⟨c, r, h1, h2, h3, h4, h5, h6, h7, cS, msg, lt, chS, hch, (by first | (simp only [i1, i2, cs, css, ce, co] at f0; exact f0) | exact f0), hcr, hmr, (by first | (simp only [i1, i2, cs, css, ce, co] at q1; exact q1) | exact q1), (by first | (simp only [i1, i2, cs, css, ce, co] at q2; exact q2) | exact q2), (by first | (simp only [i1, i2, cs, css, ce, co] at q3; exact q3) | exact q3), (by first | (simp only [i1, i2, cs, css, ce, co] at q4; exact q4) | exact q4), (by first | (simp only [i1, i2, cs, css, ce, co] at q5; exact q5) | exact q5), (by first | (simp only [i1, i2, cs, css, ce, co] at q6; exact q6) | exact q6), (by first | (simp only [i1, i2, cs, css, ce, co] at q7; exact q7) | exact q7), (by first | (simp only [i1, i2, cs, css, ce, co] at q8; exact q8) | exact q8), (by first | (simp only [i1, i2, cs, css, ce, co] at q9; exact q9) | exact q9), (by first | (simp only [i1, i2, cs, css, ce, co] at q10; exact q10) | exact q10)⟩

end UsdtVerify.Complete
