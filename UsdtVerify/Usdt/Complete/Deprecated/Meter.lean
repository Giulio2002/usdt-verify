import UsdtVerify.Evm.RunCS
import UsdtVerify.Usdt.Complete.Deprecated.TotalSupply

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
give back a reservoir.

- `incorporateChild_toNat`: the state and substate of `incorporateChild` read no gas.
- `dep_totalSupply_completeS`.
-/

namespace UsdtVerify.Complete

open EthLib.Base (Fork U256 toAddressMasked)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open UsdtVerify.Gas
open UsdtVerify.Meter
open GasCosts
open Deprecated

variable {fork : Fork}

/-- The state and the substate of `incorporateChild` over `Nat`, from the `toNat` frames with any
gas for the child, are those over `StateGasMeter`. -/
theorem incorporateChild_toNat (c ch : Evm fork StateGasMeter) (g : Nat) :
    (incorporateChild fork (toNat c) { toNat ch with gas := g }).state =
      (incorporateChild fork c ch).state ∧
    (incorporateChild fork (toNat c) { toNat ch with gas := g }).substate =
      (incorporateChild fork c ch).substate := by
  rcases ch with ⟨pc, stack, memory, code, valid, gas, running, message, output, returnData,
    state, substate, error⟩
  cases error <;> exact ⟨rfl, rfl⟩

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
  obtain ⟨c, r, h1, h2, h3, h4, h5, caller, msg, child, ⟨cS, lt, chS, hch, rfl, hchN⟩, he, hfwd,
    hmg, hcs, hcss, -, hr, ho, -, hst, hss⟩ :=
    dep_totalSupply_completeC hfork hsize' hsel hdep start hC (endsOk_of_sgm hfork hrun hok) hok
  obtain ⟨g, rfl⟩ : ∃ g, child = { toNat chS.1 with gas := g } := ⟨_, hchN⟩
  obtain ⟨i1, i2⟩ := incorporateChild_toNat cS chS.1 g
  exact ⟨c, r, h1, h2, h3, h4, h5, cS, msg, lt, chS, hch, he, hfwd, hmg, hcs, hcss, hr, ho,
    hst.trans i1, hss.trans i2⟩

end UsdtVerify.Complete
