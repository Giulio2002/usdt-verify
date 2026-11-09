import UsdtVerify.Usdt.Complete.Deprecated.CallExactS
import UsdtVerify.Usdt.Complete.Deprecated.MeterR

/-!
# Six deprecated paths over the EIP-8037 meter: the exact meter after the CALL and at the end (round 45)

`dep_X_completeR` (round 42) states, for deprecated totalSupply, balanceOf, allowance, transfer,
approve and transferFrom over `StateGasMeter` from any reservoir, the execution gas left plus the
reservoir at the end as a sum. Here the run is followed over `StateGasMeter` itself: from pc 0 to
EXTCODESIZE forward (`fwd_splitS` along `prefixG_X`), then through the CALL, the runner, the
resume and the tail (`dep_call_exactS`).

Each `dep_X_exactR`: from Berlin, from a frame `m` with ANY reservoir whose `toNat` is the fresh
frame of `CODE` with the selector of `X`, deprecated, for any gas bound and message runner over
`StateGasMeter`: every run that ends with no error has the facts of `dep_X_completeR` on the code,
the route, the guards, the gas before the CALL and the depth, and went through the CALL with a
caller whose meter is the meter of `m` with reservoir 0 and the gas before the CALL less its price,
the message of `SendsVia` carrying the reservoir of `m`, and a child with no error. The meter after
the CALL is `GasMeter.absorb caller.gas child.gas true` (its execution gas left plus its reservoir
is the caller's execution gas left plus the child's execution gas left and reservoir); the gas of
the tail (`T`: 121, 126, 128, 51, 53, 53) is at most its execution gas left; and the end has the
output, state and substate of `dep_X_completeR` and that meter less `T` execution gas. So the
split between execution gas and reservoir at the end is stated, as a function of the meter the
child ends with (which the runner fixes).
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
  Owner Admin BlackList Transfer TransferOk TransferFrom

variable {fork : Fork}
variable {bound : Nat} {runChild : MessageRunner fork StateGasMeter bound}
  {message : Message fork} {state : State.TransactionState} {substate : Substate}

/-- **Deprecated totalSupply() over the EIP-8037 meter, any reservoir, the exact meter after the
CALL and at the end.** See the module doc; the tail is 121 gas. -/
theorem dep_totalSupply_exactR (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x18160ddd)
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0)
    {c10 cU : Bool} (hc10 : coldIn substate message.currentTarget 10 = c10)
    (hcU : decide (upAddr state message ∉ substate.accessedAddresses) = cU)
    {gas : Nat} {m s : Evm fork StateGasMeter}
    (start : At CODE message 0 [] .empty gas state substate (toNat m))
    {within : GasMeter.gasHeld m.gas ≤ bound}
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild m within = .ok s)
    (hok : s.error = none) :
    ∃ c r, state.getCode (state.getAccount (upAddr state message)).codeHash = .ok c ∧
    Routes fork state c r ∧
    BitVec.ofNat 256 c.size ≠ 0 ∧
    preCost fork c10 cU + 100 +
      routeCost fork (callSub substate state message).accessedAddresses r ≤ gas ∧
    message.depth + 1 ≤ STACK_DEPTH_LIMIT ∧
    ∃ caller msg lt child, runChild caller msg lt = .ok child ∧ child.1.error = none ∧
      caller.gas = { m.gas with reservoir := 0, gasLeft := gas - preCost fork c10 cU -
        (depCallGas fork (askedOf fork gas c10 cU) (gas - preCost fork c10 cU)
          (routeCost fork (callSub substate state message).accessedAddresses r)).cost } ∧
      msg.reservoir = m.gas.reservoir ∧
      SendsVia message (upAddr state message) c r SEL_TS msg ∧
      msg.gas = (depCallGas fork (askedOf fork gas c10 cU) (gas - preCost fork c10 cU)
        (routeCost fork (callSub substate state message).accessedAddresses r)).subCall ∧
      caller.state = (routeState ((callState state message).recordAccountRead
        (upAddr state message)) r).recordAccountRead message.currentTarget ∧
      caller.substate = routeSub { callSub substate state message with
        accessedAddresses :=
          (callSub substate state message).accessedAddresses.insert (upAddr state message) } r ∧
      (GasMeter.absorb caller.gas child.1.gas true).gasLeft +
          (GasMeter.absorb caller.gas child.1.gas true).reservoir =
        caller.gas.gasLeft + child.1.gas.gasLeft + child.1.gas.reservoir ∧
      121 ≤ (GasMeter.absorb caller.gas child.1.gas true).gasLeft ∧
      s.running = false ∧ s.output = wordBytes (resWord (outMem child.1.output)) ∧
      s.state = (incorporateChild fork caller child.1).state ∧
      s.substate = (incorporateChild fork caller child.1).substate ∧
      s.gas = { GasMeter.absorb caller.gas child.1.gas true with
        gasLeft := (GasMeter.absorb caller.gas child.1.gas true).gasLeft - 121 } := by
  subst hc10 hcU
  obtain ⟨c, r, hcode, hroute, hw, hgas, hdepth, -⟩ :=
    dep_totalSupply_completeR hfork hsize' hsel hdep start hrun hok
  obtain ⟨h4, hv, -⟩ := EndsOk.dispatch hfork hsize' start (endsOk_of_sgm hfork hrun hok)
  have hs10 := slotCost_le (coldIn substate message.currentTarget 10)
  have hG0 : 602 + slotCost (coldIn substate message.currentTarget 10) +
      extCost fork (decide (upAddr state message ∉ substate.accessedAddresses)) + 100 +
      routeCost fork (callSub substate state message).accessedAddresses r ≤ gas := hgas
  -- pc 0 to EXTCODESIZE
  obtain ⟨m1, hat1, hg1, hrun1⟩ := fwd_splitS
    (fun g hg => prefixG_totalSupply hfork h4 hsize' hsel hv hdep rfl hg)
    (by omega) (fun _ _ => rfl) (by omega) start
  obtain ⟨w1, e1⟩ := hrun1 within
  rw [e1] at hrun
  have hext : extendMemory M2.size
      [((0x60 : U256), (4 : U256)), ((0x60 : U256), (0x20 : U256))] = ⟨0, 0⟩ := by
    rw [size_M2]; decide
  -- EXTCODESIZE to the end
  obtain ⟨caller, msg, lt, chS, hch, he, hcg, m0, mg, hsv, k10, k11, hsum, hT, hr, ho, hst, hss,
      hgs⟩ :=
    dep_call_exactS (message := message) (U := upWord (storageAt state message.currentTarget 10))
      (rest := [0x64, 0x18160ddd, upWord (storageAt state message.currentTarget 10), 0, 0x031d,
        BitVec.ofNat 256 (selector message.data)])
      (st := readSlot state message.currentTarget 10)
      (ss := accessSlot substate message.currentTarget 10)
      (A := extCost fork (decide (upAddr state message ∉ substate.accessedAddresses)))
      (R := routeCost fork (callSub substate state message).accessedAddresses r)
      (T := 121) (out := fun ob => wordBytes (resWord (outMem ob)))
      hfork (Or.inl ⟨rfl, rfl⟩) (by simp) hext hcode hw (Logic.Routes.congr (fun _ => rfl) hroute)
      hdepth rfl rfl (by omega) (by decide)
      (fun ob S sb g hg => okTail (fork := fork) (message := message) (state := S) (substate := sb)
        (U := upWord (storageAt state message.currentTarget 10)) (size_outMem ob) (mload_outMem ob)
        (x := BitVec.ofNat 256 (selector message.data)) hg)
      hat1 hrun hok
  have e1 : gas - (574 + slotCost (coldIn substate message.currentTarget 10)) -
      (extCost fork (decide (upAddr state message ∉ substate.accessedAddresses)) + 25) =
      gas - (599 + slotCost (coldIn substate message.currentTarget 10) +
        extCost fork (decide (upAddr state message ∉ substate.accessedAddresses))) := by omega
  have e2 : gas - (574 + slotCost (coldIn substate message.currentTarget 10)) -
      (extCost fork (decide (upAddr state message ∉ substate.accessedAddresses)) + 28) =
      gas - preCost fork (coldIn substate message.currentTarget 10)
        (decide (upAddr state message ∉ substate.accessedAddresses)) := by
    simp only [Deprecated.preCost]; omega
  refine ⟨c, r, hcode, hroute, hw, hgas, hdepth, caller, msg, lt, chS, hch, he, ?_,
    by rw [m0, hg1], ?_, ?_, k10, k11, hsum, hT, hr, ho, hst, hss, hgs⟩
  · rw [hcg, hg1, e1, e2]
  · obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13⟩ := hsv
    exact ⟨d1, d2, d3, d4, d5, d6, by
      have h := data_M2; rw [memoryExtend_zero] at h
      rw [d7, show (0x60 : U256).toNat = 96 by simp, show (4 : U256).toNat = 4 by simp, h], d8, d9, d10, d11, d12, d13⟩
  · rw [mg, e1, e2]

/-- **Deprecated balanceOf(a) over the EIP-8037 meter, any reservoir, the exact meter after the
CALL and at the end.** See the module doc; the tail is 126 gas. -/
theorem dep_balanceOf_exactR (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x70a08231)
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0)
    {c10 cU : Bool} (hc10 : coldIn substate message.currentTarget 10 = c10)
    (hcU : decide (upAddr state message ∉ substate.accessedAddresses) = cU)
    {gas : Nat} {m s : Evm fork StateGasMeter}
    (start : At CODE message 0 [] .empty gas state substate (toNat m))
    {within : GasMeter.gasHeld m.gas ≤ bound}
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild m within = .ok s)
    (hok : s.error = none) :
    ∃ c r, state.getCode (state.getAccount (upAddr state message)).codeHash = .ok c ∧
    Routes fork state c r ∧
    BitVec.ofNat 256 c.size ≠ 0 ∧
    preCostB fork c10 cU + 100 +
      routeCost fork (callSub substate state message).accessedAddresses r ≤ gas ∧
    message.depth + 1 ≤ STACK_DEPTH_LIMIT ∧
    ∃ caller msg lt child, runChild caller msg lt = .ok child ∧ child.1.error = none ∧
      caller.gas = { m.gas with reservoir := 0, gasLeft := gas - preCostB fork c10 cU -
        (depCallGas fork (askedOfB fork gas c10 cU) (gas - preCostB fork c10 cU)
          (routeCost fork (callSub substate state message).accessedAddresses r)).cost } ∧
      msg.reservoir = m.gas.reservoir ∧
      SendsVia message (upAddr state message) c r (dataB message) msg ∧
      msg.gas = (depCallGas fork (askedOfB fork gas c10 cU) (gas - preCostB fork c10 cU)
        (routeCost fork (callSub substate state message).accessedAddresses r)).subCall ∧
      caller.state = (routeState ((callState state message).recordAccountRead
        (upAddr state message)) r).recordAccountRead message.currentTarget ∧
      caller.substate = routeSub { callSub substate state message with
        accessedAddresses :=
          (callSub substate state message).accessedAddresses.insert (upAddr state message) } r ∧
      (GasMeter.absorb caller.gas child.1.gas true).gasLeft +
          (GasMeter.absorb caller.gas child.1.gas true).reservoir =
        caller.gas.gasLeft + child.1.gas.gasLeft + child.1.gas.reservoir ∧
      126 ≤ (GasMeter.absorb caller.gas child.1.gas true).gasLeft ∧
      s.running = false ∧ s.output = wordBytes (resWord (outMemOf (M2B (addrArg message.data 0)) child.1.output)) ∧
      s.state = (incorporateChild fork caller child.1).state ∧
      s.substate = (incorporateChild fork caller child.1).substate ∧
      s.gas = { GasMeter.absorb caller.gas child.1.gas true with
        gasLeft := (GasMeter.absorb caller.gas child.1.gas true).gasLeft - 126 } := by
  obtain ⟨c, r, hcode, hroute, hw, hgas, hdepth, -⟩ :=
    dep_balanceOf_completeR hfork hsize' hsel hdep start hrun hok
  rw [hc10, hcU] at hgas
  obtain ⟨h4, hv, -⟩ := EndsOk.dispatch hfork hsize' start (endsOk_of_sgm hfork hrun hok)
  have hs10 := slotCost_le c10
  have hG0 : 924 + slotCost c10 + extCost fork cU + 100 +
      routeCost fork (callSub substate state message).accessedAddresses r ≤ gas := hgas
  -- pc 0 to EXTCODESIZE
  obtain ⟨m1, hat1, hg1, hrun1⟩ := fwd_splitS
    (fun g hg => prefixG_balanceOf hfork h4 hsize' hsel hv hdep hc10 hg)
    (by omega) (fun _ _ => rfl) (by omega) start
  obtain ⟨w1, e1⟩ := hrun1 within
  rw [e1] at hrun
  have hext : extendMemory (M2B (addrArg message.data 0)).size
      [((0x60 : U256), (0x24 : U256)), ((0x60 : U256), (0x20 : U256))] = ⟨0, 0⟩ := by
    rw [size_M2B]; decide
  -- EXTCODESIZE to the end
  obtain ⟨caller, msg, lt, chS, hch, he, hcg, m0, mg, hsv, k10, k11, hsum, hT, hr, ho, hst, hss,
      hgs⟩ :=
    dep_call_exactS (message := message) (U := upWord (storageAt state message.currentTarget 10))
      (rest := [0x84, 0x70a08231, upWord (storageAt state message.currentTarget 10), 0,
        addrArg message.data 0, 0x05e7, BitVec.ofNat 256 (selector message.data)])
      (st := readSlot state message.currentTarget 10)
      (ss := accessSlot substate message.currentTarget 10)
      (A := extCost fork cU)
      (R := routeCost fork (callSub substate state message).accessedAddresses r)
      (T := 126) (out := fun ob => wordBytes (resWord (outMemOf (M2B (addrArg message.data 0)) ob)))
      hfork (Or.inr (Or.inl ⟨rfl, rfl⟩)) (by simp) hext hcode hw (Logic.Routes.congr (fun _ => rfl) hroute)
      hdepth (by rw [← hcU]) rfl (by omega) (by decide)
      (fun ob S sb g hg => okTailB (fork := fork) (message := message) (state := S) (substate := sb)
        (U := upWord (storageAt state message.currentTarget 10)) (a := addrArg message.data 0)
        (size_outMemOf (size_M2B _) ob) (mload_outMemOf (size_M2B _) (mload_M2B _) ob)
        (x := BitVec.ofNat 256 (selector message.data)) hg)
      hat1 hrun hok
  have e1 : gas - (896 + slotCost c10) - (extCost fork cU + 25) =
      gas - (921 + slotCost c10 + extCost fork cU) := by omega
  have e2 : gas - (896 + slotCost c10) - (extCost fork cU + 28) = gas - preCostB fork c10 cU := by
    show _ = gas - (924 + slotCost c10 + extCost fork cU); omega
  refine ⟨c, r, hcode, hroute, hw, hgas, hdepth, caller, msg, lt, chS, hch, he, ?_,
    by rw [m0, hg1], ?_, ?_, k10, k11, hsum, hT, hr, ho, hst, hss, hgs⟩
  · rw [hcg, hg1, e1, e2]
  · obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13⟩ := hsv
    exact ⟨d1, d2, d3, d4, d5, d6, by
      have h := data_M2B (addrArg message.data 0); rw [memoryExtend_zero] at h
      rw [d7, show (0x60 : U256).toNat = 96 by simp, show (0x24 : U256).toNat = 36 by simp, h], d8, d9, d10, d11, d12, d13⟩
  · rw [mg, e1, e2]

/-- **Deprecated allowance(a, b) over the EIP-8037 meter, any reservoir, the exact meter after the
CALL and at the end.** See the module doc; the tail is 128 gas. -/
theorem dep_allowance_exactR (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xdd62ed3e)
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0)
    {c10 cU : Bool} (hc10 : coldIn substate message.currentTarget 10 = c10)
    (hcU : decide (upAddr state message ∉ substate.accessedAddresses) = cU)
    {gas : Nat} {m s : Evm fork StateGasMeter}
    (start : At CODE message 0 [] .empty gas state substate (toNat m))
    {within : GasMeter.gasHeld m.gas ≤ bound}
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild m within = .ok s)
    (hok : s.error = none) :
    ∃ c r, state.getCode (state.getAccount (upAddr state message)).codeHash = .ok c ∧
    Routes fork state c r ∧
    BitVec.ofNat 256 c.size ≠ 0 ∧
    preCostAl fork c10 cU + 100 +
      routeCost fork (callSub substate state message).accessedAddresses r ≤ gas ∧
    message.depth + 1 ≤ STACK_DEPTH_LIMIT ∧
    ∃ caller msg lt child, runChild caller msg lt = .ok child ∧ child.1.error = none ∧
      caller.gas = { m.gas with reservoir := 0, gasLeft := gas - preCostAl fork c10 cU -
        (depCallGas fork (askedOfAl fork gas c10 cU) (gas - preCostAl fork c10 cU)
          (routeCost fork (callSub substate state message).accessedAddresses r)).cost } ∧
      msg.reservoir = m.gas.reservoir ∧
      SendsVia message (upAddr state message) c r (dataAl message) msg ∧
      msg.gas = (depCallGas fork (askedOfAl fork gas c10 cU) (gas - preCostAl fork c10 cU)
        (routeCost fork (callSub substate state message).accessedAddresses r)).subCall ∧
      caller.state = (routeState ((callState state message).recordAccountRead
        (upAddr state message)) r).recordAccountRead message.currentTarget ∧
      caller.substate = routeSub { callSub substate state message with
        accessedAddresses :=
          (callSub substate state message).accessedAddresses.insert (upAddr state message) } r ∧
      (GasMeter.absorb caller.gas child.1.gas true).gasLeft +
          (GasMeter.absorb caller.gas child.1.gas true).reservoir =
        caller.gas.gasLeft + child.1.gas.gasLeft + child.1.gas.reservoir ∧
      128 ≤ (GasMeter.absorb caller.gas child.1.gas true).gasLeft ∧
      s.running = false ∧ s.output = wordBytes (resWord (outMemOf (memAl message) child.1.output)) ∧
      s.state = (incorporateChild fork caller child.1).state ∧
      s.substate = (incorporateChild fork caller child.1).substate ∧
      s.gas = { GasMeter.absorb caller.gas child.1.gas true with
        gasLeft := (GasMeter.absorb caller.gas child.1.gas true).gasLeft - 128 } := by
  obtain ⟨c, r, hcode, hroute, hw, hgas, hdepth, -⟩ :=
    dep_allowance_completeR hfork hsize' hsel hdep hc10 hcU start hrun hok
  obtain ⟨h4, hv, -⟩ := EndsOk.dispatch hfork hsize' start (endsOk_of_sgm hfork hrun hok)
  have hs10 := slotCost_le c10
  have hG0 : 1187 + slotCost c10 + extCost fork cU + 100 +
      routeCost fork (callSub substate state message).accessedAddresses r ≤ gas := hgas
  -- pc 0 to EXTCODESIZE
  obtain ⟨m1, hat1, hg1, hrun1⟩ := fwd_splitS
    (fun g hg => prefixG_allowance hfork h4 hsize' hsel hv hdep hc10 hg)
    (by omega) (fun _ _ => rfl) (by omega) start
  obtain ⟨w1, e1⟩ := hrun1 within
  rw [e1] at hrun
  have hext : extendMemory (memAl message).size
      [((0x60 : U256), (0x44 : U256)), ((0x60 : U256), (0x20 : U256))] = ⟨0, 0⟩ := by
    rw [size_M3A]; decide
  -- EXTCODESIZE to the end
  obtain ⟨caller, msg, lt, chS, hch, he, hcg, m0, mg, hsv, k10, k11, hsum, hT, hr, ho, hst, hss,
      hgs⟩ :=
    dep_call_exactS (message := message) (U := upWord (storageAt state message.currentTarget 10))
      (rest := [0xa4, 0xdd62ed3e, upWord (storageAt state message.currentTarget 10), 0,
        addrArg message.data 1, addrArg message.data 0, BitVec.ofNat 256 2132,
        BitVec.ofNat 256 (selector message.data)])
      (st := readSlot state message.currentTarget 10)
      (ss := accessSlot substate message.currentTarget 10)
      (A := extCost fork cU)
      (R := routeCost fork (callSub substate state message).accessedAddresses r)
      (T := 128) (out := fun ob => wordBytes (resWord (outMemOf (memAl message) ob)))
      hfork (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))))) (by simp) hext hcode hw (Logic.Routes.congr (fun _ => rfl) hroute)
      hdepth (by rw [← hcU]) rfl (by omega) (by decide)
      (fun ob S sb g hg => DeprecatedAllowance.okTailA (fork := fork) (message := message) (state := S)
        (substate := sb) (U := upWord (storageAt state message.currentTarget 10)) (a := addrArg message.data 0)
        (b := addrArg message.data 1) (size_outMemOfA (size_M3A _ _) ob)
        (mload_outMemOfA (size_M3A _ _) (mload_M3A _ _) ob)
        (x := BitVec.ofNat 256 (selector message.data)) hg)
      hat1 hrun hok
  have e1 : gas - (1159 + slotCost c10) - (extCost fork cU + 25) =
      gas - (1184 + slotCost c10 + extCost fork cU) := by omega
  have e2 : gas - (1159 + slotCost c10) - (extCost fork cU + 28) = gas - preCostAl fork c10 cU := by
    show _ = gas - (1187 + slotCost c10 + extCost fork cU); omega
  refine ⟨c, r, hcode, hroute, hw, hgas, hdepth, caller, msg, lt, chS, hch, he, ?_,
    by rw [m0, hg1], ?_, ?_, k10, k11, hsum, hT, hr, ho, hst, hss, hgs⟩
  · rw [hcg, hg1, e1, e2]
  · obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13⟩ := hsv
    exact ⟨d1, d2, d3, d4, d5, d6, by
      rw [d7, show (0x60 : U256).toNat = 96 by simp, show (0x44 : U256).toNat = 68 by simp,
        data_M3A], d8, d9, d10, d11, d12, d13⟩
  · rw [mg, e1, e2]

/-- **Deprecated transfer(to, v) over the EIP-8037 meter, any reservoir, the exact meter after the
CALL and at the end.** See the module doc; the tail is 51 gas. -/
theorem dep_transfer_exactR (hfork : .berlin ≤ fork)
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
    {within : GasMeter.gasHeld m.gas ≤ bound}
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild m within = .ok s)
    (hok : s.error = none) :
    ∃ c r, state.getCode (state.getAccount (upAddr state message)).codeHash = .ok c ∧
    Routes fork state c r ∧
    byte20 (storageAt state message.currentTarget 0) = 0 ∧
    (storageAt state message.currentTarget (blackSlot message)).toNat % 256 = 0 ∧
    BitVec.ofNat 256 c.size ≠ 0 ∧
    preCostT fork c0 cB c10 cU + 100 +
      routeCost fork (callSubT substate state message).accessedAddresses r ≤ gas ∧
    message.depth + 1 ≤ STACK_DEPTH_LIMIT ∧
    ∃ caller msg lt child, runChild caller msg lt = .ok child ∧ child.1.error = none ∧
      caller.gas = { m.gas with reservoir := 0, gasLeft := gas - preCostT fork c0 cB c10 cU -
        (depCallGas fork (askedOfT fork gas c0 cB c10 cU) (gas - preCostT fork c0 cB c10 cU)
          (routeCost fork (callSubT substate state message).accessedAddresses r)).cost } ∧
      msg.reservoir = m.gas.reservoir ∧
      SendsVia message (upAddr state message) c r (dataT message) msg ∧
      msg.gas = (depCallGas fork (askedOfT fork gas c0 cB c10 cU) (gas - preCostT fork c0 cB c10 cU)
        (routeCost fork (callSubT substate state message).accessedAddresses r)).subCall ∧
      caller.state = (routeState ((callStateT state message).recordAccountRead
        (upAddr state message)) r).recordAccountRead message.currentTarget ∧
      caller.substate = routeSub { callSubT substate state message with
        accessedAddresses :=
          (callSubT substate state message).accessedAddresses.insert (upAddr state message) } r ∧
      (GasMeter.absorb caller.gas child.1.gas true).gasLeft +
          (GasMeter.absorb caller.gas child.1.gas true).reservoir =
        caller.gas.gasLeft + child.1.gas.gasLeft + child.1.gas.reservoir ∧
      51 ≤ (GasMeter.absorb caller.gas child.1.gas true).gasLeft ∧
      s.running = false ∧ s.output = .empty ∧
      s.state = (incorporateChild fork caller child.1).state ∧
      s.substate = (incorporateChild fork caller child.1).substate ∧
      s.gas = { GasMeter.absorb caller.gas child.1.gas true with
        gasLeft := (GasMeter.absorb caller.gas child.1.gas true).gasLeft - 51 } := by
  obtain ⟨c, r, hcode, hroute, hp, hb, hw, hgas, hdepth, -⟩ :=
    dep_transfer_completeR hfork hsize' hsel hdep hc0 hcB hc10 hcU start hrun hok
  obtain ⟨h4, hv, -⟩ := EndsOk.dispatch hfork hsize' start (endsOk_of_sgm hfork hrun hok)
  have hs0 := slotCost_le c0
  have hsB := slotCost_le cB
  have hs10 := slotCost_le c10
  have hG0 : 1357 + slotCost c0 + slotCost cB + slotCost c10 + extCost fork cU + 100 +
      routeCost fork (callSubT substate state message).accessedAddresses r ≤ gas := hgas
  -- pc 0 to EXTCODESIZE
  obtain ⟨m1, hat1, hg1, hrun1⟩ := fwd_splitS
    (fun g hg => prefixG_transfer hfork h4 hsize' hsel hv hp hb hdep hc0 hcB hc10 hg)
    (by omega) (fun _ _ => rfl) (by omega) start
  obtain ⟨w1, e1⟩ := hrun1 within
  rw [e1] at hrun
  have hext : extendMemory (memT message).size
      [((0x60 : U256), (0x64 : U256)), ((0x60 : U256), (0 : U256))] = ⟨0, 0⟩ := by
    rw [memT, size_W4 (size_MEMK _ _)]; decide
  -- EXTCODESIZE to the end
  obtain ⟨caller, msg, lt, chS, hch, he, hcg, m0, mg, hsv, k10, k11, hsum, hT, hr, ho, hst, hss,
      hgs⟩ :=
    dep_call_exactS (message := message) (U := upWord (storageAt state message.currentTarget 10))
      (rest := [0xc4, 0x6e18980a, upWord (storageAt state message.currentTarget 10),
        wordArg message.data 1, addrArg message.data 0, 0x078a,
        BitVec.ofNat 256 (selector message.data)])
      (st := shortState state message)
      (ss := shortSubstate substate message)
      (A := extCost fork cU)
      (R := routeCost fork (callSubT substate state message).accessedAddresses r)
      (T := 51) (out := fun _ => .empty)
      hfork (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))) (by simp) hext hcode hw (Logic.Routes.congr (fun _ => rfl) hroute)
      hdepth (by rw [← hcU]) rfl (by omega) (by decide)
      (fun ob S sb g hg => okTailT (fork := fork) (message := message) (state := S) (substate := sb) hg)
      hat1 hrun hok
  have e1 : gas - (1329 + slotCost c0 + slotCost cB + slotCost c10) - (extCost fork cU + 25) =
      gas - (1354 + slotCost c0 + slotCost cB + slotCost c10 + extCost fork cU) := by omega
  have e2 : gas - (1329 + slotCost c0 + slotCost cB + slotCost c10) - (extCost fork cU + 28) = gas - preCostT fork c0 cB c10 cU := by
    show _ = gas - (1357 + slotCost c0 + slotCost cB + slotCost c10 + extCost fork cU); omega
  refine ⟨c, r, hcode, hroute, hp, hb, hw, hgas, hdepth, caller, msg, lt, chS, hch, he, ?_,
    by rw [m0, hg1], ?_, ?_, k10, k11, hsum, hT, hr, ho, hst, hss, hgs⟩
  · rw [hcg, hg1, e1, e2]
  · obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13⟩ := hsv
    exact ⟨d1, d2, d3, d4, d5, d6, by
      have h := data_memT message; rw [memoryExtend_zero] at h
      rw [d7, show (0x60 : U256).toNat = 96 by simp, show (0x64 : U256).toNat = 100 by simp, h], d8, d9, d10, d11, d12, d13⟩
  · rw [mg, e1, e2]

/-- **Deprecated approve(s, v) over the EIP-8037 meter, any reservoir, the exact meter after the
CALL and at the end.** See the module doc; the tail is 53 gas. -/
theorem dep_approve_exactR (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x095ea7b3)
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0)
    {c10 cU : Bool} (hc10 : coldIn substate message.currentTarget 10 = c10)
    (hcU : decide (upAddr state message ∉ substate.accessedAddresses) = cU)
    {gas : Nat} {m s : Evm fork StateGasMeter}
    (start : At CODE message 0 [] .empty gas state substate (toNat m))
    {within : GasMeter.gasHeld m.gas ≤ bound}
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild m within = .ok s)
    (hok : s.error = none) :
    ∃ c r, state.getCode (state.getAccount (upAddr state message)).codeHash = .ok c ∧
    Routes fork state c r ∧
    68 ≤ message.data.size ∧
    BitVec.ofNat 256 c.size ≠ 0 ∧
    preCostA fork c10 cU + 100 +
      routeCost fork (callSub substate state message).accessedAddresses r ≤ gas ∧
    message.depth + 1 ≤ STACK_DEPTH_LIMIT ∧
    ∃ caller msg lt child, runChild caller msg lt = .ok child ∧ child.1.error = none ∧
      caller.gas = { m.gas with reservoir := 0, gasLeft := gas - preCostA fork c10 cU -
        (depCallGas fork (askedOfA fork gas c10 cU) (gas - preCostA fork c10 cU)
          (routeCost fork (callSub substate state message).accessedAddresses r)).cost } ∧
      msg.reservoir = m.gas.reservoir ∧
      SendsVia message (upAddr state message) c r (dataA message) msg ∧
      msg.gas = (depCallGas fork (askedOfA fork gas c10 cU) (gas - preCostA fork c10 cU)
        (routeCost fork (callSub substate state message).accessedAddresses r)).subCall ∧
      caller.state = (routeState ((callState state message).recordAccountRead
        (upAddr state message)) r).recordAccountRead message.currentTarget ∧
      caller.substate = routeSub { callSub substate state message with
        accessedAddresses :=
          (callSub substate state message).accessedAddresses.insert (upAddr state message) } r ∧
      (GasMeter.absorb caller.gas child.1.gas true).gasLeft +
          (GasMeter.absorb caller.gas child.1.gas true).reservoir =
        caller.gas.gasLeft + child.1.gas.gasLeft + child.1.gas.reservoir ∧
      53 ≤ (GasMeter.absorb caller.gas child.1.gas true).gasLeft ∧
      s.running = false ∧ s.output = .empty ∧
      s.state = (incorporateChild fork caller child.1).state ∧
      s.substate = (incorporateChild fork caller child.1).substate ∧
      s.gas = { GasMeter.absorb caller.gas child.1.gas true with
        gasLeft := (GasMeter.absorb caller.gas child.1.gas true).gasLeft - 53 } := by
  obtain ⟨c, r, hcode, hroute, hl, hw, hgas, hdepth, -⟩ :=
    dep_approve_completeR hfork hsize' hsel hdep hc10 hcU start hrun hok
  obtain ⟨h4, hv, -⟩ := EndsOk.dispatch hfork hsize' start (endsOk_of_sgm hfork hrun hok)
  have hs10 := slotCost_le c10
  have hG0 : 724 + slotCost c10 + extCost fork cU + 100 +
      routeCost fork (callSub substate state message).accessedAddresses r ≤ gas := hgas
  -- pc 0 to EXTCODESIZE
  obtain ⟨m1, hat1, hg1, hrun1⟩ := fwd_splitS
    (fun g hg => prefixG_approve hfork hl hsize' hsel hv hdep hc10 hg)
    (by omega) (fun _ _ => rfl) (by omega) start
  obtain ⟨w1, e1⟩ := hrun1 within
  rw [e1] at hrun
  have hext : extendMemory (memA message).size
      [((0x60 : U256), (0x64 : U256)), ((0x60 : U256), (0 : U256))] = ⟨0, 0⟩ := by
    rw [memA, size_W4 size_MEM0]; decide
  -- EXTCODESIZE to the end
  obtain ⟨caller, msg, lt, chS, hch, he, hcg, m0, mg, hsv, k10, k11, hsum, hT, hr, ho, hst, hss,
      hgs⟩ :=
    dep_call_exactS (message := message) (U := upWord (storageAt state message.currentTarget 10))
      (rest := [0xc4, 0xaee92d33, upWord (storageAt state message.currentTarget 10), 0x40,
        wordArg message.data 1, addrArg message.data 0, 0x02a2,
        BitVec.ofNat 256 (selector message.data)])
      (st := readSlot state message.currentTarget 10)
      (ss := accessSlot substate message.currentTarget 10)
      (A := extCost fork cU)
      (R := routeCost fork (callSub substate state message).accessedAddresses r)
      (T := 53) (out := fun _ => .empty)
      hfork (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))) (by simp) hext hcode hw (Logic.Routes.congr (fun _ => rfl) hroute)
      hdepth (by rw [← hcU]) rfl (by omega) (by decide)
      (fun ob S sb g hg => okTailAG (fork := fork) (message := message) (state := S) (substate := sb) hg)
      hat1 hrun hok
  have e1 : gas - (696 + slotCost c10) - (extCost fork cU + 25) =
      gas - (721 + slotCost c10 + extCost fork cU) := by omega
  have e2 : gas - (696 + slotCost c10) - (extCost fork cU + 28) = gas - preCostA fork c10 cU := by
    show _ = gas - (724 + slotCost c10 + extCost fork cU); omega
  refine ⟨c, r, hcode, hroute, hl, hw, hgas, hdepth, caller, msg, lt, chS, hch, he, ?_,
    by rw [m0, hg1], ?_, ?_, k10, k11, hsum, hT, hr, ho, hst, hss, hgs⟩
  · rw [hcg, hg1, e1, e2]
  · obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13⟩ := hsv
    exact ⟨d1, d2, d3, d4, d5, d6, by
      have h := data_memA message; rw [memoryExtend_zero] at h
      rw [d7, show (0x60 : U256).toNat = 96 by simp, show (0x64 : U256).toNat = 100 by simp, h], d8, d9, d10, d11, d12, d13⟩
  · rw [mg, e1, e2]

/-- **Deprecated transferFrom(f, t, v) over the EIP-8037 meter, any reservoir, the exact meter after the
CALL and at the end.** See the module doc; the tail is 53 gas. -/
theorem dep_transferFrom_exactR (hfork : .berlin ≤ fork)
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
    {within : GasMeter.gasHeld m.gas ≤ bound}
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild m within = .ok s)
    (hok : s.error = none) :
    ∃ c r, state.getCode (state.getAccount (upAddr state message)).codeHash = .ok c ∧
    Routes fork state c r ∧
    byte20 (storageAt state message.currentTarget 0) = 0 ∧
    (storageAt state message.currentTarget (blackFrom (fromArg message))).toNat % 256 = 0 ∧
    BitVec.ofNat 256 c.size ≠ 0 ∧
    DeprecatedTransferFrom.preCostF fork c0 cB c10 cU + 100 +
      routeCost fork (callSubF substate state message).accessedAddresses r ≤ gas ∧
    message.depth + 1 ≤ STACK_DEPTH_LIMIT ∧
    ∃ caller msg lt child, runChild caller msg lt = .ok child ∧ child.1.error = none ∧
      caller.gas = { m.gas with reservoir := 0, gasLeft := gas - DeprecatedTransferFrom.preCostF fork c0 cB c10 cU -
        (depCallGas fork (askedOfF fork gas c0 cB c10 cU) (gas - DeprecatedTransferFrom.preCostF fork c0 cB c10 cU)
          (routeCost fork (callSubF substate state message).accessedAddresses r)).cost } ∧
      msg.reservoir = m.gas.reservoir ∧
      SendsVia message (upAddr state message) c r (dataF message) msg ∧
      msg.gas = (depCallGas fork (askedOfF fork gas c0 cB c10 cU) (gas - DeprecatedTransferFrom.preCostF fork c0 cB c10 cU)
        (routeCost fork (callSubF substate state message).accessedAddresses r)).subCall ∧
      caller.state = (routeState ((callStateF state message).recordAccountRead
        (upAddr state message)) r).recordAccountRead message.currentTarget ∧
      caller.substate = routeSub { callSubF substate state message with
        accessedAddresses :=
          (callSubF substate state message).accessedAddresses.insert (upAddr state message) } r ∧
      (GasMeter.absorb caller.gas child.1.gas true).gasLeft +
          (GasMeter.absorb caller.gas child.1.gas true).reservoir =
        caller.gas.gasLeft + child.1.gas.gasLeft + child.1.gas.reservoir ∧
      53 ≤ (GasMeter.absorb caller.gas child.1.gas true).gasLeft ∧
      s.running = false ∧ s.output = .empty ∧
      s.state = (incorporateChild fork caller child.1).state ∧
      s.substate = (incorporateChild fork caller child.1).substate ∧
      s.gas = { GasMeter.absorb caller.gas child.1.gas true with
        gasLeft := (GasMeter.absorb caller.gas child.1.gas true).gasLeft - 53 } := by
  obtain ⟨c, r, hcode, hroute, hp, hb, hw, hgas, hdepth, -⟩ :=
    dep_transferFrom_completeR hfork hsize' hsel hdep hc0 hcB hc10 hcU start hrun hok
  obtain ⟨h4, hv, -⟩ := EndsOk.dispatch hfork hsize' start (endsOk_of_sgm hfork hrun hok)
  have hs0 := slotCost_le c0
  have hsB := slotCost_le cB
  have hs10 := slotCost_le c10
  have hG0 : 1093 + slotCost c0 + slotCost cB + slotCost c10 + extCost fork cU + 100 +
      routeCost fork (callSubF substate state message).accessedAddresses r ≤ gas := hgas
  -- pc 0 to EXTCODESIZE
  obtain ⟨m1, hat1, hg1, hrun1⟩ := fwd_splitS
    (fun g hg => prefixG_transferFrom hfork h4 hsize' hsel hv hp hb hdep hc0 hcB hc10 hg)
    (by omega) (fun _ _ => rfl) (by omega) start
  obtain ⟨w1, e1⟩ := hrun1 within
  rw [e1] at hrun
  have hext : extendMemory (memFD message).size
      [((0x60 : U256), (0x84 : U256)), ((0x60 : U256), (0 : U256))] = ⟨0, 0⟩ := by
    rw [memFD, size_W5 (size_memF message)]; decide
  -- EXTCODESIZE to the end
  obtain ⟨caller, msg, lt, chS, hch, he, hcg, m0, mg, hsv, k10, k11, hsum, hT, hr, ho, hst, hss,
      hgs⟩ :=
    dep_call_exactS (message := message) (U := upWord (storageAt state message.currentTarget 10))
      (rest := [0xe4, 0x8b477adb, upWord (storageAt state message.currentTarget 10), valArg message,
        toArg message, fromArg message, 0x0392, BitVec.ofNat 256 (selector message.data)])
      (st := checkState state message)
      (ss := checkSub substate message)
      (A := extCost fork cU)
      (R := routeCost fork (callSubF substate state message).accessedAddresses r)
      (T := 53) (out := fun _ => .empty)
      hfork (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))) (by simp) hext hcode hw (Logic.Routes.congr (fun _ => rfl) hroute)
      hdepth (by rw [← hcU]) rfl (by omega) (by decide)
      (fun ob S sb g hg => okTailF (fork := fork) (message := message) (state := S) (substate := sb) hg)
      hat1 hrun hok
  have e1 : gas - (1065 + slotCost c0 + slotCost cB + slotCost c10) - (extCost fork cU + 25) =
      gas - (1090 + slotCost c0 + slotCost cB + slotCost c10 + extCost fork cU) := by omega
  have e2 : gas - (1065 + slotCost c0 + slotCost cB + slotCost c10) - (extCost fork cU + 28) = gas - DeprecatedTransferFrom.preCostF fork c0 cB c10 cU := by
    show _ = gas - (1093 + slotCost c0 + slotCost cB + slotCost c10 + extCost fork cU); omega
  refine ⟨c, r, hcode, hroute, hp, hb, hw, hgas, hdepth, caller, msg, lt, chS, hch, he, ?_,
    by rw [m0, hg1], ?_, ?_, k10, k11, hsum, hT, hr, ho, hst, hss, hgs⟩
  · rw [hcg, hg1, e1, e2]
  · obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13⟩ := hsv
    exact ⟨d1, d2, d3, d4, d5, d6, by
      have h := data_memFD message; rw [memoryExtend_zero] at h
      rw [d7, show (0x60 : U256).toNat = 96 by simp, show (0x84 : U256).toNat = 132 by simp, h], d8, d9, d10, d11, d12, d13⟩
  · rw [mg, e1, e2]

end UsdtVerify.Complete
