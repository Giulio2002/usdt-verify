import UsdtVerify.Usdt.Complete.Deprecated.CallS
import UsdtVerify.Usdt.Complete.Deprecated.MeterR
import UsdtVerify.Usdt.Refill.DestroyDepS

/-!
# Deprecated destroyBlackFunds over the EIP-8037 meter: the exact gas after the CALL (round 44)

`dep_destroy_completeR` (round 42) bounds the gas of deprecated destroyBlackFunds over
`StateGasMeter` from below, since the two writes after the CALL may refill. Here the run is
followed over `StateGasMeter` itself: from pc 0 to the CALL forward (`fwd_splitS`, `fromExtS`),
through the runner and the resume (`runFrame_childS`), and the tail exactly (`tailD_sgm`).

- `resumeD`: the frame after the CALL is the frame at 4892 of the forward of destroyBlackFunds,
  with the answer of the child on the stack, the start of its output written at 0x60, its state,
  the substate of the resume and the execution gas left of the frame.
- `dep_destroy_exactR`: from Berlin, from a frame `m` with ANY reservoir whose `toNat` is the
  fresh frame of `CODE` with selector 0xf3bdc228, deprecated, for any gas bound and message
  runner over `StateGasMeter`: every run that ends with no error went through the CALL with a
  caller whose meter is the meter of `m` with reservoir 0 and the gas before the CALL less its
  price, and a child with no error. The meter after the CALL is `GasMeter.absorb` of the
  caller's and the child's meters for a child that succeeded, and its execution gas left plus its
  reservoir is the caller's execution gas left plus the child's execution gas left and reservoir.
  From that meter the two writes of the tail meet `wOk`, 1364 gas is left after the second, and
  the end is `tailState` and `tailSub` with the meter after the second write less 1364 execution
  gas. So the gas at the end is exact as a function of the meter the child ends with (which the
  runner fixes), refills included, and the split between execution gas and reservoir is stated.
-/

namespace UsdtVerify.Complete

open EthLib.Base (Fork U256 toAddressMasked Address)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open UsdtVerify.Gas
open UsdtVerify.Meter
open GasCosts
open Deprecated DeprecatedBalance DeprecatedDestroy DestroySpec Owner BlackList Transfer TransferOk

variable {fork : Fork} {message : Message fork}

/-- The frame after the CALL of the forward at 4891 over `StateGasMeter`: the `toNat` of the
resumed frame is the frame at 4892 with the answer of the child, the start of its output at 0x60,
its state and the substate of the resume, with its execution gas left. -/
theorem resumeD {caller ch y : Evm fork StateGasMeter} {rest : List U256} {M : ByteArray}
    (hlen : rest.length ≤ 10)
    (c1 : caller.code = CODE) (c2 : caller.validJumpDestinations = validJumpDestinations CODE)
    (c3 : caller.message = message) (c4 : caller.pc = 4891) (c5 : caller.stack.val = rest)
    (c6 : caller.memory = M) (c8 : caller.running = true) (c9 : caller.error = none)
    (co : caller.output = .empty)
    (hy : resumeCall fork caller 0 0x60 0x20 ch = .ok y) :
    At CODE message 4892 ((if ch.error.isNone then 1 else 0) :: rest)
      (outMemOf M ch.output) y.gas.gasLeft (incorporateChild fork caller ch).state
      (incorporateChild fork caller ch).substate (toNat y) := by
  obtain ⟨y', hy', hty, -, -⟩ := resumeCall_sgm hy
  have hlenN : (toNat caller).stack.val.length < STACK_LIMIT := by
    show caller.stack.val.length < STACK_LIMIT
    rw [c5]; simp only [STACK_LIMIT]; omega
  obtain ⟨after, ha, a1, a2, a3, a4, a5, a6, -, a8, a9, ao, a10, a11, -⟩ :=
    resumeCall_eq (child := toNat ch) (o := 0x60) (osz := 0x20) hlenN
  rw [hy'] at ha
  cases ha
  obtain ⟨i1, i2⟩ := incorporateChild_toNat caller ch (toNat ch) rfl rfl rfl rfl
  rw [hty]
  refine ⟨a1.trans c1, a2.trans c2, a3.trans c3, by rw [a4]; exact congrArg (· + 1) c4,
    by rw [a5]; exact congrArg _ c5, ?_, rfl, a8.trans c8, a9.trans c9, ao.trans co,
    a10.trans i1, a11.trans i2⟩
  rw [a6]
  show memoryWrite caller.memory _ _ = _
  rw [c6, outMemOf, memoryExtend_zero]
  rfl

/-- **Deprecated destroyBlackFunds(a) over the EIP-8037 meter, any reservoir, the exact gas after
the CALL.** See the module doc. The hypotheses are those of `dep_destroy_completeR`. -/
theorem dep_destroy_exactR (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xf3bdc228)
    {state : State.TransactionState} {substate : Substate}
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0)
    {c0 cL c10 cU : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hcL : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget
      (listSlot (addrArg message.data 0)) = cL)
    (hc10 : coldIn (preSub substate message) message.currentTarget 10 = c10)
    (hcU : decide (upAddr state message ∉ substate.accessedAddresses) = cU)
    {gas bound : Nat} {runChild : MessageRunner fork StateGasMeter bound}
    {m s : Evm fork StateGasMeter}
    (start : At CODE message 0 [] .empty gas state substate (toNat m))
    {within : GasMeter.gasHeld m.gas ≤ bound}
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild m within = .ok s)
    (hok : s.error = none) :
    ∃ c r, state.getCode (state.getAccount (upAddr state message)).codeHash = .ok c ∧
    Routes fork state c r ∧
    callerWord message = ownerOf state message.currentTarget ∧
    (storageAt state message.currentTarget (listSlot (addrArg message.data 0))).toNat % 256 ≠ 0 ∧
    BitVec.ofNat 256 c.size ≠ 0 ∧
    preCostD fork c0 cL c10 cU + 100 +
      routeCost fork (callSubD substate state message).accessedAddresses r ≤ gas ∧
    message.depth + 1 ≤ STACK_DEPTH_LIMIT ∧ message.isStatic = false ∧
    ∃ caller msg lt child, runChild caller msg lt = .ok child ∧ child.1.error = none ∧
      caller.gas = { m.gas with reservoir := 0, gasLeft := gas - preCostD fork c0 cL c10 cU -
        (depCallGas fork (askedOfD fork gas c0 cL c10 cU) (gas - preCostD fork c0 cL c10 cU)
          (routeCost fork (callSubD substate state message).accessedAddresses r)).cost } ∧
      msg.reservoir = m.gas.reservoir ∧
      SendsVia message (upAddr state message) c r (dataB message) msg ∧
      msg.gas = (depCallGas fork (askedOfD fork gas c0 cL c10 cU)
        (gas - preCostD fork c0 cL c10 cU)
        (routeCost fork (callSubD substate state message).accessedAddresses r)).subCall ∧
      caller.state = (routeState ((callStateD state message).recordAccountRead
        (upAddr state message)) r).recordAccountRead message.currentTarget ∧
      caller.substate = routeSub { callSubD substate state message with
        accessedAddresses :=
          (callSubD substate state message).accessedAddresses.insert (upAddr state message) } r ∧
      hasAccount (incorporateChild fork caller child.1).state message.currentTarget ∧
      (GasMeter.absorb caller.gas child.1.gas true).gasLeft +
          (GasMeter.absorb caller.gas child.1.gas true).reservoir =
        caller.gas.gasLeft + child.1.gas.gasLeft + child.1.gas.reservoir ∧
      wOk fork (GasMeter.absorb caller.gas child.1.gas true) 184
          (originalAt (incorporateChild fork caller child.1).state message.currentTarget
            (balSlot message))
          (storageAt (incorporateChild fork caller child.1).state message.currentTarget
            (balSlot message)) 0
          (coldIn (incorporateChild fork caller child.1).substate message.currentTarget
            (balSlot message)) ∧
      wOk fork (tailDM1 fork (GasMeter.absorb caller.gas child.1.gas true)
            (incorporateChild fork caller child.1).state message.currentTarget
            (addrArg message.data 0)
            (coldIn (incorporateChild fork caller child.1).substate message.currentTarget
              (balSlot message)))
          (33 + slotCost (coldIn (accessSlot (incorporateChild fork caller child.1).substate
            message.currentTarget (balSlot message)) message.currentTarget 1))
          (originalAt (incorporateChild fork caller child.1).state message.currentTarget 1)
          (storageAt (writeSlot (incorporateChild fork caller child.1).state
            message.currentTarget (balSlot message) 0) message.currentTarget 1)
          (sub (storageAt (writeSlot (incorporateChild fork caller child.1).state
            message.currentTarget (balSlot message) 0) message.currentTarget 1)
            (resWord (outMemOf (memD message) child.1.output))) false ∧
      1364 ≤ (tailDM2 fork (GasMeter.absorb caller.gas child.1.gas true)
          (incorporateChild fork caller child.1).state message.currentTarget
          (addrArg message.data 0) (resWord (outMemOf (memD message) child.1.output))
          (coldIn (incorporateChild fork caller child.1).substate message.currentTarget
            (balSlot message))
          (coldIn (accessSlot (incorporateChild fork caller child.1).substate
            message.currentTarget (balSlot message)) message.currentTarget 1)).gasLeft ∧
      s.running = false ∧ s.output = .empty ∧
      s.state = tailState (incorporateChild fork caller child.1).state message.currentTarget
        (addrArg message.data 0) (resWord (outMemOf (memD message) child.1.output)) ∧
      s.substate = tailSub fork (incorporateChild fork caller child.1).substate
        (incorporateChild fork caller child.1).state message.currentTarget
        (addrArg message.data 0) (resWord (outMemOf (memD message) child.1.output)) ∧
      s.gas = { tailDM2 fork (GasMeter.absorb caller.gas child.1.gas true)
          (incorporateChild fork caller child.1).state message.currentTarget
          (addrArg message.data 0) (resWord (outMemOf (memD message) child.1.output))
          (coldIn (incorporateChild fork caller child.1).substate message.currentTarget
            (balSlot message))
          (coldIn (accessSlot (incorporateChild fork caller child.1).substate
            message.currentTarget (balSlot message)) message.currentTarget 1) with
        gasLeft := (tailDM2 fork (GasMeter.absorb caller.gas child.1.gas true)
          (incorporateChild fork caller child.1).state message.currentTarget
          (addrArg message.data 0) (resWord (outMemOf (memD message) child.1.output))
          (coldIn (incorporateChild fork caller child.1).substate message.currentTarget
            (balSlot message))
          (coldIn (accessSlot (incorporateChild fork caller child.1).substate
            message.currentTarget (balSlot message)) message.currentTarget 1)).gasLeft - 1364 } := by
  obtain ⟨c, r, hcode, hroute, howner, hlisted, hw, hgas, hdepth, -, -, -, -, -, -, -, -, hstatic,
    -⟩ :=
    dep_destroy_completeR hfork hsize' hsel hdep hc0 hcL hc10 hcU start hrun hok
  obtain ⟨h4, hv, -⟩ := EndsOk.dispatch hfork hsize' start (endsOk_of_sgm hfork hrun hok)
  have hs0 := slotCost_le c0
  have hsL := slotCost_le cL
  have hs10 := slotCost_le c10
  have hpre : preCostD fork c0 cL c10 cU =
      1500 + slotCost c0 + slotCost cL + slotCost c10 + extCost fork cU := rfl
  -- pc 0 to EXTCODESIZE
  obtain ⟨m1, hat1, hg1, hrun1⟩ := fwd_splitS
    (fun g hg => prefixG_destroy hfork h4 hsize' hsel hv howner hlisted hdep hc0 hcL hc10 hg)
    (by omega) (fun _ _ => rfl) (by omega) start
  -- EXTCODESIZE to the CALL
  have hM : extendMemory (memD message).size
      [((0x60 : U256), (0x24 : U256)), ((0x60 : U256), (0x20 : U256))] = ⟨0, 0⟩ := by
    rw [size_memD]; decide
  have hcU' : decide (toAddressMasked (upWord (storageAt state message.currentTarget 10)) ∉
      (accessSlot (preSub substate message) message.currentTarget 10).accessedAddresses) = cU :=
    hcU
  obtain ⟨mC, caller, msg, hgC, hrC, hrunC, hstepC, k1, k2, k3, k4, k5, k6, k7, k8, k9, ko, k10,
      k11, m0, mg, mcl, mct, mtg, mca, mcode, mdp, md, mv, mdep, mst, mbe, mte, msh⟩ :=
    fromExtS (message := message) (U := upWord (storageAt state message.currentTarget 10))
      (rest := [0x84, 0x70a08231, upWord (storageAt state message.currentTarget 10), 0,
        addrArg message.data 0, 0x1f48, 0, addrArg message.data 0, 0x09b6,
        BitVec.ofNat 256 (selector message.data)])
      (st := readSlot (preState state message) message.currentTarget 10)
      (ss := accessSlot (preSub substate message) message.currentTarget 10)
      (A := extCost fork cU)
      (R := routeCost fork (callSubD substate state message).accessedAddresses r)
      hfork (by simp) hM hcode hw (routes_congr (fun _ => rfl) hroute)
      hdepth (by rw [hcU']) rfl (by omega) hat1
  -- through the runner and the resume
  obtain ⟨w1, e1⟩ := hrun1 within
  obtain ⟨wC, eC⟩ := hrunC w1
  rw [e1, eC] at hrun
  obtain ⟨lt, chS, y, hch, hy, wy, hrunY⟩ := runFrame_childS hrC hstepC hrun hok
  have hat := resumeD (by simp) k1 k2 k3 k4 k5 k6 k8 k9 ko hy
  obtain ⟨G, hEnds⟩ := Shadow.shadow_ends hfork hrunY hok
  have hatS := at_sh hat (Shadow.budget y)
  -- the child ended with no error
  have he : chS.1.error = none := by
    refine Classical.byContradiction fun hne => ?_
    have hz : chS.1.error.isNone = false := by
      cases h : chS.1.error
      · exact absurd h hne
      · rfl
    rw [hz] at hatS
    exact no_okE (fun g hg => failTail hfork (Or.inr (Or.inl rfl)) (by simp) hg)
      (fun g e h => by rw [h.2.1]; simp) hatS hEnds hok
  simp only [he, Option.isNone_none, ↓reduceIte] at hat hatS
  have hB := size_memD message
  -- the contract has an account after the call
  have hacc : hasAccount (incorporateChild fork caller chS.1).state message.currentTarget := by
    refine Classical.byContradiction fun hna => ?_
    exact no_ok_stuckE (fun g hg => tailBadD (x := BitVec.ofNat 256 (selector message.data))
      (.inr hna) (size_outMemOf hB chS.1.output)
      (mload_outMemOf hB (by rw [memoryExtend_zero]; exact ptr_memD message) chS.1.output) hg)
      hatS hEnds hok
  -- the meter after the CALL
  have hlenC : caller.stack.val.length < STACK_LIMIT := by rw [k5]; simp [STACK_LIMIT]
  obtain ⟨y2, hy2, -, -, -, -, -, -, hgy, -⟩ := resumeCall_okS (o := 0x60) (osz := 0x20) hlenC he
  rw [hy] at hy2
  cases hy2
  -- the tail
  obtain ⟨hiff, hend⟩ := tailD_sgm hfork (mkey_addrArg message.data 0) hstatic hacc
    (size_outMemOf hB chS.1.output)
    (mload_outMemOf hB (by rw [memoryExtend_zero]; exact ptr_memD message) chS.1.output) rfl rfl
    hat (runChild := runChild) wy
  have hokT := hiff.mp ⟨s, hrunY, hok⟩
  obtain ⟨t1, t2, t3, t4, t5⟩ := hend s hrunY hok
  rw [hgy] at hokT t5
  have e1 : gas - (1472 + slotCost c0 + slotCost cL + slotCost c10) - (extCost fork cU + 25) =
      gas - (1497 + slotCost c0 + slotCost cL + slotCost c10 + extCost fork cU) := by omega
  have e2 : gas - (1472 + slotCost c0 + slotCost cL + slotCost c10) - (extCost fork cU + 28) =
      gas - preCostD fork c0 cL c10 cU := by rw [hpre]; omega
  have hcg : caller.gas = { m.gas with reservoir := 0, gasLeft := gas - preCostD fork c0 cL c10 cU -
      (depCallGas fork (askedOfD fork gas c0 cL c10 cU) (gas - preCostD fork c0 cL c10 cU)
        (routeCost fork (callSubD substate state message).accessedAddresses r)).cost } := by
    rw [k7, hg1, e1, e2]
  refine ⟨c, r, hcode, hroute, howner, hlisted, hw, hgas, hdepth, hstatic, caller, msg, lt, chS,
    hch, he, hcg, by rw [m0, hg1], ⟨mcl, mct, mtg, mca, mcode, mdp, ?_, mv, mdep, mst, mbe, mte,
    msh⟩, ?_, k10, k11, hacc, ?_, hokT.1, hokT.2.1, hokT.2.2, t1, t2, t3, t4, t5⟩
  · rw [md]; exact data_memD message
  · rw [mg, e1, e2]
  · have hr0 : caller.gas.reservoir = 0 := by rw [hcg]
    rw [absorb_sum, hr0, Nat.add_zero]

end UsdtVerify.Complete
