import UsdtVerify.Usdt.Complete.Deprecated.Allowance
import UsdtVerify.Usdt.Complete.Owner
import UsdtVerify.Usdt.Spec.Deprecated.Destroy

/-!
# Completeness of deprecated destroyBlackFunds(address), for any gas and any runner

`prefixG_destroy` (pc 0 to EXTCODESIZE at 4874, over `StepG`) and `dep_destroy_complete`:
every run of a deprecated `destroyBlackFunds(a)` call that ends with no error, with any gas, any
gas bound and ANY message runner:

- the caller is the owner and `a` is blacklisted (the other cases are excluded by
  `Destroy.spec_notOwner` and `Destroy.spec_notListed`);
- the code size at the upgraded address is not 0, the gas covers the path to the CALL and its
  access, the depth is below the limit;
- the runner was called with the forward of `balanceOf(a)` (`SendsVia … (dataB message)`) and
  returned a frame `child` with no error;
- writing `S` for the state after the call (`incorporateChild`) and `d` for the word at 0x60
  after CALL wrote the start of the child's output: the run stopped with empty output in
  `tailState S C a d` (`balances[a] := 0`, then `_totalSupply := T' - d`, unchecked), substate
  `tailSub`, gas exact (`tailCost`); and (round 26) the gas at the return from the call covers
  the stipend bound of the tail (`tailStip`: otherwise an SSTORE of the tail is reached with at
  most 2300 gas left, `DeprecatedDestroy.tailMidD`).

The code found is in the conclusion, as for the other deprecated functions. Named hypotheses:
the coldness flags only. The conclusion also states that the frame is not static and that the
contract has an account in the child's end state (round 19): otherwise the first SSTORE of the
tail is `Stuck` (`DeprecatedDestroy.tailBadD`), so no such run ends with no error. Through round
18 both were hypotheses (`hstatic`, and `hkeep` on the runner).
-/

namespace UsdtVerify.Complete

open EthLib.Base (Fork U256 toAddressMasked)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic hiding HoareG StepG Stuck
open UsdtVerify.Gas
open GasCosts
open Deprecated DeprecatedBalance DeprecatedTransfer DeprecatedDestroy Owner Admin Destroy BlackList
  Transfer TransferOk
  DestroySpec

variable {fork : Fork} {bound : Nat} {runChild : MessageRunner fork Nat bound}
  {message : Message fork} {state : State.TransactionState} {substate : Substate}

/-- From pc 0 to 4874 (EXTCODESIZE of the upgraded address), deprecated `destroyBlackFunds`,
over `StepG` (the prefix of `preCallD`). -/
theorem prefixG_destroy (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xf3bdc228)
    (hv : message.value = 0) (hown : callerWord message = ownerOf state message.currentTarget)
    (hl : (storageAt state message.currentTarget (listSlot (addrArg message.data 0))).toNat % 256 ≠ 0)
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0) {c0 cL c10 : Bool}
    (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hcL : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget
      (listSlot (addrArg message.data 0)) = cL)
    (hc10 : coldIn (preSub substate message) message.currentTarget 10 = c10)
    {gas : Nat} (hg : 1472 + slotCost c0 + slotCost cL + slotCost c10 ≤ gas) :
    HoareG fork (At CODE message 0 [] .empty gas state substate)
      (At CODE message 4874
        [upWord (storageAt state message.currentTarget 10),
          upWord (storageAt state message.currentTarget 10), 0, 0x60, 0x24, 0x60, 0x20, 0x84,
          0x70a08231, upWord (storageAt state message.currentTarget 10), 0,
          addrArg message.data 0, 0x1f48, 0, addrArg message.data 0, 0x09b6,
          BitVec.ofNat 256 (selector message.data)]
        (memD message) (gas - (1472 + slotCost c0 + slotCost cL + slotCost c10))
        (readSlot (preState state message) message.currentTarget 10)
        (accessSlot (preSub substate message) message.currentTarget 10)) := by
  have hU : storageAt (preState state message) message.currentTarget 10 =
      storageAt state message.currentTarget 10 := by
    simp only [preState, storageAt_readSlot]
  refine Triple.seq (toGetter hfork hsize hsize' hsel hv hown hl hc0 hcL (by omega)) ?_
  step depSet hfork (Or.inr ⟨rfl, rfl⟩) (by simp) (by rw [hU]; exact hdep) hc10 (by gas_ok)
  step fwdArgsD (state := preState state message) hfork (by simp only [addrArg, mask_mask])
    (by simp) (size_mapMem size_MEM0 _ _) (ptr_mapMem size_MEM0 mload_MEM0 _ _) (by gas_ok)
  rw [hU]
  exact Gas.reshapeG rfl rfl (by gas_ok)

/-- **`dep_destroy_complete` over `RunC`** (round 39): for any relation `Run` of the child, a `RunC`
from the fresh frame that ends with no error, where `EndsOk` holds (for the dispatcher and the
guards), has the conclusion of `dep_destroy_complete` with `Run caller msg child` in place of the runner. Since round 42 it also gives a frame `after`, the frame after the CALL, with `Tail after`. -/
theorem dep_destroy_completeC {Run : Evm fork Nat → Message fork → Evm fork Nat → Prop} {Tail : Evm fork Nat → Prop}
    (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xf3bdc228)
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0)
    {c0 cL c10 cU : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hcL : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget
      (listSlot (addrArg message.data 0)) = cL)
    (hc10 : coldIn (preSub substate message) message.currentTarget 10 = c10)
    (hcU : decide (upAddr state message ∉ substate.accessedAddresses) = cU)
    {gas : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (hrun : RunC fork Run Tail evm s) (hE : EndsOk fork evm) (hok : s.error = none) :
    ∃ c r, state.getCode (state.getAccount (upAddr state message)).codeHash = .ok c ∧
    Routes fork state c r ∧
    callerWord message = ownerOf state message.currentTarget ∧
    (storageAt state message.currentTarget (listSlot (addrArg message.data 0))).toNat % 256 ≠ 0 ∧
    BitVec.ofNat 256 c.size ≠ 0 ∧
    preCostD fork c0 cL c10 cU + 100 + routeCost fork (callSubD substate state message).accessedAddresses r ≤ gas ∧
    message.depth + 1 ≤ STACK_DEPTH_LIMIT ∧
    ∃ caller msg child, Run caller msg child ∧ child.error = none ∧
      message.isStatic = false ∧ hasAccount child.state message.currentTarget ∧
      SendsVia message (upAddr state message) c r (dataB message) msg ∧
      msg.gas = (depCallGas fork (askedOfD fork gas c0 cL c10 cU) (gas - preCostD fork c0 cL c10 cU)
        (routeCost fork (callSubD substate state message).accessedAddresses r)).subCall ∧
      caller.state = (routeState ((callStateD state message).recordAccountRead
        (upAddr state message)) r).recordAccountRead message.currentTarget ∧
      caller.substate = routeSub { callSubD substate state message with
        accessedAddresses :=
          (callSubD substate state message).accessedAddresses.insert (upAddr state message) } r ∧
      tailCost fork (incorporateChild fork caller child).state message.currentTarget
          (addrArg message.data 0) (resWord (outMemOf (memD message) child.output))
          (coldIn (incorporateChild fork caller child).substate message.currentTarget
            (balSlot message))
          (coldIn (accessSlot (incorporateChild fork caller child).substate
            message.currentTarget (balSlot message)) message.currentTarget 1) ≤
        gas - preCostD fork c0 cL c10 cU - (depCallGas fork (askedOfD fork gas c0 cL c10 cU) (gas - preCostD fork c0 cL c10 cU)
        (routeCost fork (callSubD substate state message).accessedAddresses r)).cost + child.gas ∧
      s.running = false ∧ s.output = .empty ∧
      s.gas = gas - preCostD fork c0 cL c10 cU - (depCallGas fork (askedOfD fork gas c0 cL c10 cU) (gas - preCostD fork c0 cL c10 cU)
        (routeCost fork (callSubD substate state message).accessedAddresses r)).cost + child.gas -
        tailCost fork (incorporateChild fork caller child).state message.currentTarget
          (addrArg message.data 0) (resWord (outMemOf (memD message) child.output))
          (coldIn (incorporateChild fork caller child).substate message.currentTarget
            (balSlot message))
          (coldIn (accessSlot (incorporateChild fork caller child).substate
            message.currentTarget (balSlot message)) message.currentTarget 1) ∧
      s.state = tailState (incorporateChild fork caller child).state message.currentTarget
        (addrArg message.data 0) (resWord (outMemOf (memD message) child.output)) ∧
      s.substate = tailSub fork (incorporateChild fork caller child).substate
        (incorporateChild fork caller child).state message.currentTarget
        (addrArg message.data 0) (resWord (outMemOf (memD message) child.output)) ∧
      tailStip fork (incorporateChild fork caller child).state message.currentTarget
          (addrArg message.data 0)
          (coldIn (incorporateChild fork caller child).substate message.currentTarget
            (balSlot message))
          (coldIn (accessSlot (incorporateChild fork caller child).substate
            message.currentTarget (balSlot message)) message.currentTarget 1) ≤
        gas - preCostD fork c0 cL c10 cU - (depCallGas fork (askedOfD fork gas c0 cL c10 cU) (gas - preCostD fork c0 cL c10 cU)
        (routeCost fork (callSubD substate state message).accessedAddresses r)).cost + child.gas ∧
      ∃ after, Tail after := by
  obtain ⟨h4, hv, -⟩ := EndsOk.dispatch hfork hsize' start hE
  by_cases hown : callerWord message ≠ ownerOf state message.currentTarget
  · exact (hE.no_ok (fun g hg => Destroy.spec_notOwner hfork h4 hsize' hsel hv hown hc0 hg)
      (fun _ e h => halted_true_error e h) start).elim
  have hown := not_ne hown
  by_cases hl : (storageAt state message.currentTarget (listSlot (addrArg message.data 0))).toNat %
      256 = 0
  · exact (hE.no_ok (fun g hg => Destroy.spec_notListed hfork h4 hsize' hsel hv hown hl hc0 hcL hg)
      (fun _ e h => halted_true_error e h) start).elim
  obtain ⟨hg0, z, hz, hrunz⟩ := ok_splitCA (Nat.le_refl _)
    (fun g hg => prefixG_destroy hfork h4 hsize' hsel hv hown hl hdep hc0 hcL hc10 hg)
    (by simp only [slotCost]; (repeat' split) <;> omega) (fun _ _ => rfl) start hrun hok
  obtain ⟨c, hcode⟩ := fromExt_foundC (by decide) hz hrunz hok
  obtain ⟨r, hroute, hw, hgc, hdepth, hCE⟩ := fromExtC (U := upWord (storageAt state message.currentTarget 10))
    (rest := [0x84, 0x70a08231, upWord (storageAt state message.currentTarget 10), 0,
      addrArg message.data 0, 0x1f48, 0, addrArg message.data 0, 0x09b6,
      BitVec.ofNat 256 (selector message.data)])
    (st := readSlot (preState state message) message.currentTarget 10)
    (ss := accessSlot (preSub substate message) message.currentTarget 10)
    hfork (Or.inr (Or.inl ⟨rfl, rfl⟩)) (by simp) hcode hz hrunz hok
  have hB := size_memD message
  have hext : extendMemory (memD message).size
      [((0x60 : U256), (0x24 : U256)), ((0x60 : U256), (0x20 : U256))] = ⟨0, 0⟩ := by
    rw [hB]; decide
  have hcU' : decide (toAddressMasked (upWord (storageAt state message.currentTarget 10)) ∉
      (accessSlot (preSub substate message) message.currentTarget 10).accessedAddresses) =
      decide (upAddr state message ∉ substate.accessedAddresses) := rfl
  unfold CallEndC at hCE
  simp only [routeCost_insert_insert] at hCE
  have hRe : routeCost fork ((accessSlot (preSub substate message) message.currentTarget 10).accessedAddresses.insert
      (toAddressMasked (upWord (storageAt state message.currentTarget 10)))) r =
      routeCost fork (callSubD substate state message).accessedAddresses r := rfl
  rw [hRe] at hgc hCE
  refine ⟨c, r, hcode, Logic.Routes.congr (fun _ => rfl) hroute, ?_⟩
  generalize hR : routeCost fork (callSubD substate state message).accessedAddresses r = R at hgc hCE ⊢
  rw [hcU', hcU] at hgc hCE
  rw [hext] at hgc
  simp only [extCost] at hgc hg0
  have e1 : gas - (1472 + slotCost c0 + slotCost cL + slotCost c10) - (extCost fork cU + 25) =
      gas - (1497 + slotCost c0 + slotCost cL + slotCost c10 + extCost fork cU) := by
    simp only [extCost]; omega
  have e2 : gas - (1472 + slotCost c0 + slotCost cL + slotCost c10) - (extCost fork cU + 28) =
      gas - preCostD fork c0 cL c10 cU := by
    simp only [preCostD, extCost]; omega
  rw [e1, e2] at hCE
  obtain ⟨caller, msg, child, hch, hcs, hcss, hmg, hmc, hmt, hmtg, hmca, hmcode, hmdp, hmd, hmv,
    hmdep, hmst, after, hat, hT, hruna⟩ := hCE
  rw [hext] at hmg hmd hat
  simp only [accCost_false] at hmg hat
  refine ⟨hown, hl, hw, by simp only [preCostD, extCost]; omega, hdepth, ?_⟩
  have hfwd : SendsVia message (upAddr state message) c r (dataB message) msg := by
    refine ⟨hmc, hmt, hmtg, hmca, hmcode, hmdp, ?_, hmv, hmdep, hmst⟩
    rw [hmd, memoryExtend_zero]; exact data_memD message
  by_cases he : child.error = none
  · simp only [he, Option.isNone_none, ↓reduceIte] at hat
    by_cases hgood : ¬(message.isStatic = false ∧
        hasAccount (incorporateChild fork caller child).state message.currentTarget)
    · exact (no_ok_stuckE (fun g hg => tailBadD (x := BitVec.ofNat 256 (selector message.data))
        (bad_of_not hgood) (size_outMemOf hB child.output)
        (mload_outMemOf hB (by rw [memoryExtend_zero]; exact ptr_memD message) child.output) hg)
        hat hruna hok).elim
    obtain ⟨hstatic, hacc⟩ := Classical.not_not.mp hgood
    obtain ⟨hcost, hr, ho, hgs, hst, hss⟩ := ok_exact2E
      (fun g h1 _ => tailD (fork := fork) (message := message)
        hfork (mkey_addrArg message.data 0) hstatic hacc
        (size_outMemOf hB child.output)
        (mload_outMemOf hB (by rw [memoryExtend_zero]; exact ptr_memD message) child.output)
        (x := BitVec.ofNat 256 (selector message.data)) rfl rfl (gas := g) h1) hat hruna hok
    have hstip := Nat.le_of_not_lt fun hlt => no_ok_stuck_atE
      (tailMidD (x := BitVec.ofNat 256 (selector message.data)) hfork (mkey_addrArg message.data 0)
        hstatic hacc (size_outMemOf hB child.output)
        (mload_outMemOf hB (by rw [memoryExtend_zero]; exact ptr_memD message) child.output)
        rfl rfl hcost hlt) hat hruna hok
    refine ⟨caller, msg, child, hch, he, hstatic, by rwa [state_incorporateChild] at hacc,
      hfwd, hmg, hcs, hcss, ?_, hr, ho, ?_, hst, hss, ?_, after, hT⟩
    · simp only [Nat.add_zero, balSlot] at hcost ⊢
      exact hcost
    · rw [hgs]
      simp only [Nat.add_zero, balSlot]
    · simp only [Nat.add_zero, balSlot] at hstip ⊢
      exact hstip
  · have hz : child.error.isNone = false := by
      cases h : child.error
      · exact absurd h he
      · rfl
    simp only [hz, Bool.false_eq_true, ↓reduceIte] at hat
    exact (no_okE (fun g hg => failTail hfork (Or.inr (Or.inl rfl)) (by simp) hg)
      (fun g e h => by rw [h.2.1]; simp) hat hruna hok).elim


/-- Every successful deprecated `destroyBlackFunds(a)` run, for any gas and any runner: the
owner's call, not static, `a` blacklisted, the forward of `balanceOf(a)` answered with no error
(and the contract has an account in the child's end state), then the two writes over the state the call left and the log; output, gas, state and substate
exact; and (round 26) the gas at the return from the call is at least `tailStip`. -/
theorem dep_destroy_complete (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xf3bdc228)
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0)
    {c0 cL c10 cU : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hcL : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget
      (listSlot (addrArg message.data 0)) = cL)
    (hc10 : coldIn (preSub substate message) message.currentTarget 10 = c10)
    (hcU : decide (upAddr state message ∉ substate.accessedAddresses) = cU)
    {gas : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) :
    ∃ c r, state.getCode (state.getAccount (upAddr state message)).codeHash = .ok c ∧
    Routes fork state c r ∧
    callerWord message = ownerOf state message.currentTarget ∧
    (storageAt state message.currentTarget (listSlot (addrArg message.data 0))).toNat % 256 ≠ 0 ∧
    BitVec.ofNat 256 c.size ≠ 0 ∧
    preCostD fork c0 cL c10 cU + 100 + routeCost fork (callSubD substate state message).accessedAddresses r ≤ gas ∧
    message.depth + 1 ≤ STACK_DEPTH_LIMIT ∧
    ∃ caller msg lt child, runChild caller msg lt = .ok child ∧ child.1.error = none ∧
      message.isStatic = false ∧ hasAccount child.1.state message.currentTarget ∧
      SendsVia message (upAddr state message) c r (dataB message) msg ∧
      msg.gas = (depCallGas fork (askedOfD fork gas c0 cL c10 cU) (gas - preCostD fork c0 cL c10 cU)
        (routeCost fork (callSubD substate state message).accessedAddresses r)).subCall ∧
      caller.state = (routeState ((callStateD state message).recordAccountRead
        (upAddr state message)) r).recordAccountRead message.currentTarget ∧
      caller.substate = routeSub { callSubD substate state message with
        accessedAddresses :=
          (callSubD substate state message).accessedAddresses.insert (upAddr state message) } r ∧
      tailCost fork (incorporateChild fork caller child.1).state message.currentTarget
          (addrArg message.data 0) (resWord (outMemOf (memD message) child.1.output))
          (coldIn (incorporateChild fork caller child.1).substate message.currentTarget
            (balSlot message))
          (coldIn (accessSlot (incorporateChild fork caller child.1).substate
            message.currentTarget (balSlot message)) message.currentTarget 1) ≤
        gas - preCostD fork c0 cL c10 cU - (depCallGas fork (askedOfD fork gas c0 cL c10 cU) (gas - preCostD fork c0 cL c10 cU)
        (routeCost fork (callSubD substate state message).accessedAddresses r)).cost + child.1.gas ∧
      s.running = false ∧ s.output = .empty ∧
      s.gas = gas - preCostD fork c0 cL c10 cU - (depCallGas fork (askedOfD fork gas c0 cL c10 cU) (gas - preCostD fork c0 cL c10 cU)
        (routeCost fork (callSubD substate state message).accessedAddresses r)).cost + child.1.gas -
        tailCost fork (incorporateChild fork caller child.1).state message.currentTarget
          (addrArg message.data 0) (resWord (outMemOf (memD message) child.1.output))
          (coldIn (incorporateChild fork caller child.1).substate message.currentTarget
            (balSlot message))
          (coldIn (accessSlot (incorporateChild fork caller child.1).substate
            message.currentTarget (balSlot message)) message.currentTarget 1) ∧
      s.state = tailState (incorporateChild fork caller child.1).state message.currentTarget
        (addrArg message.data 0) (resWord (outMemOf (memD message) child.1.output)) ∧
      s.substate = tailSub fork (incorporateChild fork caller child.1).substate
        (incorporateChild fork caller child.1).state message.currentTarget
        (addrArg message.data 0) (resWord (outMemOf (memD message) child.1.output)) ∧
      tailStip fork (incorporateChild fork caller child.1).state message.currentTarget
          (addrArg message.data 0)
          (coldIn (incorporateChild fork caller child.1).substate message.currentTarget
            (balSlot message))
          (coldIn (accessSlot (incorporateChild fork caller child.1).substate
            message.currentTarget (balSlot message)) message.currentTarget 1) ≤
        gas - preCostD fork c0 cL c10 cU - (depCallGas fork (askedOfD fork gas c0 cL c10 cU) (gas - preCostD fork c0 cL c10 cU)
        (routeCost fork (callSubD substate state message).accessedAddresses r)).cost + child.1.gas := by
  obtain ⟨c, r, h1, h2, h3, h4, h5, h6, h7, caller, msg, child, ⟨lt, hle, hch⟩, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, -⟩ :=
    dep_destroy_completeC hfork hsize' hsel hdep hc0 hcL hc10 hcU start (RunC.of_runFrame hrun)
      (EndsOk.of_runFrame hrun hok) hok
  exact ⟨c, r, h1, h2, h3, h4, h5, h6, h7, caller, msg, lt, ⟨child, hle⟩, hch, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14⟩

end UsdtVerify.Complete
