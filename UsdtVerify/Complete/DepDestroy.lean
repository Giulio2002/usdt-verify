import UsdtVerify.Complete.DepAllowance
import UsdtVerify.Complete.Owner
import UsdtVerify.Functions.DeprecatedDestroy

/-!
# Completeness of deprecated destroyBlackFunds(address), for any gas and any runner

`prefixG_destroy` (pc 0 to EXTCODESIZE at 4874, over `StepG`) and `dep_destroy_complete`:
every run of a deprecated `destroyBlackFunds(a)` call that ends with no error, with any gas, any
gas bound and ANY message runner:

- the caller is the owner and `a` is blacklisted (the other cases are excluded by
  `Destroy.spec_notOwner` and `Destroy.spec_notListed`);
- the code size at the upgraded address is not 0, the gas covers the path to the CALL and its
  access, the depth is below the limit;
- the runner was called with the forward of `balanceOf(a)` (`Sends … (dataB message)`) and
  returned a frame `child` with no error;
- writing `S` for the state after the call (`incorporateChild`) and `d` for the word at 0x60
  after CALL wrote the start of the child's output: the run stopped with empty output in
  `tailState S C a d` (`balances[a] := 0`, then `_totalSupply := T' - d`, unchecked), substate
  `tailSub`, gas exact (`tailCost`).

Named hypotheses: `hstatic` (the frame is not static), `hcode`, `hdel` (as for the other
deprecated functions), the coldness flags, and `hkeep`, a hypothesis on the runner: when it ends
the forwarded message with no error, the contract still has an account in the child's state (the
SSTOREs of the tail need it; the case without an account is not covered).
-/

namespace UsdtVerify.Complete

open EthLib.Base (Fork U256 toAddressMasked)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
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

/-- Every successful deprecated `destroyBlackFunds(a)` run, for any gas and any runner, under
`hkeep`: the owner's call, `a` blacklisted, the forward of `balanceOf(a)` answered with no error,
then the two writes over the state the call left and the log; output, gas, state and substate
exact. -/
theorem dep_destroy_complete (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    (hstatic : message.isStatic = false)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xf3bdc228)
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0) {c : ByteArray}
    (hcode : state.getCode (state.getAccount (upAddr state message)).codeHash = .ok c)
    (hdel : .pectra ≤ fork → delegatedAddress c = none)
    {c0 cL c10 cU : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hcL : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget
      (listSlot (addrArg message.data 0)) = cL)
    (hc10 : coldIn (preSub substate message) message.currentTarget 10 = c10)
    (hcU : decide (upAddr state message ∉ substate.accessedAddresses) = cU)
    (hkeep : ∀ caller msg lt child, runChild caller msg lt = .ok child →
      Sends message (upAddr state message) c (dataB message) msg → child.1.error = none →
        hasAccount child.1.state message.currentTarget)
    {gas : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) :
    callerWord message = ownerOf state message.currentTarget ∧
    (storageAt state message.currentTarget (listSlot (addrArg message.data 0))).toNat % 256 ≠ 0 ∧
    BitVec.ofNat 256 c.size ≠ 0 ∧
    preCostD c0 cL c10 cU + 100 ≤ gas ∧
    message.depth + 1 ≤ STACK_DEPTH_LIMIT ∧
    ∃ caller msg lt child, runChild caller msg lt = .ok child ∧ child.1.error = none ∧
      Sends message (upAddr state message) c (dataB message) msg ∧
      msg.gas = (callGasD fork gas c0 cL c10 cU).subCall ∧
      caller.state = ((callStateD state message).recordAccountRead
        (upAddr state message)).recordAccountRead message.currentTarget ∧
      caller.substate = { callSubD substate state message with
        accessedAddresses :=
          (callSubD substate state message).accessedAddresses.insert (upAddr state message) } ∧
      tailCost fork (incorporateChild fork caller child.1).state message.currentTarget
          (addrArg message.data 0) (resWord (outMemOf (memD message) child.1.output))
          (coldIn (incorporateChild fork caller child.1).substate message.currentTarget
            (balSlot message))
          (coldIn (accessSlot (incorporateChild fork caller child.1).substate
            message.currentTarget (balSlot message)) message.currentTarget 1) ≤
        gas - preCostD c0 cL c10 cU - (callGasD fork gas c0 cL c10 cU).cost + child.1.gas ∧
      s.running = false ∧ s.output = .empty ∧
      s.gas = gas - preCostD c0 cL c10 cU - (callGasD fork gas c0 cL c10 cU).cost + child.1.gas -
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
        (addrArg message.data 0) (resWord (outMemOf (memD message) child.1.output)) := by
  obtain ⟨h4, hv, -⟩ := runFrame_ok_dispatch hfork hsize' start within hrun hok
  by_cases hown : callerWord message ≠ ownerOf state message.currentTarget
  · exact (no_ok (fun g hg => Destroy.spec_notOwner hfork h4 hsize' hsel hv hown hc0 hg)
      (fun _ e h => halted_true_error e h) start within hrun hok).elim
  have hown := not_ne hown
  by_cases hl : (storageAt state message.currentTarget (listSlot (addrArg message.data 0))).toNat %
      256 = 0
  · exact (no_ok (fun g hg => Destroy.spec_notListed hfork h4 hsize' hsel hv hown hl hc0 hcL hg)
      (fun _ e h => halted_true_error e h) start within hrun hok).elim
  obtain ⟨hg0, z, w, hz, hrunz⟩ := ok_split (Nat.le_refl _)
    (fun g hg => prefixG_destroy hfork h4 hsize' hsel hv hown hl hdep hc0 hcL hc10 hg)
    start within hrun hok
  obtain ⟨hw, hgc, hdepth, hCE⟩ := fromExt (U := upWord (storageAt state message.currentTarget 10))
    (rest := [0x84, 0x70a08231, upWord (storageAt state message.currentTarget 10), 0,
      addrArg message.data 0, 0x1f48, 0, addrArg message.data 0, 0x09b6,
      BitVec.ofNat 256 (selector message.data)])
    (st := readSlot (preState state message) message.currentTarget 10)
    (ss := accessSlot (preSub substate message) message.currentTarget 10)
    hfork hglam (Or.inr (Or.inl ⟨rfl, rfl⟩)) (by simp) hcode hdel hz w hrunz hok
  have hB := size_memD message
  have hext : extendMemory (memD message).size
      [((0x60 : U256), (0x24 : U256)), ((0x60 : U256), (0x20 : U256))] = ⟨0, 0⟩ := by
    rw [hB]; decide
  have hcU' : decide (toAddressMasked (upWord (storageAt state message.currentTarget 10)) ∉
      (accessSlot (preSub substate message) message.currentTarget 10).accessedAddresses) =
      decide (upAddr state message ∉ substate.accessedAddresses) := rfl
  rw [hcU', hcU] at hgc hCE
  rw [hext] at hgc
  simp only [accCost] at hgc hg0
  have e1 : gas - (1472 + slotCost c0 + slotCost cL + slotCost c10) - (accCost cU + 25) =
      gas - (1497 + slotCost c0 + slotCost cL + slotCost c10 + accCost cU) := by
    simp only [accCost]; omega
  have e2 : gas - (1472 + slotCost c0 + slotCost cL + slotCost c10) - (accCost cU + 28) =
      gas - preCostD c0 cL c10 cU := by
    simp only [preCostD, accCost]; omega
  rw [e1, e2] at hCE
  obtain ⟨caller, msg, lt, child, hch, hcs, hcss, hmg, hmc, hmt, hmtg, hmca, hmcode, hmd, hmv,
    hmdep, hmst, after, wa, hat, hruna⟩ := hCE
  rw [hext] at hmg hmd hat
  simp only [Bool.false_eq_true, ↓reduceIte] at hmg hat
  refine ⟨hown, hl, hw, by simp only [preCostD, accCost]; omega, hdepth, ?_⟩
  have hfwd : Sends message (upAddr state message) c (dataB message) msg := by
    refine ⟨hmc, hmt, hmtg, hmca, hmcode, ?_, hmv, hmdep, hmst⟩
    rw [hmd, memoryExtend_zero]; exact data_memD message
  by_cases he : child.1.error = none
  · simp only [he, Option.isNone_none, ↓reduceIte] at hat
    have hacc : hasAccount (incorporateChild fork caller child.1).state message.currentTarget := by
      rw [state_incorporateChild]; exact hkeep caller msg lt child hch hfwd he
    obtain ⟨hcost, hr, ho, hgs, hst, hss⟩ := ok_exact2
      (fun g h1 _ => tailD (fork := fork) (message := message)
        hfork hglam (mkey_addrArg0 message.data) hstatic hacc
        (size_outMemOf hB child.1.output)
        (mload_outMemOf hB (by rw [memoryExtend_zero]; exact ptr_memD message) child.1.output)
        (x := BitVec.ofNat 256 (selector message.data)) rfl rfl (gas := g) h1) hat wa hruna hok
    refine ⟨caller, msg, lt, child, hch, he, hfwd, hmg, hcs, hcss, ?_, hr, ho, ?_, hst, hss⟩
    · simp only [Nat.add_zero, balSlot] at hcost ⊢
      exact hcost
    · rw [hgs]
      simp only [Nat.add_zero, balSlot]
  · have hz : child.1.error.isNone = false := by
      cases h : child.1.error
      · exact absurd h he
      · rfl
    simp only [hz, Bool.false_eq_true, ↓reduceIte] at hat
    exact (no_ok (fun g hg => failTail hfork (Or.inr (Or.inl rfl)) (by simp) hg)
      (fun g e h => by rw [h.2.1]; simp) hat wa hruna hok).elim

end UsdtVerify.Complete
