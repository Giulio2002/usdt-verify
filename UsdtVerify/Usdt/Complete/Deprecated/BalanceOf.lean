import UsdtVerify.Usdt.Complete.Deprecated.TotalSupply
import UsdtVerify.Usdt.Spec.Deprecated.BalanceOf

/-!
# Completeness of deprecated balanceOf(address), for any gas and any runner

`prefixG_balanceOf` (pc 0 to EXTCODESIZE at 4874, over `StepG`), `dep_balanceOf_split`, and
`dep_balanceOf_complete`: every run that ends with no error, with any gas and ANY runner, is the
forward of `balanceOf(a)` to the upgraded address (`SendsVia … (dataB message)`), the runner gave a
frame with no error, and the run returns the word at 0x60 after the CALL wrote the start of that
frame's output; gas, state and substate exact. The code found and the route of the CALL (no
delegation, or an EIP-7702 delegate) as for totalSupply; no hypothesis on the code.
-/

namespace UsdtVerify.Complete

open EthLib.Base (Fork U256 toAddressMasked)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic hiding HoareG StepG
open UsdtVerify.Gas
open GasCosts
open Deprecated DeprecatedBalance

variable {fork : Fork} {bound : Nat} {runChild : MessageRunner fork Nat bound}
  {message : Message fork} {state : State.TransactionState} {substate : Substate}

/-- From pc 0 to 4874 (EXTCODESIZE of the upgraded address), deprecated `balanceOf`, over
`StepG`. -/
theorem prefixG_balanceOf (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x70a08231)
    (hv : message.value = 0) (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0)
    {c10 : Bool} (hc10 : coldIn substate message.currentTarget 10 = c10) {gas : Nat}
    (hg : 896 + slotCost c10 ≤ gas) :
    HoareG fork (At CODE message 0 [] .empty gas state substate)
      (At CODE message 4874
        [upWord (storageAt state message.currentTarget 10),
          upWord (storageAt state message.currentTarget 10), 0, 0x60, 0x24, 0x60, 0x20, 0x84,
          0x70a08231, upWord (storageAt state message.currentTarget 10), 0,
          addrArg message.data 0, 0x05e7, BitVec.ofNat 256 (selector message.data)]
        (M2B (addrArg message.data 0)) (gas - (896 + slotCost c10))
        (readSlot state message.currentTarget 10) (accessSlot substate message.currentTarget 10)) := by
  have ht : tested (BitVec.ofNat 256 (selector message.data)) ENTRIES = 17 := by
    rw [hsel]; decide
  have hb : branch (BitVec.ofNat 256 (selector message.data)) 54 (entrySize 4 2) ENTRIES =
      1456 := by
    rw [hsel]; decide
  have h1 := dispatch (state := state) (substate := substate) hsize hsize' (gas := gas)
    (by rw [ht]; gas_ok)
  rw [ht, hb] at h1
  refine Triple.seq h1 ?_
  step BalanceOf.entry hv (by gas_ok)
  step depSet hfork (Or.inr ⟨rfl, rfl⟩) (by simp) hdep hc10 (by gas_ok)
  step fwdArgsB (state := state) hfork (by simp only [addrArg, mask_mask]) (by simp)
    (by gas_ok)
  exact Gas.reshapeG rfl rfl (by gas_ok)

theorem dep_balanceOf_split (hfork : .berlin ≤ fork) (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x70a08231)
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0)
    {gas : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) :
    896 + slotCost (coldIn substate message.currentTarget 10) ≤ gas ∧ ∃ z' w,
      At CODE message 4874
        [upWord (storageAt state message.currentTarget 10),
          upWord (storageAt state message.currentTarget 10), 0, 0x60, 0x24, 0x60, 0x20, 0x84,
          0x70a08231, upWord (storageAt state message.currentTarget 10), 0,
          addrArg message.data 0, 0x05e7, BitVec.ofNat 256 (selector message.data)]
        (M2B (addrArg message.data 0))
        (gas - (896 + slotCost (coldIn substate message.currentTarget 10)))
        (readSlot state message.currentTarget 10) (accessSlot substate message.currentTarget 10) z' ∧
      Evm.runFrame (step fork) (step_decreases fork) bound runChild z' w = .ok s := by
  obtain ⟨h4, hv, -⟩ := runFrame_ok_dispatch hfork hsize' start within hrun hok
  exact ok_split (Nat.le_refl _)
    (fun g hg => prefixG_balanceOf hfork h4 hsize' hsel hv hdep rfl hg) start within hrun hok

/-- **`dep_balanceOf_complete` over `RunC`** (round 39): for any relation `Run` of the child, a `RunC`
from the fresh frame that ends with no error, where `EndsOk` holds (for the dispatcher and the
guards), has the conclusion of `dep_balanceOf_complete` with `Run caller msg child` in place of the runner. Since round 42 it also gives a frame `after`, the frame after the CALL, with `Tail after`, from which no running frame refills at an SSTORE. -/
theorem dep_balanceOf_completeC {Run : Evm fork Nat → Message fork → Evm fork Nat → Prop} {Tail : Evm fork Nat → Prop}
    (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x70a08231)
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0)
    {gas : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (hrun : RunC fork Run Tail evm s) (hE : EndsOk fork evm) (hok : s.error = none) :
    ∃ c r, state.getCode (state.getAccount (upAddr state message)).codeHash = .ok c ∧
    Routes fork state c r ∧
    BitVec.ofNat 256 c.size ≠ 0 ∧
    preCostB fork (coldIn substate message.currentTarget 10)
      (decide (upAddr state message ∉ substate.accessedAddresses)) + 100 +
      routeCost fork (callSub substate state message).accessedAddresses r ≤ gas ∧
    message.depth + 1 ≤ STACK_DEPTH_LIMIT ∧
    ∃ caller msg child, Run caller msg child ∧ child.error = none ∧
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
      126 ≤ gas - preCostB fork (coldIn substate message.currentTarget 10)
          (decide (upAddr state message ∉ substate.accessedAddresses)) -
        (depCallGas fork (askedOfB fork gas (coldIn substate message.currentTarget 10)
          (decide (upAddr state message ∉ substate.accessedAddresses)))
        (gas - preCostB fork (coldIn substate message.currentTarget 10)
          (decide (upAddr state message ∉ substate.accessedAddresses)))
        (routeCost fork (callSub substate state message).accessedAddresses r)).cost + child.gas ∧
      s.running = false ∧
      s.output = wordBytes (resWord (outMemOf (M2B (addrArg message.data 0)) child.output)) ∧
      s.gas = gas - preCostB fork (coldIn substate message.currentTarget 10)
          (decide (upAddr state message ∉ substate.accessedAddresses)) -
        (depCallGas fork (askedOfB fork gas (coldIn substate message.currentTarget 10)
          (decide (upAddr state message ∉ substate.accessedAddresses)))
        (gas - preCostB fork (coldIn substate message.currentTarget 10)
          (decide (upAddr state message ∉ substate.accessedAddresses)))
        (routeCost fork (callSub substate state message).accessedAddresses r)).cost + child.gas - 126 ∧
      s.state = (incorporateChild fork caller child).state ∧
      s.substate = (incorporateChild fork caller child).substate ∧
      ∃ after, Tail after ∧
        ∀ y, Reaches (Step fork) after y → y.running = true → Refill.NoRefillAtN y := by
  obtain ⟨h4, hv, -⟩ := EndsOk.dispatch hfork hsize' start hE
  obtain ⟨hg0, z, hz, hrunz⟩ := ok_splitCA (Nat.le_refl _)
    (fun g hg => prefixG_balanceOf hfork h4 hsize' hsel hv hdep rfl hg)
    (by simp only [slotCost]; (repeat' split) <;> omega) (fun _ _ => rfl) start hrun hok
  obtain ⟨c, hcode⟩ := fromExt_foundC (by decide) hz hrunz hok
  obtain ⟨r, hroute, hw, hgc, hdepth, hCE⟩ := fromExtC (U := upWord (storageAt state message.currentTarget 10))
    (rest := [0x84, 0x70a08231, upWord (storageAt state message.currentTarget 10), 0,
      addrArg message.data 0, 0x05e7, BitVec.ofNat 256 (selector message.data)])
    (st := readSlot state message.currentTarget 10) (ss := accessSlot substate message.currentTarget 10)
    hfork (Or.inr (Or.inl ⟨rfl, rfl⟩)) (by simp) hcode hz hrunz hok
  have hB := size_M2B (addrArg message.data 0)
  have hext : extendMemory (M2B (addrArg message.data 0)).size
      [((0x60 : U256), (0x24 : U256)), ((0x60 : U256), (0x20 : U256))] = ⟨0, 0⟩ := by
    rw [hB]; decide
  unfold CallEndC at hCE
  simp only [routeCost_insert_insert] at hCE
  have hRe : routeCost fork ((accessSlot substate message.currentTarget 10).accessedAddresses.insert
      (toAddressMasked (upWord (storageAt state message.currentTarget 10)))) r =
      routeCost fork (callSub substate state message).accessedAddresses r := rfl
  rw [hRe] at hgc hCE
  refine ⟨c, r, hcode, Logic.Routes.congr (fun _ => rfl) hroute, ?_⟩
  generalize hR : routeCost fork (callSub substate state message).accessedAddresses r = R at hgc hCE ⊢
  generalize hc10 : coldIn substate message.currentTarget 10 = c10 at *
  have hcU' : decide (toAddressMasked (upWord (storageAt state message.currentTarget 10)) ∉
      (accessSlot substate message.currentTarget 10).accessedAddresses) =
      decide (upAddr state message ∉ substate.accessedAddresses) := rfl
  rw [hcU'] at hgc hCE
  generalize hcU : decide (upAddr state message ∉ substate.accessedAddresses) = cU at *
  rw [hext] at hgc
  simp only [extCost] at hgc hg0
  have e1 : gas - (896 + slotCost c10) - (extCost fork cU + 25) =
      gas - (921 + slotCost c10 + extCost fork cU) := by
    simp only [extCost]; omega
  have e2 : gas - (896 + slotCost c10) - (extCost fork cU + 28) = gas - preCostB fork c10 cU := by
    simp only [preCostB, extCost]; omega
  rw [e1, e2] at hCE
  obtain ⟨caller, msg, child, hch, hcs, hcss, hmg, hmc, hmt, hmtg, hmca, hmcode, hmdp, hmd, hmv,
    hmdep, hmst, after, hat, hT, hruna⟩ := hCE
  rw [hext] at hmg hmd hat
  simp only [accCost_false] at hmg hat
  refine ⟨hw, by simp only [preCostB, extCost]; omega, hdepth, ?_⟩
  have hfwd : SendsVia message (upAddr state message) c r (dataB message) msg := by
    refine ⟨hmc, hmt, hmtg, hmca, hmcode, hmdp, ?_, hmv, hmdep, hmst⟩
    rw [hmd]; exact data_M2B _
  by_cases he : child.error = none
  · simp only [he, Option.isNone_none, ↓reduceIte] at hat
    have hspec := fun g (_ : 126 ≤ g) => okTailB (fork := fork) (message := message)
        (state := (incorporateChild fork caller child).state)
        (substate := (incorporateChild fork caller child).substate)
        (U := upWord (storageAt state message.currentTarget 10)) (a := addrArg message.data 0)
        (size_outMemOf hB child.output)
        (mload_outMemOf hB (mload_M2B _) child.output)
        (x := BitVec.ofNat 256 (selector message.data)) (gas := g) (by omega)
    obtain ⟨h126, hr, ho, hgs, hst, hss⟩ := ok_exactE (Nat.le_refl 126) hspec hat hruna hok
    have hnrT := noRefill_of_specA (Nat.le_refl 126) (by decide) hspec (fun _ _ => rfl) hat
    refine ⟨caller, msg, child, hch, he, hfwd, hmg, hcs, hcss, ?_, hr, ho, ?_, hst, hss,
      after, hT, hnrT⟩
    · simp only [Nat.add_zero] at h126
      omega
    · rw [hgs]
      simp only [Nat.add_zero]
  · have hz : child.error.isNone = false := by
      cases h : child.error
      · exact absurd h he
      · rfl
    simp only [hz, Bool.false_eq_true, ↓reduceIte] at hat
    exact (no_okE (fun g hg => failTail hfork (Or.inr (Or.inl rfl)) (by simp) hg)
      (fun g e h => by rw [h.2.1]; simp) hat hruna hok).elim


theorem dep_balanceOf_complete (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x70a08231)
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0)
    {gas : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) :
    ∃ c r, state.getCode (state.getAccount (upAddr state message)).codeHash = .ok c ∧
    Routes fork state c r ∧
    BitVec.ofNat 256 c.size ≠ 0 ∧
    preCostB fork (coldIn substate message.currentTarget 10)
      (decide (upAddr state message ∉ substate.accessedAddresses)) + 100 +
      routeCost fork (callSub substate state message).accessedAddresses r ≤ gas ∧
    message.depth + 1 ≤ STACK_DEPTH_LIMIT ∧
    ∃ caller msg lt child, runChild caller msg lt = .ok child ∧ child.1.error = none ∧
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
      126 ≤ gas - preCostB fork (coldIn substate message.currentTarget 10)
          (decide (upAddr state message ∉ substate.accessedAddresses)) -
        (depCallGas fork (askedOfB fork gas (coldIn substate message.currentTarget 10)
          (decide (upAddr state message ∉ substate.accessedAddresses)))
        (gas - preCostB fork (coldIn substate message.currentTarget 10)
          (decide (upAddr state message ∉ substate.accessedAddresses)))
        (routeCost fork (callSub substate state message).accessedAddresses r)).cost + child.1.gas ∧
      s.running = false ∧
      s.output = wordBytes (resWord (outMemOf (M2B (addrArg message.data 0)) child.1.output)) ∧
      s.gas = gas - preCostB fork (coldIn substate message.currentTarget 10)
          (decide (upAddr state message ∉ substate.accessedAddresses)) -
        (depCallGas fork (askedOfB fork gas (coldIn substate message.currentTarget 10)
          (decide (upAddr state message ∉ substate.accessedAddresses)))
        (gas - preCostB fork (coldIn substate message.currentTarget 10)
          (decide (upAddr state message ∉ substate.accessedAddresses)))
        (routeCost fork (callSub substate state message).accessedAddresses r)).cost + child.1.gas - 126 ∧
      s.state = (incorporateChild fork caller child.1).state ∧
      s.substate = (incorporateChild fork caller child.1).substate := by
  obtain ⟨c, r, h1, h2, h3, h4, h5, caller, msg, child, ⟨lt, hle, hch⟩, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, -⟩ :=
    dep_balanceOf_completeC hfork hsize' hsel hdep start (RunC.of_runFrame hrun)
      (EndsOk.of_runFrame hrun hok) hok
  exact ⟨c, r, h1, h2, h3, h4, h5, caller, msg, lt, ⟨child, hle⟩, hch, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11⟩

end UsdtVerify.Complete
