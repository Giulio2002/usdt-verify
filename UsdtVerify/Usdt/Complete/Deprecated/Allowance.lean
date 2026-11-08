import UsdtVerify.Usdt.Complete.Deprecated.Transfer
import UsdtVerify.Usdt.Spec.Deprecated.Allowance

/-!
# Completeness of deprecated allowance(address,address), for any gas and any runner

`prefixG_allowance` (pc 0 to EXTCODESIZE at 7186, over `StepG`) and `dep_allowance_complete`:
every run of a deprecated `allowance(owner, spender)` call that ends with no error, with any
gas, any gas bound and ANY message runner, is the forward of `allowance(owner, spender)` to the
upgraded address (`SendsVia … (dataAl message)`): the runner gave a frame with no error, and the run
returns the word at 0x60 after the CALL wrote the start of that frame's output; gas, state and
substate exact. `Complete.fromExt` covers the pcs of this path (7186 to 7203) since round 15.
The code found and the route of the CALL are in the conclusion; named hypotheses: the coldness
flags `hc10`, `hcU`.
-/

namespace UsdtVerify.Complete

open EthLib.Base (Fork U256 toAddressMasked)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open UsdtVerify.Gas
open GasCosts
open Deprecated DeprecatedBalance DeprecatedAllowance

variable {fork : Fork} {bound : Nat} {runChild : MessageRunner fork Nat bound}
  {message : Message fork} {state : State.TransactionState} {substate : Substate}

/-- From pc 0 to 7186 (EXTCODESIZE of the upgraded address), deprecated `allowance`, over
`StepG` (the prefix of `preCallAl`). -/
theorem prefixG_allowance (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xdd62ed3e)
    (hv : message.value = 0) (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0)
    {c10 : Bool} (hc10 : coldIn substate message.currentTarget 10 = c10) {gas : Nat}
    (hg : 1159 + slotCost c10 ≤ gas) :
    HoareG fork (At CODE message 0 [] .empty gas state substate)
      (At CODE message 7186
        [upWord (storageAt state message.currentTarget 10),
          upWord (storageAt state message.currentTarget 10), 0, 0x60, 0x44, 0x60, 0x20, 0xa4,
          0xdd62ed3e, upWord (storageAt state message.currentTarget 10), 0,
          addrArg message.data 1, addrArg message.data 0, BitVec.ofNat 256 2132,
          BitVec.ofNat 256 (selector message.data)]
        (memAl message) (gas - (1159 + slotCost c10))
        (readSlot state message.currentTarget 10) (accessSlot substate message.currentTarget 10)) := by
  refine Triple.seq ((Getters.toEntry (t := 26) (e := 2046) (by decide) hsize hsize' hsel
    (by omega)).seq (GettersMap.entry2 (r := 2132) (b := 6925) (by decide) hv (by omega))) ?_
  step depSetA hfork (by simp) hdep hc10 (by gas_ok)
  step fwdArgsA (state := state) hfork (by simp only [addrArg, mask_mask])
    (by simp only [addrArg, mask_mask]) (by gas_ok)
  exact Gas.reshapeG rfl rfl (by gas_ok)

/-- **`dep_allowance_complete` over `RunC`** (round 39): for any relation `Run` of the child, a `RunC`
from the fresh frame that ends with no error, where `EndsOk` holds (for the dispatcher and the
guards), has the conclusion of `dep_allowance_complete` with `Run caller msg child` in place of the runner. Since round 42 it also gives a frame `after`, the frame after the CALL, with `Tail after`, from which no running frame refills at an SSTORE. -/
theorem dep_allowance_completeC {Run : Evm fork Nat → Message fork → Evm fork Nat → Prop} {Tail : Evm fork Nat → Prop}
    (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xdd62ed3e)
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0)
    {c10 cU : Bool} (hc10 : coldIn substate message.currentTarget 10 = c10)
    (hcU : decide (upAddr state message ∉ substate.accessedAddresses) = cU)
    {gas : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (hrun : RunC fork Run Tail evm s) (hE : EndsOk fork evm) (hok : s.error = none) :
    ∃ c r, state.getCode (state.getAccount (upAddr state message)).codeHash = .ok c ∧
    Routes fork state c r ∧
    BitVec.ofNat 256 c.size ≠ 0 ∧
    preCostAl fork c10 cU + 100 + routeCost fork (callSub substate state message).accessedAddresses r ≤ gas ∧
    message.depth + 1 ≤ STACK_DEPTH_LIMIT ∧
    ∃ caller msg child, Run caller msg child ∧ child.error = none ∧
      SendsVia message (upAddr state message) c r (dataAl message) msg ∧
      msg.gas = (depCallGas fork (askedOfAl fork gas c10 cU) (gas - preCostAl fork c10 cU)
        (routeCost fork (callSub substate state message).accessedAddresses r)).subCall ∧
      caller.state = (routeState ((callState state message).recordAccountRead
        (upAddr state message)) r).recordAccountRead message.currentTarget ∧
      caller.substate = routeSub { callSub substate state message with
        accessedAddresses :=
          (callSub substate state message).accessedAddresses.insert (upAddr state message) } r ∧
      128 ≤ gas - preCostAl fork c10 cU - (depCallGas fork (askedOfAl fork gas c10 cU) (gas - preCostAl fork c10 cU)
        (routeCost fork (callSub substate state message).accessedAddresses r)).cost + child.gas ∧
      s.running = false ∧
      s.output = wordBytes (resWord (outMemOf (memAl message) child.output)) ∧
      s.gas = gas - preCostAl fork c10 cU - (depCallGas fork (askedOfAl fork gas c10 cU) (gas - preCostAl fork c10 cU)
        (routeCost fork (callSub substate state message).accessedAddresses r)).cost + child.gas - 128 ∧
      s.state = (incorporateChild fork caller child).state ∧
      s.substate = (incorporateChild fork caller child).substate ∧
      ∃ after, Tail after ∧
        ∀ y, Reaches (Step fork) after y → y.running = true → Refill.NoRefillAtN y := by
  obtain ⟨h4, hv, -⟩ := EndsOk.dispatch hfork hsize' start hE
  obtain ⟨hg0, z, hz, hrunz⟩ := ok_splitCA (Nat.le_refl _)
    (fun g hg => prefixG_allowance hfork h4 hsize' hsel hv hdep hc10 hg)
    (by simp only [slotCost]; (repeat' split) <;> omega) (fun _ _ => rfl) start hrun hok
  obtain ⟨c, hcode⟩ := fromExt_foundC (by decide) hz hrunz hok
  obtain ⟨r, hroute, hw, hgc, hdepth, hCE⟩ := fromExtC (U := upWord (storageAt state message.currentTarget 10))
    (rest := [0xa4, 0xdd62ed3e, upWord (storageAt state message.currentTarget 10), 0,
      addrArg message.data 1, addrArg message.data 0, BitVec.ofNat 256 2132,
      BitVec.ofNat 256 (selector message.data)])
    (st := readSlot state message.currentTarget 10)
    (ss := accessSlot substate message.currentTarget 10)
    hfork (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))))) (by simp) hcode hz
    hrunz hok
  have hB := size_M3A (addrArg message.data 0) (addrArg message.data 1)
  have hext : extendMemory (memAl message).size
      [((0x60 : U256), (0x44 : U256)), ((0x60 : U256), (0x20 : U256))] = ⟨0, 0⟩ := by
    rw [hB]; decide
  have hcU' : decide (toAddressMasked (upWord (storageAt state message.currentTarget 10)) ∉
      (accessSlot substate message.currentTarget 10).accessedAddresses) =
      decide (upAddr state message ∉ substate.accessedAddresses) := rfl
  unfold CallEndC at hCE
  simp only [routeCost_insert_insert] at hCE
  have hRe : routeCost fork ((accessSlot substate message.currentTarget 10).accessedAddresses.insert
      (toAddressMasked (upWord (storageAt state message.currentTarget 10)))) r =
      routeCost fork (callSub substate state message).accessedAddresses r := rfl
  rw [hRe] at hgc hCE
  refine ⟨c, r, hcode, routes_congr (fun _ => rfl) hroute, ?_⟩
  generalize hR : routeCost fork (callSub substate state message).accessedAddresses r = R at hgc hCE ⊢
  rw [hcU', hcU] at hgc hCE
  rw [hext] at hgc
  simp only [extCost] at hgc hg0
  have e1 : gas - (1159 + slotCost c10) - (extCost fork cU + 25) =
      gas - (1184 + slotCost c10 + extCost fork cU) := by
    simp only [extCost]; omega
  have e2 : gas - (1159 + slotCost c10) - (extCost fork cU + 28) = gas - preCostAl fork c10 cU := by
    simp only [preCostAl, extCost]; omega
  rw [e1, e2] at hCE
  obtain ⟨caller, msg, child, hch, hcs, hcss, hmg, hmc, hmt, hmtg, hmca, hmcode, hmdp, hmd, hmv,
    hmdep, hmst, after, hat, hT, hruna⟩ := hCE
  rw [hext] at hmg hmd hat
  simp only [accCost_false] at hmg hat
  refine ⟨hw, by simp only [preCostAl, extCost]; omega, hdepth, ?_⟩
  have hfwd : SendsVia message (upAddr state message) c r (dataAl message) msg := by
    refine ⟨hmc, hmt, hmtg, hmca, hmcode, hmdp, ?_, hmv, hmdep, hmst⟩
    rw [hmd, memoryExtend_zero]; exact data_M3A _ _
  by_cases he : child.error = none
  · simp only [he, Option.isNone_none, ↓reduceIte] at hat
    have hspec := fun g (_ : 128 ≤ g) => DeprecatedAllowance.okTailA (fork := fork) (message := message)
        (state := (incorporateChild fork caller child).state)
        (substate := (incorporateChild fork caller child).substate)
        (U := upWord (storageAt state message.currentTarget 10)) (a := addrArg message.data 0)
        (b := addrArg message.data 1)
        (size_outMemOfA hB child.output) (mload_outMemOfA hB (mload_M3A _ _) child.output)
        (x := BitVec.ofNat 256 (selector message.data)) (gas := g) (by omega)
    obtain ⟨h128, hr, ho, hgs, hst, hss⟩ := ok_exactE (Nat.le_refl 128) hspec hat hruna hok
    have hnrT := noRefill_of_specA (Nat.le_refl 128) (by decide) hspec (fun _ _ => rfl) hat
    refine ⟨caller, msg, child, hch, he, hfwd, hmg, hcs, hcss, ?_, hr, ho, ?_, hst, hss,
      after, hT, hnrT⟩
    · simp only [Nat.add_zero] at h128
      omega
    · rw [hgs]
      simp only [Nat.add_zero]
  · have hz : child.error.isNone = false := by
      cases h : child.error
      · exact absurd h he
      · rfl
    simp only [hz, Bool.false_eq_true, ↓reduceIte] at hat
    exact (no_okE (fun g hg => failTailA hfork (by simp) hg)
      (fun g e h => by rw [h.2.1]; simp) hat hruna hok).elim


/-- Every successful deprecated `allowance(owner, spender)` run, for any gas and any runner: a
nonzero code size at the upgraded address, the gas of the path, a depth below the limit, and the
forward that the runner ended with no error; then the run returns the word at 0x60 after the
CALL wrote the start of the child's output there; gas, state and substate exact. -/
theorem dep_allowance_complete (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xdd62ed3e)
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0)
    {c10 cU : Bool} (hc10 : coldIn substate message.currentTarget 10 = c10)
    (hcU : decide (upAddr state message ∉ substate.accessedAddresses) = cU)
    {gas : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) :
    ∃ c r, state.getCode (state.getAccount (upAddr state message)).codeHash = .ok c ∧
    Routes fork state c r ∧
    BitVec.ofNat 256 c.size ≠ 0 ∧
    preCostAl fork c10 cU + 100 + routeCost fork (callSub substate state message).accessedAddresses r ≤ gas ∧
    message.depth + 1 ≤ STACK_DEPTH_LIMIT ∧
    ∃ caller msg lt child, runChild caller msg lt = .ok child ∧ child.1.error = none ∧
      SendsVia message (upAddr state message) c r (dataAl message) msg ∧
      msg.gas = (depCallGas fork (askedOfAl fork gas c10 cU) (gas - preCostAl fork c10 cU)
        (routeCost fork (callSub substate state message).accessedAddresses r)).subCall ∧
      caller.state = (routeState ((callState state message).recordAccountRead
        (upAddr state message)) r).recordAccountRead message.currentTarget ∧
      caller.substate = routeSub { callSub substate state message with
        accessedAddresses :=
          (callSub substate state message).accessedAddresses.insert (upAddr state message) } r ∧
      128 ≤ gas - preCostAl fork c10 cU - (depCallGas fork (askedOfAl fork gas c10 cU) (gas - preCostAl fork c10 cU)
        (routeCost fork (callSub substate state message).accessedAddresses r)).cost + child.1.gas ∧
      s.running = false ∧
      s.output = wordBytes (resWord (outMemOf (memAl message) child.1.output)) ∧
      s.gas = gas - preCostAl fork c10 cU - (depCallGas fork (askedOfAl fork gas c10 cU) (gas - preCostAl fork c10 cU)
        (routeCost fork (callSub substate state message).accessedAddresses r)).cost + child.1.gas - 128 ∧
      s.state = (incorporateChild fork caller child.1).state ∧
      s.substate = (incorporateChild fork caller child.1).substate := by
  obtain ⟨c, r, h1, h2, h3, h4, h5, caller, msg, child, ⟨lt, hle, hch⟩, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, -⟩ :=
    dep_allowance_completeC hfork hsize' hsel hdep hc10 hcU start (RunC.of_runFrame hrun)
      (EndsOk.of_runFrame hrun hok) hok
  exact ⟨c, r, h1, h2, h3, h4, h5, caller, msg, lt, ⟨child, hle⟩, hch, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11⟩

end UsdtVerify.Complete
