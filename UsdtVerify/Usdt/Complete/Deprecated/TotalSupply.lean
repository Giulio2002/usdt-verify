import UsdtVerify.Usdt.Complete.Deprecated.Call
import UsdtVerify.Usdt.Spec.TotalSupply
import UsdtVerify.Usdt.Complete.Dispatch

/-!
# Completeness of deprecated totalSupply(), for any gas and any runner

`dep_totalSupply_complete`: from Berlin on (Glamsterdam included), a fresh frame of `CODE` at pc 0
with selector 0x18160ddd, deprecated (byte 20 of slot 10 not 0), ANY gas, ANY gas bound and ANY
message runner `runChild`. If the loop ends with no error, then:

- the code `c` of the upgraded address is found in the state, and the CALL follows a route `r`
  (`Routes`): no delegation, or, from Pectra, `c` is an EIP-7702 delegation indicator to an
  address `d` whose code is found;
- `c` has a nonzero size (as a word), the gas covers the path to the CALL plus the CALL's access
  and the access to the delegate (`preCost + 100 + routeCost`), and the depth is below the limit;
- the runner ran a message `msg` from a frame `caller` to a frame `child` with no error, `msg` is
  the forward of `totalSupply()` to the upgraded address along the route (`SendsVia`: the code
  and code address of the route, the precompiles disabled when delegated), with the gas of
  `depCallGas`; the caller's state and substate record the access to the delegate (`routeState`,
  `routeSub`);
- the run stopped with the output the 32 bytes at 0x60 after CALL wrote the child's output there
  (`resWord (outMem child.output)`), gas `gas - preCost - depCallGas.cost + child.gas - 121` (and
  at least 121 was left after the CALL), and the state and substate of
  `incorporateChild caller child`.

A failed lookup of the code of the upgraded address makes EXTCODESIZE fail (`fromExt_foundC`);
a failed lookup of the code of the delegate makes CALL fail or halt (EthLib's `callStep_fails_of_missing`). No hypothesis
on the code or on the runner: nothing is assumed of what the runner returns.
-/

namespace UsdtVerify.Complete

open EthLib.Base (Fork U256 toAddressMasked)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic hiding HoareG StepG
open UsdtVerify.Gas
open GasCosts
open Deprecated

variable {fork : Fork} {bound : Nat} {runChild : MessageRunner fork Nat bound}

section

/-! ## Deprecated totalSupply(): up to EXTCODESIZE -/

variable {message : Message fork} {state : State.TransactionState} {substate : Substate}

/-- From pc 0 to 3719 (EXTCODESIZE of the upgraded address), deprecated `totalSupply()`, over
`StepG`. -/
theorem prefixG_totalSupply (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x18160ddd)
    (hv : message.value = 0) (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0)
    {c10 : Bool} (hc10 : coldIn substate message.currentTarget 10 = c10) {gas : Nat}
    (hg : 574 + slotCost c10 ≤ gas) :
    HoareG fork (At CODE message 0 [] .empty gas state substate)
      (At CODE message 3719
        [upWord (storageAt state message.currentTarget 10),
          upWord (storageAt state message.currentTarget 10), 0, 0x60, 4, 0x60, 0x20, 0x64,
          0x18160ddd, upWord (storageAt state message.currentTarget 10), 0, 0x031d,
          BitVec.ofNat 256 (selector message.data)] M2 (gas - (574 + slotCost c10))
        (readSlot state message.currentTarget 10) (accessSlot substate message.currentTarget 10)) := by
  have ht : tested (BitVec.ofNat 256 (selector message.data)) ENTRIES = 6 := by
    rw [hsel]; decide
  have hb : branch (BitVec.ofNat 256 (selector message.data)) 54 (entrySize 4 2) ENTRIES = 778 := by
    rw [hsel]; decide
  have h1 := dispatch (state := state) (substate := substate) hsize hsize' (gas := gas)
    (by rw [ht]; gas_ok)
  rw [ht, hb] at h1
  refine Triple.seq h1 ?_
  step TotalSupply.entry hv (by gas_ok)
  step depSet hfork (Or.inl ⟨rfl, rfl⟩) (by simp) hdep hc10 (by gas_ok)
  step fwdArgs (state := state) hfork (by simp) (by gas_ok)
  exact Gas.reshapeG rfl rfl (by gas_ok)

/-- The split of deprecated totalSupply at EXTCODESIZE, over `RunC` (round 39), for any relation
`Run` of the child, given
the facts of the dispatcher (`h4`, `hv`). -/
theorem dep_totalSupply_splitC {Run : Evm fork Nat → Message fork → Evm fork Nat → Prop} {Tail : Evm fork Nat → Prop}
    (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size) (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x18160ddd) (hv : message.value = 0)
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0)
    {gas : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (hrun : RunC fork Run Tail evm s) (hok : s.error = none) :
    574 + slotCost (coldIn substate message.currentTarget 10) ≤ gas ∧ ∃ z',
      At CODE message 3719
        [upWord (storageAt state message.currentTarget 10),
          upWord (storageAt state message.currentTarget 10), 0, 0x60, 4, 0x60, 0x20, 0x64,
          0x18160ddd, upWord (storageAt state message.currentTarget 10), 0, 0x031d,
          BitVec.ofNat 256 (selector message.data)] M2
        (gas - (574 + slotCost (coldIn substate message.currentTarget 10)))
        (readSlot state message.currentTarget 10) (accessSlot substate message.currentTarget 10) z' ∧
      RunC fork Run Tail z' s :=
  ok_splitCA (Nat.le_refl _) (fun g hg => prefixG_totalSupply hfork hsize hsize' hsel hv hdep rfl hg)
    (by have := slotCost_le (coldIn substate message.currentTarget 10); omega) (fun _ _ => rfl)
    start hrun hok

end

variable {message : Message fork} {state : State.TransactionState} {substate : Substate}

/-- **`dep_totalSupply_complete` over `RunC`** (round 39): for any relation `Run` of the child,
a `RunC` from the fresh frame that ends with no error, where `EndsOk` holds (for the
dispatcher), has the conclusion of `dep_totalSupply_complete` with `Run caller msg child` in place
of the runner. Since round 42 it also gives a frame `after`, the frame after the CALL, with `Tail after`, from which no running frame refills at an SSTORE. -/
theorem dep_totalSupply_completeC {Run : Evm fork Nat → Message fork → Evm fork Nat → Prop} {Tail : Evm fork Nat → Prop}
    (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x18160ddd)
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0)
    {gas : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (hrun : RunC fork Run Tail evm s) (hE : EndsOk fork evm) (hok : s.error = none) :
    ∃ c r, state.getCode (state.getAccount (upAddr state message)).codeHash = .ok c ∧
    Routes fork state c r ∧
    BitVec.ofNat 256 c.size ≠ 0 ∧
    preCost fork (coldIn substate message.currentTarget 10)
      (decide (upAddr state message ∉ substate.accessedAddresses)) + 100 +
      routeCost fork (callSub substate state message).accessedAddresses r ≤ gas ∧
    message.depth + 1 ≤ STACK_DEPTH_LIMIT ∧
    ∃ caller msg child, Run caller msg child ∧ child.error = none ∧
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
      121 ≤ gas - preCost fork (coldIn substate message.currentTarget 10)
          (decide (upAddr state message ∉ substate.accessedAddresses)) -
        (depCallGas fork (askedOf fork gas (coldIn substate message.currentTarget 10)
          (decide (upAddr state message ∉ substate.accessedAddresses)))
        (gas - preCost fork (coldIn substate message.currentTarget 10)
          (decide (upAddr state message ∉ substate.accessedAddresses)))
        (routeCost fork (callSub substate state message).accessedAddresses r)).cost + child.gas ∧
      s.running = false ∧ s.output = wordBytes (resWord (outMem child.output)) ∧
      s.gas = gas - preCost fork (coldIn substate message.currentTarget 10)
          (decide (upAddr state message ∉ substate.accessedAddresses)) -
        (depCallGas fork (askedOf fork gas (coldIn substate message.currentTarget 10)
          (decide (upAddr state message ∉ substate.accessedAddresses)))
        (gas - preCost fork (coldIn substate message.currentTarget 10)
          (decide (upAddr state message ∉ substate.accessedAddresses)))
        (routeCost fork (callSub substate state message).accessedAddresses r)).cost +
        child.gas - 121 ∧
      s.state = (incorporateChild fork caller child).state ∧
      s.substate = (incorporateChild fork caller child).substate ∧
      ∃ after, Tail after ∧
        ∀ y, Reaches (Step fork) after y → y.running = true → Refill.NoRefillAtN y := by
  obtain ⟨h4, hv, -⟩ := EndsOk.dispatch hfork hsize' start hE
  obtain ⟨hg0, z, hz, hrunz⟩ := dep_totalSupply_splitC hfork h4 hsize' hsel hv hdep start hrun hok
  obtain ⟨c, hcode⟩ := fromExt_foundC (by decide) hz hrunz hok
  obtain ⟨r, hroute, hw, hgc, hdepth, hCE⟩ :=
    fromExtC (U := upWord (storageAt state message.currentTarget 10))
    (rest := [0x64, 0x18160ddd, upWord (storageAt state message.currentTarget 10), 0, 0x031d,
      BitVec.ofNat 256 (selector message.data)])
    (st := readSlot state message.currentTarget 10) (ss := accessSlot substate message.currentTarget 10)
    hfork (Or.inl ⟨rfl, rfl⟩) (by simp) hcode hz hrunz hok
  have hext : extendMemory M2.size [((0x60 : U256), (4 : U256)), ((0x60 : U256), (0x20 : U256))] =
      ⟨0, 0⟩ := by
    rw [size_M2]; decide
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
  have e1 : gas - (574 + slotCost c10) - (extCost fork cU + 25) = gas - (599 + slotCost c10 + extCost fork cU) := by
    simp only [extCost]; omega
  have e2 : gas - (574 + slotCost c10) - (extCost fork cU + 28) = gas - preCost fork c10 cU := by
    simp only [preCost, extCost]; omega
  rw [e1, e2] at hCE
  obtain ⟨caller, msg, child, hch, hcs, hcss, hmg, hmc, hmt, hmtg, hmca, hmcode, hmdp, hmd, hmv,
    hmdep, hmst, after, hat, hT, hruna⟩ := hCE
  rw [hext] at hmg hmd hat
  simp only [accCost_false] at hmg hat
  refine ⟨hw, by simp only [preCost, extCost]; omega, hdepth, ?_⟩
  have hfwd : SendsVia message (upAddr state message) c r SEL_TS msg := by
    refine ⟨hmc, hmt, hmtg, hmca, hmcode, hmdp, ?_, hmv, hmdep, hmst⟩
    rw [hmd]; exact data_M2
  by_cases he : child.error = none
  · simp only [he, Option.isNone_none, ↓reduceIte] at hat
    have hspec := fun g (_ : 121 ≤ g) => okTail (fork := fork) (message := message)
        (state := (incorporateChild fork caller child).state)
        (substate := (incorporateChild fork caller child).substate)
        (U := upWord (storageAt state message.currentTarget 10))
        (size_outMem child.output) (mload_outMem child.output)
        (x := BitVec.ofNat 256 (selector message.data)) (gas := g) (by omega)
    obtain ⟨h121, hr, ho, hgs, hst, hss⟩ := ok_exactE (Nat.le_refl 121) hspec hat hruna hok
    have hnrT := noRefill_of_specA (Nat.le_refl 121) (by decide) hspec (fun _ _ => rfl) hat
    refine ⟨caller, msg, child, hch, he, hfwd, hmg, hcs, hcss, ?_, hr, ho, ?_, hst, hss,
      after, hT, hnrT⟩
    · simp only [Nat.add_zero] at h121
      omega
    · rw [hgs]
      simp only [Nat.add_zero]
  · have hz : child.error.isNone = false := by
      cases h : child.error
      · exact absurd h he
      · rfl
    simp only [hz, Bool.false_eq_true, ↓reduceIte] at hat
    exact (no_okE (fun g hg => failTail hfork (Or.inl rfl) (by simp) hg)
      (fun g e h => by rw [h.2.1]; simp) hat hruna hok).elim

/-- Completeness of deprecated `totalSupply()`, for any gas, gas bound and runner over `Nat`
(since round 39 from `dep_totalSupply_completeC`). -/
theorem dep_totalSupply_complete (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x18160ddd)
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0)
    {gas : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
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
      121 ≤ gas - preCost fork (coldIn substate message.currentTarget 10)
          (decide (upAddr state message ∉ substate.accessedAddresses)) -
        (depCallGas fork (askedOf fork gas (coldIn substate message.currentTarget 10)
          (decide (upAddr state message ∉ substate.accessedAddresses)))
        (gas - preCost fork (coldIn substate message.currentTarget 10)
          (decide (upAddr state message ∉ substate.accessedAddresses)))
        (routeCost fork (callSub substate state message).accessedAddresses r)).cost + child.1.gas ∧
      s.running = false ∧ s.output = wordBytes (resWord (outMem child.1.output)) ∧
      s.gas = gas - preCost fork (coldIn substate message.currentTarget 10)
          (decide (upAddr state message ∉ substate.accessedAddresses)) -
        (depCallGas fork (askedOf fork gas (coldIn substate message.currentTarget 10)
          (decide (upAddr state message ∉ substate.accessedAddresses)))
        (gas - preCost fork (coldIn substate message.currentTarget 10)
          (decide (upAddr state message ∉ substate.accessedAddresses)))
        (routeCost fork (callSub substate state message).accessedAddresses r)).cost +
        child.1.gas - 121 ∧
      s.state = (incorporateChild fork caller child.1).state ∧
      s.substate = (incorporateChild fork caller child.1).substate := by
  obtain ⟨c, r, h1, h2, h3, h4, h5, caller, msg, child, ⟨lt, hle, hch⟩, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, -⟩ :=
    dep_totalSupply_completeC hfork hsize' hsel hdep start (RunC.of_runFrame hrun)
      (EndsOk.of_runFrame hrun hok) hok
  exact ⟨c, r, h1, h2, h3, h4, h5, caller, msg, lt, ⟨child, hle⟩, hch, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11⟩

end UsdtVerify.Complete
