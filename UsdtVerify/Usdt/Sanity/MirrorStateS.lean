import UsdtVerify.Usdt.Sanity.MirrorState
import UsdtVerify.Usdt.Sanity.ProcessMeter
import UsdtVerify.Usdt.Complete.Deprecated.DestroyS

/-!
# Sanity: a successful deprecated run over the EIP-8037 meter, with `MIRROR` (round 44)

`destroy_mirror_runs` (round 33) shows, before Glamsterdam and over the meter `Nat`, a deprecated
destroyBlackFunds call in the state `S2` that ends with no error under `processRunner`. Here the
same call runs over `StateGasMeter` under `processRunnerM`, at every fork from Paris (Glamsterdam
included), from a frame with any reservoir.

- `extCost_le`, `absorb_gasLeft_ge`, `callGas_bounds`: the price of EXTCODESIZE is at most 3100,
  the meter after a CALL whose child succeeded holds at least the execution gas left of both, and
  with at least 900000 gas at the CALL of the forward the message gets at least 2187 gas.
- `process_mirrorS_ok`: from Paris, a message that runs `MIRROR` at a target with no value and no
  precompile, with the gas `MIRROR` needs, ends under `processRunnerM` over `StateGasMeter` with no
  error, and with at least its gas less that need as execution gas left. Any reservoir.
- `destroy_mirror_runsS`: from Paris, in `S2 C H a` (`H` not the empty code hash),
  `destroyBlackFunds(a)` from the owner `CALLER_A` to `C`, from a frame of `StateGasMeter` with
  any meter whose execution gas left is at least 1000000 (and below 2^255), any substate, any gas
  bound: the loop of the interpreter with `processRunnerM` ends with no error. The run passes the
  checks, forwards `balanceOf(a)` to `UA`, `MIRROR` answers, and both writes of the tail go
  through, refills allowed.
- `mDOG`, `destroy_mirror_runsT`, `destroy_mirror_runsG` (round 45): the same for the message
  with any gas field `G` and reservoir field `R`, from any state with the facts the run needs
  (slot 10 of `C` is `W`, the owner `CALLER_A`, `a` blacklisted, `MIRROR` at `UA`, an account at
  `C`; `runsT`), and from `S2` (`runsG`; `destroy_mirror_runsS` is the case `G = R = 0`).
- `destroy_mirror_processS` (round 45): from Paris, with `C` no precompile, EthLib's
  `processMessage` of that message over `StateGasMeter`, from any substate and any starting meter
  with at least 1000000 and below 2^255 execution gas left (its held gas at most `G`), ends with a
  frame with no error.
-/

namespace UsdtVerify.Sanity

open EthLib.Base (Fork U256 Address toAddressMasked Hash32)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open UsdtVerify.Gas
open UsdtVerify.Meter (toNat)
open Complete Deprecated DeprecatedBalance DeprecatedDestroy DestroySpec Owner BlackList
  Transfer TransferOk

variable {fork : Fork}

/-- From Berlin, EXTCODESIZE costs at most 3100 (a cold access and a warm access from
Glamsterdam, EIP-8038). -/
theorem extCost_le (hfork : .berlin ≤ fork) (cold : Bool) : extCost fork cold ≤ 3100 := by
  unfold extCost externalBaseCost accountAccessCost
  by_cases hg : fork ≥ .glamsterdam <;> cases cold <;>
    simp [hg, hfork, gasSchedule, GasCosts.WARM_ACCESS] <;> decide

/-- The meter after a CALL whose child succeeded holds at least the execution gas left of the
caller and of the child. -/
theorem absorb_gasLeft_ge (c ch : StateGasMeter) :
    c.gasLeft + ch.gasLeft ≤ (GasMeter.absorb c ch true).gasLeft := by
  show _ ≤ (StateGasMeter.absorb c ch true).gasLeft
  simp only [StateGasMeter.absorb, StateGasMeter.repay, ite_true]
  omega

/-- With `G` execution gas at the CALL of a forward (the word `asked (G + 3)` on the stack, no
route), from at least 900000 and with `G + 3` below 2^256: the message gets at least 2187 gas and at most `G - 100`, and the
CALL costs 100 more than it passes on. -/
theorem callGas_bounds (hfork : .berlin ≤ fork) {G : Nat} (h1 : 900000 ≤ G) (h2 : G + 3 < 2 ^ 256) :
    2187 ≤ (depCallGas fork (asked (G + 3)) G 0).subCall ∧
    (depCallGas fork (asked (G + 3)) G 0).cost = 100 + (depCallGas fork (asked (G + 3)) G 0).subCall ∧
    (depCallGas fork (asked (G + 3)) G 0).subCall ≤ G - 100 := by
  have htw : Fork.tangerineWhistle ≤ fork := Nat.le_trans (by decide) hfork
  have ha : (asked (G + 3)).toNat = G + 3 - 710 := by
    unfold asked
    simp only [EthLib.Execution.Evm.sub, BitVec.toNat_sub, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt h2]
    have : (0x02c6 : U256).toNat = 710 := rfl
    rw [this]
    omega
  simp only [depCallGas, messageCallGas, maxMessageCallGas, ha, ge_iff_le, htw, true_and,
    Nat.add_zero]
  split <;> simp <;> omega

/-- **`MIRROR` succeeds under `processRunnerM` over `StateGasMeter`.** See the module doc. -/
theorem process_mirrorS_ok (hparis : .paris ≤ fork) {bound : Nat}
    (caller : Evm fork StateGasMeter) {msg : Message fork} (lt : msg.gas < bound)
    (hcode : msg.code = MIRROR) {ua : Address} (ht : msg.target = some ua) (hv : msg.value = 0)
    (hpre : precompileAddress fork msg = none) {k : U256} (hk : loadWord msg.data 4 32 = k)
    (hg : 87 + slotCost (coldIn caller.substate.child msg.currentTarget (mapSlot k 2)) ≤ msg.gas) :
    ∃ child, ProcessMeter.processRunnerM fork bound caller msg lt = .ok child ∧
      child.1.error = none ∧
      msg.gas - (87 + slotCost (coldIn caller.substate.child msg.currentTarget (mapSlot k 2))) ≤
        child.1.gas.gasLeft := by
  have hberlin : .berlin ≤ fork := Nat.le_trans (by decide) hparis
  have hst : startState fork msg caller.state = caller.state := by
    simp only [startState, show ¬fork < Fork.paris from Nat.not_lt.mpr hparis, ite_false]
  have hp : ProcessMeter.processRunnerM fork bound caller msg lt =
      processMessage fork msg caller.state caller.substate.child := by
    simp only [ProcessMeter.processRunnerM, ht]
  have start := ProcessMeter.at_startFrameS hcode (startState fork msg caller.state)
    caller.substate.child (GasMeter.start msg.gas msg.reservoir : StateGasMeter)
  rw [hst] at start
  have hgl : GasMeter.gasLeft (GasMeter.start msg.gas msg.reservoir : StateGasMeter) = msg.gas :=
    rfl
  rw [hgl] at start
  obtain ⟨z, hr, hz, hq⟩ := (mirror_specA hberlin hk rfl hg).toG _ start
  obtain ⟨s, hs, hzs, hle⟩ := Shadow.dom_run (runChild := ProcessMeter.processRunnerM fork msg.gas)
    hberlin hr hz hq.2.1 _ rfl (Nat.le_refl _) (Nat.le_of_eq (LawfulGasMeter.gasHeld_start _ _))
  have hse : s.error = none := by
    have : z.error = s.error := by rw [hzs]; rfl
    rw [← this]; exact hq.2.1
  rw [← hst] at hs
  have hmap := ProcessMeter.processMessage_map_valM (fun h => h.2 hv) hpre hs
  rw [← hp] at hmap
  rcases hch : ProcessMeter.processRunnerM fork bound caller msg lt with e | child
  · rw [hch] at hmap; cases hmap
  rw [hch] at hmap
  simp only [Except.map, Except.ok.injEq] at hmap
  have hc : child.1 = s := by
    rw [hmap]
    unfold rollbackOnError
    simp [hse]
  refine ⟨child, rfl, by rw [hc]; exact hse, ?_⟩
  rw [hc]
  have hzg : z.gas = msg.gas - (87 + slotCost (coldIn caller.substate.child msg.currentTarget
      (mapSlot k 2))) := hq.2.2.2.1
  omega

/-- `destroyBlackFunds(a)` from the owner `CALLER_A` to `C`, with the gas `G` and the reservoir `R`
in the fields of the message (`mDO` has 0 for both). -/
def mDOG (b : BlockEnvironment fork) (t : TransactionEnvironment fork) (C : Address) (a : U256)
    (G R : Nat) : Message fork :=
  { mDO b t C a with gas := G, reservoir := R }

/-- `destroy_mirror_runsG` from any state `S` whose slot 10 at `C` is `W`, with the owner
`CALLER_A`, `a` blacklisted, `MIRROR` at `UA` and an account at `C` (round 45; `S2 C H a` is one,
and so is `S2 C H a` with reads recorded). -/
theorem destroy_mirror_runsT (hparis : .paris ≤ fork) (G R : Nat)
    (b : BlockEnvironment fork) (t : TransactionEnvironment fork) (C : Address) (a : U256)
    (ss : Substate) {S : State.TransactionState} (hS10 : storageAt S C 10 = W)
    (hown : IsOwner S (mDOG b t C a G R))
    (hlist : (storageAt S (mDOG b t C a G R).currentTarget
      (listSlot (addrArg (mDOG b t C a G R).data 0))).toNat % 256 ≠ 0)
    (hcodeU : S.getCode (S.getAccount UA).codeHash = .ok MIRROR) (hacc : hasAccount S C)
    {m : Evm fork StateGasMeter}
    (start : At CODE (mDOG b t C a G R) 0 [] .empty m.gas.gasLeft S ss (toNat m))
    (hg : 1000000 ≤ m.gas.gasLeft) (hg' : m.gas.gasLeft < 2 ^ 255) {bound : Nat}
    (within : GasMeter.gasHeld m.gas ≤ bound) :
    Shadow.RunsOkS fork bound (ProcessMeter.processRunnerM fork bound) m within := by
  have hberlin : .berlin ≤ fork := Nat.le_trans (by decide) hparis
  have hdep : byte20 (storageAt S (mDOG b t C a G R).currentTarget 10) ≠ 0 := by
    show byte20 (storageAt S C 10) ≠ 0
    rw [hS10]; decide
  have hup : upAddr S (mDOG b t C a G R) = UA := by
    show toAddressMasked (upWord (storageAt S C 10)) = UA
    rw [hS10]; rfl
  have hcodeUA : S.getCode (S.getAccount (upAddr S (mDOG b t C a G R))).codeHash = .ok MIRROR := by
    rw [hup]; exact hcodeU
  have h4 : 4 ≤ (mDOG b t C a G R).data.size := by
    show 4 ≤ (data1 SEL_D a).size
    rw [size_data1 size_SEL_D]; decide
  have hsize' : (mDOG b t C a G R).data.size < 2 ^ 256 := by
    show (data1 SEL_D a).size < 2 ^ 256
    rw [size_data1 size_SEL_D]; decide
  have hsel : selector (mDOG b t C a G R).data = 0xf3bdc228 := by
    show selector (data1 SEL_D a) = _
    rw [selector_data1 size_SEL_D]; decide
  have hs0 := slotCost_le (coldIn ss (mDOG b t C a G R).currentTarget 0)
  have hsL := slotCost_le (coldIn (accessSlot ss (mDOG b t C a G R).currentTarget 0)
    (mDOG b t C a G R).currentTarget (listSlot (addrArg (mDOG b t C a G R).data 0)))
  have hs10 := slotCost_le (coldIn (preSub ss (mDOG b t C a G R)) (mDOG b t C a G R).currentTarget 10)
  -- pc 0 to EXTCODESIZE
  obtain ⟨m1, hat1, hg1, hrun1⟩ := fwd_splitS
    (fun g hg => prefixG_destroy hberlin h4 hsize' hsel rfl hown hlist hdep rfl rfl rfl hg)
    (by omega) (fun _ _ => rfl) (by omega) start
  -- EXTCODESIZE to the CALL
  have hM : extendMemory (memD (mDOG b t C a G R)).size
      [((0x60 : U256), (0x24 : U256)), ((0x60 : U256), (0x20 : U256))] = ⟨0, 0⟩ := by
    rw [size_memD]; decide
  have hA := extCost_le hberlin
    (decide (toAddressMasked (upWord (storageAt (S) (mDOG b t C a G R).currentTarget 10)) ∉
      (accessSlot (preSub ss (mDOG b t C a G R)) (mDOG b t C a G R).currentTarget 10).accessedAddresses))
  obtain ⟨mC, caller, msg, hgC, hrC, hrunC, hstepC, k1, k2, k3, k4, k5, k6, k7, k8, k9, ko, k10,
      k11, m0, mg, mcl, mct, mtg, mca, mcode, mdp, md, mv, mdep, mst, mbe, mte, msh⟩ :=
    fromExtS (message := mDOG b t C a G R)
      (U := upWord (storageAt (S) (mDOG b t C a G R).currentTarget 10))
      (rest := [0x84, 0x70a08231, upWord (storageAt (S) (mDOG b t C a G R).currentTarget 10), 0,
        addrArg (mDOG b t C a G R).data 0, 0x1f48, 0, addrArg (mDOG b t C a G R).data 0, 0x09b6,
        BitVec.ofNat 256 (selector (mDOG b t C a G R).data)])
      (st := readSlot (preState (S) (mDOG b t C a G R)) (mDOG b t C a G R).currentTarget 10)
      (ss := accessSlot (preSub ss (mDOG b t C a G R)) (mDOG b t C a G R).currentTarget 10)
      (r := none) (R := 0)
      hberlin (by simp) hM hcodeUA (by rw [size_MIRROR]; decide) (fun _ => delegatedAddress_mirror)
      (by show 0 + 1 ≤ STACK_DEPTH_LIMIT; decide) rfl rfl (by omega) hat1
  -- the message to `MIRROR`
  have hpre : precompileAddress fork msg = none :=
    precompile_none_of (fork := fork) (by
      show Precompiles.isPrecompile fork (upAddr (S) (mDOG b t C a G R)).toU256.toNat = false
      rw [hup]; exact hnp_UA fork) mca
  have hk : loadWord msg.data 4 32 = addrArg (mDOG b t C a G R).data 0 := by
    rw [md, data_memD]; exact loadWord_append_wordBytes SEL_B _
  generalize hG4 : m.gas.gasLeft - (1472 + slotCost (coldIn ss (mDOG b t C a G R).currentTarget 0) +
    slotCost (coldIn (accessSlot ss (mDOG b t C a G R).currentTarget 0) (mDOG b t C a G R).currentTarget
      (listSlot (addrArg (mDOG b t C a G R).data 0))) +
    slotCost (coldIn (preSub ss (mDOG b t C a G R)) (mDOG b t C a G R).currentTarget 10)) -
    (extCost fork (decide (toAddressMasked (upWord (storageAt (S)
      (mDOG b t C a G R).currentTarget 10)) ∉ (accessSlot (preSub ss (mDOG b t C a G R))
        (mDOG b t C a G R).currentTarget 10).accessedAddresses)) + 28) = G4 at k7 mg
  have e25 : m.gas.gasLeft - (1472 + slotCost (coldIn ss (mDOG b t C a G R).currentTarget 0) +
    slotCost (coldIn (accessSlot ss (mDOG b t C a G R).currentTarget 0) (mDOG b t C a G R).currentTarget
      (listSlot (addrArg (mDOG b t C a G R).data 0))) +
    slotCost (coldIn (preSub ss (mDOG b t C a G R)) (mDOG b t C a G R).currentTarget 10)) -
    (extCost fork (decide (toAddressMasked (upWord (storageAt (S)
      (mDOG b t C a G R).currentTarget 10)) ∉ (accessSlot (preSub ss (mDOG b t C a G R))
        (mDOG b t C a G R).currentTarget 10).accessedAddresses)) + 25) = G4 + 3 := by omega
  rw [e25] at k7 mg
  obtain ⟨hsub, hcost, hsub'⟩ := callGas_bounds hberlin (G := G4) (by omega) (by omega)
  have hmir : 87 + slotCost (coldIn caller.substate.child msg.currentTarget
      (mapSlot (addrArg (mDOG b t C a G R).data 0) 2)) ≤ msg.gas := by
    have := slotCost_le (coldIn caller.substate.child msg.currentTarget
      (mapSlot (addrArg (mDOG b t C a G R).data 0) 2))
    rw [mg]; omega
  have hdec := step_decreases fork hrC hstepC
  obtain ⟨w1, e1⟩ := hrun1 within
  obtain ⟨wC, eC⟩ := hrunC w1
  have lt : msg.gas < bound := Nat.lt_of_lt_of_le hdec.1 wC
  obtain ⟨chS, hch, he, hchg⟩ := process_mirrorS_ok hparis caller lt mcode mtg mv hpre hk hmir
  -- the resume
  have hlenC : caller.stack.val.length < STACK_LIMIT := by rw [k5]; simp [STACK_LIMIT]
  obtain ⟨y, hy, -, -, -, -, -, -, hgy, -⟩ := resumeCall_okS (o := 0x60) (osz := 0x20) hlenC he
  obtain ⟨wy, ey⟩ := runFrame_child_fwdS (within := wC) hrC hstepC lt hch hy
  have hat := resumeD (message := mDOG b t C a G R) (by simp) k1 k2 k3 k4 k5 k6 k8 k9 ko hy
  simp only [he, Option.isNone_none, ↓reduceIte] at hat
  -- the tail
  have hB := size_memD (mDOG b t C a G R)
  have hacc : hasAccount (incorporateChild fork caller chS.1).state (mDOG b t C a G R).currentTarget := by
    have h0 : hasAccount (readSlot (preState (S) (mDOG b t C a G R)) C 10) C :=
      hasAccount_readSlot (hasAccount_readSlot (hasAccount_readSlot hacc))
    obtain ⟨-, hs⟩ := process_mirrorS hparis caller lt mcode mtg mv hpre hk hch he
    rw [Security.state_incorporateChildS, hs]
    refine hasAccount_readSlot ?_
    rw [k10]
    simp only [routeState, hasAccount, State.TransactionState.getAccountOptional_recordAccountRead]
    exact h0
  obtain ⟨hiff, -⟩ := tailD_sgm hberlin (mkey_addrArg (mDOG b t C a G R).data 0) rfl hacc
    (size_outMemOf hB chS.1.output)
    (mload_outMemOf hB (by rw [memoryExtend_zero]; exact ptr_memD (mDOG b t C a G R)) chS.1.output)
    rfl rfl hat (runChild := ProcessMeter.processRunnerM fork bound) wy
  have hgA := absorb_gasLeft_ge caller.gas chS.1.gas
  rw [← hgy] at hgA
  have hcl : caller.gas.gasLeft = G4 - (depCallGas fork (asked (G4 + 3)) G4 0).cost := by rw [k7]
  rw [hcost] at hcl
  have hchg2 : (depCallGas fork (asked (G4 + 3)) G4 0).subCall - (87 + slotCost (coldIn
      caller.substate.child msg.currentTarget (mapSlot (addrArg (mDOG b t C a G R).data 0) 2))) ≤
      chS.1.gas.gasLeft := by rw [← mg]; exact hchg
  have hsl := slotCost_le (coldIn caller.substate.child msg.currentTarget
    (mapSlot (addrArg (mDOG b t C a G R).data 0) 2))
  have hyg : 986000 ≤ y.gas.gasLeft := by omega
  have hW := writeCost_le hberlin
  have hWm : writeMax fork ≤ 110020 := by unfold writeMax; split <;> omega
  have o1 : wOk fork y.gas 184
      (originalAt (incorporateChild fork caller chS.1).state (mDOG b t C a G R).currentTarget
        (mapSlot (addrArg (mDOG b t C a G R).data 0) 2))
      (storageAt (incorporateChild fork caller chS.1).state (mDOG b t C a G R).currentTarget
        (mapSlot (addrArg (mDOG b t C a G R).data 0) 2)) 0
      (coldIn (incorporateChild fork caller chS.1).substate (mDOG b t C a G R).currentTarget
        (mapSlot (addrArg (mDOG b t C a G R).data 0) 2)) := by
    have := hW (originalAt (incorporateChild fork caller chS.1).state (mDOG b t C a G R).currentTarget
        (mapSlot (addrArg (mDOG b t C a G R).data 0) 2))
      (storageAt (incorporateChild fork caller chS.1).state (mDOG b t C a G R).currentTarget
        (mapSlot (addrArg (mDOG b t C a G R).data 0) 2)) 0
      (coldIn (incorporateChild fork caller chS.1).substate (mDOG b t C a G R).currentTarget
        (mapSlot (addrArg (mDOG b t C a G R).data 0) 2))
    exact ⟨by omega, by omega⟩
  have g1 := wMeter_gasLeft o1
  have o2 : wOk fork (tailDM1 fork y.gas (incorporateChild fork caller chS.1).state
        (mDOG b t C a G R).currentTarget (addrArg (mDOG b t C a G R).data 0)
        (coldIn (incorporateChild fork caller chS.1).substate (mDOG b t C a G R).currentTarget
          (mapSlot (addrArg (mDOG b t C a G R).data 0) 2)))
      (33 + slotCost (coldIn (accessSlot (incorporateChild fork caller chS.1).substate
        (mDOG b t C a G R).currentTarget (mapSlot (addrArg (mDOG b t C a G R).data 0) 2))
        (mDOG b t C a G R).currentTarget 1))
      (originalAt (incorporateChild fork caller chS.1).state (mDOG b t C a G R).currentTarget 1)
      (storageAt (writeSlot (incorporateChild fork caller chS.1).state (mDOG b t C a G R).currentTarget
        (mapSlot (addrArg (mDOG b t C a G R).data 0) 2) 0) (mDOG b t C a G R).currentTarget 1)
      (sub (storageAt (writeSlot (incorporateChild fork caller chS.1).state
        (mDOG b t C a G R).currentTarget (mapSlot (addrArg (mDOG b t C a G R).data 0) 2) 0)
        (mDOG b t C a G R).currentTarget 1) (resWord (outMemOf (memD (mDOG b t C a G R)) chS.1.output)))
      false := by
    have := hW (originalAt (incorporateChild fork caller chS.1).state (mDOG b t C a G R).currentTarget 1)
      (storageAt (writeSlot (incorporateChild fork caller chS.1).state (mDOG b t C a G R).currentTarget
        (mapSlot (addrArg (mDOG b t C a G R).data 0) 2) 0) (mDOG b t C a G R).currentTarget 1)
      (sub (storageAt (writeSlot (incorporateChild fork caller chS.1).state
        (mDOG b t C a G R).currentTarget (mapSlot (addrArg (mDOG b t C a G R).data 0) 2) 0)
        (mDOG b t C a G R).currentTarget 1) (resWord (outMemOf (memD (mDOG b t C a G R)) chS.1.output)))
      false
    have := slotCost_le (coldIn (accessSlot (incorporateChild fork caller chS.1).substate
        (mDOG b t C a G R).currentTarget (mapSlot (addrArg (mDOG b t C a G R).data 0) 2))
        (mDOG b t C a G R).currentTarget 1)
    have := hW (originalAt (incorporateChild fork caller chS.1).state (mDOG b t C a G R).currentTarget
        (mapSlot (addrArg (mDOG b t C a G R).data 0) 2))
      (storageAt (incorporateChild fork caller chS.1).state (mDOG b t C a G R).currentTarget
        (mapSlot (addrArg (mDOG b t C a G R).data 0) 2)) 0
      (coldIn (incorporateChild fork caller chS.1).substate (mDOG b t C a G R).currentTarget
        (mapSlot (addrArg (mDOG b t C a G R).data 0) 2))
    simp only [tailDM1] at g1 ⊢
    exact ⟨by omega, by omega⟩
  have g2 := wMeter_gasLeft o2
  obtain ⟨s, hs, hok⟩ := hiff.mpr ⟨o1, o2, by
    have := hW (originalAt (incorporateChild fork caller chS.1).state (mDOG b t C a G R).currentTarget 1)
      (storageAt (writeSlot (incorporateChild fork caller chS.1).state (mDOG b t C a G R).currentTarget
        (mapSlot (addrArg (mDOG b t C a G R).data 0) 2) 0) (mDOG b t C a G R).currentTarget 1)
      (sub (storageAt (writeSlot (incorporateChild fork caller chS.1).state
        (mDOG b t C a G R).currentTarget (mapSlot (addrArg (mDOG b t C a G R).data 0) 2) 0)
        (mDOG b t C a G R).currentTarget 1) (resWord (outMemOf (memD (mDOG b t C a G R)) chS.1.output)))
      false
    have := slotCost_le (coldIn (accessSlot (incorporateChild fork caller chS.1).substate
        (mDOG b t C a G R).currentTarget (mapSlot (addrArg (mDOG b t C a G R).data 0) 2))
        (mDOG b t C a G R).currentTarget 1)
    have := hW (originalAt (incorporateChild fork caller chS.1).state (mDOG b t C a G R).currentTarget
        (mapSlot (addrArg (mDOG b t C a G R).data 0) 2))
      (storageAt (incorporateChild fork caller chS.1).state (mDOG b t C a G R).currentTarget
        (mapSlot (addrArg (mDOG b t C a G R).data 0) 2)) 0
      (coldIn (incorporateChild fork caller chS.1).substate (mDOG b t C a G R).currentTarget
        (mapSlot (addrArg (mDOG b t C a G R).data 0) 2))
    simp only [tailDM2, tailDM1] at g1 g2 ⊢
    omega⟩
  exact ⟨s, (e1.trans eC).trans (ey.trans hs), hok⟩

/-- `destroy_mirror_runsS` for the message `mDOG b t C a G R` (any gas and reservoir fields of
the message; round 45). -/
theorem destroy_mirror_runsG (hparis : .paris ≤ fork) (G R : Nat)
    (b : BlockEnvironment fork) (t : TransactionEnvironment fork) (C : Address) (a : U256)
    (ss : Substate) (H : Hash32) (hH : H ≠ State.EMPTY_CODE_HASH) {m : Evm fork StateGasMeter}
    (start : At CODE (mDOG b t C a G R) 0 [] .empty m.gas.gasLeft (S2 C H a) ss (toNat m))
    (hg : 1000000 ≤ m.gas.gasLeft) (hg' : m.gas.gasLeft < 2 ^ 255) {bound : Nat}
    (within : GasMeter.gasHeld m.gas ≤ bound) :
    Shadow.RunsOkS fork bound (ProcessMeter.processRunnerM fork bound) m within := by
  obtain ⟨-, hown0, hlist0, -, hup0, -, -, -, -⟩ := process_step_dep_hyps2 hparis b t C a H hH 0
  have hcodeU := hcode_SM (M := mDO b t C a) (C := C) (kvs := KD a) H hH hup0
  rw [hup0] at hcodeU
  exact destroy_mirror_runsT hparis G R b t C a ss (slot10_S2 C H a) hown0 hlist0 hcodeU
    (hasAccount_SM C H _) start hg hg' within

/-- **A successful deprecated destroyBlackFunds over the EIP-8037 meter, through `MIRROR`.** See
the module doc. -/
theorem destroy_mirror_runsS (hparis : .paris ≤ fork)
    (b : BlockEnvironment fork) (t : TransactionEnvironment fork) (C : Address) (a : U256)
    (ss : Substate) (H : Hash32) (hH : H ≠ State.EMPTY_CODE_HASH) {m : Evm fork StateGasMeter}
    (start : At CODE (mDO b t C a) 0 [] .empty m.gas.gasLeft (S2 C H a) ss (toNat m))
    (hg : 1000000 ≤ m.gas.gasLeft) (hg' : m.gas.gasLeft < 2 ^ 255) {bound : Nat}
    (within : GasMeter.gasHeld m.gas ≤ bound) :
    Shadow.RunsOkS fork bound (ProcessMeter.processRunnerM fork bound) m within :=
  destroy_mirror_runsG hparis 0 0 b t C a ss H hH start hg hg' within

/-- **The concrete deprecated run as a message over the EIP-8037 meter (round 45).** From Paris
(Glamsterdam included), in `S2 C H a` (`H` not the empty code hash) with `C` no precompile, the
message `destroyBlackFunds(a)` from `CALLER_A` to `C` with any gas field `G` and reservoir field
`R`, from any substate and any starting meter whose execution gas left is at least 1000000 and
below 2^255 (and whose held gas is at most `G`): EthLib's `processMessage` over `StateGasMeter`
ends with a frame with no error. (The proof runs the frame of its code by
`destroy_mirror_runsG`.) -/
theorem destroy_mirror_processS (hparis : .paris ≤ fork)
    (b : BlockEnvironment fork) (t : TransactionEnvironment fork) (C : Address) (a : U256)
    (ss : Substate) (H : Hash32) (hH : H ≠ State.EMPTY_CODE_HASH)
    (hnp : Precompiles.isPrecompile fork C.toU256.toNat = false) (G R : Nat)
    (meter : StateGasMeter) (hg : 1000000 ≤ meter.gasLeft) (hg' : meter.gasLeft < 2 ^ 255)
    (held : GasMeter.gasHeld meter ≤ (mDOG b t C a G R).gas) :
    ∃ child, processMessage fork (mDOG b t C a G R) (S2 C H a) ss meter held = .ok child ∧
      child.1.error = none := by
  have hst : startState fork (mDOG b t C a G R) (S2 C H a) = S2 C H a := by
    simp only [startState, show ¬fork < Fork.paris from Nat.not_lt.mpr hparis, ite_false]
  have start := ProcessMeter.at_startFrameS (code := CODE) (message := mDOG b t C a G R) rfl
    (startState fork (mDOG b t C a G R) (S2 C H a)) ss meter
  rw [hst] at start
  obtain ⟨s, hs, hse⟩ := destroy_mirror_runsG hparis G R b t C a ss H hH
    (m := startFrame (mDOG b t C a G R) (S2 C H a) ss meter) start hg hg' held
  rw [← hst] at hs
  have hpre : precompileAddress fork (mDOG b t C a G R) = none :=
    precompile_none_of (fork := fork) hnp rfl
  have hmap := ProcessMeter.processMessage_map_valM (fun h => h.2 rfl) hpre hs
  rcases hch : processMessage fork (mDOG b t C a G R) (S2 C H a) ss meter held with e | child
  · rw [hch] at hmap; cases hmap
  rw [hch] at hmap
  simp only [Except.map, Except.ok.injEq] at hmap
  refine ⟨child, rfl, ?_⟩
  rw [hmap]
  unfold rollbackOnError
  simp [hse]

end UsdtVerify.Sanity
