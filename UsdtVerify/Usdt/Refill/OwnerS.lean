import UsdtVerify.Usdt.Spec.Pause
import UsdtVerify.Usdt.Spec.AddrWrite
import UsdtVerify.Evm.Chain

/-!
# The owner functions with one write over the EIP-8037 meter: exact success condition and gas (round 43)

pause, unpause, addBlackList, removeBlackList and transferOwnership (`a ≠ 0`) by the owner write
one slot. Each success path is split at its SSTORE into a cheap stretch from pc 0 (`P` gas) and a
cheap stretch from the instruction after the SSTORE to the STOP (`T` gas), and
`Complete.one_write_sgm` applies. Over `StateGasMeter`, from a frame `m` with any meter, for any
gas bound and message runner:

- `pause_sgm`, `unpause_sgm`, `addBlackList_sgm`, `removeBlackList_sgm`, `transferOwnership_sgm`:
  under the guard of the Nat success specification, the run ends with no error if and only if
  `P + 2301 ≤ gas` (more than 2300 execution gas at the SSTORE) and the gas of the Nat
  specification is at most `gas + wBump`, where `wBump` (`sstoreBump`) is the execution gas the
  write gains from a refill and from the reservoir paying its state gas. Every run that ends with
  no error ends as the Nat specification says (output, state, substate), with
  `gasLeft + cost = gas + wBump` and the meter `wSgm` (`sstoreMeter`) of the write for the
  reservoir and the spill.

No hypothesis on refills or on the reservoir. `gas` is the execution gas left of the first frame.
deprecate writes slot 10 twice: it is a chain of two writes, in Usdt/Refill/ChainOwner.lean.
-/

namespace UsdtVerify.PauseSpec

open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts
open Owner Pause
open Complete (wBump wSgm)

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate}

/-- At 5055 (pause): from the `JUMPDEST` to the `SSTORE` of slot 0 at 5081. -/
theorem pauseToW (hfork : .berlin ≤ fork) {rest : List U256}
    (hrest : rest.length ≤ 16)
    (hc0 : coldIn substate message.currentTarget 0 = false) {M : ByteArray} {gas : Nat}
    (hg : 216 ≤ gas) :
    Gas.HoareG fork (At CODE message 5055 rest M gas state substate)
      (At CODE message 5081 (0 :: withPaused (storageAt state message.currentTarget 0) 1 :: 1 :: rest)
        M (gas - 216) (readSlot state message.currentTarget 0)
        (accessSlot substate message.currentTarget 0)) := by
  have hexp : exponentBytes (0x14 : U256) = 1 := by decide
  have hb : isZero (isZero (1 : U256)) = 1 := by decide
  step jumpdestR
  step pushR 1 (0x01 : U256)
  step pushR 1 (0 : U256)
  step pushR 1 (0x14 : U256)
  step pushR 2 (0x0100 : U256)
  flag_pre
  exact restate (by decide) rfl rfl (by gas_ok) rfl rfl

/-- At 4451 (unpause): from the `JUMPDEST` to the `SSTORE` of slot 0 at 4476. -/
theorem unpauseToW (hfork : .berlin ≤ fork) {rest : List U256}
    (hrest : rest.length ≤ 16)
    (hc0 : coldIn substate message.currentTarget 0 = false) {M : ByteArray} {gas : Nat}
    (hg : 216 ≤ gas) :
    Gas.HoareG fork (At CODE message 4451 rest M gas state substate)
      (At CODE message 4476 (0 :: withPaused (storageAt state message.currentTarget 0) 0 :: 0 :: rest)
        M (gas - 216) (readSlot state message.currentTarget 0)
        (accessSlot substate message.currentTarget 0)) := by
  have hexp : exponentBytes (0x14 : U256) = 1 := by decide
  have hb : isZero (isZero (0 : U256)) = 0 := by decide
  step jumpdestR
  step pushR 1 (0 : U256)
  step dupR 0
  step pushR 1 (0x14 : U256)
  step pushR 2 (0x0100 : U256)
  flag_pre
  exact restate (by decide) rfl rfl (by gas_ok) rfl rfl

/-- From pc 0 to the `SSTORE` of slot 0 in `pause()` by the owner, when not paused. -/
theorem pausePre (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x8456cb59)
    (hv : message.value = 0) (hown : callerWord message = ownerOf state message.currentTarget)
    (hnp : byte20 (storageAt state message.currentTarget 0) = 0)
    {c0 : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0) (gas : Nat)
    (hg : 996 + slotCost c0 ≤ gas) :
    Gas.HoareG fork (At CODE message 0 [] .empty gas state substate)
      (At CODE message 5081 (0 :: withPaused (storageAt state message.currentTarget 0) 1 :: 1 ::
          [BitVec.ofNat 256 0x0610, BitVec.ofNat 256 (selector message.data)]) MEM0
        (gas - (996 + slotCost c0)) (readSlot state message.currentTarget 0)
        (accessSlot substate message.currentTarget 0)) := by
  refine Triple.seq (toBody (Or.inl ⟨rfl, rfl, rfl, rfl, rfl⟩) hsize hsize' hsel hv (by omega)) ?_
  step ownerOk hfork (mem_CHECKS (by decide)) (by simp) hc0 hown (by gas_ok)
  at_pc 5027
  step pauseTest hfork (by simp) (coldIn_accessSlot_self _ _ _) (by gas_ok)
  rw [readSlot_readSlot, accessSlot_accessSlot, storageAt_readSlot]
  step flagPass (Or.inl ⟨rfl, rfl⟩) (isZero3_flag_ne hnp) (by simp) (by gas_ok)
  step pauseToW (state := readSlot state message.currentTarget 0) hfork (by simp) (coldIn_accessSlot_self _ _ _) (by gas_ok)
  rw [readSlot_readSlot, accessSlot_accessSlot, storageAt_readSlot]
  exact restate rfl rfl rfl (by gas_ok) rfl rfl

/-- From pc 0 to the `SSTORE` of slot 0 in `unpause()` by the owner, when paused. -/
theorem unpausePre (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x3f4ba83a)
    (hv : message.value = 0) (hown : callerWord message = ownerOf state message.currentTarget)
    (hp : byte20 (storageAt state message.currentTarget 0) ≠ 0)
    {c0 : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0) (gas : Nat)
    (hg : 883 + slotCost c0 ≤ gas) :
    Gas.HoareG fork (At CODE message 0 [] .empty gas state substate)
      (At CODE message 4476 (0 :: withPaused (storageAt state message.currentTarget 0) 0 :: 0 ::
          [BitVec.ofNat 256 0x04c4, BitVec.ofNat 256 (selector message.data)]) MEM0
        (gas - (883 + slotCost c0)) (readSlot state message.currentTarget 0)
        (accessSlot substate message.currentTarget 0)) := by
  refine Triple.seq (toBody (Or.inr ⟨rfl, rfl, rfl, rfl, rfl⟩) hsize hsize' hsel hv (by omega)) ?_
  step ownerOk hfork (mem_CHECKS (by decide)) (by simp) hc0 hown (by gas_ok)
  at_pc 4424
  step unpauseTest hfork (by simp) (coldIn_accessSlot_self _ _ _) (by gas_ok)
  rw [readSlot_readSlot, accessSlot_accessSlot, storageAt_readSlot]
  step flagPass (Or.inr ⟨rfl, rfl⟩) (isZero2_flag hp) (by simp) (by gas_ok)
  step unpauseToW (state := readSlot state message.currentTarget 0) hfork (by simp) (coldIn_accessSlot_self _ _ _) (by gas_ok)
  rw [readSlot_readSlot, accessSlot_accessSlot, storageAt_readSlot]
  exact restate rfl rfl rfl (by gas_ok) rfl rfl

/-- From the `POP` at 5082 after the `SSTORE` of pause to the STOP. -/
theorem postPause {x b : U256} (hstatic : message.isStatic = false) {gas : Nat}
    (hg : 788 ≤ gas) :
    Gas.SpecG fork (At CODE message 5082 [b, BitVec.ofNat 256 0x0610, x] MEM0 gas state substate)
      (Halted false .empty (gas - 788) state
        { substate with logs := substate.logs.push (log0 message.currentTarget PAUSE_TOPIC) }) := by
  refine Triple.seq (Gas.Triple.seqL popR (restate (pc' := 5083) (by decide) rfl rfl
    (g' := gas - 2) (by gas_ok) rfl rfl)) ?_
  refine (logStop (.inl ⟨rfl, rfl, rfl⟩) hstatic size_MEM0 mload_MEM0 (by omega)).consequence
    (fun _ h => h) ?_
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  exact ⟨hr, he, ho, by rw [hgas]; gas_ok, hs, hss⟩

/-- From the `POP` at 4477 after the `SSTORE` of unpause to the STOP. -/
theorem postUnpause {x b : U256} (hstatic : message.isStatic = false) {gas : Nat}
    (hg : 788 ≤ gas) :
    Gas.SpecG fork (At CODE message 4477 [b, BitVec.ofNat 256 0x04c4, x] MEM0 gas state substate)
      (Halted false .empty (gas - 788) state
        { substate with logs := substate.logs.push (log0 message.currentTarget UNPAUSE_TOPIC) }) := by
  refine Triple.seq (Gas.Triple.seqL popR (restate (pc' := 4478) (by decide) rfl rfl
    (g' := gas - 2) (by gas_ok) rfl rfl)) ?_
  refine (logStop (.inr ⟨rfl, rfl, rfl⟩) hstatic size_MEM0 mload_MEM0 (by omega)).consequence
    (fun _ h => h) ?_
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  exact ⟨hr, he, ho, by rw [hgas]; gas_ok, hs, hss⟩

/-- **pause() over the EIP-8037 meter, exactly, at any reservoir, refills allowed.** From
Berlin, from a frame `m` of `StateGasMeter` with any meter whose `toNat` is the fresh frame of
`CODE` with selector 0x8456cb59, by the owner, not paused, a frame that is not static and an
account: the run, for any gas bound and message runner, ends with no error if and only if
`996 + price(slot 0) + 2301 ≤ gas` and `1784 + price(slot 0) + price(write) ≤ gas + bump`, where
`bump` is `wBump` of the write of slot 0 from the meter `m.gas`. Every run that ends with no error
stops with the end of `spec_pause` (output, state, substate), with
`gasLeft + 1784 + price(slot 0) + price(write) = gas + bump` and the meter `wSgm` of the write for
the rest. -/
theorem pause_sgm (hfork : .berlin ≤ fork)
    (hstatic : message.isStatic = false) (hacc : hasAccount state message.currentTarget)
    (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x8456cb59)
    (hv : message.value = 0) (hown : callerWord message = ownerOf state message.currentTarget)
    (hnp : byte20 (storageAt state message.currentTarget 0) = 0)
    {c0 : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
    {gas : Nat} {m : Evm fork StateGasMeter}
    (start : At CODE message 0 [] .empty gas state substate (Meter.toNat m))
    {bound : Nat} {runChild : MessageRunner fork StateGasMeter bound}
    (within : GasMeter.gasHeld m.gas ≤ bound) :
    (Shadow.RunsOkS fork bound runChild m within ↔
      996 + slotCost c0 + 2301 ≤ gas ∧
      PAUSE_COST + slotCost c0 + flagCost fork state message 1 ≤
        gas + wBump fork m.gas (originalAt state message.currentTarget 0)
          (storageAt state message.currentTarget 0)
          (withPaused (storageAt state message.currentTarget 0) 1)) ∧
    ∀ s, Evm.runFrame (step fork) (step_decreases fork) bound runChild m within = .ok s →
      s.error = none →
      s.running = false ∧ s.output = .empty ∧
      s.state = writeSlot state message.currentTarget 0
        (withPaused (storageAt state message.currentTarget 0) 1) ∧
      s.substate = { storeSub fork substate message.currentTarget 0
            (originalAt state message.currentTarget 0) (storageAt state message.currentTarget 0)
            (withPaused (storageAt state message.currentTarget 0) 1) with
          logs := substate.logs.push (log0 message.currentTarget PAUSE_TOPIC) } ∧
      s.gas.gasLeft + (PAUSE_COST + slotCost c0 + flagCost fork state message 1) =
        gas + wBump fork m.gas (originalAt state message.currentTarget 0)
          (storageAt state message.currentTarget 0)
          (withPaused (storageAt state message.currentTarget 0) 1) ∧
      s.gas = { wSgm fork m.gas (originalAt state message.currentTarget 0)
          (storageAt state message.currentTarget 0)
          (withPaused (storageAt state message.currentTarget 0) 1) false with
          gasLeft := s.gas.gasLeft } := by
  have hP : 996 + slotCost c0 < 97920 := by have := Complete.slotCost_le c0; omega
  have hpre := pausePre hfork hsize hsize' hsel hv hown hnp hc0
  have hpost := fun g (hg : 788 ≤ g) => postPause (state := writeSlot (readSlot state
      message.currentTarget 0) message.currentTarget 0
      (withPaused (storageAt state message.currentTarget 0) 1))
    (substate := storeSub fork (accessSlot substate message.currentTarget 0) message.currentTarget 0
      (originalAt (readSlot state message.currentTarget 0) message.currentTarget 0)
      (storageAt (readSlot state message.currentTarget 0) message.currentTarget 0)
      (withPaused (storageAt state message.currentTarget 0) 1))
    (b := 1) (x := BitVec.ofNat 256 (selector message.data)) hstatic (gas := g) hg
  have hacc' := hasAccount_readSlot (n := 0) (other := message.currentTarget) hacc
  have hcold : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget 0 =
      false := coldIn_accessSlot_self _ _ _
  have hiff := Complete.one_write_sgm hfork hpre hP (fun _ _ => rfl) (by code_fact)
    (by code_fact) hstatic hacc' hcold hpost (by decide) (fun _ _ => rfl) start (runChild := runChild) within
  simp only [originalAt_readSlot, storageAt_readSlot] at hiff
  refine ⟨by rw [hiff]; simp only [flagCost, PAUSE_COST, wBump]; omega, fun s hrun hok => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := Complete.one_write_end hfork hpre hP (fun _ _ => rfl)
    (by code_fact) (by code_fact) hstatic hacc' hcold hpost (by decide) (fun _ _ => rfl) start
    hrun hok
  simp only [originalAt_readSlot, storageAt_readSlot] at h7 h8
  refine ⟨h3, h4, by rw [h5, writeSlot_readSlot _ _ hacc], by rw [h6, originalAt_readSlot, storageAt_readSlot, storeSub_accessSlot],
    by simp only [flagCost, PAUSE_COST, wBump]; omega, h8⟩

/-- **unpause() over the EIP-8037 meter, exactly, at any reservoir, refills allowed.** From
Berlin, from a frame `m` of `StateGasMeter` with any meter whose `toNat` is the fresh frame of
`CODE` with selector 0x3f4ba83a, by the owner, paused, a frame that is not static and an
account: the run, for any gas bound and message runner, ends with no error if and only if
`883 + price(slot 0) + 2301 ≤ gas` and `1671 + price(slot 0) + price(write) ≤ gas + bump`, where
`bump` is `wBump` of the write of slot 0 from the meter `m.gas`. Every run that ends with no error
stops with the end of `spec_unpause` (output, state, substate), with
`gasLeft + 1671 + price(slot 0) + price(write) = gas + bump` and the meter `wSgm` of the write for
the rest. -/
theorem unpause_sgm (hfork : .berlin ≤ fork)
    (hstatic : message.isStatic = false) (hacc : hasAccount state message.currentTarget)
    (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x3f4ba83a)
    (hv : message.value = 0) (hown : callerWord message = ownerOf state message.currentTarget)
    (hp : byte20 (storageAt state message.currentTarget 0) ≠ 0)
    {c0 : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
    {gas : Nat} {m : Evm fork StateGasMeter}
    (start : At CODE message 0 [] .empty gas state substate (Meter.toNat m))
    {bound : Nat} {runChild : MessageRunner fork StateGasMeter bound}
    (within : GasMeter.gasHeld m.gas ≤ bound) :
    (Shadow.RunsOkS fork bound runChild m within ↔
      883 + slotCost c0 + 2301 ≤ gas ∧
      UNPAUSE_COST + slotCost c0 + flagCost fork state message 0 ≤
        gas + wBump fork m.gas (originalAt state message.currentTarget 0)
          (storageAt state message.currentTarget 0)
          (withPaused (storageAt state message.currentTarget 0) 0)) ∧
    ∀ s, Evm.runFrame (step fork) (step_decreases fork) bound runChild m within = .ok s →
      s.error = none →
      s.running = false ∧ s.output = .empty ∧
      s.state = writeSlot state message.currentTarget 0
        (withPaused (storageAt state message.currentTarget 0) 0) ∧
      s.substate = { storeSub fork substate message.currentTarget 0
            (originalAt state message.currentTarget 0) (storageAt state message.currentTarget 0)
            (withPaused (storageAt state message.currentTarget 0) 0) with
          logs := substate.logs.push (log0 message.currentTarget UNPAUSE_TOPIC) } ∧
      s.gas.gasLeft + (UNPAUSE_COST + slotCost c0 + flagCost fork state message 0) =
        gas + wBump fork m.gas (originalAt state message.currentTarget 0)
          (storageAt state message.currentTarget 0)
          (withPaused (storageAt state message.currentTarget 0) 0) ∧
      s.gas = { wSgm fork m.gas (originalAt state message.currentTarget 0)
          (storageAt state message.currentTarget 0)
          (withPaused (storageAt state message.currentTarget 0) 0) false with
          gasLeft := s.gas.gasLeft } := by
  have hP : 883 + slotCost c0 < 97920 := by have := Complete.slotCost_le c0; omega
  have hpre := unpausePre hfork hsize hsize' hsel hv hown hp hc0
  have hpost := fun g (hg : 788 ≤ g) => postUnpause (state := writeSlot (readSlot state
      message.currentTarget 0) message.currentTarget 0
      (withPaused (storageAt state message.currentTarget 0) 0))
    (substate := storeSub fork (accessSlot substate message.currentTarget 0) message.currentTarget 0
      (originalAt (readSlot state message.currentTarget 0) message.currentTarget 0)
      (storageAt (readSlot state message.currentTarget 0) message.currentTarget 0)
      (withPaused (storageAt state message.currentTarget 0) 0))
    (b := 0) (x := BitVec.ofNat 256 (selector message.data)) hstatic (gas := g) hg
  have hacc' := hasAccount_readSlot (n := 0) (other := message.currentTarget) hacc
  have hcold : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget 0 =
      false := coldIn_accessSlot_self _ _ _
  have hiff := Complete.one_write_sgm hfork hpre hP (fun _ _ => rfl) (by code_fact)
    (by code_fact) hstatic hacc' hcold hpost (by decide) (fun _ _ => rfl) start (runChild := runChild) within
  simp only [originalAt_readSlot, storageAt_readSlot] at hiff
  refine ⟨by rw [hiff]; simp only [flagCost, UNPAUSE_COST, wBump]; omega, fun s hrun hok => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := Complete.one_write_end hfork hpre hP (fun _ _ => rfl)
    (by code_fact) (by code_fact) hstatic hacc' hcold hpost (by decide) (fun _ _ => rfl) start
    hrun hok
  simp only [originalAt_readSlot, storageAt_readSlot] at h7 h8
  refine ⟨h3, h4, by rw [h5, writeSlot_readSlot _ _ hacc], by rw [h6, originalAt_readSlot, storageAt_readSlot, storeSub_accessSlot],
    by simp only [flagCost, UNPAUSE_COST, wBump]; omega, h8⟩

end UsdtVerify.PauseSpec

namespace UsdtVerify.BlackListSpec

open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts
open Transfer TransferOk Owner Admin BlackList
open Complete (wBump wSgm)

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate}

/-- At 3375 / 7379: from the `JUMPDEST` to the `SSTORE` of `isBlackListed[a]` (at `p + 87`). -/
theorem listToW (hfork : .berlin ≤ fork) {p : Nat} {v : U256}
    (hp : (p = 3375 ∧ v = 1) ∨ (p = 7379 ∧ v = 0)) {a : U256} {rest : List U256}
    (hrest : rest.length ≤ 16) {cB : Bool}
    (hcB : coldIn substate message.currentTarget (listSlot a) = cB) {M : ByteArray}
    (hM : M.size = 96) {gas : Nat} (hg : 156 + slotCost cB ≤ gas) :
    Gas.HoareG fork (At CODE message p (a :: rest) M gas state substate)
      (At CODE message (p + 87) (listSlot a ::
          setLow (storageAt state message.currentTarget (listSlot a)) v :: v :: a :: rest)
        (mapMem M (mkey a) 6) (gas - (156 + slotCost cB))
        (readSlot state message.currentTarget (listSlot a))
        (accessSlot substate message.currentTarget (listSlot a))) := by
  have hexp : exponentBytes (0 : U256) = 0 := by decide
  have hff : mul (0xff : U256) 1 = 0xff := by decide
  have hv' : mul (isZero (isZero v)) 1 = v := by
    rcases hp with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> decide
  unfold setLow
  simp only [listSlot] at hcB ⊢
  rcases hp with ⟨rfl, hv⟩ | ⟨rfl, hv⟩
  all_goals
    list_pre
    exact restate (by decide) rfl rfl (by gas_ok) rfl rfl

/-- From the `POP` after the `SSTORE` of `isBlackListed[a]` (at `p + 88`) to the STOP. -/
theorem listPost {q : Nat} {t : U256} {r : Nat}
    (hq : (q = 3463 ∧ t = ADDED_TOPIC ∧ r = 0x0308) ∨ (q = 7467 ∧ t = REMOVED_TOPIC ∧ r = 0x091b))
    {a b x : U256} (hstatic : message.isStatic = false) {M : ByteArray} (hM : M.size = 96)
    (hptr : loadWord (memoryReadBytes M 64 32) 0 32 = 0x60) {gas : Nat} (hg : 1089 ≤ gas) :
    Gas.SpecG fork (At CODE message q [b, a, BitVec.ofNat 256 r, x] M gas state substate)
      (Halted false .empty (gas - 1089) state
        { substate with logs := substate.logs.push (log1W message.currentTarget t (mkey a)) }) := by
  rcases hq with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · refine Triple.seq (Gas.Triple.seqL popR (restate (pc' := 3464) (by decide) rfl rfl
      (g' := gas - 2) (by gas_ok) rfl rfl)) ?_
    refine (listLog (.inl ⟨rfl, rfl, rfl⟩) hstatic hM hptr (by omega)).consequence
      (fun _ h => h) ?_
    rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
    exact ⟨hr, he, ho, by rw [hgas]; gas_ok, hs, hss⟩
  · refine Triple.seq (Gas.Triple.seqL popR (restate (pc' := 7468) (by decide) rfl rfl
      (g' := gas - 2) (by gas_ok) rfl rfl)) ?_
    refine (listLog (.inr (.inl ⟨rfl, rfl, rfl⟩)) hstatic hM hptr (by omega)).consequence
      (fun _ h => h) ?_
    rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
    exact ⟨hr, he, ho, by rw [hgas]; gas_ok, hs, hss⟩

/-- From pc 0 to the `SSTORE` of `isBlackListed[a]` in addBlackList (`v = 1`) or
removeBlackList (`v = 0`). -/
theorem listPre (hfork : .berlin ≤ fork) {sel e r b t s p P : Nat} {v : U256}
    (hp : (sel = 0x0ecb93c0 ∧ e = 721 ∧ r = 0x0308 ∧ b = 3284 ∧ t = 5 ∧ s = 3288 ∧ p = 3375 ∧
        v = 1 ∧ P = 478) ∨
      (sel = 0xe4997dc5 ∧ e = 2276 ∧ r = 0x091b ∧ b = 7288 ∧ t = 29 ∧ s = 7292 ∧ p = 7379 ∧
        v = 0 ∧ P = 1006))
    (hsize : 4 ≤ message.data.size) (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = sel) (hv : message.value = 0)
    (hown : callerWord message = ownerOf state message.currentTarget)
    {c0 cB : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hcB : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget
      (listSlot (addrArg message.data 0)) = cB) (gas : Nat)
    (hg : P + slotCost c0 + slotCost cB ≤ gas) :
    Gas.HoareG fork (At CODE message 0 [] .empty gas state substate)
      (At CODE message (p + 87) (listSlot (addrArg message.data 0) ::
          setLow (storageAt state message.currentTarget (listSlot (addrArg message.data 0))) v ::
          v :: addrArg message.data 0 :: [BitVec.ofNat 256 r, BitVec.ofNat 256 (selector message.data)])
        (mapMem MEM0 (mkey (addrArg message.data 0)) 6) (gas - (P + slotCost c0 + slotCost cB))
        (readSlot (readSlot state message.currentTarget 0) message.currentTarget
          (listSlot (addrArg message.data 0)))
        (accessSlot (accessSlot substate message.currentTarget 0) message.currentTarget
          (listSlot (addrArg message.data 0)))) := by
  have hent : (e, r, b) ∈ ENTRY1 ∧ b ∈ BODIES ∧ s = b + 4 ∧ s ∈ CHECKS ∧ s + 87 = p ∧
      (p = 3375 ∧ v = 1 ∨ p = 7379 ∧ v = 0) ∧ P = 143 + 22 * t + 69 + 156 := by
    rcases hp with ⟨-, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ | ⟨-, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · exact ⟨by decide, by decide, rfl, by decide, rfl, .inl ⟨rfl, rfl⟩, rfl⟩
    · exact ⟨by decide, by decide, rfl, by decide, rfl, .inr ⟨rfl, rfl⟩, rfl⟩
  obtain ⟨hent, hb, hsb, hs, hsp, hpv, hP⟩ := hent
  have htb : tested (BitVec.ofNat 256 (selector message.data)) ENTRIES = t ∧
      branch (BitVec.ofNat 256 (selector message.data)) 54 (entrySize 4 2) ENTRIES = e := by
    rw [hsel]
    rcases hp with ⟨rfl, rfl, -, -, rfl, -⟩ | ⟨rfl, rfl, -, -, rfl, -⟩ <;> decide
  refine Triple.seq (toBody1 hent hb htb hsize hsize' hv (by omega)) ?_
  rw [← hsb]
  step ownerOk hfork hs (by simp) hc0 hown (by gas_ok)
  rw [hsp]
  refine Triple.seq (listToW (state := readSlot state message.currentTarget 0) hfork hpv (by simp)
    hcB size_MEM0 (by gas_ok)) ?_
  rw [storageAt_readSlot]
  exact restate rfl rfl rfl (by gas_ok) rfl rfl

/-- The two success paths of addBlackList (`v = 1`) and removeBlackList (`v = 0`) over
`StateGasMeter`, exactly, at any reservoir. See `addBlackList_sgm`. -/
theorem list_sgm (hfork : .berlin ≤ fork) {sel e r b t s p P : Nat} {v tp : U256}
    (hp : (sel = 0x0ecb93c0 ∧ e = 721 ∧ r = 0x0308 ∧ b = 3284 ∧ t = 5 ∧ s = 3288 ∧ p = 3375 ∧
        v = 1 ∧ P = 478 ∧ tp = ADDED_TOPIC) ∨
      (sel = 0xe4997dc5 ∧ e = 2276 ∧ r = 0x091b ∧ b = 7288 ∧ t = 29 ∧ s = 7292 ∧ p = 7379 ∧
        v = 0 ∧ P = 1006 ∧ tp = REMOVED_TOPIC))
    (hstatic : message.isStatic = false) (hacc : hasAccount state message.currentTarget)
    (hsize : 4 ≤ message.data.size) (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = sel) (hv : message.value = 0)
    (hown : callerWord message = ownerOf state message.currentTarget)
    {c0 cB : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hcB : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget
      (listSlot (addrArg message.data 0)) = cB)
    {gas : Nat} {m : Evm fork StateGasMeter}
    (start : At CODE message 0 [] .empty gas state substate (Meter.toNat m))
    {bound : Nat} {runChild : MessageRunner fork StateGasMeter bound}
    (within : GasMeter.gasHeld m.gas ≤ bound) :
    (Shadow.RunsOkS fork bound runChild m within ↔
      P + slotCost c0 + slotCost cB + 2301 ≤ gas ∧
      P + 1089 + slotCost c0 + slotCost cB + listCost fork state message v ≤
        gas + wBump fork m.gas
          (originalAt state message.currentTarget (listSlot (addrArg message.data 0)))
          (storageAt state message.currentTarget (listSlot (addrArg message.data 0)))
          (setLow (storageAt state message.currentTarget (listSlot (addrArg message.data 0))) v)) ∧
    ∀ s, Evm.runFrame (step fork) (step_decreases fork) bound runChild m within = .ok s →
      s.error = none →
      s.running = false ∧ s.output = .empty ∧ s.state = listState state message v ∧
      s.substate = listSub fork substate state message v tp ∧
      s.gas.gasLeft + (P + 1089 + slotCost c0 + slotCost cB + listCost fork state message v) =
        gas + wBump fork m.gas
          (originalAt state message.currentTarget (listSlot (addrArg message.data 0)))
          (storageAt state message.currentTarget (listSlot (addrArg message.data 0)))
          (setLow (storageAt state message.currentTarget (listSlot (addrArg message.data 0))) v) ∧
      s.gas = { wSgm fork m.gas
          (originalAt state message.currentTarget (listSlot (addrArg message.data 0)))
          (storageAt state message.currentTarget (listSlot (addrArg message.data 0)))
          (setLow (storageAt state message.currentTarget (listSlot (addrArg message.data 0))) v)
          false with gasLeft := s.gas.gasLeft } := by
  rcases hp with ⟨rfl, rfl, rfl, rfl, rfl, rfl, hp0, hv1, hP0, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, hp0, hv1, hP0, rfl⟩
  all_goals
    have hP : P + slotCost c0 + slotCost cB < 97920 := by
      have := Complete.slotCost_le c0; have := Complete.slotCost_le cB; omega
    have hpre := listPre (fork := fork) hfork (by first
      | exact .inl ⟨rfl, rfl, rfl, rfl, rfl, rfl, hp0, hv1, hP0⟩
      | exact .inr ⟨rfl, rfl, rfl, rfl, rfl, rfl, hp0, hv1, hP0⟩) hsize hsize' hsel hv hown hc0 hcB
    have hpost := fun g (hg : 1089 ≤ g) => listPost (fork := fork) (message := message)
      (state := writeSlot (readSlot (readSlot state message.currentTarget 0) message.currentTarget
        (listSlot (addrArg message.data 0))) message.currentTarget
        (listSlot (addrArg message.data 0))
        (setLow (storageAt state message.currentTarget (listSlot (addrArg message.data 0))) v))
      (substate := storeSub fork (accessSlot (accessSlot substate message.currentTarget 0)
          message.currentTarget (listSlot (addrArg message.data 0))) message.currentTarget
        (listSlot (addrArg message.data 0))
        (originalAt (readSlot (readSlot state message.currentTarget 0) message.currentTarget
          (listSlot (addrArg message.data 0))) message.currentTarget
          (listSlot (addrArg message.data 0)))
        (storageAt (readSlot (readSlot state message.currentTarget 0) message.currentTarget
          (listSlot (addrArg message.data 0))) message.currentTarget
          (listSlot (addrArg message.data 0)))
        (setLow (storageAt state message.currentTarget (listSlot (addrArg message.data 0))) v))
      (q := p + 87 + 1)
      (by subst hp0; first | exact .inl ⟨rfl, rfl, rfl⟩ | exact .inr ⟨rfl, rfl, rfl⟩)
      (a := addrArg message.data 0) (b := v) (x := BitVec.ofNat 256 (selector message.data))
      hstatic (M := mapMem MEM0 (mkey (addrArg message.data 0)) 6) (size_mapMem size_MEM0 _ _)
      (ptr_mapMem size_MEM0 mload_MEM0 _ _) (gas := g) hg
    have hacc0 := hasAccount_readSlot (n := 0) (other := message.currentTarget) hacc
    have hacc' := hasAccount_readSlot (n := listSlot (addrArg message.data 0))
      (other := message.currentTarget) hacc0
    have hcold : coldIn (accessSlot (accessSlot substate message.currentTarget 0)
        message.currentTarget (listSlot (addrArg message.data 0))) message.currentTarget
        (listSlot (addrArg message.data 0)) = false := coldIn_accessSlot_self _ _ _
    have hiff := Complete.one_write_sgm hfork hpre hP (fun _ _ => rfl) (by subst hp0; code_fact)
      (by subst hp0; code_fact) hstatic hacc' hcold hpost (by decide) (fun _ _ => rfl) start
      (runChild := runChild) within
    simp only [originalAt_readSlot, storageAt_readSlot] at hiff
    refine ⟨by rw [hiff]; simp only [listCost, wBump]; omega, fun s hrun hok => ?_⟩
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := Complete.one_write_end hfork hpre hP
      (fun _ _ => rfl) (by subst hp0; code_fact) (by subst hp0; code_fact) hstatic hacc' hcold hpost (by decide)
      (fun _ _ => rfl) start hrun hok
    simp only [originalAt_readSlot, storageAt_readSlot] at h7 h8
    refine ⟨h3, h4, by rw [h5, writeSlot_readSlot _ _ hacc0], ?_,
      by simp only [listCost, wBump]; omega, h8⟩
    rw [h6, originalAt_readSlot, originalAt_readSlot, storageAt_readSlot, storageAt_readSlot,
      storeSub_accessSlot, mkey_addrArg]

/-- **addBlackList(a) over the EIP-8037 meter, exactly, at any reservoir, refills allowed.** From
Berlin, from a frame `m` of `StateGasMeter` with any meter whose `toNat` is the fresh frame of
`CODE`, by the owner, a frame that is not static and an account, for any gas bound and message
runner: the run ends with no error if and only if `478 + price(slot 0) + price(L) + 2301 ≤ gas`
and `1567 + price(slot 0) + price(L) + price(write) ≤ gas + bump`; every run that ends with no
error ends as `spec_add` says with `gasLeft + 1567 + … = gas + bump` and the meter `wSgm` of the
write. -/
theorem addBlackList_sgm (hfork : .berlin ≤ fork)
    (hstatic : message.isStatic = false) (hacc : hasAccount state message.currentTarget)
    (hsize : 4 ≤ message.data.size) (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x0ecb93c0) (hv : message.value = 0)
    (hown : callerWord message = ownerOf state message.currentTarget)
    {c0 cB : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hcB : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget
      (listSlot (addrArg message.data 0)) = cB)
    {gas : Nat} {m : Evm fork StateGasMeter}
    (start : At CODE message 0 [] .empty gas state substate (Meter.toNat m))
    {bound : Nat} {runChild : MessageRunner fork StateGasMeter bound}
    (within : GasMeter.gasHeld m.gas ≤ bound) :
    (Shadow.RunsOkS fork bound runChild m within ↔
      478 + slotCost c0 + slotCost cB + 2301 ≤ gas ∧
      1567 + slotCost c0 + slotCost cB + listCost fork state message 1 ≤
        gas + wBump fork m.gas
          (originalAt state message.currentTarget (listSlot (addrArg message.data 0)))
          (storageAt state message.currentTarget (listSlot (addrArg message.data 0)))
          (setLow (storageAt state message.currentTarget (listSlot (addrArg message.data 0))) 1)) ∧
    ∀ s, Evm.runFrame (step fork) (step_decreases fork) bound runChild m within = .ok s →
      s.error = none →
      s.running = false ∧ s.output = .empty ∧ s.state = listState state message 1 ∧
      s.substate = listSub fork substate state message 1 ADDED_TOPIC ∧
      s.gas.gasLeft + (1567 + slotCost c0 + slotCost cB + listCost fork state message 1) =
        gas + wBump fork m.gas
          (originalAt state message.currentTarget (listSlot (addrArg message.data 0)))
          (storageAt state message.currentTarget (listSlot (addrArg message.data 0)))
          (setLow (storageAt state message.currentTarget (listSlot (addrArg message.data 0))) 1) ∧
      s.gas = { wSgm fork m.gas
          (originalAt state message.currentTarget (listSlot (addrArg message.data 0)))
          (storageAt state message.currentTarget (listSlot (addrArg message.data 0)))
          (setLow (storageAt state message.currentTarget (listSlot (addrArg message.data 0))) 1)
          false with gasLeft := s.gas.gasLeft } :=
  list_sgm hfork (.inl ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩) hstatic hacc hsize
    hsize' hsel hv hown hc0 hcB start within

/-- **removeBlackList(a) over the EIP-8037 meter, exactly, at any reservoir, refills allowed.** From
Berlin, from a frame `m` of `StateGasMeter` with any meter whose `toNat` is the fresh frame of
`CODE`, by the owner, a frame that is not static and an account, for any gas bound and message
runner: the run ends with no error if and only if `1006 + price(slot 0) + price(L) + 2301 ≤ gas`
and `2095 + price(slot 0) + price(L) + price(write) ≤ gas + bump`; every run that ends with no
error ends as `spec_remove` says with `gasLeft + 2095 + … = gas + bump` and the meter `wSgm` of the
write. -/
theorem removeBlackList_sgm (hfork : .berlin ≤ fork)
    (hstatic : message.isStatic = false) (hacc : hasAccount state message.currentTarget)
    (hsize : 4 ≤ message.data.size) (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0xe4997dc5) (hv : message.value = 0)
    (hown : callerWord message = ownerOf state message.currentTarget)
    {c0 cB : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hcB : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget
      (listSlot (addrArg message.data 0)) = cB)
    {gas : Nat} {m : Evm fork StateGasMeter}
    (start : At CODE message 0 [] .empty gas state substate (Meter.toNat m))
    {bound : Nat} {runChild : MessageRunner fork StateGasMeter bound}
    (within : GasMeter.gasHeld m.gas ≤ bound) :
    (Shadow.RunsOkS fork bound runChild m within ↔
      1006 + slotCost c0 + slotCost cB + 2301 ≤ gas ∧
      2095 + slotCost c0 + slotCost cB + listCost fork state message 0 ≤
        gas + wBump fork m.gas
          (originalAt state message.currentTarget (listSlot (addrArg message.data 0)))
          (storageAt state message.currentTarget (listSlot (addrArg message.data 0)))
          (setLow (storageAt state message.currentTarget (listSlot (addrArg message.data 0))) 0)) ∧
    ∀ s, Evm.runFrame (step fork) (step_decreases fork) bound runChild m within = .ok s →
      s.error = none →
      s.running = false ∧ s.output = .empty ∧ s.state = listState state message 0 ∧
      s.substate = listSub fork substate state message 0 REMOVED_TOPIC ∧
      s.gas.gasLeft + (2095 + slotCost c0 + slotCost cB + listCost fork state message 0) =
        gas + wBump fork m.gas
          (originalAt state message.currentTarget (listSlot (addrArg message.data 0)))
          (storageAt state message.currentTarget (listSlot (addrArg message.data 0)))
          (setLow (storageAt state message.currentTarget (listSlot (addrArg message.data 0))) 0) ∧
      s.gas = { wSgm fork m.gas
          (originalAt state message.currentTarget (listSlot (addrArg message.data 0)))
          (storageAt state message.currentTarget (listSlot (addrArg message.data 0)))
          (setLow (storageAt state message.currentTarget (listSlot (addrArg message.data 0))) 0)
          false with gasLeft := s.gas.gasLeft } :=
  list_sgm hfork (.inr ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩) hstatic hacc hsize
    hsize' hsel hv hown hc0 hcB start within

end UsdtVerify.BlackListSpec

namespace UsdtVerify.AddrWriteSpec

open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts
open Transfer TransferOk Owner Admin Issue Pause BlackList BlackListSpec AddrWrite
open Complete (wBump wSgm)

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate}

/-- At 2770 / 7755: from `PUSH2 0x0100` to the `SSTORE` of slot `k` (at `p + 58`). -/
theorem addrToW (hfork : .berlin ≤ fork) {p : Nat}
    (hp : p = 2770 ∨ p = 7755) {k a : U256} {rest : List U256} (hrest : rest.length ≤ 16)
    (hk : coldIn substate message.currentTarget k = false) {M : ByteArray} {gas : Nat}
    (hg : 156 ≤ gas) :
    Gas.HoareG fork (At CODE message p (0 :: k :: a :: a :: rest) M gas state substate)
      (At CODE message (p + 58) (k :: withAddr (storageAt state message.currentTarget k) a ::
          a :: a :: rest) M (gas - 156) (readSlot state message.currentTarget k)
        (accessSlot substate message.currentTarget k)) := by
  have hexp : exponentBytes (0 : U256) = 0 := by decide
  unfold withAddr
  rcases hp with rfl | rfl
  all_goals
    addr_pre
    exact restate (by decide) rfl rfl (by gas_ok) rfl rfl

/-- From pc 0 to the `SSTORE` of slot 0 in `transferOwnership(a)`, `a ≠ 0`, by the owner. -/
theorem ownPre (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xf2fde38b)
    (hv : message.value = 0) (hown : callerWord message = ownerOf state message.currentTarget)
    (hnz : addrArg message.data 0 ≠ 0)
    {c0 : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0) (gas : Nat)
    (hg : 1100 + slotCost c0 ≤ gas) :
    Gas.HoareG fork (At CODE message 0 [] .empty gas state substate)
      (At CODE message 7813 (0 :: withAddr (storageAt state message.currentTarget 0)
          (addrArg message.data 0) :: addrArg message.data 0 :: addrArg message.data 0 ::
          [BitVec.ofNat 256 0x097d, BitVec.ofNat 256 (selector message.data)]) MEM0
        (gas - (1100 + slotCost c0)) (readSlot state message.currentTarget 0)
        (accessSlot substate message.currentTarget 0)) := by
  refine Triple.seq (toBody1 (e := 2374) (r := 0x097d) (b := 7605) (t := 31) (by decide)
    (by decide) (by rw [hsel]; decide) hsize hsize' hv (by omega)) ?_
  step ownerOk hfork (mem_CHECKS (by decide)) (by simp) hc0 hown (by gas_ok)
  at_pc 7696
  step ownTest (by simp) (by gas_ok)
  step ownGo (by rw [addrArg, mask_mask, ← addrArg]; exact hnz) (by simp) (by gas_ok)
  refine Triple.seq (addrToW (state := readSlot state message.currentTarget 0) hfork (Or.inr rfl)
    (by simp) (coldIn_accessSlot_self _ _ _) (by gas_ok)) ?_
  rw [storageAt_readSlot, readSlot_readSlot, accessSlot_accessSlot]
  exact restate rfl rfl rfl (by gas_ok) rfl rfl

/-- From the `POP` at 7814 after the `SSTORE` of `transferOwnership` to the STOP. -/
theorem ownPost {a x : U256} {M : ByteArray} {gas : Nat} (hg : 14 ≤ gas) :
    Gas.SpecG fork (At CODE message 7814 [a, a, BitVec.ofNat 256 0x097d, x] M gas state substate)
      (Halted false .empty (gas - 14) state substate) := by
  refine Triple.seq (Gas.Triple.seqL popR (restate (pc' := 7815) (by decide) rfl rfl
    (g' := gas - 2) (by gas_ok) rfl rfl)) ?_
  refine (ownEnd (by omega)).consequence (fun _ h => h) ?_
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  exact ⟨hr, he, ho, by rw [hgas]; gas_ok, hs, hss⟩

/-- **transferOwnership(a), a ≠ 0, over the EIP-8037 meter, exactly, at any reservoir, refills
allowed.** From Berlin, from a frame `m` of `StateGasMeter` with any meter whose `toNat` is the
fresh frame of `CODE`, by the owner, a frame that is not static and an account, for any gas bound
and message runner: the run ends with no error if and only if `1100 + price(slot 0) + 2301 ≤
gas` and `1114 + price(slot 0) + price(write) ≤ gas + bump`; every run that ends with no error ends
as `spec_transferOwnership` says with `gasLeft + 1114 + … = gas + bump` and the meter `wSgm` of the
write. -/
theorem transferOwnership_sgm (hfork : .berlin ≤ fork)
    (hstatic : message.isStatic = false) (hacc : hasAccount state message.currentTarget)
    (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xf2fde38b)
    (hv : message.value = 0) (hown : callerWord message = ownerOf state message.currentTarget)
    (hnz : addrArg message.data 0 ≠ 0)
    {c0 : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
    {gas : Nat} {m : Evm fork StateGasMeter}
    (start : At CODE message 0 [] .empty gas state substate (Meter.toNat m))
    {bound : Nat} {runChild : MessageRunner fork StateGasMeter bound}
    (within : GasMeter.gasHeld m.gas ≤ bound) :
    (Shadow.RunsOkS fork bound runChild m within ↔
      1100 + slotCost c0 + 2301 ≤ gas ∧
      1114 + slotCost c0 + ownCost fork state message ≤
        gas + wBump fork m.gas (originalAt state message.currentTarget 0)
          (storageAt state message.currentTarget 0)
          (withAddr (storageAt state message.currentTarget 0) (addrArg message.data 0))) ∧
    ∀ s, Evm.runFrame (step fork) (step_decreases fork) bound runChild m within = .ok s →
      s.error = none →
      s.running = false ∧ s.output = .empty ∧
      s.state = writeSlot state message.currentTarget 0
          (withAddr (storageAt state message.currentTarget 0) (addrArg message.data 0)) ∧
      s.substate = storeSub fork substate message.currentTarget 0
          (originalAt state message.currentTarget 0) (storageAt state message.currentTarget 0)
          (withAddr (storageAt state message.currentTarget 0) (addrArg message.data 0)) ∧
      s.gas.gasLeft + (1114 + slotCost c0 + ownCost fork state message) =
        gas + wBump fork m.gas (originalAt state message.currentTarget 0)
          (storageAt state message.currentTarget 0)
          (withAddr (storageAt state message.currentTarget 0) (addrArg message.data 0)) ∧
      s.gas = { wSgm fork m.gas (originalAt state message.currentTarget 0)
          (storageAt state message.currentTarget 0)
          (withAddr (storageAt state message.currentTarget 0) (addrArg message.data 0)) false with
          gasLeft := s.gas.gasLeft } := by
  have hP : 1100 + slotCost c0 < 97920 := by have := Complete.slotCost_le c0; omega
  have hpre := ownPre hfork hsize hsize' hsel hv hown hnz hc0
  have hpost := fun g (hg : 14 ≤ g) => ownPost (fork := fork) (message := message)
    (state := writeSlot (readSlot state message.currentTarget 0) message.currentTarget 0
      (withAddr (storageAt state message.currentTarget 0) (addrArg message.data 0)))
    (substate := storeSub fork (accessSlot substate message.currentTarget 0) message.currentTarget 0
      (originalAt (readSlot state message.currentTarget 0) message.currentTarget 0)
      (storageAt (readSlot state message.currentTarget 0) message.currentTarget 0)
      (withAddr (storageAt state message.currentTarget 0) (addrArg message.data 0)))
    (a := addrArg message.data 0) (x := BitVec.ofNat 256 (selector message.data)) (M := MEM0)
    (gas := g) hg
  have hacc' := hasAccount_readSlot (n := 0) (other := message.currentTarget) hacc
  have hcold : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget 0 =
      false := coldIn_accessSlot_self _ _ _
  have hiff := Complete.one_write_sgm hfork hpre hP (fun _ _ => rfl) (by code_fact)
    (by code_fact) hstatic hacc' hcold hpost (by decide) (fun _ _ => rfl) start
    (runChild := runChild) within
  simp only [originalAt_readSlot, storageAt_readSlot] at hiff
  refine ⟨by rw [hiff]; simp only [ownCost, wBump]; omega, fun s hrun hok => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := Complete.one_write_end hfork hpre hP (fun _ _ => rfl)
    (by code_fact) (by code_fact) hstatic hacc' hcold hpost (by decide) (fun _ _ => rfl) start
    hrun hok
  simp only [originalAt_readSlot, storageAt_readSlot] at h7 h8
  refine ⟨h3, h4, by rw [h5, writeSlot_readSlot _ _ hacc],
    by rw [h6, originalAt_readSlot, storageAt_readSlot, storeSub_accessSlot],
    by simp only [ownCost, wBump]; omega, h8⟩

end UsdtVerify.AddrWriteSpec
