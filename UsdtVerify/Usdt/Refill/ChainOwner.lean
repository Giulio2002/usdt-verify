import UsdtVerify.Usdt.Refill.OwnerS
import UsdtVerify.Usdt.Refill.Owner

/-!
# The owner functions with two writes over the EIP-8037 meter: exact condition and gas (round 43)

deprecate (slot 10 twice), issue (`balances[owner]`, then `_totalSupply`), redeem (`_totalSupply`,
then `balances[owner]`), setParams (slots 3 and 4) and destroyBlackFunds (`balances[a]`, then
`_totalSupply`), by the owner, on their success paths. Each path is split at its two SSTOREs into
three cheap stretches (the Nat specification's gas, split as `P1`, `P2`, `T`), and
`Complete.exactS_write` is applied twice, then `Complete.exactS_halt`.

`deprecate_sgm`, `issue_sgm`, `redeem_sgm`, `setParams_sgm`, `destroyBlackFunds_sgm`: from a frame
with any meter, for any gas bound and message runner, under the guard of the Nat success
specification, the run ends with no error if and only if
`wOk fork m.gas P1 … ∧ wOk fork g1 P2 … ∧ T ≤ g2.gasLeft`, where `g1` is the meter after the first
write (`wMeter`) and `g2` the meter after the second. A refill of the first write goes to the
reservoir and the spill of `g1`, which the second write reads, so it can pay the state gas of the
second. Every run that ends with no error ends as the Nat specification says, with
`gasLeft + cost = gas + wBump m.gas (first write) + wBump g1 (second write)` and the meter `g2` for
the rest.

No hypothesis on refills or on the reservoir.
-/

namespace UsdtVerify.AddrWriteSpec
open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts
open Transfer TransferOk Owner Admin Issue Pause BlackList BlackListSpec AddrWrite
open Complete (wBump wSgm wOk wMeter)
variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate}

/-- At 2737 (deprecate): from the `JUMPDEST` to the first `SSTORE` of slot 10 at 2763. -/
theorem depToW (hfork : .berlin ≤ fork) {a : U256}
    {rest : List U256} (hrest : rest.length ≤ 16) {c10 : Bool}
    (hc10 : coldIn substate message.currentTarget 10 = c10) {M : ByteArray} {gas : Nat}
    (hg : 116 + slotCost c10 ≤ gas) :
    Gas.HoareG fork (At CODE message 2737 (a :: rest) M gas state substate)
      (At CODE message 2763 (0x0a :: withPaused (storageAt state message.currentTarget 10) 1 ::
          1 :: a :: rest) M (gas - (116 + slotCost c10)) (readSlot state message.currentTarget 10)
        (accessSlot substate message.currentTarget 10)) := by
  have hexp : exponentBytes (0x14 : U256) = 1 := by decide
  have hb : isZero (isZero (1 : U256)) = 1 := by decide
  unfold withPaused
  dep_pre
  exact restate (by decide) rfl rfl (by gas_ok) rfl rfl

/-- From pc 0 to the first `SSTORE` of slot 10 in `deprecate(a)` by the owner. -/
theorem depPre (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x0753c30c)
    (hv : message.value = 0) (hown : callerWord message = ownerOf state message.currentTarget)
    {c0 c10 : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hc10 : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget 10 = c10)
    (gas : Nat) (hg : 372 + slotCost c0 + slotCost c10 ≤ gas) :
    Gas.HoareG fork (At CODE message 0 [] .empty gas state substate)
      (At CODE message 2763 (0x0a :: withPaused (storageAt state message.currentTarget 10) 1 ::
          1 :: addrArg message.data 0 ::
          [BitVec.ofNat 256 0x0260, BitVec.ofNat 256 (selector message.data)]) MEM0
        (gas - (372 + slotCost c0 + slotCost c10))
        (readSlot (readSlot state message.currentTarget 0) message.currentTarget 10)
        (accessSlot (accessSlot substate message.currentTarget 0) message.currentTarget 10)) := by
  refine Triple.seq (toBody1 (e := 553) (r := 0x0260) (b := 2646) (t := 2) (by decide) (by decide)
    (by rw [hsel]; decide) hsize hsize' hv (by omega)) ?_
  step ownerOk hfork (mem_CHECKS (by decide)) (by simp) hc0 hown (by gas_ok)
  at_pc 2737
  refine Triple.seq (depToW (state := readSlot state message.currentTarget 0) hfork (by simp) hc10
    (by gas_ok)) ?_
  rw [storageAt_readSlot]
  exact restate rfl rfl rfl (by gas_ok) rfl rfl

/-- From the `POP` at 2764 after the first `SSTORE` of deprecate to the second, at 2828. -/
theorem depMid {a x : U256} (hfork : .berlin ≤ fork)
    (hk : coldIn substate message.currentTarget 10 = false) {gas : Nat} (hg : 167 ≤ gas) :
    Gas.HoareG fork (At CODE message 2764 [1, a, BitVec.ofNat 256 0x0260, x] MEM0 gas state substate)
      (At CODE message 2828 (0x0a :: withAddr (storageAt state message.currentTarget 10) a ::
          a :: a :: [BitVec.ofNat 256 0x0260, x]) MEM0 (gas - 167)
        (readSlot state message.currentTarget 10) (accessSlot substate message.currentTarget 10)) := by
  refine Triple.seq (Gas.Triple.seqL popR (restate (pc' := 2765) (by decide) rfl rfl
    (g' := gas - 2) (by gas_ok) rfl rfl)) ?_
  refine Triple.seq (depPrefix (by simp) (by omega)) ?_
  refine (addrToW hfork (Or.inl rfl) (by simp) hk (by omega)).consequence (fun _ h => h) ?_
  intro e he
  have hx : gas - 2 - 9 - 156 = gas - 167 := by omega
  rw [hx] at he
  exact he

/-- From the `POP` at 2829 after the second `SSTORE` of deprecate to the STOP. -/
theorem depPost {a x : U256} (hstatic : message.isStatic = false) {gas : Nat} (hg : 1089 ≤ gas) :
    Gas.SpecG fork (At CODE message 2829 [a, a, BitVec.ofNat 256 0x0260, x] MEM0 gas state substate)
      (Halted false .empty (gas - 1089) state
        { substate with logs := substate.logs.push (log1W message.currentTarget DEPRECATE_TOPIC
          (mkey a)) }) := by
  refine Triple.seq (Gas.Triple.seqL popR (restate (pc' := 2830) (by decide) rfl rfl
    (g' := gas - 2) (by gas_ok) rfl rfl)) ?_
  refine (listLog (.inr (.inr ⟨rfl, rfl, rfl⟩)) hstatic size_MEM0 mload_MEM0
    (by omega)).consequence (fun _ h => h) ?_
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  exact ⟨hr, he, ho, by rw [hgas]; gas_ok, hs, hss⟩

/-- **deprecate(a) over the EIP-8037 meter, exactly, at any reservoir, refills allowed.** From Berlin,
from a frame `m` of `StateGasMeter` with any meter whose `toNat` is the fresh frame of `CODE` with
selector 0x0753c30c, by the owner, a frame that is not static and an account: the run, for any gas bound and
message runner, ends with no error if and only if the chain condition holds (`wOk` of the first
write from `m.gas`, `wOk` of the second write from the meter after the first, and the gas of the
tail at most the execution gas left after the second). The meter after a write carries its refill
to the reservoir and the spill that the next write reads, so a refill of the first write can pay
the state gas of the second. Every run that ends with no error stops with the end of the Nat
specification (output, state, substate), with `gasLeft` plus the gas of the Nat specification
equal to `gas` plus the two bumps, and with the meter after the second write for the rest. -/
theorem deprecate_sgm (hfork : .berlin ≤ fork)
    (hstatic : message.isStatic = false) (hacc : hasAccount state message.currentTarget)
    (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x0753c30c)
    (hv : message.value = 0) (hown : callerWord message = ownerOf state message.currentTarget)
    {c0 c10 : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hc10 : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget 10 = c10)
    {gas : Nat} {m : Evm fork StateGasMeter}
    (start : At CODE message 0 [] .empty gas state substate (Meter.toNat m))
    {bound : Nat} {runChild : MessageRunner fork StateGasMeter bound}
    (within : GasMeter.gasHeld m.gas ≤ bound) :
    (Shadow.RunsOkS fork bound runChild m within ↔
      wOk fork m.gas (372 + slotCost c0 + slotCost c10) (originalAt state message.currentTarget 10)
          (storageAt state message.currentTarget 10)
          (withPaused (storageAt state message.currentTarget 10) 1) false ∧
      wOk fork (wMeter fork m.gas (372 + slotCost c0 + slotCost c10)
            (originalAt state message.currentTarget 10) (storageAt state message.currentTarget 10)
            (withPaused (storageAt state message.currentTarget 10) 1) false) 167
          (originalAt state message.currentTarget 10)
          (withPaused (storageAt state message.currentTarget 10) 1) (depWord state message) false ∧
      1089 ≤ (wMeter fork (wMeter fork m.gas (372 + slotCost c0 + slotCost c10)
            (originalAt state message.currentTarget 10) (storageAt state message.currentTarget 10)
            (withPaused (storageAt state message.currentTarget 10) 1) false) 167
          (originalAt state message.currentTarget 10)
          (withPaused (storageAt state message.currentTarget 10) 1) (depWord state message)
          false).gasLeft) ∧
    ∀ s, Evm.runFrame (step fork) (step_decreases fork) bound runChild m within = .ok s →
      s.error = none →
      s.running = false ∧ s.output = .empty ∧ s.state = depState state message ∧
      s.substate = depSub fork substate state message ∧
      s.gas.gasLeft + (1628 + slotCost c0 + slotCost c10 + depCost fork state message) =
        gas + wBump fork m.gas (originalAt state message.currentTarget 10)
            (storageAt state message.currentTarget 10)
            (withPaused (storageAt state message.currentTarget 10) 1) +
          wBump fork (wMeter fork m.gas (372 + slotCost c0 + slotCost c10)
            (originalAt state message.currentTarget 10) (storageAt state message.currentTarget 10)
            (withPaused (storageAt state message.currentTarget 10) 1) false)
            (originalAt state message.currentTarget 10)
            (withPaused (storageAt state message.currentTarget 10) 1) (depWord state message) ∧
      s.gas = { wMeter fork (wMeter fork m.gas (372 + slotCost c0 + slotCost c10)
            (originalAt state message.currentTarget 10) (storageAt state message.currentTarget 10)
            (withPaused (storageAt state message.currentTarget 10) 1) false) 167
          (originalAt state message.currentTarget 10)
          (withPaused (storageAt state message.currentTarget 10) 1) (depWord state message)
          false with gasLeft := s.gas.gasLeft } := by
  have hacc0 := hasAccount_readSlot (n := 0) (other := message.currentTarget) hacc
  have hacc1 := hasAccount_readSlot (n := 10) (other := message.currentTarget) hacc0
  have hP : 372 + slotCost c0 + slotCost c10 < 97920 := by
    have := Complete.slotCost_le c0; have := Complete.slotCost_le c10; omega
  have hx := Complete.exactS_write hfork (depPre hfork hsize hsize' hsel hv hown hc0 hc10) hP
    (fun _ _ => rfl) (by code_fact) (by code_fact) hstatic hacc1 (coldIn_accessSlot_self _ _ _)
    (Complete.exactS_write hfork (fun g hg => depMid hfork
        (TransferFee.coldIn_storeSub_false (coldIn_accessSlot_self _ _ _)) hg) (by decide)
      (fun _ _ => rfl) (by code_fact) (by code_fact) hstatic
      (hasAccount_readSlot (hasAccount_writeSlot hacc1)) (coldIn_accessSlot_self _ _ _)
      (Complete.exactS_halt (fun g hg => depPost hstatic hg) (by decide) (fun _ _ => rfl)))
  obtain ⟨hgas, hiff, hend⟩ := hx.run start (runChild := runChild) within
  have hw := hasAccount_writeSlot (n := 10)
    (v := withPaused (storageAt state message.currentTarget 10) 1) hacc1
  simp only [originalAt_readSlot, storageAt_readSlot, originalAt_writeSlot hacc1,
    storageAt_writeSlot_self hacc1] at hiff
  refine ⟨hiff, fun s hrun hok => ?_⟩
  have hok' := hiff.mp ⟨s, hrun, hok⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := hend s hrun hok
  simp only [originalAt_readSlot, storageAt_readSlot, originalAt_writeSlot hacc1,
    storageAt_writeSlot_self hacc1] at h5
  refine ⟨h1, h2, ?_, ?_, ?_, ?_⟩
  · rw [h3, writeSlot_readSlot _ _ hw, writeSlot_readSlot _ _ hacc0, storageAt_writeSlot_self hacc0]
  · rw [h4]
    rw [storeSub_accessSlot]
    rw [storeSub_accessSlot]
    rw [mkey_addrArg]
    repeat' first
      | rw [originalAt_readSlot]
      | rw [originalAt_writeSlot hacc1]
      | rw [originalAt_writeSlot hacc0]
      | rw [storageAt_readSlot]
      | rw [storageAt_writeSlot_self hacc1]
      | rw [storageAt_writeSlot_self hacc0]
    done
  · obtain ⟨o1, o2, o3⟩ := hok'
    have e1 := Complete.wMeter_gasLeft o1
    have e2 := Complete.wMeter_gasLeft o2
    have e3 : s.gas.gasLeft = _ := congrArg StateGasMeter.gasLeft h5
    simp only [depCost, depWord, wBump] at e1 e2 e3 o3 ⊢
    omega
  · rw [h5]

end UsdtVerify.AddrWriteSpec

namespace UsdtVerify.Issue
open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts
open Transfer TransferOk Owner Admin BlackList
variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate}

/-- At 6338 (issue) / 6758 (redeem): from the lookup of `balances[owner]` to its `SSTORE` (at
6447 / 6866), with `B + a` / `B - a`. -/
theorem ownerToW (hfork : .berlin ≤ fork) {p q j : Nat} {f : U256 → U256 → U256}
    (hp : (p = 6338 ∧ q = 6447 ∧ j = 358 ∧ f = add) ∨ (p = 6758 ∧ q = 6866 ∧ j = 357 ∧ f = sub))
    {a : U256} {rest : List U256} (hrest : rest.length ≤ 800)
    (hc0 : coldIn substate message.currentTarget 0 = false)
    (hcO : coldIn substate message.currentTarget (ownerBal state message.currentTarget) = false)
    {M : ByteArray} (hM : M.size = 96) {gas : Nat} (hg : j ≤ gas) :
    Gas.HoareG fork (At CODE message p (a :: rest) M gas state substate)
      (At CODE message q (ownerBal state message.currentTarget ::
          f (storageAt state message.currentTarget (ownerBal state message.currentTarget)) a ::
          f (storageAt state message.currentTarget (ownerBal state message.currentTarget)) a ::
          a :: rest) (mapMem M (ownerOf state message.currentTarget) 2) (gas - j)
        (readSlot (readSlot state message.currentTarget 0) message.currentTarget
          (ownerBal state message.currentTarget))
        (accessSlot (accessSlot substate message.currentTarget 0) message.currentTarget
          (ownerBal state message.currentTarget))) := by
  have hcO' := TransferFrom.coldIn_accessSlot_false (n := 0) hcO
  rcases hp with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
  · step jumpdestR
    step dupR 0
    step ownerLookup hfork (by decide) (by simp; omega) hM hc0 (gas := gas - 1 - 3) (by gas_ok)
    step pushR 1 (0 : U256)
    owner_pre 0x01 instruction_add
    rw [storageAt_readSlot]
    exact restate (by decide) rfl rfl (by gas_ok) rfl rfl
  · step dupR 0
    step ownerLookup hfork (by decide) (by simp; omega) hM hc0 (gas := gas - 3) (by gas_ok)
    step pushR 1 (0 : U256)
    owner_pre 0x03 instruction_sub
    rw [storageAt_readSlot]
    exact restate (by decide) rfl rfl (by gas_ok) rfl rfl

/-- At 6449 (issue) / 6741 (redeem): to the `SSTORE` of `_totalSupply` (at 6463 / 6756), with
`T + a` / `T - a`. -/
theorem totalToW (hfork : .berlin ≤ fork) {p q j : Nat} {f : U256 → U256 → U256}
    (hp : (p = 6449 ∧ q = 6463 ∧ j = 131 ∧ f = add) ∨ (p = 6741 ∧ q = 6756 ∧ j = 132 ∧ f = sub))
    {a : U256} {rest : List U256} (hrest : rest.length ≤ 800)
    (hc1 : coldIn substate message.currentTarget 1 = false) {M : ByteArray} {gas : Nat}
    (hg : j ≤ gas) :
    Gas.HoareG fork (At CODE message p (a :: rest) M gas state substate)
      (At CODE message q (1 :: f (storageAt state message.currentTarget 1) a ::
          f (storageAt state message.currentTarget 1) a :: a :: rest) M (gas - j)
        (readSlot state message.currentTarget 1) (accessSlot substate message.currentTarget 1)) := by
  rcases hp with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
  · step dupR 0
    step pushR 1 (0x01 : U256)
    step pushR 1 (0 : U256)
    op_pre 0x01 instruction_add hc1
    exact restate (by decide) rfl rfl (by gas_ok) rfl rfl
  · step jumpdestR
    step dupR 0
    step pushR 1 (0x01 : U256)
    step pushR 1 (0 : U256)
    op_pre 0x03 instruction_sub hc1
    exact restate (by decide) rfl rfl (by gas_ok) rfl rfl

end UsdtVerify.Issue

namespace UsdtVerify.IssueSpec
open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts
open Transfer TransferOk Owner Admin BlackList Issue
open Complete (wBump wSgm wOk wMeter)
variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate}

/-- From pc 0 to the `SSTORE` of `balances[owner]` (6447) in a successful `issue(a)`. -/
theorem issueW1 (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xcc872b66)
    (hv : message.value = 0) (hown : callerWord message = ownerOf state message.currentTarget)
    (hT : 0 < (wordArg message.data 0).toNat ∧
      (storageAt state message.currentTarget 1).toNat + (wordArg message.data 0).toNat < 2 ^ 256)
    (hB : (storageAt state message.currentTarget (ownerBal state message.currentTarget)).toNat +
        (wordArg message.data 0).toNat < 2 ^ 256)
    {c0 c1 cO : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hc1 : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget 1 = c1)
    (hcO : coldIn (accessSlot (accessSlot substate message.currentTarget 0) message.currentTarget 1)
      message.currentTarget (ownerBal state message.currentTarget) = cO)
    (gas : Nat) (hg : 1814 + slotCost c0 + slotCost c1 + slotCost cO ≤ gas) :
    Gas.HoareG fork (At CODE message 0 [] .empty gas state substate)
      (At CODE message 6447 (ownerBal state message.currentTarget ::
          add (storageAt state message.currentTarget (ownerBal state message.currentTarget))
            (wordArg message.data 0) ::
          add (storageAt state message.currentTarget (ownerBal state message.currentTarget))
            (wordArg message.data 0) ::
          wordArg message.data 0 :: [BitVec.ofNat 256 0x07d9, BitVec.ofNat 256 (selector message.data)])
        (mapMem (mapMem (mapMem MEM0 (ownerOf state message.currentTarget) 2)
          (ownerOf state message.currentTarget) 2) (ownerOf state message.currentTarget) 2)
        (gas - (1814 + slotCost c0 + slotCost c1 + slotCost cO))
        (readSlot (readSlot (reqState state message.currentTarget) message.currentTarget 0)
          message.currentTarget (ownerBal state message.currentTarget))
        (accessSlot (accessSlot (reqSub substate state message.currentTarget) message.currentTarget 0)
          message.currentTarget (ownerBal state message.currentTarget))) := by
  have hw0 : coldIn (reqSub substate state message.currentTarget) message.currentTarget 0 =
      false :=
    TransferFrom.coldIn_accessSlot_false (TransferFrom.coldIn_accessSlot_false
      (coldIn_accessSlot_self _ _ _))
  have hwO : coldIn (reqSub substate state message.currentTarget) message.currentTarget
      (ownerBal (reqState state message.currentTarget) message.currentTarget) = false := by
    rw [ownerBal_readSlot, ownerBal_readSlot, ownerBal_readSlot]
    exact coldIn_accessSlot_self _ _ _
  refine Triple.seq (issuePre hfork hsize hsize' hsel hv hown hT hc0 hc1 hcO (by omega)) ?_
  step reqPass (Or.inr (Or.inl ⟨rfl, rfl⟩)) (gtAdd_ne ⟨hT.1, hB⟩) (by simp) (by gas_ok)
  refine Triple.seq (ownerToW hfork (.inl ⟨rfl, rfl, rfl, rfl⟩) (by simp) hw0 hwO
    (size_mapMem (size_mapMem size_MEM0 _ _) _ _) (by gas_ok)) ?_
  simp only [ownerBal_readSlot, ownerOf_readSlot, storageAt_readSlot]
  exact restate rfl rfl rfl (by gas_ok) rfl rfl

/-- From the `POP` at 6448 after the first `SSTORE` of issue to the second (6463). -/
theorem issueW2 {a b x : U256} (hfork : .berlin ≤ fork)
    (hc1 : coldIn substate message.currentTarget 1 = false) {M : ByteArray} {gas : Nat}
    (hg : 133 ≤ gas) :
    Gas.HoareG fork (At CODE message 6448 [b, a, BitVec.ofNat 256 0x07d9, x] M gas state substate)
      (At CODE message 6463 (1 :: add (storageAt state message.currentTarget 1) a ::
          add (storageAt state message.currentTarget 1) a :: a :: [BitVec.ofNat 256 0x07d9, x]) M
        (gas - 133) (readSlot state message.currentTarget 1)
        (accessSlot substate message.currentTarget 1)) := by
  refine Triple.seq (Gas.Triple.seqL popR (restate (pc' := 6449) (by decide) rfl rfl
    (g' := gas - 2) (by gas_ok) rfl rfl)) ?_
  refine (totalToW hfork (.inl ⟨rfl, rfl, rfl, rfl⟩) (by simp) hc1 (by omega)).consequence
    (fun _ h => h) ?_
  intro e he
  have hx : gas - 2 - 131 = gas - 133 := by omega
  rw [hx] at he
  exact he

/-- From the `POP` after the last `SSTORE` of issue (6464) or redeem (6867) to the STOP. -/
theorem amountPost {q : Nat} {t : U256} {r : Nat}
    (hq : (q = 6464 ∧ t = ISSUE_TOPIC ∧ r = 0x07d9) ∨ (q = 6867 ∧ t = REDEEM_TOPIC ∧ r = 0x07fc))
    {a b x : U256} (hstatic : message.isStatic = false) {M : ByteArray} (hM : M.size = 96)
    (hptr : loadWord (memoryReadBytes M 64 32) 0 32 = 0x60) {gas : Nat} (hg : 1077 ≤ gas) :
    Gas.SpecG fork (At CODE message q [b, a, BitVec.ofNat 256 r, x] M gas state substate)
      (Halted false .empty (gas - 1077) state
        { substate with logs := substate.logs.push (log1W message.currentTarget t a) }) := by
  rcases hq with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · refine Triple.seq (Gas.Triple.seqL popR (restate (pc' := 6465) (by decide) rfl rfl
      (g' := gas - 2) (by gas_ok) rfl rfl)) ?_
    refine (amountLog (.inl ⟨rfl, rfl, rfl⟩) hstatic hM hptr (by omega)).consequence
      (fun _ h => h) ?_
    rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
    exact ⟨hr, he, ho, by rw [hgas]; gas_ok, hs, hss⟩
  · refine Triple.seq (Gas.Triple.seqL popR (restate (pc' := 6868) (by decide) rfl rfl
      (g' := gas - 2) (by gas_ok) rfl rfl)) ?_
    refine (amountLog (.inr ⟨rfl, rfl, rfl⟩) hstatic hM hptr (by omega)).consequence
      (fun _ h => h) ?_
    rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
    exact ⟨hr, he, ho, by rw [hgas]; gas_ok, hs, hss⟩

/-- The meter after the write of `balances[owner]` in issue, from the meter `g`. -/
abbrev issueM1 (fork : Fork) (g : StateGasMeter) (state : State.TransactionState)
    (message : Message fork) (P : Nat) : StateGasMeter :=
  wMeter fork g P (originalAt state message.currentTarget (ownerBal state message.currentTarget))
    (storageAt state message.currentTarget (ownerBal state message.currentTarget))
    (add (storageAt state message.currentTarget (ownerBal state message.currentTarget))
      (wordArg message.data 0)) false

/-- The meter after the write of `_totalSupply` in issue. -/
abbrev issueM2 (fork : Fork) (g : StateGasMeter) (state : State.TransactionState)
    (message : Message fork) (P : Nat) : StateGasMeter :=
  wMeter fork (issueM1 fork g state message P) 133 (originalAt state message.currentTarget 1)
    (storageAt (issueState1 state message) message.currentTarget 1)
    (add (storageAt (issueState1 state message) message.currentTarget 1) (wordArg message.data 0))
    false

/-- **issue(a) over the EIP-8037 meter, exactly, at any reservoir, refills allowed.** From Berlin,
from a frame `m` of `StateGasMeter` with any meter whose `toNat` is the fresh frame of `CODE` with
selector 0xcc872b66, by the owner, with the two `require`s passing, a frame that is not static and an account: the run, for any gas bound and
message runner, ends with no error if and only if the chain condition holds (`wOk` of the first
write from `m.gas`, `wOk` of the second write from the meter after the first, and the gas of the
tail at most the execution gas left after the second). The meter after a write carries its refill
to the reservoir and the spill that the next write reads, so a refill of the first write can pay
the state gas of the second. Every run that ends with no error stops with the end of the Nat
specification (output, state, substate), with `gasLeft` plus the gas of the Nat specification
equal to `gas` plus the two bumps, and with the meter after the second write for the rest. -/
theorem issue_sgm (hfork : .berlin ≤ fork)
    (hstatic : message.isStatic = false) (hacc : hasAccount state message.currentTarget)
    (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xcc872b66)
    (hv : message.value = 0) (hown : callerWord message = ownerOf state message.currentTarget)
    (hT : 0 < (wordArg message.data 0).toNat ∧
      (storageAt state message.currentTarget 1).toNat + (wordArg message.data 0).toNat < 2 ^ 256)
    (hB : (storageAt state message.currentTarget (ownerBal state message.currentTarget)).toNat +
        (wordArg message.data 0).toNat < 2 ^ 256)
    {c0 c1 cO : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hc1 : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget 1 = c1)
    (hcO : coldIn (accessSlot (accessSlot substate message.currentTarget 0) message.currentTarget 1)
      message.currentTarget (ownerBal state message.currentTarget) = cO)
    {gas : Nat} {m : Evm fork StateGasMeter}
    (start : At CODE message 0 [] .empty gas state substate (Meter.toNat m))
    {bound : Nat} {runChild : MessageRunner fork StateGasMeter bound}
    (within : GasMeter.gasHeld m.gas ≤ bound) :
    (Shadow.RunsOkS fork bound runChild m within ↔
      wOk fork m.gas (1814 + slotCost c0 + slotCost c1 + slotCost cO)
          (originalAt state message.currentTarget (ownerBal state message.currentTarget))
          (storageAt state message.currentTarget (ownerBal state message.currentTarget))
          (add (storageAt state message.currentTarget (ownerBal state message.currentTarget))
            (wordArg message.data 0)) false ∧
      wOk fork (issueM1 fork m.gas state message (1814 + slotCost c0 + slotCost c1 + slotCost cO))
          133 (originalAt state message.currentTarget 1)
          (storageAt (issueState1 state message) message.currentTarget 1)
          (add (storageAt (issueState1 state message) message.currentTarget 1)
            (wordArg message.data 0)) false ∧
      1077 ≤ (issueM2 fork m.gas state message
        (1814 + slotCost c0 + slotCost c1 + slotCost cO)).gasLeft) ∧
    ∀ s, Evm.runFrame (step fork) (step_decreases fork) bound runChild m within = .ok s →
      s.error = none →
      s.running = false ∧ s.output = .empty ∧ s.state = issueState state message ∧
      s.substate = issueSub fork substate state message ∧
      s.gas.gasLeft + (3024 + slotCost c0 + slotCost c1 + slotCost cO +
          issueCostO fork state message + issueCostT fork state message) =
        gas + wBump fork m.gas
            (originalAt state message.currentTarget (ownerBal state message.currentTarget))
            (storageAt state message.currentTarget (ownerBal state message.currentTarget))
            (add (storageAt state message.currentTarget (ownerBal state message.currentTarget))
              (wordArg message.data 0)) +
          wBump fork (issueM1 fork m.gas state message
              (1814 + slotCost c0 + slotCost c1 + slotCost cO))
            (originalAt state message.currentTarget 1)
            (storageAt (issueState1 state message) message.currentTarget 1)
            (add (storageAt (issueState1 state message) message.currentTarget 1)
              (wordArg message.data 0)) ∧
      s.gas = { issueM2 fork m.gas state message (1814 + slotCost c0 + slotCost c1 + slotCost cO)
        with gasLeft := s.gas.gasLeft } := by
  have hacc2 : hasAccount (reqState state message.currentTarget) message.currentTarget :=
    hasAccount_readSlot (hasAccount_readSlot (hasAccount_readSlot hacc))
  have hacc3 := hasAccount_readSlot (n := 0) (other := message.currentTarget) hacc2
  have hacc4 := hasAccount_readSlot (n := ownerBal state message.currentTarget)
    (other := message.currentTarget) hacc3
  have hacc5 := hasAccount_writeSlot (n := ownerBal state message.currentTarget)
    (v := add (storageAt state message.currentTarget (ownerBal state message.currentTarget))
      (wordArg message.data 0)) hacc4
  have hP : 1814 + slotCost c0 + slotCost c1 + slotCost cO < 97920 := by
    have := Complete.slotCost_le c0; have := Complete.slotCost_le c1
    have := Complete.slotCost_le cO; omega
  have hx := Complete.exactS_write hfork (issueW1 hfork hsize hsize' hsel hv hown hT hB hc0 hc1 hcO)
    hP (fun _ _ => rfl) (by code_fact) (by code_fact) hstatic hacc4 (coldIn_accessSlot_self _ _ _)
    (Complete.exactS_write hfork (fun g hg => issueW2 hfork
        (TransferFee.coldIn_storeSub_false (TransferFrom.coldIn_accessSlot_false
          (TransferFrom.coldIn_accessSlot_false (TransferFrom.coldIn_accessSlot_false
            (coldIn_accessSlot_self _ _ _))))) hg) (by decide)
      (fun _ _ => rfl) (by code_fact) (by code_fact) hstatic
      (hasAccount_readSlot hacc5) (coldIn_accessSlot_self _ _ _)
      (Complete.exactS_halt (fun g hg => amountPost (.inl ⟨rfl, rfl, rfl⟩) hstatic
        (size_mapMem (size_mapMem (size_mapMem size_MEM0 _ _) _ _) _ _)
        (ptr_mapMem (size_mapMem (size_mapMem size_MEM0 _ _) _ _)
          (ptr_mapMem (size_mapMem size_MEM0 _ _) (ptr_mapMem size_MEM0 mload_MEM0 _ _) _ _) _ _)
        hg) (by decide) (fun _ _ => rfl)))
  obtain ⟨hgas, hiff, hend⟩ := hx.run start (runChild := runChild) within
  simp only [originalAt_readSlot, storageAt_readSlot, originalAt_writeSlot hacc4, originalAt_writeSlot hacc3, originalAt_writeSlot hacc2,
    writeSlot_readSlot _ _ hacc3] at hiff
  refine ⟨hiff, fun s hrun hok => ?_⟩
  have hok' := hiff.mp ⟨s, hrun, hok⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := hend s hrun hok
  simp only [originalAt_readSlot, storageAt_readSlot, originalAt_writeSlot hacc4, originalAt_writeSlot hacc3, originalAt_writeSlot hacc2,
    writeSlot_readSlot _ _ hacc3] at h5
  refine ⟨h1, h2, ?_, ?_, ?_, ?_⟩
  · rw [h3]
    repeat' first
      | rw [storageAt_readSlot]
      | rw [writeSlot_readSlot _ _ hacc5]
      | rw [writeSlot_readSlot _ _ hacc3]
  · rw [h4]
    rw [storeSub_accessSlot, storeSub_accessSlot]
    repeat' first
      | rw [originalAt_readSlot]
      | rw [originalAt_writeSlot hacc4]
      | rw [storageAt_readSlot]
      | rw [writeSlot_readSlot _ _ hacc3]
  · obtain ⟨o1, o2, o3⟩ := hok'
    have e1 := Complete.wMeter_gasLeft o1
    have e2 := Complete.wMeter_gasLeft o2
    have e3 : s.gas.gasLeft = _ := congrArg StateGasMeter.gasLeft h5
    simp only [issueCostO, issueCostT, wBump, issueM1, issueM2, issueState1] at e1 e2 e3 o3 ⊢
    omega
  · rw [h5]

/-- From pc 0 to the `SSTORE` of `_totalSupply` (6756) in a successful `redeem(a)`. -/
theorem redeemW1 (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xdb006a75)
    (hv : message.value = 0) (hown : callerWord message = ownerOf state message.currentTarget)
    (hT : (wordArg message.data 0).toNat ≤ (storageAt state message.currentTarget 1).toNat)
    (hB : (wordArg message.data 0).toNat ≤
      (storageAt state message.currentTarget (ownerBal state message.currentTarget)).toNat)
    {c0 c1 cO : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hc1 : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget 1 = c1)
    (hcO : coldIn (accessSlot (accessSlot substate message.currentTarget 0) message.currentTarget 1)
      message.currentTarget (ownerBal state message.currentTarget) = cO)
    (gas : Nat) (hg : 1178 + slotCost c0 + slotCost c1 + slotCost cO ≤ gas) :
    Gas.HoareG fork (At CODE message 0 [] .empty gas state substate)
      (At CODE message 6756 (1 :: sub (storageAt state message.currentTarget 1)
            (wordArg message.data 0) ::
          sub (storageAt state message.currentTarget 1) (wordArg message.data 0) ::
          wordArg message.data 0 :: [BitVec.ofNat 256 0x07fc, BitVec.ofNat 256 (selector message.data)])
        (mapMem MEM0 (ownerOf state message.currentTarget) 2)
        (gas - (1178 + slotCost c0 + slotCost c1 + slotCost cO))
        (readSlot (reqState state message.currentTarget) message.currentTarget 1)
        (accessSlot (reqSub substate state message.currentTarget) message.currentTarget 1)) := by
  have hw1 : coldIn (reqSub substate state message.currentTarget) message.currentTarget 1 =
      false :=
    TransferFrom.coldIn_accessSlot_false (coldIn_accessSlot_self _ _ _)
  refine Triple.seq (redeemPre hfork hsize hsize' hsel hv hown hT hc0 hc1 hcO (by omega)) ?_
  step reqPass (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))) (ge_ne hB) (by simp) (by gas_ok)
  refine Triple.seq (totalToW hfork (.inr ⟨rfl, rfl, rfl, rfl⟩) (by simp) hw1 (by gas_ok)) ?_
  simp only [storageAt_readSlot]
  exact restate rfl rfl rfl (by gas_ok) rfl rfl

/-- From the `POP` at 6757 after the first `SSTORE` of redeem to the second (6866). -/
theorem redeemW2 {a b x : U256} (hfork : .berlin ≤ fork)
    (hc0 : coldIn substate message.currentTarget 0 = false)
    (hcO : coldIn substate message.currentTarget (ownerBal state message.currentTarget) = false)
    {M : ByteArray} (hM : M.size = 96) {gas : Nat} (hg : 359 ≤ gas) :
    Gas.HoareG fork (At CODE message 6757 [b, a, BitVec.ofNat 256 0x07fc, x] M gas state substate)
      (At CODE message 6866 (ownerBal state message.currentTarget ::
          sub (storageAt state message.currentTarget (ownerBal state message.currentTarget)) a ::
          sub (storageAt state message.currentTarget (ownerBal state message.currentTarget)) a ::
          a :: [BitVec.ofNat 256 0x07fc, x]) (mapMem M (ownerOf state message.currentTarget) 2)
        (gas - 359)
        (readSlot (readSlot state message.currentTarget 0) message.currentTarget
          (ownerBal state message.currentTarget))
        (accessSlot (accessSlot substate message.currentTarget 0) message.currentTarget
          (ownerBal state message.currentTarget))) := by
  refine Triple.seq (Gas.Triple.seqL popR (restate (pc' := 6758) (by decide) rfl rfl
    (g' := gas - 2) (by gas_ok) rfl rfl)) ?_
  refine (ownerToW hfork (.inr ⟨rfl, rfl, rfl, rfl⟩) (by simp) hc0 hcO hM (by omega)).consequence
    (fun _ h => h) ?_
  intro e he
  have hx : gas - 2 - 357 = gas - 359 := by omega
  rw [hx] at he
  exact he

/-- The meter after the write of `_totalSupply` in redeem, from the meter `g`. -/
abbrev redeemM1 (fork : Fork) (g : StateGasMeter) (state : State.TransactionState)
    (message : Message fork) (P : Nat) : StateGasMeter :=
  wMeter fork g P (originalAt state message.currentTarget 1)
    (storageAt state message.currentTarget 1)
    (sub (storageAt state message.currentTarget 1) (wordArg message.data 0)) false

/-- The meter after the write of `balances[owner]` in redeem. -/
abbrev redeemM2 (fork : Fork) (g : StateGasMeter) (state : State.TransactionState)
    (message : Message fork) (P : Nat) : StateGasMeter :=
  wMeter fork (redeemM1 fork g state message P) 359
    (originalAt state message.currentTarget (ownerBal state message.currentTarget))
    (storageAt (redeemState1 state message) message.currentTarget
      (ownerBal state message.currentTarget))
    (sub (storageAt (redeemState1 state message) message.currentTarget
      (ownerBal state message.currentTarget)) (wordArg message.data 0)) false

/-- **redeem(a) over the EIP-8037 meter, exactly, at any reservoir, refills allowed.** From Berlin,
from a frame `m` of `StateGasMeter` with any meter whose `toNat` is the fresh frame of `CODE` with
selector 0xdb006a75, by the owner, with the two `require`s passing, a frame that is not static and an account: the run, for any gas bound and
message runner, ends with no error if and only if the chain condition holds (`wOk` of the first
write from `m.gas`, `wOk` of the second write from the meter after the first, and the gas of the
tail at most the execution gas left after the second). The meter after a write carries its refill
to the reservoir and the spill that the next write reads, so a refill of the first write can pay
the state gas of the second. Every run that ends with no error stops with the end of the Nat
specification (output, state, substate), with `gasLeft` plus the gas of the Nat specification
equal to `gas` plus the two bumps, and with the meter after the second write for the rest. -/
theorem redeem_sgm (hfork : .berlin ≤ fork)
    (hstatic : message.isStatic = false) (hacc : hasAccount state message.currentTarget)
    (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xdb006a75)
    (hv : message.value = 0) (hown : callerWord message = ownerOf state message.currentTarget)
    (hT : (wordArg message.data 0).toNat ≤ (storageAt state message.currentTarget 1).toNat)
    (hB : (wordArg message.data 0).toNat ≤
      (storageAt state message.currentTarget (ownerBal state message.currentTarget)).toNat)
    {c0 c1 cO : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hc1 : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget 1 = c1)
    (hcO : coldIn (accessSlot (accessSlot substate message.currentTarget 0) message.currentTarget 1)
      message.currentTarget (ownerBal state message.currentTarget) = cO)
    {gas : Nat} {m : Evm fork StateGasMeter}
    (start : At CODE message 0 [] .empty gas state substate (Meter.toNat m))
    {bound : Nat} {runChild : MessageRunner fork StateGasMeter bound}
    (within : GasMeter.gasHeld m.gas ≤ bound) :
    (Shadow.RunsOkS fork bound runChild m within ↔
      wOk fork m.gas (1178 + slotCost c0 + slotCost c1 + slotCost cO)
          (originalAt state message.currentTarget 1) (storageAt state message.currentTarget 1)
          (sub (storageAt state message.currentTarget 1) (wordArg message.data 0)) false ∧
      wOk fork (redeemM1 fork m.gas state message (1178 + slotCost c0 + slotCost c1 + slotCost cO))
          359 (originalAt state message.currentTarget (ownerBal state message.currentTarget))
          (storageAt (redeemState1 state message) message.currentTarget
            (ownerBal state message.currentTarget))
          (sub (storageAt (redeemState1 state message) message.currentTarget
            (ownerBal state message.currentTarget)) (wordArg message.data 0)) false ∧
      1077 ≤ (redeemM2 fork m.gas state message
        (1178 + slotCost c0 + slotCost c1 + slotCost cO)).gasLeft) ∧
    ∀ s, Evm.runFrame (step fork) (step_decreases fork) bound runChild m within = .ok s →
      s.error = none →
      s.running = false ∧ s.output = .empty ∧ s.state = redeemState state message ∧
      s.substate = redeemSub fork substate state message ∧
      s.gas.gasLeft + (2614 + slotCost c0 + slotCost c1 + slotCost cO +
          redeemCostT fork state message + redeemCostO fork state message) =
        gas + wBump fork m.gas (originalAt state message.currentTarget 1)
            (storageAt state message.currentTarget 1)
            (sub (storageAt state message.currentTarget 1) (wordArg message.data 0)) +
          wBump fork (redeemM1 fork m.gas state message
              (1178 + slotCost c0 + slotCost c1 + slotCost cO))
            (originalAt state message.currentTarget (ownerBal state message.currentTarget))
            (storageAt (redeemState1 state message) message.currentTarget
              (ownerBal state message.currentTarget))
            (sub (storageAt (redeemState1 state message) message.currentTarget
              (ownerBal state message.currentTarget)) (wordArg message.data 0)) ∧
      s.gas = { redeemM2 fork m.gas state message (1178 + slotCost c0 + slotCost c1 + slotCost cO)
        with gasLeft := s.gas.gasLeft } := by
  have hacc2 : hasAccount (reqState state message.currentTarget) message.currentTarget :=
    hasAccount_readSlot (hasAccount_readSlot (hasAccount_readSlot hacc))
  have hacc3 := hasAccount_readSlot (n := 1) (other := message.currentTarget) hacc2
  have hacc4 := hasAccount_writeSlot (n := 1)
    (v := sub (storageAt state message.currentTarget 1) (wordArg message.data 0)) hacc3
  have hacc5 := hasAccount_readSlot (n := 0) (other := message.currentTarget) hacc4
  have hob : ownerBal (writeSlot (readSlot (reqState state message.currentTarget)
      message.currentTarget 1) message.currentTarget 1
      (sub (storageAt state message.currentTarget 1) (wordArg message.data 0)))
      message.currentTarget = ownerBal state message.currentTarget := by
    rw [ownerBal_writeSlot hacc3 (by decide), ownerBal_readSlot, ownerBal_readSlot,
      ownerBal_readSlot, ownerBal_readSlot]
  have hacc6 := hasAccount_readSlot (n := ownerBal state message.currentTarget)
    (other := message.currentTarget) hacc5
  have hP : 1178 + slotCost c0 + slotCost c1 + slotCost cO < 97920 := by
    have := Complete.slotCost_le c0; have := Complete.slotCost_le c1
    have := Complete.slotCost_le cO; omega
  have hw2 := fun g (hg : 359 ≤ g) => redeemW2 (a := wordArg message.data 0)
    (b := sub (storageAt state message.currentTarget 1) (wordArg message.data 0))
    (x := BitVec.ofNat 256 (selector message.data))
    (state := writeSlot (readSlot (reqState state message.currentTarget) message.currentTarget 1)
      message.currentTarget 1 (sub (storageAt state message.currentTarget 1) (wordArg message.data 0)))
    (substate := storeSub fork (accessSlot (reqSub substate state message.currentTarget)
      message.currentTarget 1) message.currentTarget 1
      (originalAt (readSlot (reqState state message.currentTarget) message.currentTarget 1)
        message.currentTarget 1)
      (storageAt (readSlot (reqState state message.currentTarget) message.currentTarget 1)
        message.currentTarget 1)
      (sub (storageAt state message.currentTarget 1) (wordArg message.data 0)))
    (M := mapMem MEM0 (ownerOf state message.currentTarget) 2) hfork
    (TransferFee.coldIn_storeSub_false (TransferFrom.coldIn_accessSlot_false
      (TransferFrom.coldIn_accessSlot_false (TransferFrom.coldIn_accessSlot_false
        (coldIn_accessSlot_self _ _ _)))))
    (by rw [hob]; exact TransferFee.coldIn_storeSub_false (TransferFrom.coldIn_accessSlot_false
      (coldIn_accessSlot_self _ _ _))) (size_mapMem size_MEM0 _ _) hg
  rw [hob] at hw2
  have hx := Complete.exactS_write hfork (redeemW1 hfork hsize hsize' hsel hv hown hT hB hc0 hc1 hcO)
    hP (fun _ _ => rfl) (by code_fact) (by code_fact) hstatic hacc3 (coldIn_accessSlot_self _ _ _)
    (Complete.exactS_write hfork hw2 (by decide)
      (fun _ _ => rfl) (by code_fact) (by code_fact) hstatic hacc6 (coldIn_accessSlot_self _ _ _)
      (Complete.exactS_halt (fun g hg => amountPost (.inr ⟨rfl, rfl, rfl⟩) hstatic
        (size_mapMem (size_mapMem size_MEM0 _ _) _ _)
        (ptr_mapMem (size_mapMem size_MEM0 _ _) (ptr_mapMem size_MEM0 mload_MEM0 _ _) _ _)
        hg) (by decide) (fun _ _ => rfl)))
  obtain ⟨hgas, hiff, hend⟩ := hx.run start (runChild := runChild) within
  simp only [originalAt_readSlot, storageAt_readSlot, originalAt_writeSlot hacc3, originalAt_writeSlot hacc2,
    writeSlot_readSlot _ _ hacc2] at hiff
  refine ⟨hiff, fun s hrun hok => ?_⟩
  have hok' := hiff.mp ⟨s, hrun, hok⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := hend s hrun hok
  simp only [originalAt_readSlot, storageAt_readSlot, originalAt_writeSlot hacc3, originalAt_writeSlot hacc2,
    writeSlot_readSlot _ _ hacc2] at h5
  refine ⟨h1, h2, ?_, ?_, ?_, ?_⟩
  · rw [h3]
    repeat' first
      | rw [storageAt_readSlot]
      | rw [writeSlot_readSlot _ _ hacc5]
      | rw [writeSlot_readSlot _ _ hacc2]
  · rw [h4]
    rw [storeSub_accessSlot, storeSub_accessSlot]
    repeat' first
      | rw [originalAt_readSlot]
      | rw [originalAt_writeSlot hacc3]
      | rw [originalAt_writeSlot hacc2]
      | rw [storageAt_readSlot]
      | rw [writeSlot_readSlot _ _ hacc2]
  · obtain ⟨o1, o2, o3⟩ := hok'
    have e1 := Complete.wMeter_gasLeft o1
    have e2 := Complete.wMeter_gasLeft o2
    have e3 : s.gas.gasLeft = _ := congrArg StateGasMeter.gasLeft h5
    simp only [redeemCostO, redeemCostT, wBump, redeemM1, redeemM2, redeemState1] at e1 e2 e3 o3 ⊢
    omega
  · rw [h5]

end UsdtVerify.IssueSpec

namespace UsdtVerify.SetParamsSpec
open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts
open Transfer TransferOk Owner Admin Issue SafeMath SetParams
open Complete (wBump wSgm wOk wMeter)
variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate}

/-- From pc 0 to the `SSTORE` of slot 3 (5917) in a successful `setParams(b, m)`. -/
theorem paramsW1 (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xc0324c77)
    (hv : message.value = 0) (hown : callerWord message = ownerOf state message.currentTarget)
    (hb : (wordArg message.data 0).toNat < 20) (hm : (wordArg message.data 1).toNat < 50)
    {c0 : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0) (gas : Nat)
    (hg : 807 + slotCost c0 ≤ gas) :
    Gas.HoareG fork (At CODE message 0 [] .empty gas state substate)
      (At CODE message 5917 (3 :: wordArg message.data 0 :: wordArg message.data 0 ::
          wordArg message.data 1 :: wordArg message.data 0 ::
          [0x07b6, BitVec.ofNat 256 (selector message.data)]) MEM0 (gas - (807 + slotCost c0))
        (readSlot state message.currentTarget 0) (accessSlot substate message.currentTarget 0)) := by
  refine Triple.seq (toBody hsize hsize' hsel hv (by omega)) ?_
  step ownerOk hfork (mem_CHECKS (by decide)) (by simp) hc0 hown (by gas_ok)
  at_pc 5881
  step test1 (by simp) (by gas_ok)
  step pass (Or.inl ⟨rfl, rfl⟩) (lt_ne (by simpa using hb)) (by simp) (by gas_ok)
  step test2 (by simp) (by gas_ok)
  step pass (Or.inr ⟨rfl, rfl⟩) (lt_ne (by simpa using hm)) (by simp) (by gas_ok)
  write3_pre
  exact restate (by decide) rfl rfl (by gas_ok) rfl rfl

/-- From the `POP` at 5918 after the `SSTORE` of slot 3 to the `SSTORE` of slot 4 (5947). -/
theorem paramsW2 (hfork : .berlin ≤ fork) {b m x : U256} {c9 : Bool}
    (hc9 : coldIn substate message.currentTarget 9 = c9)
    (hov : m.toNat * (exp (0x0a : U256) (storageAt state message.currentTarget 9)).toNat < 2 ^ 256)
    {M : ByteArray} {gas : Nat}
    (hg : 60 + slotCost c9 + 50 * exponentBytes (storageAt state message.currentTarget 9) +
      mulCost m ≤ gas) :
    Gas.HoareG fork (At CODE message 5918 [b, m, b, 0x07b6, x] M gas state substate)
      (At CODE message 5947 (4 :: mul m (exp (0x0a : U256) (storageAt state message.currentTarget 9)) ::
          mul m (exp (0x0a : U256) (storageAt state message.currentTarget 9)) :: [m, b, 0x07b6, x]) M
        (gas - (60 + slotCost c9 + 50 * exponentBytes (storageAt state message.currentTarget 9) +
          mulCost m))
        (readSlot state message.currentTarget 9) (accessSlot substate message.currentTarget 9)) := by
  refine Triple.seq (Gas.Triple.seqL popR (restate (pc' := 5919) (by decide) rfl rfl
    (g' := gas - 2) (by gas_ok) rfl rfl)) ?_
  refine Triple.seq (mulCall hfork hc9 hov (by omega)) ?_
  step jumpdestR
  step pushR 1 (0x04 : U256)
  step dupR 1
  step swapR 0
  norm
  exact restate (by decide) rfl rfl (by gas_ok) rfl rfl

/-- From the `POP` at 5948 after the `SSTORE` of slot 4 to the STOP. -/
theorem paramsPost {f b m x : U256} (hstatic : message.isStatic = false)
    (hc3 : coldIn substate message.currentTarget 3 = false)
    (hc4 : coldIn substate message.currentTarget 4 = false) (hfork : .berlin ≤ fork)
    {gas : Nat} (hg : 1558 ≤ gas) :
    Gas.SpecG fork (At CODE message 5948 [f, m, b, 0x07b6, x] MEM0 gas state substate)
      (Halted false .empty (gas - 1558)
        (readSlot (readSlot state message.currentTarget 3) message.currentTarget 4)
        { accessSlot (accessSlot substate message.currentTarget 3) message.currentTarget 4 with
          logs := substate.logs.push (paramsLog message.currentTarget
            (storageAt state message.currentTarget 3) (storageAt state message.currentTarget 4)) }) := by
  refine Triple.seq (Gas.Triple.seqL popR (restate (pc' := 5949) (by decide) rfl rfl
    (g' := gas - 2) (by gas_ok) rfl rfl)) ?_
  refine (paramsLogBlock hstatic hc3 hc4 size_MEM0 mload_MEM0 hfork (by omega)).consequence
    (fun _ h => h) ?_
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  exact ⟨hr, he, ho, by rw [hgas]; gas_ok, hs, hss⟩

/-- The execution gas of the stretch between the two writes of setParams. -/
abbrev paramsMid (state : State.TransactionState) (message : Message fork) (c9 : Bool) : Nat :=
  60 + slotCost c9 + 50 * exponentBytes (storageAt state message.currentTarget 9) +
    mulCost (wordArg message.data 1)

/-- The meter after the write of slot 3 in setParams, from the meter `g`. -/
abbrev paramsM1 (fork : Fork) (g : StateGasMeter) (state : State.TransactionState)
    (message : Message fork) (c0 c3 : Bool) : StateGasMeter :=
  wMeter fork g (807 + slotCost c0) (originalAt state message.currentTarget 3)
    (storageAt state message.currentTarget 3) (wordArg message.data 0) c3

/-- The meter after the write of slot 4 in setParams. -/
abbrev paramsM2 (fork : Fork) (g : StateGasMeter) (state : State.TransactionState)
    (message : Message fork) (c0 c3 c9 c4 : Bool) : StateGasMeter :=
  wMeter fork (paramsM1 fork g state message c0 c3) (paramsMid state message c9)
    (originalAt state message.currentTarget 4) (storageAt state message.currentTarget 4)
    (feeWord state message) c4

/-- **setParams(b, m) over the EIP-8037 meter, exactly, at any reservoir, refills allowed.** From Berlin,
from a frame `m` of `StateGasMeter` with any meter whose `toNat` is the fresh frame of `CODE` with
selector 0xc0324c77, by the owner, `b < 20`, `m < 50` and no overflow of `m * 10^d`, a frame that is not static and an account: the run, for any gas bound and
message runner, ends with no error if and only if the chain condition holds (`wOk` of the first
write from `m.gas`, `wOk` of the second write from the meter after the first, and the gas of the
tail at most the execution gas left after the second). The meter after a write carries its refill
to the reservoir and the spill that the next write reads, so a refill of the first write can pay
the state gas of the second. Every run that ends with no error stops with the end of the Nat
specification (output, state, substate), with `gasLeft` plus the gas of the Nat specification
equal to `gas` plus the two bumps, and with the meter after the second write for the rest. -/
theorem setParams_sgm (hfork : .berlin ≤ fork)
    (hstatic : message.isStatic = false) (hacc : hasAccount state message.currentTarget)
    (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xc0324c77)
    (hv : message.value = 0) (hown : callerWord message = ownerOf state message.currentTarget)
    (hb : (wordArg message.data 0).toNat < 20) (hm : (wordArg message.data 1).toNat < 50)
    (hov : (wordArg message.data 1).toNat *
      (exp (0x0a : U256) (storageAt state message.currentTarget 9)).toNat < 2 ^ 256)
    {c0 c3 c9 c4 : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hc3 : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget 3 = c3)
    (hc9 : coldIn (accessSlot (accessSlot substate message.currentTarget 0) message.currentTarget 3)
      message.currentTarget 9 = c9)
    (hc4 : coldIn (accessSlot (accessSlot (accessSlot substate message.currentTarget 0)
      message.currentTarget 3) message.currentTarget 9) message.currentTarget 4 = c4)
    {gas : Nat} {m : Evm fork StateGasMeter}
    (start : At CODE message 0 [] .empty gas state substate (Meter.toNat m))
    {bound : Nat} {runChild : MessageRunner fork StateGasMeter bound}
    (within : GasMeter.gasHeld m.gas ≤ bound) :
    (Shadow.RunsOkS fork bound runChild m within ↔
      wOk fork m.gas (807 + slotCost c0) (originalAt state message.currentTarget 3)
          (storageAt state message.currentTarget 3) (wordArg message.data 0) c3 ∧
      wOk fork (paramsM1 fork m.gas state message c0 c3) (paramsMid state message c9)
          (originalAt state message.currentTarget 4) (storageAt state message.currentTarget 4)
          (feeWord state message) c4 ∧
      1558 ≤ (paramsM2 fork m.gas state message c0 c3 c9 c4).gasLeft) ∧
    ∀ s, Evm.runFrame (step fork) (step_decreases fork) bound runChild m within = .ok s →
      s.error = none →
      s.running = false ∧ s.output = .empty ∧ s.state = paramsState state message ∧
      s.substate = paramsSub fork substate state message ∧
      s.gas.gasLeft + (2425 + paramsCost fork state message c0 c3 c9 c4) =
        gas + wBump fork m.gas (originalAt state message.currentTarget 3)
            (storageAt state message.currentTarget 3) (wordArg message.data 0) +
          wBump fork (paramsM1 fork m.gas state message c0 c3)
            (originalAt state message.currentTarget 4) (storageAt state message.currentTarget 4)
            (feeWord state message) ∧
      s.gas = { paramsM2 fork m.gas state message c0 c3 c9 c4 with gasLeft := s.gas.gasLeft } := by
  have hacc0 := hasAccount_readSlot (n := 0) (other := message.currentTarget) hacc
  have hacc1 := hasAccount_writeSlot (n := 3) (v := wordArg message.data 0) hacc0
  have hacc2 := hasAccount_readSlot (n := 9) (other := message.currentTarget) hacc1
  have h9 : storageAt (writeSlot (readSlot state message.currentTarget 0) message.currentTarget 3
      (wordArg message.data 0)) message.currentTarget 9 = storageAt state message.currentTarget 9 := by
    rw [storageAt_writeSlot_of_ne hacc0 (by decide), storageAt_readSlot]
  have hP : 807 + slotCost c0 < 97920 := by have := Complete.slotCost_le c0; omega
  have hQ : paramsMid state message c9 < 97920 := by
    have := Complete.slotCost_le c9
    have := Refill.exponentBytes_le (storageAt state message.currentTarget 9)
    have : mulCost (wordArg message.data 1) ≤ 138 := by unfold mulCost; split <;> omega
    simp only [paramsMid]; omega
  have hw2 := fun g (hg : paramsMid state message c9 ≤ g) => paramsW2 (b := wordArg message.data 0)
    (m := wordArg message.data 1) (x := BitVec.ofNat 256 (selector message.data))
    (state := writeSlot (readSlot state message.currentTarget 0) message.currentTarget 3
      (wordArg message.data 0))
    (substate := storeSub fork (accessSlot substate message.currentTarget 0) message.currentTarget 3
      (originalAt (readSlot state message.currentTarget 0) message.currentTarget 3)
      (storageAt (readSlot state message.currentTarget 0) message.currentTarget 3)
      (wordArg message.data 0))
    (M := MEM0) hfork (c9 := c9) hc9 (by rw [h9]; exact hov) (gas := g) (by rw [h9]; exact hg)
  rw [h9] at hw2
  have hc4' : coldIn (accessSlot (storeSub fork (accessSlot substate message.currentTarget 0)
      message.currentTarget 3
      (originalAt (readSlot state message.currentTarget 0) message.currentTarget 3)
      (storageAt (readSlot state message.currentTarget 0) message.currentTarget 3)
      (wordArg message.data 0)) message.currentTarget 9) message.currentTarget 4 = c4 := hc4
  have hpost := fun g (hg : 1558 ≤ g) => paramsPost (fork := fork) (message := message)
    (f := feeWord state message) (b := wordArg message.data 0) (m := wordArg message.data 1)
    (x := BitVec.ofNat 256 (selector message.data))
    (state := writeSlot (readSlot (writeSlot (readSlot state message.currentTarget 0)
      message.currentTarget 3 (wordArg message.data 0)) message.currentTarget 9)
      message.currentTarget 4 (feeWord state message))
    (substate := storeSub fork (accessSlot (storeSub fork (accessSlot substate message.currentTarget 0)
      message.currentTarget 3
      (originalAt (readSlot state message.currentTarget 0) message.currentTarget 3)
      (storageAt (readSlot state message.currentTarget 0) message.currentTarget 3)
      (wordArg message.data 0)) message.currentTarget 9) message.currentTarget 4
      (originalAt (readSlot (writeSlot (readSlot state message.currentTarget 0)
        message.currentTarget 3 (wordArg message.data 0)) message.currentTarget 9)
        message.currentTarget 4)
      (storageAt (readSlot (writeSlot (readSlot state message.currentTarget 0)
        message.currentTarget 3 (wordArg message.data 0)) message.currentTarget 9)
        message.currentTarget 4) (feeWord state message))
    hstatic (TransferFee.coldIn_storeSub_false (TransferFrom.coldIn_accessSlot_false
      (coldIn_accessSlot_self _ _ _))) (coldIn_accessSlot_self _ _ _) hfork hg
  have hx := Complete.exactS_write hfork (paramsW1 hfork hsize hsize' hsel hv hown hb hm hc0)
    hP (fun _ _ => rfl) (by code_fact) (by code_fact) hstatic hacc0 hc3
    (Complete.exactS_write hfork hw2 hQ
      (fun _ _ => rfl) (by code_fact) (by code_fact) hstatic hacc2 hc4'
      (Complete.exactS_halt hpost (by decide) (fun _ _ => rfl)))
  obtain ⟨hgas, hiff, hend⟩ := hx.run start (runChild := runChild) within
  have h4 : storageAt (readSlot (writeSlot (readSlot state message.currentTarget 0)
      message.currentTarget 3 (wordArg message.data 0)) message.currentTarget 9)
      message.currentTarget 4 = storageAt state message.currentTarget 4 := by
    rw [storageAt_readSlot, storageAt_writeSlot_of_ne hacc0 (by decide), storageAt_readSlot]
  simp only [originalAt_readSlot, originalAt_writeSlot hacc0, h4] at hiff
  rw [storageAt_readSlot] at hiff
  refine ⟨hiff, fun s hrun hok => ?_⟩
  have hok' := hiff.mp ⟨s, hrun, hok⟩
  obtain ⟨h1, h2, h3, h5, h6⟩ := hend s hrun hok
  simp only [originalAt_readSlot, originalAt_writeSlot hacc0, h4] at h6
  rw [storageAt_readSlot] at h6
  have hacc3 := hasAccount_writeSlot (n := 4) (v := feeWord state message) hacc2
  refine ⟨h1, h2, h3, ?_, ?_, ?_⟩
  · have hR3 : storageAt (writeSlot (readSlot (writeSlot (readSlot state message.currentTarget 0)
        message.currentTarget 3 (wordArg message.data 0)) message.currentTarget 9)
        message.currentTarget 4 (feeWord state message)) message.currentTarget 3 =
        wordArg message.data 0 := by
      rw [storageAt_writeSlot_of_ne hacc2 (by decide), storageAt_readSlot,
        storageAt_writeSlot_self hacc0]
    have hR4 : storageAt (writeSlot (readSlot (writeSlot (readSlot state message.currentTarget 0)
        message.currentTarget 3 (wordArg message.data 0)) message.currentTarget 9)
        message.currentTarget 4 (feeWord state message)) message.currentTarget 4 =
        feeWord state message := storageAt_writeSlot_self hacc2
    rw [h5, hR3, hR4]
    repeat' first
      | rw [originalAt_readSlot]
      | rw [originalAt_writeSlot hacc0]
      | rw [h4]
      | rw [storageAt_readSlot]
  · obtain ⟨o1, o2, o3⟩ := hok'
    have e1 := Complete.wMeter_gasLeft o1
    have e2 := Complete.wMeter_gasLeft o2
    have e3 : s.gas.gasLeft = _ := congrArg StateGasMeter.gasLeft h6
    simp only [paramsCost, wBump, paramsM1, paramsM2, paramsMid, feeWord] at e1 e2 e3 o3 ⊢
    omega
  · rw [h6]

end UsdtVerify.SetParamsSpec

namespace UsdtVerify.DestroySpec
open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts
open Transfer TransferOk Owner Admin BlackList Issue Destroy
open Complete (wBump wSgm wOk wMeter)
variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate}

/-- At 8008 (destroyBlackFunds): from the `JUMPDEST` to the `SSTORE` of `balances[a]` (8078). -/
theorem zeroToW {a b : U256} {rest : List U256} (hrest : rest.length ≤ 800) {M : ByteArray}
    (hM : M.size = 96) {gas : Nat} (hg : 108 ≤ gas) :
    Gas.HoareG fork (At CODE message 8008 (b :: 0 :: a :: rest) M gas state substate)
      (At CODE message 8078 (mapSlot (mkey a) 2 :: 0 :: 0 :: b :: a :: rest) (mapMem M (mkey a) 2)
        (gas - 108) state substate) := by
  zero_pre
  exact restate (by decide) rfl rfl (by gas_ok) rfl rfl

/-- From pc 0 to the `SSTORE` of `balances[a]` (8078) in a successful `destroyBlackFunds(a)`. -/
theorem destroyW1 (hfork : .berlin ≤ fork)
    (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xf3bdc228)
    (hv : message.value = 0) (hown : callerWord message = ownerOf state message.currentTarget)
    (hl : (storageAt state message.currentTarget (listSlot (addrArg message.data 0))).toNat % 256 ≠ 0)
    (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    {c0 cL c10 cB : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hcL : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget
      (listSlot (addrArg message.data 0)) = cL)
    (hc10 : coldIn (preSub substate message) message.currentTarget 10 = c10)
    (hcB : coldIn (accessSlot (preSub substate message) message.currentTarget 10)
      message.currentTarget (balSlot message) = cB)
    (gas : Nat) (hg : 1462 + slotCost c0 + slotCost cL + slotCost c10 + slotCost cB ≤ gas) :
    Gas.HoareG fork (At CODE message 0 [] .empty gas state substate)
      (At CODE message 8078 (balSlot message :: 0 :: 0 :: dirty state message ::
          addrArg message.data 0 :: [0x09b6, BitVec.ofNat 256 (selector message.data)])
        (mapMem (BalanceOf.lookMem (MEMB message) (addrArg message.data 0))
          (addrArg message.data 0) 2)
        (gas - (1462 + slotCost c0 + slotCost cL + slotCost c10 + slotCost cB))
        (readState state message) (readSub substate message)) := by
  have hkey : BalanceOf.key (addrArg message.data 0) = addrArg message.data 0 :=
    mkey_addrArg message.data 0
  have hk := mkey_addrArg message.data 0
  have hM1 : (MEMB message).size = 96 := size_mapMem size_MEM0 _ _
  refine Triple.seq (toGetter hfork hsize hsize' hsel hv hown hl hc0 hcL (by omega)) ?_
  step depCheck hfork (Or.inr (Or.inl ⟨rfl, rfl⟩)) (by simp)
    (by simp only [preState, storageAt_readSlot]; exact hdep) hc10 (by gas_ok)
  step BalanceOf.toLookup (by simp) (by gas_ok)
  step BalanceOf.lookup hfork (by simp) hM1 (cB := cB) (by rw [hkey]; exact hcB) (by gas_ok)
  rw [hkey, storageAt_readSlot, storageAt_readSlot, storageAt_readSlot]
  step BalanceOf.back (Or.inr rfl) (by gas_ok)
  refine Triple.seq (zeroToW (by simp) (BalanceOf.size_lookMem hM1 _) (by gas_ok)) ?_
  rw [hk]
  exact restate rfl rfl rfl (by gas_ok) rfl rfl

/-- From the `POP` at 8079 after the `SSTORE` of `balances[a]` to the `SSTORE` of `_totalSupply`
(8094). -/
theorem destroyW2 (hfork : .berlin ≤ fork) {a b x : U256} {c1 : Bool}
    (hc1 : coldIn substate message.currentTarget 1 = c1) {M : ByteArray} {gas : Nat}
    (hg : 33 + slotCost c1 ≤ gas) :
    Gas.HoareG fork (At CODE message 8079 [0, b, a, 0x09b6, x] M gas state substate)
      (At CODE message 8094 (1 :: sub (storageAt state message.currentTarget 1) b ::
          sub (storageAt state message.currentTarget 1) b :: [b, a, 0x09b6, x]) M
        (gas - (33 + slotCost c1)) (readSlot state message.currentTarget 1)
        (accessSlot substate message.currentTarget 1)) := by
  refine Triple.seq (Gas.Triple.seqL popR (restate (pc' := 8080) (by decide) rfl rfl
    (g' := gas - 2) (by gas_ok) rfl rfl)) ?_
  step dupR 0
  step pushR 1 (0x01 : U256)
  step pushR 1 (0 : U256)
  step dupR 2
  step dupR 2
  step Gas.sloadG hfork (cold := c1) (by code_fact) (by code_fact) hc1 (by gas_ok)
  rw [getStorage_eq]
  step binR 0x03 instruction_sub
  step swapR 2
  norm
  step popR
  step popR
  step dupR 1
  step swapR 0
  norm
  exact restate (by decide) rfl rfl (by gas_ok) rfl rfl

/-- From the `POP` at 8095 after the `SSTORE` of `_totalSupply` to the STOP. -/
theorem destroyPost {a b c x : U256} (hstatic : message.isStatic = false) {M : ByteArray}
    (hM : M.size = 96) (hptr : loadWord (memoryReadBytes M 64 32) 0 32 = 0x60) {gas : Nat}
    (hg : 1370 ≤ gas) :
    Gas.SpecG fork (At CODE message 8095 [c, b, a, 0x09b6, x] M gas state substate)
      (Halted false .empty (gas - 1370) state
        { substate with logs := substate.logs.push (destroyLog message.currentTarget (mkey a) b) }) := by
  refine Triple.seq (Gas.Triple.seqL popR (restate (pc' := 8096) (by decide) rfl rfl
    (g' := gas - 2) (by gas_ok) rfl rfl)) ?_
  refine (logBlock hstatic hM hptr (by omega)).consequence (fun _ h => h) ?_
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  exact ⟨hr, he, ho, by rw [hgas]; gas_ok, hs, hss⟩

/-- The meter after the write of `balances[a]` in destroyBlackFunds, from the meter `g`. -/
abbrev destroyM1 (fork : Fork) (g : StateGasMeter) (state : State.TransactionState)
    (message : Message fork) (P : Nat) : StateGasMeter :=
  wMeter fork g P (originalAt state message.currentTarget (balSlot message)) (dirty state message)
    0 false

/-- The meter after the write of `_totalSupply` in destroyBlackFunds. -/
abbrev destroyM2 (fork : Fork) (g : StateGasMeter) (state : State.TransactionState)
    (message : Message fork) (P : Nat) (c1 : Bool) : StateGasMeter :=
  wMeter fork (destroyM1 fork g state message P) (33 + slotCost c1)
    (originalAt state message.currentTarget 1) (storageAt (state1 state message) message.currentTarget 1)
    (sub (storageAt (state1 state message) message.currentTarget 1) (dirty state message)) false

/-- **destroyBlackFunds(a) over the EIP-8037 meter, exactly, at any reservoir, refills allowed.** From Berlin,
from a frame `m` of `StateGasMeter` with any meter whose `toNat` is the fresh frame of `CODE` with
selector 0xf3bdc228, by the owner, `a` blacklisted, not deprecated, a frame that is not static and an account: the run, for any gas bound and
message runner, ends with no error if and only if the chain condition holds (`wOk` of the first
write from `m.gas`, `wOk` of the second write from the meter after the first, and the gas of the
tail at most the execution gas left after the second). The meter after a write carries its refill
to the reservoir and the spill that the next write reads, so a refill of the first write can pay
the state gas of the second. Every run that ends with no error stops with the end of the Nat
specification (output, state, substate), with `gasLeft` plus the gas of the Nat specification
equal to `gas` plus the two bumps, and with the meter after the second write for the rest. -/
theorem destroyBlackFunds_sgm (hfork : .berlin ≤ fork)
    (hstatic : message.isStatic = false) (hacc : hasAccount state message.currentTarget)
    (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xf3bdc228)
    (hv : message.value = 0) (hown : callerWord message = ownerOf state message.currentTarget)
    (hl : (storageAt state message.currentTarget (listSlot (addrArg message.data 0))).toNat % 256 ≠ 0)
    (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    {c0 cL c10 cB c1 : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hcL : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget
      (listSlot (addrArg message.data 0)) = cL)
    (hc10 : coldIn (preSub substate message) message.currentTarget 10 = c10)
    (hcB : coldIn (accessSlot (preSub substate message) message.currentTarget 10)
      message.currentTarget (balSlot message) = cB)
    (hc1 : coldIn (readSub substate message) message.currentTarget 1 = c1)
    {gas : Nat} {m : Evm fork StateGasMeter}
    (start : At CODE message 0 [] .empty gas state substate (Meter.toNat m))
    {bound : Nat} {runChild : MessageRunner fork StateGasMeter bound}
    (within : GasMeter.gasHeld m.gas ≤ bound) :
    (Shadow.RunsOkS fork bound runChild m within ↔
      wOk fork m.gas (1462 + slotCost c0 + slotCost cL + slotCost c10 + slotCost cB)
          (originalAt state message.currentTarget (balSlot message)) (dirty state message) 0 false ∧
      wOk fork (destroyM1 fork m.gas state message
            (1462 + slotCost c0 + slotCost cL + slotCost c10 + slotCost cB))
          (33 + slotCost c1) (originalAt state message.currentTarget 1)
          (storageAt (state1 state message) message.currentTarget 1)
          (sub (storageAt (state1 state message) message.currentTarget 1) (dirty state message))
          false ∧
      1370 ≤ (destroyM2 fork m.gas state message
        (1462 + slotCost c0 + slotCost cL + slotCost c10 + slotCost cB) c1).gasLeft) ∧
    ∀ s, Evm.runFrame (step fork) (step_decreases fork) bound runChild m within = .ok s →
      s.error = none →
      s.running = false ∧ s.output = .empty ∧ s.state = destroyState state message ∧
      s.substate = destroySub fork substate state message ∧
      s.gas.gasLeft + (2865 + slotCost c0 + slotCost cL + slotCost c10 + slotCost cB +
          slotCost c1 + costB fork state message + costT fork state message) =
        gas + wBump fork m.gas (originalAt state message.currentTarget (balSlot message))
            (dirty state message) 0 +
          wBump fork (destroyM1 fork m.gas state message
              (1462 + slotCost c0 + slotCost cL + slotCost c10 + slotCost cB))
            (originalAt state message.currentTarget 1)
            (storageAt (state1 state message) message.currentTarget 1)
            (sub (storageAt (state1 state message) message.currentTarget 1) (dirty state message)) ∧
      s.gas = { destroyM2 fork m.gas state message
          (1462 + slotCost c0 + slotCost cL + slotCost c10 + slotCost cB) c1 with
          gasLeft := s.gas.gasLeft } := by
  have hk := mkey_addrArg message.data 0
  have hacc1 : hasAccount (readState state message) message.currentTarget :=
    hasAccount_readSlot (hasAccount_readSlot (hasAccount_readSlot (hasAccount_readSlot hacc)))
  have hacc2 := hasAccount_writeSlot (n := balSlot message) (v := 0) hacc1
  have hacc3 := hasAccount_readSlot (n := 1) (other := message.currentTarget) hacc2
  have hM1 : (MEMB message).size = 96 := size_mapMem size_MEM0 _ _
  have hp1 : loadWord (memoryReadBytes (MEMB message) 64 32) 0 32 = 0x60 :=
    ptr_mapMem size_MEM0 mload_MEM0 _ _
  have hP : 1462 + slotCost c0 + slotCost cL + slotCost c10 + slotCost cB < 97920 := by
    have := Complete.slotCost_le c0; have := Complete.slotCost_le cL
    have := Complete.slotCost_le c10; have := Complete.slotCost_le cB; omega
  have hQ : 33 + slotCost c1 < 97920 := by have := Complete.slotCost_le c1; omega
  have hc1' : coldIn (storeSub fork (readSub substate message) message.currentTarget
      (balSlot message) (originalAt (readState state message) message.currentTarget (balSlot message))
      (storageAt (readState state message) message.currentTarget (balSlot message)) 0)
      message.currentTarget 1 = c1 := by
    rw [TransferFee.coldIn_storeSub', accessSlot_accessSlot]; exact hc1
  have hw2 := fun g (hg : 33 + slotCost c1 ≤ g) => destroyW2 (a := addrArg message.data 0)
    (b := dirty state message) (x := BitVec.ofNat 256 (selector message.data))
    (M := mapMem (BalanceOf.lookMem (MEMB message) (addrArg message.data 0))
      (addrArg message.data 0) 2)
    (state := writeSlot (readState state message) message.currentTarget (balSlot message) 0)
    (substate := storeSub fork (readSub substate message) message.currentTarget
      (balSlot message) (originalAt (readState state message) message.currentTarget (balSlot message))
      (storageAt (readState state message) message.currentTarget (balSlot message)) 0)
    hfork hc1' (gas := g) hg
  have hpost := fun g (hg : 1370 ≤ g) => destroyPost (fork := fork) (message := message)
    (a := addrArg message.data 0) (b := dirty state message)
    (c := sub (storageAt (writeSlot (readState state message) message.currentTarget
      (balSlot message) 0) message.currentTarget 1) (dirty state message))
    (x := BitVec.ofNat 256 (selector message.data))
    (M := mapMem (BalanceOf.lookMem (MEMB message) (addrArg message.data 0))
      (addrArg message.data 0) 2)
    (state := writeSlot (readSlot (writeSlot (readState state message) message.currentTarget
      (balSlot message) 0) message.currentTarget 1) message.currentTarget 1
      (sub (storageAt (writeSlot (readState state message) message.currentTarget
        (balSlot message) 0) message.currentTarget 1) (dirty state message)))
    (substate := storeSub fork (accessSlot (storeSub fork (readSub substate message)
      message.currentTarget (balSlot message)
      (originalAt (readState state message) message.currentTarget (balSlot message))
      (storageAt (readState state message) message.currentTarget (balSlot message)) 0)
      message.currentTarget 1) message.currentTarget 1
      (originalAt (readSlot (writeSlot (readState state message) message.currentTarget
        (balSlot message) 0) message.currentTarget 1) message.currentTarget 1)
      (storageAt (readSlot (writeSlot (readState state message) message.currentTarget
        (balSlot message) 0) message.currentTarget 1) message.currentTarget 1)
      (sub (storageAt (writeSlot (readState state message) message.currentTarget
        (balSlot message) 0) message.currentTarget 1) (dirty state message)))
    hstatic (size_mapMem (BalanceOf.size_lookMem hM1 _) _ _)
    (ptr_mapMem (BalanceOf.size_lookMem hM1 _) (ptr_mapMem hM1 hp1 _ _) _ _) hg
  have hx := Complete.exactS_write hfork
    (destroyW1 hfork hsize hsize' hsel hv hown hl hdep hc0 hcL hc10 hcB) hP (fun _ _ => rfl)
    (by code_fact) (by code_fact) hstatic hacc1 (coldIn_accessSlot_self _ _ _)
    (Complete.exactS_write hfork hw2 hQ (fun _ _ => rfl) (by code_fact) (by code_fact) hstatic
      hacc3 (coldIn_accessSlot_self _ _ _)
      (Complete.exactS_halt hpost (by decide) (fun _ _ => rfl)))
  obtain ⟨hgas, hiff, hend⟩ := hx.run start (runChild := runChild) within
  simp only [originalAt_readSlot, storageAt_readSlot, originalAt_writeSlot hacc1] at hiff
  refine ⟨hiff, fun s hrun hok => ?_⟩
  have hok' := hiff.mp ⟨s, hrun, hok⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := hend s hrun hok
  simp only [originalAt_readSlot, storageAt_readSlot, originalAt_writeSlot hacc1] at h5
  refine ⟨h1, h2, ?_, ?_, ?_, ?_⟩
  · rw [h3]
    repeat' first
      | rw [writeSlot_readSlot _ _ hacc2]
      | rw [storageAt_readSlot]
  · rw [h4, storeSub_accessSlot, hk]
    repeat' first
      | rw [originalAt_readSlot]
      | rw [originalAt_writeSlot hacc1]
      | rw [storageAt_readSlot]
  · obtain ⟨o1, o2, o3⟩ := hok'
    have e1 := Complete.wMeter_gasLeft o1
    have e2 := Complete.wMeter_gasLeft o2
    have e3 : s.gas.gasLeft = _ := congrArg StateGasMeter.gasLeft h5
    simp only [costB, costT, wBump, destroyM1, destroyM2, state1, dirty, balSlot] at e1 e2 e3 o3 ⊢
    omega
  · rw [h5]

end UsdtVerify.DestroySpec
