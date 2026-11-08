import UsdtVerify.Usdt.Spec.Destroy
import UsdtVerify.Usdt.Spec.SetParams
import UsdtVerify.Usdt.Refill.Transfer

/-!
# The owner functions with two writes: the success paths over `StepI`

`spec_issue`, `spec_redeem`, `spec_setParams` and `DestroySpec.spec` over `StepI`, split at the
point between their two writes, each stretch lifted with `HoareG.toIA` (no write),
`HoareG.toIW` / `HoareG.toIW'` (one write) or `SpecG.toIA` (the end).

- `spec_issueI`: the write of `balances[owner]` adds without overflow (`refill_add`). The write of
  `_totalSupply` adds to the word read after the first write, which may be that same slot, so it
  takes `hnrT`.
- `spec_redeemI`: both writes subtract: `hnrT` (`_totalSupply`) and `hnrO` (`balances[owner]`,
  read after the first write).
-/

namespace UsdtVerify.IssueSpec

open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts
open Transfer TransferOk Owner Admin BlackList Issue Refill

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate}

/-- `spec_issue` over `StepI`, when the write of `_totalSupply` refills nothing (`hnrT`). -/
theorem spec_issueI (hfork : .berlin ≤ fork)
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
    (hnrT : sstoreStateRefill fork (originalAt state message.currentTarget 1)
      (storageAt (issueState1 state message) message.currentTarget 1)
      (add (storageAt (issueState1 state message) message.currentTarget 1)
        (wordArg message.data 0)) = 0)
    {gas : Nat}
    (hstip : 4248 + slotCost c0 + slotCost c1 + slotCost cO + issueCostO fork state message ≤ gas)
    (hg : 3024 + slotCost c0 + slotCost c1 + slotCost cO + issueCostO fork state message +
      issueCostT fork state message ≤ gas) :
    HoareI fork (At CODE message 0 [] .empty gas state substate)
      (fun evm => evm.running = false ∧ Halted false .empty (gas - (3024 + slotCost c0 +
          slotCost c1 + slotCost cO + issueCostO fork state message +
          issueCostT fork state message))
        (issueState state message) (issueSub fork substate state message) evm) := by
  simp only [issueCostO, issueCostT, issueState1] at hstip hg hnrT ⊢
  have hacc1 : hasAccount (readSlot (reqState state message.currentTarget) message.currentTarget 0)
      message.currentTarget :=
    hasAccount_readSlot (hasAccount_readSlot (hasAccount_readSlot (hasAccount_readSlot hacc)))
  have hacc2 : hasAccount (reqState state message.currentTarget) message.currentTarget :=
    hasAccount_readSlot (hasAccount_readSlot (hasAccount_readSlot hacc))
  have hw0 : coldIn (reqSub substate state message.currentTarget) message.currentTarget 0 =
      false :=
    TransferFrom.coldIn_accessSlot_false (TransferFrom.coldIn_accessSlot_false
      (coldIn_accessSlot_self _ _ _))
  have hwO : coldIn (reqSub substate state message.currentTarget) message.currentTarget
      (ownerBal (reqState state message.currentTarget) message.currentTarget) = false := by
    rw [ownerBal_readSlot, ownerBal_readSlot, ownerBal_readSlot]
    exact coldIn_accessSlot_self _ _ _
  have hw1 : coldIn (storeSub fork (accessSlot (reqSub substate state message.currentTarget)
      message.currentTarget 0) message.currentTarget (ownerBal state message.currentTarget)
      (originalAt state message.currentTarget (ownerBal state message.currentTarget))
      (storageAt state message.currentTarget (ownerBal state message.currentTarget))
      (add (storageAt state message.currentTarget (ownerBal state message.currentTarget))
        (wordArg message.data 0))) message.currentTarget 1 = false :=
    TransferFee.coldIn_storeSub_false (TransferFrom.coldIn_accessSlot_false
      (TransferFrom.coldIn_accessSlot_false (coldIn_accessSlot_self _ _ _)))
  refine Triple.seq (HoareG.toIA (issuePre hfork hsize hsize' hsel hv hown hT hc0 hc1 hcO
    (by omega)) (by cheap) (by same_store)) ?_
  stepC (reqPass (Or.inr (Or.inl ⟨rfl, rfl⟩)) (gtAdd_ne ⟨hT.1, hB⟩) (by simp) (by gas_ok))
  refine Triple.seq (HoareG.toIW' (issueOwner hfork (by simp) hstatic hacc2 hw0 hwO
    (size_mapMem (size_mapMem size_MEM0 _ _) _ _) (by gas_ok)
    (by simp only [ownerBal_readSlot, storageAt_readSlot, originalAt_readSlot]; gas_ok))
    (getStorage_readSlot _ _ _) (by omega) hacc1
    (by simp only [ownerBal_readSlot, storageAt_readSlot, originalAt_readSlot]; gas_ok)
    (by simp only [ownerBal_readSlot, storageAt_readSlot, originalAt_readSlot]
        exact refill_add hB)) ?_
  simp only [ownerBal_readSlot, ownerOf_readSlot, storageAt_readSlot, originalAt_readSlot]
  refine Triple.seq (HoareG.toIW (issueTotal hfork (by simp) hstatic (hasAccount_writeSlot hacc1)
    hw1 (by gas_ok)
    (by rw [originalAt_writeSlot hacc1, originalAt_readSlot, originalAt_readSlot,
      originalAt_readSlot, originalAt_readSlot]; gas_ok))
    (by omega) (hasAccount_writeSlot hacc1)
    (by rw [originalAt_writeSlot hacc1, originalAt_readSlot, originalAt_readSlot,
      originalAt_readSlot, originalAt_readSlot]; gas_ok)
    (by rw [originalAt_writeSlot hacc1, originalAt_readSlot, originalAt_readSlot,
      originalAt_readSlot, originalAt_readSlot]; exact hnrT)) ?_
  rw [originalAt_writeSlot hacc1, originalAt_readSlot, originalAt_readSlot,
      originalAt_readSlot, originalAt_readSlot]
  refine (SpecG.toIA (amountLog (Or.inl ⟨rfl, rfl, rfl⟩) hstatic
    (size_mapMem (size_mapMem (size_mapMem size_MEM0 _ _) _ _) _ _)
    (ptr_mapMem (size_mapMem (size_mapMem size_MEM0 _ _) _ _)
      (ptr_mapMem (size_mapMem size_MEM0 _ _) (ptr_mapMem size_MEM0 mload_MEM0 _ _) _ _) _ _)
    (by gas_ok)) (by cheap) (fun _ _ => rfl)).consequence (fun _ h => h) ?_
  rintro evm ⟨hr0, hr, he, ho, hgas, hs, hss⟩
  exact ⟨hr0, hr, he, ho, by rw [hgas]; gas_ok, hs, hss⟩

/-- `spec_redeem` over `StepI`, when the writes of `_totalSupply` (`hnrT`) and of
`balances[owner]` (`hnrO`) refill nothing. -/
theorem spec_redeemI (hfork : .berlin ≤ fork)
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
    (hnrT : sstoreStateRefill fork (originalAt state message.currentTarget 1)
      (storageAt state message.currentTarget 1)
      (sub (storageAt state message.currentTarget 1) (wordArg message.data 0)) = 0)
    (hnrO : sstoreStateRefill fork
      (originalAt state message.currentTarget (ownerBal state message.currentTarget))
      (storageAt (redeemState1 state message) message.currentTarget
        (ownerBal state message.currentTarget))
      (sub (storageAt (redeemState1 state message) message.currentTarget
        (ownerBal state message.currentTarget)) (wordArg message.data 0)) = 0)
    {gas : Nat}
    (hstip : 3838 + slotCost c0 + slotCost c1 + slotCost cO + redeemCostT fork state message ≤ gas)
    (hg : 2614 + slotCost c0 + slotCost c1 + slotCost cO + redeemCostT fork state message +
      redeemCostO fork state message ≤ gas) :
    HoareI fork (At CODE message 0 [] .empty gas state substate)
      (fun evm => evm.running = false ∧ Halted false .empty (gas - (2614 + slotCost c0 +
          slotCost c1 + slotCost cO + redeemCostT fork state message +
          redeemCostO fork state message))
        (redeemState state message) (redeemSub fork substate state message) evm) := by
  simp only [redeemCostO, redeemCostT, redeemState1] at hstip hg hnrO ⊢
  have hacc2 : hasAccount (reqState state message.currentTarget) message.currentTarget :=
    hasAccount_readSlot (hasAccount_readSlot (hasAccount_readSlot hacc))
  have hacc3 := hasAccount_writeSlot (n := 1)
    (v := sub (storageAt state message.currentTarget 1) (wordArg message.data 0)) hacc2
  have hw1 : coldIn (reqSub substate state message.currentTarget) message.currentTarget 1 =
      false :=
    TransferFrom.coldIn_accessSlot_false (coldIn_accessSlot_self _ _ _)
  have hw0 : coldIn (storeSub fork (reqSub substate state message.currentTarget)
      message.currentTarget 1 (originalAt state message.currentTarget 1)
      (storageAt state message.currentTarget 1)
      (sub (storageAt state message.currentTarget 1) (wordArg message.data 0)))
      message.currentTarget 0 = false :=
    TransferFee.coldIn_storeSub_false (TransferFrom.coldIn_accessSlot_false
      (TransferFrom.coldIn_accessSlot_false (coldIn_accessSlot_self _ _ _)))
  have hwO : coldIn (storeSub fork (reqSub substate state message.currentTarget)
      message.currentTarget 1 (originalAt state message.currentTarget 1)
      (storageAt state message.currentTarget 1)
      (sub (storageAt state message.currentTarget 1) (wordArg message.data 0)))
      message.currentTarget (ownerBal (writeSlot (reqState state message.currentTarget)
        message.currentTarget 1
        (sub (storageAt state message.currentTarget 1) (wordArg message.data 0)))
        message.currentTarget) = false := by
    rw [ownerBal_writeSlot hacc2 (by decide), ownerBal_readSlot, ownerBal_readSlot,
      ownerBal_readSlot]
    exact TransferFee.coldIn_storeSub_false (coldIn_accessSlot_self _ _ _)
  refine Triple.seq (HoareG.toIA (redeemPre hfork hsize hsize' hsel hv hown hT hc0 hc1 hcO
    (by omega)) (by cheap) (by same_store)) ?_
  stepC (reqPass (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))) (ge_ne hB) (by simp) (by gas_ok))
  refine Triple.seq (HoareG.toIW (redeemTotal hfork (by simp) hstatic hacc2 hw1 (by gas_ok)
    (by simp only [storageAt_readSlot, originalAt_readSlot]; gas_ok))
    (by omega) hacc2 (by simp only [storageAt_readSlot, originalAt_readSlot]; gas_ok)
    (by simp only [storageAt_readSlot, originalAt_readSlot]; exact hnrT)) ?_
  simp only [storageAt_readSlot, originalAt_readSlot]
  refine Triple.seq (HoareG.toIW' (redeemOwner hfork (by simp) hstatic hacc3 hw0 hwO
    (size_mapMem size_MEM0 _ _) (by gas_ok)
    (by rw [ownerBal_writeSlot hacc2 (by decide), ownerBal_readSlot, ownerBal_readSlot,
      ownerBal_readSlot, originalAt_writeSlot hacc2, originalAt_readSlot, originalAt_readSlot,
      originalAt_readSlot]; gas_ok))
    (getStorage_readSlot _ _ _) (by omega) (hasAccount_readSlot hacc3)
    (by rw [ownerBal_writeSlot hacc2 (by decide), ownerBal_readSlot, ownerBal_readSlot,
      ownerBal_readSlot, originalAt_writeSlot hacc2, originalAt_readSlot, originalAt_readSlot,
      originalAt_readSlot]; gas_ok)
    (by rw [ownerBal_writeSlot hacc2 (by decide), ownerBal_readSlot, ownerBal_readSlot,
      ownerBal_readSlot, originalAt_writeSlot hacc2, originalAt_readSlot, originalAt_readSlot,
      originalAt_readSlot]; exact hnrO)) ?_
  rw [ownerBal_writeSlot hacc2 (by decide), ownerOf_writeSlot hacc2 (by decide)]
  simp only [ownerBal_readSlot, ownerOf_readSlot]
  rw [originalAt_writeSlot hacc2]
  simp only [originalAt_readSlot]
  refine (SpecG.toIA (amountLog (Or.inr ⟨rfl, rfl, rfl⟩) hstatic
    (size_mapMem (size_mapMem size_MEM0 _ _) _ _)
    (ptr_mapMem (size_mapMem size_MEM0 _ _) (ptr_mapMem size_MEM0 mload_MEM0 _ _) _ _)
    (by gas_ok)) (by cheap) (fun _ _ => rfl)).consequence (fun _ h => h) ?_
  rintro evm ⟨hr0, hr, he, ho, hgas, hs, hss⟩
  exact ⟨hr0, hr, he, ho, by rw [hgas]; gas_ok, hs, hss⟩

end UsdtVerify.IssueSpec

namespace UsdtVerify.SetParamsSpec

open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts
open Transfer TransferOk Owner Admin Issue SafeMath SetParams Refill

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate}

/-- `spec_setParams` over `StepI`, when the writes of slot 3 (`hnr3`) and slot 4 (`hnr4`) refill
nothing. -/
theorem spec_setParamsI (hfork : .berlin ≤ fork)
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
    (hnr3 : sstoreStateRefill fork (originalAt state message.currentTarget 3)
      (storageAt state message.currentTarget 3) (wordArg message.data 0) = 0)
    (hnr4 : sstoreStateRefill fork (originalAt state message.currentTarget 4)
      (storageAt state message.currentTarget 4) (feeWord state message) = 0)
    {gas : Nat}
    (hstip : 3168 + slotCost c0 + Gas.writeCost fork (originalAt state message.currentTarget 3)
      (storageAt state message.currentTarget 3) (wordArg message.data 0) c3 + slotCost c9 +
      50 * exponentBytes (storageAt state message.currentTarget 9) +
      mulCost (wordArg message.data 1) ≤ gas)
    (hg : 2425 + paramsCost fork state message c0 c3 c9 c4 ≤ gas) :
    HoareI fork (At CODE message 0 [] .empty gas state substate)
      (fun evm => evm.running = false ∧ Halted false .empty
        (gas - (2425 + paramsCost fork state message c0 c3 c9 c4))
        (paramsState state message) (paramsSub fork substate state message) evm) := by
  simp only [paramsCost, feeWord] at hg hnr4 ⊢
  have hacc0 := hasAccount_readSlot (n := 0) (other := message.currentTarget) hacc
  have hacc1 := hasAccount_writeSlot (n := 3) (v := wordArg message.data 0) hacc0
  have hacc2 := hasAccount_readSlot (n := 9) (other := message.currentTarget) hacc1
  have h9 : storageAt (writeSlot (readSlot state message.currentTarget 0) message.currentTarget 3
      (wordArg message.data 0)) message.currentTarget 9 = storageAt state message.currentTarget 9 := by
    rw [storageAt_writeSlot_of_ne hacc0 (by decide), storageAt_readSlot]
  have hc9' : coldIn (storeSub fork (accessSlot substate message.currentTarget 0)
      message.currentTarget 3 (originalAt state message.currentTarget 3)
      (storageAt state message.currentTarget 3) (wordArg message.data 0)) message.currentTarget 9 =
      c9 := hc9
  have hc4' : coldIn (accessSlot (storeSub fork (accessSlot substate message.currentTarget 0)
      message.currentTarget 3 (originalAt state message.currentTarget 3)
      (storageAt state message.currentTarget 3) (wordArg message.data 0)) message.currentTarget 9)
      message.currentTarget 4 = c4 := hc4
  have he9 := exponentBytes_le (storageAt state message.currentTarget 9)
  have hs0 : slotCost c0 ≤ 2100 := by cases c0 <;> decide
  have hs9 : slotCost c9 ≤ 2100 := by cases c9 <;> decide
  have hmc : mulCost (wordArg message.data 1) ≤ 138 := by
    simp only [mulCost]; split <;> omega
  stepC (toBody hsize hsize' hsel hv (by omega))
  stepC (ownerOk hfork (mem_CHECKS (by decide)) (by simp) hc0 hown (by gas_ok))
  stepC (repc (pc' := 5881) (by decide))
  stepC (test1 (by simp) (by gas_ok))
  stepC (pass (Or.inl ⟨rfl, rfl⟩) (lt_ne (by simpa using hb)) (by simp) (by gas_ok))
  stepC (test2 (by simp) (by gas_ok))
  stepC (pass (Or.inr ⟨rfl, rfl⟩) (lt_ne (by simpa using hm)) (by simp) (by gas_ok))
  refine Triple.seq (HoareG.toIW (write3 hfork (by simp) hstatic hacc0 hc3 (by gas_ok)
    (by rw [originalAt_readSlot, storageAt_readSlot]; gas_ok))
    (by omega) hacc0 (by rw [originalAt_readSlot, storageAt_readSlot]; gas_ok)
    (by rw [originalAt_readSlot, storageAt_readSlot]; exact hnr3)) ?_
  rw [originalAt_readSlot, storageAt_readSlot]
  refine Triple.seq (HoareG.toIA (mulCall hfork (c9 := c9) hc9' (by rw [h9]; exact hov)
    (by rw [h9]; gas_ok)) (by rw [h9]; omega) (getStorage_readSlot _ _ _)) ?_
  rw [h9]
  refine Triple.seq (HoareG.toIW (write4 hfork (by simp) hstatic hacc2 (c4 := c4) hc4' (by gas_ok)
    (by rw [originalAt_readSlot, storageAt_readSlot, originalAt_writeSlot hacc0,
      originalAt_readSlot, storageAt_writeSlot_of_ne hacc0 (by decide), storageAt_readSlot]; gas_ok))
    (by omega) hacc2
    (by rw [originalAt_readSlot, storageAt_readSlot, originalAt_writeSlot hacc0,
      originalAt_readSlot, storageAt_writeSlot_of_ne hacc0 (by decide), storageAt_readSlot]; gas_ok)
    (by rw [originalAt_readSlot, storageAt_readSlot, originalAt_writeSlot hacc0,
      originalAt_readSlot, storageAt_writeSlot_of_ne hacc0 (by decide), storageAt_readSlot]
        exact hnr4)) ?_
  rw [originalAt_readSlot, storageAt_readSlot, originalAt_writeSlot hacc0,
    originalAt_readSlot, storageAt_writeSlot_of_ne hacc0 (by decide), storageAt_readSlot]
  have hR3 : storageAt (writeSlot (readSlot (writeSlot (readSlot state message.currentTarget 0)
      message.currentTarget 3 (wordArg message.data 0)) message.currentTarget 9)
      message.currentTarget 4 (mul (wordArg message.data 1)
        (exp (0x0a : U256) (storageAt state message.currentTarget 9)))) message.currentTarget 3 =
      wordArg message.data 0 := by
    rw [storageAt_writeSlot_of_ne hacc2 (by decide), storageAt_readSlot,
      storageAt_writeSlot_self hacc0]
  have hR4 : storageAt (writeSlot (readSlot (writeSlot (readSlot state message.currentTarget 0)
      message.currentTarget 3 (wordArg message.data 0)) message.currentTarget 9)
      message.currentTarget 4 (mul (wordArg message.data 1)
        (exp (0x0a : U256) (storageAt state message.currentTarget 9)))) message.currentTarget 4 =
      mul (wordArg message.data 1) (exp (0x0a : U256) (storageAt state message.currentTarget 9)) :=
    storageAt_writeSlot_self hacc2
  refine (SpecG.toIA (paramsLogBlock hstatic ?c3 ?c4 size_MEM0 mload_MEM0 hfork (by gas_ok))
    (by omega) (fun _ _ => by simp only [getStorage_readSlot])).consequence (fun _ h => h) ?_
  case c3 =>
    exact TransferFee.coldIn_storeSub_false (TransferFrom.coldIn_accessSlot_false
      (coldIn_accessSlot_self _ _ _))
  case c4 => exact coldIn_accessSlot_self _ _ _
  rintro evm ⟨hr0, hr, he, ho, hgas, hs, hss⟩
  refine ⟨hr0, hr, he, ho, by rw [hgas]; gas_ok, hs, ?_⟩
  rw [hss, hR3, hR4]

end UsdtVerify.SetParamsSpec

namespace UsdtVerify.DestroySpec

open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts
open Transfer TransferOk Owner Admin BlackList Issue Destroy Refill

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate}

/-- `spec` over `StepI`, when the writes of `balances[a]` (`hnrB`) and of `_totalSupply`
(`hnrT`, read after the first write) refill nothing. -/
theorem specI (hfork : .berlin ≤ fork)
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
    (hnrB : sstoreStateRefill fork (originalAt state message.currentTarget (balSlot message))
      (dirty state message) 0 = 0)
    (hnrT : sstoreStateRefill fork (originalAt state message.currentTarget 1)
      (storageAt (state1 state message) message.currentTarget 1)
      (sub (storageAt (state1 state message) message.currentTarget 1) (dirty state message)) = 0)
    {gas : Nat}
    (hstip1 : 3763 + slotCost c0 + slotCost cL + slotCost c10 + slotCost cB ≤ gas)
    (hstip2 : 3796 + slotCost c0 + slotCost cL + slotCost c10 + slotCost cB +
      costB fork state message + slotCost c1 ≤ gas)
    (hg : 2865 + slotCost c0 + slotCost cL + slotCost c10 + slotCost cB + slotCost c1 +
      costB fork state message + costT fork state message ≤ gas) :
    HoareI fork (At CODE message 0 [] .empty gas state substate)
      (fun evm => evm.running = false ∧ Halted false .empty (gas - (2865 + slotCost c0 +
          slotCost cL + slotCost c10 + slotCost cB + slotCost c1 + costB fork state message +
          costT fork state message))
        (destroyState state message) (destroySub fork substate state message) evm) := by
  simp only [costB, costT, dirty, balSlot, state1] at hstip2 hg hnrB hnrT ⊢
  have hkey : BalanceOf.key (addrArg message.data 0) = addrArg message.data 0 :=
    mkey_addrArg message.data 0
  have hk := mkey_addrArg message.data 0
  have hacc1 : hasAccount (readState state message) message.currentTarget :=
    hasAccount_readSlot (hasAccount_readSlot (hasAccount_readSlot (hasAccount_readSlot hacc)))
  have hM1 : (MEMB message).size = 96 := size_mapMem size_MEM0 _ _
  have hp1 : loadWord (memoryReadBytes (MEMB message) 64 32) 0 32 = 0x60 :=
    ptr_mapMem size_MEM0 mload_MEM0 _ _
  have h1 : slotCost c1 ≤ 2100 := by cases c1 <;> decide
  refine Triple.seq (HoareG.toIA (toGetter hfork hsize hsize' hsel hv hown hl hc0 hcL (by omega))
    (by cheap) (by same_store)) ?_
  stepC (depCheck hfork (Or.inr (Or.inl ⟨rfl, rfl⟩)) (by simp)
    (by simp only [preState, storageAt_readSlot]; exact hdep) hc10 (by gas_ok))
  stepC (BalanceOf.toLookup (by simp) (by gas_ok))
  stepC (BalanceOf.lookup hfork (by simp) hM1 (cB := cB) (by rw [hkey]; exact hcB) (by gas_ok))
  rw [hkey, storageAt_readSlot, storageAt_readSlot, storageAt_readSlot]
  stepC (BalanceOf.back (Or.inr rfl) (by gas_ok))
  refine Triple.seq (HoareG.toIW (zeroBal hfork (by simp) hstatic hacc1
    (by rw [hk]; exact coldIn_accessSlot_self _ _ _)
    (BalanceOf.size_lookMem hM1 _) (by gas_ok)
    (by simp only [hk, originalAt_readSlot, storageAt_readSlot]; gas_ok))
    (by omega) hacc1 (by simp only [hk, originalAt_readSlot, storageAt_readSlot]; gas_ok)
    (by simp only [hk, originalAt_readSlot, storageAt_readSlot]; exact hnrB)) ?_
  simp only [hk, originalAt_readSlot, storageAt_readSlot]
  simp only [readState, preState, balSlot] at hg hstip2 hnrT hacc1 ⊢
  refine Triple.seq (HoareG.toIW (subTotal hfork (by simp) hstatic (hasAccount_writeSlot hacc1)
    (c1 := c1) ?hc (by gas_ok)
    (by rw [originalAt_writeSlot hacc1]; simp only [originalAt_readSlot]; gas_ok))
    (by omega) (hasAccount_writeSlot hacc1)
    (by rw [originalAt_writeSlot hacc1]; simp only [originalAt_readSlot]; gas_ok)
    (by rw [originalAt_writeSlot hacc1]; simp only [originalAt_readSlot]; exact hnrT)) ?_
  case hc => rw [TransferFee.coldIn_storeSub', accessSlot_accessSlot]; exact hc1
  rw [originalAt_writeSlot hacc1]
  simp only [originalAt_readSlot]
  refine (SpecG.toIA (logBlock hstatic (size_mapMem (BalanceOf.size_lookMem hM1 _) _ _)
    (ptr_mapMem (BalanceOf.size_lookMem hM1 _) (ptr_mapMem hM1 hp1 _ _) _ _)
    (by gas_ok)) (by omega) (fun _ _ => rfl)).consequence (fun _ h => h) ?_
  rintro evm ⟨hr0, hr, he, ho, hgas, hs, hss⟩
  refine ⟨hr0, hr, he, ho, by rw [hgas]; gas_ok, hs, ?_⟩
  rw [hss, hk]

end UsdtVerify.DestroySpec
