import UsdtVerify.Usdt.Refill.Transfer

/-!
# transfer with a fee above 0: the success path over `StepI`

`feeHead`, `ownerPart`, `bodyFee` and `spec_fee` of the transfer proofs over `StepI`. The path
writes three words: the sender's balance (`sub`), the recipient's balance (`add`, no overflow) and
the owner's balance (`add`, no overflow). The two additions never refill (`refill_add`), so the
only hypothesis on refills is the one of the sender's write (`hnrD`), as with a fee of 0.
-/

namespace UsdtVerify.TransferFee

open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts
open Transfer SafeMath TransferOk Refill TransferFrom

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate}

/-- `feeHead` over `StepI`, when the write of the sender's balance refills nothing. -/
theorem feeHeadI (hfork : .berlin ≤ fork)
    (hlong : 68 ≤ message.data.size) (hsz : message.data.size < 2 ^ 256)
    (hstatic : message.isStatic = false) (hacc : hasAccount state message.currentTarget)
    {v a sel : U256} {M : ByteArray} (hM : M.size = 96)
    (hov : v.toNat * (storageAt state message.currentTarget 3).toNat < 2 ^ 256)
    (hfee : feeOf state message v ≠ 0)
    (hfv : (feeOf state message v).toNat ≤ v.toNat)
    (hbal : v.toNat ≤ (balS state message).toNat)
    (hto : (balT state message v a).toNat + (sendOf state message v).toNat < 2 ^ 256)
    {c3 c4 cS cT : Bool} (hc3 : coldIn substate message.currentTarget 3 = c3)
    (hc4 : coldIn (accessSlot substate message.currentTarget 3) message.currentTarget 4 = c4)
    (hcS : coldIn (accessSlot (accessSlot substate message.currentTarget 3) message.currentTarget 4)
      message.currentTarget (senderSlot message) = cS)
    (hcT : coldIn (access3 substate message) message.currentTarget (recipientSlot a) = cT)
    (hnrD : sstoreStateRefill fork (originalAt state message.currentTarget (senderSlot message))
      (balS state message) (sub (balS state message) v) = 0)
    {gas : Nat}
    (hg : 964 + readCost c3 c4 cS cT + mulCost v +
      capCost (rawFee state message v) (storageAt state message.currentTarget 4) +
      debitCost fork state message v + creditCostFee fork state message v a + 2401 ≤ gas) :
    HoareI fork (At CODE message 9883 [v, a, 0x1699, v, a, 0x078a, sel] M gas state substate)
      (At CODE message 10298 [0x40, sendOf state message v, feeOf state message v, v, a, 0x1699,
          v, a, 0x078a, sel] (memA M message a)
        (gas - (964 + readCost c3 c4 cS cT + mulCost v +
          capCost (rawFee state message v) (storageAt state message.currentTarget 4) +
          debitCost fork state message v + creditCostFee fork state message v a))
        (creditedFee state message v a) (creditedSubFee fork substate state message v a)) := by
  have hacc3 : hasAccount (reads3 state message) message.currentTarget :=
    hasAccount_readSlot (hasAccount_readSlot (hasAccount_readSlot hacc))
  have hacc4 : hasAccount (readSlot (debited state message v) message.currentTarget
      (recipientSlot a)) message.currentTarget :=
    hasAccount_readSlot (hasAccount_writeSlot hacc3)
  simp only [readCost, debitCost, creditCostFee, rawFee, feeOf, balS, balT, debited, reads3,
    sendOf] at hg hfee hfv hbal hto hnrD
  simp only [readCost, debitCost, creditCostFee, rawFee, feeOf, balS, balT, debited, reads3,
    sendOf, creditedFee, creditedSubFee, debitedSub, access3, memA] at hacc4 ⊢
  simp only [reads3] at hacc3
  stepC (payloadOk hlong hsz (by simp) (by gas_ok))
  stepC (feeCall hfork (by simp) hc3 (by gas_ok))
  stepC (mulBlock (by simp) (by valid_dest) hov (by gas_ok))
  stepC (repc (pc' := 9937) (by decide))
  stepC (divCall (by simp) (by gas_ok))
  stepC (divBlock (by simp) (by valid_dest) (by decide) (by gas_ok))
  stepC (repc (pc' := 9951) (by decide))
  stepC (capBlock hfork (by simp) hc4 (by simp only [storageAt_readSlot]; gas_ok))
  simp only [storageAt_readSlot]
  stepC (sendCall (by simp) (by gas_ok))
  stepC (subBlock (by simp) (by valid_dest) hfv (by gas_ok))
  stepC (repc (pc' := 9988) (by decide))
  stepC (debitCall hfork (by simp) hcS (by gas_ok) hM)
  simp only [storageAt_readSlot]
  stepC (subBlock (by simp) (by valid_dest) hbal (by gas_ok))
  stepC (repc (pc' := 10072) (by decide))
  refine Triple.seq (Refill.HoareG.toIW (debitStore hfork (by simp) hstatic hacc3
    (coldIn_accessSlot_self _ _ _) (by gas_ok)
    (by simp only [storageAt_readSlot, originalAt_readSlot]; gas_ok) (size_mapMem hM _ _))
    (by omega) hacc3 (by simp only [storageAt_readSlot, originalAt_readSlot]; gas_ok)
    (by simp only [storageAt_readSlot, originalAt_readSlot]; exact hnrD)) ?_
  simp only [storageAt_readSlot, originalAt_readSlot]
  stepC (creditCall hfork (by simp) (cT := cT) (by rw [coldIn_storeSub]; exact hcT) (by gas_ok)
    (size_mapMem (size_mapMem hM _ _) _ _))
  stepC (addBlock (by simp) (by valid_dest) hto (by gas_ok))
  stepC (repc (pc' := 10221) (by decide))
  refine Triple.seq (Refill.HoareG.toIW (creditStoreFee hfork hfee (by simp) hstatic hacc4
    (coldIn_accessSlot_self _ _ _) (by gas_ok)
    (by simp only [storageAt_readSlot, originalAt_readSlot, originalAt_writeSlot hacc3]; gas_ok)
    (size_mapMem (size_mapMem (size_mapMem hM _ _) _ _) _ _))
    (by omega) hacc4
    (by simp only [storageAt_readSlot, originalAt_readSlot, originalAt_writeSlot hacc3]; gas_ok)
    (by simp only [storageAt_readSlot]; exact Refill.refill_add hto)) ?_
  simp only [storageAt_readSlot, originalAt_readSlot, originalAt_writeSlot hacc3]
  exact HoareG.toIA (restate rfl rfl rfl (by gas_ok) rfl rfl) (by cheap) (by same_store)

/-- `ownerPart` over `StepI`: the owner's write adds the fee without overflow, so it refills
nothing. -/
theorem ownerPartI (hfork : .berlin ≤ fork)
    (hstatic : message.isStatic = false) {st : State.TransactionState} {ss : Substate}
    (hacc : hasAccount st message.currentTarget) {send fee v a sel o : U256} {M : ByteArray}
    (hM : M.size = 96) (hptr : loadWord (memoryReadBytes M 64 32) 0 32 = 0x60)
    (hc0 : coldIn ss message.currentTarget 0 = false) {cO : Bool}
    (hcO : coldIn ss message.currentTarget (ownerSlotOf st message.currentTarget) = cO)
    (ho : originalAt st message.currentTarget (ownerSlotOf st message.currentTarget) = o)
    (hown : (balOf st message.currentTarget).toNat + fee.toNat < 2 ^ 256) {gas : Nat}
    (hg : 4409 + slotCost cO + Gas.writeCost fork o (balOf st message.currentTarget)
      (add (balOf st message.currentTarget) fee) false ≤ gas) :
    HoareI fork (At CODE message 10298 [0x40, send, fee, v, a, 0x1699, v, a, 0x078a, sel] M gas
        st ss)
      (fun evm => evm.running = false ∧ Halted false .empty (gas - (4409 + slotCost cO +
          Gas.writeCost fork o (balOf st message.currentTarget)
          (add (balOf st message.currentTarget) fee) false))
        (readSlot (ownedB st message.currentTarget fee) message.currentTarget 0)
        (feeSubB fork ss st message o fee send a) evm) := by
  simp only [ownerSlotOf, balOf, ownedB, feeSubB] at hcO ho hown hg ⊢
  stepC (ownerCall (cO := cO) hfork rfl (by simp) hc0
    (by rw [coldIn_accessSlot_of_warm hc0]; exact hcO) (by gas_ok) hM)
  stepC (addBlock (by simp) (by valid_dest) hown (by gas_ok))
  stepC (repc (pc' := 10412) (by decide))
  refine Triple.seq (Refill.HoareG.toIW' (ownerStore hfork
    (by rw [storageAt_readSlot, storageAt_readSlot]) (by simp) hstatic
    (hasAccount_readSlot (hasAccount_readSlot hacc))
    (coldIn_accessSlot_false (coldIn_accessSlot_false hc0)) (coldIn_accessSlot_self _ _ _)
    (by rw [originalAt_readSlot, originalAt_readSlot, storageAt_readSlot, storageAt_readSlot, ho]
        gas_ok)
    (size_mapMem hM _ _)) (Refill.getStorage_readSlot _ _ _) (by omega)
    (hasAccount_readSlot (hasAccount_readSlot (hasAccount_readSlot hacc)))
    (by rw [originalAt_readSlot, originalAt_readSlot, storageAt_readSlot, storageAt_readSlot, ho]
        gas_ok)
    (by rw [storageAt_readSlot, storageAt_readSlot]; exact Refill.refill_add hown)) ?_
  rw [originalAt_readSlot, originalAt_readSlot, storageAt_readSlot, storageAt_readSlot, ho]
  stepC (ownerLog hfork rfl (by simp) hstatic
    (coldIn_storeSub_false (coldIn_accessSlot_self _ _ _)) (by gas_ok)
    (size_mapMem (size_mapMem hM _ _) _ _)
    (ptr_mapMem (size_mapMem hM _ _) (ptr_mapMem hM hptr _ _) _ _))
  stepC (logBlock128 (by simp) hstatic (by gas_ok)
    (by rw [ByteArray.size_append, size_wordBytes]
        exact congrArg (· + 32) (size_mapMem (size_mapMem hM _ _) _ _))
    (by rw [read64_append (size_mapMem (size_mapMem hM _ _) _ _)]
        exact ptr_mapMem (size_mapMem hM _ _) (ptr_mapMem hM hptr _ _) _ _))
  refine (Refill.SpecG.toIA (TransferOk.endBlock (by gas_ok)) (by cheap) (by same_store)).consequence
    (fun _ h => h) ?_
  rintro evm ⟨hr0, hr, he, ho, hgas, hs, hss⟩
  exact ⟨hr0, hr, he, ho, by rw [hgas]; gas_ok, hs, hss⟩

/-- `bodyFee` over `StepI`, when the write of the sender's balance refills nothing. -/
theorem bodyFeeI (hfork : .berlin ≤ fork)
    (hlong : 68 ≤ message.data.size) (hsz : message.data.size < 2 ^ 256)
    (hstatic : message.isStatic = false) (hacc : hasAccount state message.currentTarget)
    {v a sel : U256} {M : ByteArray} (hM : M.size = 96)
    (hptr : loadWord (memoryReadBytes M 64 32) 0 32 = 0x60)
    (hov : v.toNat * (storageAt state message.currentTarget 3).toNat < 2 ^ 256)
    (hfee : feeOf state message v ≠ 0)
    (hfv : (feeOf state message v).toNat ≤ v.toNat)
    (hbal : v.toNat ≤ (balS state message).toNat)
    (hto : (balT state message v a).toNat + (sendOf state message v).toNat < 2 ^ 256)
    (hown : (balO state message v a).toNat + (feeOf state message v).toNat < 2 ^ 256)
    (hc0 : coldIn substate message.currentTarget 0 = false)
    {c3 c4 cS cT cO : Bool} (hc3 : coldIn substate message.currentTarget 3 = c3)
    (hc4 : coldIn (accessSlot substate message.currentTarget 3) message.currentTarget 4 = c4)
    (hcS : coldIn (accessSlot (accessSlot substate message.currentTarget 3) message.currentTarget 4)
      message.currentTarget (senderSlot message) = cS)
    (hcT : coldIn (access3 substate message) message.currentTarget (recipientSlot a) = cT)
    (hcO : coldIn (creditedSubFee fork substate state message v a) message.currentTarget
      (ownerSlot (ownerWord state message v a)) = cO)
    (hnrD : sstoreStateRefill fork (originalAt state message.currentTarget (senderSlot message))
      (balS state message) (sub (balS state message) v) = 0)
    {gas : Nat}
    (hg : 5373 + readCost c3 c4 cS cT + slotCost cO + mulCost v +
      capCost (rawFee state message v) (storageAt state message.currentTarget 4) +
      debitCost fork state message v + creditCostFee fork state message v a +
      ownerCost fork state message v a ≤ gas) :
    HoareI fork (At CODE message 9883 [v, a, 0x1699, v, a, 0x078a, sel] M gas state substate)
      (fun evm => evm.running = false ∧ Halted false .empty (gas - (5373 + readCost c3 c4 cS cT +
        slotCost cO + mulCost v +
        capCost (rawFee state message v) (storageAt state message.currentTarget 4) +
        debitCost fork state message v + creditCostFee fork state message v a +
        ownerCost fork state message v a))
        (feeState state message v a) (feeSub fork substate state message v a) evm) := by
  have hacc4 : hasAccount (readSlot (debited state message v) message.currentTarget
      (recipientSlot a)) message.currentTarget :=
    hasAccount_readSlot (hasAccount_writeSlot
      (hasAccount_readSlot (hasAccount_readSlot (hasAccount_readSlot hacc))))
  have horig : ∀ m, originalAt (creditedFee state message v a) message.currentTarget m =
      originalAt state message.currentTarget m := by
    intro m
    rw [originalAt_writeSlot hacc4, originalAt_readSlot,
      originalAt_writeSlot (hasAccount_readSlot (hasAccount_readSlot (hasAccount_readSlot hacc)))]
    simp only [originalAt_readSlot]
  have hw : coldIn (creditedSubFee fork substate state message v a) message.currentTarget 0 =
      false :=
    coldIn_storeSub_false (coldIn_accessSlot_false (coldIn_storeSub_false
      (coldIn_accessSlot_false (coldIn_accessSlot_false (coldIn_accessSlot_false hc0)))))
  have hA := feeHeadI (sel := sel) hfork hlong hsz hstatic hacc hM hov hfee hfv hbal hto hc3
    hc4 hcS hcT hnrD (gas := gas) (by simp only [ownerCost] at hg; omega)
  have hB := ownerPartI (message := message) (st := creditedFee state message v a)
    (ss := creditedSubFee fork substate state message v a) (send := sendOf state message v)
    (v := v) (a := a) (sel := sel) (M := memA M message a) hfork hstatic (hasAccount_writeSlot hacc4)
    (size_mapMem (size_mapMem (size_mapMem (size_mapMem hM _ _) _ _) _ _) _ _)
    (ptr_mapMem (size_mapMem (size_mapMem (size_mapMem hM _ _) _ _) _ _)
      (ptr_mapMem (size_mapMem (size_mapMem hM _ _) _ _)
        (ptr_mapMem (size_mapMem hM _ _) (ptr_mapMem hM hptr _ _) _ _) _ _) _ _)
    hw hcO (horig _) hown
    (gas := gas - (964 + readCost c3 c4 cS cT + mulCost v +
          capCost (rawFee state message v) (storageAt state message.currentTarget 4) +
          debitCost fork state message v + creditCostFee fork state message v a))
    (by simp only [ownerCost, ownerSlotOf, balOf, balO, ownerWord] at hg ⊢; omega)
  refine Triple.seq hA (hB.consequence (fun _ h => h) ?_)
  rintro evm ⟨hr0, hr, he, ho, hgas, hs, hss⟩
  refine ⟨hr0, hr, he, ho, ?_, hs, hss⟩
  rw [hgas]
  simp only [ownerCost, ownerSlotOf, balOf, balO, ownerWord]
  omega

/-- `spec_fee` over `StepI`, when the write of the sender's balance refills nothing (`hnrD`). -/
theorem spec_feeI (hfork : .berlin ≤ fork)
    (hstatic : message.isStatic = false) (hacc : hasAccount state message.currentTarget)
    (hlong : 68 ≤ message.data.size) (hsz : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0xa9059cbb) (hv : message.value = 0)
    (hnp : byte20 (storageAt state message.currentTarget 0) = 0)
    (hnb : (storageAt state message.currentTarget (blackSlot message)).toNat % 256 = 0)
    (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    (hov : (wordArg message.data 1).toNat *
      (storageAt (shortState state message) message.currentTarget 3).toNat < 2 ^ 256)
    (hfee : feeOf (shortState state message) message (wordArg message.data 1) ≠ 0)
    (hfv : (feeOf (shortState state message) message (wordArg message.data 1)).toNat ≤
      (wordArg message.data 1).toNat)
    (hbal : (wordArg message.data 1).toNat ≤ (balS (shortState state message) message).toNat)
    (hto : (balT (shortState state message) message (wordArg message.data 1)
      (addrArg message.data 0)).toNat +
      (sendOf (shortState state message) message (wordArg message.data 1)).toNat < 2 ^ 256)
    (hown : (balO (shortState state message) message (wordArg message.data 1)
      (addrArg message.data 0)).toNat +
      (feeOf (shortState state message) message (wordArg message.data 1)).toNat < 2 ^ 256)
    {c0 cB c10 c3 c4 cS cT cO : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hcB : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget
      (blackSlot message) = cB)
    (hc10 : coldIn (accessSlot (accessSlot substate message.currentTarget 0) message.currentTarget
      (blackSlot message)) message.currentTarget 10 = c10)
    (hc3 : coldIn (shortSubstate substate message) message.currentTarget 3 = c3)
    (hc4 : coldIn (accessSlot (shortSubstate substate message) message.currentTarget 3)
      message.currentTarget 4 = c4)
    (hcS : coldIn (accessSlot (accessSlot (shortSubstate substate message) message.currentTarget 3)
      message.currentTarget 4) message.currentTarget (senderSlot message) = cS)
    (hcT : coldIn (access3 (shortSubstate substate message) message) message.currentTarget
      (recipientSlot (addrArg message.data 0)) = cT)
    (hcO : coldIn (creditedSubFee fork (shortSubstate substate message) (shortState state message)
      message (wordArg message.data 1) (addrArg message.data 0)) message.currentTarget
      (ownerSlot (ownerWord (shortState state message) message (wordArg message.data 1)
        (addrArg message.data 0))) = cO)
    (hnrD : sstoreStateRefill fork (originalAt state message.currentTarget (senderSlot message))
      (balS (shortState state message) message)
      (sub (balS (shortState state message) message) (wordArg message.data 1)) = 0)
    {gas : Nat} (hg : feeCost fork state message c0 cB c10 c3 c4 cS cT cO ≤ gas) :
    HoareI fork (At CODE message 0 [] .empty gas state substate)
      (fun evm => evm.running = false ∧
        Halted false .empty (gas - feeCost fork state message c0 cB c10 c3 c4 cS cT cO)
        (feeState (shortState state message) message (wordArg message.data 1)
          (addrArg message.data 0))
        (feeSub fork (shortSubstate substate message) (shortState state message) message
          (wordArg message.data 1) (addrArg message.data 0)) evm) := by
  have hB := bodyFeeI (state := shortState state message)
    (substate := shortSubstate substate message)
    (sel := BitVec.ofNat 256 (selector message.data))
    (gas := gas - (PRE_COST + slotCost c0 + slotCost cB + slotCost c10))
    hfork hlong hsz hstatic
    (hasAccount_readSlot (hasAccount_readSlot (hasAccount_readSlot hacc)))
    (size_MEMK (callerKey message) 6) (ptr_MEMK _ _) hov hfee hfv hbal hto hown
    (coldIn_accessSlot_false (coldIn_accessSlot_false (coldIn_accessSlot_self _ _ _)))
    hc3 hc4 hcS hcT hcO (by simp only [originalAt_readSlot]; exact hnrD)
    (Nat.le_sub_of_add_le (by rw [Nat.add_comm]; exact hg))
  have hpre : PRE_COST + slotCost c0 + slotCost cB + slotCost c10 ≤ gas :=
    Nat.le_trans (Nat.le_add_right _ _) hg
  refine Triple.seq (HoareG.toIA (pre hfork (by omega) hsz hsel hv hnp hnb hdep hc0 hcB hc10 hpre)
    (by simp only [PRE_COST]; cheap) (by same_store)) ?_
  refine hB.consequence (fun _ h => h) ?_
  rintro evm ⟨hr0, hr, he, ho, hgas, hs, hss⟩
  exact ⟨hr0, hr, he, ho, by rw [hgas, Nat.sub_sub], hs, hss⟩

end UsdtVerify.TransferFee
