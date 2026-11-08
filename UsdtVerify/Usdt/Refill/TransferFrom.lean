import UsdtVerify.Usdt.Spec.TransferFrom
import UsdtVerify.Usdt.Refill.Fee

/-!
# transferFrom: the success paths over `StepI`

`body`, `spec_ok`, `headF`, `ownerPartF`, `bodyFeeF` and `spec_feeF` of the transferFrom proofs
over `StepI`. The path writes the allowance (`A - v`, unless `A = MAX_UINT`), `balances[_from]`
(`sub`), `balances[_to]` (`add`, no overflow) and, with a fee above 0, `balances[owner]` (`add`,
no overflow). The two additions never refill (`refill_add`). The two subtractions take a
hypothesis each: `hnrA` for the allowance (only when `A ≠ MAX_UINT`) and `hnrD` for
`balances[_from]`.

- `allowStepI`: `allowStep` over `StepI`.
- `bodyFI`, `spec_okFI`: the path with a fee of 0.
- `headFI`, `ownerPartFI`, `bodyFeeFI`, `spec_feeFI`: the path with a fee above 0.
-/

namespace UsdtVerify.TransferFrom

open EthLib.Base (Fork U256 Address)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts
open Transfer SafeMath TransferOk TransferFee Refill

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate}

/-- `allowStep` over `StepI`: when `A ≠ MAX_UINT`, the write of `A - v` refills nothing
(`hnrA`). -/
theorem allowStepI (hfork : .berlin ≤ fork)
    {fee A v t f : U256} {rest : List U256} (hrest : rest.length ≤ 8)
    (hA : storageAt state message.currentTarget (allowFrom message f) = A)
    (hok : A = MAX_UINT ∨ v.toNat ≤ A.toNat)
    (hgood : A ≠ MAX_UINT → message.isStatic = false ∧ hasAccount state message.currentTarget)
    (hw : coldIn substate message.currentTarget (allowFrom message f) = false)
    (hnrA : A ≠ MAX_UINT → sstoreStateRefill fork
      (originalAt state message.currentTarget (allowFrom message f)) A (sub A v) = 0) {gas : Nat}
    (hg : allowCost fork (originalAt state message.currentTarget (allowFrom message f)) A v +
      2300 ≤ gas) {M : ByteArray} (hM : M.size = 96) :
    HoareI fork (At CODE message 8834 (0x60 :: 0 :: fee :: A :: v :: t :: f :: rest) M gas state
        substate)
      (At CODE message 9022 (0x60 :: 0 :: fee :: A :: v :: t :: f :: rest)
        (allowMem2 message M A f)
        (gas - allowCost fork (originalAt state message.currentTarget (allowFrom message f)) A v)
        (allowState state message.currentTarget (allowFrom message f) A v)
        (allowSub fork substate message.currentTarget (allowFrom message f)
          (originalAt state message.currentTarget (allowFrom message f)) A v)) := by
  have h := allowStep (fee := fee) (t := t) hfork hrest hA hok hgood hw hg hM
  by_cases hmax : A = MAX_UINT
  · simp only [allowCost, allowState, allowSub, allowMem2, hmax, ite_true] at h hg ⊢
    exact HoareG.toIA h (by omega) (fun _ _ => rfl)
  · simp only [allowCost, allowState, allowSub, allowMem2, hmax, ite_false] at h hg ⊢
    subst hA
    exact HoareG.toIW h (by omega) (hgood hmax).2 (by omega) (hnrA hmax)

/-- `body` over `StepI`, when the writes of the allowance (`hnrA`) and of `balances[_from]`
(`hnrD`) refill nothing. -/
theorem bodyFI (hfork : .berlin ≤ fork)
    (hstatic : message.isStatic = false) (hacc : hasAccount state message.currentTarget)
    {v t f sel : U256} {M : ByteArray} (hM : M.size = 96)
    (hptr : loadWord (memoryReadBytes M 64 32) 0 32 = 0x60)
    (hov : v.toNat * (storageAt state message.currentTarget 3).toNat < 2 ^ 256)
    (hfee : feeOf state message v = 0)
    (hallow : allowOf state message f = MAX_UINT ∨ v.toNat ≤ (allowOf state message f).toNat)
    (hbal : v.toNat ≤ (balFrom state message v f).toNat)
    (hto : (balTo state message v t f).toNat + v.toNat < 2 ^ 256)
    {cA c3 c4 cF cT : Bool}
    (hcA : coldIn substate message.currentTarget (allowFrom message f) = cA)
    (hc3 : coldIn (accessSlot substate message.currentTarget (allowFrom message f))
      message.currentTarget 3 = c3)
    (hc4 : coldIn (accessSlot (accessSlot substate message.currentTarget (allowFrom message f))
      message.currentTarget 3) message.currentTarget 4 = c4)
    (hcF : coldIn (allowedSubF fork substate state message v f) message.currentTarget
      (recipientSlot f) = cF)
    (hcT : coldIn (accessSlot (allowedSubF fork substate state message v f) message.currentTarget
      (recipientSlot f)) message.currentTarget (recipientSlot t) = cT)
    (hnrA : allowOf state message f ≠ MAX_UINT → sstoreStateRefill fork
      (originalAt state message.currentTarget (allowFrom message f)) (allowOf state message f)
      (sub (allowOf state message f) v) = 0)
    (hnrD : sstoreStateRefill fork (originalAt state message.currentTarget (recipientSlot f))
      (balFrom state message v f) (sub (balFrom state message v f) v) = 0)
    {gas : Nat}
    (hstip : 972 + slotCost cA + slotCost c3 + slotCost c4 + slotCost cF + slotCost cT +
      mulCost v + capCost (rawFee state message v) (storageAt state message.currentTarget 4) +
      allowCostF fork state message v f + debitCostF fork state message v f + 2401 ≤ gas)
    (hg : 2971 + slotCost cA + slotCost c3 + slotCost c4 + slotCost cF + slotCost cT +
      mulCost v + capCost (rawFee state message v) (storageAt state message.currentTarget 4) +
      allowCostF fork state message v f + debitCostF fork state message v f +
      creditCostF fork state message v t f ≤ gas) :
    HoareI fork (At CODE message 8648 [0x60, 0, 0, 0, v, t, f, 0x1097, v, t, f, 0x0392, sel] M gas
        state substate)
      (fun evm => evm.running = false ∧ Halted false .empty (gas - (2971 + slotCost cA +
        slotCost c3 + slotCost c4 + slotCost cF + slotCost cT + mulCost v +
        capCost (rawFee state message v) (storageAt state message.currentTarget 4) +
        allowCostF fork state message v f + debitCostF fork state message v f +
        creditCostF fork state message v t f))
        (creditedF state message v t f) (loggedSubF fork substate state message v t f) evm) := by
  have hacc3 : hasAccount (readsF state message f) message.currentTarget :=
    hasAccount_readSlot (hasAccount_readSlot (hasAccount_readSlot hacc))
  have hacc4 : hasAccount (readSlot (allowedF state message v f) message.currentTarget
      (recipientSlot f)) message.currentTarget :=
    hasAccount_readSlot (hasAccount_allowState hacc3)
  have hacc5 : hasAccount (readSlot (debitedF state message v f) message.currentTarget
      (recipientSlot t)) message.currentTarget :=
    hasAccount_readSlot (hasAccount_writeSlot hacc4)
  have horig : ∀ m, originalAt (allowedF state message v f) message.currentTarget m =
      originalAt state message.currentTarget m := by
    intro m
    rw [originalAt_allowState hacc3]
    simp only [originalAt_readSlot]
  have horig2 : ∀ m, originalAt (debitedF state message v f) message.currentTarget m =
      originalAt state message.currentTarget m := by
    intro m
    rw [originalAt_writeSlot hacc4, originalAt_readSlot, horig]
  have hT := slotCost_ge cT
  have hT' : slotCost cT ≤ 2100 := by cases cT <;> decide
  simp only [allowCostF, debitCostF, creditCostF, rawFee, feeOf, allowOf, balFrom, balTo,
    creditedF, debitedF, allowedF, readsF, loggedSubF, allowedSubF,
    accessF] at hstip hg hfee hbal hto hallow hcF hcT hacc4 hacc5 horig horig2 hnrA hnrD ⊢
  simp only [readsF] at hacc3
  stepC (allowRead hfork (by simp) hcA (by gas_ok) hM)
  stepC (feeCall hfork (by simp) hc3 (by gas_ok))
  stepC (mulBlock (by simp) (by valid_dest) (by simpa only [storageAt_readSlot] using hov)
    (by gas_ok))
  stepC (repc (pc' := 8802) (by decide))
  stepC (divCall (by simp) (by gas_ok))
  stepC (divBlock (by simp) (by valid_dest) (by decide) (by gas_ok))
  stepC (repc (pc' := 8816) (by decide))
  stepC (capBlock hfork (by simp) hc4 (by simp only [storageAt_readSlot]; gas_ok))
  simp only [storageAt_readSlot]
  stepC (Gas.reshapeG (s' := (0x60 : U256) :: 0 :: 0 ::
      storageAt state message.currentTarget (allowFrom message f) :: v :: t :: f ::
      [0x1097, v, t, f, 0x0392, sel]) (by rw [hfee]) rfl rfl)
  refine Triple.seq (allowStepI hfork (by simp) (by simp only [storageAt_readSlot]) hallow
    (fun _ => ⟨hstatic, hacc3⟩)
    (coldIn_accessSlot_false (coldIn_accessSlot_false (coldIn_accessSlot_self _ _ _)))
    (by simp only [originalAt_readSlot]; exact hnrA)
    (by simp only [originalAt_readSlot]; gas_ok)
    (size_allowMem hM f)) ?_
  simp only [originalAt_readSlot]
  have hMa : (allowMem message M f).size = 96 := size_allowMem hM f
  have hMb := size_allowMem2 (message := message) hMa (storageAt state message.currentTarget
    (allowFrom message f)) f
  have hPb := ptr_allowMem2 (message := message) hMa (ptr_allowMem hM hptr f)
    (storageAt state message.currentTarget (allowFrom message f)) f
  stepC (sendCall (by simp) (by gas_ok))
  stepC (subBlock (by simp) (by valid_dest) (by simp) (by gas_ok))
  stepC (repc (pc' := 9041) (by decide))
  stepC (Gas.reshapeG (s' := v :: (0x60 : U256) :: 0 :: 0 ::
      storageAt state message.currentTarget (allowFrom message f) :: v :: t :: f ::
      [0x1097, v, t, f, 0x0392, sel]) (by simp [sub]) rfl rfl)
  stepC (debitCall hfork (by simp) hcF (by gas_ok) hMb)
  stepC (subBlock (by simp) (by valid_dest) hbal (by gas_ok))
  stepC (repc (pc' := 9125) (by decide))
  refine Triple.seq (Refill.HoareG.toIW (debitStore hfork (by simp) hstatic hacc4
    (coldIn_accessSlot_self _ _ _)
    (by simp only [storageAt_readSlot, originalAt_readSlot, horig]; gas_ok) (size_mapMem hMb _ _))
    (by omega) hacc4 (by simp only [storageAt_readSlot, originalAt_readSlot, horig]; gas_ok)
    (by simp only [storageAt_readSlot, originalAt_readSlot, horig]; exact hnrD)) ?_
  simp only [storageAt_readSlot, originalAt_readSlot, horig]
  stepC (creditCall hfork (by simp) (cT := cT) (by rw [coldIn_storeSub]; exact hcT) (by gas_ok)
    (size_mapMem (size_mapMem hMb _ _) _ _))
  stepC (addBlock (by simp) (by valid_dest) hto (by gas_ok))
  stepC (repc (pc' := 9274) (by decide))
  refine Triple.seq (Refill.HoareG.toIW (creditStore hfork (by simp) hstatic hacc5
    (coldIn_accessSlot_self _ _ _) (by gas_ok)
    (by simp only [storageAt_readSlot, originalAt_readSlot, horig2]; gas_ok)
    (size_mapMem (size_mapMem (size_mapMem hMb _ _) _ _) _ _))
    (by omega) hacc5
    (by simp only [storageAt_readSlot, originalAt_readSlot, horig2]; gas_ok)
    (by simp only [storageAt_readSlot]; exact Refill.refill_add hto)) ?_
  simp only [storageAt_readSlot, originalAt_readSlot, horig2]
  stepC (logBlock (by simp) hstatic (by gas_ok)
    (size_mapMem (size_mapMem (size_mapMem (size_mapMem hMb _ _) _ _) _ _) _ _)
    (ptr_mapMem (size_mapMem (size_mapMem (size_mapMem hMb _ _) _ _) _ _)
      (ptr_mapMem (size_mapMem (size_mapMem hMb _ _) _ _)
        (ptr_mapMem (size_mapMem hMb _ _) (ptr_mapMem hMb hPb _ _) _ _) _ _) _ _))
  refine (Refill.SpecG.toIA (endBlock (by gas_ok)) (by cheap) (by same_store)).consequence
    (fun _ h => h) ?_
  rintro evm ⟨hr0, hr, he, ho, hgas, hs, hss⟩
  exact ⟨hr0, hr, he, ho, by rw [hgas]; gas_ok, hs, hss⟩

/-- `spec_ok` over `StepI`, when the writes of the allowance (`hnrA`) and of `balances[_from]`
(`hnrD`) refill nothing. -/
theorem spec_okFI (hfork : .berlin ≤ fork)
    (hstatic : message.isStatic = false) (hacc : hasAccount state message.currentTarget)
    (hlong : 100 ≤ message.data.size) (hsz : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x23b872dd) (hv : message.value = 0)
    (hnp : byte20 (storageAt state message.currentTarget 0) = 0)
    (hnb : (storageAt state message.currentTarget (blackFrom (fromArg message))).toNat % 256 = 0)
    (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    (hov : (valArg message).toNat *
      (storageAt (checkState state message) message.currentTarget 3).toNat < 2 ^ 256)
    (hfee : feeOf (checkState state message) message (valArg message) = 0)
    (hallow : allowOf (checkState state message) message (fromArg message) = MAX_UINT ∨
      (valArg message).toNat ≤ (allowOf (checkState state message) message (fromArg message)).toNat)
    (hbal : (valArg message).toNat ≤
      (balFrom (checkState state message) message (valArg message) (fromArg message)).toNat)
    (hto : (balTo (checkState state message) message (valArg message) (toArg message)
      (fromArg message)).toNat + (valArg message).toNat < 2 ^ 256)
    {c0 cB c10 cA c3 c4 cF cT : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hcB : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget
      (blackFrom (fromArg message)) = cB)
    (hc10 : coldIn (accessSlot (accessSlot substate message.currentTarget 0) message.currentTarget
      (blackFrom (fromArg message))) message.currentTarget 10 = c10)
    (hcA : coldIn (checkSub substate message) message.currentTarget
      (allowFrom message (fromArg message)) = cA)
    (hc3 : coldIn (accessSlot (checkSub substate message) message.currentTarget
      (allowFrom message (fromArg message))) message.currentTarget 3 = c3)
    (hc4 : coldIn (accessSlot (accessSlot (checkSub substate message) message.currentTarget
      (allowFrom message (fromArg message))) message.currentTarget 3) message.currentTarget 4 = c4)
    (hcF : coldIn (allowedSubF fork (checkSub substate message) (checkState state message) message
      (valArg message) (fromArg message)) message.currentTarget (recipientSlot (fromArg message)) =
        cF)
    (hcT : coldIn (accessSlot (allowedSubF fork (checkSub substate message)
      (checkState state message) message (valArg message) (fromArg message)) message.currentTarget
      (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (toArg message)) = cT)
    (hnrA : allowOf (checkState state message) message (fromArg message) ≠ MAX_UINT →
      sstoreStateRefill fork
        (originalAt state message.currentTarget (allowFrom message (fromArg message)))
        (allowOf (checkState state message) message (fromArg message))
        (sub (allowOf (checkState state message) message (fromArg message)) (valArg message)) = 0)
    (hnrD : sstoreStateRefill fork
      (originalAt state message.currentTarget (recipientSlot (fromArg message)))
      (balFrom (checkState state message) message (valArg message) (fromArg message))
      (sub (balFrom (checkState state message) message (valArg message) (fromArg message))
        (valArg message)) = 0)
    {gas : Nat} (hstip : stipCostF fork state message c0 cB c10 cA c3 c4 cF cT ≤ gas)
    (hg : okCostF fork state message c0 cB c10 cA c3 c4 cF cT ≤ gas) :
    HoareI fork (At CODE message 0 [] .empty gas state substate)
      (fun evm => evm.running = false ∧
        Halted false .empty (gas - okCostF fork state message c0 cB c10 cA c3 c4 cF cT)
        (creditedF (checkState state message) message (valArg message) (toArg message)
          (fromArg message))
        (loggedSubF fork (checkSub substate message) (checkState state message) message
          (valArg message) (toArg message) (fromArg message)) evm) := by
  have hB := bodyFI (state := checkState state message) (substate := checkSub substate message)
    (sel := BitVec.ofNat 256 (selector message.data))
    (gas := gas - (PRE_COST_F + slotCost c0 + slotCost cB + slotCost c10))
    hfork hstatic
    (hasAccount_readSlot (hasAccount_readSlot (hasAccount_readSlot hacc)))
    (size_mapMem size_MEM0 (mkey (fromArg message)) 6)
    (ptr_mapMem size_MEM0 mload_MEM0 _ _) hov hfee hallow hbal hto hcA hc3 hc4 hcF hcT
    (by simp only [originalAt_readSlot]; exact hnrA)
    (by simp only [originalAt_readSlot]; exact hnrD)
    (Nat.le_sub_of_add_le (by rw [Nat.add_comm]; exact hstip))
    (Nat.le_sub_of_add_le (by rw [Nat.add_comm]; exact hg))
  have hpre : PRE_COST_F + slotCost c0 + slotCost cB + slotCost c10 ≤ gas :=
    Nat.le_trans (Nat.le_add_right _ _) hg
  refine Triple.seq (HoareG.toIA (preF hfork hlong hsz hsel hv hnp hnb hdep hc0 hcB hc10 hpre)
    (by simp only [PRE_COST_F]; cheap) (by same_store)) ?_
  refine hB.consequence (fun _ h => h) ?_
  rintro evm ⟨hr0, hr, he, ho, hgas, hs, hss⟩
  exact ⟨hr0, hr, he, ho, by rw [hgas, Nat.sub_sub], hs, hss⟩

/-- `headF` over `StepI`, when the writes of the allowance (`hnrA`) and of `balances[_from]`
(`hnrD`) refill nothing. -/
theorem headFI (hfork : .berlin ≤ fork)
    (hstatic : message.isStatic = false) (hacc : hasAccount state message.currentTarget)
    {v t f sel : U256} {M : ByteArray} (hM : M.size = 96)
    (hov : v.toNat * (storageAt state message.currentTarget 3).toNat < 2 ^ 256)
    (hfee : feeOf state message v ≠ 0)
    (hfv : (feeOf state message v).toNat ≤ v.toNat)
    (hallow : allowOf state message f = MAX_UINT ∨ v.toNat ≤ (allowOf state message f).toNat)
    (hbal : v.toNat ≤ (balFrom state message v f).toNat)
    (hto : (balTo state message v t f).toNat + (sendOf state message v).toNat < 2 ^ 256)
    {cA c3 c4 cF cT : Bool}
    (hcA : coldIn substate message.currentTarget (allowFrom message f) = cA)
    (hc3 : coldIn (accessSlot substate message.currentTarget (allowFrom message f))
      message.currentTarget 3 = c3)
    (hc4 : coldIn (accessSlot (accessSlot substate message.currentTarget (allowFrom message f))
      message.currentTarget 3) message.currentTarget 4 = c4)
    (hcF : coldIn (allowedSubF fork substate state message v f) message.currentTarget
      (recipientSlot f) = cF)
    (hcT : coldIn (accessSlot (allowedSubF fork substate state message v f) message.currentTarget
      (recipientSlot f)) message.currentTarget (recipientSlot t) = cT)
    (hnrA : allowOf state message f ≠ MAX_UINT → sstoreStateRefill fork
      (originalAt state message.currentTarget (allowFrom message f)) (allowOf state message f)
      (sub (allowOf state message f) v) = 0)
    (hnrD : sstoreStateRefill fork (originalAt state message.currentTarget (recipientSlot f))
      (balFrom state message v f) (sub (balFrom state message v f) v) = 0)
    {gas : Nat}
    (hg : 1099 + slotCost cA + slotCost c3 + slotCost c4 + slotCost cF + slotCost cT +
      mulCost v + capCost (rawFee state message v) (storageAt state message.currentTarget 4) +
      allowCostF fork state message v f + debitCostF fork state message v f +
      creditCostFeeF fork state message v t f + 2401 ≤ gas) :
    HoareI fork (At CODE message 8648 [0x60, 0, 0, 0, v, t, f, 0x1097, v, t, f, 0x0392, sel] M gas
        state substate)
      (At CODE message 9351 [0x60, sendOf state message v, feeOf state message v,
          allowOf state message f, v, t, f, 0x1097, v, t, f, 0x0392, sel]
        (memAF message M (allowOf state message f) f t)
        (gas - (1099 + slotCost cA + slotCost c3 + slotCost c4 + slotCost cF + slotCost cT +
          mulCost v + capCost (rawFee state message v) (storageAt state message.currentTarget 4) +
          allowCostF fork state message v f + debitCostF fork state message v f +
          creditCostFeeF fork state message v t f))
        (creditedFeeF state message v t f) (creditedSubFeeF fork substate state message v t f)) := by
  have hacc3 : hasAccount (readsF state message f) message.currentTarget :=
    hasAccount_readSlot (hasAccount_readSlot (hasAccount_readSlot hacc))
  have hacc4 : hasAccount (readSlot (allowedF state message v f) message.currentTarget
      (recipientSlot f)) message.currentTarget :=
    hasAccount_readSlot (hasAccount_allowState hacc3)
  have hacc5 : hasAccount (readSlot (debitedF state message v f) message.currentTarget
      (recipientSlot t)) message.currentTarget :=
    hasAccount_readSlot (hasAccount_writeSlot hacc4)
  have horig : ∀ m, originalAt (allowedF state message v f) message.currentTarget m =
      originalAt state message.currentTarget m := by
    intro m
    rw [originalAt_allowState hacc3]
    simp only [originalAt_readSlot]
  have horig2 : ∀ m, originalAt (debitedF state message v f) message.currentTarget m =
      originalAt state message.currentTarget m := by
    intro m
    rw [originalAt_writeSlot hacc4, originalAt_readSlot, horig]
  have hT := slotCost_ge cT
  have hT' : slotCost cT ≤ 2100 := by cases cT <;> decide
  simp only [allowCostF, debitCostF, creditCostFeeF, rawFee, feeOf, allowOf, balFrom, balTo,
    creditedFeeF, debitedF, allowedF, readsF, creditedSubFeeF, debitedSubF, allowedSubF,
    accessF, sendOf, memAF] at hg hfee hfv hbal hto hallow hcF hcT hacc4 hacc5 horig horig2 ⊢
  simp only [allowOf, balFrom, allowedF, readsF] at hnrA hnrD
  simp only [readsF] at hacc3
  stepC (allowRead hfork (by simp) hcA (by gas_ok) hM)
  stepC (feeCall hfork (by simp) hc3 (by gas_ok))
  stepC (mulBlock (by simp) (by valid_dest) (by simpa only [storageAt_readSlot] using hov)
    (by gas_ok))
  stepC (repc (pc' := 8802) (by decide))
  stepC (divCall (by simp) (by gas_ok))
  stepC (divBlock (by simp) (by valid_dest) (by decide) (by gas_ok))
  stepC (repc (pc' := 8816) (by decide))
  stepC (capBlock hfork (by simp) hc4 (by simp only [storageAt_readSlot]; gas_ok))
  simp only [storageAt_readSlot]
  refine Triple.seq (allowStepI hfork (by simp) (by simp only [storageAt_readSlot]) hallow
    (fun _ => ⟨hstatic, hacc3⟩)
    (coldIn_accessSlot_false (coldIn_accessSlot_false (coldIn_accessSlot_self _ _ _)))
    (by simp only [originalAt_readSlot]; exact hnrA)
    (by simp only [originalAt_readSlot]; gas_ok)
    (size_allowMem hM f)) ?_
  simp only [originalAt_readSlot]
  have hMa : (allowMem message M f).size = 96 := size_allowMem hM f
  have hMb := size_allowMem2 (message := message) hMa (storageAt state message.currentTarget
    (allowFrom message f)) f
  stepC (sendCall (by simp) (by gas_ok))
  stepC (subBlock (by simp) (by valid_dest) hfv (by gas_ok))
  stepC (repc (pc' := 9041) (by decide))
  stepC (debitCall hfork (by simp) hcF (by gas_ok) hMb)
  stepC (subBlock (by simp) (by valid_dest) hbal (by gas_ok))
  stepC (repc (pc' := 9125) (by decide))
  refine Triple.seq (Refill.HoareG.toIW (debitStore hfork (by simp) hstatic hacc4
    (coldIn_accessSlot_self _ _ _)
    (by simp only [storageAt_readSlot, originalAt_readSlot, horig]; gas_ok) (size_mapMem hMb _ _))
    (by omega) hacc4 (by simp only [storageAt_readSlot, originalAt_readSlot, horig]; gas_ok)
    (by simp only [storageAt_readSlot, originalAt_readSlot, horig]; exact hnrD)) ?_
  simp only [storageAt_readSlot, originalAt_readSlot, horig]
  stepC (creditCall hfork (by simp) (cT := cT) (by rw [coldIn_storeSub]; exact hcT) (by gas_ok)
    (size_mapMem (size_mapMem hMb _ _) _ _))
  stepC (addBlock (by simp) (by valid_dest) hto (by gas_ok))
  stepC (repc (pc' := 9274) (by decide))
  refine Triple.seq (Refill.HoareG.toIW (creditStoreFeeF hfork hfee (by simp) hstatic hacc5
    (coldIn_accessSlot_self _ _ _) (by gas_ok)
    (by simp only [storageAt_readSlot, originalAt_readSlot, horig2]; gas_ok)
    (size_mapMem (size_mapMem (size_mapMem hMb _ _) _ _) _ _))
    (by omega) hacc5
    (by simp only [storageAt_readSlot, originalAt_readSlot, horig2]; gas_ok)
    (by simp only [storageAt_readSlot]; exact Refill.refill_add hto)) ?_
  simp only [storageAt_readSlot, originalAt_readSlot, horig2]
  exact HoareG.toIA (restate rfl rfl rfl (by gas_ok) rfl rfl) (by cheap) (by same_store)

/-- `ownerPartF` over `StepI`: the owner's write adds the fee without overflow, so it refills
nothing. -/
theorem ownerPartFI (hfork : .berlin ≤ fork)
    (hstatic : message.isStatic = false) {st : State.TransactionState} {ss : Substate}
    (hacc : hasAccount st message.currentTarget) {send fee A v t f sel o : U256} {M : ByteArray}
    (hM : M.size = 96) (hptr : loadWord (memoryReadBytes M 64 32) 0 32 = 0x60)
    (hc0 : coldIn ss message.currentTarget 0 = false) {cO : Bool}
    (hcO : coldIn ss message.currentTarget (ownerSlotOf st message.currentTarget) = cO)
    (ho : originalAt st message.currentTarget (ownerSlotOf st message.currentTarget) = o)
    (hown : (balOf st message.currentTarget).toNat + fee.toNat < 2 ^ 256) {gas : Nat}
    (hg : 4417 + slotCost cO + Gas.writeCost fork o (balOf st message.currentTarget)
      (add (balOf st message.currentTarget) fee) false ≤ gas) :
    HoareI fork (At CODE message 9351 [0x60, send, fee, A, v, t, f, 0x1097, v, t, f, 0x0392, sel]
        M gas st ss)
      (fun evm => evm.running = false ∧ Halted false .empty (gas - (4417 + slotCost cO +
          Gas.writeCost fork o (balOf st message.currentTarget)
          (add (balOf st message.currentTarget) fee) false))
        (readSlot (ownedB st message.currentTarget fee) message.currentTarget 0)
        (feeSubBF fork ss st message o fee send t f) evm) := by
  simp only [ownerSlotOf, balOf, ownedB, feeSubBF] at hcO ho hown hg ⊢
  stepC (ownerCallF (cO := cO) hfork rfl (by simp) hc0
    (by rw [coldIn_accessSlot_of_warm hc0]; exact hcO) (by gas_ok) hM)
  stepC (addBlock (by simp) (by valid_dest) hown (by gas_ok))
  stepC (repc (pc' := 9465) (by decide))
  refine Triple.seq (Refill.HoareG.toIW' (ownerStoreF hfork
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
  stepC (ownerLogF hfork rfl (by simp) hstatic
    (coldIn_storeSub_false (coldIn_accessSlot_self _ _ _)) (by gas_ok)
    (size_mapMem (size_mapMem hM _ _) _ _)
    (ptr_mapMem (size_mapMem hM _ _) (ptr_mapMem hM hptr _ _) _ _))
  stepC (logBlock128F (by simp) hstatic (by gas_ok)
    (by rw [ByteArray.size_append, size_wordBytes]
        exact congrArg (· + 32) (size_mapMem (size_mapMem hM _ _) _ _))
    (by rw [read64_append (size_mapMem (size_mapMem hM _ _) _ _)]
        exact ptr_mapMem (size_mapMem hM _ _) (ptr_mapMem hM hptr _ _) _ _))
  refine (Refill.SpecG.toIA (endBlock (by gas_ok)) (by cheap) (by same_store)).consequence
    (fun _ h => h) ?_
  rintro evm ⟨hr0, hr, he, ho, hgas, hs, hss⟩
  exact ⟨hr0, hr, he, ho, by rw [hgas]; gas_ok, hs, hss⟩

/-- `bodyFeeF` over `StepI`, when the writes of the allowance (`hnrA`) and of `balances[_from]`
(`hnrD`) refill nothing. -/
theorem bodyFeeFI (hfork : .berlin ≤ fork)
    (hstatic : message.isStatic = false) (hacc : hasAccount state message.currentTarget)
    {v t f sel : U256} {M : ByteArray} (hM : M.size = 96)
    (hptr : loadWord (memoryReadBytes M 64 32) 0 32 = 0x60)
    (hov : v.toNat * (storageAt state message.currentTarget 3).toNat < 2 ^ 256)
    (hfee : feeOf state message v ≠ 0)
    (hfv : (feeOf state message v).toNat ≤ v.toNat)
    (hallow : allowOf state message f = MAX_UINT ∨ v.toNat ≤ (allowOf state message f).toNat)
    (hbal : v.toNat ≤ (balFrom state message v f).toNat)
    (hto : (balTo state message v t f).toNat + (sendOf state message v).toNat < 2 ^ 256)
    (hown : (balOF state message v t f).toNat + (feeOf state message v).toNat < 2 ^ 256)
    (hc0 : coldIn substate message.currentTarget 0 = false)
    {cA c3 c4 cF cT cO : Bool}
    (hcA : coldIn substate message.currentTarget (allowFrom message f) = cA)
    (hc3 : coldIn (accessSlot substate message.currentTarget (allowFrom message f))
      message.currentTarget 3 = c3)
    (hc4 : coldIn (accessSlot (accessSlot substate message.currentTarget (allowFrom message f))
      message.currentTarget 3) message.currentTarget 4 = c4)
    (hcF : coldIn (allowedSubF fork substate state message v f) message.currentTarget
      (recipientSlot f) = cF)
    (hcT : coldIn (accessSlot (allowedSubF fork substate state message v f) message.currentTarget
      (recipientSlot f)) message.currentTarget (recipientSlot t) = cT)
    (hcO : coldIn (creditedSubFeeF fork substate state message v t f) message.currentTarget
      (ownerSlot (ownerWordF state message v t f)) = cO)
    (hnrA : allowOf state message f ≠ MAX_UINT → sstoreStateRefill fork
      (originalAt state message.currentTarget (allowFrom message f)) (allowOf state message f)
      (sub (allowOf state message f) v) = 0)
    (hnrD : sstoreStateRefill fork (originalAt state message.currentTarget (recipientSlot f))
      (balFrom state message v f) (sub (balFrom state message v f) v) = 0)
    {gas : Nat}
    (hg : 5516 + slotCost cA + slotCost c3 + slotCost c4 + slotCost cF + slotCost cT +
      slotCost cO + mulCost v +
      capCost (rawFee state message v) (storageAt state message.currentTarget 4) +
      allowCostF fork state message v f + debitCostF fork state message v f +
      creditCostFeeF fork state message v t f + ownerCostF fork state message v t f ≤ gas) :
    HoareI fork (At CODE message 8648 [0x60, 0, 0, 0, v, t, f, 0x1097, v, t, f, 0x0392, sel] M gas
        state substate)
      (fun evm => evm.running = false ∧ Halted false .empty (gas - (5516 + slotCost cA +
        slotCost c3 + slotCost c4 + slotCost cF + slotCost cT + slotCost cO + mulCost v +
        capCost (rawFee state message v) (storageAt state message.currentTarget 4) +
        allowCostF fork state message v f + debitCostF fork state message v f +
        creditCostFeeF fork state message v t f + ownerCostF fork state message v t f))
        (feeStateF state message v t f) (feeSubF fork substate state message v t f) evm) := by
  have hacc3 : hasAccount (readsF state message f) message.currentTarget :=
    hasAccount_readSlot (hasAccount_readSlot (hasAccount_readSlot hacc))
  have hacc4 : hasAccount (readSlot (allowedF state message v f) message.currentTarget
      (recipientSlot f)) message.currentTarget :=
    hasAccount_readSlot (hasAccount_allowState hacc3)
  have hacc5 : hasAccount (readSlot (debitedF state message v f) message.currentTarget
      (recipientSlot t)) message.currentTarget :=
    hasAccount_readSlot (hasAccount_writeSlot hacc4)
  have horig : ∀ m, originalAt (creditedFeeF state message v t f) message.currentTarget m =
      originalAt state message.currentTarget m := by
    intro m
    rw [originalAt_writeSlot hacc5, originalAt_readSlot, originalAt_writeSlot hacc4,
      originalAt_readSlot, originalAt_allowState hacc3]
    simp only [originalAt_readSlot]
  have hw : coldIn (creditedSubFeeF fork substate state message v t f) message.currentTarget 0 =
      false :=
    coldIn_storeSub_false (coldIn_accessSlot_false (coldIn_storeSub_false
      (coldIn_accessSlot_false (coldIn_allowSub_false (coldIn_accessSlot_false
        (coldIn_accessSlot_false (coldIn_accessSlot_false hc0)))))))
  have hMa : (allowMem message M f).size = 96 := size_allowMem hM f
  have hMb := size_allowMem2 (message := message) hMa (allowOf state message f) f
  have hPb := ptr_allowMem2 (message := message) hMa (ptr_allowMem hM hptr f)
    (allowOf state message f) f
  have hA := headFI (sel := sel) hfork hstatic hacc hM hov hfee hfv hallow hbal hto hcA hc3
    hc4 hcF hcT hnrA hnrD (gas := gas) (by simp only [ownerCostF] at hg; omega)
  have hB := ownerPartFI (message := message) (st := creditedFeeF state message v t f)
    (ss := creditedSubFeeF fork substate state message v t f) (send := sendOf state message v)
    (A := allowOf state message f) (v := v) (t := t) (f := f) (sel := sel)
    (M := memAF message M (allowOf state message f) f t) hfork hstatic
    (hasAccount_writeSlot hacc5)
    (size_mapMem (size_mapMem (size_mapMem (size_mapMem hMb _ _) _ _) _ _) _ _)
    (ptr_mapMem (size_mapMem (size_mapMem (size_mapMem hMb _ _) _ _) _ _)
      (ptr_mapMem (size_mapMem (size_mapMem hMb _ _) _ _)
        (ptr_mapMem (size_mapMem hMb _ _) (ptr_mapMem hMb hPb _ _) _ _) _ _) _ _)
    hw hcO (horig _) hown
    (gas := gas - (1099 + slotCost cA + slotCost c3 + slotCost c4 + slotCost cF + slotCost cT +
          mulCost v + capCost (rawFee state message v) (storageAt state message.currentTarget 4) +
          allowCostF fork state message v f + debitCostF fork state message v f +
          creditCostFeeF fork state message v t f))
    (by simp only [ownerCostF, ownerSlotOf, balOf, balOF, ownerWordF] at hg ⊢; omega)
  refine Triple.seq hA (hB.consequence (fun _ h => h) ?_)
  rintro evm ⟨hr0, hr, he, ho, hgas, hs, hss⟩
  refine ⟨hr0, hr, he, ho, ?_, hs, hss⟩
  rw [hgas]
  simp only [ownerCostF, ownerSlotOf, balOf, balOF, ownerWordF]
  omega

/-- `spec_feeF` over `StepI`, when the writes of the allowance (`hnrA`) and of `balances[_from]`
(`hnrD`) refill nothing. -/
theorem spec_feeFI (hfork : .berlin ≤ fork)
    (hstatic : message.isStatic = false) (hacc : hasAccount state message.currentTarget)
    (hlong : 100 ≤ message.data.size) (hsz : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x23b872dd) (hv : message.value = 0)
    (hnp : byte20 (storageAt state message.currentTarget 0) = 0)
    (hnb : (storageAt state message.currentTarget (blackFrom (fromArg message))).toNat % 256 = 0)
    (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    (hov : (valArg message).toNat *
      (storageAt (checkState state message) message.currentTarget 3).toNat < 2 ^ 256)
    (hfee : feeOf (checkState state message) message (valArg message) ≠ 0)
    (hfv : (feeOf (checkState state message) message (valArg message)).toNat ≤
      (valArg message).toNat)
    (hallow : allowOf (checkState state message) message (fromArg message) = MAX_UINT ∨
      (valArg message).toNat ≤ (allowOf (checkState state message) message (fromArg message)).toNat)
    (hbal : (valArg message).toNat ≤
      (balFrom (checkState state message) message (valArg message) (fromArg message)).toNat)
    (hto : (balTo (checkState state message) message (valArg message) (toArg message)
      (fromArg message)).toNat +
      (sendOf (checkState state message) message (valArg message)).toNat < 2 ^ 256)
    (hown : (balOF (checkState state message) message (valArg message) (toArg message)
      (fromArg message)).toNat +
      (feeOf (checkState state message) message (valArg message)).toNat < 2 ^ 256)
    {c0 cB c10 cA c3 c4 cF cT cO : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hcB : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget
      (blackFrom (fromArg message)) = cB)
    (hc10 : coldIn (accessSlot (accessSlot substate message.currentTarget 0) message.currentTarget
      (blackFrom (fromArg message))) message.currentTarget 10 = c10)
    (hcA : coldIn (checkSub substate message) message.currentTarget
      (allowFrom message (fromArg message)) = cA)
    (hc3 : coldIn (accessSlot (checkSub substate message) message.currentTarget
      (allowFrom message (fromArg message))) message.currentTarget 3 = c3)
    (hc4 : coldIn (accessSlot (accessSlot (checkSub substate message) message.currentTarget
      (allowFrom message (fromArg message))) message.currentTarget 3) message.currentTarget 4 = c4)
    (hcF : coldIn (allowedSubF fork (checkSub substate message) (checkState state message) message
      (valArg message) (fromArg message)) message.currentTarget (recipientSlot (fromArg message)) =
        cF)
    (hcT : coldIn (accessSlot (allowedSubF fork (checkSub substate message)
      (checkState state message) message (valArg message) (fromArg message)) message.currentTarget
      (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (toArg message)) = cT)
    (hcO : coldIn (creditedSubFeeF fork (checkSub substate message) (checkState state message)
      message (valArg message) (toArg message) (fromArg message)) message.currentTarget
      (ownerSlot (ownerWordF (checkState state message) message (valArg message) (toArg message)
        (fromArg message))) = cO)
    (hnrA : allowOf (checkState state message) message (fromArg message) ≠ MAX_UINT →
      sstoreStateRefill fork
        (originalAt state message.currentTarget (allowFrom message (fromArg message)))
        (allowOf (checkState state message) message (fromArg message))
        (sub (allowOf (checkState state message) message (fromArg message)) (valArg message)) = 0)
    (hnrD : sstoreStateRefill fork
      (originalAt state message.currentTarget (recipientSlot (fromArg message)))
      (balFrom (checkState state message) message (valArg message) (fromArg message))
      (sub (balFrom (checkState state message) message (valArg message) (fromArg message))
        (valArg message)) = 0)
    {gas : Nat} (hg : feeCostF fork state message c0 cB c10 cA c3 c4 cF cT cO ≤ gas) :
    HoareI fork (At CODE message 0 [] .empty gas state substate)
      (fun evm => evm.running = false ∧
        Halted false .empty (gas - feeCostF fork state message c0 cB c10 cA c3 c4 cF cT cO)
        (feeStateF (checkState state message) message (valArg message) (toArg message)
          (fromArg message))
        (feeSubF fork (checkSub substate message) (checkState state message) message
          (valArg message) (toArg message) (fromArg message)) evm) := by
  have hB := bodyFeeFI (state := checkState state message) (substate := checkSub substate message)
    (sel := BitVec.ofNat 256 (selector message.data))
    (gas := gas - (PRE_COST_F + slotCost c0 + slotCost cB + slotCost c10))
    hfork hstatic
    (hasAccount_readSlot (hasAccount_readSlot (hasAccount_readSlot hacc)))
    (size_mapMem size_MEM0 (mkey (fromArg message)) 6)
    (ptr_mapMem size_MEM0 mload_MEM0 _ _) hov hfee hfv hallow hbal hto hown
    (coldIn_accessSlot_false (coldIn_accessSlot_false (coldIn_accessSlot_self _ _ _)))
    hcA hc3 hc4 hcF hcT hcO
    (by simp only [originalAt_readSlot]; exact hnrA)
    (by simp only [originalAt_readSlot]; exact hnrD)
    (Nat.le_sub_of_add_le (by rw [Nat.add_comm]; exact hg))
  have hpre : PRE_COST_F + slotCost c0 + slotCost cB + slotCost c10 ≤ gas :=
    Nat.le_trans (Nat.le_add_right _ _) hg
  refine Triple.seq (HoareG.toIA (preF hfork hlong hsz hsel hv hnp hnb hdep hc0 hcB hc10 hpre)
    (by simp only [PRE_COST_F]; cheap) (by same_store)) ?_
  refine hB.consequence (fun _ h => h) ?_
  rintro evm ⟨hr0, hr, he, ho, hgas, hs, hss⟩
  exact ⟨hr0, hr, he, ho, by rw [hgas, Nat.sub_sub], hs, hss⟩

end UsdtVerify.TransferFrom
