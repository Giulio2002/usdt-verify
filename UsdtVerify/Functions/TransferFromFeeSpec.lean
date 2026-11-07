import UsdtVerify.Functions.TransferFromFee
import UsdtVerify.Functions.TransferFromFault

/-!
# transferFrom(address,address,uint256): the success path with a fee above 0

`headF` (8648 → 9351), `ownerPartF` (9351 → STOP at 915), `bodyFeeF` (both), and `spec_feeF` /
`runFrame_feeF` from pc 0. With the fee `fee ≠ 0` (as the bytecode computes it): the allowance
step as in `spec_ok`, `balances[_from] -= v`, `balances[_to] += v - fee`,
`balances[owner] += fee`, and the logs `Transfer(_from, owner, fee)` then
`Transfer(_from, _to, v - fee)`. `owner` is the low 160 bits of slot 0, read by the code three
times after the recipient's write; each read is stated in the state where the code makes it.
-/

namespace UsdtVerify.TransferFrom

open EthLib.Base (Fork U256 Address)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts
open Transfer SafeMath TransferOk TransferFee

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate}

theorem coldIn_allowSub_false {ss : Substate} {t : Address} {n m o A v : U256}
    (h : coldIn ss t m = false) : coldIn (allowSub fork ss t n o A v) t m = false := by
  unfold allowSub; split
  · exact h
  · exact coldIn_storeSub_false h

/-- The state after the write of `balances[_to] = balTo + sendAmount`. -/
abbrev creditedFeeF (state : State.TransactionState) (message : Message fork) (v t f : U256) :
    State.TransactionState :=
  writeSlot (readSlot (debitedF state message v f) message.currentTarget (recipientSlot t))
    message.currentTarget (recipientSlot t)
    (add (balTo state message v t f) (sendOf state message v))

/-- The substate after that write. -/
abbrev creditedSubFeeF (fork : Fork) (substate : Substate) (state : State.TransactionState)
    (message : Message fork) (v t f : U256) : Substate :=
  storeSub fork (accessSlot (debitedSubF fork substate state message v f) message.currentTarget
      (recipientSlot t)) message.currentTarget (recipientSlot t)
    (originalAt state message.currentTarget (recipientSlot t)) (balTo state message v t f)
    (add (balTo state message v t f) (sendOf state message v))

/-- The price of the write of `_to` (warm). -/
abbrev creditCostFeeF (fork : Fork) (state : State.TransactionState) (message : Message fork)
    (v t f : U256) : Nat :=
  sstoreCost fork (originalAt state message.currentTarget (recipientSlot t))
    (balTo state message v t f) (add (balTo state message v t f) (sendOf state message v)) false

/-- The memory at 9351. -/
abbrev memAF (message : Message fork) (M : ByteArray) (A f t : U256) : ByteArray :=
  mapMem (mapMem (mapMem (mapMem (allowMem2 message (allowMem message M f) A f) (mkey f) 2)
    (mkey f) 2) (mkey t) 2) (mkey t) 2

/-- From 8648, with a fee above 0, up to the owner's credit at 9351. -/
theorem headF (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
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
    {gas : Nat}
    (hg : 1099 + slotCost cA + slotCost c3 + slotCost c4 + slotCost cF + slotCost cT +
      mulCost v + capCost (rawFee state message v) (storageAt state message.currentTarget 4) +
      allowCostF fork state message v f + debitCostF fork state message v f +
      creditCostFeeF fork state message v t f + 2401 ≤ gas) :
    Hoare fork (At CODE message 8648 [0x60, 0, 0, 0, v, t, f, 0x1097, v, t, f, 0x0392, sel] M gas
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
  simp only [allowCostF, debitCostF, creditCostFeeF, rawFee, feeOf, allowOf, balFrom, balTo,
    creditedFeeF, debitedF, allowedF, readsF, creditedSubFeeF, debitedSubF, allowedSubF,
    accessF, sendOf, memAF] at hg hfee hfv hbal hto hallow hcF hcT hacc4 hacc5 horig horig2 ⊢
  step allowRead hfork (by simp) hcA (by gas_ok) hM
  step feeCall hfork (by simp) hc3 (by gas_ok)
  step mulBlock (by simp) (by valid_dest) (by simpa only [storageAt_readSlot] using hov)
    (by gas_ok)
  at_pc 8802
  step divCall (by simp) (by gas_ok)
  step divBlock (by simp) (by valid_dest) (by decide) (by gas_ok)
  at_pc 8816
  step capBlock hfork (by simp) hc4 (by simp only [storageAt_readSlot]; gas_ok)
  simp only [storageAt_readSlot]
  step allowStep hfork hglam hstatic hacc3 (by simp) (by simp only [storageAt_readSlot]) hallow
    (coldIn_accessSlot_false (coldIn_accessSlot_false (coldIn_accessSlot_self _ _ _)))
    (by simp only [originalAt_readSlot]; gas_ok)
    (size_allowMem hM f)
  simp only [originalAt_readSlot]
  have hMa : (allowMem message M f).size = 96 := size_allowMem hM f
  have hMb := size_allowMem2 (message := message) hMa (storageAt state message.currentTarget
    (allowFrom message f)) f
  step sendCall (by simp) (by gas_ok)
  step subBlock (by simp) (by valid_dest) hfv (by gas_ok)
  at_pc 9041
  step debitCall hfork (by simp) hcF (by gas_ok) hMb
  step subBlock (by simp) (by valid_dest) hbal (by gas_ok)
  at_pc 9125
  step debitStore hfork hglam (by simp) hstatic hacc4 (coldIn_accessSlot_self _ _ _)
    (by simp only [storageAt_readSlot, originalAt_readSlot, horig]; gas_ok) (size_mapMem hMb _ _)
  simp only [storageAt_readSlot, originalAt_readSlot, horig]
  step creditCall hfork (by simp) (cT := cT) (by rw [coldIn_storeSub]; exact hcT) (by gas_ok)
    (size_mapMem (size_mapMem hMb _ _) _ _)
  step addBlock (by simp) (by valid_dest) hto (by gas_ok)
  at_pc 9274
  step creditStoreFeeF hfork hglam hfee (by simp) hstatic hacc5 (coldIn_accessSlot_self _ _ _)
    (by gas_ok)
    (by simp only [storageAt_readSlot, originalAt_readSlot, horig2]; gas_ok)
    (size_mapMem (size_mapMem (size_mapMem hMb _ _) _ _) _ _)
  simp only [storageAt_readSlot, originalAt_readSlot, horig2]
  exact restate rfl rfl rfl (by gas_ok) rfl rfl

/-- The substate after the owner's log `Transfer(_from, owner', fee)`, `owner'` read from slot 0
after the owner's write. -/
abbrev ownerLoggedBF (fork : Fork) (ss : Substate) (st : State.TransactionState)
    (message : Message fork) (o fee f : U256) : Substate :=
  { accessSlot (ownedSubB fork ss st message.currentTarget o fee) message.currentTarget 0 with
    logs := (ownedSubB fork ss st message.currentTarget o fee).logs.push
      (transferLog message.currentTarget (bitwiseAnd ADDR_MASK f)
        (bitwiseAnd ADDR_MASK (ownerKey
          (storageAt (ownedB st message.currentTarget fee) message.currentTarget 0))) fee) }

/-- The substate at the end: then the main log `Transfer(_from, _to, send)`. -/
abbrev feeSubBF (fork : Fork) (ss : Substate) (st : State.TransactionState)
    (message : Message fork) (o fee send t f : U256) : Substate :=
  { ownerLoggedBF fork ss st message o fee f with
    logs := (ownerLoggedBF fork ss st message o fee f).logs.push
      (transferLog message.currentTarget (bitwiseAnd ADDR_MASK f) (bitwiseAnd ADDR_MASK t) send) }

/-- From 9351, the owner's credit, both logs and the STOP at 915. -/
theorem ownerPartF (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    (hstatic : message.isStatic = false) {st : State.TransactionState} {ss : Substate}
    (hacc : hasAccount st message.currentTarget) {send fee A v t f sel o : U256} {M : ByteArray}
    (hM : M.size = 96) (hptr : loadWord (memoryReadBytes M 64 32) 0 32 = 0x60)
    (hc0 : coldIn ss message.currentTarget 0 = false) {cO : Bool}
    (hcO : coldIn ss message.currentTarget (ownerSlotOf st message.currentTarget) = cO)
    (ho : originalAt st message.currentTarget (ownerSlotOf st message.currentTarget) = o)
    (hown : (balOf st message.currentTarget).toNat + fee.toNat < 2 ^ 256) {gas : Nat}
    (hg : 4417 + slotCost cO + sstoreCost fork o (balOf st message.currentTarget)
      (add (balOf st message.currentTarget) fee) false ≤ gas) :
    Spec fork (At CODE message 9351 [0x60, send, fee, A, v, t, f, 0x1097, v, t, f, 0x0392, sel]
        M gas st ss)
      (Local.Stopped (gas - (4417 + slotCost cO + sstoreCost fork o (balOf st message.currentTarget)
          (add (balOf st message.currentTarget) fee) false))
        (readSlot (ownedB st message.currentTarget fee) message.currentTarget 0)
        (feeSubBF fork ss st message o fee send t f)) := by
  simp only [ownerSlotOf, balOf, ownedB, feeSubBF] at hcO ho hown hg ⊢
  step ownerCallF (cO := cO) hfork rfl (by simp) hc0
    (by rw [coldIn_accessSlot_of_warm hc0]; exact hcO) (by gas_ok) hM
  step addBlock (by simp) (by valid_dest) hown (by gas_ok)
  at_pc 9465
  step ownerStoreF hfork (by rw [storageAt_readSlot, storageAt_readSlot]) hglam (by simp) hstatic
    (hasAccount_readSlot (hasAccount_readSlot hacc))
    (coldIn_accessSlot_false (coldIn_accessSlot_false hc0)) (coldIn_accessSlot_self _ _ _)
    (by rw [originalAt_readSlot, originalAt_readSlot, storageAt_readSlot, storageAt_readSlot, ho]
        gas_ok)
    (size_mapMem hM _ _)
  rw [originalAt_readSlot, originalAt_readSlot, storageAt_readSlot, storageAt_readSlot, ho]
  step ownerLogF hfork rfl (by simp) hstatic
    (coldIn_storeSub_false (coldIn_accessSlot_self _ _ _)) (by gas_ok)
    (size_mapMem (size_mapMem hM _ _) _ _)
    (ptr_mapMem (size_mapMem hM _ _) (ptr_mapMem hM hptr _ _) _ _)
  step logBlock128F (by simp) hstatic (by gas_ok)
    (by rw [ByteArray.size_append, size_wordBytes]
        exact congrArg (· + 32) (size_mapMem (size_mapMem hM _ _) _ _))
    (by rw [read64_append (size_mapMem (size_mapMem hM _ _) _ _)]
        exact ptr_mapMem (size_mapMem hM _ _) (ptr_mapMem hM hptr _ _) _ _)
  refine (endBlock (by gas_ok)).consequence (fun _ h => h) ?_
  rintro evm ⟨hr, he, hgas, hs, hss⟩
  exact ⟨hr, he, by rw [hgas]; gas_ok, hs, hss⟩

/-- The word of slot 0 read for the owner's credit (after the write of `_to`). -/
abbrev ownerWordF (state : State.TransactionState) (message : Message fork) (v t f : U256) :
    U256 :=
  storageAt (creditedFeeF state message v t f) message.currentTarget 0

/-- `balances[owner]`, read after the write of `_to`. -/
abbrev balOF (state : State.TransactionState) (message : Message fork) (v t f : U256) : U256 :=
  balOf (creditedFeeF state message v t f) message.currentTarget

/-- The state at the end. -/
abbrev feeStateF (state : State.TransactionState) (message : Message fork) (v t f : U256) :
    State.TransactionState :=
  readSlot (ownedB (creditedFeeF state message v t f) message.currentTarget
    (feeOf state message v)) message.currentTarget 0

/-- The substate at the end. -/
abbrev feeSubF (fork : Fork) (substate : Substate) (state : State.TransactionState)
    (message : Message fork) (v t f : U256) : Substate :=
  feeSubBF fork (creditedSubFeeF fork substate state message v t f)
    (creditedFeeF state message v t f) message
    (originalAt state message.currentTarget (ownerSlot (ownerWordF state message v t f)))
    (feeOf state message v) (sendOf state message v) t f

/-- The price of the owner's write (warm). -/
abbrev ownerCostF (fork : Fork) (state : State.TransactionState) (message : Message fork)
    (v t f : U256) : Nat :=
  sstoreCost fork (originalAt state message.currentTarget
      (ownerSlot (ownerWordF state message v t f)))
    (balOF state message v t f) (add (balOF state message v t f) (feeOf state message v)) false

/-- From 8648, with a fee above 0, the success path of `transferFrom` up to the STOP at 915. -/
theorem bodyFeeF (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
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
    {gas : Nat}
    (hg : 5516 + slotCost cA + slotCost c3 + slotCost c4 + slotCost cF + slotCost cT +
      slotCost cO + mulCost v +
      capCost (rawFee state message v) (storageAt state message.currentTarget 4) +
      allowCostF fork state message v f + debitCostF fork state message v f +
      creditCostFeeF fork state message v t f + ownerCostF fork state message v t f ≤ gas) :
    Spec fork (At CODE message 8648 [0x60, 0, 0, 0, v, t, f, 0x1097, v, t, f, 0x0392, sel] M gas
        state substate)
      (Local.Stopped (gas - (5516 + slotCost cA + slotCost c3 + slotCost c4 + slotCost cF +
        slotCost cT + slotCost cO + mulCost v +
        capCost (rawFee state message v) (storageAt state message.currentTarget 4) +
        allowCostF fork state message v f + debitCostF fork state message v f +
        creditCostFeeF fork state message v t f + ownerCostF fork state message v t f))
        (feeStateF state message v t f) (feeSubF fork substate state message v t f)) := by
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
  have hA := headF (sel := sel) hfork hglam hstatic hacc hM hov hfee hfv hallow hbal hto hcA hc3
    hc4 hcF hcT (gas := gas) (by simp only [ownerCostF] at hg; omega)
  have hB := ownerPartF (message := message) (st := creditedFeeF state message v t f)
    (ss := creditedSubFeeF fork substate state message v t f) (send := sendOf state message v)
    (A := allowOf state message f) (v := v) (t := t) (f := f) (sel := sel)
    (M := memAF message M (allowOf state message f) f t) hfork hglam hstatic
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
  rintro evm ⟨hr, he, hgas, hs, hss⟩
  refine ⟨hr, he, ?_, hs, hss⟩
  rw [hgas]
  simp only [ownerCostF, ownerSlotOf, balOf, balOF, ownerWordF]
  omega

/-- The whole gas of the success path of `transferFrom` with a fee above 0. -/
abbrev feeCostF (fork : Fork) (state : State.TransactionState) (message : Message fork)
    (c0 cB c10 cA c3 c4 cF cT cO : Bool) : Nat :=
  PRE_COST_F + slotCost c0 + slotCost cB + slotCost c10 + (5516 + slotCost cA + slotCost c3 +
    slotCost c4 + slotCost cF + slotCost cT + slotCost cO + mulCost (valArg message) +
    capCost (rawFee (checkState state message) message (valArg message))
      (storageAt (checkState state message) message.currentTarget 4) +
    allowCostF fork (checkState state message) message (valArg message) (fromArg message) +
    debitCostF fork (checkState state message) message (valArg message) (fromArg message) +
    creditCostFeeF fork (checkState state message) message (valArg message) (toArg message)
      (fromArg message) +
    ownerCostF fork (checkState state message) message (valArg message) (toArg message)
      (fromArg message))

/-- The specification of a successful `transferFrom(address,address,uint256)` with a fee above 0.

Write `f`, `t` for argument words 0 and 1 masked to 160 bits, `v` for word 2, `S` for the state
after the reads of the checks, `A` for `allowed[f][caller]` in `S`, `fee` for the fee as the
bytecode computes it in `S` (`feeOf`).

Hypotheses: as `spec_ok` (TransferFromSpec.lean), with `fee ≠ 0` in place of `fee = 0`, plus
`fee ≤ v` (SafeMath sub of `sendAmount`), `balances[t] + (v - fee) < 2^256` (read after the write
of `f`), and `balances[owner] + fee < 2^256` (`owner` = low 160 bits of slot 0, both read after
the write of `t`); enough gas (`feeCostF ≤ gas`; the stipends of the four SSTOREs follow, since
logs costing more than 2300 come after each).

Then the run stops normally (STOP) with gas left `gas - feeCostF`; the state `feeStateF S`: the
allowance step (`A - v` unless `A = MAX_UINT`), `balances[f] := balF - v`,
`balances[t] := balT + (v - fee)`, `balances[owner] := balO + fee`, slot 0 recorded read; the
substate with the accesses and refunds, and the logs `Transfer(f, owner', fee)` (owner' read from
slot 0 after the owner's write) then `Transfer(f, t, v - fee)`. -/
theorem spec_feeF (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
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
    {gas : Nat} (hg : feeCostF fork state message c0 cB c10 cA c3 c4 cF cT cO ≤ gas) :
    Spec fork (At CODE message 0 [] .empty gas state substate)
      (Local.Stopped (gas - feeCostF fork state message c0 cB c10 cA c3 c4 cF cT cO)
        (feeStateF (checkState state message) message (valArg message) (toArg message)
          (fromArg message))
        (feeSubF fork (checkSub substate message) (checkState state message) message
          (valArg message) (toArg message) (fromArg message))) := by
  have hB := bodyFeeF (state := checkState state message) (substate := checkSub substate message)
    (sel := BitVec.ofNat 256 (selector message.data))
    (gas := gas - (PRE_COST_F + slotCost c0 + slotCost cB + slotCost c10))
    hfork hglam hstatic
    (hasAccount_readSlot (hasAccount_readSlot (hasAccount_readSlot hacc)))
    (size_mapMem size_MEM0 (mkey (fromArg message)) 6)
    (ptr_mapMem size_MEM0 mload_MEM0 _ _) hov hfee hfv hallow hbal hto hown
    (coldIn_accessSlot_false (coldIn_accessSlot_false (coldIn_accessSlot_self _ _ _)))
    hcA hc3 hc4 hcF hcT hcO
    (Nat.le_sub_of_add_le (by rw [Nat.add_comm]; exact hg))
  have hpre : PRE_COST_F + slotCost c0 + slotCost cB + slotCost c10 ≤ gas :=
    Nat.le_trans (Nat.le_add_right _ _) hg
  refine Triple.seq (preF hfork hlong hsz hsel hv hnp hnb hdep hc0 hcB hc10 hpre)
    (hB.consequence (fun _ h => h) ?_)
  rintro evm ⟨hr, he, hgas, hs, hss⟩
  exact ⟨hr, he, by rw [hgas, Nat.sub_sub], hs, hss⟩

/-- The loop of the interpreter runs a successful `transferFrom` call with a fee above 0 to its
specification. It holds for every bound on the gas of messages and every runner of messages. -/
theorem runFrame_feeF (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
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
    {gas : Nat} (hg : feeCostF fork state message c0 cB c10 cA c3 c4 cF cT cO ≤ gas) {bound : Nat}
    {runChild : MessageRunner fork Nat bound} {evm : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    ∃ stopped, runFrame (step fork) (step_decreases fork) bound runChild evm within =
      .ok stopped ∧
      (Local.Stopped (gas - feeCostF fork state message c0 cB c10 cA c3 c4 cF cT cO)
        (feeStateF (checkState state message) message (valArg message) (toArg message)
          (fromArg message))
        (feeSubF fork (checkSub substate message) (checkState state message) message
          (valArg message) (toArg message) (fromArg message))) stopped :=
  (spec_feeF hfork hglam hstatic hacc hlong hsz hsel hv hnp hnb hdep hov hfee hfv hallow hbal hto
    hown hc0 hcB hc10 hcA hc3 hc4 hcF hcT hcO hg).runFrame start within

end UsdtVerify.TransferFrom
