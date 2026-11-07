import UsdtVerify.Functions.TransferFromFeeSpec

/-!
# transferFrom(address,address,uint256): the remaining failed SafeMath asserts

- `spec_feeGtF`: the fee is above `v`: INVALID at `sub(v, fee)`, after the allowance step.
- `spec_toOvF`: `balances[_to] + (v - fee)` overflows: INVALID at the `add`, after the write
  of `balances[_from]`.
- `spec_ownerOvF`: with a fee above 0, `balances[owner] + fee` overflows: INVALID at the owner's
  `add`, after the write of `balances[_to]`.
-/

namespace UsdtVerify.TransferFrom

open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts
open Transfer SafeMath TransferOk TransferFee

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate}

/-- From 8648, the allowance step passes and the fee is above `v`: INVALID at `sub(v, fee)`. -/
theorem bodyFeeGtF (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    (hstatic : message.isStatic = false) (hacc : hasAccount state message.currentTarget)
    {v t f sel : U256} {M : ByteArray} (hM : M.size = 96)
    (hov : v.toNat * (storageAt state message.currentTarget 3).toNat < 2 ^ 256)
    (hgt : v.toNat < (feeOf state message v).toNat)
    (hallow : allowOf state message f = MAX_UINT ∨ v.toNat ≤ (allowOf state message f).toNat)
    {cA c3 c4 : Bool}
    (hcA : coldIn substate message.currentTarget (allowFrom message f) = cA)
    (hc3 : coldIn (accessSlot substate message.currentTarget (allowFrom message f))
      message.currentTarget 3 = c3)
    (hc4 : coldIn (accessSlot (accessSlot substate message.currentTarget (allowFrom message f))
      message.currentTarget 3) message.currentTarget 4 = c4)
    {gas : Nat}
    (hstip : 361 + slotCost cA + slotCost c3 + slotCost c4 + mulCost v +
      capCost (rawFee state message v) (storageAt state message.currentTarget 4) +
      allowCostF fork state message v f + 2300 ≤ gas) :
    Spec fork (At CODE message 8648 [0x60, 0, 0, 0, v, t, f, 0x1097, v, t, f, 0x0392, sel] M gas
        state substate)
      (Faulted (.invalidOpcode 0xfe) (allowedF state message v f)
        (allowedSubF fork substate state message v f)) := by
  have hacc3 : hasAccount (readsF state message f) message.currentTarget :=
    hasAccount_readSlot (hasAccount_readSlot (hasAccount_readSlot hacc))
  simp only [allowCostF, rawFee, feeOf, allowOf, allowedF, readsF, allowedSubF,
    accessF] at hstip hgt hallow ⊢
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
  step sendCall (by simp) (by gas_ok)
  exact subFault (by simp) hgt (by gas_ok)

/-- From 8648, `balances[_to]` (read after the write of `_from`) plus `v - fee` overflows:
INVALID at the `add`. -/
theorem bodyToOvF (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    (hstatic : message.isStatic = false) (hacc : hasAccount state message.currentTarget)
    {v t f sel : U256} {M : ByteArray} (hM : M.size = 96)
    (hov : v.toNat * (storageAt state message.currentTarget 3).toNat < 2 ^ 256)
    (hfv : (feeOf state message v).toNat ≤ v.toNat)
    (hallow : allowOf state message f = MAX_UINT ∨ v.toNat ≤ (allowOf state message f).toNat)
    (hbal : v.toNat ≤ (balFrom state message v f).toNat)
    (hto : 2 ^ 256 ≤ (balTo state message v t f).toNat + (sendOf state message v).toNat)
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
    (hstip : 766 + slotCost cA + slotCost c3 + slotCost c4 + slotCost cF + mulCost v +
      capCost (rawFee state message v) (storageAt state message.currentTarget 4) +
      allowCostF fork state message v f + debitCostF fork state message v f + 2300 ≤ gas)
    (hg : 943 + slotCost cA + slotCost c3 + slotCost c4 + slotCost cF + slotCost cT +
      mulCost v + capCost (rawFee state message v) (storageAt state message.currentTarget 4) +
      allowCostF fork state message v f + debitCostF fork state message v f ≤ gas) :
    Spec fork (At CODE message 8648 [0x60, 0, 0, 0, v, t, f, 0x1097, v, t, f, 0x0392, sel] M gas
        state substate)
      (Faulted (.invalidOpcode 0xfe)
        (readSlot (debitedF state message v f) message.currentTarget (recipientSlot t))
        (accessSlot (debitedSubF fork substate state message v f) message.currentTarget
          (recipientSlot t))) := by
  have hacc3 : hasAccount (readsF state message f) message.currentTarget :=
    hasAccount_readSlot (hasAccount_readSlot (hasAccount_readSlot hacc))
  have hacc4 : hasAccount (readSlot (allowedF state message v f) message.currentTarget
      (recipientSlot f)) message.currentTarget :=
    hasAccount_readSlot (hasAccount_allowState hacc3)
  have horig : ∀ m, originalAt (allowedF state message v f) message.currentTarget m =
      originalAt state message.currentTarget m := by
    intro m
    rw [originalAt_allowState hacc3]
    simp only [originalAt_readSlot]
  simp only [allowCostF, debitCostF, rawFee, feeOf, allowOf, balFrom, balTo, debitedF, allowedF,
    readsF, debitedSubF, allowedSubF, accessF, sendOf] at hstip hg hfv hbal hto hallow hcF hcT hacc4 horig ⊢
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
  exact addFault (by simp) hto (by gas_ok)

/-- From 8648, with a fee above 0 and the transfer to `_to` done, `balances[owner]` (read after
the write of `_to`) plus the fee overflows: INVALID at the owner's `add`. -/
theorem bodyOwnerOvF (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    (hstatic : message.isStatic = false) (hacc : hasAccount state message.currentTarget)
    {v t f sel : U256} {M : ByteArray} (hM : M.size = 96)
    (hov : v.toNat * (storageAt state message.currentTarget 3).toNat < 2 ^ 256)
    (hfee : feeOf state message v ≠ 0)
    (hfv : (feeOf state message v).toNat ≤ v.toNat)
    (hallow : allowOf state message f = MAX_UINT ∨ v.toNat ≤ (allowOf state message f).toNat)
    (hbal : v.toNat ≤ (balFrom state message v f).toNat)
    (hto : (balTo state message v t f).toNat + (sendOf state message v).toNat < 2 ^ 256)
    (hown : 2 ^ 256 ≤ (balOF state message v t f).toNat + (feeOf state message v).toNat)
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
    (hstip : 1099 + slotCost cA + slotCost c3 + slotCost c4 + slotCost cF + slotCost cT +
      mulCost v + capCost (rawFee state message v) (storageAt state message.currentTarget 4) +
      allowCostF fork state message v f + debitCostF fork state message v f +
      creditCostFeeF fork state message v t f + 2401 ≤ gas)
    (hg : 1099 + slotCost cA + slotCost c3 + slotCost c4 + slotCost cF + slotCost cT +
      mulCost v + capCost (rawFee state message v) (storageAt state message.currentTarget 4) +
      allowCostF fork state message v f + debitCostF fork state message v f +
      creditCostFeeF fork state message v t f + 313 + slotCost cO ≤ gas) :
    Spec fork (At CODE message 8648 [0x60, 0, 0, 0, v, t, f, 0x1097, v, t, f, 0x0392, sel] M gas
        state substate)
      (Faulted (.invalidOpcode 0xfe)
        (readSlot (readSlot (creditedFeeF state message v t f) message.currentTarget 0)
          message.currentTarget (ownerSlot (ownerWordF state message v t f)))
        (accessSlot (accessSlot (creditedSubFeeF fork substate state message v t f)
          message.currentTarget 0) message.currentTarget
          (ownerSlot (ownerWordF state message v t f)))) := by
  have hw : coldIn (creditedSubFeeF fork substate state message v t f) message.currentTarget 0 =
      false :=
    coldIn_storeSub_false (coldIn_accessSlot_false (coldIn_storeSub_false
      (coldIn_accessSlot_false (coldIn_allowSub_false (coldIn_accessSlot_false
        (coldIn_accessSlot_false (coldIn_accessSlot_false hc0)))))))
  have hMa : (allowMem message M f).size = 96 := size_allowMem hM f
  have hMb := size_allowMem2 (message := message) hMa (allowOf state message f) f
  have hA := headF (sel := sel) hfork hglam hstatic hacc hM hov hfee hfv hallow hbal hto hcA hc3
    hc4 hcF hcT (gas := gas) hstip
  refine Triple.seq hA ?_
  have hO := ownerCallF (message := message) (state := creditedFeeF state message v t f)
    (substate := creditedSubFeeF fork substate state message v t f) (cO := cO) hfork rfl
    (send := sendOf state message v) (fee := feeOf state message v)
    (A := allowOf state message f) (v := v) (t := t) (f := f)
    (rest := [0x1097, v, t, f, 0x0392, sel]) (by simp) hw
    (by rw [coldIn_accessSlot_of_warm hw]; exact hcO)
    (gas := gas - (1099 + slotCost cA + slotCost c3 + slotCost c4 + slotCost cF + slotCost cT +
      mulCost v + capCost (rawFee state message v) (storageAt state message.currentTarget 4) +
      allowCostF fork state message v f + debitCostF fork state message v f +
      creditCostFeeF fork state message v t f))
    (Nat.le_sub_of_add_le (by omega)) (M := memAF message M (allowOf state message f) f t)
    (size_mapMem (size_mapMem (size_mapMem (size_mapMem hMb _ _) _ _) _ _) _ _)
  refine Triple.seq hO ?_
  exact addFault (by simp) hown (by omega)

/-- The specification of `transferFrom(f, t, v)` when the fee is above `v`.

Hypotheses: Berlin ≤ fork < Glamsterdam, not static, the contract has an account; the checks pass
(call data ≥ 100 bytes, not paused, `f` not blacklisted, not deprecated); `v * rate < 2^256`;
`A = MAX_UINT ∨ v ≤ A`; `v < fee`; more than 2300 gas left at the allowance's SSTORE, which also
covers the rest of the path.

Then INVALID at `sub(v, fee)`, after the allowance step (`A - v` written unless `A = MAX_UINT`). -/
theorem spec_feeGtF (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    (hstatic : message.isStatic = false) (hacc : hasAccount state message.currentTarget)
    (hlong : 100 ≤ message.data.size) (hsz : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x23b872dd) (hv : message.value = 0)
    (hnp : byte20 (storageAt state message.currentTarget 0) = 0)
    (hnb : (storageAt state message.currentTarget (blackFrom (fromArg message))).toNat % 256 = 0)
    (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    (hov : (valArg message).toNat *
      (storageAt (checkState state message) message.currentTarget 3).toNat < 2 ^ 256)
    (hallow : allowOf (checkState state message) message (fromArg message) = MAX_UINT ∨
      (valArg message).toNat ≤ (allowOf (checkState state message) message (fromArg message)).toNat)
    (hgt : (valArg message).toNat < (feeOf (checkState state message) message (valArg message)).toNat)
    {c0 cB c10 cA c3 c4 : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
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
    {gas : Nat} (hg : preCostF c0 cB c10 + (361 + slotCost cA + slotCost c3 + slotCost c4 +
      mulCost (valArg message) +
      capCost (rawFee (checkState state message) message (valArg message))
        (storageAt (checkState state message) message.currentTarget 4) +
      allowCostF fork (checkState state message) message (valArg message) (fromArg message) + 2300) ≤ gas) :
    Spec fork (At CODE message 0 [] .empty gas state substate)
      (Faulted (.invalidOpcode 0xfe) (allowedF (checkState state message) message (valArg message) (fromArg message))
        (allowedSubF fork (checkSub substate message) (checkState state message) message (valArg message)
          (fromArg message))) :=
  Triple.seq (preF hfork hlong hsz hsel hv hnp hnb hdep hc0 hcB hc10
      (Nat.le_trans (Nat.le_add_right _ _) hg))
    (bodyFeeGtF hfork hglam hstatic (hasAccount_readSlot (hasAccount_readSlot (hasAccount_readSlot hacc)))
      (size_mapMem size_MEM0 _ _) hov hgt hallow hcA hc3 hc4
      (Nat.le_sub_of_add_le (by rw [Nat.add_comm]; exact hg)))

/-- The specification of `transferFrom(f, t, v)` when `balances[t] + (v - fee)` overflows.

Hypotheses: as `spec_feeGtF` up to the allowance; `fee ≤ v`; `v ≤ balances[f]` (read after the
allowance step); `balances[t] + (v - fee) ≥ 2^256` (read after the write of `f`); more than 2300
gas left at the SSTORE of `balances[f]` (`hstip`), and enough gas to reach the assert.

Then INVALID at the `add`, after the allowance step and the write `balances[f] := balF - v`. -/
theorem spec_toOvF (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    (hstatic : message.isStatic = false) (hacc : hasAccount state message.currentTarget)
    (hlong : 100 ≤ message.data.size) (hsz : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x23b872dd) (hv : message.value = 0)
    (hnp : byte20 (storageAt state message.currentTarget 0) = 0)
    (hnb : (storageAt state message.currentTarget (blackFrom (fromArg message))).toNat % 256 = 0)
    (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    (hov : (valArg message).toNat *
      (storageAt (checkState state message) message.currentTarget 3).toNat < 2 ^ 256)
    (hallow : allowOf (checkState state message) message (fromArg message) = MAX_UINT ∨
      (valArg message).toNat ≤ (allowOf (checkState state message) message (fromArg message)).toNat)
    (hfv : (feeOf (checkState state message) message (valArg message)).toNat ≤ (valArg message).toNat)
    (hbal : (valArg message).toNat ≤
      (balFrom (checkState state message) message (valArg message) (fromArg message)).toNat)
    (hto : 2 ^ 256 ≤ (balTo (checkState state message) message (valArg message) (toArg message)
      (fromArg message)).toNat + (sendOf (checkState state message) message (valArg message)).toNat)
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
    {gas : Nat} (hstip : preCostF c0 cB c10 + (766 + slotCost cA + slotCost c3 + slotCost c4 + slotCost cF +
      mulCost (valArg message) +
      capCost (rawFee (checkState state message) message (valArg message))
        (storageAt (checkState state message) message.currentTarget 4) +
      allowCostF fork (checkState state message) message (valArg message) (fromArg message) +
      debitCostF fork (checkState state message) message (valArg message) (fromArg message) + 2300) ≤ gas)
    (hg : preCostF c0 cB c10 + (943 + slotCost cA + slotCost c3 + slotCost c4 + slotCost cF + slotCost cT +
      mulCost (valArg message) +
      capCost (rawFee (checkState state message) message (valArg message))
        (storageAt (checkState state message) message.currentTarget 4) +
      allowCostF fork (checkState state message) message (valArg message) (fromArg message) +
      debitCostF fork (checkState state message) message (valArg message) (fromArg message)) ≤ gas) :
    Spec fork (At CODE message 0 [] .empty gas state substate)
      (Faulted (.invalidOpcode 0xfe)
        (readSlot (debitedF (checkState state message) message (valArg message) (fromArg message))
          message.currentTarget (recipientSlot (toArg message)))
        (accessSlot (debitedSubF fork (checkSub substate message) (checkState state message) message
          (valArg message) (fromArg message)) message.currentTarget (recipientSlot (toArg message)))) :=
  Triple.seq (preF hfork hlong hsz hsel hv hnp hnb hdep hc0 hcB hc10
      (Nat.le_trans (Nat.le_add_right _ _) hg))
    (bodyToOvF hfork hglam hstatic (hasAccount_readSlot (hasAccount_readSlot (hasAccount_readSlot hacc)))
      (size_mapMem size_MEM0 _ _) hov hfv hallow hbal hto hcA hc3 hc4 hcF hcT
      (Nat.le_sub_of_add_le (by rw [Nat.add_comm]; exact hstip))
      (Nat.le_sub_of_add_le (by rw [Nat.add_comm]; exact hg)))

/-- The specification of `transferFrom(f, t, v)` with a fee above 0 when `balances[owner] + fee`
overflows.

Hypotheses: as `spec_feeF` up to `t` (`0 < fee ≤ v`, the allowance step, `v ≤ balances[f]`,
`balances[t] + (v - fee) < 2^256`); `balances[owner] + fee ≥ 2^256` (owner = low 160 bits of slot
0, both read after the write of `t`); more than 2300 gas left at the SSTORE of `balances[t]`
(`hstip`), and enough gas to reach the assert.

Then INVALID at the owner's `add`, after the writes of the allowance (unless `MAX_UINT`),
`balances[f]` and `balances[t]`, and the reads of slot 0 and the owner's slot. -/
theorem spec_ownerOvF (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    (hstatic : message.isStatic = false) (hacc : hasAccount state message.currentTarget)
    (hlong : 100 ≤ message.data.size) (hsz : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x23b872dd) (hv : message.value = 0)
    (hnp : byte20 (storageAt state message.currentTarget 0) = 0)
    (hnb : (storageAt state message.currentTarget (blackFrom (fromArg message))).toNat % 256 = 0)
    (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    (hov : (valArg message).toNat *
      (storageAt (checkState state message) message.currentTarget 3).toNat < 2 ^ 256)
    (hallow : allowOf (checkState state message) message (fromArg message) = MAX_UINT ∨
      (valArg message).toNat ≤ (allowOf (checkState state message) message (fromArg message)).toNat)
    (hfee : feeOf (checkState state message) message (valArg message) ≠ 0)
    (hfv : (feeOf (checkState state message) message (valArg message)).toNat ≤ (valArg message).toNat)
    (hbal : (valArg message).toNat ≤
      (balFrom (checkState state message) message (valArg message) (fromArg message)).toNat)
    (hto : (balTo (checkState state message) message (valArg message) (toArg message)
      (fromArg message)).toNat + (sendOf (checkState state message) message (valArg message)).toNat < 2 ^ 256)
    (hown : 2 ^ 256 ≤ (balOF (checkState state message) message (valArg message) (toArg message)
      (fromArg message)).toNat + (feeOf (checkState state message) message (valArg message)).toNat)
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
    {gas : Nat} (hstip : preCostF c0 cB c10 + (1099 + slotCost cA + slotCost c3 + slotCost c4 + slotCost cF + slotCost cT +
      mulCost (valArg message) +
      capCost (rawFee (checkState state message) message (valArg message))
        (storageAt (checkState state message) message.currentTarget 4) +
      allowCostF fork (checkState state message) message (valArg message) (fromArg message) +
      debitCostF fork (checkState state message) message (valArg message) (fromArg message) +
      creditCostFeeF fork (checkState state message) message (valArg message) (toArg message)
        (fromArg message) + 2401) ≤ gas)
    (hg : preCostF c0 cB c10 + (1099 + slotCost cA + slotCost c3 + slotCost c4 + slotCost cF + slotCost cT +
      mulCost (valArg message) +
      capCost (rawFee (checkState state message) message (valArg message))
        (storageAt (checkState state message) message.currentTarget 4) +
      allowCostF fork (checkState state message) message (valArg message) (fromArg message) +
      debitCostF fork (checkState state message) message (valArg message) (fromArg message) +
      creditCostFeeF fork (checkState state message) message (valArg message) (toArg message)
        (fromArg message) + 313 + slotCost cO) ≤ gas) :
    Spec fork (At CODE message 0 [] .empty gas state substate)
      (Faulted (.invalidOpcode 0xfe)
        (readSlot (readSlot (creditedFeeF (checkState state message) message (valArg message) (toArg message)
          (fromArg message)) message.currentTarget 0) message.currentTarget
          (ownerSlot (ownerWordF (checkState state message) message (valArg message) (toArg message)
            (fromArg message))))
        (accessSlot (accessSlot (creditedSubFeeF fork (checkSub substate message)
          (checkState state message) message (valArg message) (toArg message) (fromArg message))
          message.currentTarget 0) message.currentTarget
          (ownerSlot (ownerWordF (checkState state message) message (valArg message) (toArg message)
            (fromArg message))))) :=
  Triple.seq (preF hfork hlong hsz hsel hv hnp hnb hdep hc0 hcB hc10
      (Nat.le_trans (Nat.le_add_right _ _) hg))
    (bodyOwnerOvF hfork hglam hstatic (hasAccount_readSlot (hasAccount_readSlot (hasAccount_readSlot hacc)))
      (size_mapMem size_MEM0 _ _) hov hfee hfv hallow hbal hto hown
      (coldIn_accessSlot_false (coldIn_accessSlot_false (coldIn_accessSlot_self _ _ _)))
      hcA hc3 hc4 hcF hcT hcO
      (Nat.le_sub_of_add_le (by rw [Nat.add_comm]; exact hstip))
      (Nat.le_sub_of_add_le (by rw [Nat.add_comm]; exact hg)))

/-- The loop of the interpreter runs the case of `spec_feeGtF` to its end condition. It holds for
every bound on the gas of messages and every runner of messages. -/
theorem runFrame_feeGtF (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    (hstatic : message.isStatic = false) (hacc : hasAccount state message.currentTarget)
    (hlong : 100 ≤ message.data.size) (hsz : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x23b872dd) (hv : message.value = 0)
    (hnp : byte20 (storageAt state message.currentTarget 0) = 0)
    (hnb : (storageAt state message.currentTarget (blackFrom (fromArg message))).toNat % 256 = 0)
    (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    (hov : (valArg message).toNat *
      (storageAt (checkState state message) message.currentTarget 3).toNat < 2 ^ 256)
    (hallow : allowOf (checkState state message) message (fromArg message) = MAX_UINT ∨
      (valArg message).toNat ≤ (allowOf (checkState state message) message (fromArg message)).toNat)
    (hgt : (valArg message).toNat < (feeOf (checkState state message) message (valArg message)).toNat)
    {c0 cB c10 cA c3 c4 : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
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
    {gas : Nat} (hg : preCostF c0 cB c10 + (361 + slotCost cA + slotCost c3 + slotCost c4 +
      mulCost (valArg message) +
      capCost (rawFee (checkState state message) message (valArg message))
        (storageAt (checkState state message) message.currentTarget 4) +
      allowCostF fork (checkState state message) message (valArg message) (fromArg message) + 2300) ≤ gas)
    {bound : Nat} {runChild : MessageRunner fork Nat bound} {evm : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    ∃ stopped, runFrame (step fork) (step_decreases fork) bound runChild evm within =
      .ok stopped ∧
      Faulted (.invalidOpcode 0xfe) (allowedF (checkState state message) message (valArg message) (fromArg message))
          (allowedSubF fork (checkSub substate message) (checkState state message) message (valArg message)
            (fromArg message)) stopped :=
  (spec_feeGtF hfork hglam hstatic hacc hlong hsz hsel hv hnp hnb hdep hov hallow hgt hc0 hcB hc10
    hcA hc3 hc4 hg).runFrame start within

/-- The loop of the interpreter runs the case of `spec_toOvF` to its end condition. It holds for
every bound on the gas of messages and every runner of messages. -/
theorem runFrame_toOvF (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    (hstatic : message.isStatic = false) (hacc : hasAccount state message.currentTarget)
    (hlong : 100 ≤ message.data.size) (hsz : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x23b872dd) (hv : message.value = 0)
    (hnp : byte20 (storageAt state message.currentTarget 0) = 0)
    (hnb : (storageAt state message.currentTarget (blackFrom (fromArg message))).toNat % 256 = 0)
    (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    (hov : (valArg message).toNat *
      (storageAt (checkState state message) message.currentTarget 3).toNat < 2 ^ 256)
    (hallow : allowOf (checkState state message) message (fromArg message) = MAX_UINT ∨
      (valArg message).toNat ≤ (allowOf (checkState state message) message (fromArg message)).toNat)
    (hfv : (feeOf (checkState state message) message (valArg message)).toNat ≤ (valArg message).toNat)
    (hbal : (valArg message).toNat ≤
      (balFrom (checkState state message) message (valArg message) (fromArg message)).toNat)
    (hto : 2 ^ 256 ≤ (balTo (checkState state message) message (valArg message) (toArg message)
      (fromArg message)).toNat + (sendOf (checkState state message) message (valArg message)).toNat)
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
    {gas : Nat} (hstip : preCostF c0 cB c10 + (766 + slotCost cA + slotCost c3 + slotCost c4 + slotCost cF +
      mulCost (valArg message) +
      capCost (rawFee (checkState state message) message (valArg message))
        (storageAt (checkState state message) message.currentTarget 4) +
      allowCostF fork (checkState state message) message (valArg message) (fromArg message) +
      debitCostF fork (checkState state message) message (valArg message) (fromArg message) + 2300) ≤ gas)
    (hg : preCostF c0 cB c10 + (943 + slotCost cA + slotCost c3 + slotCost c4 + slotCost cF + slotCost cT +
      mulCost (valArg message) +
      capCost (rawFee (checkState state message) message (valArg message))
        (storageAt (checkState state message) message.currentTarget 4) +
      allowCostF fork (checkState state message) message (valArg message) (fromArg message) +
      debitCostF fork (checkState state message) message (valArg message) (fromArg message)) ≤ gas)
    {bound : Nat} {runChild : MessageRunner fork Nat bound} {evm : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    ∃ stopped, runFrame (step fork) (step_decreases fork) bound runChild evm within =
      .ok stopped ∧
      Faulted (.invalidOpcode 0xfe)
          (readSlot (debitedF (checkState state message) message (valArg message) (fromArg message))
            message.currentTarget (recipientSlot (toArg message)))
          (accessSlot (debitedSubF fork (checkSub substate message) (checkState state message) message
            (valArg message) (fromArg message)) message.currentTarget (recipientSlot (toArg message)))
            stopped :=
  (spec_toOvF hfork hglam hstatic hacc hlong hsz hsel hv hnp hnb hdep hov hallow hfv hbal hto hc0
    hcB hc10 hcA hc3 hc4 hcF hcT hstip hg).runFrame start within

/-- The loop of the interpreter runs the case of `spec_ownerOvF` to its end condition. It holds for
every bound on the gas of messages and every runner of messages. -/
theorem runFrame_ownerOvF (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    (hstatic : message.isStatic = false) (hacc : hasAccount state message.currentTarget)
    (hlong : 100 ≤ message.data.size) (hsz : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x23b872dd) (hv : message.value = 0)
    (hnp : byte20 (storageAt state message.currentTarget 0) = 0)
    (hnb : (storageAt state message.currentTarget (blackFrom (fromArg message))).toNat % 256 = 0)
    (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    (hov : (valArg message).toNat *
      (storageAt (checkState state message) message.currentTarget 3).toNat < 2 ^ 256)
    (hallow : allowOf (checkState state message) message (fromArg message) = MAX_UINT ∨
      (valArg message).toNat ≤ (allowOf (checkState state message) message (fromArg message)).toNat)
    (hfee : feeOf (checkState state message) message (valArg message) ≠ 0)
    (hfv : (feeOf (checkState state message) message (valArg message)).toNat ≤ (valArg message).toNat)
    (hbal : (valArg message).toNat ≤
      (balFrom (checkState state message) message (valArg message) (fromArg message)).toNat)
    (hto : (balTo (checkState state message) message (valArg message) (toArg message)
      (fromArg message)).toNat + (sendOf (checkState state message) message (valArg message)).toNat < 2 ^ 256)
    (hown : 2 ^ 256 ≤ (balOF (checkState state message) message (valArg message) (toArg message)
      (fromArg message)).toNat + (feeOf (checkState state message) message (valArg message)).toNat)
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
    {gas : Nat} (hstip : preCostF c0 cB c10 + (1099 + slotCost cA + slotCost c3 + slotCost c4 + slotCost cF + slotCost cT +
      mulCost (valArg message) +
      capCost (rawFee (checkState state message) message (valArg message))
        (storageAt (checkState state message) message.currentTarget 4) +
      allowCostF fork (checkState state message) message (valArg message) (fromArg message) +
      debitCostF fork (checkState state message) message (valArg message) (fromArg message) +
      creditCostFeeF fork (checkState state message) message (valArg message) (toArg message)
        (fromArg message) + 2401) ≤ gas)
    (hg : preCostF c0 cB c10 + (1099 + slotCost cA + slotCost c3 + slotCost c4 + slotCost cF + slotCost cT +
      mulCost (valArg message) +
      capCost (rawFee (checkState state message) message (valArg message))
        (storageAt (checkState state message) message.currentTarget 4) +
      allowCostF fork (checkState state message) message (valArg message) (fromArg message) +
      debitCostF fork (checkState state message) message (valArg message) (fromArg message) +
      creditCostFeeF fork (checkState state message) message (valArg message) (toArg message)
        (fromArg message) + 313 + slotCost cO) ≤ gas)
    {bound : Nat} {runChild : MessageRunner fork Nat bound} {evm : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    ∃ stopped, runFrame (step fork) (step_decreases fork) bound runChild evm within =
      .ok stopped ∧
      Faulted (.invalidOpcode 0xfe)
          (readSlot (readSlot (creditedFeeF (checkState state message) message (valArg message) (toArg message)
            (fromArg message)) message.currentTarget 0) message.currentTarget
            (ownerSlot (ownerWordF (checkState state message) message (valArg message) (toArg message)
              (fromArg message))))
          (accessSlot (accessSlot (creditedSubFeeF fork (checkSub substate message)
            (checkState state message) message (valArg message) (toArg message) (fromArg message))
            message.currentTarget 0) message.currentTarget
            (ownerSlot (ownerWordF (checkState state message) message (valArg message) (toArg message)
              (fromArg message)))) stopped :=
  (spec_ownerOvF hfork hglam hstatic hacc hlong hsz hsel hv hnp hnb hdep hov hallow hfee hfv hbal
    hto hown hc0 hcB hc10 hcA hc3 hc4 hcF hcT hcO hstip hg).runFrame start within

end UsdtVerify.TransferFrom
