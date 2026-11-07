import UsdtVerify.Functions.TransferFromSpec
import UsdtVerify.Functions.TransferFaults

/-!
# transferFrom(address,address,uint256): the reverts and the failed SafeMath asserts

From pc 0, with the selector 0x23b872dd and no value:

- `spec_paused`: byte 20 of slot 0 set: REVERT at 3797.
- `spec_blacklisted`: not paused, the low byte of `isBlackListed[_from]` set: REVERT at 3886.
- `spec_short`: not paused, `_from` not blacklisted, not deprecated, fewer than 100 bytes of call
  data: StandardToken's payload check reverts at 8644.
- `spec_allowLow`: the checks pass and `allowed[_from][msg.sender] < v`: INVALID at the
  `sub(_allowance, v)` (the allowance is then not `MAX_UINT`, since `v < 2^256`).
- `spec_balLow`: the allowance step passes and `balances[_from] < v`: INVALID at the `sub` of the
  debit (any fee `≤ v`).
- `spec_mulOv`: `v * basisPointsRate` overflows: INVALID in `mul`.

`preF0` / `preF` are the common prefixes from pc 0 to 8619 and to 8648.
-/

namespace UsdtVerify.TransferFrom

open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts
open Transfer SafeMath TransferOk

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate}

/-- At 3773, when byte 20 of slot 0 is set, the code reverts with no output. -/
theorem pausedRevert (hfork : .berlin ≤ fork) {rest : List U256} (hrest : rest.length ≤ 16)
    {c0 : Bool} (hpaused : byte20 (storageAt state message.currentTarget 0) ≠ 0)
    (hc0 : coldIn substate message.currentTarget 0 = c0) {gas : Nat}
    (hg : 118 + slotCost c0 ≤ gas) :
    Spec fork (At CODE message 3773 rest MEM0 gas state substate)
      (Halted true .empty (gas - (118 + slotCost c0)) (readSlot state message.currentTarget 0)
        (accessSlot substate message.currentTarget 0)) := by
  have hexp : exponentBytes (0x14 : U256) = 1 := by decide
  step jumpdestR
  step pushR 1 (0 : U256)
  step pushR 1 (0x14 : U256)
  step swapR 0
  norm
  step sload hfork (cold := c0) (by code_fact) (by code_fact) hc0 (by gas_ok)
  step swapR 0
  norm
  step pushR 2 (0x0100 : U256)
  step Local.exp (Nat.le_trans (by decide) hfork) (by code_fact) (by code_fact) (by gas_ok)
  step swapR 0
  norm
  step binR 0x04 Local.instruction_div
  step pushR 1 (0xff : U256)
  step binR 0x16 Local.instruction_and
  step unR 0x15 instruction_iszero
  step unR 0x15 instruction_iszero
  step unR 0x15 instruction_iszero
  step pushR 2 (0x0ed9 : U256)
  step jumpi0R (isZero3_flag hpaused)
  step pushR 1 (0 : U256)
  step dupR 0
  have hz : extendMemory MEM0.size [((0 : U256), (0 : U256))] = ⟨0, 0⟩ := by
    rw [size_MEM0]; decide
  refine (Logic.revert (Nat.le_trans (by decide) hfork) (by code_fact) (by code_fact)
    (by rw [hz]; gas_ok)).consequence (fun _ h => h) ?_
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  refine ⟨hr, he, ?_, ?_, hs, hss⟩
  · rw [ho]; simp [memoryReadBytes]
  · rw [hgas, hz]; gas_ok

/-- At 3801, when the low byte of `isBlackListed[_from]` is set, the code reverts. -/
theorem blackRevert (hfork : .berlin ≤ fork) {v t f : U256} {rest : List U256}
    (hrest : rest.length ≤ 16) {cB : Bool}
    (hcB : coldIn substate message.currentTarget (blackFrom f) = cB)
    (hblack : (storageAt state message.currentTarget (blackFrom f)).toNat % 256 ≠ 0) {gas : Nat}
    (hg : 158 + slotCost cB ≤ gas) {M : ByteArray} (hM : M.size = 96) :
    Spec fork (At CODE message 3801 (v :: t :: f :: rest) M gas state substate)
      (Halted true .empty (gas - (158 + slotCost cB))
        (readSlot state message.currentTarget (blackFrom f))
        (accessSlot substate message.currentTarget (blackFrom f))) := by
  have hexp : exponentBytes (0 : U256) = 0 := by decide
  have hz : extendMemory (mapMem M (mkey f) 6).size [((0 : U256), (0 : U256))] = ⟨0, 0⟩ := by
    rw [size_mapMem hM]; decide
  simp only [blackFrom, mkey] at hcB hblack hz ⊢
  step jumpdestR
  step pushR 1 (0x06 : U256)
  step pushR 1 (0 : U256)
  step dupR 4
  at_pc 3807
  step hashTail (by decide) (by simp; omega) hM (by gas_ok)
  at_pc 3865
  step pushR 1 (0 : U256)
  step swapR 0
  norm
  step sload hfork (cold := cB) (by code_fact) (by code_fact) hcB (by gas_ok)
  step swapR 0
  norm
  step pushR 2 (0x0100 : U256)
  step Local.exp (Nat.le_trans (by decide) hfork) (by code_fact) (by code_fact) (by gas_ok)
  step swapR 0
  norm
  step binR 0x04 Local.instruction_div
  step pushR 1 (0xff : U256)
  step binR 0x16 Local.instruction_and
  step unR 0x15 instruction_iszero
  step unR 0x15 instruction_iszero
  step unR 0x15 instruction_iszero
  step pushR 2 (0x0f32 : U256)
  step jumpi0R (isZero3_byte0 hblack)
  step pushR 1 (0 : U256)
  step dupR 0
  refine (Logic.revert (Nat.le_trans (by decide) hfork) (by code_fact) (by code_fact)
    (by rw [hz]; gas_ok)).consequence (fun _ h => h) ?_
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  refine ⟨hr, he, ?_, ?_, hs, hss⟩
  · rw [ho]; simp [memoryReadBytes]
  · rw [hgas, hz]; gas_ok

/-- At 8619, call data of fewer than 100 bytes (three argument words) makes the code revert. -/
theorem shortRevert (hfork : .berlin ≤ fork) {rest : List U256} (hrest : rest.length ≤ 16)
    (hshort : message.data.size < 100) {gas : Nat} (hg : 63 ≤ gas) {M : ByteArray}
    (hM : M.size = 96) :
    Spec fork (At CODE message 8619 rest M gas state substate)
      (Halted true .empty (gas - 63) state substate) := by
  have hz : extendMemory M.size [((0 : U256), (0 : U256))] = ⟨0, 0⟩ := by rw [hM]; decide
  step jumpdestR
  step pushR 1 (0 : U256)
  step dupR 0
  step pushR 1 (0 : U256)
  step pushR 1 (0x60 : U256)
  step pushR 1 (0x04 : U256)
  step dupR 1
  step binR 0x01 instruction_add
  step pushR 1 (0 : U256)
  step Logic.calldatasize (by code_fact) (by code_fact) (by gas_ok) (by stk_ok)
  step swapR 0
  norm
  step popR
  step binR 0x10 Local.instruction_lt
  step unR 0x15 instruction_iszero
  step unR 0x15 instruction_iszero
  step unR 0x15 instruction_iszero
  step pushR 2 (0x21c8 : U256)
  refine Triple.seq (Logic.jumpi_of_eq_zero (by code_fact) (by code_fact) (by gas_ok) ?_) ?_
  · have h100 : (add (0x60 : U256) (0x04 : U256)).toNat = 100 := by decide
    have hlt : lessThan (BitVec.ofNat 256 message.data.size) (add (0x60 : U256) (0x04 : U256)) =
        1 := by
      simp only [lessThan, h100, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (show message.data.size < 2 ^ 256 by omega)]
      rw [if_pos hshort]
    rw [hlt]
    decide
  step pushR 1 (0 : U256)
  step dupR 0
  refine (Logic.revert (Nat.le_trans (by decide) hfork) (by code_fact) (by code_fact)
    (by rw [hz]; gas_ok)).consequence (fun _ h => h) ?_
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  refine ⟨hr, he, ?_, ?_, hs, hss⟩
  · rw [ho]; simp [memoryReadBytes]
  · rw [hgas, hz]; gas_ok

/-- At 8834, `_allowance = A < v`: the allowance is below `MAX_UINT`, and the code's
`sub(A, v)` fails its assert (INVALID at 10989). -/
theorem allowFault {fee A v t f : U256} {rest : List U256} (hrest : rest.length ≤ 8)
    (hlt : A.toNat < v.toNat) {gas : Nat} (hg : 96 ≤ gas) {M : ByteArray} :
    Spec fork (At CODE message 8834 (0x60 :: 0 :: fee :: A :: v :: t :: f :: rest) M gas state
        substate)
      (Faulted (.invalidOpcode 0xfe) state substate) := by
  have hmax : A.toNat < 2 ^ 256 - 1 := by
    have := v.isLt
    omega
  step jumpdestR
  step pushR 32 MAX_UINT
  step dupR 4
  step binR 0x10 Local.instruction_lt
  step unR 0x15 instruction_iszero
  step pushR 2 (0x233e : U256)
  step jumpi0R (by simp [lessThan, isZero]; omega)
  step pushR 2 (0x22bd : U256)
  step dupR 5
  step dupR 5
  step pushR 2 (0x2ae0 : U256)
  step swapR 0
  norm
  step swapR 1
  norm
  step swapR 0
  norm
  step pushR 4 (0xffffffff : U256)
  step binR 0x16 Local.instruction_and
  step jumpR
  exact subFault (by simp; omega) hlt (by gas_ok)

/-- The stack at 8619 for `transferFrom(f, t, v)`. -/
abbrev stdStack (message : Message fork) : List U256 :=
  [valArg message, toArg message, fromArg message, 0x1097, valArg message, toArg message,
    fromArg message, 0x0392, BitVec.ofNat 256 (selector message.data)]

/-- The memory after the blacklist lookup of `_from`. -/
abbrev memF (message : Message fork) : ByteArray := mapMem MEM0 (mkey (fromArg message)) 6

/-- From pc 0, a `transferFrom` call that passes the checks (no value, not paused, `_from` not
blacklisted, not deprecated) reaches StandardToken's `transferFrom` at 8619. -/
theorem preF0 (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsz : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x23b872dd) (hv : message.value = 0)
    (hnp : byte20 (storageAt state message.currentTarget 0) = 0)
    (hnb : (storageAt state message.currentTarget (blackFrom (fromArg message))).toNat % 256 = 0)
    (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    {c0 cB c10 : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hcB : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget
      (blackFrom (fromArg message)) = cB)
    (hc10 : coldIn (accessSlot (accessSlot substate message.currentTarget 0) message.currentTarget
      (blackFrom (fromArg message))) message.currentTarget 10 = c10)
    {gas : Nat} (hg : 738 + slotCost c0 + slotCost cB + slotCost c10 ≤ gas) :
    Hoare fork (At CODE message 0 [] .empty gas state substate)
      (At CODE message 8619 (stdStack message) (memF message)
        (gas - (738 + slotCost c0 + slotCost cB + slotCost c10))
        (checkState state message) (checkSub substate message)) := by
  have ht : tested (BitVec.ofNat 256 (selector message.data)) ENTRIES = 7 := by
    rw [hsel]; decide
  have hb : branch (BitVec.ofNat 256 (selector message.data)) 54 (entrySize 4 2) ENTRIES =
      819 := by
    rw [hsel]; decide
  have h1 := dispatch (state := state) (substate := substate) hsize hsz (gas := gas)
    (by rw [ht]; gas_ok)
  rw [ht, hb] at h1
  refine Triple.seq h1 ?_
  step entry hv (by gas_ok)
  step notPaused hfork (by simp) hnp hc0 (by gas_ok)
  step notBlack hfork (by simp) hcB (by rw [storageAt_readSlot]; exact hnb) (by gas_ok) size_MEM0
  step notDeprecated hfork (by simp) (by rw [storageAt_readSlot, storageAt_readSlot]; exact hdep)
    hc10 (by gas_ok)
  step toStandard (by gas_ok)
  exact reshape rfl rfl (by gas_ok)

/-- From pc 0, with at least 100 bytes of call data, to 8648 (after the payload check). -/
theorem preF (hfork : .berlin ≤ fork) (hlong : 100 ≤ message.data.size)
    (hsz : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x23b872dd) (hv : message.value = 0)
    (hnp : byte20 (storageAt state message.currentTarget 0) = 0)
    (hnb : (storageAt state message.currentTarget (blackFrom (fromArg message))).toNat % 256 = 0)
    (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    {c0 cB c10 : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hcB : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget
      (blackFrom (fromArg message)) = cB)
    (hc10 : coldIn (accessSlot (accessSlot substate message.currentTarget 0) message.currentTarget
      (blackFrom (fromArg message))) message.currentTarget 10 = c10)
    {gas : Nat} (hg : PRE_COST_F + slotCost c0 + slotCost cB + slotCost c10 ≤ gas) :
    Hoare fork (At CODE message 0 [] .empty gas state substate)
      (At CODE message 8648 ((0x60 : U256) :: 0 :: 0 :: 0 :: stdStack message) (memF message)
        (gas - (PRE_COST_F + slotCost c0 + slotCost cB + slotCost c10))
        (checkState state message) (checkSub substate message)) := by
  simp only [PRE_COST_F] at hg ⊢
  refine Triple.seq (preF0 hfork (by omega) hsz hsel hv hnp hnb hdep hc0 hcB hc10
    (Nat.le_trans (by omega) hg)) ?_
  step payload hlong hsz (by simp) (by gas_ok)
  exact reshape rfl rfl (by gas_ok)

/-- From 8648, `_allowance = A < v`: INVALID at the allowance's `sub`, after the reads of the
allowance, slot 3 and slot 4 (fee computed first). -/
theorem bodyAllowLow (hfork : .berlin ≤ fork) {v t f sel : U256} {M : ByteArray}
    (hM : M.size = 96)
    (hov : v.toNat * (storageAt state message.currentTarget 3).toNat < 2 ^ 256)
    (hlt : (allowOf state message f).toNat < v.toNat)
    {cA c3 c4 : Bool}
    (hcA : coldIn substate message.currentTarget (allowFrom message f) = cA)
    (hc3 : coldIn (accessSlot substate message.currentTarget (allowFrom message f))
      message.currentTarget 3 = c3)
    (hc4 : coldIn (accessSlot (accessSlot substate message.currentTarget (allowFrom message f))
      message.currentTarget 3) message.currentTarget 4 = c4)
    {gas : Nat}
    (hg : 457 + slotCost cA + slotCost c3 + slotCost c4 + mulCost v +
      capCost (rawFee state message v) (storageAt state message.currentTarget 4) ≤ gas) :
    Spec fork (At CODE message 8648 [0x60, 0, 0, 0, v, t, f, 0x1097, v, t, f, 0x0392, sel] M gas
        state substate)
      (Faulted (.invalidOpcode 0xfe) (readsF state message f) (accessF substate message f)) := by
  simp only [rawFee, allowOf, readsF, accessF] at hg hlt ⊢
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
  exact allowFault (by simp) hlt (by gas_ok)

/-- From 8648, the allowance step passes (`A = MAX_UINT` or `v ≤ A`), the fee is at most `v`, and
`balances[_from]` (read after the allowance step) is below `v`: INVALID at the debit's `sub`. -/
theorem bodyBalLow (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    (hstatic : message.isStatic = false) (hacc : hasAccount state message.currentTarget)
    {v t f sel : U256} {M : ByteArray} (hM : M.size = 96)
    (hov : v.toNat * (storageAt state message.currentTarget 3).toNat < 2 ^ 256)
    (hfv : (feeOf state message v).toNat ≤ v.toNat)
    (hallow : allowOf state message f = MAX_UINT ∨ v.toNat ≤ (allowOf state message f).toNat)
    (hlow : (balFrom state message v f).toNat < v.toNat)
    {cA c3 c4 cF : Bool}
    (hcA : coldIn substate message.currentTarget (allowFrom message f) = cA)
    (hc3 : coldIn (accessSlot substate message.currentTarget (allowFrom message f))
      message.currentTarget 3 = c3)
    (hc4 : coldIn (accessSlot (accessSlot substate message.currentTarget (allowFrom message f))
      message.currentTarget 3) message.currentTarget 4 = c4)
    (hcF : coldIn (allowedSubF fork substate state message v f) message.currentTarget
      (recipientSlot f) = cF)
    {gas : Nat}
    (hstip : 361 + slotCost cA + slotCost c3 + slotCost c4 + mulCost v +
      capCost (rawFee state message v) (storageAt state message.currentTarget 4) +
      allowCostF fork state message v f + 2300 ≤ gas)
    (hg : 631 + slotCost cA + slotCost c3 + slotCost c4 + slotCost cF + mulCost v +
      capCost (rawFee state message v) (storageAt state message.currentTarget 4) +
      allowCostF fork state message v f ≤ gas) :
    Spec fork (At CODE message 8648 [0x60, 0, 0, 0, v, t, f, 0x1097, v, t, f, 0x0392, sel] M gas
        state substate)
      (Faulted (.invalidOpcode 0xfe)
        (readSlot (allowedF state message v f) message.currentTarget (recipientSlot f))
        (accessSlot (allowedSubF fork substate state message v f) message.currentTarget
          (recipientSlot f))) := by
  have hacc3 : hasAccount (readsF state message f) message.currentTarget :=
    hasAccount_readSlot (hasAccount_readSlot (hasAccount_readSlot hacc))
  simp only [allowCostF, rawFee, feeOf, allowOf, balFrom, allowedF, readsF, allowedSubF,
    accessF] at hstip hg hfv hlow hallow hcF ⊢
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
  exact subFault (by simp) hlow (by gas_ok)

/-- From 8648, `mul(v, basisPointsRate)` overflows: INVALID in `mul`, after the reads of the
allowance and slot 3. -/
theorem bodyMulOv (hfork : .berlin ≤ fork) {v t f sel : U256} {M : ByteArray}
    (hM : M.size = 96)
    (hov : 2 ^ 256 ≤ v.toNat *
      (storageAt state message.currentTarget 3).toNat)
    {cA c3 : Bool}
    (hcA : coldIn substate message.currentTarget (allowFrom message f) = cA)
    (hc3 : coldIn (accessSlot substate message.currentTarget (allowFrom message f))
      message.currentTarget 3 = c3)
    {gas : Nat} (hg : 337 + slotCost cA + slotCost c3 ≤ gas) :
    Spec fork (At CODE message 8648 [0x60, 0, 0, 0, v, t, f, 0x1097, v, t, f, 0x0392, sel] M gas
        state substate)
      (Faulted (.invalidOpcode 0xfe)
        (readSlot (readSlot state message.currentTarget (allowFrom message f))
          message.currentTarget 3)
        (accessSlot (accessSlot substate message.currentTarget (allowFrom message f))
          message.currentTarget 3)) := by
  step allowRead hfork (by simp) hcA (by gas_ok) hM
  step feeCall hfork (by simp) hc3 (by gas_ok)
  exact mulFault (by simp) (by simpa only [storageAt_readSlot] using hov) (by gas_ok)

/-- The specification of a `transferFrom(f, t, v)` call while paused.

Call data of 4 to 2^256 - 1 bytes with selector 0x23b872dd, no value, byte 20 of slot 0 (`paused`)
not 0. Then the run reverts with no output, after reading slot 0 (462 gas and the read). -/
theorem spec_paused (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsz : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x23b872dd)
    (hv : message.value = 0) (hpaused : byte20 (storageAt state message.currentTarget 0) ≠ 0)
    {c0 : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0) {gas : Nat}
    (hg : 462 + slotCost c0 ≤ gas) :
    Spec fork (At CODE message 0 [] .empty gas state substate)
      (Halted true .empty (gas - (462 + slotCost c0))
        (readSlot state message.currentTarget 0) (accessSlot substate message.currentTarget 0)) := by
  have ht : tested (BitVec.ofNat 256 (selector message.data)) ENTRIES = 7 := by
    rw [hsel]; decide
  have hb : branch (BitVec.ofNat 256 (selector message.data)) 54 (entrySize 4 2) ENTRIES =
      819 := by
    rw [hsel]; decide
  have h1 := dispatch (state := state) (substate := substate) hsize hsz (gas := gas)
    (by rw [ht]; gas_ok)
  rw [ht, hb] at h1
  refine Spec.seq h1 ?_
  step entry hv (by gas_ok)
  refine (pausedRevert hfork (by simp) hpaused hc0 (by gas_ok)).consequence (fun _ h => h) ?_
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  exact ⟨hr, he, ho, by rw [hgas]; gas_ok, hs, hss⟩

/-- The specification of a `transferFrom(f, t, v)` call whose `_from` is blacklisted.

Call data of 4 to 2^256 - 1 bytes with selector 0x23b872dd, no value, not paused, and the low byte
of `isBlackListed[f]` (slot `keccak(f ++ 6)`, `f` = argument word 0 masked to 160 bits) not 0.
Then the run reverts with no output, after reading slot 0 and that slot. The caller's blacklist
status is not read. -/
theorem spec_blacklisted (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsz : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x23b872dd)
    (hv : message.value = 0) (hnp : byte20 (storageAt state message.currentTarget 0) = 0)
    (hblack : (storageAt state message.currentTarget (blackFrom (fromArg message))).toNat % 256 ≠
      0)
    {c0 cB : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hcB : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget
      (blackFrom (fromArg message)) = cB)
    {gas : Nat} (hg : 614 + slotCost c0 + slotCost cB ≤ gas) :
    Spec fork (At CODE message 0 [] .empty gas state substate)
      (Halted true .empty (gas - (614 + slotCost c0 + slotCost cB))
        (readSlot (readSlot state message.currentTarget 0) message.currentTarget
          (blackFrom (fromArg message)))
        (accessSlot (accessSlot substate message.currentTarget 0) message.currentTarget
          (blackFrom (fromArg message)))) := by
  have ht : tested (BitVec.ofNat 256 (selector message.data)) ENTRIES = 7 := by
    rw [hsel]; decide
  have hb : branch (BitVec.ofNat 256 (selector message.data)) 54 (entrySize 4 2) ENTRIES =
      819 := by
    rw [hsel]; decide
  have h1 := dispatch (state := state) (substate := substate) hsize hsz (gas := gas)
    (by rw [ht]; gas_ok)
  rw [ht, hb] at h1
  refine Spec.seq h1 ?_
  step entry hv (by gas_ok)
  step notPaused hfork (by simp) hnp hc0 (by gas_ok)
  refine (blackRevert hfork (by simp) hcB (by rw [storageAt_readSlot]; exact hblack) (by gas_ok)
    size_MEM0).consequence (fun _ h => h) ?_
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  exact ⟨hr, he, ho, by rw [hgas]; gas_ok, hs, hss⟩

/-- The specification of a `transferFrom(f, t, v)` call whose call data is too short.

Call data of 4 to 99 bytes with selector 0x23b872dd, no value, not paused, `f` (argument word 0
as `addrArg` reads it) not blacklisted, not deprecated. Then StandardToken's
payload check of three words fails and the run reverts with no output. -/
theorem spec_short (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hshort : message.data.size < 100) (hsel : selector message.data = 0x23b872dd)
    (hv : message.value = 0) (hnp : byte20 (storageAt state message.currentTarget 0) = 0)
    (hnb : (storageAt state message.currentTarget (blackFrom (fromArg message))).toNat % 256 = 0)
    (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    {c0 cB c10 : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hcB : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget
      (blackFrom (fromArg message)) = cB)
    (hc10 : coldIn (accessSlot (accessSlot substate message.currentTarget 0) message.currentTarget
      (blackFrom (fromArg message))) message.currentTarget 10 = c10)
    {gas : Nat} (hg : 801 + slotCost c0 + slotCost cB + slotCost c10 ≤ gas) :
    Spec fork (At CODE message 0 [] .empty gas state substate)
      (Halted true .empty (gas - (801 + slotCost c0 + slotCost cB + slotCost c10))
        (checkState state message) (checkSub substate message)) := by
  refine Triple.seq (preF0 hfork hsize (by omega) hsel hv hnp hnb hdep hc0 hcB hc10
    (Nat.le_trans (by omega) hg)) ?_
  refine (shortRevert hfork (by simp) hshort (by gas_ok) (size_mapMem size_MEM0 _ _)).consequence
    (fun _ h => h) ?_
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  exact ⟨hr, he, ho, by rw [hgas]; gas_ok, hs, hss⟩

/-- The gas of `transferFrom` up to 8648 and the reads of the checks. -/
abbrev preCostF (c0 cB c10 : Bool) : Nat := PRE_COST_F + slotCost c0 + slotCost cB + slotCost c10

/-- The specification of `transferFrom(f, t, v)` with an allowance below `v`.

Hypotheses: call data of 100 to 2^256 - 1 bytes with selector 0x23b872dd; no value; not paused;
`f` not blacklisted; not deprecated; `v * rate < 2^256`; `A < v`, `A` = `allowed[f][caller]`
(slot `keccak(caller ++ keccak(f ++ 5))`) in `S`, the state after the reads of the checks; enough
gas to reach the assert.

Then INVALID at the allowance's `sub(A, v)` (the code computes the fee first): no output, no gas
left, state `S` with the allowance, slots 3 and 4 recorded read (nothing written). -/
theorem spec_allowLow (hfork : .berlin ≤ fork)
    (hlong : 100 ≤ message.data.size) (hsz : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x23b872dd) (hv : message.value = 0)
    (hnp : byte20 (storageAt state message.currentTarget 0) = 0)
    (hnb : (storageAt state message.currentTarget (blackFrom (fromArg message))).toNat % 256 = 0)
    (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    (hov : (valArg message).toNat *
      (storageAt (checkState state message) message.currentTarget 3).toNat < 2 ^ 256)
    (hlt : (allowOf (checkState state message) message (fromArg message)).toNat <
      (valArg message).toNat)
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
    {gas : Nat} (hg : preCostF c0 cB c10 + (457 + slotCost cA + slotCost c3 + slotCost c4 +
      mulCost (valArg message) +
      capCost (rawFee (checkState state message) message (valArg message))
        (storageAt (checkState state message) message.currentTarget 4)) ≤ gas) :
    Spec fork (At CODE message 0 [] .empty gas state substate)
      (Faulted (.invalidOpcode 0xfe) (readsF (checkState state message) message (fromArg message))
        (accessF (checkSub substate message) message (fromArg message))) :=
  Triple.seq (preF hfork hlong hsz hsel hv hnp hnb hdep hc0 hcB hc10
      (Nat.le_trans (Nat.le_add_right _ _) hg))
    (bodyAllowLow hfork (size_mapMem size_MEM0 _ _) hov hlt hcA hc3 hc4
      (Nat.le_sub_of_add_le (by rw [Nat.add_comm]; exact hg)))

/-- The specification of `transferFrom(f, t, v)` when `balances[f]` is below `v`.

Hypotheses: Berlin ≤ fork < Glamsterdam, not static, the contract has an account; the checks pass
as in `spec_allowLow`; `v * rate < 2^256`; `fee ≤ v` (any fee); `A = MAX_UINT ∨ v ≤ A`;
`balances[f] < v`, read after the allowance step (`balFrom`); more than 2300 gas left at the
allowance's SSTORE when `A ≠ MAX_UINT` (`hstip`), and enough gas to reach the assert.

Then INVALID at the debit's `sub`: no output, no gas left, in the state after the allowance step
(`A - v` written unless `A = MAX_UINT`) and the read of `balances[f]` (the caller discards it). -/
theorem spec_balLow (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    (hstatic : message.isStatic = false) (hacc : hasAccount state message.currentTarget)
    (hlong : 100 ≤ message.data.size) (hsz : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x23b872dd) (hv : message.value = 0)
    (hnp : byte20 (storageAt state message.currentTarget 0) = 0)
    (hnb : (storageAt state message.currentTarget (blackFrom (fromArg message))).toNat % 256 = 0)
    (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    (hov : (valArg message).toNat *
      (storageAt (checkState state message) message.currentTarget 3).toNat < 2 ^ 256)
    (hfv : (feeOf (checkState state message) message (valArg message)).toNat ≤
      (valArg message).toNat)
    (hallow : allowOf (checkState state message) message (fromArg message) = MAX_UINT ∨
      (valArg message).toNat ≤ (allowOf (checkState state message) message (fromArg message)).toNat)
    (hlow : (balFrom (checkState state message) message (valArg message) (fromArg message)).toNat <
      (valArg message).toNat)
    {c0 cB c10 cA c3 c4 cF : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
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
    {gas : Nat}
    (hstip : preCostF c0 cB c10 + (361 + slotCost cA + slotCost c3 + slotCost c4 +
      mulCost (valArg message) +
      capCost (rawFee (checkState state message) message (valArg message))
        (storageAt (checkState state message) message.currentTarget 4) +
      allowCostF fork (checkState state message) message (valArg message) (fromArg message) +
      2300) ≤ gas)
    (hg : preCostF c0 cB c10 + (631 + slotCost cA + slotCost c3 + slotCost c4 + slotCost cF +
      mulCost (valArg message) +
      capCost (rawFee (checkState state message) message (valArg message))
        (storageAt (checkState state message) message.currentTarget 4) +
      allowCostF fork (checkState state message) message (valArg message) (fromArg message)) ≤
        gas) :
    Spec fork (At CODE message 0 [] .empty gas state substate)
      (Faulted (.invalidOpcode 0xfe)
        (readSlot (allowedF (checkState state message) message (valArg message) (fromArg message))
          message.currentTarget (recipientSlot (fromArg message)))
        (accessSlot (allowedSubF fork (checkSub substate message) (checkState state message)
          message (valArg message) (fromArg message)) message.currentTarget
          (recipientSlot (fromArg message)))) :=
  Triple.seq (preF hfork hlong hsz hsel hv hnp hnb hdep hc0 hcB hc10
      (Nat.le_trans (Nat.le_add_right _ _) hg))
    (bodyBalLow hfork hglam hstatic
      (hasAccount_readSlot (hasAccount_readSlot (hasAccount_readSlot hacc)))
      (size_mapMem size_MEM0 _ _) hov hfv hallow hlow hcA hc3 hc4 hcF
      (Nat.le_sub_of_add_le (by rw [Nat.add_comm]; exact hstip))
      (Nat.le_sub_of_add_le (by rw [Nat.add_comm]; exact hg)))

/-- The specification of `transferFrom(f, t, v)` when `v * basisPointsRate` overflows.

Hypotheses: the checks pass as in `spec_allowLow`; `v * rate ≥ 2^256`; enough gas. Then INVALID in
`mul`: no output, no gas left, state `S` with the allowance and slot 3 recorded read. -/
theorem spec_mulOv (hfork : .berlin ≤ fork)
    (hlong : 100 ≤ message.data.size) (hsz : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x23b872dd) (hv : message.value = 0)
    (hnp : byte20 (storageAt state message.currentTarget 0) = 0)
    (hnb : (storageAt state message.currentTarget (blackFrom (fromArg message))).toNat % 256 = 0)
    (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    (hov : 2 ^ 256 ≤ (valArg message).toNat *
      (storageAt (checkState state message) message.currentTarget 3).toNat)
    {c0 cB c10 cA c3 : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hcB : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget
      (blackFrom (fromArg message)) = cB)
    (hc10 : coldIn (accessSlot (accessSlot substate message.currentTarget 0) message.currentTarget
      (blackFrom (fromArg message))) message.currentTarget 10 = c10)
    (hcA : coldIn (checkSub substate message) message.currentTarget
      (allowFrom message (fromArg message)) = cA)
    (hc3 : coldIn (accessSlot (checkSub substate message) message.currentTarget
      (allowFrom message (fromArg message))) message.currentTarget 3 = c3)
    {gas : Nat} (hg : preCostF c0 cB c10 + (337 + slotCost cA + slotCost c3) ≤ gas) :
    Spec fork (At CODE message 0 [] .empty gas state substate)
      (Faulted (.invalidOpcode 0xfe)
        (readSlot (readSlot (checkState state message) message.currentTarget
          (allowFrom message (fromArg message))) message.currentTarget 3)
        (accessSlot (accessSlot (checkSub substate message) message.currentTarget
          (allowFrom message (fromArg message))) message.currentTarget 3)) :=
  Triple.seq (preF hfork hlong hsz hsel hv hnp hnb hdep hc0 hcB hc10
      (Nat.le_trans (Nat.le_add_right _ _) hg))
    (bodyMulOv hfork (size_mapMem size_MEM0 _ _) hov hcA hc3
      (Nat.le_sub_of_add_le (by rw [Nat.add_comm]; exact hg)))

/-- The loop of the interpreter runs the case of `spec_paused` to its end condition. It holds for
every bound on the gas of messages and every runner of messages. -/
theorem runFrame_paused (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsz : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x23b872dd)
    (hv : message.value = 0) (hpaused : byte20 (storageAt state message.currentTarget 0) ≠ 0)
    {c0 : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0) {gas : Nat}
    (hg : 462 + slotCost c0 ≤ gas)
    {bound : Nat} {runChild : MessageRunner fork Nat bound} {evm : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    ∃ stopped, runFrame (step fork) (step_decreases fork) bound runChild evm within =
      .ok stopped ∧
      Halted true .empty (gas - (462 + slotCost c0))
          (readSlot state message.currentTarget 0) (accessSlot substate message.currentTarget 0)
          stopped :=
  (spec_paused hfork hsize hsz hsel hv hpaused hc0 hg).runFrame start within

/-- The loop of the interpreter runs the case of `spec_blacklisted` to its end condition. It holds for
every bound on the gas of messages and every runner of messages. -/
theorem runFrame_blacklisted (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsz : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x23b872dd)
    (hv : message.value = 0) (hnp : byte20 (storageAt state message.currentTarget 0) = 0)
    (hblack : (storageAt state message.currentTarget (blackFrom (fromArg message))).toNat % 256 ≠
      0)
    {c0 cB : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hcB : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget
      (blackFrom (fromArg message)) = cB)
    {gas : Nat} (hg : 614 + slotCost c0 + slotCost cB ≤ gas)
    {bound : Nat} {runChild : MessageRunner fork Nat bound} {evm : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    ∃ stopped, runFrame (step fork) (step_decreases fork) bound runChild evm within =
      .ok stopped ∧
      Halted true .empty (gas - (614 + slotCost c0 + slotCost cB))
          (readSlot (readSlot state message.currentTarget 0) message.currentTarget
            (blackFrom (fromArg message)))
          (accessSlot (accessSlot substate message.currentTarget 0) message.currentTarget
            (blackFrom (fromArg message))) stopped :=
  (spec_blacklisted hfork hsize hsz hsel hv hnp hblack hc0 hcB hg).runFrame start within

/-- The loop of the interpreter runs the case of `spec_short` to its end condition. It holds for
every bound on the gas of messages and every runner of messages. -/
theorem runFrame_short (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hshort : message.data.size < 100) (hsel : selector message.data = 0x23b872dd)
    (hv : message.value = 0) (hnp : byte20 (storageAt state message.currentTarget 0) = 0)
    (hnb : (storageAt state message.currentTarget (blackFrom (fromArg message))).toNat % 256 = 0)
    (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    {c0 cB c10 : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hcB : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget
      (blackFrom (fromArg message)) = cB)
    (hc10 : coldIn (accessSlot (accessSlot substate message.currentTarget 0) message.currentTarget
      (blackFrom (fromArg message))) message.currentTarget 10 = c10)
    {gas : Nat} (hg : 801 + slotCost c0 + slotCost cB + slotCost c10 ≤ gas)
    {bound : Nat} {runChild : MessageRunner fork Nat bound} {evm : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    ∃ stopped, runFrame (step fork) (step_decreases fork) bound runChild evm within =
      .ok stopped ∧
      Halted true .empty (gas - (801 + slotCost c0 + slotCost cB + slotCost c10))
          (checkState state message) (checkSub substate message) stopped :=
  (spec_short hfork hsize hshort hsel hv hnp hnb hdep hc0 hcB hc10 hg).runFrame start within

/-- The loop of the interpreter runs the case of `spec_allowLow` to its end condition. It holds for
every bound on the gas of messages and every runner of messages. -/
theorem runFrame_allowLow (hfork : .berlin ≤ fork)
    (hlong : 100 ≤ message.data.size) (hsz : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x23b872dd) (hv : message.value = 0)
    (hnp : byte20 (storageAt state message.currentTarget 0) = 0)
    (hnb : (storageAt state message.currentTarget (blackFrom (fromArg message))).toNat % 256 = 0)
    (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    (hov : (valArg message).toNat *
      (storageAt (checkState state message) message.currentTarget 3).toNat < 2 ^ 256)
    (hlt : (allowOf (checkState state message) message (fromArg message)).toNat <
      (valArg message).toNat)
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
    {gas : Nat} (hg : preCostF c0 cB c10 + (457 + slotCost cA + slotCost c3 + slotCost c4 +
      mulCost (valArg message) +
      capCost (rawFee (checkState state message) message (valArg message))
        (storageAt (checkState state message) message.currentTarget 4)) ≤ gas)
    {bound : Nat} {runChild : MessageRunner fork Nat bound} {evm : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    ∃ stopped, runFrame (step fork) (step_decreases fork) bound runChild evm within =
      .ok stopped ∧
      Faulted (.invalidOpcode 0xfe) (readsF (checkState state message) message (fromArg message))
          (accessF (checkSub substate message) message (fromArg message)) stopped :=
  (spec_allowLow hfork hlong hsz hsel hv hnp hnb hdep hov hlt hc0 hcB hc10 hcA hc3 hc4
    hg).runFrame start within

/-- The loop of the interpreter runs the case of `spec_balLow` to its end condition. It holds for
every bound on the gas of messages and every runner of messages. -/
theorem runFrame_balLow (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    (hstatic : message.isStatic = false) (hacc : hasAccount state message.currentTarget)
    (hlong : 100 ≤ message.data.size) (hsz : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x23b872dd) (hv : message.value = 0)
    (hnp : byte20 (storageAt state message.currentTarget 0) = 0)
    (hnb : (storageAt state message.currentTarget (blackFrom (fromArg message))).toNat % 256 = 0)
    (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    (hov : (valArg message).toNat *
      (storageAt (checkState state message) message.currentTarget 3).toNat < 2 ^ 256)
    (hfv : (feeOf (checkState state message) message (valArg message)).toNat ≤
      (valArg message).toNat)
    (hallow : allowOf (checkState state message) message (fromArg message) = MAX_UINT ∨
      (valArg message).toNat ≤ (allowOf (checkState state message) message (fromArg message)).toNat)
    (hlow : (balFrom (checkState state message) message (valArg message) (fromArg message)).toNat <
      (valArg message).toNat)
    {c0 cB c10 cA c3 c4 cF : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
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
    {gas : Nat}
    (hstip : preCostF c0 cB c10 + (361 + slotCost cA + slotCost c3 + slotCost c4 +
      mulCost (valArg message) +
      capCost (rawFee (checkState state message) message (valArg message))
        (storageAt (checkState state message) message.currentTarget 4) +
      allowCostF fork (checkState state message) message (valArg message) (fromArg message) +
      2300) ≤ gas)
    (hg : preCostF c0 cB c10 + (631 + slotCost cA + slotCost c3 + slotCost c4 + slotCost cF +
      mulCost (valArg message) +
      capCost (rawFee (checkState state message) message (valArg message))
        (storageAt (checkState state message) message.currentTarget 4) +
      allowCostF fork (checkState state message) message (valArg message) (fromArg message)) ≤
        gas)
    {bound : Nat} {runChild : MessageRunner fork Nat bound} {evm : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    ∃ stopped, runFrame (step fork) (step_decreases fork) bound runChild evm within =
      .ok stopped ∧
      Faulted (.invalidOpcode 0xfe)
          (readSlot (allowedF (checkState state message) message (valArg message) (fromArg message))
            message.currentTarget (recipientSlot (fromArg message)))
          (accessSlot (allowedSubF fork (checkSub substate message) (checkState state message)
            message (valArg message) (fromArg message)) message.currentTarget
            (recipientSlot (fromArg message))) stopped :=
  (spec_balLow hfork hglam hstatic hacc hlong hsz hsel hv hnp hnb hdep hov hfv hallow hlow hc0 hcB
    hc10 hcA hc3 hc4 hcF hstip hg).runFrame start within

/-- The loop of the interpreter runs the case of `spec_mulOv` to its end condition. It holds for
every bound on the gas of messages and every runner of messages. -/
theorem runFrame_mulOv (hfork : .berlin ≤ fork)
    (hlong : 100 ≤ message.data.size) (hsz : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x23b872dd) (hv : message.value = 0)
    (hnp : byte20 (storageAt state message.currentTarget 0) = 0)
    (hnb : (storageAt state message.currentTarget (blackFrom (fromArg message))).toNat % 256 = 0)
    (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    (hov : 2 ^ 256 ≤ (valArg message).toNat *
      (storageAt (checkState state message) message.currentTarget 3).toNat)
    {c0 cB c10 cA c3 : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hcB : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget
      (blackFrom (fromArg message)) = cB)
    (hc10 : coldIn (accessSlot (accessSlot substate message.currentTarget 0) message.currentTarget
      (blackFrom (fromArg message))) message.currentTarget 10 = c10)
    (hcA : coldIn (checkSub substate message) message.currentTarget
      (allowFrom message (fromArg message)) = cA)
    (hc3 : coldIn (accessSlot (checkSub substate message) message.currentTarget
      (allowFrom message (fromArg message))) message.currentTarget 3 = c3)
    {gas : Nat} (hg : preCostF c0 cB c10 + (337 + slotCost cA + slotCost c3) ≤ gas)
    {bound : Nat} {runChild : MessageRunner fork Nat bound} {evm : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    ∃ stopped, runFrame (step fork) (step_decreases fork) bound runChild evm within =
      .ok stopped ∧
      Faulted (.invalidOpcode 0xfe)
          (readSlot (readSlot (checkState state message) message.currentTarget
            (allowFrom message (fromArg message))) message.currentTarget 3)
          (accessSlot (accessSlot (checkSub substate message) message.currentTarget
            (allowFrom message (fromArg message))) message.currentTarget 3) stopped :=
  (spec_mulOv hfork hlong hsz hsel hv hnp hnb hdep hov hc0 hcB hc10 hcA hc3 hg).runFrame start
    within

end UsdtVerify.TransferFrom
