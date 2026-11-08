import UsdtVerify.Usdt.Spec.Transfer

/-!
# transferFrom(address,address,uint256): the specifications from pc 0

Proves what a call of transferFrom does from pc 0, not deprecated: the reverts, the success
paths with a fee of 0 and above 0, and the failed SafeMath asserts.

The blocks are in Usdt/Proofs/TransferFrom.lean and Usdt/Proofs/Fee.lean.

The parts below keep their own headers:

- transferFrom(address,address,uint256): the success path, from pc 0, with a fee of 0
- transferFrom(address,address,uint256): the reverts and the failed SafeMath asserts
- transferFrom(address,address,uint256): the success path with a fee above 0
- transferFrom(address,address,uint256): the remaining failed SafeMath asserts
-/

section

/-!
## transferFrom(address,address,uint256): the success path, from pc 0, with a fee of 0

`spec_ok` / `runFrame_ok`: a `transferFrom(from, to, value)` call with at least 100 bytes of call
data, not paused, `from` not blacklisted, not deprecated, whose fee (as the bytecode computes it)
is 0, with an allowance that is `MAX_UINT` or at least `value`, a sufficient balance of `from`
and no overflow at `to`, stops normally after it lowers the allowance by `value` (unless it is
`MAX_UINT`), moves `value` from `balances[from]` to `balances[to]`, and logs
`Transfer(from, to, value)`.
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

/-- `_from`: argument word 0 masked to 160 bits. -/
abbrev fromArg (message : Message fork) : U256 := addrArg message.data 0

/-- `_to`: argument word 1 masked to 160 bits. -/
abbrev toArg (message : Message fork) : U256 := addrArg message.data 1

/-- `_value`: argument word 2. -/
abbrev valArg (message : Message fork) : U256 := wordArg message.data 2

/-- The state after the reads of the checks: slot 0, `isBlackListed[_from]`, slot 10. -/
abbrev checkState (state : State.TransactionState) (message : Message fork) :
    State.TransactionState :=
  readSlot (readSlot (readSlot state message.currentTarget 0) message.currentTarget
    (blackFrom (fromArg message))) message.currentTarget 10

/-- The substate after the accesses of the checks. -/
abbrev checkSub (substate : Substate) (message : Message fork) : Substate :=
  accessSlot (accessSlot (accessSlot substate message.currentTarget 0) message.currentTarget
    (blackFrom (fromArg message))) message.currentTarget 10

/-- The gas of the path before 8648, besides the reads of slots 0, 10 and the blacklist slot. -/
abbrev PRE_COST_F : Nat := 795

/-- The whole gas of the success path with a fee of 0. -/
abbrev okCostF (fork : Fork) (state : State.TransactionState) (message : Message fork)
    (c0 cB c10 cA c3 c4 cF cT : Bool) : Nat :=
  PRE_COST_F + slotCost c0 + slotCost cB + slotCost c10 + (2971 + slotCost cA + slotCost c3 +
    slotCost c4 + slotCost cF + slotCost cT + mulCost (valArg message) +
    capCost (rawFee (checkState state message) message (valArg message))
      (storageAt (checkState state message) message.currentTarget 4) +
    allowCostF fork (checkState state message) message (valArg message) (fromArg message) +
    debitCostF fork (checkState state message) message (valArg message) (fromArg message) +
    creditCostF fork (checkState state message) message (valArg message) (toArg message)
      (fromArg message))

/-- The gas used before the SSTORE of `balances[_to]`, which needs more than 2300 gas left. -/
abbrev stipCostF (fork : Fork) (state : State.TransactionState) (message : Message fork)
    (c0 cB c10 cA c3 c4 cF cT : Bool) : Nat :=
  PRE_COST_F + slotCost c0 + slotCost cB + slotCost c10 + (972 + slotCost cA + slotCost c3 +
    slotCost c4 + slotCost cF + slotCost cT + mulCost (valArg message) +
    capCost (rawFee (checkState state message) message (valArg message))
      (storageAt (checkState state message) message.currentTarget 4) +
    allowCostF fork (checkState state message) message (valArg message) (fromArg message) +
    debitCostF fork (checkState state message) message (valArg message) (fromArg message) + 2401)

/-- The specification of a successful `transferFrom(address,address,uint256)` with a fee of 0.

Write `C` for the contract, `f`, `t` for argument words 0 and 1 masked to 160 bits, `v` for
argument word 2, `S` for the state after the reads of the checks (slot 0, `isBlackListed[f]`,
slot 10; reads change no word), `A` for `allowed[f][caller]` (slot
`keccak(caller ++ keccak(f ++ 5))`) in `S`.

Hypotheses: Berlin ≤ fork (Glamsterdam included); not static; `C` has an account; call data of 100 to
2^256 - 1 bytes with selector 0x23b872dd; no value; not paused; `f` not blacklisted (low byte of
`isBlackListed[f]` is 0; the caller and `t` are not checked); not deprecated;
`v * basisPointsRate` does not overflow; the fee is 0; `A = MAX_UINT` or `v ≤ A`;
`v ≤ balances[f]` read after the allowance step; `balances[t] + v < 2^256` read after the write of
`f`; enough gas, and more than 2300 gas left at the SSTORE of `balances[t]` (`stipCostF ≤ gas`;
the stipends of the two earlier SSTOREs follow from the total).

Then the run stops normally (STOP) with gas left `gas - okCostF`; the state `creditedF S`: when
`A ≠ MAX_UINT` the allowance slot := `A - v` (else untouched), then `balances[f] := balF - v`,
then `balances[t] := balT + v`; the substate with the slots accessed, the refunds of the writes,
and the log `Transfer(f, t, v)` (topic 0xddf252ad…, data the 32 bytes of `v`) appended. -/
theorem spec_ok (hfork : .berlin ≤ fork)
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
    {gas : Nat} (hstip : stipCostF fork state message c0 cB c10 cA c3 c4 cF cT ≤ gas)
    (hg : okCostF fork state message c0 cB c10 cA c3 c4 cF cT ≤ gas) :
    Gas.SpecG fork (At CODE message 0 [] .empty gas state substate)
      (Halted false .empty (gas - okCostF fork state message c0 cB c10 cA c3 c4 cF cT)
        (creditedF (checkState state message) message (valArg message) (toArg message)
          (fromArg message))
        (loggedSubF fork (checkSub substate message) (checkState state message) message
          (valArg message) (toArg message) (fromArg message))) := by
  have hB := body (state := checkState state message) (substate := checkSub substate message)
    (sel := BitVec.ofNat 256 (selector message.data))
    (gas := gas - (PRE_COST_F + slotCost c0 + slotCost cB + slotCost c10))
    hfork hstatic
    (hasAccount_readSlot (hasAccount_readSlot (hasAccount_readSlot hacc)))
    (size_mapMem size_MEM0 (mkey (fromArg message)) 6)
    (ptr_mapMem size_MEM0 mload_MEM0 _ _) hov hfee hallow hbal hto hcA hc3 hc4 hcF hcT
    (Nat.le_sub_of_add_le (by rw [Nat.add_comm]; exact hstip))
    (Nat.le_sub_of_add_le (by rw [Nat.add_comm]; exact hg))
  have hpre : PRE_COST_F + slotCost c0 + slotCost cB + slotCost c10 ≤ gas :=
    Nat.le_trans (Nat.le_add_right _ _) hg
  clear hov hfee hallow hbal hto hstip hg
  simp only [PRE_COST_F] at hpre hB
  have ht : tested (BitVec.ofNat 256 (selector message.data)) ENTRIES = 7 := by
    rw [hsel]; decide
  have hb : branch (BitVec.ofNat 256 (selector message.data)) 54 (entrySize 4 2) ENTRIES =
      819 := by
    rw [hsel]; decide
  have h1 := dispatch (state := state) (substate := substate) (by omega) hsz (gas := gas)
    (by rw [ht]; gas_ok)
  rw [ht, hb] at h1
  refine Gas.SpecG.seq h1 ?_
  step entry hv (by gas_ok)
  step notPaused hfork (by simp) hnp hc0 (by gas_ok)
  step notBlack hfork (by simp) hcB (by rw [storageAt_readSlot]; exact hnb) (by gas_ok) size_MEM0
  step notDeprecated hfork (by simp) (by rw [storageAt_readSlot, storageAt_readSlot]; exact hdep)
    hc10 (by gas_ok)
  step toStandard (by gas_ok)
  step payload hlong hsz (by simp) (by gas_ok)
  step Gas.reshapeG (g' := gas - (795 + slotCost c0 + slotCost cB + slotCost c10)) rfl rfl (by gas_ok)
  refine hB.consequence (fun _ h => h) ?_
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  exact ⟨hr, he, ho, by rw [hgas, Nat.sub_sub], hs, hss⟩

/-- The loop of the interpreter runs a successful `transferFrom` call with a fee of 0 to its
specification. It holds for every bound on the gas of messages and every runner of messages. -/
theorem runFrame_ok (hfork : .berlin ≤ fork)
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
    {gas : Nat} (hstip : stipCostF fork state message c0 cB c10 cA c3 c4 cF cT ≤ gas)
    (hg : okCostF fork state message c0 cB c10 cA c3 c4 cF cT ≤ gas) {bound : Nat}
    {runChild : MessageRunner fork Nat bound} {evm : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    ∃ stopped, runFrame (step fork) (step_decreases fork) bound runChild evm within =
      .ok stopped ∧
      Halted false .empty (gas - okCostF fork state message c0 cB c10 cA c3 c4 cF cT)
        (creditedF (checkState state message) message (valArg message) (toArg message)
          (fromArg message))
        (loggedSubF fork (checkSub substate message) (checkState state message) message
          (valArg message) (toArg message) (fromArg message)) stopped :=
  (spec_ok hfork hstatic hacc hlong hsz hsel hv hnp hnb hdep hov hfee hallow hbal hto hc0 hcB
    hc10 hcA hc3 hc4 hcF hcT hstip hg).runFrame start within

end UsdtVerify.TransferFrom

end

section

/-!
## transferFrom(address,address,uint256): the reverts and the failed SafeMath asserts

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
    Gas.SpecG fork (At CODE message 3773 rest MEM0 gas state substate)
      (Halted true .empty (gas - (118 + slotCost c0)) (readSlot state message.currentTarget 0)
        (accessSlot substate message.currentTarget 0)) := by
  have hexp : exponentBytes (0x14 : U256) = 1 := by decide
  step jumpdestR
  step pushR 1 (0 : U256)
  step pushR 1 (0x14 : U256)
  step swapR 0
  norm
  step Gas.sloadG hfork (cold := c0) (by code_fact) (by code_fact) hc0 (by gas_ok)
  step swapR 0
  norm
  step pushR 2 (0x0100 : U256)
  step Gas.expLG (Nat.le_trans (by decide) hfork) (by code_fact) (by code_fact) (by gas_ok)
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
  refine (Gas.revertG (Nat.le_trans (by decide) hfork) (by code_fact) (by code_fact)
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
    Gas.SpecG fork (At CODE message 3801 (v :: t :: f :: rest) M gas state substate)
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
  step Gas.sloadG hfork (cold := cB) (by code_fact) (by code_fact) hcB (by gas_ok)
  step swapR 0
  norm
  step pushR 2 (0x0100 : U256)
  step Gas.expLG (Nat.le_trans (by decide) hfork) (by code_fact) (by code_fact) (by gas_ok)
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
  refine (Gas.revertG (Nat.le_trans (by decide) hfork) (by code_fact) (by code_fact)
    (by rw [hz]; gas_ok)).consequence (fun _ h => h) ?_
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  refine ⟨hr, he, ?_, ?_, hs, hss⟩
  · rw [ho]; simp [memoryReadBytes]
  · rw [hgas, hz]; gas_ok

/-- At 8619, call data of fewer than 100 bytes (three argument words) makes the code revert. -/
theorem shortRevert (hfork : .berlin ≤ fork) {rest : List U256} (hrest : rest.length ≤ 16)
    (hshort : message.data.size < 100) {gas : Nat} (hg : 63 ≤ gas) {M : ByteArray}
    (hM : M.size = 96) :
    Gas.SpecG fork (At CODE message 8619 rest M gas state substate)
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
  step Gas.calldatasizeG (by code_fact) (by code_fact) (by gas_ok) (by stk_ok)
  step swapR 0
  norm
  step popR
  step binR 0x10 Local.instruction_lt
  step unR 0x15 instruction_iszero
  step unR 0x15 instruction_iszero
  step unR 0x15 instruction_iszero
  step pushR 2 (0x21c8 : U256)
  refine Triple.seq (Gas.jumpi_of_eq_zeroG (by code_fact) (by code_fact) (by gas_ok) ?_) ?_
  · have h100 : (add (0x60 : U256) (0x04 : U256)).toNat = 100 := by decide
    have hlt : lessThan (BitVec.ofNat 256 message.data.size) (add (0x60 : U256) (0x04 : U256)) =
        1 := by
      simp only [lessThan, h100, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (show message.data.size < 2 ^ 256 by omega)]
      rw [ite_eq_left hshort]
    rw [hlt]
    decide
  step pushR 1 (0 : U256)
  step dupR 0
  refine (Gas.revertG (Nat.le_trans (by decide) hfork) (by code_fact) (by code_fact)
    (by rw [hz]; gas_ok)).consequence (fun _ h => h) ?_
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  refine ⟨hr, he, ?_, ?_, hs, hss⟩
  · rw [ho]; simp [memoryReadBytes]
  · rw [hgas, hz]; gas_ok

/-- At 8834, `_allowance = A < v`: the allowance is below `MAX_UINT`, and the code's
`sub(A, v)` fails its assert (INVALID at 10989). -/
theorem allowFault {fee A v t f : U256} {rest : List U256} (hrest : rest.length ≤ 8)
    (hlt : A.toNat < v.toNat) {gas : Nat} (hg : 96 ≤ gas) {M : ByteArray} :
    Gas.SpecG fork (At CODE message 8834 (0x60 :: 0 :: fee :: A :: v :: t :: f :: rest) M gas state
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
    Gas.HoareG fork (At CODE message 0 [] .empty gas state substate)
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
  exact Gas.reshapeG rfl rfl (by gas_ok)

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
    Gas.HoareG fork (At CODE message 0 [] .empty gas state substate)
      (At CODE message 8648 ((0x60 : U256) :: 0 :: 0 :: 0 :: stdStack message) (memF message)
        (gas - (PRE_COST_F + slotCost c0 + slotCost cB + slotCost c10))
        (checkState state message) (checkSub substate message)) := by
  simp only [PRE_COST_F] at hg ⊢
  refine Triple.seq (preF0 hfork (by omega) hsz hsel hv hnp hnb hdep hc0 hcB hc10
    (Nat.le_trans (by omega) hg)) ?_
  step payload hlong hsz (by simp) (by gas_ok)
  exact Gas.reshapeG rfl rfl (by gas_ok)

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
    Gas.SpecG fork (At CODE message 8648 [0x60, 0, 0, 0, v, t, f, 0x1097, v, t, f, 0x0392, sel] M gas
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
theorem bodyBalLow (hfork : .berlin ≤ fork)
    {v t f sel : U256} {M : ByteArray} (hM : M.size = 96)
    (hov : v.toNat * (storageAt state message.currentTarget 3).toNat < 2 ^ 256)
    (hfv : (feeOf state message v).toNat ≤ v.toNat)
    (hallow : allowOf state message f = MAX_UINT ∨ v.toNat ≤ (allowOf state message f).toNat)
    (hgood : allowOf state message f ≠ MAX_UINT →
      message.isStatic = false ∧ hasAccount state message.currentTarget)
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
    Gas.SpecG fork (At CODE message 8648 [0x60, 0, 0, 0, v, t, f, 0x1097, v, t, f, 0x0392, sel] M gas
        state substate)
      (Faulted (.invalidOpcode 0xfe)
        (readSlot (allowedF state message v f) message.currentTarget (recipientSlot f))
        (accessSlot (allowedSubF fork substate state message v f) message.currentTarget
          (recipientSlot f))) := by
  have hgood3 : allowOf state message f ≠ MAX_UINT →
      message.isStatic = false ∧ hasAccount (readsF state message f) message.currentTarget :=
    fun h => ⟨(hgood h).1,
      hasAccount_readSlot (hasAccount_readSlot (hasAccount_readSlot (hgood h).2))⟩
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
  step allowStep hfork (by simp) (by simp only [storageAt_readSlot]) hallow hgood3
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
    Gas.SpecG fork (At CODE message 8648 [0x60, 0, 0, 0, v, t, f, 0x1097, v, t, f, 0x0392, sel] M gas
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
    Gas.SpecG fork (At CODE message 0 [] .empty gas state substate)
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
  refine Gas.SpecG.seq h1 ?_
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
    Gas.SpecG fork (At CODE message 0 [] .empty gas state substate)
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
  refine Gas.SpecG.seq h1 ?_
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
    Gas.SpecG fork (At CODE message 0 [] .empty gas state substate)
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
    Gas.SpecG fork (At CODE message 0 [] .empty gas state substate)
      (Faulted (.invalidOpcode 0xfe) (readsF (checkState state message) message (fromArg message))
        (accessF (checkSub substate message) message (fromArg message))) :=
  Triple.seq (preF hfork hlong hsz hsel hv hnp hnb hdep hc0 hcB hc10
      (Nat.le_trans (Nat.le_add_right _ _) hg))
    (bodyAllowLow hfork (size_mapMem size_MEM0 _ _) hov hlt hcA hc3 hc4
      (Nat.le_sub_of_add_le (by rw [Nat.add_comm]; exact hg)))

/-- The specification of `transferFrom(f, t, v)` when `balances[f]` is below `v`.

Hypotheses: Berlin ≤ fork (Glamsterdam included); the checks pass as in `spec_allowLow`;
`v * rate < 2^256`; `fee ≤ v` (any fee); `A = MAX_UINT ∨ v ≤ A`; when `A ≠ MAX_UINT`, not static
and the contract has an account (`hgood`; the allowance is then written); `balances[f] < v`, read after the allowance step (`balFrom`); more than 2300 gas left at the
allowance's SSTORE when `A ≠ MAX_UINT` (`hstip`), and enough gas to reach the assert.

Then INVALID at the debit's `sub`: no output, no gas left, in the state after the allowance step
(`A - v` written unless `A = MAX_UINT`) and the read of `balances[f]` (the caller discards it). -/
theorem spec_balLow (hfork : .berlin ≤ fork)
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
    (hgood : allowOf (checkState state message) message (fromArg message) ≠ MAX_UINT →
      message.isStatic = false ∧ hasAccount state message.currentTarget)
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
    Gas.SpecG fork (At CODE message 0 [] .empty gas state substate)
      (Faulted (.invalidOpcode 0xfe)
        (readSlot (allowedF (checkState state message) message (valArg message) (fromArg message))
          message.currentTarget (recipientSlot (fromArg message)))
        (accessSlot (allowedSubF fork (checkSub substate message) (checkState state message)
          message (valArg message) (fromArg message)) message.currentTarget
          (recipientSlot (fromArg message)))) :=
  Triple.seq (preF hfork hlong hsz hsel hv hnp hnb hdep hc0 hcB hc10
      (Nat.le_trans (Nat.le_add_right _ _) hg))
    (bodyBalLow hfork (size_mapMem size_MEM0 _ _) hov hfv hallow
      (fun h => ⟨(hgood h).1,
      hasAccount_readSlot (hasAccount_readSlot (hasAccount_readSlot (hgood h).2))⟩) hlow hcA hc3 hc4 hcF
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
    Gas.SpecG fork (At CODE message 0 [] .empty gas state substate)
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
theorem runFrame_balLow (hfork : .berlin ≤ fork)
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
  (spec_balLow hfork hlong hsz hsel hv hnp hnb hdep hov hfv hallow (fun _ => ⟨hstatic, hacc⟩) hlow
    hc0 hcB hc10 hcA hc3 hc4 hcF hstip hg).runFrame start within

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

end

section

/-!
## transferFrom(address,address,uint256): the success path with a fee above 0

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
  Gas.writeCost fork (originalAt state message.currentTarget (recipientSlot t))
    (balTo state message v t f) (add (balTo state message v t f) (sendOf state message v)) false

/-- The memory at 9351. -/
abbrev memAF (message : Message fork) (M : ByteArray) (A f t : U256) : ByteArray :=
  mapMem (mapMem (mapMem (mapMem (allowMem2 message (allowMem message M f) A f) (mkey f) 2)
    (mkey f) 2) (mkey t) 2) (mkey t) 2

/-- From 8648, with a fee above 0, up to the owner's credit at 9351. -/
theorem headF (hfork : .berlin ≤ fork)
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
    Gas.HoareG fork (At CODE message 8648 [0x60, 0, 0, 0, v, t, f, 0x1097, v, t, f, 0x0392, sel] M gas
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
  step allowStep hfork (by simp) (by simp only [storageAt_readSlot]) hallow
    (fun _ => ⟨hstatic, hacc3⟩)
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
  step debitStore hfork (by simp) hstatic hacc4 (coldIn_accessSlot_self _ _ _)
    (by simp only [storageAt_readSlot, originalAt_readSlot, horig]; gas_ok) (size_mapMem hMb _ _)
  simp only [storageAt_readSlot, originalAt_readSlot, horig]
  step creditCall hfork (by simp) (cT := cT) (by rw [coldIn_storeSub]; exact hcT) (by gas_ok)
    (size_mapMem (size_mapMem hMb _ _) _ _)
  step addBlock (by simp) (by valid_dest) hto (by gas_ok)
  at_pc 9274
  step creditStoreFeeF hfork hfee (by simp) hstatic hacc5 (coldIn_accessSlot_self _ _ _)
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
theorem ownerPartF (hfork : .berlin ≤ fork)
    (hstatic : message.isStatic = false) {st : State.TransactionState} {ss : Substate}
    (hacc : hasAccount st message.currentTarget) {send fee A v t f sel o : U256} {M : ByteArray}
    (hM : M.size = 96) (hptr : loadWord (memoryReadBytes M 64 32) 0 32 = 0x60)
    (hc0 : coldIn ss message.currentTarget 0 = false) {cO : Bool}
    (hcO : coldIn ss message.currentTarget (ownerSlotOf st message.currentTarget) = cO)
    (ho : originalAt st message.currentTarget (ownerSlotOf st message.currentTarget) = o)
    (hown : (balOf st message.currentTarget).toNat + fee.toNat < 2 ^ 256) {gas : Nat}
    (hg : 4417 + slotCost cO + Gas.writeCost fork o (balOf st message.currentTarget)
      (add (balOf st message.currentTarget) fee) false ≤ gas) :
    Gas.SpecG fork (At CODE message 9351 [0x60, send, fee, A, v, t, f, 0x1097, v, t, f, 0x0392, sel]
        M gas st ss)
      (Halted false .empty (gas - (4417 + slotCost cO + Gas.writeCost fork o (balOf st message.currentTarget)
          (add (balOf st message.currentTarget) fee) false))
        (readSlot (ownedB st message.currentTarget fee) message.currentTarget 0)
        (feeSubBF fork ss st message o fee send t f)) := by
  simp only [ownerSlotOf, balOf, ownedB, feeSubBF] at hcO ho hown hg ⊢
  step ownerCallF (cO := cO) hfork rfl (by simp) hc0
    (by rw [coldIn_accessSlot_of_warm hc0]; exact hcO) (by gas_ok) hM
  step addBlock (by simp) (by valid_dest) hown (by gas_ok)
  at_pc 9465
  step ownerStoreF hfork (by rw [storageAt_readSlot, storageAt_readSlot]) (by simp) hstatic
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
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  exact ⟨hr, he, ho, by rw [hgas]; gas_ok, hs, hss⟩

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
  Gas.writeCost fork (originalAt state message.currentTarget
      (ownerSlot (ownerWordF state message v t f)))
    (balOF state message v t f) (add (balOF state message v t f) (feeOf state message v)) false

/-- From 8648, with a fee above 0, the success path of `transferFrom` up to the STOP at 915. -/
theorem bodyFeeF (hfork : .berlin ≤ fork)
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
    Gas.SpecG fork (At CODE message 8648 [0x60, 0, 0, 0, v, t, f, 0x1097, v, t, f, 0x0392, sel] M gas
        state substate)
      (Halted false .empty (gas - (5516 + slotCost cA + slotCost c3 + slotCost c4 + slotCost cF +
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
  have hA := headF (sel := sel) hfork hstatic hacc hM hov hfee hfv hallow hbal hto hcA hc3
    hc4 hcF hcT (gas := gas) (by simp only [ownerCostF] at hg; omega)
  have hB := ownerPartF (message := message) (st := creditedFeeF state message v t f)
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
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  refine ⟨hr, he, ho, ?_, hs, hss⟩
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

Hypotheses: as `spec_ok` (the first part of this file), with `fee ≠ 0` in place of `fee = 0`, plus
`fee ≤ v` (SafeMath sub of `sendAmount`), `balances[t] + (v - fee) < 2^256` (read after the write
of `f`), and `balances[owner] + fee < 2^256` (`owner` = low 160 bits of slot 0, both read after
the write of `t`); enough gas (`feeCostF ≤ gas`; the stipends of the four SSTOREs follow, since
logs costing more than 2300 come after each).

Then the run stops normally (STOP) with gas left `gas - feeCostF`; the state `feeStateF S`: the
allowance step (`A - v` unless `A = MAX_UINT`), `balances[f] := balF - v`,
`balances[t] := balT + (v - fee)`, `balances[owner] := balO + fee`, slot 0 recorded read; the
substate with the accesses and refunds, and the logs `Transfer(f, owner', fee)` (owner' read from
slot 0 after the owner's write) then `Transfer(f, t, v - fee)`. -/
theorem spec_feeF (hfork : .berlin ≤ fork)
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
    Gas.SpecG fork (At CODE message 0 [] .empty gas state substate)
      (Halted false .empty (gas - feeCostF fork state message c0 cB c10 cA c3 c4 cF cT cO)
        (feeStateF (checkState state message) message (valArg message) (toArg message)
          (fromArg message))
        (feeSubF fork (checkSub substate message) (checkState state message) message
          (valArg message) (toArg message) (fromArg message))) := by
  have hB := bodyFeeF (state := checkState state message) (substate := checkSub substate message)
    (sel := BitVec.ofNat 256 (selector message.data))
    (gas := gas - (PRE_COST_F + slotCost c0 + slotCost cB + slotCost c10))
    hfork hstatic
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
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  exact ⟨hr, he, ho, by rw [hgas, Nat.sub_sub], hs, hss⟩

/-- The loop of the interpreter runs a successful `transferFrom` call with a fee above 0 to its
specification. It holds for every bound on the gas of messages and every runner of messages. -/
theorem runFrame_feeF (hfork : .berlin ≤ fork)
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
      (Halted false .empty (gas - feeCostF fork state message c0 cB c10 cA c3 c4 cF cT cO)
        (feeStateF (checkState state message) message (valArg message) (toArg message)
          (fromArg message))
        (feeSubF fork (checkSub substate message) (checkState state message) message
          (valArg message) (toArg message) (fromArg message))) stopped :=
  (spec_feeF hfork hstatic hacc hlong hsz hsel hv hnp hnb hdep hov hfee hfv hallow hbal hto
    hown hc0 hcB hc10 hcA hc3 hc4 hcF hcT hcO hg).runFrame start within

end UsdtVerify.TransferFrom

end

section

/-!
## transferFrom(address,address,uint256): the remaining failed SafeMath asserts

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
theorem bodyFeeGtF (hfork : .berlin ≤ fork)
    {v t f sel : U256} {M : ByteArray} (hM : M.size = 96)
    (hov : v.toNat * (storageAt state message.currentTarget 3).toNat < 2 ^ 256)
    (hgt : v.toNat < (feeOf state message v).toNat)
    (hallow : allowOf state message f = MAX_UINT ∨ v.toNat ≤ (allowOf state message f).toNat)
    (hgood : allowOf state message f ≠ MAX_UINT →
      message.isStatic = false ∧ hasAccount state message.currentTarget)
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
    Gas.SpecG fork (At CODE message 8648 [0x60, 0, 0, 0, v, t, f, 0x1097, v, t, f, 0x0392, sel] M gas
        state substate)
      (Faulted (.invalidOpcode 0xfe) (allowedF state message v f)
        (allowedSubF fork substate state message v f)) := by
  have hgood3 : allowOf state message f ≠ MAX_UINT →
      message.isStatic = false ∧ hasAccount (readsF state message f) message.currentTarget :=
    fun h => ⟨(hgood h).1,
      hasAccount_readSlot (hasAccount_readSlot (hasAccount_readSlot (hgood h).2))⟩
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
  step allowStep hfork (by simp) (by simp only [storageAt_readSlot]) hallow hgood3
    (coldIn_accessSlot_false (coldIn_accessSlot_false (coldIn_accessSlot_self _ _ _)))
    (by simp only [originalAt_readSlot]; gas_ok)
    (size_allowMem hM f)
  simp only [originalAt_readSlot]
  step sendCall (by simp) (by gas_ok)
  exact subFault (by simp) hgt (by gas_ok)

/-- From 8648, with `v ≤ A < MAX_UINT` (`A` the allowance), in a static frame or with no account
for `C`: the run reaches the `SSTORE` of the allowance, which is `Stuck`. -/
theorem bodyAllowBad (hfork : .berlin ≤ fork)
    (hbad : message.isStatic = true ∨ ¬hasAccount state message.currentTarget)
    {v t f sel : U256} {M : ByteArray} (hM : M.size = 96)
    (hov : v.toNat * (storageAt state message.currentTarget 3).toNat < 2 ^ 256)
    (hmax : allowOf state message f ≠ MAX_UINT) (hle : v.toNat ≤ (allowOf state message f).toNat)
    {cA c3 c4 : Bool}
    (hcA : coldIn substate message.currentTarget (allowFrom message f) = cA)
    (hc3 : coldIn (accessSlot substate message.currentTarget (allowFrom message f))
      message.currentTarget 3 = c3)
    (hc4 : coldIn (accessSlot (accessSlot substate message.currentTarget (allowFrom message f))
      message.currentTarget 3) message.currentTarget 4 = c4)
    {gas : Nat}
    (hg : 2000 + slotCost cA + slotCost c3 + slotCost c4 + mulCost v +
      capCost (rawFee state message v) (storageAt state message.currentTarget 4) ≤ gas) :
    Gas.HoareG fork (At CODE message 8648 [0x60, 0, 0, 0, v, t, f, 0x1097, v, t, f, 0x0392, sel] M
        gas state substate) Gas.Stuck := by
  simp only [rawFee, allowOf] at hg hmax hle
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
  refine allowStepBad (state := readsF state message f) ?_ hbad hmax hle ?_ (size_allowMem hM f)
  · simp
  · gas_ok

/-- From 8648, with the allowance `MAX_UINT` (nothing written), `fee ≤ v` and
`v ≤ balances[_from]`, in a static frame or with no account for `C`: the run reaches the
`SSTORE` of `balances[_from]`, which is `Stuck`. -/
theorem bodyDebitBad (hfork : .berlin ≤ fork)
    (hbad : message.isStatic = true ∨ ¬hasAccount state message.currentTarget)
    {v t f sel : U256} {M : ByteArray} (hM : M.size = 96)
    (hov : v.toNat * (storageAt state message.currentTarget 3).toNat < 2 ^ 256)
    (hfv : (feeOf state message v).toNat ≤ v.toNat)
    (hmax : allowOf state message f = MAX_UINT)
    (hbal : v.toNat ≤ (balFrom state message v f).toNat)
    {cA c3 c4 cF : Bool}
    (hcA : coldIn substate message.currentTarget (allowFrom message f) = cA)
    (hc3 : coldIn (accessSlot substate message.currentTarget (allowFrom message f))
      message.currentTarget 3 = c3)
    (hc4 : coldIn (accessSlot (accessSlot substate message.currentTarget (allowFrom message f))
      message.currentTarget 3) message.currentTarget 4 = c4)
    (hcF : coldIn (allowedSubF fork substate state message v f) message.currentTarget
      (recipientSlot f) = cF)
    {gas : Nat}
    (hg : 4000 + slotCost cA + slotCost c3 + slotCost c4 + slotCost cF + mulCost v +
      capCost (rawFee state message v) (storageAt state message.currentTarget 4) +
      allowCostF fork state message v f ≤ gas) :
    Gas.HoareG fork (At CODE message 8648 [0x60, 0, 0, 0, v, t, f, 0x1097, v, t, f, 0x0392, sel] M
        gas state substate) Gas.Stuck := by
  have hbad' : message.isStatic = true ∨
      ¬hasAccount (allowedF state message v f) message.currentTarget := by
    have h : allowedF state message v f = readsF state message f := by
      unfold allowedF allowState
      split
      · rfl
      · contradiction
    rw [h]; exact hbad
  simp only [allowCostF, rawFee, feeOf, allowOf, balFrom, allowedF, readsF, allowedSubF,
    accessF] at hg hfv hbal hmax hcF hbad'
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
  step allowStep hfork (by simp) (by simp only [storageAt_readSlot]) (Or.inl hmax)
    (fun h => absurd hmax h)
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
  refine debitStoreFBad (state := readSlot (allowState (readSlot (readSlot (readSlot state
    message.currentTarget (allowFrom message f)) message.currentTarget 3) message.currentTarget 4)
    message.currentTarget (allowFrom message f)
    (storageAt state message.currentTarget (allowFrom message f)) v) message.currentTarget
    (recipientSlot f)) ?_ hbad' ?_ (size_mapMem hMb _ _)
  · simp
  · gas_ok

/-- From 8648, `balances[_to]` (read after the write of `_from`) plus `v - fee` overflows:
INVALID at the `add`. -/
theorem bodyToOvF (hfork : .berlin ≤ fork)
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
    Gas.SpecG fork (At CODE message 8648 [0x60, 0, 0, 0, v, t, f, 0x1097, v, t, f, 0x0392, sel] M gas
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
  step allowStep hfork (by simp) (by simp only [storageAt_readSlot]) hallow
    (fun _ => ⟨hstatic, hacc3⟩)
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
  step debitStore hfork (by simp) hstatic hacc4 (coldIn_accessSlot_self _ _ _)
    (by simp only [storageAt_readSlot, originalAt_readSlot, horig]; gas_ok) (size_mapMem hMb _ _)
  simp only [storageAt_readSlot, originalAt_readSlot, horig]
  step creditCall hfork (by simp) (cT := cT) (by rw [coldIn_storeSub]; exact hcT) (by gas_ok)
    (size_mapMem (size_mapMem hMb _ _) _ _)
  exact addFault (by simp) hto (by gas_ok)

/-- From 8648, with a fee above 0 and the transfer to `_to` done, `balances[owner]` (read after
the write of `_to`) plus the fee overflows: INVALID at the owner's `add`. -/
theorem bodyOwnerOvF (hfork : .berlin ≤ fork)
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
    Gas.SpecG fork (At CODE message 8648 [0x60, 0, 0, 0, v, t, f, 0x1097, v, t, f, 0x0392, sel] M gas
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
  have hA := headF (sel := sel) hfork hstatic hacc hM hov hfee hfv hallow hbal hto hcA hc3
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

Hypotheses: Berlin ≤ fork (Glamsterdam included); the checks pass (call data ≥ 100 bytes, not
paused, `f` not blacklisted, not deprecated); `v * rate < 2^256`; `A = MAX_UINT ∨ v ≤ A`; when
`A ≠ MAX_UINT`, not static and the contract has an account (`hgood`; the allowance is then
written); `v < fee`; more than 2300 gas left at the allowance's SSTORE, which also
covers the rest of the path.

Then INVALID at `sub(v, fee)`, after the allowance step (`A - v` written unless `A = MAX_UINT`). -/
theorem spec_feeGtF (hfork : .berlin ≤ fork)
    (hlong : 100 ≤ message.data.size) (hsz : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x23b872dd) (hv : message.value = 0)
    (hnp : byte20 (storageAt state message.currentTarget 0) = 0)
    (hnb : (storageAt state message.currentTarget (blackFrom (fromArg message))).toNat % 256 = 0)
    (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    (hov : (valArg message).toNat *
      (storageAt (checkState state message) message.currentTarget 3).toNat < 2 ^ 256)
    (hallow : allowOf (checkState state message) message (fromArg message) = MAX_UINT ∨
      (valArg message).toNat ≤ (allowOf (checkState state message) message (fromArg message)).toNat)
    (hgood : allowOf (checkState state message) message (fromArg message) ≠ MAX_UINT →
      message.isStatic = false ∧ hasAccount state message.currentTarget)
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
    Gas.SpecG fork (At CODE message 0 [] .empty gas state substate)
      (Faulted (.invalidOpcode 0xfe) (allowedF (checkState state message) message (valArg message) (fromArg message))
        (allowedSubF fork (checkSub substate message) (checkState state message) message (valArg message)
          (fromArg message))) :=
  Triple.seq (preF hfork hlong hsz hsel hv hnp hnb hdep hc0 hcB hc10
      (Nat.le_trans (Nat.le_add_right _ _) hg))
    (bodyFeeGtF hfork (size_mapMem size_MEM0 _ _) hov hgt hallow
      (fun h => ⟨(hgood h).1,
      hasAccount_readSlot (hasAccount_readSlot (hasAccount_readSlot (hgood h).2))⟩) hcA hc3 hc4
      (Nat.le_sub_of_add_le (by rw [Nat.add_comm]; exact hg)))

/-- `transferFrom(f, t, v)`, not deprecated, with the checks passing, `v * rate < 2^256` and
`v ≤ A < MAX_UINT` (`A` the allowance), in a static frame or with no account for `C`: the run
reaches the `SSTORE` of the allowance, which is `Stuck`. -/
theorem bad_allowF (hfork : .berlin ≤ fork)
    (hbad : message.isStatic = true ∨ ¬hasAccount state message.currentTarget)
    (hlong : 100 ≤ message.data.size) (hsz : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x23b872dd) (hv : message.value = 0)
    (hnp : byte20 (storageAt state message.currentTarget 0) = 0)
    (hnb : (storageAt state message.currentTarget (blackFrom (fromArg message))).toNat % 256 = 0)
    (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    (hov : (valArg message).toNat *
      (storageAt (checkState state message) message.currentTarget 3).toNat < 2 ^ 256)
    (hmax : allowOf (checkState state message) message (fromArg message) ≠ MAX_UINT)
    (hle : (valArg message).toNat ≤
      (allowOf (checkState state message) message (fromArg message)).toNat)
    {c0 cB c10 cA c3 c4 : Bool}
    (hc0 : coldIn substate message.currentTarget 0 = c0)
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
    {gas : Nat} (hg : preCostF c0 cB c10 + (2000 + slotCost cA + slotCost c3 + slotCost c4 +
      mulCost (valArg message) +
      capCost (rawFee (checkState state message) message (valArg message))
        (storageAt (checkState state message) message.currentTarget 4)) ≤ gas) :
    Gas.HoareG fork (At CODE message 0 [] .empty gas state substate) Gas.Stuck :=
  Triple.seq (preF hfork hlong hsz hsel hv hnp hnb hdep hc0 hcB hc10
      (Nat.le_trans (Nat.le_add_right _ _) hg))
    (bodyAllowBad (state := checkState state message) hfork hbad (size_mapMem size_MEM0 _ _) hov
      hmax hle hcA hc3 hc4 (Nat.le_sub_of_add_le (by rw [Nat.add_comm]; exact hg)))

/-- `transferFrom(f, t, v)`, not deprecated, with the checks passing, `v * rate < 2^256`, the
allowance `MAX_UINT`, `fee ≤ v` and `v ≤ balances[f]`, in a static frame or with no account for
`C`: the run reaches the `SSTORE` of `balances[f]`, which is `Stuck`. -/
theorem bad_transferFrom (hfork : .berlin ≤ fork)
    (hbad : message.isStatic = true ∨ ¬hasAccount state message.currentTarget)
    (hlong : 100 ≤ message.data.size) (hsz : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x23b872dd) (hv : message.value = 0)
    (hnp : byte20 (storageAt state message.currentTarget 0) = 0)
    (hnb : (storageAt state message.currentTarget (blackFrom (fromArg message))).toNat % 256 = 0)
    (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    (hov : (valArg message).toNat *
      (storageAt (checkState state message) message.currentTarget 3).toNat < 2 ^ 256)
    (hfv : (feeOf (checkState state message) message (valArg message)).toNat ≤
      (valArg message).toNat)
    (hmax : allowOf (checkState state message) message (fromArg message) = MAX_UINT)
    (hbal : (valArg message).toNat ≤
      (balFrom (checkState state message) message (valArg message) (fromArg message)).toNat)
    {c0 cB c10 cA c3 c4 cF : Bool}
    (hc0 : coldIn substate message.currentTarget 0 = c0)
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
    {gas : Nat} (hg : preCostF c0 cB c10 + (4000 + slotCost cA + slotCost c3 + slotCost c4 +
      slotCost cF + mulCost (valArg message) +
      capCost (rawFee (checkState state message) message (valArg message))
        (storageAt (checkState state message) message.currentTarget 4) +
      allowCostF fork (checkState state message) message (valArg message) (fromArg message)) ≤
        gas) :
    Gas.HoareG fork (At CODE message 0 [] .empty gas state substate) Gas.Stuck :=
  Triple.seq (preF hfork hlong hsz hsel hv hnp hnb hdep hc0 hcB hc10
      (Nat.le_trans (Nat.le_add_right _ _) hg))
    (bodyDebitBad (state := checkState state message) hfork hbad (size_mapMem size_MEM0 _ _) hov
      hfv hmax hbal hcA hc3 hc4 hcF (Nat.le_sub_of_add_le (by rw [Nat.add_comm]; exact hg)))

/-- `transferFrom(f, t, v)`, not deprecated, with the checks of `spec_ok` passing (a fee of 0), a
frame that may write and an account for `C`, the gas of the whole success path (`hg`) but at most
2300 gas left at the `SSTORE` of `balances[t]` (`hlow`): the run reaches it, and it is
`Stuck`. -/
theorem low_transferFrom2 (hfork : .berlin ≤ fork)
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
    {gas : Nat} (hg : okCostF fork state message c0 cB c10 cA c3 c4 cF cT ≤ gas)
    (hlow : gas < stipCostF fork state message c0 cB c10 cA c3 c4 cF cT) :
    Gas.HoareG fork (At CODE message 0 [] .empty gas state substate) Gas.Stuck :=
  Triple.seq (preF hfork hlong hsz hsel hv hnp hnb hdep hc0 hcB hc10
      (Nat.le_trans (Nat.le_add_right _ _) hg))
    (bodyLow2F (state := checkState state message) (substate := checkSub substate message)
      hfork hstatic (hasAccount_readSlot (hasAccount_readSlot (hasAccount_readSlot hacc)))
      (size_mapMem size_MEM0 (mkey (fromArg message)) 6) hov hfee hallow hbal hto hcA hc3 hc4 hcF
      hcT (Nat.le_sub_of_add_le (by rw [Nat.add_comm]; exact hg))
      (by simp only [stipCostF] at hlow; omega))

/-- The specification of `transferFrom(f, t, v)` when `balances[t] + (v - fee)` overflows.

Hypotheses: as `spec_feeGtF` up to the allowance, with a frame that is not static and an account
for `C` (`hstatic`, `hacc`); `fee ≤ v`; `v ≤ balances[f]` (read after the
allowance step); `balances[t] + (v - fee) ≥ 2^256` (read after the write of `f`); more than 2300
gas left at the SSTORE of `balances[f]` (`hstip`), and enough gas to reach the assert.

Then INVALID at the `add`, after the allowance step and the write `balances[f] := balF - v`. -/
theorem spec_toOvF (hfork : .berlin ≤ fork)
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
    Gas.SpecG fork (At CODE message 0 [] .empty gas state substate)
      (Faulted (.invalidOpcode 0xfe)
        (readSlot (debitedF (checkState state message) message (valArg message) (fromArg message))
          message.currentTarget (recipientSlot (toArg message)))
        (accessSlot (debitedSubF fork (checkSub substate message) (checkState state message) message
          (valArg message) (fromArg message)) message.currentTarget (recipientSlot (toArg message)))) :=
  Triple.seq (preF hfork hlong hsz hsel hv hnp hnb hdep hc0 hcB hc10
      (Nat.le_trans (Nat.le_add_right _ _) hg))
    (bodyToOvF hfork hstatic (hasAccount_readSlot (hasAccount_readSlot (hasAccount_readSlot hacc)))
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
theorem spec_ownerOvF (hfork : .berlin ≤ fork)
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
    Gas.SpecG fork (At CODE message 0 [] .empty gas state substate)
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
    (bodyOwnerOvF hfork hstatic (hasAccount_readSlot (hasAccount_readSlot (hasAccount_readSlot hacc)))
      (size_mapMem size_MEM0 _ _) hov hfee hfv hallow hbal hto hown
      (coldIn_accessSlot_false (coldIn_accessSlot_false (coldIn_accessSlot_self _ _ _)))
      hcA hc3 hc4 hcF hcT hcO
      (Nat.le_sub_of_add_le (by rw [Nat.add_comm]; exact hstip))
      (Nat.le_sub_of_add_le (by rw [Nat.add_comm]; exact hg)))

/-- The loop of the interpreter runs the case of `spec_feeGtF` to its end condition. It holds for
every bound on the gas of messages and every runner of messages. -/
theorem runFrame_feeGtF (hfork : .berlin ≤ fork)
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
  (spec_feeGtF hfork hlong hsz hsel hv hnp hnb hdep hov hallow (fun _ => ⟨hstatic, hacc⟩) hgt hc0
    hcB hc10 hcA hc3 hc4 hg).runFrame start within

/-- The loop of the interpreter runs the case of `spec_toOvF` to its end condition. It holds for
every bound on the gas of messages and every runner of messages. -/
theorem runFrame_toOvF (hfork : .berlin ≤ fork)
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
  (spec_toOvF hfork hstatic hacc hlong hsz hsel hv hnp hnb hdep hov hallow hfv hbal hto hc0
    hcB hc10 hcA hc3 hc4 hcF hcT hstip hg).runFrame start within

/-- The loop of the interpreter runs the case of `spec_ownerOvF` to its end condition. It holds for
every bound on the gas of messages and every runner of messages. -/
theorem runFrame_ownerOvF (hfork : .berlin ≤ fork)
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
  (spec_ownerOvF hfork hstatic hacc hlong hsz hsel hv hnp hnb hdep hov hallow hfee hfv hbal
    hto hown hc0 hcB hc10 hcA hc3 hc4 hcF hcT hcO hstip hg).runFrame start within

end UsdtVerify.TransferFrom

end
