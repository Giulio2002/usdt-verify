import UsdtVerify.Functions.TransferFromBody

/-!
# transferFrom(address,address,uint256): the success path, from pc 0, with a fee of 0

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

Hypotheses: Berlin ≤ fork < Glamsterdam; not static; `C` has an account; call data of 100 to
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
theorem spec_ok (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
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
    Spec fork (At CODE message 0 [] .empty gas state substate)
      (Local.Stopped (gas - okCostF fork state message c0 cB c10 cA c3 c4 cF cT)
        (creditedF (checkState state message) message (valArg message) (toArg message)
          (fromArg message))
        (loggedSubF fork (checkSub substate message) (checkState state message) message
          (valArg message) (toArg message) (fromArg message))) := by
  have hB := body (state := checkState state message) (substate := checkSub substate message)
    (sel := BitVec.ofNat 256 (selector message.data))
    (gas := gas - (PRE_COST_F + slotCost c0 + slotCost cB + slotCost c10))
    hfork hglam hstatic
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
  refine Spec.seq h1 ?_
  step entry hv (by gas_ok)
  step notPaused hfork (by simp) hnp hc0 (by gas_ok)
  step notBlack hfork (by simp) hcB (by rw [storageAt_readSlot]; exact hnb) (by gas_ok) size_MEM0
  step notDeprecated hfork (by simp) (by rw [storageAt_readSlot, storageAt_readSlot]; exact hdep)
    hc10 (by gas_ok)
  step toStandard (by gas_ok)
  step payload hlong hsz (by simp) (by gas_ok)
  step reshape (g' := gas - (795 + slotCost c0 + slotCost cB + slotCost c10)) rfl rfl (by gas_ok)
  refine hB.consequence (fun _ h => h) ?_
  rintro evm ⟨hr, he, hgas, hs, hss⟩
  exact ⟨hr, he, by rw [hgas, Nat.sub_sub], hs, hss⟩

/-- The loop of the interpreter runs a successful `transferFrom` call with a fee of 0 to its
specification. It holds for every bound on the gas of messages and every runner of messages. -/
theorem runFrame_ok (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
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
      Local.Stopped (gas - okCostF fork state message c0 cB c10 cA c3 c4 cF cT)
        (creditedF (checkState state message) message (valArg message) (toArg message)
          (fromArg message))
        (loggedSubF fork (checkSub substate message) (checkState state message) message
          (valArg message) (toArg message) (fromArg message)) stopped :=
  (spec_ok hfork hglam hstatic hacc hlong hsz hsel hv hnp hnb hdep hov hfee hallow hbal hto hc0 hcB
    hc10 hcA hc3 hc4 hcF hcT hstip hg).runFrame start within

end UsdtVerify.TransferFrom
