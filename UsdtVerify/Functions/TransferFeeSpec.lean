import UsdtVerify.Functions.TransferFeeBody

/-!
# transfer(address,uint256): the success path, from pc 0, with a fee above 0

`spec_fee` / `runFrame_fee`: as `TransferOk.spec_ok`, but the fee `fee` that the bytecode computes
(`min(v * basisPointsRate / 10000, maximumFee)`) is not 0. Then `v - fee` goes to `_to`, `fee`
goes to `balances[owner]` (owner = low 160 bits of slot 0), and two logs are appended:
`Transfer(caller, owner', fee)` then `Transfer(caller, _to, v - fee)`.
-/

namespace UsdtVerify.TransferFee

open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts
open Transfer SafeMath TransferOk TransferFrom

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate}

/-- The whole gas of the success path with a fee above 0. -/
abbrev feeCost (fork : Fork) (state : State.TransactionState) (message : Message fork)
    (c0 cB c10 c3 c4 cS cT cO : Bool) : Nat :=
  PRE_COST + slotCost c0 + slotCost cB + slotCost c10 + (5373 + readCost c3 c4 cS cT +
    slotCost cO + mulCost (wordArg message.data 1) +
    capCost (rawFee (shortState state message) message (wordArg message.data 1))
      (storageAt (shortState state message) message.currentTarget 4) +
    debitCost fork (shortState state message) message (wordArg message.data 1) +
    creditCostFee fork (shortState state message) message (wordArg message.data 1)
      (addrArg message.data 0) +
    ownerCost fork (shortState state message) message (wordArg message.data 1)
      (addrArg message.data 0))

/-- The specification of a successful `transfer(address,uint256)` call with a fee above 0.

Write `v` for argument word 1, `a` for argument word 0 masked, `S` for the state after the reads of
the checks, `fee = feeOf S v`. Hypotheses as for `TransferOk.spec_ok`, with `fee ≠ 0` in place of
`fee = 0`, and: `fee ≤ v` (SafeMath `sub` of `sendAmount`); the recipient's balance (read after the
sender's write) plus `v - fee` does not overflow; the owner's balance (read after the recipient's
write) plus `fee` does not overflow. No stipend hypothesis is needed: the logs that follow each
SSTORE cost more than 2300.

Then the run stops normally with gas left `gas - feeCost`, the state `feeState S` (sender := balS -
v; recipient := balT + (v - fee); owner := balO + fee; slot 0 read where the code reads it), and
the substate `feeSub` with both logs. -/
theorem spec_fee (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
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
    {gas : Nat} (hg : feeCost fork state message c0 cB c10 c3 c4 cS cT cO ≤ gas) :
    Spec fork (At CODE message 0 [] .empty gas state substate)
      (Halted false .empty (gas - feeCost fork state message c0 cB c10 c3 c4 cS cT cO)
        (feeState (shortState state message) message (wordArg message.data 1)
          (addrArg message.data 0))
        (feeSub fork (shortSubstate substate message) (shortState state message) message
          (wordArg message.data 1) (addrArg message.data 0))) := by
  have hB := bodyFee (state := shortState state message)
    (substate := shortSubstate substate message)
    (sel := BitVec.ofNat 256 (selector message.data))
    (gas := gas - (PRE_COST + slotCost c0 + slotCost cB + slotCost c10))
    hfork hglam hlong hsz hstatic
    (hasAccount_readSlot (hasAccount_readSlot (hasAccount_readSlot hacc)))
    (size_MEMK (callerKey message) 6) (ptr_MEMK _ _) hov hfee hfv hbal hto hown
    (coldIn_accessSlot_false (coldIn_accessSlot_false (coldIn_accessSlot_self _ _ _)))
    hc3 hc4 hcS hcT hcO
    (Nat.le_sub_of_add_le (by rw [Nat.add_comm]; exact hg))
  have hpre : PRE_COST + slotCost c0 + slotCost cB + slotCost c10 ≤ gas :=
    Nat.le_trans (Nat.le_add_right _ _) hg
  clear hov hfee hfv hbal hto hown hg
  simp only [PRE_COST] at hpre hB
  have ht : tested (BitVec.ofNat 256 (selector message.data)) ENTRIES = 22 := by
    rw [hsel]; decide
  have hb : branch (BitVec.ofNat 256 (selector message.data)) 54 (entrySize 4 2) ENTRIES =
      1866 := by
    rw [hsel]; decide
  have h1 := dispatch (state := state) (substate := substate) (by omega) hsz (gas := gas)
    (by rw [ht]; gas_ok)
  rw [ht, hb] at h1
  refine Spec.seq h1 ?_
  step Transfer.entry hv (by gas_ok)
  step Transfer.notPaused hfork (by simp) hnp hc0 (by gas_ok)
  step blackLookup hfork (by simp) hcB (by gas_ok)
  step jumpiR (blackTest_ne (by rw [storageAt_readSlot]; exact hnb))
  step repc (pc' := 5481) (by decide)
  step depInline hfork (by simp) (by rw [storageAt_readSlot, storageAt_readSlot]; exact hdep) hc10
    (by gas_ok)
  step toBasic (by gas_ok)
  step reshape (g' := gas - (1034 + slotCost c0 + slotCost cB + slotCost c10)) rfl rfl (by gas_ok)
  refine hB.consequence (fun _ h => h) ?_
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  exact ⟨hr, he, ho, by rw [hgas, Nat.sub_sub], hs, hss⟩

/-- The loop of the interpreter runs a successful `transfer` call with a fee above 0 to its
specification, for every bound on the gas of messages and every runner of messages. -/
theorem runFrame_fee (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
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
    {gas : Nat} (hg : feeCost fork state message c0 cB c10 c3 c4 cS cT cO ≤ gas) {bound : Nat}
    {runChild : MessageRunner fork Nat bound} {evm : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    ∃ stopped, runFrame (step fork) (step_decreases fork) bound runChild evm within =
      .ok stopped ∧
      Halted false .empty (gas - feeCost fork state message c0 cB c10 c3 c4 cS cT cO)
        (feeState (shortState state message) message (wordArg message.data 1)
          (addrArg message.data 0))
        (feeSub fork (shortSubstate substate message) (shortState state message) message
          (wordArg message.data 1) (addrArg message.data 0)) stopped :=
  (spec_fee hfork hglam hstatic hacc hlong hsz hsel hv hnp hnb hdep hov hfee hfv hbal hto hown hc0
    hcB hc10 hc3 hc4 hcS hcT hcO hg).runFrame start within

end UsdtVerify.TransferFee
