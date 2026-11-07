import UsdtVerify.Functions.TransferBody
import UsdtVerify.Functions.BalanceOf

/-!
# transfer(address,uint256): the success path, from pc 0, with a fee of 0

`spec_ok` / `runFrame_ok`: a `transfer(to, value)` call with at least 68 bytes of call data, not
paused, from a caller that is not blacklisted, not deprecated, whose fee (as the bytecode computes
it from `basisPointsRate` and `maximumFee`) is 0, with a sufficient balance and no overflow at the
recipient, stops normally after it moves `value` from `balances[msg.sender]` to `balances[to]`
and logs `Transfer(msg.sender, to, value)`.
-/

namespace UsdtVerify.TransferOk

open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts
open Transfer SafeMath

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate}

/-- The key word of the recipient is the recipient: argument word 0 is already masked. -/
theorem mkey_addrArg (data : ByteArray) : mkey (addrArg data 0) = addrArg data 0 := by
  simp only [mkey, addrArg, mask_mask]

/-- The recipient's slot is the slot that `balanceOf(to)` reads. -/
theorem recipientSlot_addrArg (data : ByteArray) :
    recipientSlot (addrArg data 0) = BalanceOf.balanceSlot data := by
  simp only [recipientSlot, mkey_addrArg]

theorem ptr_MEMK (k b : U256) : loadWord (memoryReadBytes (MEMK k b) 64 32) 0 32 = 0x60 :=
  ptr_mapMem size_MEM0 mload_MEM0 k b

/-- The gas of the path before 9883, besides the reads of slots 0, 10 and the blacklist slot. -/
abbrev PRE_COST : Nat := 1034

/-- The whole gas of the success path with a fee of 0: 3863 and the prices of the seven reads
and the two writes, the extra price of `mul` when `value ≠ 0`, and of the cap when it applies. -/
abbrev okCost (fork : Fork) (state : State.TransactionState) (message : Message fork)
    (c0 cB c10 c3 c4 cS cT : Bool) : Nat :=
  PRE_COST + slotCost c0 + slotCost cB + slotCost c10 + (2829 + readCost c3 c4 cS cT +
    mulCost (wordArg message.data 1) +
    capCost (rawFee (shortState state message) message (wordArg message.data 1))
      (storageAt (shortState state message) message.currentTarget 4) +
    debitCost fork (shortState state message) message (wordArg message.data 1) +
    creditCost fork (shortState state message) message (wordArg message.data 1)
      (addrArg message.data 0))

/-- The specification of a successful `transfer(address,uint256)` call with a fee of 0.

Write `C` for the contract, `v` for argument word 1 (the value), `a` for argument word 0 masked to
160 bits (the recipient), `S` for the state after the reads of the checks (slot 0, the blacklist
slot, slot 10; reads change no word).

Hypotheses: Berlin ≤ fork < Glamsterdam (the SSTORE rule of the logic); a frame that may write
(not static) of an existing account `C`; call data of 68 to 2^256 - 1 bytes with selector
0xa9059cbb; no value; not paused (byte 20 of slot 0 is 0); the caller not blacklisted (low byte of
`isBlackListed[caller]` is 0); not deprecated (byte 20 of slot 10 is 0); `v * basisPointsRate`
does not overflow (SafeMath's `mul` assert); the fee `min(v * rate / 10000, maximumFee)` is 0; the
sender's balance (slot `keccak(caller ++ 2)`) is at least `v`; the recipient's balance, read
after the sender's write, plus `v` does not overflow; and enough gas: all of it, and more than the
stipend of 2300 at each SSTORE (EIP-2200).

Then the run stops normally (STOP), with gas left `gas - okCost`, the state `credited S` (sender's
slot := balance - v, then recipient's slot := its balance after that write + v), and the substate
with both slots accessed, the refunds of both writes, and the log
`Transfer(caller, a, v)` (topic 0xddf252ad…, data the 32 bytes of `v`) appended. -/
theorem spec_ok (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    (hstatic : message.isStatic = false) (hacc : hasAccount state message.currentTarget)
    (hlong : 68 ≤ message.data.size) (hsz : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0xa9059cbb) (hv : message.value = 0)
    (hnp : byte20 (storageAt state message.currentTarget 0) = 0)
    (hnb : (storageAt state message.currentTarget (blackSlot message)).toNat % 256 = 0)
    (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    (hov : (wordArg message.data 1).toNat *
      (storageAt (shortState state message) message.currentTarget 3).toNat < 2 ^ 256)
    (hfee : feeOf (shortState state message) message (wordArg message.data 1) = 0)
    (hbal : (wordArg message.data 1).toNat ≤ (balS (shortState state message) message).toNat)
    (hto : (balT (shortState state message) message (wordArg message.data 1)
      (addrArg message.data 0)).toNat + (wordArg message.data 1).toNat < 2 ^ 256)
    {c0 cB c10 c3 c4 cS cT : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
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
    {gas : Nat}
    (hstip1 : PRE_COST + slotCost c0 + slotCost cB + slotCost c10 + (530 + slotCost c3 +
      slotCost c4 + slotCost cS + mulCost (wordArg message.data 1) +
      capCost (rawFee (shortState state message) message (wordArg message.data 1))
        (storageAt (shortState state message) message.currentTarget 4) + 2400) ≤ gas)
    (hstip2 : PRE_COST + slotCost c0 + slotCost cB + slotCost c10 + (837 + readCost c3 c4 cS cT +
      mulCost (wordArg message.data 1) +
      capCost (rawFee (shortState state message) message (wordArg message.data 1))
        (storageAt (shortState state message) message.currentTarget 4) +
      debitCost fork (shortState state message) message (wordArg message.data 1) + 2401) ≤ gas)
    (hg : okCost fork state message c0 cB c10 c3 c4 cS cT ≤ gas) :
    Spec fork (At CODE message 0 [] .empty gas state substate)
      (Halted false .empty (gas - okCost fork state message c0 cB c10 c3 c4 cS cT)
        (credited (shortState state message) message (wordArg message.data 1)
          (addrArg message.data 0))
        (loggedSub fork (shortSubstate substate message) (shortState state message) message
          (wordArg message.data 1) (addrArg message.data 0))) := by
  have hB := body (state := shortState state message) (substate := shortSubstate substate message)
    (sel := BitVec.ofNat 256 (selector message.data))
    (gas := gas - (PRE_COST + slotCost c0 + slotCost cB + slotCost c10))
    hfork hglam hlong hsz hstatic
    (hasAccount_readSlot (hasAccount_readSlot (hasAccount_readSlot hacc)))
    (size_MEMK (callerKey message) 6) (ptr_MEMK _ _) hov hfee hbal hto hc3 hc4 hcS hcT
    (Nat.le_sub_of_add_le (by rw [Nat.add_comm]; exact hstip1))
    (Nat.le_sub_of_add_le (by rw [Nat.add_comm]; exact hstip2))
    (Nat.le_sub_of_add_le (by rw [Nat.add_comm]; exact hg))
  have hpre : PRE_COST + slotCost c0 + slotCost cB + slotCost c10 ≤ gas :=
    Nat.le_trans (Nat.le_add_right _ _) hg
  clear hov hfee hbal hto hstip1 hstip2 hg
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
  step entry hv (by gas_ok)
  step notPaused hfork (by simp) hnp hc0 (by gas_ok)
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

/-- The loop of the interpreter runs a successful `transfer` call with a fee of 0 to its
specification. It holds for every bound on the gas of messages and every runner of messages. -/
theorem runFrame_ok (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    (hstatic : message.isStatic = false) (hacc : hasAccount state message.currentTarget)
    (hlong : 68 ≤ message.data.size) (hsz : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0xa9059cbb) (hv : message.value = 0)
    (hnp : byte20 (storageAt state message.currentTarget 0) = 0)
    (hnb : (storageAt state message.currentTarget (blackSlot message)).toNat % 256 = 0)
    (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    (hov : (wordArg message.data 1).toNat *
      (storageAt (shortState state message) message.currentTarget 3).toNat < 2 ^ 256)
    (hfee : feeOf (shortState state message) message (wordArg message.data 1) = 0)
    (hbal : (wordArg message.data 1).toNat ≤ (balS (shortState state message) message).toNat)
    (hto : (balT (shortState state message) message (wordArg message.data 1)
      (addrArg message.data 0)).toNat + (wordArg message.data 1).toNat < 2 ^ 256)
    {c0 cB c10 c3 c4 cS cT : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
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
    {gas : Nat}
    (hstip1 : PRE_COST + slotCost c0 + slotCost cB + slotCost c10 + (530 + slotCost c3 +
      slotCost c4 + slotCost cS + mulCost (wordArg message.data 1) +
      capCost (rawFee (shortState state message) message (wordArg message.data 1))
        (storageAt (shortState state message) message.currentTarget 4) + 2400) ≤ gas)
    (hstip2 : PRE_COST + slotCost c0 + slotCost cB + slotCost c10 + (837 + readCost c3 c4 cS cT +
      mulCost (wordArg message.data 1) +
      capCost (rawFee (shortState state message) message (wordArg message.data 1))
        (storageAt (shortState state message) message.currentTarget 4) +
      debitCost fork (shortState state message) message (wordArg message.data 1) + 2401) ≤ gas)
    (hg : okCost fork state message c0 cB c10 c3 c4 cS cT ≤ gas) {bound : Nat}
    {runChild : MessageRunner fork Nat bound} {evm : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    ∃ stopped, runFrame (step fork) (step_decreases fork) bound runChild evm within =
      .ok stopped ∧
      Halted false .empty (gas - okCost fork state message c0 cB c10 c3 c4 cS cT)
        (credited (shortState state message) message (wordArg message.data 1)
          (addrArg message.data 0))
        (loggedSub fork (shortSubstate substate message) (shortState state message) message
          (wordArg message.data 1) (addrArg message.data 0)) stopped :=
  (spec_ok hfork hglam hstatic hacc hlong hsz hsel hv hnp hnb hdep hov hfee hbal hto hc0 hcB hc10
    hc3 hc4 hcS hcT hstip1 hstip2 hg).runFrame start within

end UsdtVerify.TransferOk
