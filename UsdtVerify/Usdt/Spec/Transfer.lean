import UsdtVerify.Usdt.Proofs.Fee
import UsdtVerify.Usdt.Spec.BalanceOf
import EthLib.Execution.Proofs.Evm.Logic.Fault

/-!
# transfer(address,uint256): the specifications from pc 0

Proves what a call of transfer does from pc 0, not deprecated: the reverts, the success paths
with a fee of 0 and above 0, and the failed SafeMath asserts.

The blocks are in Usdt/Proofs/Transfer.lean and Usdt/Proofs/Fee.lean.

The parts below keep their own headers:

- transfer(address,uint256): the reverts before the body
- transfer(address,uint256): the success path, from pc 0, with a fee of 0
- SafeMath asserts that fail, and `transfer` with an insufficient balance
- transfer(address,uint256): the success path, from pc 0, with a fee above 0
- transfer(address,uint256): the failed SafeMath asserts (INVALID)
-/

section

/-!
## transfer(address,uint256): the reverts before the body

- `spec_paused`: the revert while paused.
- `spec_blacklisted`: the revert for a blacklisted caller.
- `spec_short`: the revert for call data shorter than 68 bytes.
-/

namespace UsdtVerify.Transfer

open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate}

/-- The gas of the paused path, besides the read of slot 0. -/
abbrev PAUSED_COST : Nat := 762

/-- The specification of a `transfer(address,uint256)` call while paused, from Berlin.

The call data starts with the selector 0xa9059cbb and has at least 4 bytes, the call has no
value, and byte 20 of slot 0 (the `paused` flag) is not 0.

Then the run reverts with no output, after reading slot 0 (762 gas and the price of the read). -/
theorem spec_paused (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xa9059cbb)
    (hv : message.value = 0) (hpaused : byte20 (storageAt state message.currentTarget 0) ≠ 0)
    {c0 : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0) {gas : Nat}
    (hg : PAUSED_COST + slotCost c0 ≤ gas) :
    Gas.SpecG fork (At CODE message 0 [] .empty gas state substate)
      (Halted true .empty (gas - (PAUSED_COST + slotCost c0))
        (readSlot state message.currentTarget 0) (accessSlot substate message.currentTarget 0)) := by
  simp only [PAUSED_COST] at hg ⊢
  have ht : tested (BitVec.ofNat 256 (selector message.data)) ENTRIES = 22 := by
    rw [hsel]; decide
  have hb : branch (BitVec.ofNat 256 (selector message.data)) 54 (entrySize 4 2) ENTRIES =
      1866 := by
    rw [hsel]; decide
  have h1 := dispatch (state := state) (substate := substate) hsize hsize' (gas := gas)
    (by rw [ht]; gas_ok)
  rw [ht, hb] at h1
  have h2 := entry (state := state) (substate := substate) hv
    (x := BitVec.ofNat 256 (selector message.data)) (gas := gas - 62 - 22 * 22) (by gas_ok)
  have h3 := pausedRevert (message := message) (state := state) (substate := substate) hfork
    (rest := [wordArg message.data 1, addrArg message.data 0, 0x078a,
      BitVec.ofNat 256 (selector message.data)]) (by simp) hpaused hc0
    (gas := gas - 62 - 22 * 22 - 98) (by gas_ok)
  refine Gas.SpecG.seq (h1.seq h2) (h3.consequence (fun _ h => h) ?_)
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  exact ⟨hr, he, ho, by rw [hgas]; gas_ok, hs, hss⟩

/-- The gas of the blacklisted path, besides the reads of slot 0 and of the blacklist slot. -/
abbrev BLACK_COST : Nat := 913

/-- The specification of a `transfer(address,uint256)` call from a blacklisted caller, from Berlin.

The call data starts with the selector 0xa9059cbb and has at least 4 bytes, the call has no
value, and byte 20 of slot 0 (the `paused` flag) is 0.

The low byte of the slot `keccak256(c ++ w6)` is not 0, where `c` is the caller's address as a
word and `w6` is the word 6 (the `isBlackListed` mapping at base slot 6).

Then the run reverts with no output, after reading slot 0 and that slot; `cB` is whether the
blacklist slot is cold once slot 0 has been accessed. -/
theorem spec_blacklisted (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xa9059cbb)
    (hv : message.value = 0) (hnp : byte20 (storageAt state message.currentTarget 0) = 0)
    (hblack : (storageAt state message.currentTarget (blackSlot message)).toNat % 256 ≠ 0)
    {c0 cB : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hcB : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget
      (blackSlot message) = cB)
    {gas : Nat} (hg : BLACK_COST + slotCost c0 + slotCost cB ≤ gas) :
    Gas.SpecG fork (At CODE message 0 [] .empty gas state substate)
      (Halted true .empty (gas - (BLACK_COST + slotCost c0 + slotCost cB))
        (readSlot (readSlot state message.currentTarget 0) message.currentTarget (blackSlot message))
        (accessSlot (accessSlot substate message.currentTarget 0) message.currentTarget
          (blackSlot message))) := by
  simp only [BLACK_COST] at hg ⊢
  have ht : tested (BitVec.ofNat 256 (selector message.data)) ENTRIES = 22 := by
    rw [hsel]; decide
  have hb : branch (BitVec.ofNat 256 (selector message.data)) 54 (entrySize 4 2) ENTRIES =
      1866 := by
    rw [hsel]; decide
  have h1 := dispatch (state := state) (substate := substate) hsize hsize' (gas := gas)
    (by rw [ht]; gas_ok)
  rw [ht, hb] at h1
  have h2 := entry (state := state) (substate := substate) hv
    (x := BitVec.ofNat 256 (selector message.data)) (gas := gas - 62 - 22 * 22) (by gas_ok)
  have h3 := notPaused (message := message) (state := state) (substate := substate) hfork
    (rest := [wordArg message.data 1, addrArg message.data 0, 0x078a,
      BitVec.ofNat 256 (selector message.data)]) (by simp) hnp hc0 (M := MEM0)
    (gas := gas - 62 - 22 * 22 - 98) (by gas_ok)
  have h4 := blackRevert (message := message) (state := readSlot state message.currentTarget 0)
    (substate := accessSlot substate message.currentTarget 0) hfork
    (rest := [wordArg message.data 1, addrArg message.data 0, 0x078a,
      BitVec.ofNat 256 (selector message.data)]) (by simp)
    (by rw [storageAt_readSlot]; exact hblack) hcB
    (gas := gas - 62 - 22 * 22 - 98 - (112 + slotCost c0)) (by gas_ok)
  refine Gas.SpecG.seq (h1.seq (h2.seq h3)) (h4.consequence (fun _ h => h) ?_)
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  exact ⟨hr, he, ho, by rw [hgas]; gas_ok, hs, hss⟩

/-- The gas of the short-payload path, besides the reads of slots 0, 10 and the blacklist slot. -/
abbrev SHORT_COST : Nat := 1094

/-- The state after the reads of the short-payload path: slot 0, the blacklist slot, slot 10. -/
abbrev shortState (state : State.TransactionState) (message : Message fork) :
    State.TransactionState :=
  readSlot (readSlot (readSlot state message.currentTarget 0) message.currentTarget
    (blackSlot message)) message.currentTarget 10

/-- The substate after the accesses of the short-payload path. -/
abbrev shortSubstate (substate : Substate) (message : Message fork) : Substate :=
  accessSlot (accessSlot (accessSlot substate message.currentTarget 0) message.currentTarget
    (blackSlot message)) message.currentTarget 10

/-- The specification of a `transfer(address,uint256)` call whose call data is too short.

The call data starts with the selector 0xa9059cbb and has from 4 to 67 bytes, the call has no
value, the contract is not paused (byte 20 of slot 0 is 0), the caller is not blacklisted (the low
byte of `isBlackListed[caller]` is 0), and the contract is not deprecated (byte 20 of slot 10 is 0).

Then the payload check of two argument words fails and the run reverts with no output.

`cB` and `c10` are the coldness of the blacklist slot and of slot 10 when the code reads them. -/
theorem spec_short (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hshort : message.data.size < 68) (hsel : selector message.data = 0xa9059cbb)
    (hv : message.value = 0) (hnp : byte20 (storageAt state message.currentTarget 0) = 0)
    (hnb : (storageAt state message.currentTarget (blackSlot message)).toNat % 256 = 0)
    (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    {c0 cB c10 : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hcB : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget
      (blackSlot message) = cB)
    (hc10 : coldIn (accessSlot (accessSlot substate message.currentTarget 0) message.currentTarget
      (blackSlot message)) message.currentTarget 10 = c10)
    {gas : Nat} (hg : SHORT_COST + slotCost c0 + slotCost cB + slotCost c10 ≤ gas) :
    Gas.SpecG fork (At CODE message 0 [] .empty gas state substate)
      (Halted true .empty (gas - (SHORT_COST + slotCost c0 + slotCost cB + slotCost c10))
        (shortState state message) (shortSubstate substate message)) := by
  simp only [SHORT_COST] at hg ⊢
  have hsize' : message.data.size < 2 ^ 256 := by omega
  have ht : tested (BitVec.ofNat 256 (selector message.data)) ENTRIES = 22 := by
    rw [hsel]; decide
  have hb : branch (BitVec.ofNat 256 (selector message.data)) 54 (entrySize 4 2) ENTRIES =
      1866 := by
    rw [hsel]; decide
  have h1 := dispatch (state := state) (substate := substate) hsize hsize' (gas := gas)
    (by rw [ht]; gas_ok)
  rw [ht, hb] at h1
  refine Gas.SpecG.seq h1 ?_
  step entry hv (by gas_ok)
  step notPaused hfork (by simp) hnp hc0 (by gas_ok)
  step blackLookup hfork (by simp) hcB (by gas_ok)
  step jumpiR (blackTest_ne (by rw [storageAt_readSlot]; exact hnb))
  step repc (pc' := 5481) (by decide)
  step depInline hfork (by simp) (by rw [storageAt_readSlot, storageAt_readSlot]; exact hdep) hc10
    (by gas_ok)
  step toBasic (by gas_ok)
  refine ((shortRevert hfork (by simp) hshort (by gas_ok) (size_MEMK _ _))).consequence
    (fun _ h => h) ?_
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  exact ⟨hr, he, ho, by rw [hgas]; gas_ok, hs, hss⟩

end UsdtVerify.Transfer

end

section

/-!
## transfer(address,uint256): the success path, from pc 0, with a fee of 0

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

Hypotheses: Berlin ≤ fork, Glamsterdam included (each write costs `writeCost`); a frame that may write
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
theorem spec_ok (hfork : .berlin ≤ fork)
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
    Gas.SpecG fork (At CODE message 0 [] .empty gas state substate)
      (Halted false .empty (gas - okCost fork state message c0 cB c10 c3 c4 cS cT)
        (credited (shortState state message) message (wordArg message.data 1)
          (addrArg message.data 0))
        (loggedSub fork (shortSubstate substate message) (shortState state message) message
          (wordArg message.data 1) (addrArg message.data 0))) := by
  have hB := body (state := shortState state message) (substate := shortSubstate substate message)
    (sel := BitVec.ofNat 256 (selector message.data))
    (gas := gas - (PRE_COST + slotCost c0 + slotCost cB + slotCost c10))
    hfork hlong hsz hstatic
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
  refine Gas.SpecG.seq h1 ?_
  step entry hv (by gas_ok)
  step notPaused hfork (by simp) hnp hc0 (by gas_ok)
  step blackLookup hfork (by simp) hcB (by gas_ok)
  step jumpiR (blackTest_ne (by rw [storageAt_readSlot]; exact hnb))
  step repc (pc' := 5481) (by decide)
  step depInline hfork (by simp) (by rw [storageAt_readSlot, storageAt_readSlot]; exact hdep) hc10
    (by gas_ok)
  step toBasic (by gas_ok)
  step Gas.reshapeG (g' := gas - (1034 + slotCost c0 + slotCost cB + slotCost c10)) rfl rfl (by gas_ok)
  refine hB.consequence (fun _ h => h) ?_
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  exact ⟨hr, he, ho, by rw [hgas, Nat.sub_sub], hs, hss⟩

/-- The loop of the interpreter runs a successful `transfer` call with a fee of 0 to its
specification. It holds for every bound on the gas of messages and every runner of messages. -/
theorem runFrame_ok (hfork : .berlin ≤ fork)
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
  (spec_ok hfork hstatic hacc hlong hsz hsel hv hnp hnb hdep hov hfee hbal hto hc0 hcB hc10
    hc3 hc4 hcS hcT hstip1 hstip2 hg).runFrame start within

end UsdtVerify.TransferOk

end

section

/-!
## SafeMath asserts that fail, and `transfer` with an insufficient balance

SafeMath's `assert` compiles to `JUMPI` over `INVALID` (0xfe). With EthLib's rule for INVALID
(#1250, `invalid_fe`), a failed assert halts the frame exceptionally: `Faulted`, with the error
`invalidOpcode 0xfe`, no output, no gas left, and the state and substate it had (the caller
discards them).

- `subFault`: `sub(a, b)` at 10976 with `a < b`.
- `addFault`: `add(a, b)` at 11001 with `a + b ≥ 2^256`.
- `spec_low`: `transfer(to, v)` with `balances[msg.sender] < v`.
-/

namespace UsdtVerify.SafeMath

open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate}

/-- `sub(a, b)` at 10976 with `a < b` fails its assert: INVALID at 10989, after 35 gas. -/
theorem subFault {a b ret : U256} {rest : List U256} (hrest : rest.length ≤ 20)
    (hlt : a.toNat < b.toNat) {gas : Nat} (hg : 35 ≤ gas) {M : ByteArray} :
    Gas.SpecG fork (At CODE message 10976 (b :: a :: ret :: rest) M gas state substate)
      (Faulted (.invalidOpcode 0xfe) state substate) := by
  have hgt : greaterThan b a = 1 := by simp [greaterThan, hlt]
  step jumpdestR
  step pushR 1 (0 : U256)
  step dupR 2
  step dupR 2
  step binR 0x11 (instruction_of_stackOnlyStep rfl)
  step unR 0x15 instruction_iszero
  step unR 0x15 instruction_iszero
  step unR 0x15 instruction_iszero
  step pushR 2 (0x2aee : U256)
  step jumpi0R (by rw [hgt]; decide)
  exact Gas.invalid_feG (by code_fact) (by code_fact)

/-- `add(a, b)` at 11001 with `a + b ≥ 2^256` fails its assert: INVALID at 11020, after 52 gas. -/
theorem addFault {a b ret : U256} {rest : List U256} (hrest : rest.length ≤ 20)
    (hov : 2 ^ 256 ≤ a.toNat + b.toNat) {gas : Nat} (hg : 52 ≤ gas) {M : ByteArray} :
    Gas.SpecG fork (At CODE message 11001 (b :: a :: ret :: rest) M gas state substate)
      (Faulted (.invalidOpcode 0xfe) state substate) := by
  have hlt : lessThan (add a b) a = 1 := by
    have h1 := a.isLt
    have h2 := b.isLt
    have : (add a b).toNat = a.toNat + b.toNat - 2 ^ 256 := by
      simp only [add, BitVec.toNat_add]
      rw [Nat.mod_eq_sub_mod hov, Nat.mod_eq_of_lt (by omega)]
    simp only [lessThan, this]
    rw [ite_eq_left (by omega)]
  step jumpdestR
  step pushR 1 (0 : U256)
  step dupR 0
  step dupR 2
  step dupR 4
  step binR 0x01 instruction_add
  step swapR 0
  norm
  step popR
  step dupR 3
  step dupR 1
  step binR 0x10 (instruction_of_stackOnlyStep rfl)
  step unR 0x15 instruction_iszero
  step unR 0x15 instruction_iszero
  step unR 0x15 instruction_iszero
  step pushR 2 (0x2b0d : U256)
  step jumpi0R (by rw [hlt]; decide)
  exact Gas.invalid_feG (by code_fact) (by code_fact)

end UsdtVerify.SafeMath

namespace UsdtVerify.TransferOk

open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts
open Transfer SafeMath

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate}

/-- From 9883, a `transfer` whose sender's balance is below `v` faults at the `sub` of the debit
(after the fee and `sendAmount = v - fee`, which need no overflow and `fee ≤ v`). -/
theorem bodyLow (hfork : .berlin ≤ fork) (hlong : 68 ≤ message.data.size)
    (hsz : message.data.size < 2 ^ 256)
    {v a sel : U256} {M : ByteArray} (hM : M.size = 96)
    (hov : v.toNat * (storageAt state message.currentTarget 3).toNat < 2 ^ 256)
    (hfv : (feeOf state message v).toNat ≤ v.toNat)
    (hlow : (balS state message).toNat < v.toNat)
    {c3 c4 cS : Bool} (hc3 : coldIn substate message.currentTarget 3 = c3)
    (hc4 : coldIn (accessSlot substate message.currentTarget 3) message.currentTarget 4 = c4)
    (hcS : coldIn (accessSlot (accessSlot substate message.currentTarget 3) message.currentTarget 4)
      message.currentTarget (senderSlot message) = cS)
    {gas : Nat}
    (hg : 497 + slotCost c3 + slotCost c4 + slotCost cS + mulCost v +
      capCost (rawFee state message v) (storageAt state message.currentTarget 4) ≤ gas) :
    Gas.SpecG fork (At CODE message 9883 [v, a, 0x1699, v, a, 0x078a, sel] M gas state substate)
      (Faulted (.invalidOpcode 0xfe) (reads3 state message) (access3 substate message)) := by
  simp only [rawFee, feeOf, balS, reads3, access3] at hg hfv hlow ⊢
  step payloadOk hlong hsz (by simp) (by gas_ok)
  step feeCall hfork (by simp) hc3 (by gas_ok)
  step mulBlock (by simp) (by valid_dest) hov (by gas_ok)
  at_pc 9937
  step divCall (by simp) (by gas_ok)
  step divBlock (by simp) (by valid_dest) (by decide) (by gas_ok)
  at_pc 9951
  step capBlock hfork (by simp) hc4 (by simp only [storageAt_readSlot]; gas_ok)
  simp only [storageAt_readSlot]
  step sendCall (by simp) (by gas_ok)
  step subBlock (by simp) (by valid_dest) hfv (by gas_ok)
  at_pc 9988
  step debitCall hfork (by simp) hcS (by gas_ok) hM
  simp only [storageAt_readSlot]
  exact subFault (by simp) hlow (by gas_ok)

/-- The gas a `transfer` with an insufficient balance needs to reach its INVALID. -/
abbrev lowCost (state : State.TransactionState) (message : Message fork)
    (c0 cB c10 c3 c4 cS : Bool) : Nat :=
  PRE_COST + slotCost c0 + slotCost cB + slotCost c10 + (497 + slotCost c3 + slotCost c4 +
    slotCost cS + mulCost (wordArg message.data 1) +
    capCost (rawFee (shortState state message) message (wordArg message.data 1))
      (storageAt (shortState state message) message.currentTarget 4))

/-- The specification of `transfer(to, v)` when the sender's balance is below `v`.

Hypotheses: as for `spec_ok` up to the fee: call data of 68 to 2^256 - 1 bytes with selector
0xa9059cbb, no value, not paused, caller not blacklisted, not deprecated, `v * basisPointsRate`
does not overflow, the fee is at most `v`; then `balances[msg.sender] < v`, and enough gas to reach
the assert (`lowCost ≤ gas`; with less, the frame runs out of gas instead).

Then the frame halts exceptionally with INVALID (error `invalidOpcode 0xfe`), no output, no gas
left, in the state after the reads of slots 0, the blacklist slot, 10, 3, 4 and the sender's
balance (nothing written). The caller discards that state. -/
theorem spec_low (hfork : .berlin ≤ fork)
    (hlong : 68 ≤ message.data.size) (hsz : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0xa9059cbb) (hv : message.value = 0)
    (hnp : byte20 (storageAt state message.currentTarget 0) = 0)
    (hnb : (storageAt state message.currentTarget (blackSlot message)).toNat % 256 = 0)
    (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    (hov : (wordArg message.data 1).toNat *
      (storageAt (shortState state message) message.currentTarget 3).toNat < 2 ^ 256)
    (hfv : (feeOf (shortState state message) message (wordArg message.data 1)).toNat ≤
      (wordArg message.data 1).toNat)
    (hlow : (balS (shortState state message) message).toNat < (wordArg message.data 1).toNat)
    {c0 cB c10 c3 c4 cS : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hcB : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget
      (blackSlot message) = cB)
    (hc10 : coldIn (accessSlot (accessSlot substate message.currentTarget 0) message.currentTarget
      (blackSlot message)) message.currentTarget 10 = c10)
    (hc3 : coldIn (shortSubstate substate message) message.currentTarget 3 = c3)
    (hc4 : coldIn (accessSlot (shortSubstate substate message) message.currentTarget 3)
      message.currentTarget 4 = c4)
    (hcS : coldIn (accessSlot (accessSlot (shortSubstate substate message) message.currentTarget 3)
      message.currentTarget 4) message.currentTarget (senderSlot message) = cS)
    {gas : Nat} (hg : lowCost state message c0 cB c10 c3 c4 cS ≤ gas) :
    Gas.SpecG fork (At CODE message 0 [] .empty gas state substate)
      (Faulted (.invalidOpcode 0xfe) (reads3 (shortState state message) message)
        (access3 (shortSubstate substate message) message)) := by
  have hB := bodyLow (state := shortState state message) (substate := shortSubstate substate message)
    (sel := BitVec.ofNat 256 (selector message.data)) (a := addrArg message.data 0)
    (gas := gas - (PRE_COST + slotCost c0 + slotCost cB + slotCost c10))
    hfork hlong hsz (size_MEMK (callerKey message) 6) hov hfv hlow hc3 hc4 hcS
    (Nat.le_sub_of_add_le (by rw [Nat.add_comm]; exact hg))
  have hpre : PRE_COST + slotCost c0 + slotCost cB + slotCost c10 ≤ gas :=
    Nat.le_trans (Nat.le_add_right _ _) hg
  clear hov hfv hlow hg
  simp only [PRE_COST] at hpre hB
  have ht : tested (BitVec.ofNat 256 (selector message.data)) ENTRIES = 22 := by
    rw [hsel]; decide
  have hb : branch (BitVec.ofNat 256 (selector message.data)) 54 (entrySize 4 2) ENTRIES =
      1866 := by
    rw [hsel]; decide
  have h1 := dispatch (state := state) (substate := substate) (by omega) hsz (gas := gas)
    (by rw [ht]; gas_ok)
  rw [ht, hb] at h1
  refine Gas.SpecG.seq h1 ?_
  step entry hv (by gas_ok)
  step notPaused hfork (by simp) hnp hc0 (by gas_ok)
  step blackLookup hfork (by simp) hcB (by gas_ok)
  step jumpiR (blackTest_ne (by rw [storageAt_readSlot]; exact hnb))
  step repc (pc' := 5481) (by decide)
  step depInline hfork (by simp) (by rw [storageAt_readSlot, storageAt_readSlot]; exact hdep) hc10
    (by gas_ok)
  step toBasic (by gas_ok)
  step Gas.reshapeG (g' := gas - (1034 + slotCost c0 + slotCost cB + slotCost c10)) rfl rfl (by gas_ok)
  exact hB

end UsdtVerify.TransferOk

end

section

/-!
## transfer(address,uint256): the success path, from pc 0, with a fee above 0

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
theorem spec_fee (hfork : .berlin ≤ fork)
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
    Gas.SpecG fork (At CODE message 0 [] .empty gas state substate)
      (Halted false .empty (gas - feeCost fork state message c0 cB c10 c3 c4 cS cT cO)
        (feeState (shortState state message) message (wordArg message.data 1)
          (addrArg message.data 0))
        (feeSub fork (shortSubstate substate message) (shortState state message) message
          (wordArg message.data 1) (addrArg message.data 0))) := by
  have hB := bodyFee (state := shortState state message)
    (substate := shortSubstate substate message)
    (sel := BitVec.ofNat 256 (selector message.data))
    (gas := gas - (PRE_COST + slotCost c0 + slotCost cB + slotCost c10))
    hfork hlong hsz hstatic
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
  refine Gas.SpecG.seq h1 ?_
  step Transfer.entry hv (by gas_ok)
  step Transfer.notPaused hfork (by simp) hnp hc0 (by gas_ok)
  step blackLookup hfork (by simp) hcB (by gas_ok)
  step jumpiR (blackTest_ne (by rw [storageAt_readSlot]; exact hnb))
  step repc (pc' := 5481) (by decide)
  step depInline hfork (by simp) (by rw [storageAt_readSlot, storageAt_readSlot]; exact hdep) hc10
    (by gas_ok)
  step toBasic (by gas_ok)
  step Gas.reshapeG (g' := gas - (1034 + slotCost c0 + slotCost cB + slotCost c10)) rfl rfl (by gas_ok)
  refine hB.consequence (fun _ h => h) ?_
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  exact ⟨hr, he, ho, by rw [hgas, Nat.sub_sub], hs, hss⟩

end UsdtVerify.TransferFee

end

section

/-!
## transfer(address,uint256): the failed SafeMath asserts (INVALID)

Each SafeMath assert compiles to `JUMPI` over INVALID (0xfe); a failed one halts the frame with
EthLib's `Faulted (.invalidOpcode 0xfe)`: no output, no gas left, and the state and substate
it had (the caller discards them). Besides `spec_low` (above), the asserts of
`transfer` that can fail are:

- `spec_mulOv`: `mul(v, basisPointsRate)` overflows (INVALID at 10802, `mulFault`);
- `spec_feeGt`: the fee is above `v` (`sub(v, fee)`, INVALID at 10989);
- `spec_toOv`: the recipient's balance plus `sendAmount` overflows (`add`, INVALID at 11020);
  for every fee, after the sender's write;
- `spec_ownerOv`: with a fee above 0, the owner's balance plus the fee overflows (`add`), after
  the recipient's write.

`pre` is the common prefix from pc 0 to BasicToken's `transfer` at 9883.
-/

namespace UsdtVerify.SafeMath

open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate}

/-- With an overflow, the product divided by the first factor is not the second. -/
theorem div_mul_ne {a b : U256} (hov : 2 ^ 256 ≤ a.toNat * b.toNat) : div (mul a b) a ≠ b := by
  have ha : a ≠ 0 := by
    intro h
    subst h
    simp at hov
  intro h
  have h2 := congrArg BitVec.toNat h
  simp only [div, ha, ite_false, mul, BitVec.toNat_mul] at h2
  have h3 := Nat.div_mul_le_self (a.toNat * b.toNat % 2 ^ 256) a.toNat
  have h4 := Nat.mod_lt (a.toNat * b.toNat) (show 0 < 2 ^ 256 by decide)
  have h5 : a.toNat * b.toNat % 2 ^ 256 / a.toNat < 2 ^ 256 :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) h4
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h5] at h2
  rw [h2] at h3
  have h6 : b.toNat * a.toNat = a.toNat * b.toNat := Nat.mul_comm _ _
  omega

/-- `mul(a, b)` at 10755 with `a * b ≥ 2^256` fails its assert: INVALID at 10802, after 108 gas. -/
theorem mulFault {a b ret : U256} {rest : List U256} (hrest : rest.length ≤ 20)
    (hov : 2 ^ 256 ≤ a.toNat * b.toNat) {gas : Nat} (hg : 108 ≤ gas) {M : ByteArray} :
    Gas.SpecG fork (At CODE message 10755 (b :: a :: ret :: rest) M gas state substate)
      (Faulted (.invalidOpcode 0xfe) state substate) := by
  have ha : a ≠ 0 := by
    intro h
    subst h
    simp at hov
  have hq := div_mul_ne hov
  step jumpdestR
  step pushR 1 (0 : U256)
  step dupR 0
  step pushR 1 (0 : U256)
  step dupR 4
  step binR 0x14 instruction_eq
  step unR 0x15 instruction_iszero
  step pushR 2 (0x2a18 : U256)
  step jumpiR (by simp [equal, isZero]; exact ha)
  at_pc 10776
  step jumpdestR
  step dupR 2
  step dupR 4
  step binR 0x02 (instruction_of_stackOnlyStep rfl)
  step swapR 0
  norm
  step popR
  step dupR 2
  step dupR 4
  step dupR 2
  step dupR 1
  step unR 0x15 instruction_iszero
  step unR 0x15 instruction_iszero
  step pushR 2 (0x2a29 : U256)
  step jumpiR (by simp [isZero]; exact ha)
  at_pc 10793
  step jumpdestR
  step binR 0x04 (instruction_of_stackOnlyStep rfl)
  step binR 0x14 instruction_eq
  step unR 0x15 instruction_iszero
  step unR 0x15 instruction_iszero
  step pushR 2 (0x2a33 : U256)
  step jumpi0R (by simp [hq, equal, isZero])
  exact Gas.invalid_feG (by code_fact) (by code_fact)

end UsdtVerify.SafeMath

namespace UsdtVerify.TransferOk

open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts
open Transfer SafeMath TransferFee TransferFrom

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate}

/-- The stack at 9883 for `transfer(to, v)`. -/
abbrev bodyStack (message : Message fork) : List U256 :=
  [wordArg message.data 1, addrArg message.data 0, 0x1699, wordArg message.data 1,
    addrArg message.data 0, 0x078a, BitVec.ofNat 256 (selector message.data)]

/-- From pc 0, a `transfer` call that passes the checks (no value, not paused, caller not
blacklisted, not deprecated) reaches BasicToken's `transfer` at 9883. -/
theorem pre (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsz : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0xa9059cbb) (hv : message.value = 0)
    (hnp : byte20 (storageAt state message.currentTarget 0) = 0)
    (hnb : (storageAt state message.currentTarget (blackSlot message)).toNat % 256 = 0)
    (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    {c0 cB c10 : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hcB : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget
      (blackSlot message) = cB)
    (hc10 : coldIn (accessSlot (accessSlot substate message.currentTarget 0) message.currentTarget
      (blackSlot message)) message.currentTarget 10 = c10)
    {gas : Nat} (hg : PRE_COST + slotCost c0 + slotCost cB + slotCost c10 ≤ gas) :
    Gas.HoareG fork (At CODE message 0 [] .empty gas state substate)
      (At CODE message 9883 (bodyStack message) (MEMK (callerKey message) 6)
        (gas - (PRE_COST + slotCost c0 + slotCost cB + slotCost c10))
        (shortState state message) (shortSubstate substate message)) := by
  simp only [PRE_COST] at hg ⊢
  have ht : tested (BitVec.ofNat 256 (selector message.data)) ENTRIES = 22 := by
    rw [hsel]; decide
  have hb : branch (BitVec.ofNat 256 (selector message.data)) 54 (entrySize 4 2) ENTRIES =
      1866 := by
    rw [hsel]; decide
  have h1 := dispatch (state := state) (substate := substate) hsize hsz (gas := gas)
    (by rw [ht]; gas_ok)
  rw [ht, hb] at h1
  refine Triple.seq h1 ?_
  step entry hv (by gas_ok)
  step notPaused hfork (by simp) hnp hc0 (by gas_ok)
  step blackLookup hfork (by simp) hcB (by gas_ok)
  step jumpiR (blackTest_ne (by rw [storageAt_readSlot]; exact hnb))
  step repc (pc' := 5481) (by decide)
  step depInline hfork (by simp) (by rw [storageAt_readSlot, storageAt_readSlot]; exact hdep) hc10
    (by gas_ok)
  step toBasic (by gas_ok)
  exact Gas.reshapeG rfl rfl (by gas_ok)

/-- From 9883, `mul(v, basisPointsRate)` overflows: INVALID after the read of slot 3. -/
theorem bodyMulOv (hlong : 68 ≤ message.data.size) (hsz : message.data.size < 2 ^ 256)
    (hfork : .berlin ≤ fork) {v a sel : U256} {M : ByteArray}
    (hov : 2 ^ 256 ≤ v.toNat * (storageAt state message.currentTarget 3).toNat)
    {c3 : Bool} (hc3 : coldIn substate message.currentTarget 3 = c3)
    {gas : Nat} (hg : 204 + slotCost c3 ≤ gas) :
    Gas.SpecG fork (At CODE message 9883 [v, a, 0x1699, v, a, 0x078a, sel] M gas state substate)
      (Faulted (.invalidOpcode 0xfe) (readSlot state message.currentTarget 3)
        (accessSlot substate message.currentTarget 3)) := by
  step payloadOk hlong hsz (by simp) (by gas_ok)
  step feeCall hfork (by simp) hc3 (by gas_ok)
  exact mulFault (by simp) hov (by gas_ok)

/-- From 9883, a fee above `v`: INVALID at the `sub(v, fee)` of `sendAmount`. -/
theorem bodyFeeGt (hlong : 68 ≤ message.data.size) (hsz : message.data.size < 2 ^ 256)
    (hfork : .berlin ≤ fork) {v a sel : U256} {M : ByteArray}
    (hov : v.toNat * (storageAt state message.currentTarget 3).toNat < 2 ^ 256)
    (hgt : v.toNat < (feeOf state message v).toNat)
    {c3 c4 : Bool} (hc3 : coldIn substate message.currentTarget 3 = c3)
    (hc4 : coldIn (accessSlot substate message.currentTarget 3) message.currentTarget 4 = c4)
    {gas : Nat}
    (hg : 299 + slotCost c3 + slotCost c4 + mulCost v +
      capCost (rawFee state message v) (storageAt state message.currentTarget 4) ≤ gas) :
    Gas.SpecG fork (At CODE message 9883 [v, a, 0x1699, v, a, 0x078a, sel] M gas state substate)
      (Faulted (.invalidOpcode 0xfe)
        (readSlot (readSlot state message.currentTarget 3) message.currentTarget 4)
        (accessSlot (accessSlot substate message.currentTarget 3) message.currentTarget 4)) := by
  simp only [rawFee, feeOf] at hg hgt ⊢
  step payloadOk hlong hsz (by simp) (by gas_ok)
  step feeCall hfork (by simp) hc3 (by gas_ok)
  step mulBlock (by simp) (by valid_dest) hov (by gas_ok)
  at_pc 9937
  step divCall (by simp) (by gas_ok)
  step divBlock (by simp) (by valid_dest) (by decide) (by gas_ok)
  at_pc 9951
  step capBlock hfork (by simp) hc4 (by simp only [storageAt_readSlot]; gas_ok)
  simp only [storageAt_readSlot]
  step sendCall (by simp) (by gas_ok)
  exact subFault (by simp) hgt (by gas_ok)

/-- The state at the recipient's `add`: the sender written, the recipient's slot read. -/
abbrev toOvState (state : State.TransactionState) (message : Message fork) (v a : U256) :
    State.TransactionState :=
  readSlot (debited state message v) message.currentTarget (recipientSlot a)

/-- The substate at the recipient's `add`. -/
abbrev toOvSub (fork : Fork) (substate : Substate) (state : State.TransactionState)
    (message : Message fork) (v a : U256) : Substate :=
  accessSlot (debitedSub fork substate state message v) message.currentTarget (recipientSlot a)

/-- From 9883, for any fee `≤ v`, the recipient's balance (read after the sender's write) plus
`sendAmount = v - fee` overflows: INVALID at the `add`, after the sender's write. -/
theorem bodyToOv (hfork : .berlin ≤ fork)
    (hlong : 68 ≤ message.data.size) (hsz : message.data.size < 2 ^ 256)
    (hstatic : message.isStatic = false) (hacc : hasAccount state message.currentTarget)
    {v a sel : U256} {M : ByteArray} (hM : M.size = 96)
    (hov : v.toNat * (storageAt state message.currentTarget 3).toNat < 2 ^ 256)
    (hfv : (feeOf state message v).toNat ≤ v.toNat)
    (hbal : v.toNat ≤ (balS state message).toNat)
    (hto : 2 ^ 256 ≤ (balT state message v a).toNat + (sendOf state message v).toNat)
    {c3 c4 cS cT : Bool} (hc3 : coldIn substate message.currentTarget 3 = c3)
    (hc4 : coldIn (accessSlot substate message.currentTarget 3) message.currentTarget 4 = c4)
    (hcS : coldIn (accessSlot (accessSlot substate message.currentTarget 3) message.currentTarget 4)
      message.currentTarget (senderSlot message) = cS)
    (hcT : coldIn (access3 substate message) message.currentTarget (recipientSlot a) = cT)
    {gas : Nat}
    (hstip : 530 + slotCost c3 + slotCost c4 + slotCost cS + mulCost v +
      capCost (rawFee state message v) (storageAt state message.currentTarget 4) + 2400 ≤ gas)
    (hg : 808 + readCost c3 c4 cS cT + mulCost v +
      capCost (rawFee state message v) (storageAt state message.currentTarget 4) +
      debitCost fork state message v ≤ gas) :
    Gas.SpecG fork (At CODE message 9883 [v, a, 0x1699, v, a, 0x078a, sel] M gas state substate)
      (Faulted (.invalidOpcode 0xfe) (toOvState state message v a)
        (toOvSub fork substate state message v a)) := by
  have hacc3 : hasAccount (reads3 state message) message.currentTarget :=
    hasAccount_readSlot (hasAccount_readSlot (hasAccount_readSlot hacc))
  simp only [readCost, debitCost, rawFee, feeOf, balS, balT, debited, reads3, sendOf, toOvState,
    toOvSub, debitedSub, access3] at hstip hg hfv hbal hto hcT hacc3 ⊢
  step payloadOk hlong hsz (by simp) (by gas_ok)
  step feeCall hfork (by simp) hc3 (by gas_ok)
  step mulBlock (by simp) (by valid_dest) hov (by gas_ok)
  at_pc 9937
  step divCall (by simp) (by gas_ok)
  step divBlock (by simp) (by valid_dest) (by decide) (by gas_ok)
  at_pc 9951
  step capBlock hfork (by simp) hc4 (by simp only [storageAt_readSlot]; gas_ok)
  simp only [storageAt_readSlot]
  step sendCall (by simp) (by gas_ok)
  step subBlock (by simp) (by valid_dest) hfv (by gas_ok)
  at_pc 9988
  step debitCall hfork (by simp) hcS (by gas_ok) hM
  simp only [storageAt_readSlot]
  step subBlock (by simp) (by valid_dest) hbal (by gas_ok)
  at_pc 10072
  step debitStore hfork (by simp) hstatic hacc3 (coldIn_accessSlot_self _ _ _) (by gas_ok)
    (by simp only [storageAt_readSlot, originalAt_readSlot]; gas_ok) (size_mapMem hM _ _)
  simp only [storageAt_readSlot, originalAt_readSlot]
  step creditCall hfork (by simp) (cT := cT) (by rw [coldIn_storeSub]; exact hcT) (by gas_ok)
    (size_mapMem (size_mapMem hM _ _) _ _)
  exact addFault (by simp) hto (by gas_ok)

/-- From 9883, for any fee `≤ v` and `v ≤ balances[caller]`, when the `SSTORE` cannot complete
(`NoWrite`: a static frame, no account for `C`, or at most 2300 gas left there): the run reaches the
`SSTORE` of the sender's balance (`Stuck`). -/
theorem bodyBad (hfork : .berlin ≤ fork)
    (hlong : 68 ≤ message.data.size) (hsz : message.data.size < 2 ^ 256)
    {v a sel : U256} {M : ByteArray} (hM : M.size = 96)
    (hov : v.toNat * (storageAt state message.currentTarget 3).toNat < 2 ^ 256)
    (hfv : (feeOf state message v).toNat ≤ v.toNat)
    (hbal : v.toNat ≤ (balS state message).toNat)
    {c3 c4 cS : Bool} (hc3 : coldIn substate message.currentTarget 3 = c3)
    (hc4 : coldIn (accessSlot substate message.currentTarget 3) message.currentTarget 4 = c4)
    (hcS : coldIn (accessSlot (accessSlot substate message.currentTarget 3) message.currentTarget 4)
      message.currentTarget (senderSlot message) = cS)
    {gas : Nat}
    (hbad : Gas.NoWrite message state (gas - (629 + slotCost c3 + slotCost c4 + slotCost cS +
      mulCost v + capCost (rawFee state message v) (storageAt state message.currentTarget 4))))
    (hg : 629 + slotCost c3 + slotCost c4 + slotCost cS + mulCost v +
      capCost (rawFee state message v) (storageAt state message.currentTarget 4) ≤ gas) :
    Gas.HoareG fork (At CODE message 9883 [v, a, 0x1699, v, a, 0x078a, sel] M gas state substate)
      Gas.Stuck := by
  simp only [rawFee, feeOf, balS] at hg hfv hbal hbad
  step payloadOk hlong hsz (by simp) (by gas_ok)
  step feeCall hfork (by simp) hc3 (by gas_ok)
  step mulBlock (by simp) (by valid_dest) hov (by gas_ok)
  at_pc 9937
  step divCall (by simp) (by gas_ok)
  step divBlock (by simp) (by valid_dest) (by decide) (by gas_ok)
  at_pc 9951
  step capBlock hfork (by simp) hc4 (by simp only [storageAt_readSlot]; gas_ok)
  simp only [storageAt_readSlot]
  step sendCall (by simp) (by gas_ok)
  step subBlock (by simp) (by valid_dest) hfv (by gas_ok)
  at_pc 9988
  step debitCall hfork (by simp) hcS (by gas_ok) hM
  simp only [storageAt_readSlot]
  step subBlock (by simp) (by valid_dest) hbal (by gas_ok)
  at_pc 10072
  refine debitStoreBad (state := readSlot (readSlot (readSlot state message.currentTarget 3)
    message.currentTarget 4) message.currentTarget (senderSlot message)) ?_ (hbad.le ?_) ?_
    (size_mapMem hM _ _)
  · simp
  · gas_ok
  · gas_ok

/-- The state at the owner's `add`: after the recipient's write, slot 0 and the owner's slot read. -/
abbrev ownerOvState (state : State.TransactionState) (message : Message fork) (v a : U256) :
    State.TransactionState :=
  readSlot (readSlot (creditedFee state message v a) message.currentTarget 0)
    message.currentTarget (ownerSlot (ownerWord state message v a))

/-- The substate at the owner's `add`. -/
abbrev ownerOvSub (fork : Fork) (substate : Substate) (state : State.TransactionState)
    (message : Message fork) (v a : U256) : Substate :=
  accessSlot (accessSlot (creditedSubFee fork substate state message v a) message.currentTarget 0)
    message.currentTarget (ownerSlot (ownerWord state message v a))

/-- From 9883, with a fee above 0 and the transfer to `_to` done, the owner's balance (read after
the recipient's write) plus the fee overflows: INVALID at the `add` of the owner's credit. -/
theorem bodyOwnerOv (hfork : .berlin ≤ fork)
    (hlong : 68 ≤ message.data.size) (hsz : message.data.size < 2 ^ 256)
    (hstatic : message.isStatic = false) (hacc : hasAccount state message.currentTarget)
    {v a sel : U256} {M : ByteArray} (hM : M.size = 96)
    (hov : v.toNat * (storageAt state message.currentTarget 3).toNat < 2 ^ 256)
    (hfee : feeOf state message v ≠ 0)
    (hfv : (feeOf state message v).toNat ≤ v.toNat)
    (hbal : v.toNat ≤ (balS state message).toNat)
    (hto : (balT state message v a).toNat + (sendOf state message v).toNat < 2 ^ 256)
    (hown : 2 ^ 256 ≤ (balO state message v a).toNat + (feeOf state message v).toNat)
    (hc0 : coldIn substate message.currentTarget 0 = false)
    {c3 c4 cS cT cO : Bool} (hc3 : coldIn substate message.currentTarget 3 = c3)
    (hc4 : coldIn (accessSlot substate message.currentTarget 3) message.currentTarget 4 = c4)
    (hcS : coldIn (accessSlot (accessSlot substate message.currentTarget 3) message.currentTarget 4)
      message.currentTarget (senderSlot message) = cS)
    (hcT : coldIn (access3 substate message) message.currentTarget (recipientSlot a) = cT)
    (hcO : coldIn (creditedSubFee fork substate state message v a) message.currentTarget
      (ownerSlot (ownerWord state message v a)) = cO)
    {gas : Nat}
    (hstip : 964 + readCost c3 c4 cS cT + mulCost v +
      capCost (rawFee state message v) (storageAt state message.currentTarget 4) +
      debitCost fork state message v + creditCostFee fork state message v a + 2401 ≤ gas)
    (hg : 964 + readCost c3 c4 cS cT + mulCost v +
      capCost (rawFee state message v) (storageAt state message.currentTarget 4) +
      debitCost fork state message v + creditCostFee fork state message v a + 313 +
      slotCost cO ≤ gas) :
    Gas.SpecG fork (At CODE message 9883 [v, a, 0x1699, v, a, 0x078a, sel] M gas state substate)
      (Faulted (.invalidOpcode 0xfe) (ownerOvState state message v a)
        (ownerOvSub fork substate state message v a)) := by
  have hw : coldIn (creditedSubFee fork substate state message v a) message.currentTarget 0 =
      false :=
    coldIn_storeSub_false (coldIn_accessSlot_false (coldIn_storeSub_false
      (coldIn_accessSlot_false (coldIn_accessSlot_false (coldIn_accessSlot_false hc0)))))
  have hA := feeHead (sel := sel) hfork hlong hsz hstatic hacc hM hov hfee hfv hbal hto hc3
    hc4 hcS hcT (gas := gas) hstip
  refine Triple.seq hA ?_
  have hO := ownerCall (message := message) (state := creditedFee state message v a)
    (substate := creditedSubFee fork substate state message v a) (cO := cO) hfork rfl
    (send := sendOf state message v) (fee := feeOf state message v) (v := v) (a := a)
    (rest := [0x1699, v, a, 0x078a, sel]) (by simp) hw
    (by rw [coldIn_accessSlot_of_warm hw]; exact hcO)
    (gas := gas - (964 + readCost c3 c4 cS cT + mulCost v +
          capCost (rawFee state message v) (storageAt state message.currentTarget 4) +
          debitCost fork state message v + creditCostFee fork state message v a))
    (Nat.le_sub_of_add_le (by omega)) (M := memA M message a)
    (size_mapMem (size_mapMem (size_mapMem (size_mapMem hM _ _) _ _) _ _) _ _)
  refine Triple.seq hO ?_
  exact addFault (by simp) hown (by omega)

/-- The gas of `transfer` up to 9883 and the reads of slots 0, the blacklist slot and 10. -/
abbrev preCost (c0 cB c10 : Bool) : Nat := PRE_COST + slotCost c0 + slotCost cB + slotCost c10

/-- The specification of `transfer(to, v)` when `v * basisPointsRate` overflows.

Hypotheses: call data of 68 to 2^256 - 1 bytes with selector 0xa9059cbb; no value; not paused;
the caller not blacklisted; not deprecated; `v * rate ≥ 2^256` (`rate` = slot 3, read in `S`,
the state after the reads of the checks); enough gas to reach the assert.

Then the frame halts exceptionally with INVALID (`invalidOpcode 0xfe`), no output, no gas left,
in `S` with slot 3 recorded read (nothing written). -/
theorem spec_mulOv (hfork : .berlin ≤ fork)
    (hlong : 68 ≤ message.data.size) (hsz : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0xa9059cbb) (hv : message.value = 0)
    (hnp : byte20 (storageAt state message.currentTarget 0) = 0)
    (hnb : (storageAt state message.currentTarget (blackSlot message)).toNat % 256 = 0)
    (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    (hov : 2 ^ 256 ≤ (wordArg message.data 1).toNat *
      (storageAt (shortState state message) message.currentTarget 3).toNat)
    {c0 cB c10 c3 : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hcB : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget
      (blackSlot message) = cB)
    (hc10 : coldIn (accessSlot (accessSlot substate message.currentTarget 0) message.currentTarget
      (blackSlot message)) message.currentTarget 10 = c10)
    (hc3 : coldIn (shortSubstate substate message) message.currentTarget 3 = c3)
    {gas : Nat} (hg : preCost c0 cB c10 + (204 + slotCost c3) ≤ gas) :
    Gas.SpecG fork (At CODE message 0 [] .empty gas state substate)
      (Faulted (.invalidOpcode 0xfe) (readSlot (shortState state message) message.currentTarget 3)
        (accessSlot (shortSubstate substate message) message.currentTarget 3)) :=
  Triple.seq (pre hfork (by omega) hsz hsel hv hnp hnb hdep hc0 hcB hc10
      (Nat.le_trans (Nat.le_add_right _ _) hg))
    (bodyMulOv hlong hsz hfork hov hc3 (Nat.le_sub_of_add_le (by rw [Nat.add_comm]; exact hg)))

/-- The specification of `transfer(to, v)` when the fee is above `v`.

Hypotheses: as `spec_mulOv` up to the checks; `v * rate < 2^256`; `v < fee`, the fee as the
bytecode computes it (`feeOf`, from slots 3 and 4 in `S`); enough gas.

Then INVALID at the `sub(v, fee)` of `sendAmount`: no output, no gas left, state `S` with slots 3
and 4 recorded read (nothing written). -/
theorem spec_feeGt (hfork : .berlin ≤ fork)
    (hlong : 68 ≤ message.data.size) (hsz : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0xa9059cbb) (hv : message.value = 0)
    (hnp : byte20 (storageAt state message.currentTarget 0) = 0)
    (hnb : (storageAt state message.currentTarget (blackSlot message)).toNat % 256 = 0)
    (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    (hov : (wordArg message.data 1).toNat *
      (storageAt (shortState state message) message.currentTarget 3).toNat < 2 ^ 256)
    (hgt : (wordArg message.data 1).toNat <
      (feeOf (shortState state message) message (wordArg message.data 1)).toNat)
    {c0 cB c10 c3 c4 : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hcB : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget
      (blackSlot message) = cB)
    (hc10 : coldIn (accessSlot (accessSlot substate message.currentTarget 0) message.currentTarget
      (blackSlot message)) message.currentTarget 10 = c10)
    (hc3 : coldIn (shortSubstate substate message) message.currentTarget 3 = c3)
    (hc4 : coldIn (accessSlot (shortSubstate substate message) message.currentTarget 3)
      message.currentTarget 4 = c4)
    {gas : Nat} (hg : preCost c0 cB c10 + (299 + slotCost c3 + slotCost c4 +
      mulCost (wordArg message.data 1) +
      capCost (rawFee (shortState state message) message (wordArg message.data 1))
        (storageAt (shortState state message) message.currentTarget 4)) ≤ gas) :
    Gas.SpecG fork (At CODE message 0 [] .empty gas state substate)
      (Faulted (.invalidOpcode 0xfe)
        (readSlot (readSlot (shortState state message) message.currentTarget 3)
          message.currentTarget 4)
        (accessSlot (accessSlot (shortSubstate substate message) message.currentTarget 3)
          message.currentTarget 4)) :=
  Triple.seq (pre hfork (by omega) hsz hsel hv hnp hnb hdep hc0 hcB hc10
      (Nat.le_trans (Nat.le_add_right _ _) hg))
    (bodyFeeGt hlong hsz hfork hov hgt hc3 hc4
      (Nat.le_sub_of_add_le (by rw [Nat.add_comm]; exact hg)))

/-- The specification of `transfer(to, v)` when the recipient's balance overflows.

Hypotheses: Berlin ≤ fork (Glamsterdam included), not static, the contract has an account; the checks pass
as in `spec_ok`; `v * rate < 2^256`; `fee ≤ v` (any fee, 0 included); `v ≤ balances[caller]`;
`balances[to] + (v - fee) ≥ 2^256`, with `balances[to]` read after the sender's write (`balT`);
more than 2300 gas left at the sender's SSTORE (`hstip`), and enough gas to reach the assert.

Then INVALID at the recipient's `add`: no output, no gas left, in the state after the sender's
write `balances[caller] := balS - v` and the read of the recipient's slot (the caller discards
it). -/
theorem spec_toOv (hfork : .berlin ≤ fork)
    (hstatic : message.isStatic = false) (hacc : hasAccount state message.currentTarget)
    (hlong : 68 ≤ message.data.size) (hsz : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0xa9059cbb) (hv : message.value = 0)
    (hnp : byte20 (storageAt state message.currentTarget 0) = 0)
    (hnb : (storageAt state message.currentTarget (blackSlot message)).toNat % 256 = 0)
    (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    (hov : (wordArg message.data 1).toNat *
      (storageAt (shortState state message) message.currentTarget 3).toNat < 2 ^ 256)
    (hfv : (feeOf (shortState state message) message (wordArg message.data 1)).toNat ≤
      (wordArg message.data 1).toNat)
    (hbal : (wordArg message.data 1).toNat ≤ (balS (shortState state message) message).toNat)
    (hto : 2 ^ 256 ≤ (balT (shortState state message) message (wordArg message.data 1)
      (addrArg message.data 0)).toNat +
      (sendOf (shortState state message) message (wordArg message.data 1)).toNat)
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
    (hstip : preCost c0 cB c10 + (530 + slotCost c3 + slotCost c4 + slotCost cS +
      mulCost (wordArg message.data 1) +
      capCost (rawFee (shortState state message) message (wordArg message.data 1))
        (storageAt (shortState state message) message.currentTarget 4) + 2400) ≤ gas)
    (hg : preCost c0 cB c10 + (808 + readCost c3 c4 cS cT + mulCost (wordArg message.data 1) +
      capCost (rawFee (shortState state message) message (wordArg message.data 1))
        (storageAt (shortState state message) message.currentTarget 4) +
      debitCost fork (shortState state message) message (wordArg message.data 1)) ≤ gas) :
    Gas.SpecG fork (At CODE message 0 [] .empty gas state substate)
      (Faulted (.invalidOpcode 0xfe)
        (toOvState (shortState state message) message (wordArg message.data 1)
          (addrArg message.data 0))
        (toOvSub fork (shortSubstate substate message) (shortState state message) message
          (wordArg message.data 1) (addrArg message.data 0))) :=
  Triple.seq (pre hfork (by omega) hsz hsel hv hnp hnb hdep hc0 hcB hc10
      (Nat.le_trans (Nat.le_add_right _ _) hg))
    (bodyToOv hfork hlong hsz hstatic
      (hasAccount_readSlot (hasAccount_readSlot (hasAccount_readSlot hacc)))
      (size_MEMK (callerKey message) 6) hov hfv hbal hto hc3 hc4 hcS hcT
      (Nat.le_sub_of_add_le (by rw [Nat.add_comm]; exact hstip))
      (Nat.le_sub_of_add_le (by rw [Nat.add_comm]; exact hg)))

/-- `transfer(to, v)`, not deprecated, with the checks passing, `v * rate < 2^256`, `fee ≤ v` and `v
≤ balances[caller]`, when the `SSTORE` cannot complete (`NoWrite`: a static frame, no account for
`C`, or at most 2300 gas left there): the run reaches the `SSTORE` of the sender's balance
(`Stuck`). -/
theorem bad_transfer (hfork : .berlin ≤ fork)
    (hlong : 68 ≤ message.data.size) (hsz : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0xa9059cbb) (hv : message.value = 0)
    (hnp : byte20 (storageAt state message.currentTarget 0) = 0)
    (hnb : (storageAt state message.currentTarget (blackSlot message)).toNat % 256 = 0)
    (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    (hov : (wordArg message.data 1).toNat *
      (storageAt (shortState state message) message.currentTarget 3).toNat < 2 ^ 256)
    (hfv : (feeOf (shortState state message) message (wordArg message.data 1)).toNat ≤
      (wordArg message.data 1).toNat)
    (hbal : (wordArg message.data 1).toNat ≤ (balS (shortState state message) message).toNat)
    {c0 cB c10 c3 c4 cS : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hcB : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget
      (blackSlot message) = cB)
    (hc10 : coldIn (accessSlot (accessSlot substate message.currentTarget 0) message.currentTarget
      (blackSlot message)) message.currentTarget 10 = c10)
    (hc3 : coldIn (shortSubstate substate message) message.currentTarget 3 = c3)
    (hc4 : coldIn (accessSlot (shortSubstate substate message) message.currentTarget 3)
      message.currentTarget 4 = c4)
    (hcS : coldIn (accessSlot (accessSlot (shortSubstate substate message) message.currentTarget 3)
      message.currentTarget 4) message.currentTarget (senderSlot message) = cS)
    {gas : Nat}
    (hbad : Gas.NoWrite message state (gas - (PRE_COST + slotCost c0 + slotCost cB + slotCost c10 + (629 + slotCost c3 + slotCost c4 +
      slotCost cS + mulCost (wordArg message.data 1) +
      capCost (rawFee (shortState state message) message (wordArg message.data 1))
        (storageAt (shortState state message) message.currentTarget 4)))))
    (hg : PRE_COST + slotCost c0 + slotCost cB + slotCost c10 + (629 + slotCost c3 + slotCost c4 +
      slotCost cS + mulCost (wordArg message.data 1) +
      capCost (rawFee (shortState state message) message (wordArg message.data 1))
        (storageAt (shortState state message) message.currentTarget 4)) ≤ gas) :
    Gas.HoareG fork (At CODE message 0 [] .empty gas state substate) Gas.Stuck :=
  Triple.seq (pre hfork (by omega) hsz hsel hv hnp hnb hdep hc0 hcB hc10
      (Nat.le_trans (Nat.le_add_right _ _) hg))
    (bodyBad (state := shortState state message) hfork hlong hsz
      (size_MEMK (callerKey message) 6) hov hfv hbal hc3 hc4 hcS (hbad.le (by omega))
      (Nat.le_sub_of_add_le (by rw [Nat.add_comm]; exact hg)))

/-- `transfer(to, v)`, not deprecated, with the checks passing, a fee of 0, `v ≤ balances[caller]`
and no overflow at the recipient, a frame that may write and an account for `C`, with more than
2300 gas left at the `SSTORE` of the sender's balance but at most 2300 at the `SSTORE` of the
recipient's balance (`hlow`): the run reaches the second one, which is `Stuck`. -/
theorem low_transfer2 (hfork : .berlin ≤ fork)
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
    (hg : PRE_COST + slotCost c0 + slotCost cB + slotCost c10 + (937 + readCost c3 c4 cS cT +
      mulCost (wordArg message.data 1) +
      capCost (rawFee (shortState state message) message (wordArg message.data 1))
        (storageAt (shortState state message) message.currentTarget 4) +
      debitCost fork (shortState state message) message (wordArg message.data 1)) ≤ gas)
    (hlow : gas < PRE_COST + slotCost c0 + slotCost cB + slotCost c10 + (837 +
      readCost c3 c4 cS cT + mulCost (wordArg message.data 1) +
      capCost (rawFee (shortState state message) message (wordArg message.data 1))
        (storageAt (shortState state message) message.currentTarget 4) +
      debitCost fork (shortState state message) message (wordArg message.data 1) + 2401)) :
    Gas.HoareG fork (At CODE message 0 [] .empty gas state substate) Gas.Stuck :=
  Triple.seq (pre hfork (by omega) hsz hsel hv hnp hnb hdep hc0 hcB hc10
      (Nat.le_trans (Nat.le_add_right _ _) hg))
    (bodyLow2 (state := shortState state message) hfork hlong hsz hstatic
      (hasAccount_readSlot (hasAccount_readSlot (hasAccount_readSlot hacc)))
      (size_MEMK (callerKey message) 6) hov hfee hbal hto hc3 hc4 hcS hcT
      (Nat.le_sub_of_add_le (by rw [Nat.add_comm]; exact hstip1))
      (Nat.le_sub_of_add_le (by rw [Nat.add_comm]; exact hg)) (by omega))

/-- The specification of `transfer(to, v)` with a fee above 0 when the owner's balance
overflows.

Hypotheses: as `spec_fee` (above) up to the recipient: the checks pass,
`v * rate < 2^256`, `0 < fee ≤ v`, `v ≤ balances[caller]`, `balances[to] + (v - fee) < 2^256`;
then `balances[owner] + fee ≥ 2^256`, with `owner` the low 160 bits of slot 0 and both read after
the recipient's write (`balO`); more than 2300 gas left at the recipient's SSTORE (`hstip`; the
sender's follows), and enough gas to reach the assert.

Then INVALID at the owner's `add`: no output, no gas left, in the state after the sender's and
the recipient's writes and the reads of slot 0 and the owner's slot. -/
theorem spec_ownerOv (hfork : .berlin ≤ fork)
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
    (hown : 2 ^ 256 ≤ (balO (shortState state message) message (wordArg message.data 1)
      (addrArg message.data 0)).toNat +
      (feeOf (shortState state message) message (wordArg message.data 1)).toNat)
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
    {gas : Nat}
    (hstip : preCost c0 cB c10 + (964 + readCost c3 c4 cS cT + mulCost (wordArg message.data 1) +
      capCost (rawFee (shortState state message) message (wordArg message.data 1))
        (storageAt (shortState state message) message.currentTarget 4) +
      debitCost fork (shortState state message) message (wordArg message.data 1) +
      creditCostFee fork (shortState state message) message (wordArg message.data 1)
        (addrArg message.data 0) + 2401) ≤ gas)
    (hg : preCost c0 cB c10 + (964 + readCost c3 c4 cS cT + mulCost (wordArg message.data 1) +
      capCost (rawFee (shortState state message) message (wordArg message.data 1))
        (storageAt (shortState state message) message.currentTarget 4) +
      debitCost fork (shortState state message) message (wordArg message.data 1) +
      creditCostFee fork (shortState state message) message (wordArg message.data 1)
        (addrArg message.data 0) + 313 + slotCost cO) ≤ gas) :
    Gas.SpecG fork (At CODE message 0 [] .empty gas state substate)
      (Faulted (.invalidOpcode 0xfe)
        (ownerOvState (shortState state message) message (wordArg message.data 1)
          (addrArg message.data 0))
        (ownerOvSub fork (shortSubstate substate message) (shortState state message) message
          (wordArg message.data 1) (addrArg message.data 0))) :=
  Triple.seq (pre hfork (by omega) hsz hsel hv hnp hnb hdep hc0 hcB hc10
      (Nat.le_trans (Nat.le_add_right _ _) hg))
    (bodyOwnerOv hfork hlong hsz hstatic
      (hasAccount_readSlot (hasAccount_readSlot (hasAccount_readSlot hacc)))
      (size_MEMK (callerKey message) 6) hov hfee hfv hbal hto hown
      (coldIn_accessSlot_false (coldIn_accessSlot_false (coldIn_accessSlot_self _ _ _)))
      hc3 hc4 hcS hcT hcO
      (Nat.le_sub_of_add_le (by rw [Nat.add_comm]; exact hstip))
      (Nat.le_sub_of_add_le (by rw [Nat.add_comm]; exact hg)))

end UsdtVerify.TransferOk

end
