import UsdtVerify.Functions.TransferFee
import UsdtVerify.Functions.TransferFromBody

/-!
# transfer(address,uint256): the success path from 9883, with a fee above 0

`bodyFee` composes the blocks from BasicToken's `transfer` at 9883 to the STOP at 1931 for a call
whose fee `fee` (as the bytecode computes it) is not 0: `sendAmount = v - fee` goes to `_to`,
`fee` goes to `balances[owner]`, and two logs are appended: `Transfer(msg.sender, owner, fee)`,
then `Transfer(msg.sender, _to, sendAmount)`.

`owner` is the low 160 bits of slot 0. The code reads slot 0 three times after the balance
writes: for the owner's read, for the owner's write, and for the topic of the owner's log. Each
is stated as the code reads it (no assumption that slot 0 differs from the balance slots).
-/

namespace UsdtVerify.TransferFee

open EthLib.Base (Fork U256 Address)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts
open Transfer SafeMath TransferOk TransferFrom

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate}

theorem coldIn_storeSub' {ss : Substate} {t : Address} {n m o c w : U256} :
    coldIn (storeSub fork ss t n o c w) t m = coldIn (accessSlot ss t n) t m := rfl

/-- GENERIC: the word at 64 of a memory of 96 bytes is the same after appending. -/
theorem read64_append {M : ByteArray} (hM : M.size = 96) (w : ByteArray) :
    memoryReadBytes (M ++ w) 64 32 = memoryReadBytes M 64 32 := by
  simp only [memoryReadBytes, ByteArray.extract_append, hM]
  simp

theorem coldIn_storeSub_false {ss : Substate} {t : Address} {n m o c w : U256}
    (h : coldIn ss t m = false) : coldIn (storeSub fork ss t n o c w) t m = false :=
  coldIn_accessSlot_false h

/-- `sendAmount = v - fee`. -/
abbrev sendOf (state : State.TransactionState) (message : Message fork) (v : U256) : U256 :=
  sub v (feeOf state message v)

/-- The state after the recipient's write: `balances[_to] = balT + sendAmount`. -/
abbrev creditedFee (state : State.TransactionState) (message : Message fork) (v a : U256) :
    State.TransactionState :=
  writeSlot (readSlot (debited state message v) message.currentTarget (recipientSlot a))
    message.currentTarget (recipientSlot a) (add (balT state message v a) (sendOf state message v))

/-- The substate after the recipient's write. -/
abbrev creditedSubFee (fork : Fork) (substate : Substate) (state : State.TransactionState)
    (message : Message fork) (v a : U256) : Substate :=
  storeSub fork (accessSlot (debitedSub fork substate state message v) message.currentTarget
      (recipientSlot a)) message.currentTarget (recipientSlot a)
    (originalAt state message.currentTarget (recipientSlot a)) (balT state message v a)
    (add (balT state message v a) (sendOf state message v))

/-- The slot of `balances[owner]` for the owner read from slot 0 of `st`. -/
abbrev ownerSlotOf (st : State.TransactionState) (c : Address) : U256 :=
  ownerSlot (storageAt st c 0)

/-- `balances[owner]` in `st`. -/
abbrev balOf (st : State.TransactionState) (c : Address) : U256 :=
  storageAt st c (ownerSlotOf st c)

/-- The state after the owner's write `balances[owner] = balOf + fee` (slot 0 read twice). -/
abbrev ownedB (st : State.TransactionState) (c : Address) (fee : U256) :
    State.TransactionState :=
  writeSlot (readSlot (readSlot (readSlot st c 0) c (ownerSlotOf st c)) c 0) c (ownerSlotOf st c)
    (add (balOf st c) fee)

/-- The substate after the owner's write, with `o` the word of the slot before the transaction. -/
abbrev ownedSubB (fork : Fork) (ss : Substate) (st : State.TransactionState) (c : Address)
    (o fee : U256) : Substate :=
  storeSub fork (accessSlot (accessSlot (accessSlot ss c 0) c (ownerSlotOf st c)) c 0) c
    (ownerSlotOf st c) o (balOf st c) (add (balOf st c) fee)

/-- The substate after the owner's log `Transfer(caller, owner', fee)`, `owner'` read from slot
0 after the owner's write. -/
abbrev ownerLoggedB (fork : Fork) (ss : Substate) (st : State.TransactionState)
    (message : Message fork) (o fee : U256) : Substate :=
  { accessSlot (ownedSubB fork ss st message.currentTarget o fee) message.currentTarget 0 with
    logs := (ownedSubB fork ss st message.currentTarget o fee).logs.push
      (transferLog message.currentTarget (bitwiseAnd ADDR_MASK message.caller.toU256)
        (bitwiseAnd ADDR_MASK (ownerKey
          (storageAt (ownedB st message.currentTarget fee) message.currentTarget 0))) fee) }

/-- The substate at the end: then the main log `Transfer(caller, _to, send)`. -/
abbrev feeSubB (fork : Fork) (ss : Substate) (st : State.TransactionState)
    (message : Message fork) (o fee send a : U256) : Substate :=
  { ownerLoggedB fork ss st message o fee with
    logs := (ownerLoggedB fork ss st message o fee).logs.push
      (transferLog message.currentTarget (bitwiseAnd ADDR_MASK message.caller.toU256)
        (bitwiseAnd ADDR_MASK a) send) }

/-- From 10298, the owner's credit, both logs and the STOP at 1931. -/
theorem ownerPart (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    (hstatic : message.isStatic = false) {st : State.TransactionState} {ss : Substate}
    (hacc : hasAccount st message.currentTarget) {send fee v a sel o : U256} {M : ByteArray}
    (hM : M.size = 96) (hptr : loadWord (memoryReadBytes M 64 32) 0 32 = 0x60)
    (hc0 : coldIn ss message.currentTarget 0 = false) {cO : Bool}
    (hcO : coldIn ss message.currentTarget (ownerSlotOf st message.currentTarget) = cO)
    (ho : originalAt st message.currentTarget (ownerSlotOf st message.currentTarget) = o)
    (hown : (balOf st message.currentTarget).toNat + fee.toNat < 2 ^ 256) {gas : Nat}
    (hg : 4409 + slotCost cO + sstoreCost fork o (balOf st message.currentTarget)
      (add (balOf st message.currentTarget) fee) false ≤ gas) :
    Gas.SpecG fork (At CODE message 10298 [0x40, send, fee, v, a, 0x1699, v, a, 0x078a, sel] M gas st ss)
      (Halted false .empty (gas - (4409 + slotCost cO + sstoreCost fork o (balOf st message.currentTarget)
          (add (balOf st message.currentTarget) fee) false))
        (readSlot (ownedB st message.currentTarget fee) message.currentTarget 0)
        (feeSubB fork ss st message o fee send a)) := by
  simp only [ownerSlotOf, balOf, ownedB, feeSubB, ownerLoggedB, ownedSubB] at hcO ho hown hg ⊢
  step ownerCall (cO := cO) hfork rfl (by simp) hc0 (by rw [coldIn_accessSlot_of_warm hc0]; exact hcO)
    (by gas_ok) hM
  step addBlock (by simp) (by valid_dest) hown (by gas_ok)
  at_pc 10412
  step ownerStore hfork (by rw [storageAt_readSlot, storageAt_readSlot]) hglam (by simp) hstatic
    (hasAccount_readSlot (hasAccount_readSlot hacc))
    (coldIn_accessSlot_false (coldIn_accessSlot_false hc0)) (coldIn_accessSlot_self _ _ _)
    (by rw [originalAt_readSlot, originalAt_readSlot, storageAt_readSlot, storageAt_readSlot, ho]
        gas_ok)
    (size_mapMem hM _ _)
  rw [originalAt_readSlot, originalAt_readSlot, storageAt_readSlot, storageAt_readSlot, ho]
  step ownerLog hfork rfl (by simp) hstatic
    (coldIn_storeSub_false (coldIn_accessSlot_self _ _ _)) (by gas_ok)
    (size_mapMem (size_mapMem hM _ _) _ _)
    (ptr_mapMem (size_mapMem hM _ _) (ptr_mapMem hM hptr _ _) _ _)
  step logBlock128 (by simp) hstatic (by gas_ok)
    (by rw [ByteArray.size_append, size_wordBytes]
        exact congrArg (· + 32) (size_mapMem (size_mapMem hM _ _) _ _))
    (by rw [read64_append (size_mapMem (size_mapMem hM _ _) _ _)]
        exact ptr_mapMem (size_mapMem hM _ _) (ptr_mapMem hM hptr _ _) _ _)
  refine (TransferOk.endBlock (by gas_ok)).consequence (fun _ h => h) ?_
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  exact ⟨hr, he, ho, by rw [hgas]; gas_ok, hs, hss⟩

/-- The price of the recipient's write (warm). -/
abbrev creditCostFee (fork : Fork) (state : State.TransactionState) (message : Message fork)
    (v a : U256) : Nat :=
  sstoreCost fork (originalAt state message.currentTarget (recipientSlot a))
    (balT state message v a) (add (balT state message v a) (sendOf state message v)) false

/-- The memory at 10298: the four lookups of the debit and the credit. -/
abbrev memA (M : ByteArray) (message : Message fork) (a : U256) : ByteArray :=
  mapMem (mapMem (mapMem (mapMem M (callerKey message) 2) (callerKey message) 2) (mkey a) 2)
    (mkey a) 2

/-- From 9883, with a fee above 0, up to the owner's credit at 10298. -/
theorem feeHead (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
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
    {gas : Nat}
    (hg : 964 + readCost c3 c4 cS cT + mulCost v +
      capCost (rawFee state message v) (storageAt state message.currentTarget 4) +
      debitCost fork state message v + creditCostFee fork state message v a + 2401 ≤ gas) :
    Gas.HoareG fork (At CODE message 9883 [v, a, 0x1699, v, a, 0x078a, sel] M gas state substate)
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
    sendOf, creditedFee, creditedSubFee, debitedSub, access3, memA] at hg hfee hfv hbal hto
  simp only [readCost, debitCost, creditCostFee, rawFee, feeOf, balS, balT, debited, reads3,
    sendOf, creditedFee, creditedSubFee, debitedSub, access3, memA] at hacc4 ⊢
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
  step debitStore hfork hglam (by simp) hstatic hacc3 (coldIn_accessSlot_self _ _ _) (by gas_ok)
    (by simp only [storageAt_readSlot, originalAt_readSlot]; gas_ok) (size_mapMem hM _ _)
  simp only [storageAt_readSlot, originalAt_readSlot]
  step creditCall hfork (by simp) (cT := cT) (by rw [coldIn_storeSub]; exact hcT) (by gas_ok)
    (size_mapMem (size_mapMem hM _ _) _ _)
  step addBlock (by simp) (by valid_dest) hto (by gas_ok)
  at_pc 10221
  step creditStoreFee hfork hglam hfee (by simp) hstatic hacc4 (coldIn_accessSlot_self _ _ _)
    (by gas_ok)
    (by simp only [storageAt_readSlot, originalAt_readSlot, originalAt_writeSlot hacc3]; gas_ok)
    (size_mapMem (size_mapMem (size_mapMem hM _ _) _ _) _ _)
  simp only [storageAt_readSlot, originalAt_readSlot, originalAt_writeSlot hacc3]
  exact restate rfl rfl rfl (by gas_ok) rfl rfl

/-- The word of slot 0 read for the owner's credit (after the recipient's write). -/
abbrev ownerWord (state : State.TransactionState) (message : Message fork) (v a : U256) : U256 :=
  storageAt (creditedFee state message v a) message.currentTarget 0

/-- `balances[owner]`, read after the recipient's write. -/
abbrev balO (state : State.TransactionState) (message : Message fork) (v a : U256) : U256 :=
  balOf (creditedFee state message v a) message.currentTarget

/-- The state at the end. -/
abbrev feeState (state : State.TransactionState) (message : Message fork) (v a : U256) :
    State.TransactionState :=
  readSlot (ownedB (creditedFee state message v a) message.currentTarget (feeOf state message v))
    message.currentTarget 0

/-- The substate at the end. -/
abbrev feeSub (fork : Fork) (substate : Substate) (state : State.TransactionState)
    (message : Message fork) (v a : U256) : Substate :=
  feeSubB fork (creditedSubFee fork substate state message v a) (creditedFee state message v a)
    message (originalAt state message.currentTarget (ownerSlot (ownerWord state message v a)))
    (feeOf state message v) (sendOf state message v) a

/-- The price of the owner's write (warm). -/
abbrev ownerCost (fork : Fork) (state : State.TransactionState) (message : Message fork)
    (v a : U256) : Nat :=
  sstoreCost fork (originalAt state message.currentTarget (ownerSlot (ownerWord state message v a)))
    (balO state message v a) (add (balO state message v a) (feeOf state message v)) false

/-- From 9883, with a fee above 0, the success path of `transfer` up to the STOP at 1931. -/
theorem bodyFee (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
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
    {gas : Nat}
    (hg : 5373 + readCost c3 c4 cS cT + slotCost cO + mulCost v +
      capCost (rawFee state message v) (storageAt state message.currentTarget 4) +
      debitCost fork state message v + creditCostFee fork state message v a +
      ownerCost fork state message v a ≤ gas) :
    Gas.SpecG fork (At CODE message 9883 [v, a, 0x1699, v, a, 0x078a, sel] M gas state substate)
      (Halted false .empty (gas - (5373 + readCost c3 c4 cS cT + slotCost cO + mulCost v +
        capCost (rawFee state message v) (storageAt state message.currentTarget 4) +
        debitCost fork state message v + creditCostFee fork state message v a +
        ownerCost fork state message v a))
        (feeState state message v a) (feeSub fork substate state message v a)) := by
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
  have hA := feeHead (sel := sel) hfork hglam hlong hsz hstatic hacc hM hov hfee hfv hbal hto hc3
    hc4 hcS hcT (gas := gas) (by simp only [ownerCost] at hg; omega)
  have hB := ownerPart (message := message) (st := creditedFee state message v a)
    (ss := creditedSubFee fork substate state message v a) (send := sendOf state message v)
    (v := v) (a := a) (sel := sel) (M := memA M message a) hfork hglam hstatic (hasAccount_writeSlot hacc4)
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
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  refine ⟨hr, he, ho, ?_, hs, hss⟩
  rw [hgas]
  simp only [ownerCost, ownerSlotOf, balOf, balO, ownerWord]
  omega

end UsdtVerify.TransferFee
