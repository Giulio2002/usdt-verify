import UsdtVerify.Functions.TransferOk

/-!
# transfer(address,uint256): the success path from 9883, with a fee of 0

`body` composes the blocks of `TransferOk` from BasicToken's `transfer` at 9883 to the STOP at
1931, for a call whose fee, as the bytecode computes it, is 0.

The states and substates along the path are named below; the recipient's balance is read in the
state after the sender's write (`debited`), as the bytecode reads it.
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

/-- The raw fee of `_value = v`: `mul(v, basisPointsRate) / 10000` (slot 3). -/
abbrev rawFee (state : State.TransactionState) (message : Message fork) (v : U256) : U256 :=
  div (mul v (storageAt state message.currentTarget 3)) 0x2710

/-- The fee of `_value = v`, as the bytecode computes it: the raw fee, capped by `maximumFee`
(slot 4). -/
abbrev feeOf (state : State.TransactionState) (message : Message fork) (v : U256) : U256 :=
  capped (rawFee state message v) (storageAt state message.currentTarget 4)

/-- The state after the reads of slots 3, 4 and `balances[msg.sender]`. -/
abbrev reads3 (state : State.TransactionState) (message : Message fork) :
    State.TransactionState :=
  readSlot (readSlot (readSlot state message.currentTarget 3) message.currentTarget 4)
    message.currentTarget (senderSlot message)

/-- The substate after the accesses of slots 3, 4 and `balances[msg.sender]`. -/
abbrev access3 (substate : Substate) (message : Message fork) : Substate :=
  accessSlot (accessSlot (accessSlot substate message.currentTarget 3) message.currentTarget 4)
    message.currentTarget (senderSlot message)

/-- The sender's balance before the call. -/
abbrev balS (state : State.TransactionState) (message : Message fork) : U256 :=
  storageAt state message.currentTarget (senderSlot message)

/-- The state after the sender's write: `balances[msg.sender] = balS - v`. -/
abbrev debited (state : State.TransactionState) (message : Message fork) (v : U256) :
    State.TransactionState :=
  writeSlot (reads3 state message) message.currentTarget (senderSlot message)
    (sub (balS state message) v)

/-- The substate after the sender's write. -/
abbrev debitedSub (fork : Fork) (substate : Substate) (state : State.TransactionState)
    (message : Message fork) (v : U256) : Substate :=
  storeSub fork (access3 substate message) message.currentTarget (senderSlot message)
    (originalAt state message.currentTarget (senderSlot message)) (balS state message)
    (sub (balS state message) v)

/-- The recipient's balance, read after the sender's write. -/
abbrev balT (state : State.TransactionState) (message : Message fork) (v a : U256) : U256 :=
  storageAt (debited state message v) message.currentTarget (recipientSlot a)

/-- The state after the recipient's write: `balances[_to] = balT + v`. -/
abbrev credited (state : State.TransactionState) (message : Message fork) (v a : U256) :
    State.TransactionState :=
  writeSlot (readSlot (debited state message v) message.currentTarget (recipientSlot a))
    message.currentTarget (recipientSlot a) (add (balT state message v a) v)

/-- The substate after the recipient's write and the Transfer log. -/
abbrev creditedSub (fork : Fork) (substate : Substate) (state : State.TransactionState)
    (message : Message fork) (v a : U256) : Substate :=
  storeSub fork (accessSlot (debitedSub fork substate state message v) message.currentTarget
      (recipientSlot a)) message.currentTarget (recipientSlot a)
    (originalAt state message.currentTarget (recipientSlot a)) (balT state message v a)
    (add (balT state message v a) v)

/-- The substate at the end: the Transfer log appended. -/
abbrev loggedSub (fork : Fork) (substate : Substate) (state : State.TransactionState)
    (message : Message fork) (v a : U256) : Substate :=
  { creditedSub fork substate state message v a with
    logs := (creditedSub fork substate state message v a).logs.push
      (transferLog message.currentTarget (bitwiseAnd ADDR_MASK message.caller.toU256)
        (bitwiseAnd ADDR_MASK a) v) }

/-- The price of the sender's write (the slot is warm: the code has just read it). -/
abbrev debitCost (fork : Fork) (state : State.TransactionState) (message : Message fork)
    (v : U256) : Nat :=
  sstoreCost fork (originalAt state message.currentTarget (senderSlot message))
    (balS state message) (sub (balS state message) v) false

/-- The price of the recipient's write (warm too). -/
abbrev creditCost (fork : Fork) (state : State.TransactionState) (message : Message fork)
    (v a : U256) : Nat :=
  sstoreCost fork (originalAt state message.currentTarget (recipientSlot a))
    (balT state message v a) (add (balT state message v a) v) false

/-- The coldness accessed by the reads: `c3`, `c4`, the sender's slot `cS`, the recipient's `cT`. -/
abbrev readCost (c3 c4 cS cT : Bool) : Nat :=
  slotCost c3 + slotCost c4 + slotCost cS + slotCost cT

theorem coldIn_storeSub {fork : Fork} {ss : Substate} {target : EthLib.Base.Address}
    {n m o c w : U256} :
    coldIn (storeSub fork (accessSlot ss target n) target n o c w) target m =
      coldIn (accessSlot ss target n) target m := by
  show coldIn (accessSlot (accessSlot ss target n) target n) target m = _
  rw [accessSlot_accessSlot]

/-- From 9883, with a fee of 0, the success path of `transfer` up to the STOP at 1931. -/
theorem body (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    (hlong : 68 ≤ message.data.size) (hsz : message.data.size < 2 ^ 256)
    (hstatic : message.isStatic = false) (hacc : hasAccount state message.currentTarget)
    {v a sel : U256} {M : ByteArray} (hM : M.size = 96)
    (hptr : loadWord (memoryReadBytes M 64 32) 0 32 = 0x60)
    (hov : v.toNat * (storageAt state message.currentTarget 3).toNat < 2 ^ 256)
    (hfee : feeOf state message v = 0)
    (hbal : v.toNat ≤ (balS state message).toNat)
    (hto : (balT state message v a).toNat + v.toNat < 2 ^ 256)
    {c3 c4 cS cT : Bool} (hc3 : coldIn substate message.currentTarget 3 = c3)
    (hc4 : coldIn (accessSlot substate message.currentTarget 3) message.currentTarget 4 = c4)
    (hcS : coldIn (accessSlot (accessSlot substate message.currentTarget 3) message.currentTarget 4)
      message.currentTarget (senderSlot message) = cS)
    (hcT : coldIn (access3 substate message) message.currentTarget (recipientSlot a) = cT)
    {gas : Nat}
    (hstip1 : 530 + slotCost c3 + slotCost c4 + slotCost cS + mulCost v +
      capCost (rawFee state message v) (storageAt state message.currentTarget 4) + 2400 ≤ gas)
    (hstip2 : 837 + readCost c3 c4 cS cT + mulCost v +
      capCost (rawFee state message v) (storageAt state message.currentTarget 4) +
      debitCost fork state message v + 2401 ≤ gas)
    (hg : 2829 + readCost c3 c4 cS cT + mulCost v +
      capCost (rawFee state message v) (storageAt state message.currentTarget 4) +
      debitCost fork state message v + creditCost fork state message v a ≤ gas) :
    Spec fork (At CODE message 9883 [v, a, 0x1699, v, a, 0x078a, sel] M gas state substate)
      (Halted false .empty (gas - (2829 + readCost c3 c4 cS cT + mulCost v +
        capCost (rawFee state message v) (storageAt state message.currentTarget 4) +
        debitCost fork state message v + creditCost fork state message v a))
        (credited state message v a) (loggedSub fork substate state message v a)) := by
  simp only [readCost, debitCost, creditCost, rawFee, feeOf, balS, balT, debited, reads3] at hstip1 hstip2 hg hfee hbal hto ⊢
  have hacc3 : hasAccount (reads3 state message) message.currentTarget :=
    hasAccount_readSlot (hasAccount_readSlot (hasAccount_readSlot hacc))
  have hacc4 : hasAccount (readSlot (debited state message v) message.currentTarget
      (recipientSlot a)) message.currentTarget :=
    hasAccount_readSlot (hasAccount_writeSlot hacc3)
  simp only [debited, reads3, balS] at hacc3 hacc4
  step payloadOk hlong hsz (by simp) (by gas_ok)
  step feeCall hfork (by simp) hc3 (by gas_ok)
  step mulBlock (by simp) (by valid_dest) hov (by gas_ok)
  at_pc 9937
  step divCall (by simp) (by gas_ok)
  step divBlock (by simp) (by valid_dest) (by decide) (by gas_ok)
  at_pc 9951
  step capBlock hfork (by simp) hc4 (by simp only [storageAt_readSlot]; gas_ok)
  simp only [storageAt_readSlot]
  step reshape (s' := (0x40 : U256) :: 0 :: 0 :: v :: a :: [0x1699, v, a, 0x078a, sel])
    (by rw [hfee]) rfl rfl
  step sendCall (by simp) (by gas_ok)
  step subBlock (by simp) (by valid_dest) (by simp) (by gas_ok)
  at_pc 9988
  step reshape (s' := v :: (0x40 : U256) :: 0 :: 0 :: v :: a :: [0x1699, v, a, 0x078a, sel])
    (by simp [sub]) rfl rfl
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
  step creditStore hfork hglam (by simp) hstatic hacc4 (coldIn_accessSlot_self _ _ _) (by gas_ok)
    (by simp only [storageAt_readSlot, originalAt_readSlot, originalAt_writeSlot hacc3]; gas_ok)
    (size_mapMem (size_mapMem (size_mapMem hM _ _) _ _) _ _)
  simp only [storageAt_readSlot, originalAt_readSlot, originalAt_writeSlot hacc3]
  step logBlock (by simp) hstatic (by gas_ok)
    (size_mapMem (size_mapMem (size_mapMem (size_mapMem hM _ _) _ _) _ _) _ _)
    (ptr_mapMem (size_mapMem (size_mapMem (size_mapMem hM _ _) _ _) _ _)
      (ptr_mapMem (size_mapMem (size_mapMem hM _ _) _ _)
        (ptr_mapMem (size_mapMem hM _ _) (ptr_mapMem hM hptr _ _) _ _) _ _) _ _)
  refine (endBlock (by gas_ok)).consequence (fun _ h => h) ?_
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  exact ⟨hr, he, ho, by rw [hgas]; gas_ok, hs, hss⟩

end UsdtVerify.TransferOk
