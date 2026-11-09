import UsdtVerify.Usdt.Proofs.TransferFrom

/-!
# transfer and transferFrom with a fee above 0: the blocks

Proves the Hoare triples of the blocks that credit the owner with the fee, in transfer and
transferFrom, and the success path of transfer from 9883 with a fee above 0.

The parts below keep their own headers:

- transfer(address,uint256): the blocks of the owner's credit, for a fee above 0
- transfer(address,uint256): the success path from 9883, with a fee above 0
- transferFrom(address,address,uint256): the blocks of the owner's credit, for a fee above 0
-/

section

/-!
## transfer(address,uint256): the blocks of the owner's credit, for a fee above 0

BasicToken's `transfer` at 10289 runs `if (fee > 0)`:

- 10298: reads `owner` (the low 160 bits of slot 0, read again: warm) and `balances[owner]`,
  calls `add(balance, fee)`.
- 10412: reads `owner` again and writes `balances[owner]`.
- 10513: reads `owner` again and logs `Transfer(msg.sender, owner, fee)` (LOG3); the memory grows
  to 128 bytes.
- 10647: the main log `Transfer(msg.sender, _to, sendAmount)`, now over 128 bytes of memory (no
  expansion), back to 5785.
-/

namespace UsdtVerify.TransferFee

open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts
open Transfer SafeMath TransferOk

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate}

/-- Equal parts up to recorded reads: `rfl`, or the read lemmas, then `rfl`. -/
macro "eqs" : tactic => `(tactic| first
  | rfl
  | (simp only [storageAt_readSlot, originalAt_readSlot]; done)
  | (simp only [storageAt_readSlot, originalAt_readSlot]; rfl))

/-- GENERIC: accessing a warm slot changes no slot's coldness. -/
theorem coldIn_accessSlot_of_warm {ss : Substate} {target : EthLib.Base.Address} {n m : U256}
    (hn : coldIn ss target n = false) :
    coldIn (accessSlot ss target n) target m = coldIn ss target m := by
  by_cases h : U256.toBeBytes m = U256.toBeBytes n
  · rw [show coldIn (accessSlot ss target n) target m = coldIn (accessSlot ss target n) target n by
        simp only [coldIn, h],
      coldIn_accessSlot_self, show coldIn ss target m = coldIn ss target n by simp only [coldIn, h],
      hn]
  · exact coldIn_accessSlot h

/-- At 10221, the code writes the new balance of the recipient; with a fee above 0 it goes on to
the owner's credit at 10298. -/
theorem creditStoreFee (hfork : .berlin ≤ fork)
    {nt send fee v a : U256} (hfee : fee ≠ 0)
    {rest : List U256} (hrest : rest.length ≤ 800) (hstatic : message.isStatic = false)
    (hacc : hasAccount state message.currentTarget) {cT : Bool}
    (hcT : coldIn substate message.currentTarget (recipientSlot a) = cT) {gas : Nat}
    (hstip : 2401 ≤ gas)
    (hg : 127 + Gas.writeCost fork (originalAt state message.currentTarget (recipientSlot a))
      (storageAt state message.currentTarget (recipientSlot a)) nt cT ≤ gas)
    {M : ByteArray} (hM : M.size = 96) :
    Gas.HoareG fork (At CODE message 10221 (nt :: 0x40 :: send :: fee :: v :: a :: rest) M gas state
        substate)
      (At CODE message 10298 (0x40 :: send :: fee :: v :: a :: rest) (mapMem M (mkey a) 2)
        (gas - (127 + Gas.writeCost fork (originalAt state message.currentTarget (recipientSlot a))
          (storageAt state message.currentTarget (recipientSlot a)) nt cT))
        (writeSlot state message.currentTarget (recipientSlot a) nt)
        (storeSub fork substate message.currentTarget (recipientSlot a)
          (originalAt state message.currentTarget (recipientSlot a))
          (storageAt state message.currentTarget (recipientSlot a)) nt)) := by
  have hpos : 0 < fee.toNat := by
    rcases Nat.eq_zero_or_pos fee.toNat with h | h
    · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h)) hfee
    · exact h
  simp only [recipientSlot, mkey] at hcT hg ⊢
  step jumpdestR
  step pushR 1 (0x02 : U256)
  step pushR 1 (0 : U256)
  step dupR 7
  at_pc 10227
  step hashTail (by decide) (by simp; omega) hM (by gas_ok)
  at_pc 10285
  step dupR 1
  step swapR 0
  norm
  step Gas.sstoreWG hfork (by code_fact) (by code_fact) hstatic hacc hcT (by gas_ok) (by gas_ok)
  step popR
  step pushR 1 (0 : U256)
  step dupR 3
  step binR 0x11 (instruction_of_stackOnlyStep rfl)
  step unR 0x15 instruction_iszero
  step pushR 2 (0x2997 : U256)
  step jumpi0R (by simp [greaterThan, isZero, hpos])
  exact restate (by decide) rfl rfl (by gas_ok) rfl rfl

/-- The owner word as the code computes it from slot 0: `w0 / 256^0`, masked to 160 bits. -/
abbrev ownerKey (w0 : U256) : U256 := bitwiseAnd ADDR_MASK (div w0 (exp (0x0100 : U256) (0 : U256)))

/-- The slot of `balances[owner]` for the word `w0` of slot 0. -/
abbrev ownerSlot (w0 : U256) : U256 := mapSlot (mkey (ownerKey w0)) 2

/-- At 10298, the code reads `owner` (slot 0, warm) and `balances[owner]`, and calls
`add(balance, fee)`. -/
theorem ownerCall (hfork : .berlin ≤ fork) {w0 : U256}
    (hw0 : storageAt state message.currentTarget 0 = w0) {send fee v a : U256} {rest : List U256}
    (hrest : rest.length ≤ 800) (hc0 : coldIn substate message.currentTarget 0 = false) {cO : Bool}
    (hcO : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget
      (ownerSlot (w0)) = cO) {gas : Nat}
    (hg : 261 + slotCost cO ≤ gas) {M : ByteArray} (hM : M.size = 96) :
    Gas.HoareG fork (At CODE message 10298 (0x40 :: send :: fee :: v :: a :: rest) M gas state
        substate)
      (At CODE message 11001 (fee :: storageAt state message.currentTarget
          (ownerSlot (w0)) ::
        0x28ac :: 0x40 :: send :: fee :: v :: a :: rest)
        (mapMem M (mkey (ownerKey (w0))) 2)
        (gas - (261 + slotCost cO))
        (readSlot (readSlot state message.currentTarget 0) message.currentTarget
          (ownerSlot (w0)))
        (accessSlot (accessSlot substate message.currentTarget 0) message.currentTarget
          (ownerSlot (w0)))) := by
  have hexp : exponentBytes (0 : U256) = 0 := by decide
  simp only [ownerSlot, ownerKey, mkey] at hcO ⊢
  step pushR 2 (0x28ac : U256)
  step dupR 3
  step pushR 1 (0x02 : U256)
  step pushR 1 (0 : U256)
  step dupR 0
  step pushR 1 (0 : U256)
  step swapR 0
  norm
  step Gas.sloadG hfork (cold := false) (by code_fact) (by code_fact) hc0 (by gas_ok)
  rw [show state.getStorage message.currentTarget (U256.toBeBytes 0) = w0 from hw0]
  step swapR 0
  norm
  step pushR 2 (0x0100 : U256)
  step Gas.expLG (Nat.le_trans (by decide) hfork) (by code_fact) (by code_fact) (by gas_ok)
  step swapR 0
  norm
  step binR 0x04 (instruction_of_stackOnlyStep rfl)
  step pushR 20 ADDR_MASK
  step binR 0x16 (instruction_of_stackOnlyStep rfl)
  at_pc 10340
  step hashTail (by decide) (by simp; omega) hM (by gas_ok)
  at_pc 10398
  step Gas.sloadG hfork (cold := cO) (by code_fact) (by code_fact)
    hcO (by gas_ok)
  step pushR 2 (0x2af9 : U256)
  step swapR 0
  norm
  step swapR 1
  norm
  step swapR 0
  norm
  step pushR 4 (0xffffffff : U256)
  step binR 0x16 (instruction_of_stackOnlyStep rfl)
  step jumpR
  exact restate (by decide) (by eqs) rfl (by gas_ok) (by eqs) (by eqs)

/-- At 10412, the code reads `owner` again (warm) and writes the new balance of the owner. -/
theorem ownerStore (hfork : .berlin ≤ fork) {w0 : U256}
    (hw0 : storageAt state message.currentTarget 0 = w0)
    {no send fee v a : U256} {rest : List U256} (hrest : rest.length ≤ 800)
    (hstatic : message.isStatic = false) (hacc : hasAccount state message.currentTarget)
    (hc0 : coldIn substate message.currentTarget 0 = false) {cO : Bool}
    (hcO : coldIn substate message.currentTarget
      (ownerSlot (w0)) = cO) {gas : Nat}
    (hg : 238 + Gas.writeCost fork
      (originalAt state message.currentTarget (ownerSlot (w0)))
      (storageAt state message.currentTarget (ownerSlot (w0)))
      no cO + 2300 ≤ gas)
    {M : ByteArray} (hM : M.size = 96) :
    Gas.HoareG fork (At CODE message 10412 (no :: 0x40 :: send :: fee :: v :: a :: rest) M gas state
        substate)
      (At CODE message 10513 (0x40 :: send :: fee :: v :: a :: rest)
        (mapMem M (mkey (ownerKey (w0))) 2)
        (gas - (238 + Gas.writeCost fork (originalAt state message.currentTarget
          (ownerSlot (w0)))
          (storageAt state message.currentTarget (ownerSlot (w0)))
          no cO))
        (writeSlot (readSlot state message.currentTarget 0) message.currentTarget
          (ownerSlot (w0)) no)
        (storeSub fork (accessSlot substate message.currentTarget 0) message.currentTarget
          (ownerSlot (w0))
          (originalAt state message.currentTarget (ownerSlot (w0)))
          (storageAt state message.currentTarget (ownerSlot (w0)))
          no)) := by
  have hexp : exponentBytes (0 : U256) = 0 := by decide
  have hcO' : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget
      (ownerSlot (w0)) = cO := by
    rw [coldIn_accessSlot_of_warm hc0, hcO]
  simp only [ownerSlot, ownerKey, mkey] at hcO' hg ⊢
  step jumpdestR
  step pushR 1 (0x02 : U256)
  step pushR 1 (0 : U256)
  step dupR 0
  step pushR 1 (0 : U256)
  step swapR 0
  norm
  step Gas.sloadG hfork (cold := false) (by code_fact) (by code_fact) hc0 (by gas_ok)
  rw [show state.getStorage message.currentTarget (U256.toBeBytes 0) = w0 from hw0]
  step swapR 0
  norm
  step pushR 2 (0x0100 : U256)
  step Gas.expLG (Nat.le_trans (by decide) hfork) (by code_fact) (by code_fact) (by gas_ok)
  step swapR 0
  norm
  step binR 0x04 (instruction_of_stackOnlyStep rfl)
  step pushR 20 ADDR_MASK
  step binR 0x16 (instruction_of_stackOnlyStep rfl)
  at_pc 10451
  step hashTail (by decide) (by simp; omega) hM (by gas_ok)
  at_pc 10509
  step dupR 1
  step swapR 0
  norm
  step Gas.sstoreWG hfork (by code_fact) (by code_fact) hstatic (hasAccount_readSlot hacc) hcO'
    (by gas_ok) (by rw [originalAt_readSlot, storageAt_readSlot]; gas_ok)
  rw [originalAt_readSlot, storageAt_readSlot]
  step popR
  exact restate (by decide) rfl rfl (by gas_ok) rfl rfl

/-- At 10513, the code reads `owner` again (warm) and logs `Transfer(msg.sender, owner, fee)`;
the fee word goes to memory at 0x60, which grows to 128 bytes. -/
theorem ownerLog (hfork : .berlin ≤ fork) {w0 : U256}
    (hw0 : storageAt state message.currentTarget 0 = w0) {send fee v a : U256} {rest : List U256}
    (hrest : rest.length ≤ 800) (hstatic : message.isStatic = false)
    (hc0 : coldIn substate message.currentTarget 0 = false) {gas : Nat} (hg : 1967 ≤ gas)
    {M : ByteArray} (hM : M.size = 96) (hptr : loadWord (memoryReadBytes M 64 32) 0 32 = 0x60) :
    Gas.HoareG fork (At CODE message 10513 (0x40 :: send :: fee :: v :: a :: rest) M gas state
        substate)
      (At CODE message 10647 (0x40 :: send :: fee :: v :: a :: rest) (M ++ wordBytes fee)
        (gas - 1967) (readSlot state message.currentTarget 0)
        { accessSlot substate message.currentTarget 0 with
          logs := substate.logs.push (transferLog message.currentTarget
            (bitwiseAnd ADDR_MASK message.caller.toU256)
            (bitwiseAnd ADDR_MASK (ownerKey w0)) fee) }) := by
  have hexp : exponentBytes (0 : U256) = 0 := by decide
  have hext0 : extendMemory M.size [((0x40 : U256), (32 : U256))] = ⟨0, 0⟩ := by
    rw [hM]; decide
  have hext1 : extendMemory M.size [((0x60 : U256), (32 : U256))] = ⟨3, 32⟩ := by
    rw [hM]; decide
  have hsz : (M ++ wordBytes fee).size = 128 := by
    rw [ByteArray.size_append, hM, size_wordBytes]
  have hext2 : extendMemory (M ++ wordBytes fee).size [((0x40 : U256), (32 : U256))] =
      ⟨0, 0⟩ := by rw [hsz]; decide
  have hext3 : extendMemory (M ++ wordBytes fee).size [((0x60 : U256), (0x20 : U256))] =
      ⟨0, 0⟩ := by rw [hsz]; decide
  have hmem1 : memoryWrite (memoryExtend M 32) (0x60 : U256).toNat (wordBytes fee) =
      M ++ wordBytes fee := by
    have h := memoryWrite_extend_end (memory := M) (value := wordBytes fee)
    rwa [size_wordBytes, hM] at h
  have hread2 : memoryReadBytes (M ++ wordBytes fee) 64 32 = memoryReadBytes M 64 32 := by
    simp only [memoryReadBytes, ByteArray.extract_append, hM]
    simp
  have hlog : logCost (3 : Fin 5).val (0x20 : U256) = 1756 := by decide
  simp only [ownerKey]
  step pushR 1 (0 : U256)
  step dupR 0
  step swapR 0
  norm
  step Gas.sloadG hfork (cold := false) (by code_fact) (by code_fact) hc0 (by gas_ok)
  rw [show state.getStorage message.currentTarget (U256.toBeBytes 0) = w0 from hw0]
  step swapR 0
  norm
  step pushR 2 (0x0100 : U256)
  step Gas.expLG (Nat.le_trans (by decide) hfork) (by code_fact) (by code_fact) (by gas_ok)
  step swapR 0
  norm
  step binR 0x04 (instruction_of_stackOnlyStep rfl)
  step pushR 20 ADDR_MASK
  step binR 0x16 (instruction_of_stackOnlyStep rfl)
  step pushR 20 ADDR_MASK
  step binR 0x16 (instruction_of_stackOnlyStep rfl)
  step Gas.callerG (by code_fact) (by code_fact) (by gas_ok) (by stk_ok)
  step pushR 20 ADDR_MASK
  step binR 0x16 (instruction_of_stackOnlyStep rfl)
  step pushR 32 TransferOk.TRANSFER_TOPIC
  step dupR 5
  step pushR 1 (0x40 : U256)
  step Gas.mloadG (by code_fact) (by code_fact) (by rw [hext0]; gas_ok)
  step Gas.reshapeG (s' := 0x60 :: fee :: TransferOk.TRANSFER_TOPIC ::
      bitwiseAnd ADDR_MASK message.caller.toU256 ::
      bitwiseAnd ADDR_MASK (bitwiseAnd ADDR_MASK (div (w0)
        (exp (0x0100 : U256) (0 : U256)))) :: 0x40 :: send :: fee :: v :: a :: rest) (m' := M)
    (by rw [hext0, memoryExtend_zero]; exact congrArg (· :: _) hptr)
    (by rw [hext0, memoryExtend_zero]) (by rw [hext0])
  step dupR 0
  step dupR 2
  step dupR 1
  step Gas.mstoreG (by code_fact) (by code_fact) (by rw [hext1]; gas_ok)
  step Gas.reshapeG (m' := M ++ wordBytes fee) rfl (by rw [hext1]; exact hmem1) (by rw [hext1])
  step pushR 1 (0x20 : U256)
  step binR 0x01 instruction_add
  step swapR 1
  norm
  step popR
  step popR
  step pushR 1 (0x40 : U256)
  step Gas.mloadG (by code_fact) (by code_fact) (by rw [hext2]; gas_ok)
  step Gas.reshapeG (s' := 0x60 :: 0x80 :: TransferOk.TRANSFER_TOPIC ::
      bitwiseAnd ADDR_MASK message.caller.toU256 ::
      bitwiseAnd ADDR_MASK (bitwiseAnd ADDR_MASK (div (w0)
        (exp (0x0100 : U256) (0 : U256)))) :: 0x40 :: send :: fee :: v :: a :: rest)
    (m' := M ++ wordBytes fee)
    (by rw [hext2, memoryExtend_zero, show (0x40 : U256).toNat = 64 from rfl, hread2, hptr]; rfl)
    (by rw [hext2, memoryExtend_zero]) (by rw [hext2])
  step dupR 0
  step swapR 1
  norm
  step binR 0x03 instruction_sub
  step swapR 0
  norm
  step Gas.reshapeG (s' := 0x60 :: 0x20 :: ([TransferOk.TRANSFER_TOPIC,
      bitwiseAnd ADDR_MASK message.caller.toU256,
      bitwiseAnd ADDR_MASK (bitwiseAnd ADDR_MASK (div (w0)
        (exp (0x0100 : U256) (0 : U256))))] ++ (0x40 :: send :: fee :: v :: a :: rest))) rfl rfl rfl
  step Gas.logG (n := 3) (byte := 0xa3) rfl (by code_fact) (by code_fact) rfl hstatic
    (by rw [hlog, hext3]; gas_ok)
  step Gas.reshapeG rfl (by rw [hext3, memoryExtend_zero]) (by rw [hlog, hext3])
  refine restate (by decide) rfl rfl (by gas_ok) (by eqs) ?_
  rw [hext3, memoryExtend_zero, show (0x60 : U256).toNat = 96 from rfl,
    show (0x20 : U256).toNat = 32 from rfl, read_after hM _ (size_wordBytes fee)]

/-- At 10647, over 128 bytes of memory with the pointer 0x60 at 0x40, the code logs
`Transfer(msg.sender, _to, sendAmount)` and returns to 5785. -/
theorem logBlock128 {send fee v a : U256} {rest : List U256} (hrest : rest.length ≤ 900)
    (hstatic : message.isStatic = false) {gas : Nat} (hg : 1847 ≤ gas) {M : ByteArray}
    (hM : M.size = 128) (hptr : loadWord (memoryReadBytes M 64 32) 0 32 = 0x60) :
    Gas.HoareG fork (At CODE message 10647 (0x40 :: send :: fee :: v :: a :: 0x1699 :: rest) M gas
        state substate)
      (At CODE message 5785 rest (memoryWrite M 96 (wordBytes send)) (gas - 1847) state
        { substate with logs := substate.logs.push (transferLog message.currentTarget
          (bitwiseAnd ADDR_MASK message.caller.toU256) (bitwiseAnd ADDR_MASK a) send) }) := by
  have hsz : (memoryWrite M 96 (wordBytes send)).size = 128 := by
    rw [size_memoryWrite (by simp [hM, size_wordBytes]), hM]
  have hext0 : extendMemory M.size [((0x40 : U256), (32 : U256))] = ⟨0, 0⟩ := by
    rw [hM]; decide
  have hext1 : extendMemory M.size [((0x60 : U256), (32 : U256))] = ⟨0, 0⟩ := by
    rw [hM]; decide
  have hext2 : extendMemory (memoryWrite M 96 (wordBytes send)).size
      [((0x40 : U256), (32 : U256))] = ⟨0, 0⟩ := by rw [hsz]; decide
  have hext3 : extendMemory (memoryWrite M 96 (wordBytes send)).size
      [((0x60 : U256), (0x20 : U256))] = ⟨0, 0⟩ := by rw [hsz]; decide
  have hread2 : memoryReadBytes (memoryWrite M 96 (wordBytes send)) 64 32 =
      memoryReadBytes M 64 32 :=
    memoryReadBytes_memoryWrite_of_disjoint (by simp [hM, size_wordBytes])
      (by simp [size_wordBytes])
  have hread3 : memoryReadBytes (memoryWrite M 96 (wordBytes send)) 96 32 = wordBytes send := by
    have h := memoryReadBytes_memoryWrite (memory := M) (value := wordBytes send)
      (start := 96) (by simp [hM, size_wordBytes])
    rwa [size_wordBytes] at h
  have hlog : logCost (3 : Fin 5).val (0x20 : U256) = 1756 := by decide
  step jumpdestR
  step dupR 4
  step pushR 20 ADDR_MASK
  step binR 0x16 (instruction_of_stackOnlyStep rfl)
  step Gas.callerG (by code_fact) (by code_fact) (by gas_ok) (by stk_ok)
  step pushR 20 ADDR_MASK
  step binR 0x16 (instruction_of_stackOnlyStep rfl)
  step pushR 32 TransferOk.TRANSFER_TOPIC
  step dupR 4
  step pushR 1 (0x40 : U256)
  step Gas.mloadG (by code_fact) (by code_fact) (by rw [hext0]; gas_ok)
  step Gas.reshapeG (s' := 0x60 :: send :: TransferOk.TRANSFER_TOPIC ::
      bitwiseAnd ADDR_MASK message.caller.toU256 ::
      bitwiseAnd ADDR_MASK a :: 0x40 :: send :: fee :: v :: a :: 0x1699 :: rest) (m' := M)
    (by rw [hext0, memoryExtend_zero]; exact congrArg (· :: _) hptr)
    (by rw [hext0, memoryExtend_zero]) (by rw [hext0])
  step dupR 0
  step dupR 2
  step dupR 1
  step Gas.mstoreG (by code_fact) (by code_fact) (by rw [hext1]; gas_ok)
  step Gas.reshapeG (m' := memoryWrite M 96 (wordBytes send)) rfl
    (by rw [hext1, memoryExtend_zero]; rfl) (by rw [hext1])
  step pushR 1 (0x20 : U256)
  step binR 0x01 instruction_add
  step swapR 1
  norm
  step popR
  step popR
  step pushR 1 (0x40 : U256)
  step Gas.mloadG (by code_fact) (by code_fact) (by rw [hext2]; gas_ok)
  step Gas.reshapeG (s' := 0x60 :: 0x80 :: TransferOk.TRANSFER_TOPIC ::
      bitwiseAnd ADDR_MASK message.caller.toU256 ::
      bitwiseAnd ADDR_MASK a :: 0x40 :: send :: fee :: v :: a :: 0x1699 :: rest)
    (m' := memoryWrite M 96 (wordBytes send))
    (by rw [hext2, memoryExtend_zero, show (0x40 : U256).toNat = 64 from rfl, hread2, hptr]; rfl)
    (by rw [hext2, memoryExtend_zero]) (by rw [hext2])
  step dupR 0
  step swapR 1
  norm
  step binR 0x03 instruction_sub
  step swapR 0
  norm
  step Gas.reshapeG (s' := 0x60 :: 0x20 :: ([TransferOk.TRANSFER_TOPIC,
      bitwiseAnd ADDR_MASK message.caller.toU256,
      bitwiseAnd ADDR_MASK a] ++ (0x40 :: send :: fee :: v :: a :: 0x1699 :: rest))) rfl rfl rfl
  step Gas.logG (n := 3) (byte := 0xa3) rfl (by code_fact) (by code_fact) rfl hstatic
    (by rw [hlog, hext3]; gas_ok)
  step Gas.reshapeG rfl (by rw [hext3, memoryExtend_zero]) (by rw [hlog, hext3])
  step popR
  step popR
  step popR
  step popR
  step popR
  step jumpR
  refine restate (by decide) rfl rfl (by gas_ok) rfl ?_
  rw [hext3, memoryExtend_zero, show (0x60 : U256).toNat = 96 from rfl,
    show (0x20 : U256).toNat = 32 from rfl, hread3]

end UsdtVerify.TransferFee

end

section

/-!
## transfer(address,uint256): the success path from 9883, with a fee above 0

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
theorem ownerPart (hfork : .berlin ≤ fork)
    (hstatic : message.isStatic = false) {st : State.TransactionState} {ss : Substate}
    (hacc : hasAccount st message.currentTarget) {send fee v a sel o : U256} {M : ByteArray}
    (hM : M.size = 96) (hptr : loadWord (memoryReadBytes M 64 32) 0 32 = 0x60)
    (hc0 : coldIn ss message.currentTarget 0 = false) {cO : Bool}
    (hcO : coldIn ss message.currentTarget (ownerSlotOf st message.currentTarget) = cO)
    (ho : originalAt st message.currentTarget (ownerSlotOf st message.currentTarget) = o)
    (hown : (balOf st message.currentTarget).toNat + fee.toNat < 2 ^ 256) {gas : Nat}
    (hg : 4409 + slotCost cO + Gas.writeCost fork o (balOf st message.currentTarget)
      (add (balOf st message.currentTarget) fee) false ≤ gas) :
    Gas.SpecG fork (At CODE message 10298 [0x40, send, fee, v, a, 0x1699, v, a, 0x078a, sel] M gas st ss)
      (Halted false .empty (gas - (4409 + slotCost cO + Gas.writeCost fork o (balOf st message.currentTarget)
          (add (balOf st message.currentTarget) fee) false))
        (readSlot (ownedB st message.currentTarget fee) message.currentTarget 0)
        (feeSubB fork ss st message o fee send a)) := by
  simp only [ownerSlotOf, balOf, ownedB, feeSubB] at hcO ho hown hg ⊢
  step ownerCall (cO := cO) hfork rfl (by simp) hc0 (by rw [coldIn_accessSlot_of_warm hc0]; exact hcO)
    (by gas_ok) hM
  step addBlock (by simp) (by valid_dest) hown (by gas_ok)
  at_pc 10412
  step ownerStore hfork (by rw [storageAt_readSlot, storageAt_readSlot]) (by simp) hstatic
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
  Gas.writeCost fork (originalAt state message.currentTarget (recipientSlot a))
    (balT state message v a) (add (balT state message v a) (sendOf state message v)) false

/-- The memory at 10298: the four lookups of the debit and the credit. -/
abbrev memA (M : ByteArray) (message : Message fork) (a : U256) : ByteArray :=
  mapMem (mapMem (mapMem (mapMem M (callerKey message) 2) (callerKey message) 2) (mkey a) 2)
    (mkey a) 2

/-- From 9883, with a fee above 0, up to the owner's credit at 10298. -/
theorem feeHead (hfork : .berlin ≤ fork)
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
    sendOf] at hg hfee hfv hbal hto
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
  step debitStore hfork (by simp) hstatic hacc3 (coldIn_accessSlot_self _ _ _) (by gas_ok)
    (by simp only [storageAt_readSlot, originalAt_readSlot]; gas_ok) (size_mapMem hM _ _)
  simp only [storageAt_readSlot, originalAt_readSlot]
  step creditCall hfork (by simp) (cT := cT) (by rw [coldIn_storeSub]; exact hcT) (by gas_ok)
    (size_mapMem (size_mapMem hM _ _) _ _)
  step addBlock (by simp) (by valid_dest) hto (by gas_ok)
  at_pc 10221
  step creditStoreFee hfork hfee (by simp) hstatic hacc4 (coldIn_accessSlot_self _ _ _)
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
  Gas.writeCost fork (originalAt state message.currentTarget (ownerSlot (ownerWord state message v a)))
    (balO state message v a) (add (balO state message v a) (feeOf state message v)) false

/-- From 9883, with a fee above 0, the success path of `transfer` up to the STOP at 1931. -/
theorem bodyFee (hfork : .berlin ≤ fork)
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
  have hA := feeHead (sel := sel) hfork hlong hsz hstatic hacc hM hov hfee hfv hbal hto hc3
    hc4 hcS hcT (gas := gas) (by simp only [ownerCost] at hg; omega)
  have hB := ownerPart (message := message) (st := creditedFee state message v a)
    (ss := creditedSubFee fork substate state message v a) (send := sendOf state message v)
    (v := v) (a := a) (sel := sel) (M := memA M message a) hfork hstatic (hasAccount_writeSlot hacc4)
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

end

section

/-!
## transferFrom(address,address,uint256): the blocks of the owner's credit, for a fee above 0

StandardToken's `transferFrom` at 9342 runs `if (fee > 0)`, with the same code as `transfer`'s
(the first part of this file) at other positions and over the deeper stack of `transferFrom`:

- 9274: the write of `balances[_to]`; with a fee above 0, on to 9351.
- 9351: reads `owner` (slot 0, warm) and `balances[owner]`, calls `add(balance, fee)`.
- 9465: reads `owner` again and writes `balances[owner]`.
- 9566: reads `owner` again and logs `Transfer(_from, owner, fee)` (LOG3); memory grows to 128.
- 9700: the main log `Transfer(_from, _to, sendAmount)` over 128 bytes, back to 4247.

The two mapping lookups of `owner` are copies of the lookup tail at 9393 and 9504 (`hashTailF`,
the proof of `hashTail` at these two positions).
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

/-- The two copies of the lookup tail in the owner's credit of `transferFrom`. -/
abbrev HASH_PCS_F : List Nat := [9393, 9504]

/-- The tail of a mapping lookup at 9393 and 9504 (as `hashTail`). -/
theorem hashTailF {p : Nat} (hp : p ∈ HASH_PCS_F) {x base : U256}
    {rest : List U256} (hrest : rest.length ≤ 900) {M : ByteArray} (hM : M.size = 96) {gas : Nat}
    (hg : 84 ≤ gas) :
    Gas.HoareG fork (At CODE message p (x :: 0 :: base :: rest) M gas state substate)
      (At CODE message (p + 58) (mapSlot ((bitwiseAnd ADDR_MASK (bitwiseAnd ADDR_MASK x))) base :: rest) (mapMem M ((bitwiseAnd ADDR_MASK (bitwiseAnd ADDR_MASK x))) base)
        (gas - 84) state substate) := by
  have hs1 : (memoryWrite M 0 (wordBytes ((bitwiseAnd ADDR_MASK (bitwiseAnd ADDR_MASK x))))).size = 96 := by
    rw [size_memoryWrite] <;> simp [hM, size_wordBytes]
  have hext1 : extendMemory M.size [((0 : U256), (32 : U256))] = ⟨0, 0⟩ := by rw [hM]; decide
  have hext2 : extendMemory (memoryWrite M 0 (wordBytes ((bitwiseAnd ADDR_MASK (bitwiseAnd ADDR_MASK x))))).size
      [((0x20 : U256), (32 : U256))] = ⟨0, 0⟩ := by rw [hs1]; decide
  have hext3 : extendMemory (mapMem M ((bitwiseAnd ADDR_MASK (bitwiseAnd ADDR_MASK x))) base).size [((0 : U256), (0x40 : U256))] =
      ⟨0, 0⟩ := by rw [size_mapMem hM]; decide
  have hk : keccak256Cost (0x40 : U256) = 42 := by decide
  have hread : memoryReadBytes (mapMem M ((bitwiseAnd ADDR_MASK (bitwiseAnd ADDR_MASK x))) base) 0 64 =
      wordBytes ((bitwiseAnd ADDR_MASK (bitwiseAnd ADDR_MASK x))) ++ wordBytes base := by
    have h := memoryReadBytes_memoryWrite_memoryWrite (memory := M) (a := wordBytes ((bitwiseAnd ADDR_MASK (bitwiseAnd ADDR_MASK x))))
      (b := wordBytes base) (s := 0) (by simp [hM, size_wordBytes])
    simpa [size_wordBytes, mapMem] using h
  simp only [HASH_PCS_F, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl
  all_goals
    step pushR 20 ADDR_MASK
    step binR 0x16 (instruction_of_stackOnlyStep rfl)
    step pushR 20 ADDR_MASK
    step binR 0x16 (instruction_of_stackOnlyStep rfl)
    step dupR 1
    step Gas.mstoreG (by code_fact) (by code_fact) (by rw [hext1]; gas_ok)
    step Gas.reshapeG (m' := memoryWrite M 0 (wordBytes ((bitwiseAnd ADDR_MASK (bitwiseAnd ADDR_MASK x))))) rfl
      (by rw [hext1, memoryExtend_zero]; rfl) (by rw [hext1] <;> gas_ok)
    step pushR 1 (0x20 : U256)
    step binR 0x01 instruction_add
    step swapR 0
    norm
    step dupR 1
    step Gas.reshapeG (s' := (0x20 : U256) :: base :: 0x20 :: rest) rfl rfl rfl
    step Gas.mstoreG (by code_fact) (by code_fact) (by rw [hext2]; gas_ok)
    step Gas.reshapeG (m' := mapMem M ((bitwiseAnd ADDR_MASK (bitwiseAnd ADDR_MASK x))) base) rfl (by rw [hext2, memoryExtend_zero]; rfl)
      (by rw [hext2] <;> gas_ok)
    step pushR 1 (0x20 : U256)
    step binR 0x01 instruction_add
    step pushR 1 (0 : U256)
    step Gas.reshapeG (s' := (0 : U256) :: 0x40 :: rest) rfl rfl rfl
    step Gas.keccak256G (by code_fact) (by code_fact) (by rw [hk, hext3]; gas_ok)
    exact restate (by decide)
      (by rw [hext3, memoryExtend_zero, show (0 : U256).toNat = 0 from rfl,
        show (0x40 : U256).toNat = 64 from rfl, hread]; rfl)
      (by rw [hext3, memoryExtend_zero]) (by rw [hext3, hk] <;> gas_ok) rfl rfl

/-- At 9274, the code writes the new balance of `_to`; with a fee above 0 it goes on to the
owner's credit at 9351. -/
theorem creditStoreFeeF (hfork : .berlin ≤ fork)
    {nt send fee A v t f : U256} (hfee : fee ≠ 0) {rest : List U256} (hrest : rest.length ≤ 8)
    (hstatic : message.isStatic = false) (hacc : hasAccount state message.currentTarget)
    {cT : Bool} (hcT : coldIn substate message.currentTarget (recipientSlot t) = cT) {gas : Nat}
    (hstip : 2401 ≤ gas)
    (hg : 127 + Gas.writeCost fork (originalAt state message.currentTarget (recipientSlot t))
      (storageAt state message.currentTarget (recipientSlot t)) nt cT ≤ gas)
    {M : ByteArray} (hM : M.size = 96) :
    Gas.HoareG fork (At CODE message 9274 (nt :: 0x60 :: send :: fee :: A :: v :: t :: f :: rest) M
        gas state substate)
      (At CODE message 9351 (0x60 :: send :: fee :: A :: v :: t :: f :: rest)
        (mapMem M (mkey t) 2)
        (gas - (127 + Gas.writeCost fork (originalAt state message.currentTarget (recipientSlot t))
          (storageAt state message.currentTarget (recipientSlot t)) nt cT))
        (writeSlot state message.currentTarget (recipientSlot t) nt)
        (storeSub fork substate message.currentTarget (recipientSlot t)
          (originalAt state message.currentTarget (recipientSlot t))
          (storageAt state message.currentTarget (recipientSlot t)) nt)) := by
  have hpos : 0 < fee.toNat := by
    rcases Nat.eq_zero_or_pos fee.toNat with h | h
    · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h)) hfee
    · exact h
  simp only [recipientSlot, mkey] at hcT hg ⊢
  step jumpdestR
  step pushR 1 (0x02 : U256)
  step pushR 1 (0 : U256)
  step dupR 8
  at_pc 9280
  step hashTail (by decide) (by simp; omega) hM (by gas_ok)
  at_pc 9338
  step dupR 1
  step swapR 0
  norm
  step Gas.sstoreWG hfork (by code_fact) (by code_fact) hstatic hacc hcT (by gas_ok) (by gas_ok)
  step popR
  step pushR 1 (0 : U256)
  step dupR 3
  step binR 0x11 (instruction_of_stackOnlyStep rfl)
  step unR 0x15 instruction_iszero
  step pushR 2 (0x25e4 : U256)
  step jumpi0R (by simp [greaterThan, isZero, hpos])
  exact restate (by decide) rfl rfl (by gas_ok) rfl rfl

/-- At 9351, the code reads `owner` (slot 0, warm) and `balances[owner]`, and calls
`add(balance, fee)`. -/
theorem ownerCallF (hfork : .berlin ≤ fork) {w0 : U256}
    (hw0 : storageAt state message.currentTarget 0 = w0) {send fee A v t f : U256}
    {rest : List U256} (hrest : rest.length ≤ 800)
    (hc0 : coldIn substate message.currentTarget 0 = false) {cO : Bool}
    (hcO : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget
      (ownerSlot w0) = cO) {gas : Nat}
    (hg : 261 + slotCost cO ≤ gas) {M : ByteArray} (hM : M.size = 96) :
    Gas.HoareG fork (At CODE message 9351 (0x60 :: send :: fee :: A :: v :: t :: f :: rest) M gas state
        substate)
      (At CODE message 11001 (fee :: storageAt state message.currentTarget (ownerSlot w0) ::
        0x24f9 :: 0x60 :: send :: fee :: A :: v :: t :: f :: rest)
        (mapMem M (mkey (ownerKey w0)) 2)
        (gas - (261 + slotCost cO))
        (readSlot (readSlot state message.currentTarget 0) message.currentTarget (ownerSlot w0))
        (accessSlot (accessSlot substate message.currentTarget 0) message.currentTarget
          (ownerSlot w0))) := by
  have hexp : exponentBytes (0 : U256) = 0 := by decide
  simp only [ownerSlot, ownerKey, mkey] at hcO ⊢
  step pushR 2 (0x24f9 : U256)
  step dupR 3
  step pushR 1 (0x02 : U256)
  step pushR 1 (0 : U256)
  step dupR 0
  step pushR 1 (0 : U256)
  step swapR 0
  norm
  step Gas.sloadG hfork (cold := false) (by code_fact) (by code_fact) hc0 (by gas_ok)
  rw [show state.getStorage message.currentTarget (U256.toBeBytes 0) = w0 from hw0]
  step swapR 0
  norm
  step pushR 2 (0x0100 : U256)
  step Gas.expLG (Nat.le_trans (by decide) hfork) (by code_fact) (by code_fact) (by gas_ok)
  step swapR 0
  norm
  step binR 0x04 (instruction_of_stackOnlyStep rfl)
  step pushR 20 ADDR_MASK
  step binR 0x16 (instruction_of_stackOnlyStep rfl)
  at_pc 9393
  step hashTailF (by decide) (by simp; omega) hM (by gas_ok)
  at_pc 9451
  step Gas.sloadG hfork (cold := cO) (by code_fact) (by code_fact) hcO (by gas_ok)
  step pushR 2 (0x2af9 : U256)
  step swapR 0
  norm
  step swapR 1
  norm
  step swapR 0
  norm
  step pushR 4 (0xffffffff : U256)
  step binR 0x16 (instruction_of_stackOnlyStep rfl)
  step jumpR
  exact restate (by decide) (by eqs) rfl (by gas_ok) (by eqs) (by eqs)

/-- At 9465, the code reads `owner` again (warm) and writes the new balance of the owner. -/
theorem ownerStoreF (hfork : .berlin ≤ fork) {w0 : U256}
    (hw0 : storageAt state message.currentTarget 0 = w0)
    {no send fee A v t f : U256} {rest : List U256} (hrest : rest.length ≤ 800)
    (hstatic : message.isStatic = false) (hacc : hasAccount state message.currentTarget)
    (hc0 : coldIn substate message.currentTarget 0 = false) {cO : Bool}
    (hcO : coldIn substate message.currentTarget (ownerSlot w0) = cO) {gas : Nat}
    (hg : 238 + Gas.writeCost fork (originalAt state message.currentTarget (ownerSlot w0))
      (storageAt state message.currentTarget (ownerSlot w0)) no cO + 2300 ≤ gas)
    {M : ByteArray} (hM : M.size = 96) :
    Gas.HoareG fork (At CODE message 9465 (no :: 0x60 :: send :: fee :: A :: v :: t :: f :: rest) M gas
        state substate)
      (At CODE message 9566 (0x60 :: send :: fee :: A :: v :: t :: f :: rest)
        (mapMem M (mkey (ownerKey w0)) 2)
        (gas - (238 + Gas.writeCost fork (originalAt state message.currentTarget (ownerSlot w0))
          (storageAt state message.currentTarget (ownerSlot w0)) no cO))
        (writeSlot (readSlot state message.currentTarget 0) message.currentTarget
          (ownerSlot w0) no)
        (storeSub fork (accessSlot substate message.currentTarget 0) message.currentTarget
          (ownerSlot w0) (originalAt state message.currentTarget (ownerSlot w0))
          (storageAt state message.currentTarget (ownerSlot w0)) no)) := by
  have hexp : exponentBytes (0 : U256) = 0 := by decide
  have hcO' : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget
      (ownerSlot w0) = cO := by
    rw [coldIn_accessSlot_of_warm hc0, hcO]
  simp only [ownerSlot, ownerKey, mkey] at hcO' hg ⊢
  step jumpdestR
  step pushR 1 (0x02 : U256)
  step pushR 1 (0 : U256)
  step dupR 0
  step pushR 1 (0 : U256)
  step swapR 0
  norm
  step Gas.sloadG hfork (cold := false) (by code_fact) (by code_fact) hc0 (by gas_ok)
  rw [show state.getStorage message.currentTarget (U256.toBeBytes 0) = w0 from hw0]
  step swapR 0
  norm
  step pushR 2 (0x0100 : U256)
  step Gas.expLG (Nat.le_trans (by decide) hfork) (by code_fact) (by code_fact) (by gas_ok)
  step swapR 0
  norm
  step binR 0x04 (instruction_of_stackOnlyStep rfl)
  step pushR 20 ADDR_MASK
  step binR 0x16 (instruction_of_stackOnlyStep rfl)
  at_pc 9504
  step hashTailF (by decide) (by simp; omega) hM (by gas_ok)
  at_pc 9562
  step dupR 1
  step swapR 0
  norm
  step Gas.sstoreWG hfork (by code_fact) (by code_fact) hstatic (hasAccount_readSlot hacc) hcO'
    (by gas_ok) (by rw [originalAt_readSlot, storageAt_readSlot]; gas_ok)
  rw [originalAt_readSlot, storageAt_readSlot]
  step popR
  exact restate (by decide) rfl rfl (by gas_ok) rfl rfl

/-- At 9566, the code reads `owner` again (warm) and logs `Transfer(_from, owner, fee)`; the fee
word goes to memory at 0x60, which grows to 128 bytes. -/
theorem ownerLogF (hfork : .berlin ≤ fork) {w0 : U256}
    (hw0 : storageAt state message.currentTarget 0 = w0) {send fee A v t f : U256}
    {rest : List U256} (hrest : rest.length ≤ 800) (hstatic : message.isStatic = false)
    (hc0 : coldIn substate message.currentTarget 0 = false) {gas : Nat} (hg : 1968 ≤ gas)
    {M : ByteArray} (hM : M.size = 96) (hptr : loadWord (memoryReadBytes M 64 32) 0 32 = 0x60) :
    Gas.HoareG fork (At CODE message 9566 (0x60 :: send :: fee :: A :: v :: t :: f :: rest) M gas state
        substate)
      (At CODE message 9700 (0x60 :: send :: fee :: A :: v :: t :: f :: rest) (M ++ wordBytes fee)
        (gas - 1968) (readSlot state message.currentTarget 0)
        { accessSlot substate message.currentTarget 0 with
          logs := substate.logs.push (transferLog message.currentTarget
            (bitwiseAnd ADDR_MASK f) (bitwiseAnd ADDR_MASK (ownerKey w0)) fee) }) := by
  have hexp : exponentBytes (0 : U256) = 0 := by decide
  have hext0 : extendMemory M.size [((0x40 : U256), (32 : U256))] = ⟨0, 0⟩ := by
    rw [hM]; decide
  have hext1 : extendMemory M.size [((0x60 : U256), (32 : U256))] = ⟨3, 32⟩ := by
    rw [hM]; decide
  have hsz : (M ++ wordBytes fee).size = 128 := by
    rw [ByteArray.size_append, hM, size_wordBytes]
  have hext2 : extendMemory (M ++ wordBytes fee).size [((0x40 : U256), (32 : U256))] =
      ⟨0, 0⟩ := by rw [hsz]; decide
  have hext3 : extendMemory (M ++ wordBytes fee).size [((0x60 : U256), (0x20 : U256))] =
      ⟨0, 0⟩ := by rw [hsz]; decide
  have hmem1 : memoryWrite (memoryExtend M 32) (0x60 : U256).toNat (wordBytes fee) =
      M ++ wordBytes fee := by
    have h := memoryWrite_extend_end (memory := M) (value := wordBytes fee)
    rwa [size_wordBytes, hM] at h
  have hread2 : memoryReadBytes (M ++ wordBytes fee) 64 32 = memoryReadBytes M 64 32 := by
    simp only [memoryReadBytes, ByteArray.extract_append, hM]
    simp
  have hlog : logCost (3 : Fin 5).val (0x20 : U256) = 1756 := by decide
  simp only [ownerKey]
  step pushR 1 (0 : U256)
  step dupR 0
  step swapR 0
  norm
  step Gas.sloadG hfork (cold := false) (by code_fact) (by code_fact) hc0 (by gas_ok)
  rw [show state.getStorage message.currentTarget (U256.toBeBytes 0) = w0 from hw0]
  step swapR 0
  norm
  step pushR 2 (0x0100 : U256)
  step Gas.expLG (Nat.le_trans (by decide) hfork) (by code_fact) (by code_fact) (by gas_ok)
  step swapR 0
  norm
  step binR 0x04 (instruction_of_stackOnlyStep rfl)
  step pushR 20 ADDR_MASK
  step binR 0x16 (instruction_of_stackOnlyStep rfl)
  step pushR 20 ADDR_MASK
  step binR 0x16 (instruction_of_stackOnlyStep rfl)
  step dupR 7
  step pushR 20 ADDR_MASK
  step binR 0x16 (instruction_of_stackOnlyStep rfl)
  step pushR 32 TransferOk.TRANSFER_TOPIC
  step dupR 5
  step pushR 1 (0x40 : U256)
  step Gas.mloadG (by code_fact) (by code_fact) (by rw [hext0]; gas_ok)
  step Gas.reshapeG (s' := 0x60 :: fee :: TransferOk.TRANSFER_TOPIC :: bitwiseAnd ADDR_MASK f ::
      bitwiseAnd ADDR_MASK (bitwiseAnd ADDR_MASK (div (w0)
        (exp (0x0100 : U256) (0 : U256)))) :: 0x60 :: send :: fee :: A :: v :: t :: f :: rest)
    (m' := M)
    (by rw [hext0, memoryExtend_zero]; exact congrArg (· :: _) hptr)
    (by rw [hext0, memoryExtend_zero]) (by rw [hext0])
  step dupR 0
  step dupR 2
  step dupR 1
  step Gas.mstoreG (by code_fact) (by code_fact) (by rw [hext1]; gas_ok)
  step Gas.reshapeG (m' := M ++ wordBytes fee) rfl (by rw [hext1]; exact hmem1) (by rw [hext1])
  step pushR 1 (0x20 : U256)
  step binR 0x01 instruction_add
  step swapR 1
  norm
  step popR
  step popR
  step pushR 1 (0x40 : U256)
  step Gas.mloadG (by code_fact) (by code_fact) (by rw [hext2]; gas_ok)
  step Gas.reshapeG (s' := 0x60 :: 0x80 :: TransferOk.TRANSFER_TOPIC :: bitwiseAnd ADDR_MASK f ::
      bitwiseAnd ADDR_MASK (bitwiseAnd ADDR_MASK (div (w0)
        (exp (0x0100 : U256) (0 : U256)))) :: 0x60 :: send :: fee :: A :: v :: t :: f :: rest)
    (m' := M ++ wordBytes fee)
    (by rw [hext2, memoryExtend_zero, show (0x40 : U256).toNat = 64 from rfl, hread2, hptr]; rfl)
    (by rw [hext2, memoryExtend_zero]) (by rw [hext2])
  step dupR 0
  step swapR 1
  norm
  step binR 0x03 instruction_sub
  step swapR 0
  norm
  step Gas.reshapeG (s' := 0x60 :: 0x20 :: ([TransferOk.TRANSFER_TOPIC, bitwiseAnd ADDR_MASK f,
      bitwiseAnd ADDR_MASK (bitwiseAnd ADDR_MASK (div (w0)
        (exp (0x0100 : U256) (0 : U256))))] ++
      (0x60 :: send :: fee :: A :: v :: t :: f :: rest))) rfl rfl rfl
  step Gas.logG (n := 3) (byte := 0xa3) rfl (by code_fact) (by code_fact) rfl hstatic
    (by rw [hlog, hext3]; gas_ok)
  step Gas.reshapeG rfl (by rw [hext3, memoryExtend_zero]) (by rw [hlog, hext3])
  refine restate (by decide) rfl rfl (by gas_ok) (by eqs) ?_
  rw [hext3, memoryExtend_zero, show (0x60 : U256).toNat = 96 from rfl,
    show (0x20 : U256).toNat = 32 from rfl, read_after hM _ (size_wordBytes fee)]

/-- At 9700, over 128 bytes of memory with the pointer 0x60 at 0x40, the code logs
`Transfer(_from, _to, sendAmount)` and returns to 4247. -/
theorem logBlock128F {send fee A v t f : U256} {rest : List U256} (hrest : rest.length ≤ 900)
    (hstatic : message.isStatic = false) {gas : Nat} (hg : 1852 ≤ gas) {M : ByteArray}
    (hM : M.size = 128) (hptr : loadWord (memoryReadBytes M 64 32) 0 32 = 0x60) :
    Gas.HoareG fork (At CODE message 9700 (0x60 :: send :: fee :: A :: v :: t :: f :: 0x1097 :: rest)
        M gas state substate)
      (At CODE message 4247 rest (memoryWrite M 96 (wordBytes send)) (gas - 1852) state
        { substate with logs := substate.logs.push (transferLog message.currentTarget
          (bitwiseAnd ADDR_MASK f) (bitwiseAnd ADDR_MASK t) send) }) := by
  have hsz : (memoryWrite M 96 (wordBytes send)).size = 128 := by
    rw [size_memoryWrite (by simp [hM, size_wordBytes]), hM]
  have hext0 : extendMemory M.size [((0x40 : U256), (32 : U256))] = ⟨0, 0⟩ := by
    rw [hM]; decide
  have hext1 : extendMemory M.size [((0x60 : U256), (32 : U256))] = ⟨0, 0⟩ := by
    rw [hM]; decide
  have hext2 : extendMemory (memoryWrite M 96 (wordBytes send)).size
      [((0x40 : U256), (32 : U256))] = ⟨0, 0⟩ := by rw [hsz]; decide
  have hext3 : extendMemory (memoryWrite M 96 (wordBytes send)).size
      [((0x60 : U256), (0x20 : U256))] = ⟨0, 0⟩ := by rw [hsz]; decide
  have hread2 : memoryReadBytes (memoryWrite M 96 (wordBytes send)) 64 32 =
      memoryReadBytes M 64 32 :=
    memoryReadBytes_memoryWrite_of_disjoint (by simp [hM, size_wordBytes])
      (by simp [size_wordBytes])
  have hread3 : memoryReadBytes (memoryWrite M 96 (wordBytes send)) 96 32 = wordBytes send := by
    have h := memoryReadBytes_memoryWrite (memory := M) (value := wordBytes send)
      (start := 96) (by simp [hM, size_wordBytes])
    rwa [size_wordBytes] at h
  have hlog : logCost (3 : Fin 5).val (0x20 : U256) = 1756 := by decide
  step jumpdestR
  step dupR 5
  step pushR 20 ADDR_MASK
  step binR 0x16 (instruction_of_stackOnlyStep rfl)
  step dupR 7
  step pushR 20 ADDR_MASK
  step binR 0x16 (instruction_of_stackOnlyStep rfl)
  step pushR 32 TransferOk.TRANSFER_TOPIC
  step dupR 4
  step pushR 1 (0x40 : U256)
  step Gas.mloadG (by code_fact) (by code_fact) (by rw [hext0]; gas_ok)
  step Gas.reshapeG (s' := 0x60 :: send :: TransferOk.TRANSFER_TOPIC :: bitwiseAnd ADDR_MASK f ::
      bitwiseAnd ADDR_MASK t :: 0x60 :: send :: fee :: A :: v :: t :: f :: 0x1097 :: rest) (m' := M)
    (by rw [hext0, memoryExtend_zero]; exact congrArg (· :: _) hptr)
    (by rw [hext0, memoryExtend_zero]) (by rw [hext0])
  step dupR 0
  step dupR 2
  step dupR 1
  step Gas.mstoreG (by code_fact) (by code_fact) (by rw [hext1]; gas_ok)
  step Gas.reshapeG (m' := memoryWrite M 96 (wordBytes send)) rfl
    (by rw [hext1, memoryExtend_zero]; rfl) (by rw [hext1])
  step pushR 1 (0x20 : U256)
  step binR 0x01 instruction_add
  step swapR 1
  norm
  step popR
  step popR
  step pushR 1 (0x40 : U256)
  step Gas.mloadG (by code_fact) (by code_fact) (by rw [hext2]; gas_ok)
  step Gas.reshapeG (s' := 0x60 :: 0x80 :: TransferOk.TRANSFER_TOPIC :: bitwiseAnd ADDR_MASK f ::
      bitwiseAnd ADDR_MASK t :: 0x60 :: send :: fee :: A :: v :: t :: f :: 0x1097 :: rest)
    (m' := memoryWrite M 96 (wordBytes send))
    (by rw [hext2, memoryExtend_zero, show (0x40 : U256).toNat = 64 from rfl, hread2, hptr]; rfl)
    (by rw [hext2, memoryExtend_zero]) (by rw [hext2])
  step dupR 0
  step swapR 1
  norm
  step binR 0x03 instruction_sub
  step swapR 0
  norm
  step Gas.reshapeG (s' := 0x60 :: 0x20 :: ([TransferOk.TRANSFER_TOPIC, bitwiseAnd ADDR_MASK f,
      bitwiseAnd ADDR_MASK t] ++ (0x60 :: send :: fee :: A :: v :: t :: f :: 0x1097 :: rest)))
    rfl rfl rfl
  step Gas.logG (n := 3) (byte := 0xa3) rfl (by code_fact) (by code_fact) rfl hstatic
    (by rw [hlog, hext3]; gas_ok)
  step Gas.reshapeG rfl (by rw [hext3, memoryExtend_zero]) (by rw [hlog, hext3])
  step popR
  step popR
  step popR
  step popR
  step popR
  step popR
  step popR
  step jumpR
  refine restate (by decide) rfl rfl (by gas_ok) rfl ?_
  rw [hext3, memoryExtend_zero, show (0x60 : U256).toNat = 96 from rfl,
    show (0x20 : U256).toNat = 32 from rfl, hread3]

end UsdtVerify.TransferFrom

end
