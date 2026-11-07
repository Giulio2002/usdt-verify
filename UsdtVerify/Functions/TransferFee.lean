import UsdtVerify.Functions.TransferOk

/-!
# transfer(address,uint256): the blocks of the owner's credit, for a fee above 0

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
theorem creditStoreFee (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    {nt send fee v a : U256} (hfee : fee ≠ 0)
    {rest : List U256} (hrest : rest.length ≤ 800) (hstatic : message.isStatic = false)
    (hacc : hasAccount state message.currentTarget) {cT : Bool}
    (hcT : coldIn substate message.currentTarget (recipientSlot a) = cT) {gas : Nat}
    (hstip : 2401 ≤ gas)
    (hg : 127 + sstoreCost fork (originalAt state message.currentTarget (recipientSlot a))
      (storageAt state message.currentTarget (recipientSlot a)) nt cT ≤ gas)
    {M : ByteArray} (hM : M.size = 96) :
    Gas.HoareG fork (At CODE message 10221 (nt :: 0x40 :: send :: fee :: v :: a :: rest) M gas state
        substate)
      (At CODE message 10298 (0x40 :: send :: fee :: v :: a :: rest) (mapMem M (mkey a) 2)
        (gas - (127 + sstoreCost fork (originalAt state message.currentTarget (recipientSlot a))
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
  step Gas.sstoreWG hfork hglam (by code_fact) (by code_fact) hstatic hacc hcT (by gas_ok) (by gas_ok)
  step popR
  step pushR 1 (0 : U256)
  step dupR 3
  step binR 0x11 Local.instruction_gt
  step unR 0x15 instruction_iszero
  step pushR 2 (0x2997 : U256)
  step jumpi0R (by simp [greaterThan, isZero, hpos])
  exact restate (by decide) rfl rfl (by gas_ok) rfl rfl

/-- The owner word as the code computes it from slot 0: `w0 / 256^0`, masked to 160 bits. -/
abbrev ownerKey (w0 : U256) : U256 := bitwiseAnd ADDR_MASK (div w0 (exp (0x0100 : U256) (0 : U256)))

/-- The slot of `balances[owner]` for the word `w0` of slot 0. -/
abbrev ownerSlot (w0 : U256) : U256 := mapSlot (mkey (ownerKey w0)) 2

/-- The owner word is the low 160 bits of slot 0. -/
theorem ownerKey_eq (w0 : U256) : ownerKey w0 = bitwiseAnd ADDR_MASK w0 := by
  have he : exp (0x0100 : U256) (0 : U256) = 1 := by decide +kernel
  have hd : div w0 1 = w0 := by
    apply BitVec.eq_of_toNat_eq
    simp [div]
  rw [ownerKey, he, hd]

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
  step binR 0x04 Local.instruction_div
  step pushR 20 ADDR_MASK
  step binR 0x16 Local.instruction_and
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
  step binR 0x16 Local.instruction_and
  step jumpR
  exact restate (by decide) (by eqs) rfl (by gas_ok) (by eqs) (by eqs)

/-- At 10412, the code reads `owner` again (warm) and writes the new balance of the owner. -/
theorem ownerStore (hfork : .berlin ≤ fork) {w0 : U256}
    (hw0 : storageAt state message.currentTarget 0 = w0) (hglam : fork < .glamsterdam)
    {no send fee v a : U256} {rest : List U256} (hrest : rest.length ≤ 800)
    (hstatic : message.isStatic = false) (hacc : hasAccount state message.currentTarget)
    (hc0 : coldIn substate message.currentTarget 0 = false) {cO : Bool}
    (hcO : coldIn substate message.currentTarget
      (ownerSlot (w0)) = cO) {gas : Nat}
    (hg : 238 + sstoreCost fork
      (originalAt state message.currentTarget (ownerSlot (w0)))
      (storageAt state message.currentTarget (ownerSlot (w0)))
      no cO + 2300 ≤ gas)
    {M : ByteArray} (hM : M.size = 96) :
    Gas.HoareG fork (At CODE message 10412 (no :: 0x40 :: send :: fee :: v :: a :: rest) M gas state
        substate)
      (At CODE message 10513 (0x40 :: send :: fee :: v :: a :: rest)
        (mapMem M (mkey (ownerKey (w0))) 2)
        (gas - (238 + sstoreCost fork (originalAt state message.currentTarget
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
  step binR 0x04 Local.instruction_div
  step pushR 20 ADDR_MASK
  step binR 0x16 Local.instruction_and
  at_pc 10451
  step hashTail (by decide) (by simp; omega) hM (by gas_ok)
  at_pc 10509
  step dupR 1
  step swapR 0
  norm
  step Gas.sstoreWG hfork hglam (by code_fact) (by code_fact) hstatic (hasAccount_readSlot hacc) hcO'
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
  step binR 0x04 Local.instruction_div
  step pushR 20 ADDR_MASK
  step binR 0x16 Local.instruction_and
  step pushR 20 ADDR_MASK
  step binR 0x16 Local.instruction_and
  step Gas.callerG (by code_fact) (by code_fact) (by gas_ok) (by stk_ok)
  step pushR 20 ADDR_MASK
  step binR 0x16 Local.instruction_and
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
  step binR 0x03 Local.instruction_sub
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
  step binR 0x16 Local.instruction_and
  step Gas.callerG (by code_fact) (by code_fact) (by gas_ok) (by stk_ok)
  step pushR 20 ADDR_MASK
  step binR 0x16 Local.instruction_and
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
  step binR 0x03 Local.instruction_sub
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
