import UsdtVerify.Functions.TransferFeeBody

/-!
# transferFrom(address,address,uint256): the blocks of the owner's credit, for a fee above 0

StandardToken's `transferFrom` at 9342 runs `if (fee > 0)`, with the same code as `transfer`'s
(TransferFee.lean) at other positions and over the deeper stack of `transferFrom`:

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
    step binR 0x16 Local.instruction_and
    step pushR 20 ADDR_MASK
    step binR 0x16 Local.instruction_and
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
  step binR 0x11 Local.instruction_gt
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
  step binR 0x04 Local.instruction_div
  step pushR 20 ADDR_MASK
  step binR 0x16 Local.instruction_and
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
  step binR 0x16 Local.instruction_and
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
  step binR 0x04 Local.instruction_div
  step pushR 20 ADDR_MASK
  step binR 0x16 Local.instruction_and
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
  step binR 0x04 Local.instruction_div
  step pushR 20 ADDR_MASK
  step binR 0x16 Local.instruction_and
  step pushR 20 ADDR_MASK
  step binR 0x16 Local.instruction_and
  step dupR 7
  step pushR 20 ADDR_MASK
  step binR 0x16 Local.instruction_and
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
  step binR 0x03 Local.instruction_sub
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
  step binR 0x16 Local.instruction_and
  step dupR 7
  step pushR 20 ADDR_MASK
  step binR 0x16 Local.instruction_and
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
  step binR 0x03 Local.instruction_sub
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
