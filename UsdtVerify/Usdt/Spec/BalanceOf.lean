import UsdtVerify.Usdt.Proofs.Common

/-!
# balanceOf(address)

The path of a call with selector 0x70a08231, no value, and the contract not deprecated.

- At 1456, the entry checks that the call has no value, masks argument word 0 to 160 bits, and
  calls the getter at 4665 with return address 1511.
- At 4665, the deprecation check reads slot 10 and, when byte 20 is 0, goes to 4919.
- At 4919, the code calls the lookup at 9810 with return address 4928.
- At 9810, the lookup writes the key word at 0 and the word 2 at 32, hashes those 64 bytes, and
  reads the slot at that hash.
- At 4928, the code returns to 1511, which returns the word.

`toLookup`, `lookup` and `back` hold for any words below the getter's own and (for `lookup`) any
memory of 96 bytes: destroyBlackFunds calls the same getter from 7999 (return address 8008).
-/

namespace UsdtVerify.BalanceOf

open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate}

/-- From 1456, a call with no value goes to the check at 4665 with the masked argument. -/
theorem entry (hv : message.value = 0) {x : U256} {gas : Nat} (hg : 74 ≤ gas) :
    Gas.HoareG fork (At CODE message 1456 [x] MEM0 gas state substate)
      (At CODE message 4665 [addrArg message.data 0, 0x05e7, x] MEM0 (gas - 74) state
        substate) := by
  step jumpdestR
  step Gas.callvalueG (by code_fact) (by code_fact) (by gas_ok) (by stk_ok)
  step unR 0x15 instruction_iszero
  step pushR 2 (0x05bb : U256)
  step jumpiR (by simp [hv, isZero])
  step jumpdestR
  step pushR 2 (0x05e7 : U256)
  step pushR 1 (0x04 : U256)
  step dupR 0
  step dupR 0
  step Gas.calldataloadG (by code_fact) (by code_fact) (by gas_ok)
  step pushR 20 ADDR_MASK
  step binR 0x16 Local.instruction_and
  step swapR 0
  norm
  step pushR 1 (0x20 : U256)
  step binR 0x01 instruction_add
  step swapR 0
  norm
  step swapR 1
  norm
  step swapR 0
  norm
  step popR
  step popR
  step pushR 2 (0x1239 : U256)
  step jumpR
  exact (repc (by decide)).seq (Gas.reshapeG rfl rfl (by gas_ok))

/-- From 4919, the code calls the lookup at 9810 with return address 4928. The words below the
getter's own (`a` and its return address `r1`) are any `rest`. -/
theorem toLookup {a r1 : U256} {rest : List U256} (hrest : rest.length ≤ 900) {M : ByteArray}
    {gas : Nat} (hg : 18 ≤ gas) :
    Gas.HoareG fork (At CODE message 4919 (0 :: a :: r1 :: rest) M gas state substate)
      (At CODE message 9810 (a :: 0x1340 :: 0 :: a :: r1 :: rest) M (gas - 18) state substate) := by
  step jumpdestR
  step pushR 2 (0x1340 : U256)
  step dupR 2
  step pushR 2 (0x2652 : U256)
  step jumpR
  exact (repc (by decide)).seq (Gas.reshapeG rfl rfl (by gas_ok))

/-- The key word that the lookup writes for `a`: `a` masked twice to 160 bits. -/
abbrev key (a : U256) : U256 := bitwiseAnd ADDR_MASK (bitwiseAnd ADDR_MASK a)

/-- The memory after the lookup: the key word at 0 and the word 2 at 32. -/
abbrev MEM1 (a : U256) : ByteArray := memoryWrite (memoryWrite MEM0 0 (wordBytes (key a))) 32 (wordBytes 2)

theorem size_MEM1 (a : U256) : (MEM1 a).size = 96 := by
  rw [MEM1, size_memoryWrite, size_memoryWrite] <;>
    simp [size_memoryWrite, size_MEM0, size_wordBytes]

theorem mload_MEM1 (a : U256) : loadWord (memoryReadBytes (MEM1 a) 64 32) 0 32 = 0x60 := by
  rw [MEM1, memoryReadBytes_memoryWrite_of_disjoint, 
    memoryReadBytes_memoryWrite_of_disjoint, mload_MEM0] <;>
    simp [size_memoryWrite, size_MEM0, size_wordBytes]

/-- The memory after the lookup from a memory `M`: the key word at 0 and the word 2 at 32. -/
abbrev lookMem (M : ByteArray) (a : U256) : ByteArray :=
  memoryWrite (memoryWrite M 0 (wordBytes (key a))) 32 (wordBytes 2)

theorem MEM1_eq (a : U256) : MEM1 a = lookMem MEM0 a := rfl

theorem size_lookMem {M : ByteArray} (hM : M.size = 96) (a : U256) : (lookMem M a).size = 96 := by
  rw [lookMem, size_memoryWrite, size_memoryWrite] <;>
    simp [size_memoryWrite, hM, size_wordBytes]

/-- The lookup at 9810: it reads the slot at the hash of the key word and the word 2. The memory
`M` is any memory of 96 bytes and the words below the getter's own are any `rest`. -/
theorem lookup (hfork : .berlin ≤ fork) {a r1 : U256} {rest : List U256}
    (hrest : rest.length ≤ 900) {M : ByteArray} (hM : M.size = 96) {cB : Bool}
    (hcB : coldIn substate message.currentTarget (mapSlot (key a) 2) = cB) {gas : Nat}
    (hg : 118 + slotCost cB ≤ gas) :
    Gas.HoareG fork (At CODE message 9810 (a :: 0x1340 :: 0 :: a :: r1 :: rest) M gas state substate)
      (At CODE message 4928 (storageAt state message.currentTarget (mapSlot (key a) 2) :: 0 :: a ::
          r1 :: rest)
        (lookMem M a) (gas - (118 + slotCost cB))
        (readSlot state message.currentTarget (mapSlot (key a) 2))
        (accessSlot substate message.currentTarget (mapSlot (key a) 2))) := by
  have hs1 : (memoryWrite M 0 (wordBytes (key a))).size = 96 := by
    rw [size_memoryWrite] <;> simp [hM, size_wordBytes]
  have hext1 : extendMemory M.size [((0 : U256), (32 : U256))] = ⟨0, 0⟩ := by
    rw [hM]; decide
  have hext2 : extendMemory (memoryWrite M 0 (wordBytes (key a))).size
      [((0x20 : U256), (32 : U256))] = ⟨0, 0⟩ := by
    rw [hs1]; decide
  have hext3 : extendMemory (lookMem M a).size [((0 : U256), (0x40 : U256))] = ⟨0, 0⟩ := by
    rw [size_lookMem hM]; decide
  have hk : keccak256Cost (0x40 : U256) = 42 := by decide
  have hread : memoryReadBytes (lookMem M a) 0 64 = wordBytes (key a) ++ wordBytes 2 := by
    have h := memoryReadBytes_memoryWrite_memoryWrite (memory := M) (a := wordBytes (key a))
      (b := wordBytes 2) (s := 0) (by simp [hM, size_wordBytes])
    simpa [size_wordBytes, lookMem] using h
  step jumpdestR
  step pushR 1 (0 : U256)
  step pushR 1 (0x02 : U256)
  step pushR 1 (0 : U256)
  step dupR 3
  step pushR 20 ADDR_MASK
  step binR 0x16 Local.instruction_and
  step pushR 20 ADDR_MASK
  step binR 0x16 Local.instruction_and
  step dupR 1
  step Gas.mstoreG (by code_fact) (by code_fact) (by rw [hext1]; gas_ok)
  step Gas.reshapeG (m' := memoryWrite M 0 (wordBytes (key a))) rfl
    (by rw [hext1, memoryExtend_zero]; rfl) (by rw [hext1] <;> gas_ok)
  step pushR 1 (0x20 : U256)
  step binR 0x01 instruction_add
  step swapR 0
  norm
  step dupR 1
  step Gas.reshapeG (s' := (0x20 : U256) :: 2 :: 0x20 :: 0 :: a :: 0x1340 :: 0 :: a :: r1 :: rest) rfl rfl rfl
  step Gas.mstoreG (by code_fact) (by code_fact) (by rw [hext2]; gas_ok)
  step Gas.reshapeG (m' := lookMem M a) rfl (by rw [hext2, memoryExtend_zero]; rfl) (by rw [hext2] <;> gas_ok)
  step pushR 1 (0x20 : U256)
  step binR 0x01 instruction_add
  step pushR 1 (0 : U256)
  step Gas.reshapeG (s' := (0 : U256) :: 0x40 :: 0 :: a :: 0x1340 :: 0 :: a :: r1 :: rest) rfl rfl rfl
  step Gas.keccak256G (by code_fact) (by code_fact) (by rw [hk, hext3]; gas_ok)
  step Gas.reshapeG (s' := mapSlot (key a) 2 :: 0 :: a :: 0x1340 :: 0 :: a :: r1 :: rest) (m' := lookMem M a)
    (by rw [hext3, memoryExtend_zero, show (0 : U256).toNat = 0 from rfl,
      show (0x40 : U256).toNat = 64 from rfl, hread]; rfl)
    (by rw [hext3, memoryExtend_zero]) (by rw [hext3, hk] <;> gas_ok)
  step Gas.sloadG hfork (cold := cB) (by code_fact) (by code_fact) hcB (by gas_ok)
  step swapR 0
  norm
  step popR
  step swapR 1
  norm
  step swapR 0
  norm
  step popR
  step jumpR
  exact (repc (by decide)).seq (Gas.reshapeG rfl rfl (by gas_ok))

/-- From 4928, the getter returns the word to its return address: 1511 (balanceOf) or 8008
(destroyBlackFunds), with any `rest` below. -/
theorem back {p : Nat} (hp : p = 1511 ∨ p = 8008) {b a : U256} {rest : List U256}
    {gas : Nat} (hg : 23 ≤ gas) {M : ByteArray} :
    Gas.HoareG fork (At CODE message 4928 (b :: 0 :: a :: BitVec.ofNat 256 p :: rest) M gas state substate)
      (At CODE message p (b :: rest) M (gas - 23) state substate) := by
  rcases hp with rfl | rfl
  all_goals
    step jumpdestR
    step swapR 0
    norm
    step popR
    step jumpdestR
    step swapR 1
    norm
    step swapR 0
    norm
    step popR
    step jumpR
    exact (repc (by decide)).seq (Gas.reshapeG rfl rfl (by gas_ok))

/-- The slot of the balance of the address in argument word 0: mapping base slot 2. -/
abbrev balanceSlot (data : ByteArray) : U256 := mapSlot (addrArg data 0) 2

/-- The gas of the whole path, besides the two reads of storage. -/
abbrev COST : Nat := 831

/-- The specification of `balanceOf(address)`, from Berlin, with the one-counter meter.

The call data starts with the selector 0x70a08231 and has at least 4 bytes, and the call has no
value.

Byte 20 of slot 10 of the contract (the `deprecated` flag) is 0.

Then the run returns the 32 bytes of the slot `keccak256(k ++ w2)`, where `k` is argument word 0
masked to its low 160 bits and `w2` is the word 2.

It records slot 10 and that slot as read and accessed.

It pays 831 gas and the price of each read; `cB` is whether the balance slot is cold once slot 10
has been accessed. -/
theorem spec (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x70a08231)
    (hv : message.value = 0) (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    {c10 cB : Bool} (hc10 : coldIn substate message.currentTarget 10 = c10)
    (hcB : coldIn (accessSlot substate message.currentTarget 10) message.currentTarget
      (balanceSlot message.data) = cB)
    {gas : Nat} (hg : COST + slotCost c10 + slotCost cB ≤ gas) :
    Gas.SpecG fork (At CODE message 0 [] .empty gas state substate)
      (Halted false (wordBytes (storageAt state message.currentTarget (balanceSlot message.data)))
        (gas - (COST + slotCost c10 + slotCost cB))
        (readSlot (readSlot state message.currentTarget 10) message.currentTarget
          (balanceSlot message.data))
        (accessSlot (accessSlot substate message.currentTarget 10) message.currentTarget
          (balanceSlot message.data))) := by
  simp only [COST] at hg ⊢
  have hkey : key (addrArg message.data 0) = addrArg message.data 0 := by
    simp only [key, addrArg, mask_mask]
  have ht : tested (BitVec.ofNat 256 (selector message.data)) ENTRIES = 17 := by
    rw [hsel]; decide
  have hb : branch (BitVec.ofNat 256 (selector message.data)) 54 (entrySize 4 2) ENTRIES =
      1456 := by
    rw [hsel]; decide
  have h1 := dispatch (state := state) (substate := substate) hsize hsize' (gas := gas)
    (by rw [ht]; gas_ok)
  rw [ht, hb] at h1
  have h2 := entry (state := state) (substate := substate) hv
    (x := BitVec.ofNat 256 (selector message.data)) (gas := gas - 62 - 22 * 17) (by gas_ok)
  have h3 := depCheck (substate := substate) (M := MEM0) hfork (Or.inr (Or.inl ⟨rfl, rfl⟩))
    (rest := [addrArg message.data 0, 0x05e7, BitVec.ofNat 256 (selector message.data)])
    (by simp) hdep hc10 (gas := gas - 62 - 22 * 17 - 74) (by gas_ok)
  have h4 := toLookup (message := message) (state := readSlot state message.currentTarget 10)
    (substate := accessSlot substate message.currentTarget 10)
    (a := addrArg message.data 0) (r1 := 0x05e7) (rest := [BitVec.ofNat 256 (selector message.data)])
    (by simp) (M := MEM0) (gas := gas - 62 - 22 * 17 - 74 - (109 + slotCost c10)) (by gas_ok)
  have h5 := lookup (message := message) (state := readSlot state message.currentTarget 10)
    (substate := accessSlot substate message.currentTarget 10) hfork
    (a := addrArg message.data 0) (r1 := 0x05e7) (rest := [BitVec.ofNat 256 (selector message.data)])
    (by simp) size_MEM0 (cB := cB) (by rw [hkey]; exact hcB)
    (gas := gas - 62 - 22 * 17 - 74 - (109 + slotCost c10) - 18) (by gas_ok)
  rw [hkey, storageAt_readSlot, ← MEM1_eq] at h5
  have h6 := back (message := message) (p := 1511) (Or.inl rfl)
    (state := readSlot (readSlot state message.currentTarget 10) message.currentTarget
      (balanceSlot message.data))
    (substate := accessSlot (accessSlot substate message.currentTarget 10) message.currentTarget
      (balanceSlot message.data))
    (b := storageAt state message.currentTarget (balanceSlot message.data))
    (a := addrArg message.data 0) (rest := [BitVec.ofNat 256 (selector message.data)])
    (M := MEM1 (addrArg message.data 0))
    (gas := gas - 62 - 22 * 17 - 74 - (109 + slotCost c10) - 18 - (118 + slotCost cB))
    (by gas_ok)
  have h7 := ret (message := message) (p := 1511) (by decide)
    (state := readSlot (readSlot state message.currentTarget 10) message.currentTarget
      (balanceSlot message.data))
    (substate := accessSlot (accessSlot substate message.currentTarget 10) message.currentTarget
      (balanceSlot message.data))
    (size_MEM1 (addrArg message.data 0)) (mload_MEM1 (addrArg message.data 0))
    (v := storageAt state message.currentTarget (balanceSlot message.data))
    (rest := [BitVec.ofNat 256 (selector message.data)]) (by simp)
    (gas := gas - 62 - 22 * 17 - 74 - (109 + slotCost c10) - 18 - (118 + slotCost cB) - 23)
    (by gas_ok)
  refine Gas.SpecG.seq (h1.seq (h2.seq (h3.seq (h4.seq (h5.seq h6))))) (h7.consequence (fun _ h => h) ?_)
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  exact ⟨hr, he, ho, by rw [hgas]; gas_ok, hs, hss⟩

/-- The loop of the interpreter runs a `balanceOf(address)` call to its specification.

It holds for every bound on the gas of messages and every runner of messages. -/
theorem runFrame_spec (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x70a08231)
    (hv : message.value = 0) (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    {c10 cB : Bool} (hc10 : coldIn substate message.currentTarget 10 = c10)
    (hcB : coldIn (accessSlot substate message.currentTarget 10) message.currentTarget
      (balanceSlot message.data) = cB)
    {gas : Nat} (hg : COST + slotCost c10 + slotCost cB ≤ gas) {bound : Nat}
    {runChild : MessageRunner fork Nat bound} {evm : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    ∃ stopped, runFrame (step fork) (step_decreases fork) bound runChild evm within =
      .ok stopped ∧
      Halted false (wordBytes (storageAt state message.currentTarget (balanceSlot message.data)))
        (gas - (COST + slotCost c10 + slotCost cB))
        (readSlot (readSlot state message.currentTarget 10) message.currentTarget
          (balanceSlot message.data))
        (accessSlot (accessSlot substate message.currentTarget 10) message.currentTarget
          (balanceSlot message.data)) stopped :=
  (spec hfork hsize hsize' hsel hv hdep hc10 hcB hg).runFrame start within

end UsdtVerify.BalanceOf
