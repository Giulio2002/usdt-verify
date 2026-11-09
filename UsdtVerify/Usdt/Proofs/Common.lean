import UsdtVerify.Evm.Storage
import UsdtVerify.Usdt.Map
import EthLib.Execution.Proofs.Evm.Machine.Memory

/-!
# Blocks shared by several functions of USDT

Proves the Hoare triples of the code blocks that several functions share: the returns of one
word and the deprecation check, with the memory after the prelude and the tests of a flag byte.

- `size_MEM0`, `mload_MEM0`, `read_after`: facts about `MEM0` (Map.lean), the memory after the
  prelude.
- `ret`, `retB`, `retA`: the blocks that return one word, one boolean, one address (at the pcs
  `RET_PCS`, `BOOL_PCS`, `ADDR_PCS`).
- `flag_eq`, `isZero3_flag`, `isZero3_flag_ne`, `isZero_flag_ne`: the tests of byte 20 of a word.
- `depCheck`: the deprecation check of totalSupply, balanceOf and allowance.
-/

namespace UsdtVerify

open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate}

/-- Normalize the stack after a SWAP and fold the gas. -/
macro "norm" : tactic => `(tactic| simp only [List.set_cons_zero, List.set_cons_succ, Fin.val_zero,
  Fin.isValue, Nat.sub_sub, Nat.reduceAdd])

theorem size_MEM0 : MEM0.size = 96 := by
  unfold MEM0
  rw [size_memoryWrite (by simp [size_memoryExtend, size_wordBytes]), size_memoryExtend]
  rfl

theorem mload_MEM0 : loadWord (memoryReadBytes MEM0 64 32) 0 32 = 0x60 :=
  loadWord_memoryWrite_wordBytes _ (by simp [size_memoryExtend])

/-- The 32 bytes after a memory `M` of 96 bytes in `M ++ w` are `w`. -/
theorem read_after {M : ByteArray} (hM : M.size = 96) (w : ByteArray) (hw : w.size = 32) :
    memoryReadBytes (M ++ w) 96 32 = w := by
  have h := ByteArray.extract_append_size_add' (a := M) (b := w) (i := 0) (j := 32) hM.symm
  simp only [memoryReadBytes, Nat.add_zero, show ¬ (32 = 0) from by decide, ite_false] at h ⊢
  rw [h, ← hw, ByteArray.extract_zero_size]

/-- The copies of the block that returns one word: 797 (totalSupply), 1511 (balanceOf), 1056
(balances), 1097 (decimals), 1138 (maximumFee), 1179 (_totalSupply), 1389 (allowed), 2132
(allowance), 2173 (basisPointsRate), 2352 (MAX_UINT). -/
abbrev RET_PCS : List Nat := [797, 1511, 1056, 1097, 1138, 1179, 1389, 2132, 2173, 2352]

/-- The return block at 797 and its copies (`RET_PCS`): it writes the top word at the free memory
pointer 0x60 and returns those 32 bytes. The words below are any `rest`.

The memory has 96 bytes and holds the pointer 0x60 at 0x40. -/
theorem ret {p : Nat} (hp : p ∈ RET_PCS) {M : ByteArray} (hM : M.size = 96)
    (hptr : loadWord (memoryReadBytes M 64 32) 0 32 = 0x60) {v : U256} {rest : List U256}
    (hrest : rest.length ≤ 900) {gas : Nat} (hg : 53 ≤ gas) :
    Gas.SpecG fork (At CODE message p (v :: rest) M gas state substate)
      (Halted false (wordBytes v) (gas - 53) state substate) := by
  have hext0 : extendMemory M.size [((0x40 : U256), (32 : U256))] = ⟨0, 0⟩ := by
    rw [hM]; decide
  have hext1 : extendMemory M.size [((0x60 : U256), (32 : U256))] = ⟨3, 32⟩ := by
    rw [hM]; decide
  have hext2 : extendMemory (M ++ wordBytes v).size [((0x40 : U256), (32 : U256))] = ⟨0, 0⟩ := by
    rw [ByteArray.size_append, hM, size_wordBytes]; decide
  have hmem1 : memoryWrite (memoryExtend M 32) (0x60 : U256).toNat (wordBytes v) =
      M ++ wordBytes v := by
    have h := memoryWrite_extend_end (memory := M) (value := wordBytes v)
    rwa [size_wordBytes, hM] at h
  have hread2 : memoryReadBytes (M ++ wordBytes v) 64 32 = memoryReadBytes M 64 32 := by
    simp only [memoryReadBytes, ByteArray.extract_append, hM]
    simp
  simp only [RET_PCS, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    step jumpdestR
    step pushR 1 (0x40 : U256)
    step Gas.mloadG (by code_fact) (by code_fact) (by rw [hext0]; gas_ok)
    step Gas.reshapeG (s' := (0x60 : U256) :: v :: rest) (m' := M) (g' := gas - 7)
      (by rw [hext0, memoryExtend_zero]; exact congrArg (· :: v :: rest) hptr)
      (by rw [hext0, memoryExtend_zero]) (by rw [hext0]; gas_ok)
    step dupR 0
    step dupR 2
    step dupR 1
    step Gas.mstoreG (by code_fact) (by code_fact) (by rw [hext1]; gas_ok)
    step Gas.reshapeG (s' := (0x60 : U256) :: 0x60 :: v :: rest) (m' := M ++ wordBytes v) (g' := gas - 22) rfl
      (by rw [hext1]; exact hmem1) (by rw [hext1]; gas_ok)
    step pushR 1 (0x20 : U256)
    step binR 0x01 instruction_add
    step swapR 1
    norm
    step popR
    step popR
    step pushR 1 (0x40 : U256)
    step Gas.mloadG (by code_fact) (by code_fact) (by rw [hext2]; gas_ok)
    step Gas.reshapeG (s' := (0x60 : U256) :: 0x80 :: rest) (m' := M ++ wordBytes v) (g' := gas - 41)
      (by rw [hext2, memoryExtend_zero, show (0x40 : U256).toNat = 64 from rfl, hread2, hptr]
          rfl) (by rw [hext2, memoryExtend_zero])
      (by rw [hext2]; gas_ok)
    step dupR 0
    step swapR 1
    norm
    step binR 0x03 instruction_sub
    step swapR 0
    norm
    have hext3 : extendMemory (M ++ wordBytes v).size [((0x60 : U256), (0x20 : U256))] =
        ⟨0, 0⟩ := by
      rw [ByteArray.size_append, hM, size_wordBytes]; decide
    refine Gas.SpecG.reshape (s' := (0x60 : U256) :: 0x20 :: rest) (by rfl) rfl rfl ?_
    refine (Gas.returnG (by code_fact) (by code_fact) (by rw [hext3]; gas_ok)).consequence
      (fun _ h => h) ?_
    rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
    refine ⟨hr, he, ?_, ?_, hs, hss⟩
    · rw [ho, hext3, memoryExtend_zero]
      exact read_after hM _ (size_wordBytes v)
    · rw [hgas, hext3]
      gas_ok

/-- The copies of the block that returns a bool: 695 (deprecated), 1277 (getBlackListStatus),
1430 (paused), 2250 (isBlackListed). -/
abbrev BOOL_PCS : List Nat := [695, 1277, 1430, 2250]

/-- The return block of a bool (`BOOL_PCS`): as `ret`, the word written is `ISZERO` four times
of the top word (0 or 1). -/
theorem retB {p : Nat} (hp : p ∈ BOOL_PCS) {M : ByteArray} (hM : M.size = 96)
    (hptr : loadWord (memoryReadBytes M 64 32) 0 32 = 0x60) {v : U256} {rest : List U256}
    (hrest : rest.length ≤ 900) {gas : Nat} (hg : 65 ≤ gas) :
    Gas.SpecG fork (At CODE message p (v :: rest) M gas state substate)
      (Halted false (wordBytes (isZero (isZero (isZero (isZero v))))) (gas - 65) state substate) := by
  have hext0 : extendMemory M.size [((0x40 : U256), (32 : U256))] = ⟨0, 0⟩ := by
    rw [hM]; decide
  have hext1 : extendMemory M.size [((0x60 : U256), (32 : U256))] = ⟨3, 32⟩ := by
    rw [hM]; decide
  have hext2 : extendMemory (M ++ wordBytes (isZero (isZero (isZero (isZero v))))).size [((0x40 : U256), (32 : U256))] = ⟨0, 0⟩ := by
    rw [ByteArray.size_append, hM, size_wordBytes]; decide
  have hmem1 : memoryWrite (memoryExtend M 32) (0x60 : U256).toNat (wordBytes (isZero (isZero (isZero (isZero v))))) =
      M ++ wordBytes (isZero (isZero (isZero (isZero v)))) := by
    have h := memoryWrite_extend_end (memory := M) (value := wordBytes (isZero (isZero (isZero (isZero v)))))
    rwa [size_wordBytes, hM] at h
  have hread2 : memoryReadBytes (M ++ wordBytes (isZero (isZero (isZero (isZero v))))) 64 32 = memoryReadBytes M 64 32 := by
    simp only [memoryReadBytes, ByteArray.extract_append, hM]
    simp
  simp only [BOOL_PCS, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl
  all_goals
    step jumpdestR
    step pushR 1 (0x40 : U256)
    step Gas.mloadG (by code_fact) (by code_fact) (by rw [hext0]; gas_ok)
    step Gas.reshapeG (s' := (0x60 : U256) :: v :: rest) (m' := M) (g' := gas - 7)
      (by rw [hext0, memoryExtend_zero]; exact congrArg (· :: v :: rest) hptr)
      (by rw [hext0, memoryExtend_zero]) (by rw [hext0]; gas_ok)
    step dupR 0
    step dupR 2
    step unR 0x15 instruction_iszero
    step unR 0x15 instruction_iszero
    step unR 0x15 instruction_iszero
    step unR 0x15 instruction_iszero
    step dupR 1
    step Gas.mstoreG (by code_fact) (by code_fact) (by rw [hext1]; gas_ok)
    step Gas.reshapeG (s' := (0x60 : U256) :: 0x60 :: v :: rest) (m' := M ++ wordBytes (isZero (isZero (isZero (isZero v))))) (g' := gas - 34) rfl
      (by rw [hext1]; exact hmem1) (by rw [hext1]; gas_ok)
    step pushR 1 (0x20 : U256)
    step binR 0x01 instruction_add
    step swapR 1
    norm
    step popR
    step popR
    step pushR 1 (0x40 : U256)
    step Gas.mloadG (by code_fact) (by code_fact) (by rw [hext2]; gas_ok)
    step Gas.reshapeG (s' := (0x60 : U256) :: 0x80 :: rest) (m' := M ++ wordBytes (isZero (isZero (isZero (isZero v))))) (g' := gas - 53)
      (by rw [hext2, memoryExtend_zero, show (0x40 : U256).toNat = 64 from rfl, hread2, hptr]
          rfl) (by rw [hext2, memoryExtend_zero])
      (by rw [hext2]; gas_ok)
    step dupR 0
    step swapR 1
    norm
    step binR 0x03 instruction_sub
    step swapR 0
    norm
    have hext3 : extendMemory (M ++ wordBytes (isZero (isZero (isZero (isZero v))))).size [((0x60 : U256), (0x20 : U256))] =
        ⟨0, 0⟩ := by
      rw [ByteArray.size_append, hM, size_wordBytes]; decide
    refine Gas.SpecG.reshape (s' := (0x60 : U256) :: 0x20 :: rest) (by rfl) rfl rfl ?_
    refine (Gas.returnG (by code_fact) (by code_fact) (by rw [hext3]; gas_ok)).consequence
      (fun _ h => h) ?_
    rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
    refine ⟨hr, he, ?_, ?_, hs, hss⟩
    · rw [ho, hext3, memoryExtend_zero]
      exact read_after hM _ (size_wordBytes (isZero (isZero (isZero (isZero v)))))
    · rw [hgas, hext3]
      gas_ok

/-- The copies of the block that returns an address: 935 (upgradedAddress), 1573 (getOwner),
1658 (owner). -/
abbrev ADDR_PCS : List Nat := [935, 1573, 1658]

/-- The return block of an address (`ADDR_PCS`): as `ret`, the word written is the top word
masked twice to 160 bits. -/
theorem retA {p : Nat} (hp : p ∈ ADDR_PCS) {M : ByteArray} (hM : M.size = 96)
    (hptr : loadWord (memoryReadBytes M 64 32) 0 32 = 0x60) {v : U256} {rest : List U256}
    (hrest : rest.length ≤ 900) {gas : Nat} (hg : 65 ≤ gas) :
    Gas.SpecG fork (At CODE message p (v :: rest) M gas state substate)
      (Halted false (wordBytes (bitwiseAnd ADDR_MASK (bitwiseAnd ADDR_MASK v))) (gas - 65) state substate) := by
  have hext0 : extendMemory M.size [((0x40 : U256), (32 : U256))] = ⟨0, 0⟩ := by
    rw [hM]; decide
  have hext1 : extendMemory M.size [((0x60 : U256), (32 : U256))] = ⟨3, 32⟩ := by
    rw [hM]; decide
  have hext2 : extendMemory (M ++ wordBytes (bitwiseAnd ADDR_MASK (bitwiseAnd ADDR_MASK v))).size [((0x40 : U256), (32 : U256))] = ⟨0, 0⟩ := by
    rw [ByteArray.size_append, hM, size_wordBytes]; decide
  have hmem1 : memoryWrite (memoryExtend M 32) (0x60 : U256).toNat (wordBytes (bitwiseAnd ADDR_MASK (bitwiseAnd ADDR_MASK v))) =
      M ++ wordBytes (bitwiseAnd ADDR_MASK (bitwiseAnd ADDR_MASK v)) := by
    have h := memoryWrite_extend_end (memory := M) (value := wordBytes (bitwiseAnd ADDR_MASK (bitwiseAnd ADDR_MASK v)))
    rwa [size_wordBytes, hM] at h
  have hread2 : memoryReadBytes (M ++ wordBytes (bitwiseAnd ADDR_MASK (bitwiseAnd ADDR_MASK v))) 64 32 = memoryReadBytes M 64 32 := by
    simp only [memoryReadBytes, ByteArray.extract_append, hM]
    simp
  simp only [ADDR_PCS, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl
  all_goals
    step jumpdestR
    step pushR 1 (0x40 : U256)
    step Gas.mloadG (by code_fact) (by code_fact) (by rw [hext0]; gas_ok)
    step Gas.reshapeG (s' := (0x60 : U256) :: v :: rest) (m' := M) (g' := gas - 7)
      (by rw [hext0, memoryExtend_zero]; exact congrArg (· :: v :: rest) hptr)
      (by rw [hext0, memoryExtend_zero]) (by rw [hext0]; gas_ok)
    step dupR 0
    step dupR 2
    step pushR 20 ADDR_MASK
    step binR 0x16 (instruction_of_stackOnlyStep rfl)
    step pushR 20 ADDR_MASK
    step binR 0x16 (instruction_of_stackOnlyStep rfl)
    step dupR 1
    step Gas.mstoreG (by code_fact) (by code_fact) (by rw [hext1]; gas_ok)
    step Gas.reshapeG (s' := (0x60 : U256) :: 0x60 :: v :: rest) (m' := M ++ wordBytes (bitwiseAnd ADDR_MASK (bitwiseAnd ADDR_MASK v))) (g' := gas - 34) rfl
      (by rw [hext1]; exact hmem1) (by rw [hext1]; gas_ok)
    step pushR 1 (0x20 : U256)
    step binR 0x01 instruction_add
    step swapR 1
    norm
    step popR
    step popR
    step pushR 1 (0x40 : U256)
    step Gas.mloadG (by code_fact) (by code_fact) (by rw [hext2]; gas_ok)
    step Gas.reshapeG (s' := (0x60 : U256) :: 0x80 :: rest) (m' := M ++ wordBytes (bitwiseAnd ADDR_MASK (bitwiseAnd ADDR_MASK v))) (g' := gas - 53)
      (by rw [hext2, memoryExtend_zero, show (0x40 : U256).toNat = 64 from rfl, hread2, hptr]
          rfl) (by rw [hext2, memoryExtend_zero])
      (by rw [hext2]; gas_ok)
    step dupR 0
    step swapR 1
    norm
    step binR 0x03 instruction_sub
    step swapR 0
    norm
    have hext3 : extendMemory (M ++ wordBytes (bitwiseAnd ADDR_MASK (bitwiseAnd ADDR_MASK v))).size [((0x60 : U256), (0x20 : U256))] =
        ⟨0, 0⟩ := by
      rw [ByteArray.size_append, hM, size_wordBytes]; decide
    refine Gas.SpecG.reshape (s' := (0x60 : U256) :: 0x20 :: rest) (by rfl) rfl rfl ?_
    refine (Gas.returnG (by code_fact) (by code_fact) (by rw [hext3]; gas_ok)).consequence
      (fun _ h => h) ?_
    rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
    refine ⟨hr, he, ?_, ?_, hs, hss⟩
    · rw [ho, hext3, memoryExtend_zero]
      exact read_after hM _ (size_wordBytes (bitwiseAnd ADDR_MASK (bitwiseAnd ADDR_MASK v)))
    · rw [hgas, hext3]
      gas_ok

/-- The test word of a packed flag at byte 20 is that byte, as a word. -/
theorem flag_eq (w : U256) :
    bitwiseAnd (0xff : U256) (div w (exp (0x0100 : U256) (0x14 : U256))) =
      BitVec.ofNat 256 (byte20 w) := by
  have he : exp (0x0100 : U256) (0x14 : U256) = BitVec.ofNat 256 (2 ^ 160) := by decide +kernel
  have hne : (BitVec.ofNat 256 (2 ^ 160) : U256) ≠ 0 := by decide
  have h160 : (BitVec.ofNat 256 (2 ^ 160) : U256).toNat = 2 ^ 160 := by
    rw [BitVec.toNat_ofNat]
  have hlt : w.toNat / 2 ^ 160 < 2 ^ 256 :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) w.isLt
  have hb : w.toNat / 2 ^ 160 % 256 < 2 ^ 256 :=
    Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide)
  apply BitVec.eq_of_toNat_eq
  simp only [he, bitwiseAnd, div, hne, ite_false, BitVec.toNat_and, h160, BitVec.toNat_ofNat,
    byte20, Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt hb]
  rw [show BitVec.toNat (0xff : U256) = 2 ^ 8 - 1 by rfl, Nat.and_comm,
    Nat.and_two_pow_sub_one_eq_mod]

/-- A set flag makes the triple ISZERO of its test word 0. -/
theorem isZero3_flag {w : U256} (h : byte20 w ≠ 0) :
    isZero (isZero (isZero (bitwiseAnd (0xff : U256) (div w (exp (0x0100 : U256) (0x14 : U256)))))) =
      0 := by
  rw [flag_eq]
  have hb : byte20 w < 256 := Nat.mod_lt _ (by decide)
  have hne : (BitVec.ofNat 256 (byte20 w) : U256) ≠ 0 := by
    intro hz
    have := congrArg BitVec.toNat hz
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
    exact h this
  unfold isZero
  rw [ite_eq_right hne]
  decide

/-- A clear flag makes the triple ISZERO of its test word nonzero. -/
theorem isZero3_flag_ne {w : U256} (h : byte20 w = 0) :
    isZero (isZero (isZero (bitwiseAnd (0xff : U256) (div w (exp (0x0100 : U256) (0x14 : U256)))))) ≠
      0 := by
  rw [flag_eq, h]
  decide

/-- Byte 20 of a word is 0 exactly when the test word of the deprecation check is nonzero. -/
theorem isZero_flag_ne {w : U256} (h : byte20 w = 0) :
    isZero (bitwiseAnd (0xff : U256) (div w (exp (0x0100 : U256) (0x14 : U256)))) ≠ 0 := by
  have he : exp (0x0100 : U256) (0x14 : U256) = BitVec.ofNat 256 (2 ^ 160) := by decide +kernel
  have hne : (BitVec.ofNat 256 (2 ^ 160) : U256) ≠ 0 := by decide
  have h160 : (BitVec.ofNat 256 (2 ^ 160) : U256).toNat = 2 ^ 160 := by
    rw [BitVec.toNat_ofNat]
  have hz : bitwiseAnd (0xff : U256) (div w (exp (0x0100 : U256) (0x14 : U256))) = 0 := by
    apply BitVec.eq_of_toNat_eq
    simp only [he, bitwiseAnd, div, hne, ite_false, BitVec.toNat_and, h160, BitVec.toNat_ofNat]
    have hlt : w.toNat / 2 ^ 160 < 2 ^ 256 :=
      Nat.lt_of_le_of_lt (Nat.div_le_self _ _) w.isLt
    rw [show BitVec.toNat (0xff : U256) = 2 ^ 8 - 1 by rfl, Nat.mod_eq_of_lt hlt, Nat.and_comm,
      Nat.and_two_pow_sub_one_eq_mod]
    simpa [byte20] using h
  unfold isZero
  split
  · decide
  · contradiction

/-- The deprecation check, at 3565 (totalSupply), 4665 (balanceOf) and 6925 (allowance).

It reads slot 10 and, when byte 20 of it is 0, jumps to `dest` with a 0 pushed on the stack. -/
theorem depCheck (hfork : .berlin ≤ fork) {p d : Nat}
    (hp : (p = 3565 ∧ d = 0x0eb4) ∨ (p = 4665 ∧ d = 0x1337) ∨ (p = 6925 ∧ d = 0x1c3f))
    {M : ByteArray} {rest : List U256}
    (hrest : rest.length ≤ 16) {c10 : Bool}
    (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    (hc10 : coldIn substate message.currentTarget 10 = c10)
    {gas : Nat} (hg : 109 + slotCost c10 ≤ gas) :
    Gas.HoareG fork (At CODE message p rest M gas state substate)
      (At CODE message d (0 :: rest) M (gas - (109 + slotCost c10))
        (readSlot state message.currentTarget 10)
        (accessSlot substate message.currentTarget 10)) := by
  have hexp : exponentBytes (0x14 : U256) = 1 := by decide
  rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals
    step jumpdestR
    step pushR 1 (0 : U256)
    step pushR 1 (0x0a : U256)
    step pushR 1 (0x14 : U256)
    step swapR 0
    norm
    step Gas.sloadG hfork (cold := c10) (by code_fact) (by code_fact) hc10 (by gas_ok)
    step swapR 0
    norm
    step pushR 2 (0x0100 : U256)
    step Gas.expLG (Nat.le_trans (by decide) hfork) (by code_fact) (by code_fact) (by gas_ok)
    step swapR 0
    norm
    step binR 0x04 (instruction_of_stackOnlyStep rfl)
    step pushR 1 (0xff : U256)
    step binR 0x16 (instruction_of_stackOnlyStep rfl)
    step unR 0x15 instruction_iszero
    step pushAnyR 2
    step jumpiR (isZero_flag_ne hdep)
    exact (repc (by decide)).seq (Gas.reshapeG rfl rfl (by gas_ok))

end UsdtVerify
