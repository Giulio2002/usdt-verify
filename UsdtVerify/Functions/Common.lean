import UsdtVerify.Table
import UsdtVerify.Spec.Storage
import EthLib.Execution.Proofs.Evm.Machine.Memory

/-!
# Blocks shared by several functions of USDT

- `MEM0`: the memory after the prelude, and its facts.
- `ret`: the block that returns one word, at 797 (totalSupply) and at 1511 (balanceOf).
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

/-- The return block at 797, and its copy at 1511: it writes the top word at the free memory
pointer 0x60 and returns those 32 bytes.

The memory has 96 bytes and holds the pointer 0x60 at 0x40. -/
theorem ret {p : Nat} (hp : p = 797 ∨ p = 1511) {M : ByteArray} (hM : M.size = 96)
    (hptr : loadWord (memoryReadBytes M 64 32) 0 32 = 0x60) {v x : U256} {gas : Nat}
    (hg : 53 ≤ gas) :
    Spec fork (At CODE message p [v, x] M gas state substate)
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
  rcases hp with rfl | rfl
  all_goals
    step jumpdestR
    step pushR 1 (0x40 : U256)
    step mload (by code_fact) (by code_fact) (by rw [hext0]; gas_ok)
    step reshape (s' := [0x60, v, x]) (m' := M) (g' := gas - 7)
      (by rw [hext0, memoryExtend_zero]; exact congrArg (· :: [v, x]) hptr)
      (by rw [hext0, memoryExtend_zero]) (by rw [hext0]; gas_ok)
    step dupR 0
    step dupR 2
    step dupR 1
    step mstore (by code_fact) (by code_fact) (by rw [hext1]; gas_ok)
    step reshape (s' := [0x60, 0x60, v, x]) (m' := M ++ wordBytes v) (g' := gas - 22) rfl
      (by rw [hext1]; exact hmem1) (by rw [hext1]; gas_ok)
    step pushR 1 (0x20 : U256)
    step binR 0x01 instruction_add
    step swapR 1
    norm
    step popR
    step popR
    step pushR 1 (0x40 : U256)
    step mload (by code_fact) (by code_fact) (by rw [hext2]; gas_ok)
    step reshape (s' := [0x60, 0x80, x]) (m' := M ++ wordBytes v) (g' := gas - 41)
      (by rw [hext2, memoryExtend_zero, show (0x40 : U256).toNat = 64 from rfl, hread2, hptr]
          rfl) (by rw [hext2, memoryExtend_zero])
      (by rw [hext2]; gas_ok)
    step dupR 0
    step swapR 1
    norm
    step binR 0x03 Local.instruction_sub
    step swapR 0
    norm
    have hext3 : extendMemory (M ++ wordBytes v).size [((0x60 : U256), (0x20 : U256))] =
        ⟨0, 0⟩ := by
      rw [ByteArray.size_append, hM, size_wordBytes]; decide
    refine Spec.reshape (s' := [0x60, 0x20, x]) (by rfl) rfl rfl ?_
    refine (Logic.«return» (by code_fact) (by code_fact) (by rw [hext3]; gas_ok)).consequence
      (fun _ h => h) ?_
    rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
    refine ⟨hr, he, ?_, ?_, hs, hss⟩
    · rw [ho, hext3, memoryExtend_zero]
      exact read_after hM _ (size_wordBytes v)
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
  rw [if_neg hne]
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

/-- The deprecation check, at 3565 (totalSupply) and at 4665 (balanceOf).

It reads slot 10 and, when byte 20 of it is 0, jumps to `dest` with a 0 pushed on the stack. -/
theorem depCheck (hfork : .berlin ≤ fork) {p d : Nat}
    (hp : (p = 3565 ∧ d = 0x0eb4) ∨ (p = 4665 ∧ d = 0x1337)) {M : ByteArray} {rest : List U256}
    (hrest : rest.length ≤ 16) {c10 : Bool}
    (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    (hc10 : coldIn substate message.currentTarget 10 = c10)
    {gas : Nat} (hg : 109 + slotCost c10 ≤ gas) :
    Hoare fork (At CODE message p rest M gas state substate)
      (At CODE message d (0 :: rest) M (gas - (109 + slotCost c10))
        (readSlot state message.currentTarget 10)
        (accessSlot substate message.currentTarget 10)) := by
  have hexp : exponentBytes (0x14 : U256) = 1 := by decide
  rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals
    step jumpdestR
    step pushR 1 (0 : U256)
    step pushR 1 (0x0a : U256)
    step pushR 1 (0x14 : U256)
    step swapR 0
    norm
    step sload hfork (cold := c10) (by code_fact) (by code_fact) hc10 (by gas_ok)
    step swapR 0
    norm
    step pushR 2 (0x0100 : U256)
    step Local.exp (Nat.le_trans (by decide) hfork) (by code_fact) (by code_fact) (by gas_ok)
    step swapR 0
    norm
    step binR 0x04 Local.instruction_div
    step pushR 1 (0xff : U256)
    step binR 0x16 Local.instruction_and
    step unR 0x15 instruction_iszero
    step pushAnyR 2
    step jumpiR (isZero_flag_ne hdep)
    exact (repc (by decide)).seq (reshape rfl rfl (by gas_ok))

end UsdtVerify
