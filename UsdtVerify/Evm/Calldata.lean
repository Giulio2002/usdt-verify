import UsdtVerify.Evm.Steps
import EthLib.Base.Proofs.BigEndian

/-!
# Call data, stated over its bytes

- `selector data`: the number of the first four bytes of the call data, big-endian.
- `selector_word`: the word that the dispatcher computes from the call data is that number.
-/

namespace UsdtVerify

open EthLib.Base (Fork U256 bytesToNat byteAt)
open EthLib.Execution.Evm

/-- The first four bytes of the call data, as a big-endian number (0 past the end). -/
def selector (data : ByteArray) : Nat :=
  bytesToNat [byteAt data 0, byteAt data 1, byteAt data 2, byteAt data 3]

theorem selector_lt (data : ByteArray) : selector data < 2 ^ 32 := by
  have h := EthLib.Base.bytesToNat_lt [byteAt data 0, byteAt data 1, byteAt data 2, byteAt data 3]
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reducePow] at h
  unfold selector
  simp only [Nat.reducePow]
  exact h

/-- The word of call data at 0, divided by `2 ^ 224` and masked to 32 bits, is the selector. -/
theorem selector_word (data : ByteArray) :
    bitwiseAnd (BitVec.ofNat 256 0xffffffff) (div (loadWord data 0 32) (BitVec.ofNat 256 (2 ^ 224))) =
      BitVec.ofNat 256 (selector data) := by
  have hsplit : bufferRead data 0 32 =
      [byteAt data 0, byteAt data 1, byteAt data 2, byteAt data 3] ++
        (List.range 28).map fun i => byteAt data (4 + i) := by
    simp only [bufferRead, List.range_succ, List.map_cons, List.map_nil,
      List.range_zero, List.nil_append, List.cons_append, Nat.zero_add]
  have hB := EthLib.Base.bytesToNat_lt ((List.range 28).map fun i => byteAt data (4 + i))
  simp only [List.length_map, List.length_range] at hB
  have hA := selector_lt data
  have hval : bytesToNat (bufferRead data 0 32) =
      selector data * 2 ^ 224 + bytesToNat ((List.range 28).map fun i => byteAt data (4 + i)) := by
    rw [hsplit, EthLib.Base.bytesToNat_append]
    simp [selector, show (256 : Nat) ^ 28 = 2 ^ 224 by rfl]
  have hlt : bytesToNat (bufferRead data 0 32) < 2 ^ 256 := by
    rw [hval]
    have : selector data * 2 ^ 224 ≤ (2 ^ 32 - 1) * 2 ^ 224 :=
      Nat.mul_le_mul_right _ (by omega)
    have h256 : (2 : Nat) ^ 256 = 2 ^ 32 * 2 ^ 224 := by rfl
    rw [h256]
    rw [Nat.sub_mul, Nat.one_mul] at this
    have : 2 ^ 224 ≤ 2 ^ 32 * 2 ^ 224 := Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)
    omega
  have hq : bytesToNat (bufferRead data 0 32) / 2 ^ 224 = selector data := by
    rw [hval, Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hB,
      Nat.zero_add]
  apply BitVec.eq_of_toNat_eq
  have hne : (BitVec.ofNat 256 (2 ^ 224) : U256) ≠ 0 := by decide
  have h224 : (BitVec.ofNat 256 (2 ^ 224) : U256).toNat = 2 ^ 224 := by
    rw [BitVec.toNat_ofNat]
  have hmask : (BitVec.ofNat 256 0xffffffff : U256).toNat = 2 ^ 32 - 1 := by
    rw [BitVec.toNat_ofNat]
  simp only [bitwiseAnd, div, hne, ite_false, loadWord, BitVec.toNat_and, h224, hmask]
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt, hq,
    Nat.mod_eq_of_lt (show selector data < 2 ^ 256 by have := hA; omega), Nat.and_comm,
    Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hA, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show selector data < 2 ^ 256 by have := hA; omega)]

/-- The mask of the low 160 bits of a word, the bits of an address. -/
abbrev ADDR_MASK : U256 := BitVec.ofNat 256 (2 ^ 160 - 1)

/-- The low 160 bits of argument word `i` of the call data (the word at `4 + 32 * i`). -/
def addrArg (data : ByteArray) (i : Nat) : U256 :=
  bitwiseAnd ADDR_MASK (loadWord data (4 + 32 * i) 32)

/-- Argument word `i` of the call data (the word at `4 + 32 * i`). -/
def wordArg (data : ByteArray) (i : Nat) : U256 := loadWord data (4 + 32 * i) 32

/-- Masking twice is masking once. -/
theorem mask_mask (w : U256) : bitwiseAnd ADDR_MASK (bitwiseAnd ADDR_MASK w) = bitwiseAnd ADDR_MASK w := by
  simp only [bitwiseAnd, ← BitVec.and_assoc, BitVec.and_self]

end UsdtVerify
