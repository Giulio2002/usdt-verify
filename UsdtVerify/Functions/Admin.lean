import UsdtVerify.Functions.TransferOk
import UsdtVerify.Functions.PauseSpec

/-!
# Blocks shared by the admin functions (round 7)

- `hashTail7`: the mapping-lookup tail of `TransferOk.hashTail` at its other copies.
- `entry1`: the entry of a function with one address argument (value check, argument word 0
  masked to 160 bits, jump to the body).
- `setLow`, `lowByte_setLow`: the word that the blacklist functions write, with its low byte.
- `logAddr`: a log of one topic whose data is one address word, then the jump back and STOP.
-/

namespace UsdtVerify.Admin

open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts
open Transfer TransferOk

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate}

/-- The other copies of the lookup tail (`TransferOk.HASH_PCS` lists the ones used before). -/
abbrev HASH_PCS7 : List Nat := [3383, 4531, 5398, 6169, 6267, 6378, 6670, 6797, 7387, 7917, 8018,
  10822, 10883]

/-- The tail of a lookup in a mapping at the copies in `HASH_PCS7` (as `hashTail`). -/
theorem hashTail7 {p : Nat} (hp : p ∈ HASH_PCS7) {x base : U256}
    {rest : List U256} (hrest : rest.length ≤ 900) {M : ByteArray} (hM : M.size = 96) {gas : Nat}
    (hg : 84 ≤ gas) :
    Gas.HoareG fork (At CODE message p (x :: 0 :: base :: rest) M gas state substate)
      (At CODE message (p + 58) (mapSlot (mkey x) base :: rest) (mapMem M (mkey x) base)
        (gas - 84) state substate) := by
  have hs1 : (memoryWrite M 0 (wordBytes (mkey x))).size = 96 := by
    rw [size_memoryWrite] <;> simp [hM, size_wordBytes]
  have hext1 : extendMemory M.size [((0 : U256), (32 : U256))] = ⟨0, 0⟩ := by rw [hM]; decide
  have hext2 : extendMemory (memoryWrite M 0 (wordBytes (mkey x))).size
      [((0x20 : U256), (32 : U256))] = ⟨0, 0⟩ := by rw [hs1]; decide
  have hext3 : extendMemory (mapMem M (mkey x) base).size [((0 : U256), (0x40 : U256))] =
      ⟨0, 0⟩ := by rw [size_mapMem hM]; decide
  have hk : keccak256Cost (0x40 : U256) = 42 := by decide
  have hread : memoryReadBytes (mapMem M (mkey x) base) 0 64 =
      wordBytes (mkey x) ++ wordBytes base := by
    have h := memoryReadBytes_memoryWrite_memoryWrite (memory := M) (a := wordBytes (mkey x))
      (b := wordBytes base) (s := 0) (by simp [hM, size_wordBytes])
    simpa [size_wordBytes, mapMem] using h
  simp only [HASH_PCS7, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    step pushR 20 ADDR_MASK
    step binR 0x16 Local.instruction_and
    step pushR 20 ADDR_MASK
    step binR 0x16 Local.instruction_and
    step dupR 1
    step Gas.mstoreG (by code_fact) (by code_fact) (by rw [hext1]; gas_ok)
    step Gas.reshapeG (m' := memoryWrite M 0 (wordBytes (mkey x))) rfl
      (by rw [hext1, memoryExtend_zero]; rfl) (by rw [hext1] <;> gas_ok)
    step pushR 1 (0x20 : U256)
    step binR 0x01 instruction_add
    step swapR 0
    norm
    step dupR 1
    step Gas.reshapeG (s' := (0x20 : U256) :: base :: 0x20 :: rest) rfl rfl rfl
    step Gas.mstoreG (by code_fact) (by code_fact) (by rw [hext2]; gas_ok)
    step Gas.reshapeG (m' := mapMem M (mkey x) base) rfl (by rw [hext2, memoryExtend_zero]; rfl)
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

/-- The entries `(e, r, b)` of the functions with one address argument: addBlackList,
removeBlackList, deprecate, transferOwnership, destroyBlackFunds. -/
abbrev ENTRY1 : List (Nat × Nat × Nat) := [(721, 0x0308, 3284), (2276, 0x091b, 7288),
  (553, 0x0260, 2646), (2374, 0x097d, 7605), (2431, 0x09b6, 7818)]

/-- The entry of a function with one address argument: a call with no value goes to the body
`b` with argument word 0 masked to 160 bits and the return address `r`. -/
theorem entry1 {e r b : Nat} (hp : (e, r, b) ∈ ENTRY1) (hv : message.value = 0) {x : U256}
    {M : ByteArray} {gas : Nat} (hg : 74 ≤ gas) :
    Gas.HoareG fork (At CODE message e [x] M gas state substate)
      (At CODE message b [addrArg message.data 0, BitVec.ofNat 256 r, x] M (gas - 74) state
        substate) := by
  simp only [ENTRY1, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hp
  rcases hp with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩
  all_goals
    step jumpdestR
    step Gas.callvalueG (by code_fact) (by code_fact) (by gas_ok) (by stk_ok)
    step unR 0x15 instruction_iszero
    step pushAnyR 2
    step jumpiR (by simp [hv, isZero])
    step jumpdestR
    step pushAnyR 2
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
    step pushAnyR 2
    step jumpR
    exact restate (by decide) (congrArg (addrArg message.data 0 :: · :: [x]) (by decide)) rfl
      (by gas_ok) rfl rfl

/-- The key word of an address argument is the argument. -/
theorem mkey_addrArg0 (data : ByteArray) : mkey (addrArg data 0) = addrArg data 0 := by
  simp only [mkey, addrArg, mask_mask]

/-! ## The word of a blacklist flag -/

/-- A word with its low byte replaced by `b` (0 or 1): `(w & ~0xff) | b`. -/
def setLow (w b : U256) : U256 := bitwiseOr b (bitwiseAnd (bitwiseNot 0xff) w)

/-- The low byte of a word, from its bits 0 to 7. -/
theorem lowByte_of_bits {x : U256} (b : Nat) (hb : b < 256)
    (h : ∀ j, j < 8 → x.getLsbD j = b.testBit j) : x.toNat % 256 = b := by
  apply Nat.eq_of_testBit_eq
  intro j
  change (x.toNat % 2 ^ 8).testBit j = b.testBit j
  rw [Nat.testBit_mod_two_pow]
  by_cases hj : j < 8
  · simp only [hj, decide_true, Bool.true_and]
    exact h j hj
  · simp only [hj, decide_false, Bool.false_and]
    have h8 : 2 ^ 8 ≤ 2 ^ j := Nat.pow_le_pow_right (by decide) (by omega)
    exact (Nat.testBit_lt_two_pow (show b < 2 ^ j by omega)).symm

/-- The low byte of `setLow w b` is `b`, for `b` 0 or 1. -/
theorem lowByte_setLow (w b : U256) (hb : b = 0 ∨ b = 1) : (setLow w b).toNat % 256 = b.toNat := by
  have hlt : b.toNat < 256 := by rcases hb with rfl | rfl <;> decide
  apply lowByte_of_bits _ hlt
  intro j hj
  have hff : (0xff : U256).getLsbD j = true := by
    rw [show (0xff : U256) = BitVec.ofNat 256 (2 ^ 8 - 1) by decide, BitVec.getLsbD_ofNat,
      Nat.testBit_two_pow_sub_one]
    simp; omega
  simp only [setLow, bitwiseOr, bitwiseAnd, bitwiseNot, BitVec.getLsbD_or, BitVec.getLsbD_and,
    BitVec.getLsbD_not, hff]
  simp only [Bool.not_true, Bool.false_and, Bool.and_false, Bool.or_false]
  rfl

/-- `setLow w b` keeps every bit of `w` from bit 8 on. -/
theorem bit_setLow (w b : U256) (hb : b = 0 ∨ b = 1) {i : Nat} (hi : 8 ≤ i) :
    (setLow w b).getLsbD i = w.getLsbD i := by
  have hff : (0xff : U256).getLsbD i = false := by
    rw [show (0xff : U256) = BitVec.ofNat 256 (2 ^ 8 - 1) by decide, BitVec.getLsbD_ofNat,
      Nat.testBit_two_pow_sub_one]
    simp; omega
  have hbi : b.getLsbD i = false := by
    rcases hb with rfl | rfl
    · simp
    · show Nat.testBit 1 i = false
      rw [Pause.testBit_one']; simp; omega
  by_cases h' : 256 ≤ i
  · rw [BitVec.getLsbD_of_ge (setLow w b) i h', BitVec.getLsbD_of_ge w i h']
  have h : i < 256 := by omega
  simp only [setLow, bitwiseOr, bitwiseAnd, bitwiseNot, BitVec.getLsbD_or, BitVec.getLsbD_and,
    BitVec.getLsbD_not, hff, hbi]
  cases w.getLsbD i <;> simp [h]

end UsdtVerify.Admin
