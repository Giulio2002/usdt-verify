import UsdtVerify.Usdt.Spec.Getters
import EthLib.Execution.Proofs.Evm.PowMod

/-!
# name() and symbol(): the specifications from pc 0

Proves what a call of name() or symbol() does from pc 0, for every form of string Solidity
stores: the short form, the empty string and the long form.

The parts below keep their own headers:

- name() and symbol(): the string getters
- name() and symbol() for any string Solidity stores: the empty string and the long form
-/

section

/-!
## name() and symbol(): the string getters

Read off the bytecode (TetherToken, Solidity 0.4.17): `name` is slot 7, `symbol` slot 8, both
`string`. A string of at most 31 bytes is stored in Solidity's short form: the bytes from the top
of the word, the low byte `2 * length` (low bit 0). The getter (body 2488 / 5206) reads the slot
three times: it computes the length `(w AND (256 * ISZERO(w AND 1) - 1)) / 2`, allocates
`0x20 + 32 * ceil(len / 32)` bytes at the free pointer 0x60 (the pointer becomes 0xa0), writes
the length at 0x60 and, for 1 ≤ len ≤ 31, `(w / 256) * 256` at 0x80. The shared return block
(430 / 1743) writes the offset 0x20 at 0xa0 and the length at 0xc0, copies the data with one
round of its loop (467) to 0xe0, then, the length not being a multiple of 32, masks the last
word with `NOT(256 ^ (32 - len) - 1)` and returns the 96 bytes from 0xa0.

- `spec_name` / `spec_symbol`: the returned bytes are the word 0x20, the word `n`, and
  `topBytes w n` (the first `n` bytes of the slot word, then zeros), exact gas.
- `spec_name_tether` / `spec_symbol_usdt`: for the words of "Tether USD" and "USDT", the bytes
  are the UTF-8 bytes of the string padded with zeros (checked by `decide +kernel`).

The empty string and the long form (32 bytes or more) are in the second part of this file.
-/

namespace UsdtVerify.Strings

open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts
open Transfer TransferOk Owner Admin BlackList Issue Getters

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate}

/-- The string getters `(e, r, b, k)`: entry, return block, body, slot. -/
abbrev STR : List (Nat × Nat × Nat × U256) := [(411, 430, 2488, 7), (1724, 1743, 5206, 8)]

/-- The entry of a string getter: with no value, jump to the body `b` with the return address
`r` pushed. -/
theorem entryS {e r b : Nat} {k : U256} (hp : (e, r, b, k) ∈ STR) (hv : message.value = 0)
    {x : U256} {M : ByteArray} {gas : Nat} (hg : 34 ≤ gas) :
    Gas.HoareG fork (At CODE message e [x] M gas state substate)
      (At CODE message b [BitVec.ofNat 256 r, x] M (gas - 34) state substate) := by
  simp only [STR, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hp
  rcases hp with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
  all_goals
    step jumpdestR
    step Gas.callvalueG (by code_fact) (by code_fact) (by gas_ok) (by stk_ok)
    step unR 0x15 instruction_iszero
    step pushAnyR 2
    step jumpiR (by simp [hv, isZero])
    step jumpdestR
    step pushAnyR 2
    step pushAnyR 2
    step jumpR
    exact restate (by decide) (congrArg (· :: [x]) (by decide)) rfl (by gas_ok) rfl rfl

theorem and255 (w : U256) : (bitwiseAnd 255 w).toNat = w.toNat % 256 := by
  simp only [bitwiseAnd, BitVec.toNat_and]
  rw [Nat.and_comm]
  exact Nat.and_two_pow_sub_one_eq_mod w.toNat 8

theorem and1 (w : U256) : (bitwiseAnd 1 w).toNat = w.toNat % 2 := by
  simp only [bitwiseAnd, BitVec.toNat_and]
  rw [Nat.and_comm]
  exact Nat.and_two_pow_sub_one_eq_mod w.toNat 1

/-- The length that the code computes from a slot word in the short form (low bit 0): the low
byte halved. -/
theorem lenWord {w : U256} {n : Nat} (hn : w.toNat % 256 = 2 * n) :
    div (bitwiseAnd (sub (mul 256 (isZero (bitwiseAnd 1 w))) 1) w) 2 = BitVec.ofNat 256 n := by
  have h0 : bitwiseAnd 1 w = 0 := BitVec.eq_of_toNat_eq (by rw [and1]; simp; omega)
  rw [h0, show sub (mul 256 (isZero 0)) 1 = (255 : U256) by decide]
  unfold div
  rw [ite_eq_right (by decide), and255]
  congr 1
  simp
  omega

theorem roundWord {n : Nat} (h1 : 1 ≤ n) (h31 : n ≤ 31) :
    add 32 (mul (div (add 31 (BitVec.ofNat 256 n)) 32) 32) = 64 := by
  apply BitVec.eq_of_toNat_eq
  have hd : div (add 31 (BitVec.ofNat 256 n)) 32 = 1 := by
    unfold div
    rw [ite_eq_right (by decide)]
    apply BitVec.eq_of_toNat_eq
    simp [add, BitVec.toNat_add]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  rw [hd]
  decide

theorem isZero_n {n : Nat} (h1 : 1 ≤ n) (h31 : n ≤ 31) : isZero (BitVec.ofNat 256 n) = 0 := by
  unfold isZero
  rw [ite_eq_right (fun h => by
    have := congrArg BitVec.toNat h
    simp at this
    omega)]

theorem lt_n {n : Nat} (h31 : n ≤ 31) : lessThan 31 (BitVec.ofNat 256 n) = 0 := by
  unfold lessThan
  rw [ite_eq_right (fun h => by
    simp at h
    omega)]

/-- The free memory pointer 0xa0 written at 0x40 over the memory of the prelude. -/
abbrev MEM1 : ByteArray := memoryWrite MEM0 64 (wordBytes 0xa0)

/-- GENERIC: MSTORE of a word at the end of memory appends it. -/
theorem write_end {A : ByteArray} {s : U256} (h : A.size = s.toNat) (v : U256) :
    memoryWrite (memoryExtend A 32) s.toNat (wordBytes v) = A ++ wordBytes v := by
  have e := memoryWrite_extend_end (memory := A) (value := wordBytes v)
  rwa [size_wordBytes, h] at e

theorem size_MEM1 : MEM1.size = 96 := by
  rw [MEM1, size_memoryWrite (by rw [size_wordBytes, size_MEM0]; decide), size_MEM0]

theorem mload_MEM1 : loadWord (memoryReadBytes MEM1 64 32) 0 32 = 0xa0 :=
  loadWord_memoryWrite_wordBytes _ (by rw [size_MEM0]; decide)

/-- The memory after the body: the free pointer moved to 0xa0, the length at 0x60, the data
word at 0x80. -/
abbrev MEMB (n : Nat) (d : U256) : ByteArray :=
  MEM1 ++ wordBytes (BitVec.ofNat 256 n) ++ wordBytes d

/-- The bodies `(b, k, r)`: the body, its slot, the return block it jumps to. -/
abbrev BODY : List (Nat × U256 × Nat) := [(2488, 7, 430), (5206, 8, 1743)]

/-- The body to the write of the free pointer: one read of the slot, the length, 0xa0 at 0x40. -/
theorem body1 {b r : Nat} {k : U256} (hp : (b, k, r) ∈ BODY) (hfork : .berlin ≤ fork) {n : Nat}
    (hn : (storageAt state message.currentTarget k).toNat % 256 = 2 * n)
    (h1 : 1 ≤ n) (h31 : n ≤ 31) {ck : Bool}
    (hck : coldIn substate message.currentTarget k = ck) {x y : U256}
    {gas : Nat} (hg : 102 + slotCost ck ≤ gas) :
    Gas.HoareG fork (At CODE message b [y, x] MEM0 gas state substate)
      (At CODE message (b + 44) [0x60, BitVec.ofNat 256 n, k, y, x] MEM1
        (gas - (102 + slotCost ck))
        (readSlot state message.currentTarget k)
        (accessSlot substate message.currentTarget k)) := by
  simp only [BODY, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hp
  rcases hp with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  all_goals
    step jumpdestR
    first | step pushR 1 (7 : U256) | step pushR 1 (8 : U256)
    step dupR 0
    step Gas.sloadG hfork (cold := ck) (by code_fact) (by code_fact) hck (by gas_ok)
    rw [getStorage_eq]
    step pushR 1 (1 : U256)
    step dupR 1
    step pushR 1 (1 : U256)
    step binR 0x16 Local.instruction_and
    step unR 0x15 instruction_iszero
    step pushR 2 (0x0100 : U256)
    step binR 0x02 Local.instruction_mul
    step binR 0x03 instruction_sub
    step binR 0x16 Local.instruction_and
    step pushR 1 (2 : U256)
    step swapR 0
    norm
    step binR 0x04 Local.instruction_div
    rw [lenWord hn]
    step dupR 0
    step pushR 1 (0x1f : U256)
    step binR 0x01 instruction_add
    step pushR 1 (0x20 : U256)
    step dupR 0
    step swapR 1
    norm
    step binR 0x04 Local.instruction_div
    step binR 0x02 Local.instruction_mul
    step pushR 1 (0x20 : U256)
    step binR 0x01 instruction_add
    step Gas.reshapeG (s' := [64, BitVec.ofNat 256 n, _, _, x]) (g' := gas - (81 + slotCost ck))
      (by rw [roundWord h1 h31]) rfl (by gas_ok)
    -- the free pointer: 0x60, moved to 0xa0
    step pushR 1 (0x40 : U256)
    have hext0 : extendMemory MEM0.size [((0x40 : U256), (32 : U256))] = ⟨0, 0⟩ := by
      rw [size_MEM0]; decide
    step Gas.mloadG (by code_fact) (by code_fact) (by rw [hext0]; gas_ok)
    step Gas.reshapeG (s' := [0x60, 64, BitVec.ofNat 256 n, _, _, x]) (m' := MEM0)
      (g' := gas - (87 + slotCost ck))
      (by rw [hext0, memoryExtend_zero]; exact congrArg (· :: _) mload_MEM0)
      (by rw [hext0, memoryExtend_zero]) (by rw [hext0]; gas_ok)
    step swapR 0
    norm
    step dupR 1
    step binR 0x01 instruction_add
    step pushR 1 (0x40 : U256)
    step Gas.mstoreG (by code_fact) (by code_fact) (by rw [hext0]; gas_ok)
    step Gas.reshapeG (s' := [0x60, BitVec.ofNat 256 n, _, _, x]) (m' := MEM1)
      (g' := gas - (102 + slotCost ck)) rfl
      (by rw [hext0, memoryExtend_zero]; rfl) (by rw [hext0]; gas_ok)
    exact restate (by decide) rfl rfl rfl rfl rfl

/-- The length written at 0x60, the second read of the slot (warm), the two length tests. -/
theorem body2 {b r : Nat} {k : U256} (hp : (b, k, r) ∈ BODY) (hfork : .berlin ≤ fork) {n : Nat}
    (hn : (storageAt state message.currentTarget k).toNat % 256 = 2 * n)
    (h1 : 1 ≤ n) (h31 : n ≤ 31)
    (hck : coldIn substate message.currentTarget k = false) {x y : U256}
    {gas : Nat} (hg : 217 ≤ gas) :
    Gas.HoareG fork (At CODE message (b + 44) [0x60, BitVec.ofNat 256 n, k, y, x] MEM1 gas state
        substate)
      (At CODE message (b + 88) [BitVec.ofNat 256 n, k, 0x80, BitVec.ofNat 256 n, k, 0x60, y, x]
        (MEM1 ++ wordBytes (BitVec.ofNat 256 n)) (gas - 217)
        (readSlot state message.currentTarget k)
        (accessSlot substate message.currentTarget k)) := by
  simp only [BODY, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hp
  rcases hp with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  all_goals
    -- the length at 0x60
    step dupR 0
    step swapR 2
    norm
    step swapR 1
    norm
    step swapR 0
    norm
    step dupR 1
    step dupR 1
    have hext1 : extendMemory MEM1.size [((0x60 : U256), (32 : U256))] = ⟨3, 32⟩ := by
      rw [size_MEM1]; decide
    step Gas.mstoreG (by code_fact) (by code_fact) (by rw [hext1]; gas_ok)
    have hm1 : memoryWrite (memoryExtend MEM1 32) (0x60 : U256).toNat
        (wordBytes (BitVec.ofNat 256 n)) = MEM1 ++ wordBytes (BitVec.ofNat 256 n) := by
      have h := memoryWrite_extend_end (memory := MEM1) (value := wordBytes (BitVec.ofNat 256 n))
      rwa [size_wordBytes, size_MEM1] at h
    step Gas.reshapeG (m' := MEM1 ++ wordBytes (BitVec.ofNat 256 n)) (g' := gas - 24)
      rfl (by rw [hext1]; exact hm1) (by rw [hext1]; gas_ok)
    step pushR 1 (0x20 : U256)
    step binR 0x01 instruction_add
    step Gas.reshapeG (s' := [0x80, BitVec.ofNat 256 n, _, 0x60, _, x]) rfl rfl rfl
    -- the second read of the slot (warm), the length again
    step dupR 2
    step dupR 0
    step Gas.sloadG hfork (cold := false) (by code_fact) (by code_fact) hck
      (by gas_ok)
    rw [getStorage_eq]
    step pushR 1 (1 : U256)
    step dupR 1
    step pushR 1 (1 : U256)
    step binR 0x16 Local.instruction_and
    step unR 0x15 instruction_iszero
    step pushR 2 (0x0100 : U256)
    step binR 0x02 Local.instruction_mul
    step binR 0x03 instruction_sub
    step binR 0x16 Local.instruction_and
    step pushR 1 (2 : U256)
    step swapR 0
    norm
    step binR 0x04 Local.instruction_div
    rw [lenWord hn]
    step dupR 0
    step unR 0x15 instruction_iszero
    step pushAnyR 2
    step jumpi0R (isZero_n h1 h31)
    step dupR 0
    step pushR 1 (0x1f : U256)
    step binR 0x10 Local.instruction_lt
    step pushAnyR 2
    step jumpi0R (lt_n h31)
    exact restate (by decide) rfl rfl (by gas_ok) rfl rfl

/-- The data word at 0x80 (third read, warm), then the return to `r`. -/
theorem body3 {b r : Nat} {k : U256} (hp : (b, k, r) ∈ BODY) (hfork : .berlin ≤ fork) {n : Nat}
    (hck : coldIn substate message.currentTarget k = false) {x : U256}
    {gas : Nat} (hg : 173 ≤ gas) :
    Gas.HoareG fork (At CODE message (b + 88)
        [BitVec.ofNat 256 n, k, 0x80, BitVec.ofNat 256 n, k, 0x60, BitVec.ofNat 256 r, x]
        (MEM1 ++ wordBytes (BitVec.ofNat 256 n)) gas state substate)
      (At CODE message r [0x60, BitVec.ofNat 256 r, x]
        (MEMB n (mul (div (storageAt state message.currentTarget k) 0x100) 0x100)) (gas - 173)
        (readSlot state message.currentTarget k)
        (accessSlot substate message.currentTarget k)) := by
  simp only [BODY, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hp
  rcases hp with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  all_goals
    -- the data word at 0x80
    step pushR 2 (0x0100 : U256)
    step dupR 0
    step dupR 3
    step Gas.sloadG hfork (cold := false) (by code_fact) (by code_fact) hck
      (by gas_ok)
    rw [getStorage_eq]
    step binR 0x04 Local.instruction_div
    step binR 0x02 Local.instruction_mul
    step dupR 3
    have hext2 : extendMemory (MEM1 ++ wordBytes (BitVec.ofNat 256 n)).size
        [((0x80 : U256), (32 : U256))] = ⟨3, 32⟩ := by
      rw [ByteArray.size_append, size_MEM1, size_wordBytes]; decide
    step Gas.mstoreG (by code_fact) (by code_fact) (by rw [hext2]; gas_ok)
    step Gas.reshapeG (m' := MEMB n (mul (div (storageAt state message.currentTarget _) 0x100) 0x100))
      (g' := gas - 128) rfl
      (by
        rw [hext2]
        exact write_end (by rw [ByteArray.size_append, size_MEM1, size_wordBytes]; rfl) _)
      (by rw [hext2]; gas_ok)
    step swapR 1
    norm
    step pushR 1 (0x20 : U256)
    step binR 0x01 instruction_add
    step swapR 1
    norm
    step pushAnyR 2
    step jumpR
    first | at_pc 2638 | at_pc 5356
    step jumpdestR
    step popR
    step popR
    step popR
    step popR
    step popR
    step dupR 1
    step jumpR
    exact restate (by decide) rfl rfl (by gas_ok) rfl rfl

/-! ## Words and reads of the return block -/

/-- The word `w` with its low `32 - n` bytes cleared: its first `n` bytes, then zeros. -/
def topBytes (w : U256) (n : Nat) : U256 :=
  BitVec.ofNat 256 (w.toNat / 2 ^ (8 * (32 - n)) * 2 ^ (8 * (32 - n)))

theorem maskWord {n : Nat} (h1 : 1 ≤ n) (h31 : n ≤ 31) :
    sub (exp 256 (sub 32 (BitVec.ofNat 256 n))) 1 = BitVec.ofNat 256 (2 ^ (8 * (32 - n)) - 1) := by
  have hs : sub 32 (BitVec.ofNat 256 n) = BitVec.ofNat 256 (32 - n) := by
    apply BitVec.eq_of_toNat_eq
    simp [sub, BitVec.toNat_sub]
    omega
  have hp : (2 : Nat) ^ (8 * (32 - n)) < 2 ^ 256 := Nat.pow_lt_pow_right (by decide) (by omega)
  have hp1 : 1 ≤ (2 : Nat) ^ (8 * (32 - n)) := Nat.one_le_two_pow
  rw [hs]
  apply BitVec.eq_of_toNat_eq
  simp only [sub, Evm.exp, BitVec.toNat_sub, powMod_eq, BitVec.toNat_ofNat]
  rw [show (BitVec.toNat (256 : U256)) = 2 ^ 8 from rfl,
    show (BitVec.toNat (1 : U256)) = 1 from rfl,
    Nat.mod_eq_of_lt (show 32 - n < 2 ^ 256 by omega), ← Nat.pow_mul]
  generalize (2 : Nat) ^ (8 * (32 - n)) = P at hp hp1 ⊢
  omega

theorem strWord_eq (w : U256) {n : Nat} (h1 : 1 ≤ n) (h31 : n ≤ 31) :
    bitwiseAnd (bitwiseNot (BitVec.ofNat 256 (2 ^ (8 * (32 - n)) - 1))) (mul (div w 256) 256) =
      topBytes w n := by
  have hd : mul (div w 256) 256 = BitVec.ofNat 256 (w.toNat / 2 ^ 8 * 2 ^ 8) := by
    apply BitVec.eq_of_toNat_eq
    simp [mul, div, BitVec.toNat_mul]
  rw [hd]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [bitwiseAnd, bitwiseNot, topBytes, BitVec.getLsbD_and, BitVec.getLsbD_not,
    BitVec.getLsbD_ofNat,
    Nat.testBit_mul_two_pow, Nat.testBit_div_two_pow, Nat.testBit_two_pow_sub_one, hi]
  by_cases h : 8 * (32 - n) ≤ i
  · have h8 : 8 ≤ i := by omega
    simp [h, h8, Nat.not_lt.mpr h, Nat.sub_add_cancel h8, Nat.sub_add_cancel h]
  · simp [h, Nat.lt_of_not_le h]

theorem expBytes {n : Nat} (h1 : 1 ≤ n) (h31 : n ≤ 31) :
    exponentBytes (BitVec.ofNat 256 (32 - n)) = 1 := by
  have key : ∀ m, m < 32 → 1 ≤ m → exponentBytes (BitVec.ofNat 256 m) = 1 := by decide +kernel
  exact key _ (by omega) (by omega)

/-- GENERIC: a read within the first part of an appended memory. -/
theorem read_left {A B : ByteArray} {s k : Nat} (h : s + k ≤ A.size) :
    memoryReadBytes (A ++ B) s k = memoryReadBytes A s k := by
  have h' : s + k ≤ (A ++ B).size := by rw [ByteArray.size_append]; omega
  apply EthLib.Base.eq_of_byteAt
  · rw [size_memoryReadBytes h', size_memoryReadBytes h]
  · intro i
    rw [byteAt_memoryReadBytes h', byteAt_memoryReadBytes h, EthLib.Base.byteAt_append]
    split
    · rw [ite_eq_left (by omega)]
    · rfl

/-- GENERIC: a read of the second part of an appended memory. -/
theorem read_right {A B : ByteArray} {s : Nat} (h : A.size = s) :
    memoryReadBytes (A ++ B) s B.size = B := by
  have h' : s + B.size ≤ (A ++ B).size := by rw [ByteArray.size_append]; omega
  apply EthLib.Base.eq_of_byteAt
  · rw [size_memoryReadBytes h']
  · intro i
    rw [byteAt_memoryReadBytes h', EthLib.Base.byteAt_append]
    split
    · split
      · omega
      · congr 1; omega
    · rw [EthLib.Base.byteAt_of_size_le (by omega)]

/-- GENERIC: the word of its own 32 bytes. -/
theorem ld (v : U256) : loadWord (wordBytes v) 0 32 = v := by
  have h := loadWord_memoryWrite_wordBytes (memory := wordBytes v) (start := 0) v
    (by simp [size_wordBytes])
  rw [memoryWrite_whole rfl] at h
  have e : memoryReadBytes (wordBytes v) 0 32 = wordBytes v := by
    have := memoryReadBytes_whole (memory := wordBytes v)
    rwa [size_wordBytes] at this
  rwa [e] at h

/-! ## The return block (430 for name, 1743 for symbol) -/

/-- The memory after the body, with the offset word 0x20 at 0xa0. -/
abbrev MEMC (n : Nat) (v : U256) : ByteArray := MEMB n v ++ wordBytes 0x20

/-- Then the length at 0xc0. -/
abbrev MEMD (n : Nat) (v : U256) : ByteArray := MEMC n v ++ wordBytes (BitVec.ofNat 256 n)

/-- Then the data word copied at 0xe0 by the one round of the copy loop. -/
abbrev MEME (n : Nat) (v : U256) : ByteArray := MEMD n v ++ wordBytes v

theorem size_MEMB (n : Nat) (v : U256) : (MEMB n v).size = 160 := by
  rw [MEMB, ByteArray.size_append, ByteArray.size_append, size_MEM1, size_wordBytes,
    size_wordBytes]

theorem size_MEMC (n : Nat) (v : U256) : (MEMC n v).size = 192 := by
  rw [MEMC, ByteArray.size_append, size_MEMB, size_wordBytes]

theorem size_MEMD (n : Nat) (v : U256) : (MEMD n v).size = 224 := by
  rw [MEMD, ByteArray.size_append, size_MEMC, size_wordBytes]

theorem size_MEME (n : Nat) (v : U256) : (MEME n v).size = 256 := by
  rw [MEME, ByteArray.size_append, size_MEMD, size_wordBytes]

/-- Sizes of the memories of the string getters. -/
macro "sz" : tactic => `(tactic| (simp only [ByteArray.size_append, size_wordBytes, size_MEM1,
  size_MEMB, size_MEMC, size_MEMD, size_MEME] <;> decide))

theorem ptr_MEMB (n : Nat) (v : U256) :
    loadWord (memoryReadBytes (MEMB n v) (0x40 : U256).toNat 32) 0 32 = 0xa0 := by
  rw [MEMB, read_left (by sz), read_left (by sz)]
  exact mload_MEM1

theorem len_MEMC (n : Nat) (v : U256) :
    loadWord (memoryReadBytes (MEMC n v) (0x60 : U256).toNat 32) 0 32 = BitVec.ofNat 256 n := by
  rw [MEMC, MEMB, read_left (by sz), read_left (by sz)]
  have h := read_right (A := MEM1) (B := wordBytes (BitVec.ofNat 256 n)) (s := 96) size_MEM1
  rw [size_wordBytes] at h
  rw [show (0x60 : U256).toNat = 96 from rfl, h, ld]

theorem len_MEMD (n : Nat) (v : U256) :
    loadWord (memoryReadBytes (MEMD n v) (0x60 : U256).toNat 32) 0 32 = BitVec.ofNat 256 n := by
  rw [MEMD, read_left (by sz)]
  exact len_MEMC n v

theorem data_MEMD (n : Nat) (v : U256) :
    loadWord (memoryReadBytes (MEMD n v) (0x80 : U256).toNat 32) 0 32 = v := by
  rw [MEMD, MEMC, read_left (by sz), read_left (by sz), MEMB]
  have h := read_right (A := MEM1 ++ wordBytes (BitVec.ofNat 256 n)) (B := wordBytes v) (s := 128)
    (by sz)
  rw [size_wordBytes] at h
  rw [show (0x80 : U256).toNat = 128 from rfl, h, ld]

theorem copy_MEME (n : Nat) (v : U256) :
    loadWord (memoryReadBytes (MEME n v) (0xe0 : U256).toNat 32) 0 32 = v := by
  have h := read_right (A := MEMD n v) (B := wordBytes v) (s := 224) (size_MEMD n v)
  rw [size_wordBytes] at h
  rw [MEME, show (0xe0 : U256).toNat = 224 from rfl, h, ld]

/-- The bytes returned: the words at 0xa0 and 0xc0, then the masked data word at 0xe0. -/
theorem out_MEME (n : Nat) (v u : U256) :
    memoryReadBytes (memoryWrite (MEME n v) 224 (wordBytes u)) 160 96 =
      wordBytes 0x20 ++ wordBytes (BitVec.ofNat 256 n) ++ wordBytes u := by
  have h := memoryReadBytes_memoryWrite_eq_append (memory := MEME n v) (value := wordBytes u)
    (s := 160) (k := 64) (by sz)
  rw [size_wordBytes] at h
  rw [h, MEME, read_left (by sz), MEMD, MEMC, ByteArray.append_assoc]
  have h2 := read_right (A := MEMB n v) (B := wordBytes 0x20 ++ wordBytes (BitVec.ofNat 256 n))
    (s := 160) (size_MEMB n v)
  rw [ByteArray.size_append, size_wordBytes, size_wordBytes] at h2
  rw [h2]

theorem ptr_MEMF (n : Nat) (v u : U256) :
    loadWord (memoryReadBytes (memoryWrite (MEME n v) 224 (wordBytes u)) (0x40 : U256).toNat 32)
      0 32 = 0xa0 := by
  rw [memoryReadBytes_memoryWrite_of_disjoint (by sz) (.inl (by decide)), MEME, MEMD, MEMC,
    read_left (by sz), read_left (by sz), read_left (by sz)]
  exact ptr_MEMB n v

theorem lt0_n {n : Nat} (h1 : 1 ≤ n) (h31 : n ≤ 31) :
    isZero (lessThan 0 (BitVec.ofNat 256 n)) = 0 := by
  unfold lessThan
  rw [ite_eq_left (by simp [Nat.mod_eq_of_lt (show n < 2 ^ 256 by omega)]; omega)]
  decide

theorem lt32_n {n : Nat} (h31 : n ≤ 31) : isZero (lessThan 32 (BitVec.ofNat 256 n)) ≠ 0 := by
  unfold lessThan
  rw [ite_eq_right (by simp [Nat.mod_eq_of_lt (show n < 2 ^ 256 by omega)]; omega)]
  decide

theorem and31_n {n : Nat} (h31 : n ≤ 31) :
    bitwiseAnd 31 (BitVec.ofNat 256 n) = BitVec.ofNat 256 n := by
  apply BitVec.eq_of_toNat_eq
  simp only [bitwiseAnd, BitVec.toNat_and, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show n < 2 ^ 256 by omega),
    show (BitVec.toNat (31 : U256)) = 2 ^ 5 - 1 from rfl, Nat.and_comm,
    Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem addSub_n (n : Nat) :
    sub (add (BitVec.ofNat 256 n) 0xe0) (BitVec.ofNat 256 n) = 0xe0 := by
  simp only [sub, add]
  rw [BitVec.add_comm]
  exact BitVec.add_sub_cancel ..

theorem subN {n : Nat} (h31 : n ≤ 31) :
    sub 32 (BitVec.ofNat 256 n) = BitVec.ofNat 256 (32 - n) := by
  apply BitVec.eq_of_toNat_eq
  simp [sub, BitVec.toNat_sub]
  omega

/-- The return blocks. -/
abbrev RETS : List Nat := [430, 1743]

/-- From the return block to the head of the copy loop: the offset 0x20 written at 0xa0, the
length at 0xc0. -/
theorem retA {r : Nat} (hp : r ∈ RETS) {n : Nat} {v : U256} {y x : U256} {gas : Nat}
    (hg : 99 ≤ gas) :
    Gas.HoareG fork (At CODE message r [0x60, y, x] (MEMB n v) gas state substate)
      (At CODE message (r + 37) [0, 0x80, 0xe0, BitVec.ofNat 256 n, BitVec.ofNat 256 n, 0x80, 0xe0,
        0xa0, 0xa0, 0x60, y, x] (MEMD n v) (gas - 99) state substate) := by
  have e0 : extendMemory (MEMB n v).size [((0x40 : U256), (32 : U256))] = ⟨0, 0⟩ := by
    rw [size_MEMB]; decide
  have e1 : extendMemory (MEMB n v).size [((0xa0 : U256), (32 : U256))] = ⟨3, 32⟩ := by
    rw [size_MEMB]; decide
  have e2 : extendMemory (MEMC n v).size [((0x60 : U256), (32 : U256))] = ⟨0, 0⟩ := by
    rw [size_MEMC]; decide
  have e3 : extendMemory (MEMC n v).size [((0xc0 : U256), (32 : U256))] = ⟨3, 32⟩ := by
    rw [size_MEMC]; decide
  have e4 : extendMemory (MEMD n v).size [((0x60 : U256), (32 : U256))] = ⟨0, 0⟩ := by
    rw [size_MEMD]; decide
  simp only [RETS, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl
  all_goals
    step jumpdestR
    step pushR 1 (0x40 : U256)
    step Gas.mloadG (by code_fact) (by code_fact) (by rw [e0]; gas_ok)
    step Gas.reshapeG (s' := [0xa0, 0x60, y, x]) (m' := MEMB n v) (g' := gas - 7)
      (by rw [e0, memoryExtend_zero, ptr_MEMB]) (by rw [e0, memoryExtend_zero]) (by rw [e0]; gas_ok)
    step dupR 0
    step dupR 0
    step pushR 1 (0x20 : U256)
    step binR 0x01 instruction_add
    step Gas.reshapeG (s' := [0xc0, 0xa0, 0xa0, 0x60, y, x]) rfl rfl rfl
    step dupR 2
    step dupR 1
    step binR 0x03 instruction_sub
    step Gas.reshapeG (s' := [0x20, 0xc0, 0xa0, 0xa0, 0x60, y, x]) rfl rfl rfl
    step dupR 2
    step Gas.mstoreG (by code_fact) (by code_fact) (by rw [e1]; gas_ok)
    step Gas.reshapeG (m' := MEMC n v) (g' := gas - 37) rfl
      (by rw [e1]; exact write_end (by rw [size_MEMB]; rfl) _) (by rw [e1]; gas_ok)
    step dupR 3
    step dupR 1
    step dupR 1
    step Gas.mloadG (by code_fact) (by code_fact) (by rw [e2]; gas_ok)
    step Gas.reshapeG (s' := [BitVec.ofNat 256 n, 0xc0, 0x60, 0xc0, 0xa0, 0xa0, 0x60, y, x])
      (m' := MEMC n v) (g' := gas - 49)
      (by rw [e2, memoryExtend_zero, len_MEMC]) (by rw [e2, memoryExtend_zero]) (by rw [e2]; gas_ok)
    step dupR 1
    step Gas.mstoreG (by code_fact) (by code_fact) (by rw [e3]; gas_ok)
    step Gas.reshapeG (m' := MEMD n v) (g' := gas - 58) rfl
      (by rw [e3]; exact write_end (by rw [size_MEMC]; rfl) _) (by rw [e3]; gas_ok)
    step pushR 1 (0x20 : U256)
    step binR 0x01 instruction_add
    step Gas.reshapeG (s' := [0xe0, 0x60, 0xc0, 0xa0, 0xa0, 0x60, y, x]) rfl rfl rfl
    step swapR 1
    step Gas.reshapeG (s' := [0xc0, 0x60, 0xe0, 0xa0, 0xa0, 0x60, y, x]) rfl rfl rfl
    step popR
    step dupR 0
    step Gas.mloadG (by code_fact) (by code_fact) (by rw [e4]; gas_ok)
    step Gas.reshapeG (s' := [BitVec.ofNat 256 n, 0x60, 0xe0, 0xa0, 0xa0, 0x60, y, x])
      (m' := MEMD n v) (g' := gas - 75)
      (by rw [e4, memoryExtend_zero, len_MEMD]) (by rw [e4, memoryExtend_zero]) (by rw [e4]; gas_ok)
    step swapR 0
    norm
    step pushR 1 (0x20 : U256)
    step binR 0x01 instruction_add
    step Gas.reshapeG (s' := [0x80, BitVec.ofNat 256 n, 0xe0, 0xa0, 0xa0, 0x60, y, x]) rfl rfl rfl
    step swapR 0
    norm
    step dupR 0
    step dupR 3
    step dupR 3
    step pushR 1 (0 : U256)
    exact restate (by decide) rfl rfl (by gas_ok) rfl rfl

/-- One round of the copy loop: the data word at 0x80 copied to 0xe0; the counter becomes 32. -/
theorem retL {r : Nat} (hp : r ∈ RETS) {n : Nat} (h1 : 1 ≤ n) (h31 : n ≤ 31) {v : U256}
    {y x : U256} {gas : Nat} (hg : 78 ≤ gas) :
    Gas.HoareG fork (At CODE message (r + 37) [0, 0x80, 0xe0, BitVec.ofNat 256 n, BitVec.ofNat 256 n,
        0x80, 0xe0, 0xa0, 0xa0, 0x60, y, x] (MEMD n v) gas state substate)
      (At CODE message (r + 37) [0x20, 0x80, 0xe0, BitVec.ofNat 256 n, BitVec.ofNat 256 n, 0x80,
        0xe0, 0xa0, 0xa0, 0x60, y, x] (MEME n v) (gas - 78) state substate) := by
  have e0 : extendMemory (MEMD n v).size [((0x80 : U256), (32 : U256))] = ⟨0, 0⟩ := by
    rw [size_MEMD]; decide
  have e1 : extendMemory (MEMD n v).size [((0xe0 : U256), (32 : U256))] = ⟨3, 32⟩ := by
    rw [size_MEMD]; decide
  simp only [RETS, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl
  all_goals
    step jumpdestR
    step dupR 3
    step dupR 1
    step binR 0x10 Local.instruction_lt
    step unR 0x15 instruction_iszero
    step pushAnyR 2
    step jumpi0R (lt0_n h1 h31)
    step dupR 0
    step dupR 2
    step binR 0x01 instruction_add
    step Gas.reshapeG (s' := [0x80, 0, 0x80, 0xe0, BitVec.ofNat 256 n, BitVec.ofNat 256 n, 0x80, 0xe0,
      0xa0, 0xa0, 0x60, y, x]) rfl rfl rfl
    step Gas.mloadG (by code_fact) (by code_fact) (by rw [e0]; gas_ok)
    step Gas.reshapeG (s' := [v, 0, 0x80, 0xe0, BitVec.ofNat 256 n, BitVec.ofNat 256 n, 0x80, 0xe0,
      0xa0, 0xa0, 0x60, y, x]) (m' := MEMD n v) (g' := gas - 38)
      (by rw [e0, memoryExtend_zero, data_MEMD]) (by rw [e0, memoryExtend_zero])
      (by rw [e0]; gas_ok)
    step dupR 1
    step dupR 4
    step binR 0x01 instruction_add
    step Gas.reshapeG (s' := [0xe0, v, 0, 0x80, 0xe0, BitVec.ofNat 256 n, BitVec.ofNat 256 n, 0x80, 0xe0,
      0xa0, 0xa0, 0x60, y, x]) rfl rfl rfl
    step Gas.mstoreG (by code_fact) (by code_fact) (by rw [e1]; gas_ok)
    step Gas.reshapeG (m' := MEME n v) (g' := gas - 53) rfl
      (by rw [e1]; exact write_end (by rw [size_MEMD]; rfl) _) (by rw [e1]; gas_ok)
    step pushR 1 (0x20 : U256)
    step dupR 1
    step binR 0x01 instruction_add
    step Gas.reshapeG (s' := [0x20, 0, 0x80, 0xe0, BitVec.ofNat 256 n, BitVec.ofNat 256 n, 0x80, 0xe0,
      0xa0, 0xa0, 0x60, y, x]) rfl rfl rfl
    step swapR 0
    step Gas.reshapeG (s' := [0, 0x20, 0x80, 0xe0, BitVec.ofNat 256 n, BitVec.ofNat 256 n, 0x80, 0xe0,
      0xa0, 0xa0, 0x60, y, x]) rfl rfl rfl
    step popR
    step pushAnyR 2
    step jumpR
    exact restate (by decide) rfl rfl (by gas_ok) rfl rfl

/-- The loop test fails (32 is not below the length), the copy loop ends; the end of the data
`0xe0 + n` and the length's low five bits (`n`, not 0) select the padding branch. -/
theorem retE1 {r : Nat} (hp : r ∈ RETS) {n : Nat} (h1 : 1 ≤ n) (h31 : n ≤ 31) {M : ByteArray}
    {y x : U256} {gas : Nat} (hg : 77 ≤ gas) :
    Gas.HoareG fork (At CODE message (r + 37) [0x20, 0x80, 0xe0, BitVec.ofNat 256 n,
        BitVec.ofNat 256 n, 0x80, 0xe0, 0xa0, 0xa0, 0x60, y, x] M gas state substate)
      (At CODE message (r + 84) [BitVec.ofNat 256 n, add (BitVec.ofNat 256 n) 0xe0, 0xa0, 0xa0,
        0x60, y, x] M (gas - 77) state substate) := by
  simp only [RETS, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl
  all_goals
    step jumpdestR
    step dupR 3
    step dupR 1
    step binR 0x10 Local.instruction_lt
    step unR 0x15 instruction_iszero
    step pushAnyR 2
    step jumpiR (lt32_n h31)
    first | at_pc 494 | at_pc 1807
    step jumpdestR
    step popR
    step popR
    step popR
    step popR
    step swapR 0
    norm
    step popR
    step swapR 0
    norm
    step dupR 1
    step binR 0x01 instruction_add
    step swapR 0
    norm
    step pushR 1 (0x1f : U256)
    step binR 0x16 Local.instruction_and
    rw [and31_n h31]
    step dupR 0
    step unR 0x15 instruction_iszero
    step pushAnyR 2
    step jumpi0R (isZero_n h1 h31)
    exact restate (by decide) rfl rfl (by gas_ok) rfl rfl

/-- The masked data word that the code writes back at 0xe0. -/
abbrev maskedWord (n : Nat) (v : U256) : U256 :=
  bitwiseAnd (bitwiseNot (sub (exp 256 (sub 32 (BitVec.ofNat 256 n))) 1)) v

theorem expBytes' {n : Nat} (h1 : 1 ≤ n) (h31 : n ≤ 31) :
    exponentBytes (sub 32 (BitVec.ofNat 256 n)) = 1 := by
  rw [subN h31]; exact expBytes h1 h31

/-- The padding branch: the data word at 0xe0 masked to its first `n` bytes, then RETURN of the
96 bytes from 0xa0. -/
theorem retE2 (hfork : .berlin ≤ fork) {r : Nat} (hp : r ∈ RETS) {n : Nat} (h1 : 1 ≤ n)
    (h31 : n ≤ 31) {v : U256} {y x : U256} {gas : Nat} (hg : 146 ≤ gas) :
    Gas.SpecG fork (At CODE message (r + 84) [BitVec.ofNat 256 n, add (BitVec.ofNat 256 n) 0xe0, 0xa0,
        0xa0, 0x60, y, x] (MEME n v) gas state substate)
      (Halted false (wordBytes 0x20 ++ wordBytes (BitVec.ofNat 256 n) ++
        wordBytes (maskedWord n v)) (gas - 146) state substate) := by
  have e0 : extendMemory (MEME n v).size [((0xe0 : U256), (32 : U256))] = ⟨0, 0⟩ := by
    rw [size_MEME]; decide
  have hF : (memoryWrite (MEME n v) 224 (wordBytes (maskedWord n v))).size = 256 := by
    rw [size_memoryWrite (by sz), size_MEME]
  have e1 : extendMemory (memoryWrite (MEME n v) 224 (wordBytes (maskedWord n v))).size
      [((0x40 : U256), (32 : U256))] = ⟨0, 0⟩ := by
    rw [hF]; decide
  have e2 : extendMemory (memoryWrite (MEME n v) 224 (wordBytes (maskedWord n v))).size
      [((0xa0 : U256), (0x60 : U256))] = ⟨0, 0⟩ := by
    rw [hF]; decide
  simp only [RETS, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl
  all_goals
    step dupR 0
    step dupR 2
    step binR 0x03 instruction_sub
    rw [addSub_n]
    step dupR 0
    step Gas.mloadG (by code_fact) (by code_fact) (by rw [e0]; gas_ok)
    step Gas.reshapeG (s' := [v, 0xe0, BitVec.ofNat 256 n, add (BitVec.ofNat 256 n) 0xe0, 0xa0, 0xa0,
      0x60, y, x]) (m' := MEME n v) (g' := gas - 15)
      (by rw [e0, memoryExtend_zero, copy_MEME]) (by rw [e0, memoryExtend_zero])
      (by rw [e0]; gas_ok)
    step pushR 1 (1 : U256)
    step dupR 3
    step pushR 1 (0x20 : U256)
    step binR 0x03 instruction_sub
    step pushR 2 (0x0100 : U256)
    step Gas.expLG (Nat.le_trans (by decide) hfork) (by code_fact) (by code_fact)
      (by rw [expBytes' h1 h31]; gas_ok)
    rw [expBytes' h1 h31]
    step binR 0x03 instruction_sub
    step unR 0x19 Local.instruction_not
    step binR 0x16 Local.instruction_and
    step dupR 1
    step Gas.mstoreG (by code_fact) (by code_fact) (by rw [e0]; gas_ok)
    step Gas.reshapeG (s' := [0xe0, BitVec.ofNat 256 n, add (BitVec.ofNat 256 n) 0xe0, 0xa0, 0xa0,
      0x60, y, x]) (m' := memoryWrite (MEME n v) 224 (wordBytes (maskedWord n v)))
      (g' := gas - 105) rfl (by rw [e0, memoryExtend_zero]; rfl) (by rw [e0]; gas_ok)
    step pushR 1 (0x20 : U256)
    step binR 0x01 instruction_add
    step swapR 1
    step Gas.reshapeG (s' := [add (BitVec.ofNat 256 n) 0xe0, BitVec.ofNat 256 n, 0x100, 0xa0, 0xa0,
      0x60, y, x]) rfl rfl rfl
    step popR
    step jumpdestR
    step popR
    step swapR 2
    step Gas.reshapeG (s' := [0x60, 0xa0, 0xa0, 0x100, y, x]) rfl rfl rfl
    step popR
    step popR
    step popR
    step pushR 1 (0x40 : U256)
    step Gas.mloadG (by code_fact) (by code_fact) (by rw [e1]; gas_ok)
    step Gas.reshapeG (s' := [0xa0, 0x100, y, x])
      (m' := memoryWrite (MEME n v) 224 (wordBytes (maskedWord n v))) (g' := gas - 134)
      (by rw [e1, memoryExtend_zero, ptr_MEMF]) (by rw [e1, memoryExtend_zero]) (by rw [e1]; gas_ok)
    step dupR 0
    step swapR 1
    step Gas.reshapeG (s' := [0x100, 0xa0, 0xa0, y, x]) rfl rfl rfl
    step binR 0x03 instruction_sub
    step swapR 0
    step Gas.reshapeG (s' := [0xa0, 0x60, y, x]) rfl rfl rfl
    refine (Gas.returnG (by code_fact) (by code_fact) (by rw [e2]; gas_ok)).consequence
      (fun _ h => h) ?_
    rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
    refine ⟨hr, he, ?_, ?_, hs, hss⟩
    · rw [ho, e2, memoryExtend_zero]
      exact out_MEME n v _
    · rw [hgas, e2]
      gas_ok

/-! ## The specifications -/

/-- The masked word is the slot word with its low `32 - n` bytes cleared. -/
theorem maskedWord_eq (w : U256) {n : Nat} (h1 : 1 ≤ n) (h31 : n ≤ 31) :
    maskedWord n (mul (div w 0x100) 0x100) = topBytes w n := by
  rw [maskedWord, maskWord h1 h31]
  exact strWord_eq w h1 h31

/-- The string getters `(sel, t, e, r, b, k)`: selector, its table key number, entry, return
block, body, slot. name() reads slot 7, symbol() slot 8. -/
abbrev STR_GETTERS : List (Nat × Nat × Nat × Nat × Nat × U256) :=
  [(0x06fdde03, 1, 411, 430, 2488, 7), (0x95d89b41, 21, 1724, 1743, 5206, 8)]

/-- The specification of `name()` and `symbol()` for a string of 1 to 31 bytes stored in the
short form (Solidity stores such a string in one slot: the bytes from the top, the low byte
`2 * n`). The run returns the ABI encoding of the string: the word 0x20 (the offset), the word
`n` (the length), then one word with the first `n` bytes of the slot word followed by zeros
(`topBytes`). The slot is read three times (the first read at the price of `ck`, then warm). -/
theorem spec_str (hfork : .berlin ≤ fork) {sel t e r b : Nat} {k : U256}
    (hp : (sel, t, e, r, b, k) ∈ STR_GETTERS) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = sel)
    (hv : message.value = 0) {n : Nat}
    (hn : (storageAt state message.currentTarget k).toNat % 256 = 2 * n) (h1 : 1 ≤ n)
    (h31 : n ≤ 31) {ck : Bool} (hck : coldIn substate message.currentTarget k = ck) {gas : Nat}
    (hg : 988 + 22 * t + slotCost ck ≤ gas) :
    Gas.SpecG fork (At CODE message 0 [] .empty gas state substate)
      (Halted false (wordBytes 0x20 ++ wordBytes (BitVec.ofNat 256 n) ++
          wordBytes (topBytes (storageAt state message.currentTarget k) n))
        (gas - (988 + 22 * t + slotCost ck))
        (readSlot state message.currentTarget k)
        (accessSlot substate message.currentTarget k)) := by
  have hpe : (e, r, b, k) ∈ STR := by
    simp only [STR_GETTERS, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hp
    rcases hp with ⟨-, -, rfl, rfl, rfl, rfl⟩ | ⟨-, -, rfl, rfl, rfl, rfl⟩ <;> decide
  have hpb : (b, k, r) ∈ BODY := by
    simp only [STR_GETTERS, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hp
    rcases hp with ⟨-, -, -, rfl, rfl, rfl⟩ | ⟨-, -, -, rfl, rfl, rfl⟩ <;> decide
  have hpr : r ∈ RETS := by
    simp only [STR_GETTERS, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hp
    rcases hp with ⟨-, -, -, rfl, -, -⟩ | ⟨-, -, -, rfl, -, -⟩ <;> decide
  have ht : tested (BitVec.ofNat 256 sel) ENTRIES = t ∧
      branch (BitVec.ofNat 256 sel) 54 (entrySize 4 2) ENTRIES = e := by
    simp only [STR_GETTERS, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hp
    rcases hp with ⟨rfl, rfl, rfl, -, -, -⟩ | ⟨rfl, rfl, rfl, -, -, -⟩ <;> decide
  have hc2 : coldIn (accessSlot substate message.currentTarget k) message.currentTarget k =
      false := coldIn_accessSlot_self _ _ _
  have hn2 : (storageAt (readSlot state message.currentTarget k) message.currentTarget k).toNat %
      256 = 2 * n := by rw [storageAt_readSlot]; exact hn
  refine Gas.SpecG.seq ((toEntry ht hsize hsize' hsel (by omega)).seq
    ((entryS hpe hv (by omega)).seq (body1 hpb hfork hn h1 h31 hck (by omega)))) ?_
  refine Gas.SpecG.seq (body2 hpb hfork hn2 h1 h31 hc2 (by omega)) ?_
  rw [readSlot_readSlot, accessSlot_accessSlot]
  refine Gas.SpecG.seq (body3 hpb hfork hc2 (by omega)) ?_
  rw [readSlot_readSlot, accessSlot_accessSlot, storageAt_readSlot]
  refine Gas.SpecG.seq (retA hpr (by omega)) ?_
  refine Gas.SpecG.seq (retL hpr h1 h31 (by omega)) ?_
  refine Gas.SpecG.seq (retE1 hpr h1 h31 (by omega)) ?_
  refine (retE2 hfork hpr h1 h31 (by omega)).consequence (fun _ h => h) ?_
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  refine ⟨hr, he, ?_, ?_, hs, hss⟩
  · rw [ho, maskedWord_eq _ h1 h31]
  · rw [hgas]
    gas_ok

/-- `name()` (selector 0x06fdde03, slot 7) for a short string of `n` bytes, 1 ≤ n ≤ 31. -/
theorem spec_name (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x06fdde03)
    (hv : message.value = 0) {n : Nat}
    (hn : (storageAt state message.currentTarget 7).toNat % 256 = 2 * n) (h1 : 1 ≤ n)
    (h31 : n ≤ 31) {c : Bool} (hc : coldIn substate message.currentTarget 7 = c) {gas : Nat}
    (hg : 1010 + slotCost c ≤ gas) :
    Gas.SpecG fork (At CODE message 0 [] .empty gas state substate)
      (Halted false (wordBytes 0x20 ++ wordBytes (BitVec.ofNat 256 n) ++
          wordBytes (topBytes (storageAt state message.currentTarget 7) n))
        (gas - (1010 + slotCost c))
        (readSlot state message.currentTarget 7) (accessSlot substate message.currentTarget 7)) :=
  spec_str (t := 1) (e := 411) (r := 430) (b := 2488) hfork (by decide) hsize hsize' hsel hv hn h1
    h31 hc hg

/-- `symbol()` (selector 0x95d89b41, slot 8) for a short string of `n` bytes, 1 ≤ n ≤ 31. -/
theorem spec_symbol (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x95d89b41)
    (hv : message.value = 0) {n : Nat}
    (hn : (storageAt state message.currentTarget 8).toNat % 256 = 2 * n) (h1 : 1 ≤ n)
    (h31 : n ≤ 31) {c : Bool} (hc : coldIn substate message.currentTarget 8 = c) {gas : Nat}
    (hg : 1450 + slotCost c ≤ gas) :
    Gas.SpecG fork (At CODE message 0 [] .empty gas state substate)
      (Halted false (wordBytes 0x20 ++ wordBytes (BitVec.ofNat 256 n) ++
          wordBytes (topBytes (storageAt state message.currentTarget 8) n))
        (gas - (1450 + slotCost c))
        (readSlot state message.currentTarget 8) (accessSlot substate message.currentTarget 8)) :=
  spec_str (t := 21) (e := 1724) (r := 1743) (b := 5206) hfork (by decide) hsize hsize' hsel hv hn
    h1 h31 hc hg

/-! ## The strings of the deployed contract

The slot words of "Tether USD" (slot 7) and "USDT" (slot 8) in Solidity's short form: the bytes
from the top, the low byte twice the length. When the slots hold them, `name()` and `symbol()`
return the ABI encoding of the string, byte for byte. -/

/-- "Tether USD" (10 bytes) in the short form. -/
def NAME_WORD : U256 := 0x5465746865722055534400000000000000000000000000000000000000000014

/-- "USDT" (4 bytes) in the short form. -/
def SYMBOL_WORD : U256 := 0x5553445400000000000000000000000000000000000000000000000000000008

theorem name_bytes : wordBytes 0x20 ++ wordBytes (BitVec.ofNat 256 10) ++
    wordBytes (topBytes NAME_WORD 10) =
      wordBytes 0x20 ++ wordBytes 10 ++ ("Tether USD".toUTF8 ++ ⟨Array.replicate 22 0⟩) := by
  decide +kernel

theorem symbol_bytes : wordBytes 0x20 ++ wordBytes (BitVec.ofNat 256 4) ++
    wordBytes (topBytes SYMBOL_WORD 4) =
      wordBytes 0x20 ++ wordBytes 4 ++ ("USDT".toUTF8 ++ ⟨Array.replicate 28 0⟩) := by
  decide +kernel

/-- With slot 7 holding "Tether USD", `name()` returns the word 0x20, the word 10, and the 10
bytes of "Tether USD" padded with 22 zero bytes. -/
theorem spec_name_tether (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x06fdde03)
    (hv : message.value = 0) (hw : storageAt state message.currentTarget 7 = NAME_WORD)
    {c : Bool} (hc : coldIn substate message.currentTarget 7 = c) {gas : Nat}
    (hg : 1010 + slotCost c ≤ gas) :
    Gas.SpecG fork (At CODE message 0 [] .empty gas state substate)
      (Halted false (wordBytes 0x20 ++ wordBytes 10 ++
          ("Tether USD".toUTF8 ++ ⟨Array.replicate 22 0⟩))
        (gas - (1010 + slotCost c))
        (readSlot state message.currentTarget 7)
        (accessSlot substate message.currentTarget 7)) := by
  have h := spec_name (n := 10) hfork hsize hsize' hsel hv (by rw [hw]; decide) (by decide)
    (by decide) hc hg
  rwa [hw, name_bytes] at h

/-- With slot 8 holding "USDT", `symbol()` returns the word 0x20, the word 4, and the 4 bytes of
"USDT" padded with 28 zero bytes. -/
theorem spec_symbol_usdt (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x95d89b41)
    (hv : message.value = 0) (hw : storageAt state message.currentTarget 8 = SYMBOL_WORD)
    {c : Bool} (hc : coldIn substate message.currentTarget 8 = c) {gas : Nat}
    (hg : 1450 + slotCost c ≤ gas) :
    Gas.SpecG fork (At CODE message 0 [] .empty gas state substate)
      (Halted false (wordBytes 0x20 ++ wordBytes 4 ++ ("USDT".toUTF8 ++ ⟨Array.replicate 28 0⟩))
        (gas - (1450 + slotCost c))
        (readSlot state message.currentTarget 8)
        (accessSlot substate message.currentTarget 8)) := by
  have h := spec_symbol (n := 4) hfork hsize hsize' hsel hv (by rw [hw]; decide) (by decide)
    (by decide) hc hg
  rwa [hw, symbol_bytes] at h

/-! ## For the interpreter loop -/

/-- `spec_name` for the interpreter loop `runFrame`. -/
theorem runFrame_name (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x06fdde03)
    (hv : message.value = 0) {n : Nat}
    (hn : (storageAt state message.currentTarget 7).toNat % 256 = 2 * n) (h1 : 1 ≤ n)
    (h31 : n ≤ 31) {c : Bool} (hc : coldIn substate message.currentTarget 7 = c) {gas : Nat}
    (hg : 1010 + slotCost c ≤ gas)
    {bound : Nat} {runChild : MessageRunner fork Nat bound} {evm : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    ∃ stopped, runFrame (step fork) (step_decreases fork) bound runChild evm within =
      .ok stopped ∧
      (Halted false (wordBytes 0x20 ++ wordBytes (BitVec.ofNat 256 n) ++
          wordBytes (topBytes (storageAt state message.currentTarget 7) n))
        (gas - (1010 + slotCost c))
        (readSlot state message.currentTarget 7)
        (accessSlot substate message.currentTarget 7)) stopped :=
  (spec_name hfork hsize hsize' hsel hv hn h1 h31 hc hg).runFrame start within

/-- `spec_symbol` for the interpreter loop `runFrame`. -/
theorem runFrame_symbol (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x95d89b41)
    (hv : message.value = 0) {n : Nat}
    (hn : (storageAt state message.currentTarget 8).toNat % 256 = 2 * n) (h1 : 1 ≤ n)
    (h31 : n ≤ 31) {c : Bool} (hc : coldIn substate message.currentTarget 8 = c) {gas : Nat}
    (hg : 1450 + slotCost c ≤ gas)
    {bound : Nat} {runChild : MessageRunner fork Nat bound} {evm : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    ∃ stopped, runFrame (step fork) (step_decreases fork) bound runChild evm within =
      .ok stopped ∧
      (Halted false (wordBytes 0x20 ++ wordBytes (BitVec.ofNat 256 n) ++
          wordBytes (topBytes (storageAt state message.currentTarget 8) n))
        (gas - (1450 + slotCost c))
        (readSlot state message.currentTarget 8)
        (accessSlot substate message.currentTarget 8)) stopped :=
  (spec_symbol hfork hsize hsize' hsel hv hn h1 h31 hc hg).runFrame start within

end UsdtVerify.Strings

end

section

/-!
## name() and symbol() for any string Solidity stores: the empty string and the long form

The first part of this file covers a string of 1 to 31 bytes. Here:

- the empty string (the slot word has low byte 0): the body's JUMPI at 2567 / 5285 is taken, the
  return block runs its copy loop zero times and skips the padding;
- the long form (the slot word is `2 * n + 1` with `n ≥ 32`): the body copies the
  `W = ceil(n / 32)` words of storage from slot `keccak(k)` on (loop at 2609 / 5327) to memory at
  0x80, and the return block copies them again after the offset and length words (loop at 467 /
  1780), masks the last word when `n` is not a multiple of 32, and returns `64 + 32 W` bytes.

Generic local rules (any code): `mloadIn` / `mstoreIn` (a word within a memory whose size is a
multiple of 32: no growth) and `mstoreApp` (a word written at the end: the memory is appended,
and the price is the difference of EthLib's `memoryGasCost`).
-/

namespace UsdtVerify.StringsGen

open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts
open Transfer TransferOk Owner Admin BlackList Issue Getters Strings

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate}

/-! ## Generic memory rules -/

/-- The word of a natural number. -/
abbrev wd (m : Nat) : U256 := BitVec.ofNat 256 m

abbrev mg (s : Nat) : Nat := memoryGasCost s

theorem toNat_wd {m : Nat} (h : m < 2 ^ 256) : (wd m).toNat = m := by
  simp [Nat.mod_eq_of_lt h]

theorem ceil32_le {a s : Nat} (h : a ≤ s) (hs : s % 32 = 0) : ceil32 a ≤ s := by
  unfold ceil32 WORD_BYTES; split <;> omega

theorem ext_in {s : Nat} {o : U256} (h : o.toNat + 32 ≤ s) (hs : s % 32 = 0) :
    extendMemory s [(o, (32 : U256))] = ⟨0, 0⟩ := by
  apply extendMemory_eq_zero
  intro p hp
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
  subst hp
  right
  rw [ceil32_of_mod hs]
  exact ceil32_le (by simpa using h) hs

theorem ext_app {s : Nat} {o : U256} (ho : o.toNat = s) (hs : s % 32 = 0) :
    extendMemory s [(o, (32 : U256))] = ⟨mg (s + 32) - mg s, 32⟩ := by
  have h1 : ceil32 s = s := ceil32_of_mod hs
  have h2 : ceil32 (s + 32) = s + 32 := ceil32_of_mod (by omega)
  simp only [extendMemory, ho, show (32 : U256) ≠ 0 by decide, ↓reduceIte,
    show (32 : U256).toNat = 32 from rfl, h1, h2, show ¬ (s + 32 ≤ s) by omega, Nat.add_zero,
    mg, ExtendMemory.mk.injEq]
  exact ⟨trivial, by omega⟩

variable {code : ByteArray} {pc : Nat} {gas : Nat}

/-- MLOAD of a word within memory (size a multiple of 32): no growth, 3 gas. -/
theorem mloadIn {M : ByteArray} {start : U256} {rest : List U256} (hlt : pc < code.size)
    (hbyte : code[pc] = 0x51) (hin : start.toNat + 32 ≤ M.size) (hmod : M.size % 32 = 0)
    (hg : 3 ≤ gas) :
    Gas.HoareG fork (At code message pc (start :: rest) M gas state substate)
      (At code message (pc + 1) (loadWord (memoryReadBytes M start.toNat 32) 0 32 :: rest) M
        (gas - 3) state substate) := by
  have he := ext_in hin hmod
  refine (Gas.mloadG hlt hbyte (by rw [he]; omega)).seq ?_
  exact restate rfl (by rw [he, memoryExtend_zero]) (by rw [he, memoryExtend_zero])
    (by rw [he]; rfl) rfl rfl

/-- MSTORE within memory (size a multiple of 32): no growth, 3 gas. -/
theorem mstoreIn {M : ByteArray} {start v : U256} {rest : List U256} (hlt : pc < code.size)
    (hbyte : code[pc] = 0x52) (hin : start.toNat + 32 ≤ M.size) (hmod : M.size % 32 = 0)
    (hg : 3 ≤ gas) :
    Gas.HoareG fork (At code message pc (start :: v :: rest) M gas state substate)
      (At code message (pc + 1) rest (memoryWrite M start.toNat (wordBytes v)) (gas - 3) state
        substate) := by
  have he := ext_in hin hmod
  refine (Gas.mstoreG hlt hbyte (by rw [he]; omega)).seq ?_
  exact restate rfl rfl (by rw [he, memoryExtend_zero]) (by rw [he]; rfl) rfl rfl

/-- MSTORE at the end of memory (size a multiple of 32): the word is appended, and the price is
3 plus the growth of `memoryGasCost`. -/
theorem mstoreApp {M : ByteArray} {start v : U256} {rest : List U256} (hlt : pc < code.size)
    (hbyte : code[pc] = 0x52) (hs : start.toNat = M.size) (hmod : M.size % 32 = 0)
    (hg : 3 + (mg (M.size + 32) - mg M.size) ≤ gas) :
    Gas.HoareG fork (At code message pc (start :: v :: rest) M gas state substate)
      (At code message (pc + 1) rest (M ++ wordBytes v)
        (gas - (3 + (mg (M.size + 32) - mg M.size))) state substate) := by
  have he := ext_app hs hmod
  refine (Gas.mstoreG hlt hbyte (by rw [he]; exact hg)).seq ?_
  exact restate rfl rfl (by rw [he]; exact write_end hs.symm v) (by rw [he]) rfl rfl

/-! ## Words -/

theorem add_wd (c a : Nat) : add (wd c) (wd a) = wd (a + c) := by
  apply BitVec.eq_of_toNat_eq
  simp [add, BitVec.toNat_add, Nat.add_comm]

theorem sub_wd {a b : Nat} (h : b ≤ a) : sub (wd a) (wd b) = wd (a - b) := by
  have e : wd a = wd (a - b) + wd b := by
    rw [BitVec.ofNat_add_ofNat, Nat.sub_add_cancel h]
  simp only [sub]
  rw [e, BitVec.add_sub_cancel]

theorem add20 (a : Nat) : add (0x20 : U256) (wd a) = wd (a + 32) := add_wd 32 a

theorem addw20 (a : Nat) : add (wd a) (0x20 : U256) = wd (a + 32) := by
  rw [show (0x20 : U256) = wd 32 from rfl, add_wd, Nat.add_comm]

theorem size_app (M : ByteArray) (v : U256) : (M ++ wordBytes v).size = M.size + 32 := by
  rw [ByteArray.size_append, size_wordBytes]

/-! ## The return block for any memory -/

/-- From the return block (430 / 1743) to the head of the copy loop, on a memory `Mb` of `P`
bytes with the free memory pointer `P` and the length `N` at 0x60: the offset 0x20 and the
length are appended. -/
theorem retAG {r : Nat} (hp : r ∈ RETS) {Mb : ByteArray} {P N : Nat} (hP : Mb.size = P)
    (hmod : P % 32 = 0) (h128 : 128 ≤ P) (hPb : P < 2 ^ 200)
    (hptr : loadWord (memoryReadBytes Mb 64 32) 0 32 = wd P)
    (hlen : loadWord (memoryReadBytes Mb 96 32) 0 32 = wd N) {y x : U256} {gas : Nat}
    (hg : 93 + (mg (P + 64) - mg P) ≤ gas) :
    Gas.HoareG fork (At CODE message r [0x60, y, x] Mb gas state substate)
      (At CODE message (r + 37) [0, 0x80, wd (P + 64), wd N, wd N, 0x80, wd (P + 64), wd P, wd P,
        0x60, y, x] (Mb ++ wordBytes 0x20 ++ wordBytes (wd N))
        (gas - (93 + (mg (P + 64) - mg P))) state substate) := by
  have m1 : mg P ≤ mg (P + 32) := memoryGasCost_mono (by omega)
  have m2 : mg (P + 32) ≤ mg (P + 64) := memoryGasCost_mono (by omega)
  have s1 : (Mb ++ wordBytes 0x20).size = P + 32 := by rw [size_app, hP]
  have rd1 : loadWord (memoryReadBytes (Mb ++ wordBytes 0x20) 96 32) 0 32 = wd N := by
    rw [read_left (by omega)]; exact hlen
  have rd2 : loadWord (memoryReadBytes (Mb ++ wordBytes 0x20 ++ wordBytes (wd N)) 96 32) 0 32 =
      wd N := by
    rw [read_left (by rw [s1]; omega)]; exact rd1
  have t40 : (0x40 : U256).toNat = 64 := rfl
  have t60 : (0x60 : U256).toNat = 96 := rfl
  simp only [RETS, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl
  all_goals
    step jumpdestR
    step pushR 1 (0x40 : U256)
    step mloadIn (by code_fact) (by code_fact) (by rw [hP, t40]; omega)
      (by rw [hP]; exact hmod) (by gas_ok)
    rw [show (0x40 : U256).toNat = 64 from rfl, hptr]
    step dupR 0
    step dupR 0
    step pushR 1 (0x20 : U256)
    step binR 0x01 instruction_add
    rw [add20]
    step dupR 2
    step dupR 1
    step binR 0x03 instruction_sub
    rw [sub_wd (by omega), show P + 32 - P = 32 by omega, show wd 32 = (0x20 : U256) from rfl]
    step dupR 2
    step mstoreApp (by code_fact) (by code_fact) (by rw [toNat_wd (by omega), hP])
      (by rw [hP]; exact hmod) (by rw [hP]; gas_ok)
    rw [hP]
    step dupR 3
    step dupR 1
    step dupR 1
    step mloadIn (by code_fact) (by code_fact) (by rw [s1, t60]; omega)
      (by rw [s1]; omega) (by gas_ok)
    rw [show (0x60 : U256).toNat = 96 from rfl, rd1]
    step dupR 1
    step mstoreApp (by code_fact) (by code_fact) (by rw [toNat_wd (by omega), s1])
      (by rw [s1]; omega) (by rw [s1, show P + 32 + 32 = P + 64 by omega]; gas_ok)
    rw [s1, show P + 32 + 32 = P + 64 by omega]
    step pushR 1 (0x20 : U256)
    step binR 0x01 instruction_add
    rw [add20]
    step swapR 1
    norm
    step popR
    step dupR 0
    step mloadIn (by code_fact) (by code_fact) (by rw [size_app, s1, t60]; omega)
      (by rw [size_app, s1]; omega) (by gas_ok)
    rw [show (0x60 : U256).toNat = 96 from rfl, rd2]
    step swapR 0
    norm
    step pushR 1 (0x20 : U256)
    step binR 0x01 instruction_add
    step swapR 0
    norm
    step dupR 0
    step dupR 3
    step dupR 3
    step pushR 1 (0 : U256)
    exact restate (by decide) (by simp only [show P + 32 + 32 = P + 64 by omega]; rfl) rfl
      (by gas_ok) rfl rfl

/-! ## The copy loop of the return block -/

/-- The words `f 0, ..., f (j - 1)`, 32 bytes each. -/
def cat (f : Nat → U256) : Nat → ByteArray
  | 0 => .empty
  | j + 1 => cat f j ++ wordBytes (f j)

theorem size_cat (f : Nat → U256) (j : Nat) : (cat f j).size = 32 * j := by
  induction j with
  | zero => rfl
  | succ j ih => rw [cat, size_app, ih]; omega

theorem isZero_lt {a b : Nat} (h : a < b) (hb : b < 2 ^ 256) : isZero (lessThan (wd a) (wd b)) = 0 := by
  unfold lessThan
  rw [ite_eq_left (by rw [toNat_wd (by omega), toNat_wd hb]; exact h)]
  decide

theorem isZero_ge {a b : Nat} (h : b ≤ a) (ha : a < 2 ^ 256) :
    isZero (lessThan (wd a) (wd b)) ≠ 0 := by
  unfold lessThan
  rw [ite_eq_right (by rw [toNat_wd ha, toNat_wd (by omega)]; omega)]
  decide

/-- The stack at the head of the copy loop, after `j` rounds. -/
abbrev loopStk (P N j : Nat) (y x : U256) : List U256 :=
  [wd (32 * j), 0x80, wd (P + 64), wd N, wd N, 0x80, wd (P + 64), wd P, wd P, 0x60, y, x]

/-- One round of the copy loop: the word `dw j` at `0x80 + 32 j` is appended. -/
theorem retLG {r : Nat} (hp : r ∈ RETS) {Mb : ByteArray} {P N : Nat} (hP : Mb.size = P)
    (hmod : P % 32 = 0) (hPb : P < 2 ^ 200) {dw : Nat → U256} {j : Nat} (hj : 32 * j < N)
    (hin : 128 + 32 * j + 32 ≤ P)
    (hd : loadWord (memoryReadBytes Mb (128 + 32 * j) 32) 0 32 = dw j) (hN : N < 2 ^ 200)
    {y x : U256} {gas : Nat}
    (hg : 75 + (mg (P + 64 + 32 * (j + 1)) - mg (P + 64 + 32 * j)) ≤ gas) :
    Gas.HoareG fork (At CODE message (r + 37) (loopStk P N j y x)
        (Mb ++ wordBytes 0x20 ++ wordBytes (wd N) ++ cat dw j) gas state substate)
      (At CODE message (r + 37) (loopStk P N (j + 1) y x)
        (Mb ++ wordBytes 0x20 ++ wordBytes (wd N) ++ cat dw (j + 1))
        (gas - (75 + (mg (P + 64 + 32 * (j + 1)) - mg (P + 64 + 32 * j)))) state substate) := by
  have sz : (Mb ++ wordBytes 0x20 ++ wordBytes (wd N) ++ cat dw j).size = P + 64 + 32 * j := by
    rw [ByteArray.size_append, size_app, size_app, size_cat, hP]
  have rd : loadWord (memoryReadBytes (Mb ++ wordBytes 0x20 ++ wordBytes (wd N) ++ cat dw j)
      (128 + 32 * j) 32) 0 32 = dw j := by
    rw [read_left (by rw [size_app, size_app, hP]; omega), read_left (by rw [size_app, hP]; omega),
      read_left (by rw [hP]; omega)]
    exact hd
  have e1 : P + 64 + 32 * j + 32 = P + 64 + 32 * (j + 1) := by omega
  simp only [loopStk]
  simp only [RETS, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl
  all_goals
    step jumpdestR
    step dupR 3
    step dupR 1
    step binR 0x10 Local.instruction_lt
    step unR 0x15 instruction_iszero
    step pushAnyR 2
    step jumpi0R (isZero_lt hj (by omega))
    step dupR 0
    step dupR 2
    step binR 0x01 instruction_add
    rw [show (0x80 : U256) = wd 128 from rfl, add_wd]
    step mloadIn (by code_fact) (by code_fact) (by rw [sz, toNat_wd (by omega)]; omega)
      (by rw [sz]; omega) (by gas_ok)
    rw [toNat_wd (by omega), show 32 * j + 128 = 128 + 32 * j by omega, rd]
    step dupR 1
    step dupR 4
    step binR 0x01 instruction_add
    rw [add_wd]
    step mstoreApp (by code_fact) (by code_fact) (by rw [sz, toNat_wd (by omega)]; omega)
      (by rw [sz]; omega) (by rw [sz, e1]; gas_ok)
    rw [sz, e1]
    step pushR 1 (0x20 : U256)
    step dupR 1
    step binR 0x01 instruction_add
    rw [addw20]
    step swapR 0
    norm
    step popR
    step pushAnyR 2
    step jumpR
    exact restate (by decide) (by rw [show 32 * j + 32 = 32 * (j + 1) by omega])
      (by rw [cat, ByteArray.append_assoc]) (by gas_ok) rfl rfl

/-- The copy loop from round `j` to its last round `W` (`j + d = W`), each word `dw i` (`i < W`)
read at `0x80 + 32 i` within `Mb`. -/
theorem loopG {r : Nat} (hp : r ∈ RETS) {Mb : ByteArray} {P N W : Nat} (hP : Mb.size = P)
    (hmod : P % 32 = 0) (hPb : P < 2 ^ 200) (hW : 128 + 32 * W ≤ P) (hN : N < 2 ^ 200)
    (hNW : 32 * W < N + 32) {dw : Nat → U256}
    (hd : ∀ i, i < W → loadWord (memoryReadBytes Mb (128 + 32 * i) 32) 0 32 = dw i)
    {y x : U256} : ∀ (d j : Nat) (gas : Nat), j + d = W →
    75 * d + (mg (P + 64 + 32 * W) - mg (P + 64 + 32 * j)) ≤ gas →
    Gas.HoareG fork (At CODE message (r + 37) (loopStk P N j y x)
        (Mb ++ wordBytes 0x20 ++ wordBytes (wd N) ++ cat dw j) gas state substate)
      (At CODE message (r + 37) (loopStk P N W y x)
        (Mb ++ wordBytes 0x20 ++ wordBytes (wd N) ++ cat dw W)
        (gas - (75 * d + (mg (P + 64 + 32 * W) - mg (P + 64 + 32 * j)))) state substate) := by
  intro d
  induction d with
  | zero =>
    intro j gas hj _
    have hj' : W = j := by omega
    subst hj'
    exact restate rfl rfl rfl (by omega) rfl rfl
  | succ d ih =>
    intro j gas hj hg
    have m1 : mg (P + 64 + 32 * j) ≤ mg (P + 64 + 32 * (j + 1)) := memoryGasCost_mono (by omega)
    have m2 : mg (P + 64 + 32 * (j + 1)) ≤ mg (P + 64 + 32 * W) := memoryGasCost_mono (by omega)
    refine (retLG hp hP hmod hPb (by omega) (by omega) (hd j (by omega)) hN
      (gas := gas) (by omega)).seq ?_
    refine (ih (j + 1) _ (by omega) (by omega)).seq ?_
    exact restate rfl rfl rfl (by omega) rfl rfl

/-! ## The end of the return block -/

theorem and31w {N : Nat} (hN : N < 2 ^ 256) : bitwiseAnd 31 (wd N) = wd (N % 32) := by
  apply BitVec.eq_of_toNat_eq
  rw [toNat_wd (by omega : N % 32 < 2 ^ 256)]
  simp only [bitwiseAnd, BitVec.toNat_and, toNat_wd hN]
  rw [show (BitVec.toNat (31 : U256)) = 2 ^ 5 - 1 from rfl, Nat.and_comm,
    Nat.and_two_pow_sub_one_eq_mod]

theorem isZero_wd_ne {m : Nat} (h : m ≠ 0) (hm : m < 2 ^ 256) : isZero (wd m) = 0 := by
  unfold isZero
  rw [ite_eq_right (fun h' => h (by have := congrArg BitVec.toNat h'; rwa [toNat_wd hm] at this))]

/-- GENERIC: a word written over the last word of a memory replaces it. -/
theorem write_last (A : ByteArray) (u v : U256) :
    memoryWrite (A ++ wordBytes u) A.size (wordBytes v) = A ++ wordBytes v := by
  have hfit : A.size + (wordBytes v).size ≤ (A ++ wordBytes u).size := by
    rw [size_app, size_wordBytes]; exact Nat.le_refl _
  apply EthLib.Base.eq_of_byteAt
  · rw [size_memoryWrite hfit, size_app, size_app]
  · intro i
    rw [byteAt_memoryWrite hfit, EthLib.Base.byteAt_append, EthLib.Base.byteAt_append,
      size_wordBytes]
    by_cases h1 : i < A.size
    · rw [ite_eq_right (by omega), ite_eq_left h1, ite_eq_left h1]
    · by_cases h2 : i < A.size + 32
      · rw [ite_eq_left ⟨by omega, h2⟩, ite_eq_right h1]
      · rw [ite_eq_right (by omega), ite_eq_right h1, ite_eq_right h1,
          EthLib.Base.byteAt_of_size_le (by rw [size_wordBytes]; omega),
          EthLib.Base.byteAt_of_size_le (by rw [size_wordBytes]; omega)]

/-- The word `v` with its low `32 - m` bytes cleared (1 ≤ m ≤ 31). -/
theorem maskTop (v : U256) {m : Nat} (h1 : 1 ≤ m) (h31 : m ≤ 31) :
    maskedWord m v = topBytes v m := by
  rw [maskedWord, maskWord h1 h31]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [bitwiseAnd, bitwiseNot, topBytes, BitVec.getLsbD_and, BitVec.getLsbD_not,
    BitVec.getLsbD_ofNat, Nat.testBit_mul_two_pow, Nat.testBit_div_two_pow,
    Nat.testBit_two_pow_sub_one, hi, BitVec.testBit_toNat]
  by_cases h : 8 * (32 - m) ≤ i
  · simp [h, Nat.not_lt.mpr h, Nat.sub_add_cancel h]
  · simp [h, Nat.lt_of_not_le h]

/-- The exit of the copy loop when the length `N` is a multiple of 32: on at 539 (r + 109). -/
theorem retXZ {r : Nat} (hp : r ∈ RETS) {M : ByteArray} {P N W : Nat} (hNW : N ≤ 32 * W)
    (hW : 32 * W < 2 ^ 200) (hm : N % 32 = 0) {y x : U256} {gas : Nat}
    (hg : 77 ≤ gas) :
    Gas.HoareG fork (At CODE message (r + 37) (loopStk P N W y x) M gas state substate)
      (At CODE message (r + 109) [0, wd (P + 64 + N), wd P, wd P, 0x60, y, x] M (gas - 77) state
        substate) := by
  simp only [loopStk]
  simp only [RETS, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl
  all_goals
    step jumpdestR
    step dupR 3
    step dupR 1
    step binR 0x10 Local.instruction_lt
    step unR 0x15 instruction_iszero
    step pushAnyR 2
    step jumpiR (isZero_ge hNW (by omega))
    first | at_pc 494 | at_pc 1807
    step jumpdestR
    step popR
    step popR
    step popR
    step popR
    step swapR 0
    norm
    step popR
    step swapR 0
    norm
    step dupR 1
    step binR 0x01 instruction_add
    rw [add_wd]
    step swapR 0
    norm
    step pushR 1 (0x1f : U256)
    step binR 0x16 Local.instruction_and
    rw [and31w (by omega), hm]
    step dupR 0
    step unR 0x15 instruction_iszero
    step pushAnyR 2
    step jumpiR (by decide)
    exact restate (by decide) rfl rfl (by gas_ok) rfl rfl

/-- The exit of the copy loop when `N` is not a multiple of 32: on at r + 84 (padding). -/
theorem retXP {r : Nat} (hp : r ∈ RETS) {M : ByteArray} {P N W : Nat} (hNW : N ≤ 32 * W)
    (hW : 32 * W < 2 ^ 200) (hm : N % 32 ≠ 0) {y x : U256} {gas : Nat}
    (hg : 77 ≤ gas) :
    Gas.HoareG fork (At CODE message (r + 37) (loopStk P N W y x) M gas state substate)
      (At CODE message (r + 84) [wd (N % 32), wd (P + 64 + N), wd P, wd P, 0x60, y, x] M
        (gas - 77) state substate) := by
  simp only [loopStk]
  simp only [RETS, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl
  all_goals
    step jumpdestR
    step dupR 3
    step dupR 1
    step binR 0x10 Local.instruction_lt
    step unR 0x15 instruction_iszero
    step pushAnyR 2
    step jumpiR (isZero_ge hNW (by omega))
    first | at_pc 494 | at_pc 1807
    step jumpdestR
    step popR
    step popR
    step popR
    step popR
    step swapR 0
    norm
    step popR
    step swapR 0
    norm
    step dupR 1
    step binR 0x01 instruction_add
    rw [add_wd]
    step swapR 0
    norm
    step pushR 1 (0x1f : U256)
    step binR 0x16 Local.instruction_and
    rw [and31w (by omega)]
    step dupR 0
    step unR 0x15 instruction_iszero
    step pushAnyR 2
    step jumpi0R (isZero_wd_ne hm (by omega))
    exact restate (by decide) rfl rfl (by gas_ok) rfl rfl

/-- RETURN of a range within memory (size a multiple of 32): no growth, no gas. -/
theorem returnIn {code : ByteArray} {pc : Nat} {M : ByteArray} {start size : U256}
    {rest : List U256} (hlt : pc < code.size) (hbyte : code[pc] = 0xf3)
    (hin : start.toNat + size.toNat ≤ M.size) (hmod : M.size % 32 = 0) {gas : Nat} :
    Gas.SpecG fork (At code message pc (start :: size :: rest) M gas state substate)
      (Halted false (memoryReadBytes M start.toNat size.toNat) gas state substate) := by
  have he : extendMemory M.size [(start, size)] = ⟨0, 0⟩ := by
    apply extendMemory_eq_zero
    intro q hq
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq
    subst hq
    right
    rw [ceil32_of_mod hmod]
    exact ceil32_le hin hmod
  refine (Gas.returnG hlt hbyte (by rw [he]; exact Nat.zero_le _)).consequence
    (fun _ h => h) ?_
  rintro evm ⟨hr, he', ho, hgas, hs, hss⟩
  refine ⟨hr, he', ?_, ?_, hs, hss⟩
  · rw [ho, he, memoryExtend_zero]
  · rw [hgas, he]; rfl

/-- At 539 / 1852 (r + 109), the length a multiple of 32: RETURN of the memory from `P` to its
end `E`. -/
theorem retZG {r : Nat} (hp : r ∈ RETS) {M : ByteArray} {P E : Nat} (hE : M.size = E)
    (hmod : E % 32 = 0) (hPE : P ≤ E) (h96 : 96 ≤ P) (hEb : E < 2 ^ 200)
    (hptr : loadWord (memoryReadBytes M 64 32) 0 32 = wd P) {y x : U256} {gas : Nat}
    (hg : 30 ≤ gas) :
    Gas.SpecG fork (At CODE message (r + 109) [0, wd E, wd P, wd P, 0x60, y, x] M gas state substate)
      (Halted false (memoryReadBytes M P (E - P)) (gas - 30) state substate) := by
  have t40 : (0x40 : U256).toNat = 64 := rfl
  simp only [RETS, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl
  all_goals
    step jumpdestR
    step popR
    step swapR 2
    norm
    step popR
    step popR
    step popR
    step pushR 1 (0x40 : U256)
    step mloadIn (by code_fact) (by code_fact) (by rw [hE, t40]; omega) (by rw [hE]; exact hmod)
      (by gas_ok)
    rw [t40, hptr]
    step dupR 0
    step swapR 1
    norm
    step binR 0x03 instruction_sub
    rw [sub_wd hPE]
    step swapR 0
    norm
    refine (returnIn (by code_fact) (by code_fact)
      (by rw [toNat_wd (by omega), toNat_wd (by omega), hE]; omega) (by rw [hE]; exact hmod)).consequence
      (fun _ h => h) ?_
    rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
    refine ⟨hr, he, ?_, by rw [hgas]; gas_ok, hs, hss⟩
    rw [ho, toNat_wd (by omega), toNat_wd (by omega)]

/-- At r + 84, the length `N = E - (P + 64)` not a multiple of 32 (`m = N % 32`): the last word
`v` (at `A.size = E - m`) is masked to its first `m` bytes and written back, then RETURN of the
memory from `P` to its end `Q = A.size + 32`. -/
theorem retPG (hfork : .berlin ≤ fork) {r : Nat} (hp : r ∈ RETS) {A : ByteArray} {P E m : Nat}
    {v : U256} (hA : A.size + m = E) (h1 : 1 ≤ m) (h31 : m ≤ 31) (hmod : A.size % 32 = 0)
    (hPA : P ≤ A.size) (h96 : 96 ≤ A.size) (hEb : E < 2 ^ 200)
    (hptr : loadWord (memoryReadBytes A 64 32) 0 32 = wd P) {y x : U256} {gas : Nat}
    (hg : 146 ≤ gas) :
    Gas.SpecG fork (At CODE message (r + 84) [wd m, wd E, wd P, wd P, 0x60, y, x] (A ++ wordBytes v)
        gas state substate)
      (Halted false (memoryReadBytes (A ++ wordBytes (topBytes v m)) P (A.size + 32 - P))
        (gas - 146) state substate) := by
  have t40 : (0x40 : U256).toNat = 64 := rfl
  have sA : (A ++ wordBytes v).size = A.size + 32 := size_app _ _
  have sB : (A ++ wordBytes (maskedWord m v)).size = A.size + 32 := size_app _ _
  have rv : loadWord (memoryReadBytes (A ++ wordBytes v) A.size 32) 0 32 = v := by
    have h := read_right (A := A) (B := wordBytes v) (s := A.size) rfl
    rw [size_wordBytes] at h
    rw [h, ld]
  have rp : loadWord (memoryReadBytes (A ++ wordBytes (maskedWord m v)) 64 32) 0 32 = wd P := by
    rw [read_left (by omega)]; exact hptr
  simp only [RETS, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl
  all_goals
    step dupR 0
    step dupR 2
    step binR 0x03 instruction_sub
    rw [sub_wd (by omega), show E - m = A.size by omega]
    step dupR 0
    step mloadIn (by code_fact) (by code_fact) (by rw [sA, toNat_wd (by omega)] <;> omega)
      (by rw [sA]; omega) (by gas_ok)
    rw [toNat_wd (by omega), rv]
    step pushR 1 (1 : U256)
    step dupR 3
    step pushR 1 (0x20 : U256)
    step binR 0x03 instruction_sub
    step pushR 2 (0x0100 : U256)
    step Gas.expLG (Nat.le_trans (by decide) hfork) (by code_fact) (by code_fact)
      (by rw [expBytes' h1 h31]; gas_ok)
    rw [expBytes' h1 h31]
    step binR 0x03 instruction_sub
    step unR 0x19 Local.instruction_not
    step binR 0x16 Local.instruction_and
    step dupR 1
    step mstoreIn (by code_fact) (by code_fact) (by rw [sA, toNat_wd (by omega)] <;> omega)
      (by rw [sA]; omega) (by gas_ok)
    rw [toNat_wd (by omega), show bitwiseAnd (bitwiseNot (sub (exp 256 (sub 32 (wd m))) 1)) v =
      maskedWord m v from rfl, write_last]
    step pushR 1 (0x20 : U256)
    step binR 0x01 instruction_add
    rw [add20]
    step swapR 1
    norm
    step popR
    step jumpdestR
    step popR
    step swapR 2
    norm
    step popR
    step popR
    step popR
    step pushR 1 (0x40 : U256)
    step mloadIn (by code_fact) (by code_fact) (by rw [sB, t40]; omega) (by rw [sB]; omega)
      (by gas_ok)
    rw [t40, rp]
    step dupR 0
    step swapR 1
    norm
    step binR 0x03 instruction_sub
    rw [sub_wd (by omega)]
    step swapR 0
    norm
    refine (returnIn (by code_fact) (by code_fact)
      (by rw [toNat_wd (by omega), toNat_wd (by omega), sB]; omega)
      (by rw [sB]; omega)).consequence (fun _ h => h) ?_
    rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
    refine ⟨hr, he, ?_, by rw [hgas]; gas_ok, hs, hss⟩
    rw [ho, toNat_wd (by omega), toNat_wd (by omega), maskTop v h1 h31]

/-! ## The whole return block -/

/-- The data part of the returned string of `N` bytes, from its words `dw 0, dw 1, ...`: the
`N / 32` whole words, then, when `N` is not a multiple of 32, the first `N % 32` bytes of the
next word followed by zeros. -/
def strData (dw : Nat → U256) (N : Nat) : ByteArray :=
  if N % 32 = 0 then cat dw (N / 32) else cat dw (N / 32) ++ wordBytes (topBytes (dw (N / 32)) (N % 32))

/-- The gas of the return block for a memory of `P` bytes and a string of `N` bytes. -/
abbrev retCost (P N : Nat) : Nat :=
  170 + 75 * ((N + 31) / 32) + (if N % 32 = 0 then 30 else 146) +
    (mg (P + 64 + 32 * ((N + 31) / 32)) - mg P)

/-- The return block (430 / 1743) for any string of `N` bytes whose `W = ceil(N / 32)` words
`dw i` are in memory at `0x80 + 32 i`, the memory `Mb` being `P` bytes (a multiple of 32) with
the free memory pointer `P` at 0x40 and `N` at 0x60: it returns the word 0x20, the word `N`, and
`strData dw N`. -/
theorem retG (hfork : .berlin ≤ fork) {r : Nat} (hp : r ∈ RETS) {Mb : ByteArray} {P N : Nat}
    (hP : Mb.size = P) (hmod : P % 32 = 0) (hW : 128 + 32 * ((N + 31) / 32) ≤ P)
    (hPb : P < 2 ^ 190) (hN : N < 2 ^ 190)
    (hptr : loadWord (memoryReadBytes Mb 64 32) 0 32 = wd P)
    (hlen : loadWord (memoryReadBytes Mb 96 32) 0 32 = wd N) {dw : Nat → U256}
    (hd : ∀ i, i < (N + 31) / 32 → loadWord (memoryReadBytes Mb (128 + 32 * i) 32) 0 32 = dw i)
    {y x : U256} {gas : Nat} (hg : retCost P N ≤ gas) :
    Gas.SpecG fork (At CODE message r [0x60, y, x] Mb gas state substate)
      (Halted false (wordBytes 0x20 ++ wordBytes (wd N) ++ strData dw N) (gas - retCost P N)
        state substate) := by
  simp only [retCost] at hg ⊢
  generalize hWd : (N + 31) / 32 = W at hW hd hg ⊢
  have m1 : mg P ≤ mg (P + 64) := memoryGasCost_mono (by omega)
  have m2 : mg (P + 64) ≤ mg (P + 64 + 32 * W) := memoryGasCost_mono (by omega)
  have hMD : (Mb ++ wordBytes 0x20 ++ wordBytes (wd N)).size = P + 64 := by
    rw [size_app, size_app, hP]
  refine Gas.SpecG.seq (retAG hp hP hmod (by omega) (by omega) hptr hlen (gas := gas) (by omega)) ?_
  refine Gas.SpecG.seq ((restate rfl rfl (by rw [cat, ByteArray.append_empty]) rfl rfl rfl).seq (loopG (W := W) (N := N) (dw := dw) hp hP hmod (by omega) (by omega) (by omega) (by omega) hd W 0 (gas - (93 + (mg (P + 64) - mg P)))
    (by omega) (by simp only [Nat.mul_zero, Nat.add_zero]; omega))) ?_
  simp only [Nat.mul_zero, Nat.add_zero]
  by_cases hm : N % 32 = 0
  · have hNW : N = 32 * W := by omega
    have sF : (Mb ++ wordBytes 0x20 ++ wordBytes (wd N) ++ cat dw W).size = P + 64 + N := by
      rw [ByteArray.size_append, hMD, size_cat]; omega
    refine Gas.SpecG.seq (retXZ hp (W := W) (by omega) (by omega) hm (gas := gas - (93 + (mg (P + 64) - mg P)) -
      (75 * W + (mg (P + 64 + 32 * W) - mg (P + 64)))) (by simp only [hm, ↓reduceIte] at hg; omega)) ?_
    refine (retZG hp sF (by omega) (by omega) (by omega) (by omega)
      (by rw [read_left (by rw [hMD]; omega), read_left (by rw [size_app, hP]; omega),
        read_left (by rw [hP]; omega)]; exact hptr)
      (by simp only [hm, ↓reduceIte] at hg; omega)).consequence (fun _ h => h) ?_
    rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
    refine ⟨hr, he, ?_, by rw [hgas]; simp only [hm, ↓reduceIte]; omega, hs, hss⟩
    simp only [strData, hm, ↓reduceIte]
    rw [ho, show N / 32 = W by omega, ByteArray.append_assoc,
      ByteArray.append_assoc]
    have h := read_right (A := Mb) (B := wordBytes 0x20 ++ (wordBytes (wd N) ++ cat dw W))
      (s := P) hP
    rw [ByteArray.size_append, ByteArray.size_append, size_wordBytes, size_wordBytes, size_cat] at h
    rw [show P + 64 + N - P = 32 + (32 + 32 * W) by omega, h, ← ByteArray.append_assoc]
  · have hW1 : W = N / 32 + 1 := by omega
    subst hW1
    have sA : (Mb ++ wordBytes 0x20 ++ wordBytes (wd N) ++ cat dw (N / 32)).size =
        P + 64 + 32 * (N / 32) := by
      rw [ByteArray.size_append, hMD, size_cat]
    refine Gas.SpecG.seq (retXP hp (W := N / 32 + 1) (by omega) (by omega) hm
      (gas := gas - (93 + (mg (P + 64) - mg P)) - (75 * (N / 32 + 1) +
        (mg (P + 64 + 32 * (N / 32 + 1)) - mg (P + 64))))
      (by simp only [hm, ↓reduceIte] at hg; omega)) ?_
    rw [cat, ← ByteArray.append_assoc]
    refine (retPG hfork hp (E := P + 64 + N) (by rw [sA]; omega) (by omega) (by omega)
      (by rw [sA]; omega) (by rw [sA]; omega) (by rw [sA]; omega) (by omega)
      (by rw [read_left (by rw [hMD]; omega), read_left (by rw [size_app, hP]; omega),
        read_left (by rw [hP]; omega)]; exact hptr)
      (by simp only [hm, ↓reduceIte] at hg; omega)).consequence (fun _ h => h) ?_
    rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
    refine ⟨hr, he, ?_, by rw [hgas]; simp only [hm, ↓reduceIte]; omega, hs, hss⟩
    simp only [strData, hm, ↓reduceIte]
    rw [ho, sA]
    simp only [ByteArray.append_assoc]
    have h := read_right (A := Mb) (B := wordBytes 0x20 ++ (wordBytes (wd N) ++
      (cat dw (N / 32) ++ wordBytes (topBytes (dw (N / 32)) (N % 32))))) (s := P) hP
    rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_append, size_wordBytes,
      size_wordBytes, size_wordBytes, size_cat] at h
    rw [show P + 64 + 32 * (N / 32) + 32 - P = 32 + (32 + (32 * (N / 32) + 32)) by omega, h]

/-! ## The body for any length -/

/-- The length that the code computes from the slot word `w`: the low byte halved when the low
bit is 0 (short form), `w / 2` when it is 1 (long form). -/
abbrev lenOf (w : U256) : U256 :=
  div (bitwiseAnd (sub (mul 256 (isZero (bitwiseAnd 1 w))) 1) w) 2

theorem lenOf_long {w : U256} (h : w.toNat % 2 = 1) : lenOf w = wd (w.toNat / 2) := by
  have h0 : bitwiseAnd 1 w ≠ 0 := by
    intro hz
    have := congrArg BitVec.toNat hz
    rw [and1] at this
    simp at this; omega
  have hz : isZero (bitwiseAnd 1 w) = 0 := by unfold isZero; exact ite_eq_right h0
  rw [lenOf, hz, show sub (mul 256 (0 : U256)) 1 = (BitVec.allOnes 256 : U256) by decide]
  simp only [bitwiseAnd, BitVec.allOnes_and]
  apply BitVec.eq_of_toNat_eq
  simp [div]

theorem roundW {N : Nat} (hN : N < 2 ^ 200) :
    add 32 (mul (div (add 31 (wd N)) 32) 32) = wd (32 + 32 * ((N + 31) / 32)) := by
  apply BitVec.eq_of_toNat_eq
  have hd : div (add 31 (wd N)) 32 = wd ((N + 31) / 32) := by
    unfold div
    rw [ite_eq_right (by decide)]
    apply BitVec.eq_of_toNat_eq
    simp [add, BitVec.toNat_add]
    omega
  rw [hd, toNat_wd (by omega)]
  simp [add, mul, BitVec.toNat_add, BitVec.toNat_mul]
  omega

/-- The memory of the prelude with the free memory pointer `p`. -/
abbrev MEMP (p : Nat) : ByteArray := memoryWrite MEM0 64 (wordBytes (wd p))

theorem size_MEMP (p : Nat) : (MEMP p).size = 96 := by
  rw [MEMP, size_memoryWrite (by rw [size_wordBytes, size_MEM0]; decide), size_MEM0]

theorem ptr_MEMP (p : Nat) : loadWord (memoryReadBytes (MEMP p) 64 32) 0 32 = wd p :=
  loadWord_memoryWrite_wordBytes _ (by rw [size_MEM0]; decide)

/-- The body to the write of the free pointer, for a length `N`: one read of the slot, the free
pointer moved to `96 + 32 + 32 ceil(N / 32)`. -/
theorem body1G {b r : Nat} {k : U256} (hp : (b, k, r) ∈ BODY) (hfork : .berlin ≤ fork) {N : Nat}
    (hL : lenOf (storageAt state message.currentTarget k) = wd N) (hN : N < 2 ^ 200) {ck : Bool}
    (hck : coldIn substate message.currentTarget k = ck) {x y : U256}
    {gas : Nat} (hg : 102 + slotCost ck ≤ gas) :
    Gas.HoareG fork (At CODE message b [y, x] MEM0 gas state substate)
      (At CODE message (b + 44) [0x60, wd N, k, y, x] (MEMP (32 + 32 * ((N + 31) / 32) + 96))
        (gas - (102 + slotCost ck))
        (readSlot state message.currentTarget k)
        (accessSlot substate message.currentTarget k)) := by
  simp only [lenOf] at hL
  simp only [BODY, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hp
  rcases hp with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  all_goals
    step jumpdestR
    first | step pushR 1 (7 : U256) | step pushR 1 (8 : U256)
    step dupR 0
    step Gas.sloadG hfork (cold := ck) (by code_fact) (by code_fact) hck (by gas_ok)
    rw [getStorage_eq]
    step pushR 1 (1 : U256)
    step dupR 1
    step pushR 1 (1 : U256)
    step binR 0x16 Local.instruction_and
    step unR 0x15 instruction_iszero
    step pushR 2 (0x0100 : U256)
    step binR 0x02 Local.instruction_mul
    step binR 0x03 instruction_sub
    step binR 0x16 Local.instruction_and
    step pushR 1 (2 : U256)
    step swapR 0
    norm
    step binR 0x04 Local.instruction_div
    rw [hL]
    step dupR 0
    step pushR 1 (0x1f : U256)
    step binR 0x01 instruction_add
    step pushR 1 (0x20 : U256)
    step dupR 0
    step swapR 1
    norm
    step binR 0x04 Local.instruction_div
    step binR 0x02 Local.instruction_mul
    step pushR 1 (0x20 : U256)
    step binR 0x01 instruction_add
    rw [roundW hN]
    step pushR 1 (0x40 : U256)
    have hext0 : extendMemory MEM0.size [((0x40 : U256), (32 : U256))] = ⟨0, 0⟩ := by
      rw [size_MEM0]; decide
    step Gas.mloadG (by code_fact) (by code_fact) (by rw [hext0]; gas_ok)
    step Gas.reshapeG (s' := [0x60, wd (32 + 32 * ((N + 31) / 32)), wd N, _, _, x]) (m' := MEM0)
      (g' := gas - (87 + slotCost ck))
      (by rw [hext0, memoryExtend_zero]; exact congrArg (· :: _) mload_MEM0)
      (by rw [hext0, memoryExtend_zero]) (by rw [hext0]; gas_ok)
    step swapR 0
    norm
    step dupR 1
    step binR 0x01 instruction_add
    rw [show (0x60 : U256) = wd 96 from rfl, add_wd]
    step pushR 1 (0x40 : U256)
    step Gas.mstoreG (by code_fact) (by code_fact) (by rw [hext0]; gas_ok)
    step Gas.reshapeG (s' := [wd 96, wd N, _, _, x]) (m' := MEMP (32 + 32 * ((N + 31) / 32) + 96))
      (g' := gas - (102 + slotCost ck)) rfl
      (by rw [hext0, memoryExtend_zero]; rfl) (by rw [hext0]; gas_ok)
    exact restate (by decide) rfl rfl rfl rfl rfl

/-- The empty string: the length 0 written at 0x60, the second read of the slot (warm), and the
JUMPI at 2567 / 5285 taken; back to the return block `r` with the memory `MEMP p ++ [0]`. -/
theorem body2E {b r : Nat} {k : U256} (hp : (b, k, r) ∈ BODY) (hfork : .berlin ≤ fork) {p : Nat}
    (hL : lenOf (storageAt state message.currentTarget k) = wd 0)
    (hck : coldIn substate message.currentTarget k = false) {x : U256}
    {gas : Nat} (hg : 217 ≤ gas) :
    Gas.HoareG fork (At CODE message (b + 44) [0x60, wd 0, k, BitVec.ofNat 256 r, x] (MEMP p) gas state
        substate)
      (At CODE message r [0x60, BitVec.ofNat 256 r, x] (MEMP p ++ wordBytes (wd 0)) (gas - 217)
        (readSlot state message.currentTarget k)
        (accessSlot substate message.currentTarget k)) := by
  simp only [lenOf] at hL
  have hext1 : extendMemory (MEMP p).size [((0x60 : U256), (32 : U256))] = ⟨3, 32⟩ := by
    rw [size_MEMP]; decide
  simp only [BODY, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hp
  rcases hp with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  all_goals
    step dupR 0
    step swapR 2
    norm
    step swapR 1
    norm
    step swapR 0
    norm
    step dupR 1
    step dupR 1
    step Gas.mstoreG (by code_fact) (by code_fact) (by rw [hext1]; gas_ok)
    step Gas.reshapeG (m' := MEMP p ++ wordBytes (wd 0)) (g' := gas - 24)
      rfl (by rw [hext1]; exact write_end (by rw [size_MEMP]; rfl) _) (by rw [hext1]; gas_ok)
    step pushR 1 (0x20 : U256)
    step binR 0x01 instruction_add
    step Gas.reshapeG (s' := [0x80, wd 0, _, 0x60, _, x]) rfl rfl rfl
    step dupR 2
    step dupR 0
    step Gas.sloadG hfork (cold := false) (by code_fact) (by code_fact) hck (by gas_ok)
    rw [getStorage_eq]
    step pushR 1 (1 : U256)
    step dupR 1
    step pushR 1 (1 : U256)
    step binR 0x16 Local.instruction_and
    step unR 0x15 instruction_iszero
    step pushR 2 (0x0100 : U256)
    step binR 0x02 Local.instruction_mul
    step binR 0x03 instruction_sub
    step binR 0x16 Local.instruction_and
    step pushR 1 (2 : U256)
    step swapR 0
    norm
    step binR 0x04 Local.instruction_div
    rw [hL]
    step dupR 0
    step unR 0x15 instruction_iszero
    step pushAnyR 2
    step jumpiR (by decide)
    first | at_pc 2638 | at_pc 5356
    step jumpdestR
    step popR
    step popR
    step popR
    step popR
    step popR
    step dupR 1
    step jumpR
    exact restate (by decide) rfl rfl (by gas_ok) rfl rfl

/-- The specification of `name()` / `symbol()` for the empty string: the slot word has low byte
0 (the short form of length 0). The run returns 64 bytes, the word 0x20 and the word 0; the slot
is read twice. -/
theorem spec_strEmpty (hfork : .berlin ≤ fork) {sel t e r b : Nat} {k : U256}
    (hp : (sel, t, e, r, b, k) ∈ STR_GETTERS) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = sel)
    (hv : message.value = 0)
    (hn : (storageAt state message.currentTarget k).toNat % 256 = 0) {ck : Bool}
    (hck : coldIn substate message.currentTarget k = ck) {gas : Nat}
    (hg : 62 + 22 * t + 34 + (102 + slotCost ck) + 217 + retCost 128 0 ≤ gas) :
    Gas.SpecG fork (At CODE message 0 [] .empty gas state substate)
      (Halted false (wordBytes 0x20 ++ wordBytes 0)
        (gas - (62 + 22 * t + 34 + (102 + slotCost ck) + 217 + retCost 128 0))
        (readSlot state message.currentTarget k)
        (accessSlot substate message.currentTarget k)) := by
  have hpe : (e, r, b, k) ∈ STR := by
    simp only [STR_GETTERS, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hp
    rcases hp with ⟨-, -, rfl, rfl, rfl, rfl⟩ | ⟨-, -, rfl, rfl, rfl, rfl⟩ <;> decide
  have hpb : (b, k, r) ∈ BODY := by
    simp only [STR_GETTERS, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hp
    rcases hp with ⟨-, -, -, rfl, rfl, rfl⟩ | ⟨-, -, -, rfl, rfl, rfl⟩ <;> decide
  have hpr : r ∈ RETS := by
    simp only [STR_GETTERS, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hp
    rcases hp with ⟨-, -, -, rfl, -, -⟩ | ⟨-, -, -, rfl, -, -⟩ <;> decide
  have ht : tested (BitVec.ofNat 256 sel) ENTRIES = t ∧
      branch (BitVec.ofNat 256 sel) 54 (entrySize 4 2) ENTRIES = e := by
    simp only [STR_GETTERS, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hp
    rcases hp with ⟨rfl, rfl, rfl, -, -, -⟩ | ⟨rfl, rfl, rfl, -, -, -⟩ <;> decide
  have hL : lenOf (storageAt state message.currentTarget k) = wd 0 := lenWord (n := 0) hn
  have hL2 : lenOf (storageAt (readSlot state message.currentTarget k) message.currentTarget k) =
      wd 0 := by rw [storageAt_readSlot]; exact hL
  have hc2 : coldIn (accessSlot substate message.currentTarget k) message.currentTarget k =
      false := coldIn_accessSlot_self _ _ _
  have sM : (MEMP 128 ++ wordBytes (wd 0)).size = 128 := by rw [size_app, size_MEMP]
  refine Gas.SpecG.seq ((toEntry ht hsize hsize' hsel (by omega)).seq
    ((entryS hpe hv (by omega)).seq (body1G hpb hfork hL (by decide) hck (by omega)))) ?_
  refine Gas.SpecG.seq (body2E (p := 128) hpb hfork hL2 hc2 (by omega)) ?_
  rw [readSlot_readSlot, accessSlot_accessSlot]
  refine (retG (N := 0) hfork hpr sM (by decide) (by decide) (by decide) (by decide)
    (by rw [read_left (by rw [size_MEMP] <;> omega)]; exact ptr_MEMP 128)
    (by
      have h := read_right (A := MEMP 128) (B := wordBytes (wd 0)) (s := 96) (size_MEMP 128)
      rw [size_wordBytes] at h
      rw [h, ld])
    (dw := fun _ => 0) (by intro i hi; omega) (by omega)).consequence (fun _ h => h) ?_
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  refine ⟨hr, he, ?_, by rw [hgas]; omega, hs, hss⟩
  rw [ho]
  rfl

/-! ## The long form -/

theorem isZero_wd_lt {a b : Nat} (h : a < b) (hb : b < 2 ^ 256) :
    lessThan (wd a) (wd b) ≠ 0 := by
  unfold lessThan
  rw [ite_eq_left (by rw [toNat_wd (by omega), toNat_wd hb]; exact h)]
  decide

theorem gt_ne {a b : Nat} (h : b < a) (ha : a < 2 ^ 256) : greaterThan (wd a) (wd b) ≠ 0 := by
  unfold greaterThan
  rw [ite_eq_left (by rw [toNat_wd ha, toNat_wd (by omega)]; exact h)]
  decide

theorem gt_eq {a b : Nat} (h : a ≤ b) (hb : b < 2 ^ 256) : greaterThan (wd a) (wd b) = 0 := by
  unfold greaterThan
  rw [ite_eq_right (by rw [toNat_wd (by omega), toNat_wd hb]; omega)]

/-- The memory before the storage loop of the long form: the free pointer `p`, the length `N` at
0x60, and the slot number `k` written at 0 (for its hash). -/
abbrev MEMK (p N : Nat) (k : U256) : ByteArray :=
  memoryWrite (MEMP p ++ wordBytes (wd N)) 0 (wordBytes k)

theorem size_MEMK (p N : Nat) (k : U256) : (MEMK p N k).size = 128 := by
  rw [MEMK, size_memoryWrite (by rw [size_app, size_MEMP, size_wordBytes]; decide), size_app,
    size_MEMP]

theorem read_MEMK0 (p N : Nat) (k : U256) : memoryReadBytes (MEMK p N k) 0 32 = wordBytes k := by
  have h := memoryReadBytes_memoryWrite (memory := MEMP p ++ wordBytes (wd N)) (start := 0)
    (value := wordBytes k) (by rw [size_app, size_MEMP, size_wordBytes]; decide)
  rwa [size_wordBytes] at h

theorem ptr_MEMK (p N : Nat) (k : U256) :
    loadWord (memoryReadBytes (MEMK p N k) 64 32) 0 32 = wd p := by
  rw [MEMK, memoryReadBytes_memoryWrite_of_disjoint (by rw [size_app, size_MEMP, size_wordBytes]; decide)
    (.inr (by simp [size_wordBytes])), read_left (by rw [size_MEMP] <;> omega)]
  exact ptr_MEMP p

theorem len_MEMK (p N : Nat) (k : U256) :
    loadWord (memoryReadBytes (MEMK p N k) 96 32) 0 32 = wd N := by
  rw [MEMK, memoryReadBytes_memoryWrite_of_disjoint (by rw [size_app, size_MEMP, size_wordBytes]; decide)
    (.inr (by simp [size_wordBytes]))]
  have h := read_right (A := MEMP p) (B := wordBytes (wd N)) (s := 96) (size_MEMP p)
  rw [size_wordBytes] at h
  rw [h, ld]

theorem MEMK_eq (p N : Nat) (k : U256) :
    memoryWrite (MEMP p ++ wordBytes (wd N)) (BitVec.toNat (0 : U256)) (wordBytes k) = MEMK p N k :=
  rfl

/-- The long form, from the length write to the head of the storage loop at 2609 / 5327: the
second read of the slot (warm), the two length tests (JUMPI at 2575 / 5293 taken), the end
`0x80 + N`, and the hash of the slot number. -/
theorem body2L {b r : Nat} {k : U256} (hp : (b, k, r) ∈ BODY) (hfork : .berlin ≤ fork) {p N : Nat}
    (hL : lenOf (storageAt state message.currentTarget k) = wd N) (h32 : 32 ≤ N)
    (hN : N < 2 ^ 200) (hck : coldIn substate message.currentTarget k = false) {x : U256}
    {gas : Nat} (hg : 281 ≤ gas) :
    Gas.HoareG fork (At CODE message (b + 44) [0x60, wd N, k, BitVec.ofNat 256 r, x] (MEMP p) gas state
        substate)
      (At CODE message (b + 121) [wd 128, keccak (wordBytes k), wd (N + 128), wd N, k, 0x60,
          BitVec.ofNat 256 r, x] (MEMK p N k) (gas - 281)
        (readSlot state message.currentTarget k)
        (accessSlot substate message.currentTarget k)) := by
  simp only [lenOf] at hL
  have hext1 : extendMemory (MEMP p).size [((0x60 : U256), (32 : U256))] = ⟨3, 32⟩ := by
    rw [size_MEMP]; decide
  have sA : (MEMP p ++ wordBytes (wd N)).size = 128 := by rw [size_app, size_MEMP]
  have hk : keccak256Cost (0x20 : U256) = 36 := by decide
  simp only [BODY, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hp
  rcases hp with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  all_goals
    step dupR 0
    step swapR 2
    norm
    step swapR 1
    norm
    step swapR 0
    norm
    step dupR 1
    step dupR 1
    step Gas.mstoreG (by code_fact) (by code_fact) (by rw [hext1]; gas_ok)
    step Gas.reshapeG (m' := MEMP p ++ wordBytes (wd N)) (g' := gas - 24)
      rfl (by rw [hext1]; exact write_end (by rw [size_MEMP]; rfl) _) (by rw [hext1]; gas_ok)
    step pushR 1 (0x20 : U256)
    step binR 0x01 instruction_add
    step Gas.reshapeG (s' := [0x80, wd N, _, 0x60, _, x]) rfl rfl rfl
    step dupR 2
    step dupR 0
    step Gas.sloadG hfork (cold := false) (by code_fact) (by code_fact) hck (by gas_ok)
    rw [getStorage_eq]
    step pushR 1 (1 : U256)
    step dupR 1
    step pushR 1 (1 : U256)
    step binR 0x16 Local.instruction_and
    step unR 0x15 instruction_iszero
    step pushR 2 (0x0100 : U256)
    step binR 0x02 Local.instruction_mul
    step binR 0x03 instruction_sub
    step binR 0x16 Local.instruction_and
    step pushR 1 (2 : U256)
    step swapR 0
    norm
    step binR 0x04 Local.instruction_div
    rw [hL]
    step dupR 0
    step unR 0x15 instruction_iszero
    step pushAnyR 2
    step jumpi0R (isZero_wd_ne (by omega) (by omega))
    step dupR 0
    step pushR 1 (0x1f : U256)
    step binR 0x10 Local.instruction_lt
    step pushAnyR 2
    step jumpiR (isZero_wd_lt (a := 31) (by omega) (by omega))
    first | at_pc 2595 | at_pc 5313
    step jumpdestR
    step dupR 2
    step binR 0x01 instruction_add
    rw [show (0x80 : U256) = wd 128 from rfl, add_wd]
    step swapR 1
    norm
    step swapR 0
    norm
    step pushR 1 (0 : U256)
    step mstoreIn (by code_fact) (by code_fact) (by rw [sA] <;> decide) (by rw [sA] <;> decide)
      (by gas_ok)
    rw [MEMK_eq]
    step pushR 1 (0x20 : U256)
    step pushR 1 (0 : U256)
    step Gas.keccak256G (by code_fact) (by code_fact)
      (by rw [hk, size_MEMK, ext_in (by decide) (by decide)]; gas_ok)
    rw [hk, size_MEMK, ext_in (by decide) (by decide), memoryExtend_zero,
      show (0 : U256).toNat = 0 from rfl, show (0x20 : U256).toNat = 32 from rfl, read_MEMK0]
    step swapR 0
    norm
    exact restate (by decide) rfl rfl (by gas_ok) rfl rfl

/-- The slot of word `j` of a long string whose data starts at slot `h`. -/
abbrev slotJ (h : U256) (j : Nat) : U256 := add (wd j) h

theorem slotJ_succ (h : U256) (j : Nat) : add 1 (slotJ h j) = slotJ h (j + 1) := by
  simp only [slotJ, add]
  rw [← BitVec.add_assoc, show (1 : U256) = wd 1 from rfl, BitVec.ofNat_add_ofNat, Nat.add_comm]

theorem slotJ_zero (h : U256) : slotJ h 0 = h := by
  simp only [slotJ, add]
  exact BitVec.zero_add h

/-- The state after the reads of the first `j` data slots. -/
def rdSt (S : State.TransactionState) (C : EthLib.Base.Address) (h : U256) :
    Nat → State.TransactionState
  | 0 => S
  | j + 1 => readSlot (rdSt S C h j) C (slotJ h j)

/-- The substate after the reads of the first `j` data slots. -/
def rdSs (ss : Substate) (C : EthLib.Base.Address) (h : U256) : Nat → Substate
  | 0 => ss
  | j + 1 => accessSlot (rdSs ss C h j) C (slotJ h j)

/-- The price of the reads of the first `j` data slots, each cold or warm in the substate where
the code reads it. -/
def rdGas (ss : Substate) (C : EthLib.Base.Address) (h : U256) : Nat → Nat
  | 0 => 0
  | j + 1 => rdGas ss C h j + slotCost (coldIn (rdSs ss C h j) C (slotJ h j))

theorem storageAt_rdSt (S : State.TransactionState) (C : EthLib.Base.Address) (h n : U256) :
    ∀ j, storageAt (rdSt S C h j) C n = storageAt S C n
  | 0 => rfl
  | j + 1 => by rw [rdSt, storageAt_readSlot, storageAt_rdSt S C h n j]

theorem rdGas_le (ss : Substate) (C : EthLib.Base.Address) (h : U256) {i j : Nat} (hij : i ≤ j) :
    rdGas ss C h i ≤ rdGas ss C h j := by
  induction j with
  | zero => rw [Nat.le_zero.mp hij]; exact Nat.le_refl _
  | succ j ih =>
    rcases Nat.lt_or_eq_of_le hij with h1 | h1
    · have := ih (by omega); rw [rdGas]; omega
    · rw [h1]; exact Nat.le_refl _

/-- The stack at the head of the storage loop after `j` rounds. -/
abbrev sStk (h : U256) (N j : Nat) (k : U256) (y x : U256) : List U256 :=
  [wd (128 + 32 * j), slotJ h j, wd (N + 128), wd N, k, 0x60, y, x]

/-- One round of the storage loop that goes on: the word of slot `slotJ h j` appended. -/
theorem roundC {b r : Nat} {k : U256} (hp : (b, k, r) ∈ BODY) (hfork : .berlin ≤ fork)
    {S : State.TransactionState} {ss : Substate} {h : U256} {p N j : Nat} (hj : 32 * (j + 1) < N)
    (hN : N < 2 ^ 200) {x : U256} {gas : Nat}
    (hg : 50 + slotCost (coldIn (rdSs ss message.currentTarget h j) message.currentTarget (slotJ h j)) +
      (mg (128 + 32 * (j + 1)) - mg (128 + 32 * j)) ≤ gas) :
    Gas.HoareG fork (At CODE message (b + 121) (sStk h N j k (BitVec.ofNat 256 r) x)
        (MEMK p N k ++ cat (fun i => storageAt S message.currentTarget (slotJ h i)) j) gas
        (rdSt S message.currentTarget h j) (rdSs ss message.currentTarget h j))
      (At CODE message (b + 121) (sStk h N (j + 1) k (BitVec.ofNat 256 r) x)
        (MEMK p N k ++ cat (fun i => storageAt S message.currentTarget (slotJ h i)) (j + 1))
        (gas - (50 + slotCost (coldIn (rdSs ss message.currentTarget h j) message.currentTarget
          (slotJ h j)) + (mg (128 + 32 * (j + 1)) - mg (128 + 32 * j))))
        (rdSt S message.currentTarget h (j + 1)) (rdSs ss message.currentTarget h (j + 1))) := by
  have sz : (MEMK p N k ++ cat (fun i => storageAt S message.currentTarget (slotJ h i)) j).size =
      128 + 32 * j := by rw [ByteArray.size_append, size_MEMK, size_cat]
  have e1 : 128 + 32 * j + 32 = 128 + 32 * (j + 1) := by omega
  simp only [sStk]
  simp only [BODY, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hp
  rcases hp with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  all_goals
    step jumpdestR
    step dupR 1
    step Gas.sloadG hfork (cold := coldIn (rdSs ss message.currentTarget h j) message.currentTarget
      (slotJ h j)) (by code_fact) (by code_fact) rfl (by gas_ok)
    rw [getStorage_eq, storageAt_rdSt]
    step dupR 1
    step mstoreApp (by code_fact) (by code_fact) (by rw [sz, toNat_wd (by omega)])
      (by rw [sz]; omega) (by rw [sz, e1]; gas_ok)
    rw [sz, e1]
    step swapR 0
    norm
    step pushR 1 (1 : U256)
    step binR 0x01 instruction_add
    rw [slotJ_succ]
    step swapR 0
    norm
    step pushR 1 (0x20 : U256)
    step binR 0x01 instruction_add
    rw [add20]
    step dupR 0
    step dupR 3
    step binR 0x11 Local.instruction_gt
    step pushAnyR 2
    step jumpiR (gt_ne (by omega) (by omega))
    exact restate (by decide) (by rw [e1]) (by rw [cat, ByteArray.append_assoc]) (by gas_ok) rfl rfl

/-- The last round of the storage loop (`N ≤ 32 (j + 1)`), then the exit to the return block. -/
theorem roundX {b r : Nat} {k : U256} (hp : (b, k, r) ∈ BODY) (hfork : .berlin ≤ fork)
    {S : State.TransactionState} {ss : Substate} {h : U256} {p N j : Nat} (hj : N ≤ 32 * (j + 1))
    (hj' : 32 * (j + 1) < 2 ^ 210) {x : U256} {gas : Nat}
    (hg : 96 + slotCost (coldIn (rdSs ss message.currentTarget h j) message.currentTarget (slotJ h j)) +
      (mg (128 + 32 * (j + 1)) - mg (128 + 32 * j)) ≤ gas) :
    Gas.HoareG fork (At CODE message (b + 121) (sStk h N j k (BitVec.ofNat 256 r) x)
        (MEMK p N k ++ cat (fun i => storageAt S message.currentTarget (slotJ h i)) j) gas
        (rdSt S message.currentTarget h j) (rdSs ss message.currentTarget h j))
      (At CODE message r [0x60, BitVec.ofNat 256 r, x]
        (MEMK p N k ++ cat (fun i => storageAt S message.currentTarget (slotJ h i)) (j + 1))
        (gas - (96 + slotCost (coldIn (rdSs ss message.currentTarget h j) message.currentTarget
          (slotJ h j)) + (mg (128 + 32 * (j + 1)) - mg (128 + 32 * j))))
        (rdSt S message.currentTarget h (j + 1)) (rdSs ss message.currentTarget h (j + 1))) := by
  have sz : (MEMK p N k ++ cat (fun i => storageAt S message.currentTarget (slotJ h i)) j).size =
      128 + 32 * j := by rw [ByteArray.size_append, size_MEMK, size_cat]
  have e1 : 128 + 32 * j + 32 = 128 + 32 * (j + 1) := by omega
  simp only [sStk]
  simp only [BODY, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hp
  rcases hp with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  all_goals
    step jumpdestR
    step dupR 1
    step Gas.sloadG hfork (cold := coldIn (rdSs ss message.currentTarget h j) message.currentTarget
      (slotJ h j)) (by code_fact) (by code_fact) rfl (by gas_ok)
    rw [getStorage_eq, storageAt_rdSt]
    step dupR 1
    step mstoreApp (by code_fact) (by code_fact) (by rw [sz, toNat_wd (by omega)])
      (by rw [sz]; omega) (by rw [sz, e1]; gas_ok)
    rw [sz, e1]
    step swapR 0
    norm
    step pushR 1 (1 : U256)
    step binR 0x01 instruction_add
    step swapR 0
    norm
    step pushR 1 (0x20 : U256)
    step binR 0x01 instruction_add
    rw [add20]
    step dupR 0
    step dupR 3
    step binR 0x11 Local.instruction_gt
    step pushAnyR 2
    step jumpi0R (gt_eq (by omega) (by omega))
    step dupR 2
    step swapR 0
    norm
    step binR 0x03 instruction_sub
    step pushR 1 (0x1f : U256)
    step binR 0x16 Local.instruction_and
    step dupR 2
    step binR 0x01 instruction_add
    step swapR 1
    norm
    first | at_pc 2638 | at_pc 5356
    step jumpdestR
    step popR
    step popR
    step popR
    step popR
    step popR
    step dupR 1
    step jumpR
    exact restate (by decide) rfl (by rw [cat, ByteArray.append_assoc]) (by gas_ok) rfl rfl

/-- The storage loop from round `j` to its end (`j + d + 1 = W` rounds in all), then the exit. -/
theorem loopL {b r : Nat} {k : U256} (hp : (b, k, r) ∈ BODY) (hfork : .berlin ≤ fork)
    {S : State.TransactionState} {ss : Substate} {h : U256} {p N W : Nat}
    (hW : W = (N + 31) / 32) (hN : N < 2 ^ 200) {x : U256} :
    ∀ (d j gas : Nat), j + d + 1 = W →
    50 * d + 96 + (rdGas ss message.currentTarget h W - rdGas ss message.currentTarget h j) +
      (mg (128 + 32 * W) - mg (128 + 32 * j)) ≤ gas →
    Gas.HoareG fork (At CODE message (b + 121) (sStk h N j k (BitVec.ofNat 256 r) x)
        (MEMK p N k ++ cat (fun i => storageAt S message.currentTarget (slotJ h i)) j) gas
        (rdSt S message.currentTarget h j) (rdSs ss message.currentTarget h j))
      (At CODE message r [0x60, BitVec.ofNat 256 r, x]
        (MEMK p N k ++ cat (fun i => storageAt S message.currentTarget (slotJ h i)) W)
        (gas - (50 * d + 96 + (rdGas ss message.currentTarget h W - rdGas ss message.currentTarget h j) +
          (mg (128 + 32 * W) - mg (128 + 32 * j))))
        (rdSt S message.currentTarget h W) (rdSs ss message.currentTarget h W)) := by
  intro d
  induction d with
  | zero =>
    intro j gas hj hg
    have hW' : W = j + 1 := by omega
    subst hW'
    have hr : rdGas ss message.currentTarget h (j + 1) = rdGas ss message.currentTarget h j +
        slotCost (coldIn (rdSs ss message.currentTarget h j) message.currentTarget (slotJ h j)) := rfl
    rw [hr] at hg ⊢
    refine (roundX hp hfork (S := S) (p := p) (by omega) (by omega) (gas := gas) (by omega)).seq ?_
    exact restate rfl rfl rfl (by omega) rfl rfl
  | succ d ih =>
    intro j gas hj hg
    have m1 : mg (128 + 32 * j) ≤ mg (128 + 32 * (j + 1)) := memoryGasCost_mono (by omega)
    have m2 : mg (128 + 32 * (j + 1)) ≤ mg (128 + 32 * W) := memoryGasCost_mono (by omega)
    have r1 : rdGas ss message.currentTarget h (j + 1) = rdGas ss message.currentTarget h j +
        slotCost (coldIn (rdSs ss message.currentTarget h j) message.currentTarget (slotJ h j)) := rfl
    have r2 := rdGas_le ss message.currentTarget h (show j + 1 ≤ W by omega)
    refine (roundC hp hfork (S := S) (p := p) (by omega) hN (gas := gas) (by omega)).seq ?_
    refine (ih (j + 1) _ (by omega) (by omega)).seq ?_
    exact restate rfl rfl rfl (by omega) rfl rfl

theorem read_cat (A : ByteArray) (f : Nat → U256) :
    ∀ W i, i < W → loadWord (memoryReadBytes (A ++ cat f W) (A.size + 32 * i) 32) 0 32 = f i
  | 0, _, hi => absurd hi (Nat.not_lt_zero _)
  | W + 1, i, hi => by
    rw [cat, ← ByteArray.append_assoc]
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with h | h
    · rw [read_left (by rw [ByteArray.size_append, size_cat]; omega)]
      exact read_cat A f W i h
    · subst h
      have e := read_right (A := A ++ cat f i) (B := wordBytes (f i)) (s := A.size + 32 * i)
        (by rw [ByteArray.size_append, size_cat])
      rw [size_wordBytes] at e
      rw [e, ld]

/-- From pc 0 to the head of the storage loop, for a slot word in the long form. -/
theorem preLong (hfork : .berlin ≤ fork) {sel t e r b : Nat} {k : U256}
    (hp : (sel, t, e, r, b, k) ∈ STR_GETTERS) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = sel)
    (hv : message.value = 0)
    (hodd : (storageAt state message.currentTarget k).toNat % 2 = 1) {N : Nat}
    (hNw : (storageAt state message.currentTarget k).toNat / 2 = N) (h32 : 32 ≤ N)
    (hN : N < 2 ^ 180) {ck : Bool}
    (hck : coldIn substate message.currentTarget k = ck) {gas : Nat}
    (hg : 62 + 22 * t + 34 + (102 + slotCost ck) + 281 ≤ gas) :
    Gas.HoareG fork (At CODE message 0 [] .empty gas state substate)
      (At CODE message (b + 121) (sStk (keccak (wordBytes k)) N 0 k (BitVec.ofNat 256 r)
          (BitVec.ofNat 256 sel))
        (MEMK (128 + 32 * ((N + 31) / 32)) N k ++
          cat (fun i => storageAt (readSlot state message.currentTarget k) message.currentTarget
            (slotJ (keccak (wordBytes k)) i)) 0)
        (gas - (62 + 22 * t + 34 + (102 + slotCost ck) + 281))
        (rdSt (readSlot state message.currentTarget k) message.currentTarget (keccak (wordBytes k)) 0)
        (rdSs (accessSlot substate message.currentTarget k) message.currentTarget
          (keccak (wordBytes k)) 0)) := by
  have hpe : (e, r, b, k) ∈ STR := by
    simp only [STR_GETTERS, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hp
    rcases hp with ⟨-, -, rfl, rfl, rfl, rfl⟩ | ⟨-, -, rfl, rfl, rfl, rfl⟩ <;> decide
  have hpb : (b, k, r) ∈ BODY := by
    simp only [STR_GETTERS, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hp
    rcases hp with ⟨-, -, -, rfl, rfl, rfl⟩ | ⟨-, -, -, rfl, rfl, rfl⟩ <;> decide
  have ht : tested (BitVec.ofNat 256 sel) ENTRIES = t ∧
      branch (BitVec.ofNat 256 sel) 54 (entrySize 4 2) ENTRIES = e := by
    simp only [STR_GETTERS, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hp
    rcases hp with ⟨rfl, rfl, rfl, -, -, -⟩ | ⟨rfl, rfl, rfl, -, -, -⟩ <;> decide
  have hL : lenOf (storageAt state message.currentTarget k) = wd N := by
    rw [lenOf_long hodd, hNw]
  have hL2 : lenOf (storageAt (readSlot state message.currentTarget k) message.currentTarget k) =
      wd N := by rw [storageAt_readSlot]; exact hL
  have hc2 : coldIn (accessSlot substate message.currentTarget k) message.currentTarget k =
      false := coldIn_accessSlot_self _ _ _
  have hP : 32 + 32 * ((N + 31) / 32) + 96 = 128 + 32 * ((N + 31) / 32) := by omega
  refine ((toEntry ht hsize hsize' hsel (by omega)).seq
    ((entryS hpe hv (by omega)).seq (body1G hpb hfork hL (by omega) hck (by omega)))).seq ?_
  rw [hP]
  refine (body2L (p := 128 + 32 * ((N + 31) / 32)) hpb hfork hL2 h32 (by omega) hc2
    (by omega)).seq ?_
  rw [readSlot_readSlot, accessSlot_accessSlot]
  exact restate rfl (by simp only [sStk, slotJ_zero, hsel, Nat.mul_zero, Nat.add_zero]) (by rw [cat, ByteArray.append_empty])
    (by omega) rfl rfl

/-- The specification of `name()` / `symbol()` for a string in the long form: the slot word `w`
of slot `k` is odd and `N = w / 2 ≥ 32` (Solidity stores such a string as `2 N + 1`, its bytes
from slot `keccak(k)` on). The run returns the word 0x20, the word `N`, and `strData` of the
words of the slots `keccak(k) + i` (`slotJ`): the first `N` bytes of their concatenation, padded
with zeros to a multiple of 32. It reads slot `k` twice and the `ceil(N / 32)` data slots once
each, in order (`rdSt`, `rdSs`, priced by `rdGas`). `N < 2^180` is a hypothesis. -/
theorem spec_strLong (hfork : .berlin ≤ fork) {sel t e r b : Nat} {k : U256}
    (hp : (sel, t, e, r, b, k) ∈ STR_GETTERS) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = sel)
    (hv : message.value = 0)
    (hodd : (storageAt state message.currentTarget k).toNat % 2 = 1) {N : Nat}
    (hNw : (storageAt state message.currentTarget k).toNat / 2 = N) (h32 : 32 ≤ N)
    (hN : N < 2 ^ 180) {ck : Bool}
    (hck : coldIn substate message.currentTarget k = ck) {gas : Nat}
    (hg : 62 + 22 * t + 34 + (102 + slotCost ck) + 281 +
      (50 * ((N + 31) / 32 - 1) + 96 +
        rdGas (accessSlot substate message.currentTarget k) message.currentTarget
          (keccak (wordBytes k)) ((N + 31) / 32) +
        (mg (128 + 32 * ((N + 31) / 32)) - mg 128)) +
      retCost (128 + 32 * ((N + 31) / 32)) N ≤ gas) :
    Gas.SpecG fork (At CODE message 0 [] .empty gas state substate)
      (Halted false (wordBytes 0x20 ++ wordBytes (wd N) ++
          strData (fun i => storageAt state message.currentTarget (slotJ (keccak (wordBytes k)) i)) N)
        (gas - (62 + 22 * t + 34 + (102 + slotCost ck) + 281 +
          (50 * ((N + 31) / 32 - 1) + 96 +
            rdGas (accessSlot substate message.currentTarget k) message.currentTarget
              (keccak (wordBytes k)) ((N + 31) / 32) +
            (mg (128 + 32 * ((N + 31) / 32)) - mg 128)) +
          retCost (128 + 32 * ((N + 31) / 32)) N))
        (rdSt (readSlot state message.currentTarget k) message.currentTarget (keccak (wordBytes k))
          ((N + 31) / 32))
        (rdSs (accessSlot substate message.currentTarget k) message.currentTarget
          (keccak (wordBytes k)) ((N + 31) / 32))) := by
  have hpb : (b, k, r) ∈ BODY := by
    simp only [STR_GETTERS, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hp
    rcases hp with ⟨-, -, -, rfl, rfl, rfl⟩ | ⟨-, -, -, rfl, rfl, rfl⟩ <;> decide
  have hpr : r ∈ RETS := by
    simp only [STR_GETTERS, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hp
    rcases hp with ⟨-, -, -, rfl, -, -⟩ | ⟨-, -, -, rfl, -, -⟩ <;> decide
  have hpre := preLong hfork hp hsize hsize' hsel hv hodd hNw h32 hN hck (gas := gas) (by omega)
  have hdw : (fun i => storageAt state message.currentTarget (slotJ (keccak (wordBytes k)) i)) =
      (fun i => storageAt (readSlot state message.currentTarget k) message.currentTarget
        (slotJ (keccak (wordBytes k)) i)) := by
    funext i; rw [storageAt_readSlot]
  rw [hdw]
  generalize hWd : (N + 31) / 32 = W at hg hpre ⊢
  generalize readSlot state message.currentTarget k = S at hpre ⊢
  generalize hss : accessSlot substate message.currentTarget k = ss at hg hpre ⊢
  generalize keccak (wordBytes k) = h at hg hpre ⊢
  have hW1 : 1 ≤ W := by omega
  have m0 : mg 128 ≤ mg (128 + 32 * W) := memoryGasCost_mono (by omega)
  have g0 := rdGas_le ss message.currentTarget h (Nat.zero_le W)
  have r0 : rdGas ss message.currentTarget h 0 = 0 := rfl
  refine Gas.SpecG.seq hpre ?_
  refine Gas.SpecG.seq (loopL (W := W) (S := S) (ss := ss) (h := h) hpb hfork hWd.symm (by omega)
    (W - 1) 0 _ (by omega) (by simp only [Nat.mul_zero, Nat.add_zero, r0]; omega)) ?_
  have sM : (MEMK (128 + 32 * W) N k ++
      cat (fun i => storageAt S message.currentTarget (slotJ h i)) W).size = 128 + 32 * W := by
    rw [ByteArray.size_append, size_MEMK, size_cat]
  refine (retG hfork hpr sM (by omega) (by rw [hWd]; exact Nat.le_refl _) (by omega) (by omega)
    (by rw [read_left (by rw [size_MEMK] <;> omega)]; exact ptr_MEMK _ _ _)
    (by rw [read_left (by rw [size_MEMK] <;> omega)]; exact len_MEMK _ _ _)
    (by
      intro i hi
      have := read_cat (MEMK (128 + 32 * W) N k)
        (fun i => storageAt S message.currentTarget (slotJ h i)) W i (by omega)
      simpa [size_MEMK] using this)
    (by simp only [Nat.mul_zero, Nat.add_zero, r0] at *; omega)).consequence (fun _ h => h) ?_
  rintro evm ⟨hr, he, ho, hgas, hs, hss'⟩
  refine ⟨hr, he, ho, by rw [hgas]; simp only [Nat.mul_zero, Nat.add_zero, r0]; omega, hs, hss'⟩

/-- `name()` for the empty string (low byte of slot 7 is 0): returns the word 0x20 and the word 0. -/
theorem spec_nameEmpty (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x06fdde03)
    (hv : message.value = 0) (hn : (storageAt state message.currentTarget 7).toNat % 256 = 0)
    {c : Bool} (hc : coldIn substate message.currentTarget 7 = c) {gas : Nat}
    (hg : 643 + slotCost c ≤ gas) :
    Gas.SpecG fork (At CODE message 0 [] .empty gas state substate)
      (Halted false (wordBytes 0x20 ++ wordBytes 0) (gas - (643 + slotCost c))
        (readSlot state message.currentTarget 7) (accessSlot substate message.currentTarget 7)) := by
  have hr : retCost 128 0 = 206 := by decide
  have h := spec_strEmpty (t := 1) (e := 411) (r := 430) (b := 2488) hfork (by decide) hsize hsize'
    hsel hv hn hc (gas := gas) (by rw [hr]; omega)
  rw [hr] at h
  refine h.consequence (fun _ h => h) ?_
  rintro evm ⟨h1, h2, h3, h4, h5, h6⟩
  exact ⟨h1, h2, h3, by rw [h4]; omega, h5, h6⟩

/-- `name()` for a string of `N ≥ 32` bytes in the long form (slot 7 holds `2 N + 1`). -/
theorem spec_nameLong (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x06fdde03)
    (hv : message.value = 0)
    (hodd : (storageAt state message.currentTarget 7).toNat % 2 = 1) {N : Nat}
    (hNw : (storageAt state message.currentTarget 7).toNat / 2 = N) (h32 : 32 ≤ N)
    (hN : N < 2 ^ 180) {c : Bool} (hc : coldIn substate message.currentTarget 7 = c) {gas : Nat}
    (hg : 62 + 22 * 1 + 34 + (102 + slotCost c) + 281 +
      (50 * ((N + 31) / 32 - 1) + 96 +
        rdGas (accessSlot substate message.currentTarget 7) message.currentTarget
          (keccak (wordBytes 7)) ((N + 31) / 32) +
        (mg (128 + 32 * ((N + 31) / 32)) - mg 128)) +
      retCost (128 + 32 * ((N + 31) / 32)) N ≤ gas) :
    Gas.SpecG fork (At CODE message 0 [] .empty gas state substate)
      (Halted false (wordBytes 0x20 ++ wordBytes (wd N) ++
          strData (fun i => storageAt state message.currentTarget (slotJ (keccak (wordBytes 7)) i)) N)
        (gas - (62 + 22 * 1 + 34 + (102 + slotCost c) + 281 +
          (50 * ((N + 31) / 32 - 1) + 96 +
            rdGas (accessSlot substate message.currentTarget 7) message.currentTarget
              (keccak (wordBytes 7)) ((N + 31) / 32) +
            (mg (128 + 32 * ((N + 31) / 32)) - mg 128)) +
          retCost (128 + 32 * ((N + 31) / 32)) N))
        (rdSt (readSlot state message.currentTarget 7) message.currentTarget (keccak (wordBytes 7))
          ((N + 31) / 32))
        (rdSs (accessSlot substate message.currentTarget 7) message.currentTarget
          (keccak (wordBytes 7)) ((N + 31) / 32))) :=
  spec_strLong (t := 1) (e := 411) (r := 430) (b := 2488) hfork (by decide) hsize hsize' hsel hv hodd
    hNw h32 hN hc hg

/-- `symbol()` for the empty string (low byte of slot 8 is 0): returns the word 0x20 and the word 0. -/
theorem spec_symbolEmpty (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x95d89b41)
    (hv : message.value = 0) (hn : (storageAt state message.currentTarget 8).toNat % 256 = 0)
    {c : Bool} (hc : coldIn substate message.currentTarget 8 = c) {gas : Nat}
    (hg : 1083 + slotCost c ≤ gas) :
    Gas.SpecG fork (At CODE message 0 [] .empty gas state substate)
      (Halted false (wordBytes 0x20 ++ wordBytes 0) (gas - (1083 + slotCost c))
        (readSlot state message.currentTarget 8) (accessSlot substate message.currentTarget 8)) := by
  have hr : retCost 128 0 = 206 := by decide
  have h := spec_strEmpty (t := 21) (e := 1724) (r := 1743) (b := 5206) hfork (by decide) hsize hsize'
    hsel hv hn hc (gas := gas) (by rw [hr]; omega)
  rw [hr] at h
  refine h.consequence (fun _ h => h) ?_
  rintro evm ⟨h1, h2, h3, h4, h5, h6⟩
  exact ⟨h1, h2, h3, by rw [h4]; omega, h5, h6⟩

/-- `symbol()` for a string of `N ≥ 32` bytes in the long form (slot 8 holds `2 N + 1`). -/
theorem spec_symbolLong (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x95d89b41)
    (hv : message.value = 0)
    (hodd : (storageAt state message.currentTarget 8).toNat % 2 = 1) {N : Nat}
    (hNw : (storageAt state message.currentTarget 8).toNat / 2 = N) (h32 : 32 ≤ N)
    (hN : N < 2 ^ 180) {c : Bool} (hc : coldIn substate message.currentTarget 8 = c) {gas : Nat}
    (hg : 62 + 22 * 21 + 34 + (102 + slotCost c) + 281 +
      (50 * ((N + 31) / 32 - 1) + 96 +
        rdGas (accessSlot substate message.currentTarget 8) message.currentTarget
          (keccak (wordBytes 8)) ((N + 31) / 32) +
        (mg (128 + 32 * ((N + 31) / 32)) - mg 128)) +
      retCost (128 + 32 * ((N + 31) / 32)) N ≤ gas) :
    Gas.SpecG fork (At CODE message 0 [] .empty gas state substate)
      (Halted false (wordBytes 0x20 ++ wordBytes (wd N) ++
          strData (fun i => storageAt state message.currentTarget (slotJ (keccak (wordBytes 8)) i)) N)
        (gas - (62 + 22 * 21 + 34 + (102 + slotCost c) + 281 +
          (50 * ((N + 31) / 32 - 1) + 96 +
            rdGas (accessSlot substate message.currentTarget 8) message.currentTarget
              (keccak (wordBytes 8)) ((N + 31) / 32) +
            (mg (128 + 32 * ((N + 31) / 32)) - mg 128)) +
          retCost (128 + 32 * ((N + 31) / 32)) N))
        (rdSt (readSlot state message.currentTarget 8) message.currentTarget (keccak (wordBytes 8))
          ((N + 31) / 32))
        (rdSs (accessSlot substate message.currentTarget 8) message.currentTarget
          (keccak (wordBytes 8)) ((N + 31) / 32))) :=
  spec_strLong (t := 21) (e := 1724) (r := 1743) (b := 5206) hfork (by decide) hsize hsize' hsel hv hodd
    hNw h32 hN hc hg

/-- `spec_nameEmpty` for the interpreter loop `runFrame`. -/
theorem runFrame_nameEmpty (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x06fdde03)
    (hv : message.value = 0) (hn : (storageAt state message.currentTarget 7).toNat % 256 = 0)
    {c : Bool} (hc : coldIn substate message.currentTarget 7 = c) {gas : Nat}
    (hg : 643 + slotCost c ≤ gas)
    {bound : Nat} {runChild : MessageRunner fork Nat bound} {evm : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    ∃ stopped, runFrame (step fork) (step_decreases fork) bound runChild evm within =
      .ok stopped ∧
      (Halted false (wordBytes 0x20 ++ wordBytes 0) (gas - (643 + slotCost c))
        (readSlot state message.currentTarget 7) (accessSlot substate message.currentTarget 7))
        stopped :=
  (spec_nameEmpty hfork hsize hsize' hsel hv hn hc hg).runFrame start within

/-- `spec_nameLong` for the interpreter loop `runFrame`. -/
theorem runFrame_nameLong (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x06fdde03)
    (hv : message.value = 0)
    (hodd : (storageAt state message.currentTarget 7).toNat % 2 = 1) {N : Nat}
    (hNw : (storageAt state message.currentTarget 7).toNat / 2 = N) (h32 : 32 ≤ N)
    (hN : N < 2 ^ 180) {c : Bool} (hc : coldIn substate message.currentTarget 7 = c) {gas : Nat}
    (hg : 62 + 22 * 1 + 34 + (102 + slotCost c) + 281 +
      (50 * ((N + 31) / 32 - 1) + 96 +
        rdGas (accessSlot substate message.currentTarget 7) message.currentTarget
          (keccak (wordBytes 7)) ((N + 31) / 32) +
        (mg (128 + 32 * ((N + 31) / 32)) - mg 128)) +
      retCost (128 + 32 * ((N + 31) / 32)) N ≤ gas)
    {bound : Nat} {runChild : MessageRunner fork Nat bound} {evm : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    ∃ stopped, runFrame (step fork) (step_decreases fork) bound runChild evm within =
      .ok stopped ∧
      (Halted false (wordBytes 0x20 ++ wordBytes (wd N) ++
          strData (fun i => storageAt state message.currentTarget (slotJ (keccak (wordBytes 7)) i)) N)
        (gas - (62 + 22 * 1 + 34 + (102 + slotCost c) + 281 +
          (50 * ((N + 31) / 32 - 1) + 96 +
            rdGas (accessSlot substate message.currentTarget 7) message.currentTarget
              (keccak (wordBytes 7)) ((N + 31) / 32) +
            (mg (128 + 32 * ((N + 31) / 32)) - mg 128)) +
          retCost (128 + 32 * ((N + 31) / 32)) N))
        (rdSt (readSlot state message.currentTarget 7) message.currentTarget (keccak (wordBytes 7))
          ((N + 31) / 32))
        (rdSs (accessSlot substate message.currentTarget 7) message.currentTarget
          (keccak (wordBytes 7)) ((N + 31) / 32))) stopped :=
  (spec_nameLong hfork hsize hsize' hsel hv hodd hNw h32 hN hc hg).runFrame start within

/-- `spec_symbolEmpty` for the interpreter loop `runFrame`. -/
theorem runFrame_symbolEmpty (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x95d89b41)
    (hv : message.value = 0) (hn : (storageAt state message.currentTarget 8).toNat % 256 = 0)
    {c : Bool} (hc : coldIn substate message.currentTarget 8 = c) {gas : Nat}
    (hg : 1083 + slotCost c ≤ gas)
    {bound : Nat} {runChild : MessageRunner fork Nat bound} {evm : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    ∃ stopped, runFrame (step fork) (step_decreases fork) bound runChild evm within =
      .ok stopped ∧
      (Halted false (wordBytes 0x20 ++ wordBytes 0) (gas - (1083 + slotCost c))
        (readSlot state message.currentTarget 8) (accessSlot substate message.currentTarget 8))
        stopped :=
  (spec_symbolEmpty hfork hsize hsize' hsel hv hn hc hg).runFrame start within

/-- `spec_symbolLong` for the interpreter loop `runFrame`. -/
theorem runFrame_symbolLong (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x95d89b41)
    (hv : message.value = 0)
    (hodd : (storageAt state message.currentTarget 8).toNat % 2 = 1) {N : Nat}
    (hNw : (storageAt state message.currentTarget 8).toNat / 2 = N) (h32 : 32 ≤ N)
    (hN : N < 2 ^ 180) {c : Bool} (hc : coldIn substate message.currentTarget 8 = c) {gas : Nat}
    (hg : 62 + 22 * 21 + 34 + (102 + slotCost c) + 281 +
      (50 * ((N + 31) / 32 - 1) + 96 +
        rdGas (accessSlot substate message.currentTarget 8) message.currentTarget
          (keccak (wordBytes 8)) ((N + 31) / 32) +
        (mg (128 + 32 * ((N + 31) / 32)) - mg 128)) +
      retCost (128 + 32 * ((N + 31) / 32)) N ≤ gas)
    {bound : Nat} {runChild : MessageRunner fork Nat bound} {evm : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    ∃ stopped, runFrame (step fork) (step_decreases fork) bound runChild evm within =
      .ok stopped ∧
      (Halted false (wordBytes 0x20 ++ wordBytes (wd N) ++
          strData (fun i => storageAt state message.currentTarget (slotJ (keccak (wordBytes 8)) i)) N)
        (gas - (62 + 22 * 21 + 34 + (102 + slotCost c) + 281 +
          (50 * ((N + 31) / 32 - 1) + 96 +
            rdGas (accessSlot substate message.currentTarget 8) message.currentTarget
              (keccak (wordBytes 8)) ((N + 31) / 32) +
            (mg (128 + 32 * ((N + 31) / 32)) - mg 128)) +
          retCost (128 + 32 * ((N + 31) / 32)) N))
        (rdSt (readSlot state message.currentTarget 8) message.currentTarget (keccak (wordBytes 8))
          ((N + 31) / 32))
        (rdSs (accessSlot substate message.currentTarget 8) message.currentTarget
          (keccak (wordBytes 8)) ((N + 31) / 32))) stopped :=
  (spec_symbolLong hfork hsize hsize' hsel hv hodd hNw h32 hN hc hg).runFrame start within

end UsdtVerify.StringsGen

end
