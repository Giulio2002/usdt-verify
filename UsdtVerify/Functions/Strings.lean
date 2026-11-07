import UsdtVerify.Functions.Getters
import EthLib.Execution.Proofs.Evm.PowMod

/-!
# name() and symbol(): the string getters

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

Not covered: the empty string and strings of 32 bytes or more (the long form: the loop over
`keccak(slot)` at 2595).
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
    Hoare fork (At CODE message e [x] M gas state substate)
      (At CODE message b [BitVec.ofNat 256 r, x] M (gas - 34) state substate) := by
  simp only [STR, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hp
  rcases hp with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
  all_goals
    step jumpdestR
    step Logic.callvalue (by code_fact) (by code_fact) (by gas_ok) (by stk_ok)
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
    Hoare fork (At CODE message b [y, x] MEM0 gas state substate)
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
    step sload hfork (cold := ck) (by code_fact) (by code_fact) hck (by gas_ok)
    rw [getStorage_eq]
    step pushR 1 (1 : U256)
    step dupR 1
    step pushR 1 (1 : U256)
    step binR 0x16 Local.instruction_and
    step unR 0x15 instruction_iszero
    step pushR 2 (0x0100 : U256)
    step binR 0x02 Local.instruction_mul
    step binR 0x03 Local.instruction_sub
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
    step reshape (s' := [64, BitVec.ofNat 256 n, _, _, x]) (g' := gas - (81 + slotCost ck))
      (by rw [roundWord h1 h31]) rfl (by gas_ok)
    -- the free pointer: 0x60, moved to 0xa0
    step pushR 1 (0x40 : U256)
    have hext0 : extendMemory MEM0.size [((0x40 : U256), (32 : U256))] = ⟨0, 0⟩ := by
      rw [size_MEM0]; decide
    step mload (by code_fact) (by code_fact) (by rw [hext0]; gas_ok)
    step reshape (s' := [0x60, 64, BitVec.ofNat 256 n, _, _, x]) (m' := MEM0)
      (g' := gas - (87 + slotCost ck))
      (by rw [hext0, memoryExtend_zero]; exact congrArg (· :: _) mload_MEM0)
      (by rw [hext0, memoryExtend_zero]) (by rw [hext0]; gas_ok)
    step swapR 0
    norm
    step dupR 1
    step binR 0x01 instruction_add
    step pushR 1 (0x40 : U256)
    step mstore (by code_fact) (by code_fact) (by rw [hext0]; gas_ok)
    step reshape (s' := [0x60, BitVec.ofNat 256 n, _, _, x]) (m' := MEM1)
      (g' := gas - (102 + slotCost ck)) rfl
      (by rw [hext0, memoryExtend_zero]; rfl) (by rw [hext0]; gas_ok)
    exact restate (by decide) rfl rfl rfl rfl rfl

/-- The length written at 0x60, the second read of the slot (warm), the two length tests. -/
theorem body2 {b r : Nat} {k : U256} (hp : (b, k, r) ∈ BODY) (hfork : .berlin ≤ fork) {n : Nat}
    (hn : (storageAt state message.currentTarget k).toNat % 256 = 2 * n)
    (h1 : 1 ≤ n) (h31 : n ≤ 31)
    (hck : coldIn substate message.currentTarget k = false) {x y : U256}
    {gas : Nat} (hg : 217 ≤ gas) :
    Hoare fork (At CODE message (b + 44) [0x60, BitVec.ofNat 256 n, k, y, x] MEM1 gas state
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
    step mstore (by code_fact) (by code_fact) (by rw [hext1]; gas_ok)
    have hm1 : memoryWrite (memoryExtend MEM1 32) (0x60 : U256).toNat
        (wordBytes (BitVec.ofNat 256 n)) = MEM1 ++ wordBytes (BitVec.ofNat 256 n) := by
      have h := memoryWrite_extend_end (memory := MEM1) (value := wordBytes (BitVec.ofNat 256 n))
      rwa [size_wordBytes, size_MEM1] at h
    step reshape (m' := MEM1 ++ wordBytes (BitVec.ofNat 256 n)) (g' := gas - 24)
      rfl (by rw [hext1]; exact hm1) (by rw [hext1]; gas_ok)
    step pushR 1 (0x20 : U256)
    step binR 0x01 instruction_add
    step reshape (s' := [0x80, BitVec.ofNat 256 n, _, 0x60, _, x]) rfl rfl rfl
    -- the second read of the slot (warm), the length again
    step dupR 2
    step dupR 0
    step sload hfork (cold := false) (by code_fact) (by code_fact) hck
      (by gas_ok)
    rw [getStorage_eq]
    step pushR 1 (1 : U256)
    step dupR 1
    step pushR 1 (1 : U256)
    step binR 0x16 Local.instruction_and
    step unR 0x15 instruction_iszero
    step pushR 2 (0x0100 : U256)
    step binR 0x02 Local.instruction_mul
    step binR 0x03 Local.instruction_sub
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
    Hoare fork (At CODE message (b + 88)
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
    step sload hfork (cold := false) (by code_fact) (by code_fact) hck
      (by gas_ok)
    rw [getStorage_eq]
    step binR 0x04 Local.instruction_div
    step binR 0x02 Local.instruction_mul
    step dupR 3
    have hext2 : extendMemory (MEM1 ++ wordBytes (BitVec.ofNat 256 n)).size
        [((0x80 : U256), (32 : U256))] = ⟨3, 32⟩ := by
      rw [ByteArray.size_append, size_MEM1, size_wordBytes]; decide
    step mstore (by code_fact) (by code_fact) (by rw [hext2]; gas_ok)
    step reshape (m' := MEMB n (mul (div (storageAt state message.currentTarget _) 0x100) 0x100))
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
    Hoare fork (At CODE message r [0x60, y, x] (MEMB n v) gas state substate)
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
    step mload (by code_fact) (by code_fact) (by rw [e0]; gas_ok)
    step reshape (s' := [0xa0, 0x60, y, x]) (m' := MEMB n v) (g' := gas - 7)
      (by rw [e0, memoryExtend_zero, ptr_MEMB]) (by rw [e0, memoryExtend_zero]) (by rw [e0]; gas_ok)
    step dupR 0
    step dupR 0
    step pushR 1 (0x20 : U256)
    step binR 0x01 instruction_add
    step reshape (s' := [0xc0, 0xa0, 0xa0, 0x60, y, x]) rfl rfl rfl
    step dupR 2
    step dupR 1
    step binR 0x03 Local.instruction_sub
    step reshape (s' := [0x20, 0xc0, 0xa0, 0xa0, 0x60, y, x]) rfl rfl rfl
    step dupR 2
    step mstore (by code_fact) (by code_fact) (by rw [e1]; gas_ok)
    step reshape (m' := MEMC n v) (g' := gas - 37) rfl
      (by rw [e1]; exact write_end (by rw [size_MEMB]; rfl) _) (by rw [e1]; gas_ok)
    step dupR 3
    step dupR 1
    step dupR 1
    step mload (by code_fact) (by code_fact) (by rw [e2]; gas_ok)
    step reshape (s' := [BitVec.ofNat 256 n, 0xc0, 0x60, 0xc0, 0xa0, 0xa0, 0x60, y, x])
      (m' := MEMC n v) (g' := gas - 49)
      (by rw [e2, memoryExtend_zero, len_MEMC]) (by rw [e2, memoryExtend_zero]) (by rw [e2]; gas_ok)
    step dupR 1
    step mstore (by code_fact) (by code_fact) (by rw [e3]; gas_ok)
    step reshape (m' := MEMD n v) (g' := gas - 58) rfl
      (by rw [e3]; exact write_end (by rw [size_MEMC]; rfl) _) (by rw [e3]; gas_ok)
    step pushR 1 (0x20 : U256)
    step binR 0x01 instruction_add
    step reshape (s' := [0xe0, 0x60, 0xc0, 0xa0, 0xa0, 0x60, y, x]) rfl rfl rfl
    step swapR 1
    step reshape (s' := [0xc0, 0x60, 0xe0, 0xa0, 0xa0, 0x60, y, x]) rfl rfl rfl
    step popR
    step dupR 0
    step mload (by code_fact) (by code_fact) (by rw [e4]; gas_ok)
    step reshape (s' := [BitVec.ofNat 256 n, 0x60, 0xe0, 0xa0, 0xa0, 0x60, y, x])
      (m' := MEMD n v) (g' := gas - 75)
      (by rw [e4, memoryExtend_zero, len_MEMD]) (by rw [e4, memoryExtend_zero]) (by rw [e4]; gas_ok)
    step swapR 0
    norm
    step pushR 1 (0x20 : U256)
    step binR 0x01 instruction_add
    step reshape (s' := [0x80, BitVec.ofNat 256 n, 0xe0, 0xa0, 0xa0, 0x60, y, x]) rfl rfl rfl
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
    Hoare fork (At CODE message (r + 37) [0, 0x80, 0xe0, BitVec.ofNat 256 n, BitVec.ofNat 256 n,
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
    step reshape (s' := [0x80, 0, 0x80, 0xe0, BitVec.ofNat 256 n, BitVec.ofNat 256 n, 0x80, 0xe0,
      0xa0, 0xa0, 0x60, y, x]) rfl rfl rfl
    step mload (by code_fact) (by code_fact) (by rw [e0]; gas_ok)
    step reshape (s' := [v, 0, 0x80, 0xe0, BitVec.ofNat 256 n, BitVec.ofNat 256 n, 0x80, 0xe0,
      0xa0, 0xa0, 0x60, y, x]) (m' := MEMD n v) (g' := gas - 38)
      (by rw [e0, memoryExtend_zero, data_MEMD]) (by rw [e0, memoryExtend_zero])
      (by rw [e0]; gas_ok)
    step dupR 1
    step dupR 4
    step binR 0x01 instruction_add
    step reshape (s' := [0xe0, v, 0, 0x80, 0xe0, BitVec.ofNat 256 n, BitVec.ofNat 256 n, 0x80, 0xe0,
      0xa0, 0xa0, 0x60, y, x]) rfl rfl rfl
    step mstore (by code_fact) (by code_fact) (by rw [e1]; gas_ok)
    step reshape (m' := MEME n v) (g' := gas - 53) rfl
      (by rw [e1]; exact write_end (by rw [size_MEMD]; rfl) _) (by rw [e1]; gas_ok)
    step pushR 1 (0x20 : U256)
    step dupR 1
    step binR 0x01 instruction_add
    step reshape (s' := [0x20, 0, 0x80, 0xe0, BitVec.ofNat 256 n, BitVec.ofNat 256 n, 0x80, 0xe0,
      0xa0, 0xa0, 0x60, y, x]) rfl rfl rfl
    step swapR 0
    step reshape (s' := [0, 0x20, 0x80, 0xe0, BitVec.ofNat 256 n, BitVec.ofNat 256 n, 0x80, 0xe0,
      0xa0, 0xa0, 0x60, y, x]) rfl rfl rfl
    step popR
    step pushAnyR 2
    step jumpR
    exact restate (by decide) rfl rfl (by gas_ok) rfl rfl

/-- The loop test fails (32 is not below the length), the copy loop ends; the end of the data
`0xe0 + n` and the length's low five bits (`n`, not 0) select the padding branch. -/
theorem retE1 {r : Nat} (hp : r ∈ RETS) {n : Nat} (h1 : 1 ≤ n) (h31 : n ≤ 31) {M : ByteArray}
    {y x : U256} {gas : Nat} (hg : 77 ≤ gas) :
    Hoare fork (At CODE message (r + 37) [0x20, 0x80, 0xe0, BitVec.ofNat 256 n,
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
    Spec fork (At CODE message (r + 84) [BitVec.ofNat 256 n, add (BitVec.ofNat 256 n) 0xe0, 0xa0,
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
    step binR 0x03 Local.instruction_sub
    rw [addSub_n]
    step dupR 0
    step mload (by code_fact) (by code_fact) (by rw [e0]; gas_ok)
    step reshape (s' := [v, 0xe0, BitVec.ofNat 256 n, add (BitVec.ofNat 256 n) 0xe0, 0xa0, 0xa0,
      0x60, y, x]) (m' := MEME n v) (g' := gas - 15)
      (by rw [e0, memoryExtend_zero, copy_MEME]) (by rw [e0, memoryExtend_zero])
      (by rw [e0]; gas_ok)
    step pushR 1 (1 : U256)
    step dupR 3
    step pushR 1 (0x20 : U256)
    step binR 0x03 Local.instruction_sub
    step pushR 2 (0x0100 : U256)
    step Local.exp (Nat.le_trans (by decide) hfork) (by code_fact) (by code_fact)
      (by rw [expBytes' h1 h31]; gas_ok)
    rw [expBytes' h1 h31]
    step binR 0x03 Local.instruction_sub
    step unR 0x19 Local.instruction_not
    step binR 0x16 Local.instruction_and
    step dupR 1
    step mstore (by code_fact) (by code_fact) (by rw [e0]; gas_ok)
    step reshape (s' := [0xe0, BitVec.ofNat 256 n, add (BitVec.ofNat 256 n) 0xe0, 0xa0, 0xa0,
      0x60, y, x]) (m' := memoryWrite (MEME n v) 224 (wordBytes (maskedWord n v)))
      (g' := gas - 105) rfl (by rw [e0, memoryExtend_zero]; rfl) (by rw [e0]; gas_ok)
    step pushR 1 (0x20 : U256)
    step binR 0x01 instruction_add
    step swapR 1
    step reshape (s' := [add (BitVec.ofNat 256 n) 0xe0, BitVec.ofNat 256 n, 0x100, 0xa0, 0xa0,
      0x60, y, x]) rfl rfl rfl
    step popR
    step jumpdestR
    step popR
    step swapR 2
    step reshape (s' := [0x60, 0xa0, 0xa0, 0x100, y, x]) rfl rfl rfl
    step popR
    step popR
    step popR
    step pushR 1 (0x40 : U256)
    step mload (by code_fact) (by code_fact) (by rw [e1]; gas_ok)
    step reshape (s' := [0xa0, 0x100, y, x])
      (m' := memoryWrite (MEME n v) 224 (wordBytes (maskedWord n v))) (g' := gas - 134)
      (by rw [e1, memoryExtend_zero, ptr_MEMF]) (by rw [e1, memoryExtend_zero]) (by rw [e1]; gas_ok)
    step dupR 0
    step swapR 1
    step reshape (s' := [0x100, 0xa0, 0xa0, y, x]) rfl rfl rfl
    step binR 0x03 Local.instruction_sub
    step swapR 0
    step reshape (s' := [0xa0, 0x60, y, x]) rfl rfl rfl
    refine (Logic.«return» (by code_fact) (by code_fact) (by rw [e2]; gas_ok)).consequence
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
    Spec fork (At CODE message 0 [] .empty gas state substate)
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
  refine Spec.seq ((toEntry ht hsize hsize' hsel (by omega)).seq
    ((entryS hpe hv (by omega)).seq (body1 hpb hfork hn h1 h31 hck (by omega)))) ?_
  refine Spec.seq (body2 hpb hfork hn2 h1 h31 hc2 (by omega)) ?_
  rw [readSlot_readSlot, accessSlot_accessSlot]
  refine Spec.seq (body3 hpb hfork hc2 (by omega)) ?_
  rw [readSlot_readSlot, accessSlot_accessSlot, storageAt_readSlot]
  refine Spec.seq (retA hpr (by omega)) ?_
  refine Spec.seq (retL hpr h1 h31 (by omega)) ?_
  refine Spec.seq (retE1 hpr h1 h31 (by omega)) ?_
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
    Spec fork (At CODE message 0 [] .empty gas state substate)
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
    Spec fork (At CODE message 0 [] .empty gas state substate)
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
    Spec fork (At CODE message 0 [] .empty gas state substate)
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
    Spec fork (At CODE message 0 [] .empty gas state substate)
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
