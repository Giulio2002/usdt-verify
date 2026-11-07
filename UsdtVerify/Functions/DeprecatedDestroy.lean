import UsdtVerify.Functions.DestroySpec
import UsdtVerify.Functions.DeprecatedTransfer

/-!
# destroyBlackFunds(a) when deprecated: the internal balanceOf forwards

After the owner check and the `require(isBlackListed[a])`, destroyBlackFunds calls TetherToken's
own `balanceOf(a)` (the getter at 4665, return address 8008). With byte 20 of slot 10 set, that
getter does not read `balances[a]`: it calls `upgradedAddress.balanceOf(a)` (as in
`DeprecatedBalance`) and hands the first word of the answer back to the body at 8008. The body
then writes, in THIS contract, `balances[a] := 0` and `_totalSupply := _totalSupply - d`
(unchecked), where `d` is the word that the upgraded contract answered, and logs
`DestroyedBlackFunds(a, d)`.

- pc 0 → 4665: `DestroySpec.toGetter` (owner, `a` blacklisted; memory `MEMB`, 96 bytes).
- 4665: `depSet` (flag set), 4689 → 4874: `fwdArgsD` (as `fwdArgsB` on any 96-byte memory with
  the free memory pointer 0x60), 4874: `toCall` / `noCode`, CALL at 4891.
- 4892: `failTail` (revert, empty output) or `okTailD` (back to 8008 with the answer word).
- 8008: `zeroBalD` (the write of `balances[a]`, on the 160-byte memory; the slot may be cold, the
  getter did not read it), 8080: `DestroySpec.subTotal`, 8096: `logBlockD` (the log on the
  160-byte memory, no growth).

The state after the call is the callee's (EthLib's `incorporateChild`); the writes are stated
over it. That the account of the contract still exists after the call is an assumption on the
callee (`hkeep`).
-/

namespace UsdtVerify.DeprecatedDestroy

open EthLib.Base (Fork U256 toAddressMasked)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts
open Deprecated DeprecatedBalance DeprecatedTransfer Transfer TransferOk Owner Admin BlackList
  Destroy DestroySpec

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate}

/-! ## The memory of the forward, from any 96-byte memory -/

/-- 0 written at 0x80 (memory grown to 160 bytes). -/
def D1 (M : ByteArray) : ByteArray := memoryWrite (memoryExtend M 64) 128 (wordBytes 0)

/-- Then the selector word of `balanceOf` at 0x60. -/
def D2 (M : ByteArray) : ByteArray := memoryWrite (D1 M) 96 (wordBytes SELWB)

/-- Then the address word at 0x64: the memory before the call. -/
abbrev D3 (M : ByteArray) (a : U256) : ByteArray := memoryWrite (D2 M) 100 (wordBytes a)

theorem selB_prefix : (wordBytes SELWB).extract 0 4 = SEL_B := by decide +kernel

section Mem

variable {M : ByteArray} (hM : M.size = 96) {a : U256}
include hM

theorem size_D1 : (D1 M).size = 160 := by
  rw [D1, size_memoryWrite (by rw [size_wordBytes, size_memoryExtend, hM]; omega), size_memoryExtend, hM]

theorem size_D2 : (D2 M).size = 160 := by
  rw [D2, size_memoryWrite (by rw [size_wordBytes, size_D1 hM]; omega), size_D1 hM]

theorem size_D3 : (D3 M a).size = 160 := by
  rw [D3, size_memoryWrite (by rw [size_wordBytes, size_D2 hM]; omega), size_D2 hM]

theorem read40_D1 : memoryReadBytes (D1 M) 64 32 = memoryReadBytes M 64 32 := by
  rw [D1, memoryReadBytes_memoryWrite_of_disjoint
      (by rw [size_wordBytes, size_memoryExtend, hM]; omega) (.inl (by decide)),
    read_ext (by rw [hM]; omega)]

theorem read40_D2 : memoryReadBytes (D2 M) 64 32 = memoryReadBytes M 64 32 := by
  rw [D2, memoryReadBytes_memoryWrite_of_disjoint (by rw [size_wordBytes, size_D1 hM]; omega)
    (.inl (by decide)), read40_D1 hM]

theorem read40_D3 : memoryReadBytes (D3 M a) 64 32 = memoryReadBytes M 64 32 := by
  rw [D3, memoryReadBytes_memoryWrite_of_disjoint (by rw [size_wordBytes, size_D2 hM]; omega)
    (.inl (by decide)), read40_D2 hM]

theorem data_D3 : memoryReadBytes (D3 M a) 96 36 = SEL_B ++ wordBytes a := by
  have h := memoryReadBytes_memoryWrite_eq_append (memory := D2 M) (value := wordBytes a)
    (s := 96) (k := 4) (by rw [size_wordBytes, size_D2 hM]; omega)
  rw [size_wordBytes, show (96 + 4 : Nat) = 100 from rfl] at h
  rw [D3, h, D2, read_prefix (by rw [size_wordBytes, size_D1 hM]; omega) (by rw [size_wordBytes]; decide),
    selB_prefix]

end Mem

/-- From 4689, on any memory of 96 bytes with the free memory pointer 0x60: as `fwdArgsB`. -/
theorem fwdArgsD (hfork : .berlin ≤ fork) {a : U256} (ha : bitwiseAnd ADDR_MASK a = a)
    {rest : List U256} (hrest : rest.length ≤ 8) {M : ByteArray} (hM : M.size = 96)
    (hptr : loadWord (memoryReadBytes M 64 32) 0 32 = 0x60) {gas : Nat} (hg : 277 ≤ gas) :
    Hoare fork (At CODE message 4689 (0 :: a :: rest) M gas
        (readSlot state message.currentTarget 10) (accessSlot substate message.currentTarget 10))
      (At CODE message 4874
        ([upWord (storageAt state message.currentTarget 10),
          upWord (storageAt state message.currentTarget 10), 0, 0x60, 0x24, 0x60, 0x20, 0x84,
          0x70a08231, upWord (storageAt state message.currentTarget 10), 0, a] ++ rest) (D3 M a)
        (gas - 277) (readSlot state message.currentTarget 10)
        (accessSlot substate message.currentTarget 10)) := by
  have hexp : exponentBytes (0 : U256) = 0 := by decide
  step pushR 1 (0x0a : U256)
  step pushR 1 (0 : U256)
  step swapR 0
  norm
  step sload hfork (cold := false) (by code_fact) (by code_fact)
    (coldIn_accessSlot_self _ _ _) (by gas_ok)
  step swapR 0
  norm
  step pushR 2 (0x0100 : U256)
  step Local.exp (Nat.le_trans (by decide) hfork) (by code_fact) (by code_fact) (by gas_ok)
  step swapR 0
  norm
  step binR 0x04 Local.instruction_div
  step pushR 20 ADDR_MASK
  step binR 0x16 Local.instruction_and
  step pushR 20 ADDR_MASK
  step binR 0x16 Local.instruction_and
  step reshape (s' := [upWord (storageAt state message.currentTarget 10), 0, a] ++ rest)
    (m' := M) (g' := gas - 145)
    (by rw [up_eq, ← storageAt_readSlot state message.currentTarget message.currentTarget 10 10]
        rfl) rfl (by gas_ok)
  step pushR 4 (0x70a08231 : U256)
  step dupR 3
  step pushR 1 (0 : U256)
  step pushR 1 (0x40 : U256)
  have hx0 : extendMemory M.size [((0x40 : U256), (32 : U256))] = ⟨0, 0⟩ := by
    rw [hM]; decide
  step mload (by code_fact) (by code_fact) (by rw [hx0]; gas_ok)
  step reshape (s' := [0x60, 0, a, 0x70a08231, upWord (storageAt state message.currentTarget 10),
      0, a] ++ rest) (m' := M) (g' := gas - 160)
    (by rw [hx0, memoryExtend_zero, show (0x40 : U256).toNat = 64 from rfl, hptr]; rfl)
    (by rw [hx0, memoryExtend_zero]) (by rw [hx0]; gas_ok)
  step pushR 1 (0x20 : U256)
  step binR 0x01 instruction_add
  step reshape (s' := [0x80, 0, a, 0x70a08231, upWord (storageAt state message.currentTarget 10),
      0, a] ++ rest) (m' := M) (g' := gas - 166) rfl rfl (by gas_ok)
  have hx1 : extendMemory M.size [((0x80 : U256), (32 : U256))] = ⟨6, 64⟩ := by
    rw [hM]; decide
  step mstore (by code_fact) (by code_fact) (by rw [hx1]; gas_ok)
  step reshape (s' := [a, 0x70a08231, upWord (storageAt state message.currentTarget 10), 0, a]
      ++ rest) (m' := D1 M) (g' := gas - 175) rfl (by rw [hx1]; rfl) (by rw [hx1]; gas_ok)
  at_pc 4761
  step pushR 1 (0x40 : U256)
  have hx2 : extendMemory (D1 M).size [((0x40 : U256), (32 : U256))] = ⟨0, 0⟩ := by
    rw [size_D1 hM]; decide
  step mload (by code_fact) (by code_fact) (by rw [hx2]; gas_ok)
  step reshape (s' := [0x60, a, 0x70a08231, upWord (storageAt state message.currentTarget 10), 0,
      a] ++ rest) (m' := D1 M) (g' := gas - 181)
    (by rw [hx2, memoryExtend_zero, show (0x40 : U256).toNat = 64 from rfl, read40_D1 hM, hptr]; rfl)
    (by rw [hx2, memoryExtend_zero]) (by rw [hx2]; gas_ok)
  step dupR 2
  step pushR 4 (0xffffffff : U256)
  step binR 0x16 Local.instruction_and
  step pushR 29 (0x0100000000000000000000000000000000000000000000000000000000 : U256)
  step binR 0x02 Local.instruction_mul
  step dupR 1
  have hx3 : extendMemory (D1 M).size [((0x60 : U256), (32 : U256))] = ⟨0, 0⟩ := by
    rw [size_D1 hM]; decide
  step mstore (by code_fact) (by code_fact) (by rw [hx3]; gas_ok)
  step reshape (s' := [0x60, a, 0x70a08231, upWord (storageAt state message.currentTarget 10), 0,
      a] ++ rest) (m' := D2 M) (g' := gas - 204) rfl (by rw [hx3, memoryExtend_zero]; rfl)
    (by rw [hx3]; gas_ok)
  at_pc 4804
  step pushR 1 (0x04 : U256)
  step binR 0x01 instruction_add
  have h64 : add (0x04 : U256) (0x60 : U256) = 0x64 := by decide
  rw [h64]
  step dupR 0
  step dupR 2
  step pushR 20 ADDR_MASK
  step binR 0x16 Local.instruction_and
  step pushR 20 ADDR_MASK
  step binR 0x16 Local.instruction_and
  rw [ha, ha]
  step dupR 1
  have hx4 : extendMemory (D2 M).size [((0x64 : U256), (32 : U256))] = ⟨0, 0⟩ := by
    rw [size_D2 hM]; decide
  step mstore (by code_fact) (by code_fact) (by rw [hx4]; gas_ok)
  step reshape (s' := [0x64, 0x64, a, 0x70a08231, upWord (storageAt state message.currentTarget 10),
      0, a] ++ rest) (m' := D3 M a) (g' := gas - 234) rfl (by rw [hx4, memoryExtend_zero]; rfl)
    (by rw [hx4]; gas_ok)
  at_pc 4855
  step pushR 1 (0x20 : U256)
  step binR 0x01 instruction_add
  have h84 : add (0x20 : U256) (0x64 : U256) = 0x84 := by decide
  rw [h84]
  step swapR 1
  norm
  step popR
  step popR
  step pushR 1 (0x20 : U256)
  step pushR 1 (0x40 : U256)
  have hx5 : extendMemory (D3 M a).size [((0x40 : U256), (32 : U256))] = ⟨0, 0⟩ := by
    rw [size_D3 hM]; decide
  step mload (by code_fact) (by code_fact) (by rw [hx5]; gas_ok)
  step reshape (s' := [0x60, 0x20, 0x84, 0x70a08231,
      upWord (storageAt state message.currentTarget 10), 0, a] ++ rest) (m' := D3 M a)
    (g' := gas - 256)
    (by rw [hx5, memoryExtend_zero, show (0x40 : U256).toNat = 64 from rfl, read40_D3 hM, hptr]; rfl)
    (by rw [hx5, memoryExtend_zero]) (by rw [hx5]; gas_ok)
  step dupR 0
  step dupR 3
  step binR 0x03 Local.instruction_sub
  have h24 : sub (0x84 : U256) (0x60 : U256) = 0x24 := by decide
  rw [h24]
  step dupR 1
  step pushR 1 (0 : U256)
  step dupR 7
  step dupR 0
  exact restate (by decide) (by simp) rfl (by gas_ok)
    (readSlot_readSlot state message.currentTarget 10)
    (accessSlot_accessSlot substate message.currentTarget 10)

/-! ## After the call -/

/-- After a call that succeeded (flag 1), from 4892: the code reads the word at 0x60 and returns
it to the caller of the getter at `0x1f48` (8008), below which the words `rest` stay. -/
theorem okTailD {M : ByteArray} (hM : M.size = 160)
    (hptr : loadWord (memoryReadBytes M 64 32) 0 32 = 0x60) {U a : U256} {rest : List U256}
    (hrest : rest.length ≤ 8) {gas : Nat} (hg : 76 ≤ gas) :
    Hoare fork (At CODE message 4892 (1 :: 0x84 :: 0x70a08231 :: U :: 0 :: a :: 0x1f48 :: rest) M
        gas state substate)
      (At CODE message 8008 (resWord M :: rest) M (gas - 76) state substate) := by
  have hext0 : extendMemory M.size [((0x40 : U256), (32 : U256))] = ⟨0, 0⟩ := by
    rw [hM]; decide
  have hext1 : extendMemory M.size [((0x60 : U256), (32 : U256))] = ⟨0, 0⟩ := by
    rw [hM]; decide
  step unR 0x15 instruction_iszero
  step unR 0x15 instruction_iszero
  step pushR 2 (0x1326 : U256)
  step jumpiR (by decide)
  step jumpdestR
  step popR
  step popR
  step popR
  step pushR 1 (0x40 : U256)
  step mload (by code_fact) (by code_fact) (by rw [hext0]; gas_ok)
  step reshape (s' := 0x60 :: 0 :: a :: 0x1f48 :: rest) (m' := M) (g' := gas - 32)
    (by rw [hext0, memoryExtend_zero]; exact congrArg (· :: 0 :: a :: 0x1f48 :: rest) hptr)
    (by rw [hext0, memoryExtend_zero]) (by rw [hext0]; gas_ok)
  step dupR 0
  step mload (by code_fact) (by code_fact) (by rw [hext1]; gas_ok)
  step reshape (s' := resWord M :: 0x60 :: 0 :: a :: 0x1f48 :: rest) (m' := M) (g' := gas - 38)
    (by rw [hext1, memoryExtend_zero]; rfl) (by rw [hext1, memoryExtend_zero])
    (by rw [hext1]; gas_ok)
  step swapR 0
  norm
  step popR
  step swapR 0
  norm
  step popR
  step pushR 2 (0x1343 : U256)
  step jumpR
  at_pc 4931
  step jumpdestR
  step swapR 1
  norm
  step swapR 0
  norm
  step popR
  step jumpR
  exact restate (by decide) rfl rfl (by gas_ok) rfl rfl

theorem size_mapMem160 {M : ByteArray} (hM : M.size = 160) (k b : U256) :
    (mapMem M k b).size = 160 := by
  rw [mapMem, size_memoryWrite, size_memoryWrite] <;> simp [size_memoryWrite, hM, size_wordBytes]

theorem ptr_mapMem160 {M : ByteArray} (hM : M.size = 160)
    (hptr : loadWord (memoryReadBytes M 64 32) 0 32 = 0x60) (k b : U256) :
    loadWord (memoryReadBytes (mapMem M k b) 64 32) 0 32 = 0x60 := by
  rw [mapMem, memoryReadBytes_memoryWrite_of_disjoint,
    memoryReadBytes_memoryWrite_of_disjoint, hptr] <;>
    simp [size_memoryWrite, hM, size_wordBytes]

/-- The lookup tail at 8018 on a memory of 160 bytes (as `hashTail7`, no growth). -/
theorem hashTail160 {x base : U256} {rest : List U256} (hrest : rest.length ≤ 900)
    {M : ByteArray} (hM : M.size = 160) {gas : Nat} (hg : 84 ≤ gas) :
    Hoare fork (At CODE message 8018 (x :: 0 :: base :: rest) M gas state substate)
      (At CODE message (8018 + 58) (mapSlot (mkey x) base :: rest) (mapMem M (mkey x) base)
        (gas - 84) state substate) := by
  have hs1 : (memoryWrite M 0 (wordBytes (mkey x))).size = 160 := by
    rw [size_memoryWrite] <;> simp [hM, size_wordBytes]
  have hext1 : extendMemory M.size [((0 : U256), (32 : U256))] = ⟨0, 0⟩ := by rw [hM]; decide
  have hext2 : extendMemory (memoryWrite M 0 (wordBytes (mkey x))).size
      [((0x20 : U256), (32 : U256))] = ⟨0, 0⟩ := by rw [hs1]; decide
  have hext3 : extendMemory (mapMem M (mkey x) base).size [((0 : U256), (0x40 : U256))] =
      ⟨0, 0⟩ := by rw [size_mapMem160 hM]; decide
  have hk : keccak256Cost (0x40 : U256) = 42 := by decide
  have hread : memoryReadBytes (mapMem M (mkey x) base) 0 64 =
      wordBytes (mkey x) ++ wordBytes base := by
    have h := memoryReadBytes_memoryWrite_memoryWrite (memory := M) (a := wordBytes (mkey x))
      (b := wordBytes base) (s := 0) (by simp [hM, size_wordBytes])
    simpa [size_wordBytes, mapMem] using h
  step pushR 20 ADDR_MASK
  step binR 0x16 Local.instruction_and
  step pushR 20 ADDR_MASK
  step binR 0x16 Local.instruction_and
  step dupR 1
  step mstore (by code_fact) (by code_fact) (by rw [hext1]; gas_ok)
  step reshape (m' := memoryWrite M 0 (wordBytes (mkey x))) rfl
    (by rw [hext1, memoryExtend_zero]; rfl) (by rw [hext1] <;> gas_ok)
  step pushR 1 (0x20 : U256)
  step binR 0x01 instruction_add
  step swapR 0
  norm
  step dupR 1
  step reshape (s' := (0x20 : U256) :: base :: 0x20 :: rest) rfl rfl rfl
  step mstore (by code_fact) (by code_fact) (by rw [hext2]; gas_ok)
  step reshape (m' := mapMem M (mkey x) base) rfl (by rw [hext2, memoryExtend_zero]; rfl)
    (by rw [hext2] <;> gas_ok)
  step pushR 1 (0x20 : U256)
  step binR 0x01 instruction_add
  step pushR 1 (0 : U256)
  step reshape (s' := (0 : U256) :: 0x40 :: rest) rfl rfl rfl
  step keccak256 (by code_fact) (by code_fact) (by rw [hk, hext3]; gas_ok)
  exact restate (by decide)
    (by rw [hext3, memoryExtend_zero, show (0 : U256).toNat = 0 from rfl,
      show (0x40 : U256).toNat = 64 from rfl, hread]; rfl)
    (by rw [hext3, memoryExtend_zero]) (by rw [hext3, hk] <;> gas_ok) rfl rfl

/-- At 8008 on a memory of 160 bytes, back from the forward with the answer `b`:
`balances[a] := 0`. The slot was not read by the getter, so it may be cold (`cB`). -/
theorem zeroBalD (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam) {a b : U256}
    {rest : List U256} (hrest : rest.length ≤ 800) (hstatic : message.isStatic = false)
    (hacc : hasAccount state message.currentTarget) {cB : Bool}
    (hcB : coldIn substate message.currentTarget (mapSlot (mkey a) 2) = cB) {M : ByteArray}
    (hM : M.size = 160) {gas : Nat} (hstip : 2409 ≤ gas)
    (hg : 110 + sstoreCost fork (originalAt state message.currentTarget (mapSlot (mkey a) 2))
      (storageAt state message.currentTarget (mapSlot (mkey a) 2)) 0 cB ≤ gas) :
    Hoare fork (At CODE message 8008 (b :: 0 :: a :: rest) M gas state substate)
      (At CODE message 8080 (b :: a :: rest) (mapMem M (mkey a) 2)
        (gas - (110 + sstoreCost fork (originalAt state message.currentTarget (mapSlot (mkey a) 2))
          (storageAt state message.currentTarget (mapSlot (mkey a) 2)) 0 cB))
        (writeSlot state message.currentTarget (mapSlot (mkey a) 2) 0)
        (storeSub fork substate message.currentTarget (mapSlot (mkey a) 2)
          (originalAt state message.currentTarget (mapSlot (mkey a) 2))
          (storageAt state message.currentTarget (mapSlot (mkey a) 2)) 0)) := by
  step jumpdestR
  step swapR 0
  norm
  step popR
  step pushR 1 (0 : U256)
  step pushR 1 (0x02 : U256)
  step pushR 1 (0 : U256)
  step dupR 4
  step hashTail160 (by simp; omega) hM (by gas_ok)
  step dupR 1
  step swapR 0
  norm
  step sstoreW hfork hglam (by code_fact) (by code_fact) hstatic hacc hcB (by gas_ok) (by gas_ok)
  step popR
  exact restate (by decide) rfl rfl (by gas_ok) rfl rfl

/-- At 8096 on a memory of 160 bytes: logs `DestroyedBlackFunds(a, b)` (the words written at 0x60
and 0x80, no growth), returns to 2486 and stops. -/
theorem logBlockD {a b x : U256} (hstatic : message.isStatic = false) {M : ByteArray}
    (hM : M.size = 160) (hptr : loadWord (memoryReadBytes M 64 32) 0 32 = 0x60) {gas : Nat}
    (hg : 1362 ≤ gas) :
    Spec fork (At CODE message 8096 [b, a, 0x09b6, x] M gas state substate)
      (Halted false .empty (gas - 1362) state
        { substate with logs := substate.logs.push (destroyLog message.currentTarget (mkey a) b) }) := by
  have hext0 : extendMemory M.size [((0x40 : U256), (32 : U256))] = ⟨0, 0⟩ := by
    rw [hM]; decide
  have hext1 : extendMemory M.size [((0x60 : U256), (32 : U256))] = ⟨0, 0⟩ := by
    rw [hM]; decide
  have hfit1 : 96 + (wordBytes (mkey a)).size ≤ M.size := by rw [size_wordBytes, hM]; decide
  have hs1 : (memoryWrite M 96 (wordBytes (mkey a))).size = 160 := by
    rw [size_memoryWrite hfit1, hM]
  have hext2 : extendMemory (memoryWrite M 96 (wordBytes (mkey a))).size
      [((0x80 : U256), (32 : U256))] = ⟨0, 0⟩ := by rw [hs1]; decide
  have hfit2 : 128 + (wordBytes b).size ≤ (memoryWrite M 96 (wordBytes (mkey a))).size := by
    rw [size_wordBytes, hs1]; decide
  have hs2 : (memoryWrite (memoryWrite M 96 (wordBytes (mkey a))) 128 (wordBytes b)).size = 160 := by
    rw [size_memoryWrite hfit2, hs1]
  have hext3 : extendMemory (memoryWrite (memoryWrite M 96 (wordBytes (mkey a))) 128
      (wordBytes b)).size [((0x40 : U256), (32 : U256))] = ⟨0, 0⟩ := by rw [hs2]; decide
  have hext4 : extendMemory (memoryWrite (memoryWrite M 96 (wordBytes (mkey a))) 128
      (wordBytes b)).size [((0x60 : U256), (0x40 : U256))] = ⟨0, 0⟩ := by rw [hs2]; decide
  have hread : memoryReadBytes (memoryWrite (memoryWrite M 96 (wordBytes (mkey a))) 128
      (wordBytes b)) 64 32 = memoryReadBytes M 64 32 := by
    rw [memoryReadBytes_memoryWrite_of_disjoint hfit2 (.inl (by decide)),
      memoryReadBytes_memoryWrite_of_disjoint hfit1 (.inl (by decide))]
  have hdata : memoryReadBytes (memoryWrite (memoryWrite M 96 (wordBytes (mkey a))) 128
      (wordBytes b)) 96 64 = wordBytes (mkey a) ++ wordBytes b := by
    have h := memoryReadBytes_memoryWrite_memoryWrite (memory := M) (a := wordBytes (mkey a))
      (b := wordBytes b) (s := 96) (by simp [hM, size_wordBytes])
    simpa [size_wordBytes] using h
  have hlog : logCost (1 : Fin 5).val (0x40 : U256) = 1262 := by decide
  step push (n := 32) (word := DESTROY_TOPIC) (by decide) (by code_fact) (by code_fact)
    (decode_push 32 (by decide)) (by rw [pushData_CODE]; decide) (by gas_ok) (by stk_ok)
  step dupR 2
  step dupR 2
  step pushR 1 (0x40 : U256)
  step mload (by code_fact) (by code_fact) (by rw [hext0]; gas_ok)
  step reshape (s' := (0x60 : U256) :: _) (m' := M)
    (by rw [hext0, memoryExtend_zero]; exact congrArg (· :: _) hptr)
    (by rw [hext0, memoryExtend_zero]) (by rw [hext0])
  step dupR 0
  step dupR 3
  step pushR 20 ADDR_MASK
  step binR 0x16 Local.instruction_and
  step pushR 20 ADDR_MASK
  step binR 0x16 Local.instruction_and
  step dupR 1
  step mstore (by code_fact) (by code_fact) (by rw [hext1]; gas_ok)
  step reshape (m' := memoryWrite M 96 (wordBytes (mkey a))) rfl
    (by rw [hext1, memoryExtend_zero]; rfl) (by rw [hext1])
  step pushR 1 (0x20 : U256)
  step binR 0x01 instruction_add
  step dupR 2
  step dupR 1
  step reshape (s' := (0x80 : U256) :: _ :: 0x80 :: _) rfl rfl rfl
  step mstore (by code_fact) (by code_fact) (by rw [hext2]; gas_ok)
  step reshape (m' := memoryWrite (memoryWrite M 96 (wordBytes (mkey a))) 128 (wordBytes b)) rfl
    (by rw [hext2, memoryExtend_zero]; rfl) (by rw [hext2])
  step pushR 1 (0x20 : U256)
  step binR 0x01 instruction_add
  step swapR 2
  norm
  step popR
  step popR
  step popR
  step pushR 1 (0x40 : U256)
  step mload (by code_fact) (by code_fact) (by rw [hext3]; gas_ok)
  step reshape (s' := (0x60 : U256) :: _)
    (m' := memoryWrite (memoryWrite M 96 (wordBytes (mkey a))) 128 (wordBytes b))
    (by rw [hext3, memoryExtend_zero, show (0x40 : U256).toNat = 64 from rfl, hread, hptr])
    (by rw [hext3, memoryExtend_zero]) (by rw [hext3])
  step dupR 0
  step swapR 1
  norm
  step binR 0x03 Local.instruction_sub
  step swapR 0
  norm
  step reshape (s' := 0x60 :: 0x40 :: ([DESTROY_TOPIC] ++ [b, a, 0x09b6, x])) rfl rfl rfl
  step Logic.log (n := 1) (byte := 0xa1) rfl (by code_fact) (by code_fact) rfl hstatic
    (by rw [hlog, hext4]; gas_ok)
  step reshape rfl (by rw [hext4, memoryExtend_zero]) (by rw [hlog, hext4])
  step popR
  step popR
  step jumpR
  step jumpdestR
  refine (Logic.stop (by code_fact) (by code_fact)).consequence (fun _ h => h) ?_
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  refine ⟨hr, he, ho, by rw [hgas]; gas_ok, hs, ?_⟩
  rw [hss, hext4, memoryExtend_zero, show (0x60 : U256).toNat = 96 from rfl,
    show (0x40 : U256).toNat = 64 from rfl, hdata]

/-! ## The tail, from the result of the call to STOP -/

/-- The state after the tail, over the state `S` that the call left: `balances[a] := 0`, then
`_totalSupply := T' - d` (unchecked), `T'` read after the first write. -/
abbrev tailState (S : State.TransactionState) (C : EthLib.Base.Address) (a d : U256) :
    State.TransactionState :=
  writeSlot (writeSlot S C (mapSlot a 2) 0) C 1
    (sub (storageAt (writeSlot S C (mapSlot a 2) 0) C 1) d)

/-- The substate after the tail: the two writes (accesses, refunds) and the log. -/
abbrev tailSub (fork : Fork) (ss : Substate) (S : State.TransactionState)
    (C : EthLib.Base.Address) (a d : U256) : Substate :=
  { storeSub fork (storeSub fork ss C (mapSlot a 2) (originalAt S C (mapSlot a 2))
        (storageAt S C (mapSlot a 2)) 0) C 1 (originalAt S C 1)
      (storageAt (writeSlot S C (mapSlot a 2) 0) C 1)
      (sub (storageAt (writeSlot S C (mapSlot a 2) 0) C 1) d) with
    logs := ss.logs.push (destroyLog C a d) }

/-- The gas of the tail: `cB` the coldness of `balances[a]` after the call, `c1` that of slot 1
after the first write. -/
abbrev tailCost (fork : Fork) (S : State.TransactionState) (C : EthLib.Base.Address) (a d : U256)
    (cB c1 : Bool) : Nat :=
  1581 + sstoreCost fork (originalAt S C (mapSlot a 2)) (storageAt S C (mapSlot a 2)) 0 cB +
    slotCost c1 + sstoreCost fork (originalAt S C 1) (storageAt (writeSlot S C (mapSlot a 2) 0) C 1)
      (sub (storageAt (writeSlot S C (mapSlot a 2) 0) C 1) d) false

/-- An upper bound of the gas that the tail needs (both writes at their highest price). -/
abbrev TAIL_MAX : Nat := 47881

/-- From 4892 after a call that succeeded, on the memory `M` the call left (160 bytes) and the
state `S` it left: back to 8008 with the word at 0x60, then the two writes and the log. -/
theorem tailD (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam) {a x U : U256}
    (ha : mkey a = a) (hstatic : message.isStatic = false) {S : State.TransactionState}
    {ss : Substate} (hacc : hasAccount S message.currentTarget) {M : ByteArray}
    (hM : M.size = 160) (hptr : loadWord (memoryReadBytes M 64 32) 0 32 = 0x60) {cB c1 : Bool}
    (hcB : coldIn ss message.currentTarget (mapSlot a 2) = cB)
    (hc1 : coldIn (accessSlot ss message.currentTarget (mapSlot a 2)) message.currentTarget 1 = c1)
    {gas : Nat} (hg : TAIL_MAX ≤ gas) :
    Spec fork (At CODE message 4892 [1, 0x84, 0x70a08231, U, 0, a, 0x1f48, 0, a, 0x09b6, x] M
        gas S ss)
      (Halted false .empty (gas - tailCost fork S message.currentTarget a (resWord M) cB c1)
        (tailState S message.currentTarget a (resWord M))
        (tailSub fork ss S message.currentTarget a (resWord M))) := by
  have hb1 := sstoreCost_le hfork hglam (originalAt S message.currentTarget (mapSlot a 2))
    (storageAt S message.currentTarget (mapSlot a 2)) 0 cB
  have hb2 := sstoreCost_le hfork hglam (originalAt S message.currentTarget 1)
    (storageAt (writeSlot S message.currentTarget (mapSlot a 2) 0) message.currentTarget 1)
    (sub (storageAt (writeSlot S message.currentTarget (mapSlot a 2) 0) message.currentTarget 1)
      (resWord M)) false
  simp only [COLD_STORAGE_ACCESS, STORAGE_SET] at hb1 hb2
  simp only [TAIL_MAX] at hg
  have hs1 : slotCost c1 ≤ 2100 := by unfold slotCost; split <;> omega
  have hM1 : (mapMem M (mkey a) 2).size = 160 := size_mapMem160 hM _ _
  have hp1 := ptr_mapMem160 hM hptr (mkey a) 2
  step okTailD hM hptr (rest := [0, a, 0x09b6, x]) (by simp) (by omega)
  step zeroBalD hfork hglam (by simp) hstatic hacc (cB := cB) (by rw [ha]; exact hcB) hM
    (by omega) (by rw [ha]; omega)
  rw [ha]
  rw [ha] at hM1 hp1
  step subTotal hfork hglam (by simp) hstatic (hasAccount_writeSlot hacc) (c1 := c1)
    (by rw [TransferFee.coldIn_storeSub']; exact hc1) (by omega)
    (by rw [originalAt_writeSlot hacc]; omega)
  rw [originalAt_writeSlot hacc]
  refine (logBlockD hstatic hM1 hp1 (by omega)).consequence
    (fun _ h => h) ?_
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  refine ⟨hr, he, ho, by rw [hgas]; simp only [tailCost]; omega, hs, ?_⟩
  rw [hss, ha]

/-! ## From pc 0 to the CALL -/

/-- The gas of the path from pc 0 to the CALL. -/
abbrev preCostD (c0 cL c10 cU : Bool) : Nat :=
  1500 + slotCost c0 + slotCost cL + slotCost c10 + accCost cU

/-- The gas that the code asks CALL to pass on. -/
abbrev askedOfD (gas : Nat) (c0 cL c10 cU : Bool) : U256 :=
  asked (gas - (1497 + slotCost c0 + slotCost cL + slotCost c10 + accCost cU))

/-- What CALL pays and passes on (the address is warm after EXTCODESIZE). -/
abbrev callGasD (fork : Fork) (gas : Nat) (c0 cL c10 cU : Bool) : MessageCallGas :=
  messageCallGas fork 0 (askedOfD gas c0 cL c10 cU).toNat (gas - preCostD c0 cL c10 cU) 0 100

/-- The state when the code calls: slots 0, `isBlackListed[a]`, 10 and the upgraded account
recorded read. -/
abbrev callStateD (state : State.TransactionState) (message : Message fork) :
    State.TransactionState :=
  (readSlot (preState state message) message.currentTarget 10).recordAccountRead
    (upAddr state message)

/-- The substate when the code calls: those slots and the upgraded address accessed. -/
abbrev callSubD (substate : Substate) (state : State.TransactionState) (message : Message fork) :
    Substate :=
  { accessSlot (preSub substate message) message.currentTarget 10 with
    accessedAddresses :=
      (accessSlot (preSub substate message) message.currentTarget 10).accessedAddresses.insert
        (upAddr state message) }

/-- The memory when the code calls (160 bytes). -/
abbrev memD (message : Message fork) : ByteArray := D3 (MEMB message) (addrArg message.data 0)

theorem size_memD (message : Message fork) : (memD message).size = 160 :=
  size_D3 (size_mapMem size_MEM0 _ _)

theorem ptr_memD (message : Message fork) :
    loadWord (memoryReadBytes (memD message) 64 32) 0 32 = 0x60 := by
  rw [memD, read40_D3 (size_mapMem size_MEM0 _ _)]
  exact ptr_mapMem size_MEM0 mload_MEM0 _ _

theorem data_memD (message : Message fork) :
    memoryReadBytes (memD message) 96 36 = dataB message :=
  data_D3 (size_mapMem size_MEM0 _ _)

/-- From pc 0 to the CALL at 4891: the owner, `a` blacklisted, deprecated, the upgraded account
has code. -/
theorem preCallD (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    (hsize : 4 ≤ message.data.size) (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0xf3bdc228) (hv : message.value = 0)
    (hown : callerWord message = ownerOf state message.currentTarget)
    (hl : (storageAt state message.currentTarget (listSlot (addrArg message.data 0))).toNat % 256 ≠ 0)
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0) {c : ByteArray}
    (hcode : state.getCode (state.getAccount (upAddr state message)).codeHash = .ok c)
    (hsz : 0 < c.size) (hszl : c.size < 2 ^ 256) {c0 cL c10 cU : Bool}
    (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hcL : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget
      (listSlot (addrArg message.data 0)) = cL)
    (hc10 : coldIn (preSub substate message) message.currentTarget 10 = c10)
    (hcU : decide (upAddr state message ∉ substate.accessedAddresses) = cU)
    {gas : Nat} (hg : preCostD c0 cL c10 cU ≤ gas) :
    Hoare fork (At CODE message 0 [] .empty gas state substate)
      (At CODE message 4891
        [askedOfD gas c0 cL c10 cU, upWord (storageAt state message.currentTarget 10), 0, 0x60,
          0x24, 0x60, 0x20, 0x84, 0x70a08231, upWord (storageAt state message.currentTarget 10), 0,
          addrArg message.data 0, 0x1f48, 0, addrArg message.data 0, 0x09b6,
          BitVec.ofNat 256 (selector message.data)]
        (memD message) (gas - preCostD c0 cL c10 cU) (callStateD state message)
        (callSubD substate state message)) := by
  simp only [preCostD, askedOfD, accCost] at hg ⊢
  have hU : storageAt (preState state message) message.currentTarget 10 =
      storageAt state message.currentTarget 10 := by
    simp only [preState, storageAt_readSlot]
  refine (toGetter hfork hsize hsize' hsel hv hown hl hc0 hcL (by omega)).seq ?_
  step depSet hfork (Or.inr ⟨rfl, rfl⟩) (by simp) (by rw [hU]; exact hdep) hc10 (by gas_ok)
  step fwdArgsD (state := preState state message) hfork (by simp only [addrArg, mask_mask])
    (by simp) (size_mapMem size_MEM0 _ _) (ptr_mapMem size_MEM0 mload_MEM0 _ _) (by gas_ok)
  rw [hU]
  step reshape (g' := gas - (1472 + slotCost c0 + slotCost cL + slotCost c10)) rfl rfl (by gas_ok)
  refine (toCall (gas := gas - (1472 + slotCost c0 + slotCost cL + slotCost c10))
    (st := readSlot (preState state message) message.currentTarget 10)
    (ss := accessSlot (preSub substate message) message.currentTarget 10) (message := message)
    (M := memD message)
    (rest := [upWord (storageAt state message.currentTarget 10), 0, 0x60, 0x24, 0x60, 0x20, 0x84,
      0x70a08231, upWord (storageAt state message.currentTarget 10), 0, addrArg message.data 0,
      0x1f48, 0, addrArg message.data 0, 0x09b6, BitVec.ofNat 256 (selector message.data)])
    hfork hglam (Or.inr (Or.inl ⟨rfl, rfl⟩))
    (by simp) hcode hsz hszl hcU (by simp only [accCost]; gas_ok)).seq ?_
  refine reshape ?_ rfl (by simp only [accCost]; gas_ok)
  simp only [List.cons.injEq, and_true]
  congr 1
  unfold accCost; omega

/-! ## The whole path -/

theorem state_incorporateChild (caller child : Evm fork Nat) :
    (incorporateChild fork caller child).state = child.state := by
  unfold incorporateChild; split <;> rfl

/-- The specification of `destroyBlackFunds(a)` when deprecated, for every callee.

Hypotheses: Berlin ≤ fork < Glamsterdam; a frame that may write; call data of 4 to 2^256 - 1
bytes with selector 0xf3bdc228; no value; the caller is the owner; `a` (argument word 0 masked)
blacklisted; deprecated (byte 20 of slot 10 not 0); the upgraded address `ua` (low 160 bits of
slot 10) holds a code `c` with 0 < |c| < 2^256, no delegation from Pectra; depth + 1 ≤ 1024; the
gas to the CALL plus 100 (`hg`), and at least `TAIL_MAX` = 47881 gas left after the CALL's price
(`htail`); and an assumption on the callee (`hkeep`): when a forwarded message ends with no error,
the account of the contract exists in its state.

Then under every runner whose ended messages meet `callee`, the run ends (or the runner aborts)
in a stopped frame for which there are a caller frame, a message `msg` and an ended frame `child`
with `callee caller msg child`, `msg` sent to `ua` with data `0x70a08231 ++ a` (`dataB`) and no
value, the caller's state and substate exact, and, writing `S`, `ss` for the state and substate
that the call left and `d` for the word at 0x60 after CALL wrote the first `min 32 (output size)`
bytes of the child's output there:
- if `child` ended with no error, the frame stops normally (empty output) in `tailState S C a d`
  (`balances[a] := 0`, then `_totalSupply := T' - d` unchecked, `T'` read after the first write),
  substate `tailSub` (the writes and the log `DestroyedBlackFunds(a, d)`), gas exact;
- otherwise it reverts with no output.
So `d` is the balance that the UPGRADED contract answers, subtracted from THIS contract's
`_totalSupply`, while THIS contract's `balances[a]` is set to 0. -/
theorem spec_depD (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    (hstatic : message.isStatic = false)
    (hsize : 4 ≤ message.data.size) (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0xf3bdc228) (hv : message.value = 0)
    (hown : callerWord message = ownerOf state message.currentTarget)
    (hl : (storageAt state message.currentTarget (listSlot (addrArg message.data 0))).toNat % 256 ≠ 0)
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0) {c : ByteArray}
    (hcode : state.getCode (state.getAccount (upAddr state message)).codeHash = .ok c)
    (hsz : 0 < c.size) (hszl : c.size < 2 ^ 256)
    (hdel : .pectra ≤ fork → delegatedAddress c = none)
    (hdepth : message.depth + 1 ≤ STACK_DEPTH_LIMIT) {c0 cL c10 cU : Bool}
    (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hcL : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget
      (listSlot (addrArg message.data 0)) = cL)
    (hc10 : coldIn (preSub substate message) message.currentTarget 10 = c10)
    (hcU : decide (upAddr state message ∉ substate.accessedAddresses) = cU)
    {gas : Nat} (hg : preCostD c0 cL c10 cU + 100 ≤ gas)
    (htail : TAIL_MAX ≤ gas - preCostD c0 cL c10 cU - (callGasD fork gas c0 cL c10 cU).cost)
    {callee : Evm fork Nat → Message fork → Evm fork Nat → Prop}
    (hkeep : ∀ caller msg child, callee caller msg child →
      Sends message (upAddr state message) c (dataB message) msg → child.error = none →
        hasAccount child.state message.currentTarget) :
    SpecUnder fork callee (At CODE message 0 [] .empty gas state substate)
      fun evm => ∃ caller msg child, callee caller msg child ∧
        Sends message (upAddr state message) c (dataB message) msg ∧
        msg.gas = (callGasD fork gas c0 cL c10 cU).subCall ∧
        caller.state = ((callStateD state message).recordAccountRead (upAddr state message)).recordAccountRead
          message.currentTarget ∧
        caller.substate = { callSubD substate state message with
          accessedAddresses :=
            (callSubD substate state message).accessedAddresses.insert (upAddr state message) } ∧
        (child.error = none →
          Halted false .empty
            (gas - preCostD c0 cL c10 cU - (callGasD fork gas c0 cL c10 cU).cost + child.gas -
              tailCost fork (incorporateChild fork caller child).state message.currentTarget
                (addrArg message.data 0) (resWord (outMemOf (memD message) child.output))
                (coldIn (incorporateChild fork caller child).substate message.currentTarget
                  (balSlot message))
                (coldIn (accessSlot (incorporateChild fork caller child).substate
                  message.currentTarget (balSlot message)) message.currentTarget 1))
            (tailState (incorporateChild fork caller child).state message.currentTarget
              (addrArg message.data 0) (resWord (outMemOf (memD message) child.output)))
            (tailSub fork (incorporateChild fork caller child).substate
              (incorporateChild fork caller child).state message.currentTarget
              (addrArg message.data 0) (resWord (outMemOf (memD message) child.output))) evm) ∧
        (child.error ≠ none →
          Halted true .empty
            (gas - preCostD c0 cL c10 cU - (callGasD fork gas c0 cL c10 cU).cost + child.gas - 25)
            (incorporateChild fork caller child).state
            (incorporateChild fork caller child).substate evm) := by
  have hext : extendMemory (memD message).size
      [((0x60 : U256), (0x24 : U256)), ((0x60 : U256), (0x20 : U256))] = ⟨0, 0⟩ := by
    rw [size_memD]; decide
  have hcall := callWith (fork := fork) (code := CODE) (message := message) (pc := 4891)
    (memory := memD message) (gas := gas - preCostD c0 cL c10 cU)
    (state := callStateD state message)
    (substate := callSubD substate state message) (callee := callee)
    (asked := askedOfD gas c0 cL c10 cU) (to := upWord (storageAt state message.currentTarget 10))
    (inputStart := 0x60) (inputSize := 0x24) (outputStart := 0x60) (outputSize := 0x20)
    (rest := [0x84, 0x70a08231, upWord (storageAt state message.currentTarget 10), 0,
      addrArg message.data 0, 0x1f48, 0, addrArg message.data 0, 0x09b6,
      BitVec.ofNat 256 (selector message.data)]) (cold := false)
    hfork hglam (by code_fact) (by code_fact) hcode hdel hdepth (by simp [upAddr])
    (by rw [hext]; simp only [Bool.false_eq_true, ↓reduceIte]; omega)
  rw [hext] at hcall
  simp only [Bool.false_eq_true, ↓reduceIte] at hcall
  refine SpecUnder.seq (HoareUnder.of_hoare (preCallD hfork hglam hsize hsize' hsel hv hown hl
    hdep hcode hsz hszl hc0 hcL hc10 hcU (by omega))) (HoareUnder.seq hcall (HoareUnder.of_hoare ?_))
  rintro evm ⟨caller, msg, child, hcal, -, hcs, hcss, hmg, hmc, hmt, hmtg, hmca, hmcode, hmd, hmv,
    hmdep, hmst, hat⟩
  have hfwd : Sends message (upAddr state message) c (dataB message) msg := by
    refine ⟨hmc, hmt, hmtg, hmca, hmcode, ?_, hmv, hmdep, hmst⟩
    rw [hmd, memoryExtend_zero]; exact data_memD message
  have hB := size_memD message
  by_cases he : child.error = none
  · simp only [he, Option.isNone_none, ↓reduceIte] at hat
    have hacc : hasAccount (incorporateChild fork caller child).state message.currentTarget := by
      rw [state_incorporateChild]; exact hkeep caller msg child hcal hfwd he
    obtain ⟨after, hreach, hrun, hq⟩ := tailD (fork := fork) (message := message)
      hfork hglam (mkey_addrArg0 message.data) hstatic hacc
      (size_outMemOf hB child.output) (mload_outMemOf hB (by rw [memoryExtend_zero]; exact ptr_memD message) child.output)
      (x := BitVec.ofNat 256 (selector message.data)) rfl rfl
      (gas := gas - preCostD c0 cL c10 cU - ((callGasD fork gas c0 cL c10 cU).cost + 0) + child.gas)
      (by omega) evm hat
    refine ⟨after, hreach, hrun, caller, msg, child, hcal, hfwd, hmg, hcs, hcss, fun _ => ?_,
      fun h => absurd he h⟩
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hq
    exact ⟨h1, h2, h3, by rw [h4]; simp only [balSlot]; omega, h5, h6⟩
  · have hz : child.error.isNone = false := by
      cases h : child.error
      · exact absurd h he
      · rfl
    simp only [hz, Bool.false_eq_true, ↓reduceIte] at hat
    obtain ⟨after, hreach, hrun, hq⟩ := failTail (fork := fork) (message := message)
      (state := (incorporateChild fork caller child).state)
      (substate := (incorporateChild fork caller child).substate) hfork (Or.inr (Or.inl rfl))
      (rest := [0x84, 0x70a08231,
        upWord (storageAt state message.currentTarget 10), 0, addrArg message.data 0, 0x1f48, 0,
        addrArg message.data 0, 0x09b6, BitVec.ofNat 256 (selector message.data)])
      (by simp)
      (gas := gas - preCostD c0 cL c10 cU - ((callGasD fork gas c0 cL c10 cU).cost + 0) + child.gas)
      (by simp only [TAIL_MAX] at htail; omega) evm hat
    refine ⟨after, hreach, hrun, caller, msg, child, hcal, hfwd, hmg, hcs, hcss,
      fun h => absurd h he, fun _ => ?_⟩
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hq
    exact ⟨h1, h2, h3, by rw [h4]; omega, h5, h6⟩

/-- `destroyBlackFunds(a)` when deprecated, for a callee that answers `o` (at least 32 bytes) to
the forwarded `balanceOf(a)` and keeps the contract's account: the run stops normally with an
empty output, and its state is `tailState S C a d` for the state `S` that the call left, with
`d` the first word of `o`: `balances[a] := 0`, then `_totalSupply := T' - d`. -/
theorem spec_depD_answers (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    (hstatic : message.isStatic = false)
    (hsize : 4 ≤ message.data.size) (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0xf3bdc228) (hv : message.value = 0)
    (hown : callerWord message = ownerOf state message.currentTarget)
    (hl : (storageAt state message.currentTarget (listSlot (addrArg message.data 0))).toNat % 256 ≠ 0)
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0) {c : ByteArray}
    (hcode : state.getCode (state.getAccount (upAddr state message)).codeHash = .ok c)
    (hsz : 0 < c.size) (hszl : c.size < 2 ^ 256)
    (hdel : .pectra ≤ fork → delegatedAddress c = none)
    (hdepth : message.depth + 1 ≤ STACK_DEPTH_LIMIT) {c0 cL c10 cU : Bool}
    (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hcL : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget
      (listSlot (addrArg message.data 0)) = cL)
    (hc10 : coldIn (preSub substate message) message.currentTarget 10 = c10)
    (hcU : decide (upAddr state message ∉ substate.accessedAddresses) = cU)
    {gas : Nat} (hg : preCostD c0 cL c10 cU + 100 ≤ gas)
    (htail : TAIL_MAX ≤ gas - preCostD c0 cL c10 cU - (callGasD fork gas c0 cL c10 cU).cost)
    {callee : Evm fork Nat → Message fork → Evm fork Nat → Prop} {o : ByteArray}
    (hans : AnswersD message (upAddr state message) c (dataB message) o callee)
    (ho : 32 ≤ o.size)
    (hkeep : ∀ caller msg child, callee caller msg child →
      Sends message (upAddr state message) c (dataB message) msg → child.error = none →
        hasAccount child.state message.currentTarget) :
    SpecUnder fork callee (At CODE message 0 [] .empty gas state substate)
      fun evm => evm.error = none ∧ evm.output = .empty ∧
        ∃ S : State.TransactionState,
          evm.state = tailState S message.currentTarget (addrArg message.data 0) (loadWord o 0 32) := by
  refine (spec_depD hfork hglam hstatic hsize hsize' hsel hv hown hl hdep hcode hsz hszl hdel hdepth hc0 hcL hc10
    hcU hg htail hkeep).consequence (fun _ h => h) ?_
  rintro evm ⟨caller, msg, child, hcal, hfwd, -, -, -, hok, -⟩
  obtain ⟨he, hout⟩ := hans caller msg child hcal hfwd
  obtain ⟨-, herr, hevm, -, hs, -⟩ := hok he
  refine ⟨by simpa using herr, hevm, (incorporateChild fork caller child).state, ?_⟩
  rw [hs, hout, resWord_outMemOf (size_memD _) ho]

/-- `destroyBlackFunds(a)` when deprecated, for a callee whose answer fails: the run reverts
with no output. -/
theorem spec_depD_fails (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    (hstatic : message.isStatic = false)
    (hsize : 4 ≤ message.data.size) (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0xf3bdc228) (hv : message.value = 0)
    (hown : callerWord message = ownerOf state message.currentTarget)
    (hl : (storageAt state message.currentTarget (listSlot (addrArg message.data 0))).toNat % 256 ≠ 0)
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0) {c : ByteArray}
    (hcode : state.getCode (state.getAccount (upAddr state message)).codeHash = .ok c)
    (hsz : 0 < c.size) (hszl : c.size < 2 ^ 256)
    (hdel : .pectra ≤ fork → delegatedAddress c = none)
    (hdepth : message.depth + 1 ≤ STACK_DEPTH_LIMIT) {c0 cL c10 cU : Bool}
    (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hcL : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget
      (listSlot (addrArg message.data 0)) = cL)
    (hc10 : coldIn (preSub substate message) message.currentTarget 10 = c10)
    (hcU : decide (upAddr state message ∉ substate.accessedAddresses) = cU)
    {gas : Nat} (hg : preCostD c0 cL c10 cU + 100 ≤ gas)
    (htail : TAIL_MAX ≤ gas - preCostD c0 cL c10 cU - (callGasD fork gas c0 cL c10 cU).cost)
    {callee : Evm fork Nat → Message fork → Evm fork Nat → Prop}
    (hkeep : ∀ caller msg child, callee caller msg child →
      Sends message (upAddr state message) c (dataB message) msg → child.error = none →
        hasAccount child.state message.currentTarget)
    (hfail : ∀ caller msg child, callee caller msg child →
      Sends message (upAddr state message) c (dataB message) msg → child.error ≠ none) :
    SpecUnder fork callee (At CODE message 0 [] .empty gas state substate)
      fun evm => evm.error = some .revert ∧ evm.output = .empty := by
  refine (spec_depD hfork hglam hstatic hsize hsize' hsel hv hown hl hdep hcode hsz hszl hdel hdepth hc0 hcL hc10
    hcU hg htail hkeep).consequence (fun _ h => h) ?_
  rintro evm ⟨caller, msg, child, hcal, hfwd, -, -, -, -, hko⟩
  obtain ⟨-, herr, hevm, -⟩ := hko (hfail caller msg child hcal hfwd)
  exact ⟨by simpa using herr, hevm⟩

/-- EthLib's `RunsAs c G Q` keeps the account of `C` when every stopped frame of `Q` has it in
its state, those messages meet `G`, and `ua` is no precompile. -/
theorem keep_runsAs {ua C : EthLib.Base.Address} {c d : ByteArray}
    {G : Message fork → State.TransactionState → Substate → Prop}
    {Q : Message fork → State.TransactionState → Substate → Evm fork Nat → Prop}
    (hQ : ∀ msg st ss stopped, Q msg st ss stopped →
      stopped.error = none ∧ hasAccount stopped.state C)
    (hG : ∀ msg st ss, Sends message ua c d msg → G msg st ss)
    (hpre : Precompiles.isPrecompile fork ua.toU256.toNat = false) :
    ∀ caller msg child, RunsAs c G Q caller msg child → Sends message ua c d msg →
      child.error = none → hasAccount child.state C := by
  intro caller msg child hrun hfwd' _
  have ⟨_, _, hmt, hmca, hmc, _, hmv, _, _⟩ := hfwd'
  obtain ⟨stopped, hq, hchild⟩ := hrun hmc (by simp [hmt]) (by simp [hmv])
    (by simp [precompileAddress, hmca, hpre]) (hG _ _ _ hfwd')
  obtain ⟨he', hs⟩ := hQ _ _ _ _ hq
  rw [hchild, rollbackOnError_of_error_eq_none he']
  exact hs

/-- `destroyBlackFunds(a)` when deprecated, run by the interpreter's own message runner: for every
upgraded code `c` with a specification (as `meets_of_spec` takes it) whose stopped frames end
with no error, the output `o` (at least 32 bytes) and the contract's account in their state, the
run stops normally in a state `tailState S C a d` (`d` the first word of `o`), or the runner
aborts. -/
theorem runFrame_depD_process (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    (hstatic : message.isStatic = false)
    (hsize : 4 ≤ message.data.size) (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0xf3bdc228) (hv : message.value = 0)
    (hown : callerWord message = ownerOf state message.currentTarget)
    (hl : (storageAt state message.currentTarget (listSlot (addrArg message.data 0))).toNat % 256 ≠ 0)
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0) {c : ByteArray}
    (hcode : state.getCode (state.getAccount (upAddr state message)).codeHash = .ok c)
    (hsz : 0 < c.size) (hszl : c.size < 2 ^ 256)
    (hdel : .pectra ≤ fork → delegatedAddress c = none)
    (hpre : Precompiles.isPrecompile fork (upAddr state message).toU256.toNat = false)
    (hdepth : message.depth + 1 ≤ STACK_DEPTH_LIMIT) {c0 cL c10 cU : Bool}
    (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hcL : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget
      (listSlot (addrArg message.data 0)) = cL)
    (hc10 : coldIn (preSub substate message) message.currentTarget 10 = c10)
    (hcU : decide (upAddr state message ∉ substate.accessedAddresses) = cU)
    {gas : Nat} (hg : preCostD c0 cL c10 cU + 100 ≤ gas)
    (htail : TAIL_MAX ≤ gas - preCostD c0 cL c10 cU - (callGasD fork gas c0 cL c10 cU).cost)
    {G : Message fork → State.TransactionState → Substate → Prop}
    {Q : Message fork → State.TransactionState → Substate → Evm fork Nat → Prop}
    (hspec : ∀ msg st ss, msg.code = c → G msg st ss →
      Spec fork (At c msg 0 [] .empty msg.gas (startState fork msg st) ss) (Q msg st ss))
    (hG : ∀ msg st ss, Sends message (upAddr state message) c (dataB message) msg → G msg st ss)
    {o : ByteArray} (hQ : ∀ msg st ss stopped, Q msg st ss stopped →
      stopped.error = none ∧ stopped.output = o ∧ hasAccount stopped.state message.currentTarget)
    (ho : 32 ≤ o.size) {bound : Nat} {evm : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    (∃ stopped, runFrame (step fork) (step_decreases fork) bound (processRunner fork bound) evm
        within = .ok stopped ∧ stopped.error = none ∧ stopped.output = .empty ∧
      ∃ S : State.TransactionState, stopped.state =
        tailState S message.currentTarget (addrArg message.data 0) (loadWord o 0 32)) ∨
    ∃ e, runFrame (step fork) (step_decreases fork) bound (processRunner fork bound) evm
        within = .error e ∧ e.aborts = true :=
  (spec_depD_answers hfork hglam hstatic hsize hsize' hsel hv hown hl hdep hcode hsz hszl hdel hdepth hc0 hcL hc10
    hcU hg htail
    (answersD_runsAs (fun _ _ _ _ h => ⟨(hQ _ _ _ _ h).1, (hQ _ _ _ _ h).2.1⟩) hG hpre) ho
    (keep_runsAs (fun _ _ _ _ h => ⟨(hQ _ _ _ _ h).1, (hQ _ _ _ _ h).2.2⟩) hG hpre)).runFrame
    (meets_of_spec hspec bound) start within

/-- The specification of `destroyBlackFunds(a)` when deprecated and the upgraded address has no
code: the run reverts with no output before any call. Gas `1497 + prices of slots 0,
isBlackListed[a], 10 + price(address)`. -/
theorem spec_depDNoCode (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    (hsize : 4 ≤ message.data.size) (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0xf3bdc228) (hv : message.value = 0)
    (hown : callerWord message = ownerOf state message.currentTarget)
    (hl : (storageAt state message.currentTarget (listSlot (addrArg message.data 0))).toNat % 256 ≠ 0)
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0)
    (hcode : state.getCode (state.getAccount (upAddr state message)).codeHash = .ok .empty)
    {c0 cL c10 cU : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hcL : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget
      (listSlot (addrArg message.data 0)) = cL)
    (hc10 : coldIn (preSub substate message) message.currentTarget 10 = c10)
    (hcU : decide (upAddr state message ∉ substate.accessedAddresses) = cU)
    {gas : Nat} (hg : 1497 + slotCost c0 + slotCost cL + slotCost c10 + accCost cU ≤ gas) :
    Spec fork (At CODE message 0 [] .empty gas state substate)
      (Halted true .empty (gas - (1497 + slotCost c0 + slotCost cL + slotCost c10 + accCost cU))
        (callStateD state message) (callSubD substate state message)) := by
  simp only [accCost] at hg ⊢
  have hU : storageAt (preState state message) message.currentTarget 10 =
      storageAt state message.currentTarget 10 := by
    simp only [preState, storageAt_readSlot]
  refine Spec.seq (toGetter hfork hsize hsize' hsel hv hown hl hc0 hcL (by omega)) ?_
  step depSet hfork (Or.inr ⟨rfl, rfl⟩) (by simp) (by rw [hU]; exact hdep) hc10 (by gas_ok)
  step fwdArgsD (state := preState state message) hfork (by simp only [addrArg, mask_mask])
    (by simp) (size_mapMem size_MEM0 _ _) (ptr_mapMem size_MEM0 mload_MEM0 _ _) (by gas_ok)
  rw [hU]
  step reshape (g' := gas - (1472 + slotCost c0 + slotCost cL + slotCost c10)) rfl rfl (by gas_ok)
  refine (noCode (gas := gas - (1472 + slotCost c0 + slotCost cL + slotCost c10))
    (st := readSlot (preState state message) message.currentTarget 10)
    (ss := accessSlot (preSub substate message) message.currentTarget 10) (message := message)
    (M := memD message)
    (rest := [upWord (storageAt state message.currentTarget 10), 0, 0x60, 0x24, 0x60, 0x20, 0x84,
      0x70a08231, upWord (storageAt state message.currentTarget 10), 0, addrArg message.data 0,
      0x1f48, 0, addrArg message.data 0, 0x09b6, BitVec.ofNat 256 (selector message.data)])
    hfork hglam (Or.inr (Or.inl rfl)) (by simp) hcode hcU
    (by simp only [accCost]; gas_ok)).consequence (fun _ h => h) ?_
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  exact ⟨hr, he, ho, by rw [hgas]; simp only [accCost]; gas_ok, hs, hss⟩

/-- The loop of the interpreter runs `spec_depDNoCode`'s path to its end. -/
theorem runFrame_depDNoCode (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    (hsize : 4 ≤ message.data.size) (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0xf3bdc228) (hv : message.value = 0)
    (hown : callerWord message = ownerOf state message.currentTarget)
    (hl : (storageAt state message.currentTarget (listSlot (addrArg message.data 0))).toNat % 256 ≠ 0)
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0)
    (hcode : state.getCode (state.getAccount (upAddr state message)).codeHash = .ok .empty)
    {c0 cL c10 cU : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hcL : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget
      (listSlot (addrArg message.data 0)) = cL)
    (hc10 : coldIn (preSub substate message) message.currentTarget 10 = c10)
    (hcU : decide (upAddr state message ∉ substate.accessedAddresses) = cU)
    {gas : Nat} (hg : 1497 + slotCost c0 + slotCost cL + slotCost c10 + accCost cU ≤ gas)
    {bound : Nat} {runChild : MessageRunner fork Nat bound} {evm : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    ∃ stopped, runFrame (step fork) (step_decreases fork) bound runChild evm within =
      .ok stopped ∧
      (Halted true .empty (gas - (1497 + slotCost c0 + slotCost cL + slotCost c10 + accCost cU))
          (callStateD state message) (callSubD substate state message)) stopped :=
  (spec_depDNoCode hfork hglam hsize hsize' hsel hv hown hl hdep hcode hc0 hcL hc10 hcU hg).runFrame
    start within

end UsdtVerify.DeprecatedDestroy
