import UsdtVerify.Usdt.Spec.Deprecated.BalanceOf
import UsdtVerify.Usdt.Spec.Deprecated.Transfer
import UsdtVerify.Usdt.Spec.Getters

/-!
# allowance(owner, spender) when deprecated: the forward to the upgraded contract

The path of a call with selector 0xdd62ed3e, no value, and byte 20 of slot 10 (`deprecated`) set.

- At 2046, the entry (`GettersMap.entry2`) checks that the call has no value, masks the two
  address arguments and calls the getter at 6925 with return address 2132.
- At 6925, the deprecation check (`depSetA`, the bytes of `Deprecated.depSet`); the flag is set,
  so on at 6949.
- At 6949, the code reads slot 10 again and keeps its low 160 bits: `upgradedAddress`.
- It writes 0 at 0x80, the selector 0xdd62ed3e shifted left by 224 bits at 0x60, the owner at
  0x64 and the spender at 0x84 (memory grows to 192 bytes): the call data is the 4 selector bytes
  then the two address words, 68 bytes.
- At 7186, EXTCODESIZE (`toCallA` / `noCodeA`); at 7203, CALL with gas `gasleft - 710`, value
  0, input 68 bytes at 0x60, output 32 bytes at 0x60.
- At 7204, a revert when the call failed (`failTailA`); else the code reads the word at 0x60 and
  returns it through 2132 (`okTailA`, `retAl`).

The blocks `depSetA`, `toCallA`, `noCodeA`, `failTailA` repeat the proofs of the shared blocks
of `Usdt/Spec/Deprecated/TotalSupply.lean` at the pcs of this path.
-/

namespace UsdtVerify.DeprecatedAllowance

open EthLib.Base (Fork U256 toAddressMasked)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts
open UsdtVerify.Complete (Route Routes routeAddr routeCode routeCost routeState routeSub SendsVia
  CallFrom atCallState atCallSub routes_congr routeCost_insert_insert callWithR)
open Deprecated DeprecatedBalance DeprecatedTransfer GettersMap Getters

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate}

/-- The deprecation check at 6925 with the flag set: it reads slot 10 and goes on at 6949. -/
theorem depSetA (hfork : .berlin ≤ fork) {M : ByteArray} {rest : List U256}
    (hrest : rest.length ≤ 16) {c10 : Bool}
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0)
    (hc10 : coldIn substate message.currentTarget 10 = c10)
    {gas : Nat} (hg : 109 + slotCost c10 ≤ gas) :
    Gas.HoareG fork (At CODE message 6925 rest M gas state substate)
      (At CODE message 6949 (0 :: rest) M (gas - (109 + slotCost c10))
        (readSlot state message.currentTarget 10)
        (accessSlot substate message.currentTarget 10)) := by
  have hexp : exponentBytes (0x14 : U256) = 1 := by decide
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
  step binR 0x04 Local.instruction_div
  step pushR 1 (0xff : U256)
  step binR 0x16 Local.instruction_and
  step unR 0x15 instruction_iszero
  step pushAnyR 2
  step jumpi0R (isZero_flag_set hdep)
  exact (repc (by decide)).seq (Gas.reshapeG rfl rfl (by gas_ok))

/-- The selector word that the code writes at 0x60: 0xdd62ed3e shifted left by 224 bits. -/
def SELWA : U256 :=
  mul (0x0100000000000000000000000000000000000000000000000000000000 : U256)
    (bitwiseAnd (0xffffffff : U256) (0xdd62ed3e : U256))

/-- The memory with the selector word at 0x60 (160 bytes). -/
def M1A : ByteArray := memoryWrite M1 96 (wordBytes SELWA)

/-- The owner `a` written at 0x64, over the selector word. -/
abbrev M2A (a : U256) : ByteArray := memoryWrite M1A 100 (wordBytes a)

/-- The spender `b` written at 0x84: the memory grows to 192 bytes. -/
abbrev M3A (a b : U256) : ByteArray := memoryWrite (memoryExtend (M2A a) 32) 132 (wordBytes b)

/-- The 4 bytes of the selector of `allowance(address,address)`. -/
def SEL_A : ByteArray := ⟨#[0xdd, 0x62, 0xed, 0x3e]⟩

theorem size_M1A : M1A.size = 160 := by decide +kernel

theorem mload_M1A : loadWord (memoryReadBytes M1A 64 32) 0 32 = 0x60 := by
  decide +kernel

theorem sel_M1A : memoryReadBytes M1A 96 4 = SEL_A := by decide +kernel

theorem size_M2A (a : U256) : (M2A a).size = 160 := by
  rw [M2A, size_memoryWrite (by rw [size_wordBytes, size_M1A]; decide), size_M1A]

theorem size_M3A (a b : U256) : (M3A a b).size = 192 := by
  rw [M3A, size_memoryWrite (by rw [size_wordBytes, size_memoryExtend, size_M2A]; decide),
    size_memoryExtend, size_M2A]

theorem mload_M2A (a : U256) : loadWord (memoryReadBytes (M2A a) 64 32) 0 32 = 0x60 := by
  rw [M2A, memoryReadBytes_memoryWrite_of_disjoint
    (by rw [size_wordBytes, size_M1A]; decide) (.inl (by decide))]
  exact mload_M1A

theorem mload_M3A (a b : U256) : loadWord (memoryReadBytes (M3A a b) 64 32) 0 32 = 0x60 := by
  rw [M3A, memoryReadBytes_memoryWrite_of_disjoint
    (by rw [size_wordBytes, size_memoryExtend, size_M2A]; decide) (.inl (by decide)),
    read_ext (by rw [size_M2A]; decide)]
  exact mload_M2A a

/-- The 68 bytes from 0x60: the selector, the owner word, the spender word. -/
theorem data_M3A (a b : U256) :
    memoryReadBytes (M3A a b) 96 68 = SEL_A ++ wordBytes a ++ wordBytes b := by
  have h3 := memoryReadBytes_memoryWrite_eq_append (memory := memoryExtend (M2A a) 32)
    (value := wordBytes b) (s := 96) (k := 36)
    (by rw [size_wordBytes, size_memoryExtend, size_M2A]; decide)
  have h2 := memoryReadBytes_memoryWrite_eq_append (memory := M1A) (value := wordBytes a)
    (s := 96) (k := 4) (by rw [size_wordBytes, size_M1A]; decide)
  rw [size_wordBytes] at h3 h2
  rw [M3A, h3, read_ext (by rw [size_M2A]; decide), M2A, h2, sel_M1A]

/-- From 6949: the code reads slot 10 again (warm), keeps the address, writes the call data at
0x60 (the selector, the owner `a` at 0x64, the spender `b` at 0x84) and pushes the operands of
CALL, up to EXTCODESIZE at 7186. The address arguments are already masked. -/
theorem fwdArgsA (hfork : .berlin ≤ fork) {a b : U256} (ha : bitwiseAnd ADDR_MASK a = a)
    (hb : bitwiseAnd ADDR_MASK b = b) {r x : U256} {gas : Nat} (hg : 312 ≤ gas) :
    Gas.HoareG fork (At CODE message 6949 [0, b, a, r, x] MEM0 gas
        (readSlot state message.currentTarget 10) (accessSlot substate message.currentTarget 10))
      (At CODE message 7186
        [upWord (storageAt state message.currentTarget 10),
          upWord (storageAt state message.currentTarget 10), 0, 0x60, 0x44, 0x60, 0x20, 0xa4,
          0xdd62ed3e, upWord (storageAt state message.currentTarget 10), 0, b, a, r, x] (M3A a b)
        (gas - 312) (readSlot state message.currentTarget 10)
        (accessSlot substate message.currentTarget 10)) := by
  have hexp : exponentBytes (0 : U256) = 0 := by decide
  step pushR 1 (0x0a : U256)
  step pushR 1 (0 : U256)
  step swapR 0
  norm
  step Gas.sloadG hfork (cold := false) (by code_fact) (by code_fact)
    (coldIn_accessSlot_self _ _ _) (by gas_ok)
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
  step Gas.reshapeG (s' := [upWord (storageAt state message.currentTarget 10), 0, b, a, r, x])
    (m' := MEM0) (g' := gas - 145)
    (by rw [up_eq, ← storageAt_readSlot state message.currentTarget message.currentTarget 10 10])
    rfl (by gas_ok)
  step pushR 4 (0xdd62ed3e : U256)
  step dupR 4
  step dupR 4
  step pushR 1 (0 : U256)
  step pushR 1 (0x40 : U256)
  have hx0 : extendMemory MEM0.size [((0x40 : U256), (32 : U256))] = ⟨0, 0⟩ := by
    rw [size_MEM0]; decide
  step Gas.mloadG (by code_fact) (by code_fact) (by rw [hx0]; gas_ok)
  step Gas.reshapeG (s' := [0x60, 0, b, a, 0xdd62ed3e, upWord (storageAt state message.currentTarget 10),
      0, b, a, r, x]) (m' := MEM0) (g' := gas - 163)
    (by rw [hx0, memoryExtend_zero, show (0x40 : U256).toNat = 64 from rfl, mload_MEM0])
    (by rw [hx0, memoryExtend_zero]) (by rw [hx0]; gas_ok)
  step pushR 1 (0x20 : U256)
  step binR 0x01 instruction_add
  step Gas.reshapeG (s' := [0x80, 0, b, a, 0xdd62ed3e, upWord (storageAt state message.currentTarget 10),
      0, b, a, r, x]) (m' := MEM0) (g' := gas - 169) rfl rfl (by gas_ok)
  have hx1 : extendMemory MEM0.size [((0x80 : U256), (32 : U256))] = ⟨6, 64⟩ := by
    rw [size_MEM0]; decide
  step Gas.mstoreG (by code_fact) (by code_fact) (by rw [hx1]; gas_ok)
  step Gas.reshapeG (s' := [b, a, 0xdd62ed3e, upWord (storageAt state message.currentTarget 10), 0, b,
      a, r, x]) (m' := M1) (g' := gas - 178) rfl (by rw [hx1]; rfl) (by rw [hx1]; gas_ok)
  step pushR 1 (0x40 : U256)
  have hx2 : extendMemory M1.size [((0x40 : U256), (32 : U256))] = ⟨0, 0⟩ := by
    rw [size_M1]; decide
  step Gas.mloadG (by code_fact) (by code_fact) (by rw [hx2]; gas_ok)
  step Gas.reshapeG (s' := [0x60, b, a, 0xdd62ed3e, upWord (storageAt state message.currentTarget 10),
      0, b, a, r, x]) (m' := M1) (g' := gas - 184)
    (by rw [hx2, show (0x40 : U256).toNat = 64 from rfl, mload_M1])
    (by rw [hx2, memoryExtend_zero]) (by rw [hx2]; gas_ok)
  step dupR 3
  step pushR 4 (0xffffffff : U256)
  step binR 0x16 Local.instruction_and
  step pushR 29 (0x0100000000000000000000000000000000000000000000000000000000 : U256)
  step binR 0x02 Local.instruction_mul
  step dupR 1
  have hx3 : extendMemory M1.size [((0x60 : U256), (32 : U256))] = ⟨0, 0⟩ := by
    rw [size_M1]; decide
  step Gas.mstoreG (by code_fact) (by code_fact) (by rw [hx3]; gas_ok)
  step Gas.reshapeG (s' := [0x60, b, a, 0xdd62ed3e, upWord (storageAt state message.currentTarget 10),
      0, b, a, r, x]) (m' := M1A) (g' := gas - 207) rfl (by rw [hx3, memoryExtend_zero]; rfl)
    (by rw [hx3]; gas_ok)
  step pushR 1 (0x04 : U256)
  step binR 0x01 instruction_add
  have h64 : add (0x04 : U256) (0x60 : U256) = 0x64 := by decide
  rw [h64]
  step dupR 0
  step dupR 3
  step pushR 20 ADDR_MASK
  step binR 0x16 Local.instruction_and
  step pushR 20 ADDR_MASK
  step binR 0x16 Local.instruction_and
  rw [ha, ha]
  step dupR 1
  have hx4 : extendMemory M1A.size [((0x64 : U256), (32 : U256))] = ⟨0, 0⟩ := by
    rw [size_M1A]; decide
  step Gas.mstoreG (by code_fact) (by code_fact) (by rw [hx4]; gas_ok)
  step Gas.reshapeG (s' := [0x64, 0x64, b, a, 0xdd62ed3e,
      upWord (storageAt state message.currentTarget 10), 0, b, a, r, x]) (m' := M2A a)
    (g' := gas - 237) rfl (by rw [hx4, memoryExtend_zero]; rfl) (by rw [hx4]; gas_ok)
  step pushR 1 (0x20 : U256)
  step binR 0x01 instruction_add
  have h84 : add (0x20 : U256) (0x64 : U256) = 0x84 := by decide
  rw [h84]
  step dupR 2
  step pushR 20 ADDR_MASK
  step binR 0x16 Local.instruction_and
  step pushR 20 ADDR_MASK
  step binR 0x16 Local.instruction_and
  rw [hb, hb]
  step dupR 1
  have hx5 : extendMemory (M2A a).size [((0x84 : U256), (32 : U256))] = ⟨3, 32⟩ := by
    rw [size_M2A]; decide
  step Gas.mstoreG (by code_fact) (by code_fact) (by rw [hx5]; gas_ok)
  step Gas.reshapeG (s' := [0x84, 0x64, b, a, 0xdd62ed3e,
      upWord (storageAt state message.currentTarget 10), 0, b, a, r, x]) (m' := M3A a b)
    (g' := gas - 267) rfl (by rw [hx5]; rfl) (by rw [hx5]; gas_ok)
  step pushR 1 (0x20 : U256)
  step binR 0x01 instruction_add
  have ha4 : add (0x20 : U256) (0x84 : U256) = 0xa4 := by decide
  rw [ha4]
  step swapR 2
  step Gas.reshapeG (s' := [a, 0x64, b, 0xa4, 0xdd62ed3e,
      upWord (storageAt state message.currentTarget 10), 0, b, a, r, x]) rfl rfl rfl
  step popR
  step popR
  step popR
  step pushR 1 (0x20 : U256)
  step pushR 1 (0x40 : U256)
  have hx6 : extendMemory (M3A a b).size [((0x40 : U256), (32 : U256))] = ⟨0, 0⟩ := by
    rw [size_M3A]; decide
  step Gas.mloadG (by code_fact) (by code_fact) (by rw [hx6]; gas_ok)
  step Gas.reshapeG (s' := [0x60, 0x20, 0xa4, 0xdd62ed3e,
      upWord (storageAt state message.currentTarget 10), 0, b, a, r, x]) (m' := M3A a b)
    (g' := gas - 291)
    (by rw [hx6, memoryExtend_zero, show (0x40 : U256).toNat = 64 from rfl, mload_M3A])
    (by rw [hx6, memoryExtend_zero]) (by rw [hx6]; gas_ok)
  step dupR 0
  step dupR 3
  step binR 0x03 instruction_sub
  have h44 : sub (0xa4 : U256) (0x60 : U256) = 0x44 := by decide
  rw [h44]
  step dupR 1
  step pushR 1 (0 : U256)
  step dupR 7
  step dupR 0
  exact restate (by decide) (by simp) rfl (by gas_ok)
    (readSlot_readSlot state message.currentTarget 10)
    (accessSlot_accessSlot substate message.currentTarget 10)

/-- At 7186: EXTCODESIZE of the address; the code is not empty, so the JUMPI goes on, then GAS and
the subtraction of 710 give the gas that CALL asks for, at the CALL at 7203 (`Deprecated.toCall`
at these pcs). -/
theorem toCallA (hfork : .berlin ≤ fork) {U : U256}
    {rest : List U256} (hrest : rest.length ≤ 16) {M : ByteArray} {st : State.TransactionState}
    {ss : Substate} {cU : Bool} {c : ByteArray}
    (hcode : st.getCode (st.getAccount (toAddressMasked U)).codeHash = .ok c)
    (hsz : 0 < c.size) (hszl : c.size < 2 ^ 256)
    (hcold : decide (toAddressMasked U ∉ ss.accessedAddresses) = cU)
    {gas : Nat} (hg : extCost fork cU + 28 ≤ gas) :
    Hoare fork (At CODE message 7186 (U :: rest) M gas st ss)
      (At CODE message 7203 (asked (gas - (extCost fork cU + 25)) :: rest) M (gas - (extCost fork cU + 28))
        (st.recordAccountRead (toAddressMasked U))
        { ss with accessedAddresses := ss.accessedAddresses.insert (toAddressMasked U) }) := by
  simp only [extCost] at hg ⊢
  have he : ∀ g : Nat, (g - externalBaseCost fork cU) - OPCODE_ISZERO - OPCODE_ISZERO - 3 -
      10 - 1 - 3 - 2 = g - (externalBaseCost fork cU + 25) := by intro g; gas_ok
  step At.extcodesize hfork (by code_fact) (by code_fact) hcode hcold (by gas_ok)
  step unR 0x15 instruction_iszero
  step unR 0x15 instruction_iszero
  step pushAnyR 2
  step jumpiR (isZero2_ne (ofNat_size_ne hsz hszl))
  step jumpdestR
  step pushR 2 (0x02c6 : U256)
  step At.gas_rule (by code_fact) (by code_fact) (by gas_ok) (by stk_ok)
  step binR 0x03 instruction_sub
  refine (repcH (by decide)).seq (At.reshape ?_ rfl (by gas_ok))
  rw [he]

/-- At 7186, when the upgraded address has no code: EXTCODESIZE pushes 0 and the code reverts
with no output (`Deprecated.noCode` at this pc). -/
theorem noCodeA (hfork : .berlin ≤ fork) {U : U256}
    {rest : List U256} (hrest : rest.length ≤ 16) {M : ByteArray} {st : State.TransactionState}
    {ss : Substate} {cU : Bool}
    (hcode : st.getCode (st.getAccount (toAddressMasked U)).codeHash = .ok .empty)
    (hcold : decide (toAddressMasked U ∉ ss.accessedAddresses) = cU)
    {gas : Nat} (hg : extCost fork cU + 25 ≤ gas) :
    Spec fork (At CODE message 7186 (U :: rest) M gas st ss)
      (Halted true .empty (gas - (extCost fork cU + 25)) (st.recordAccountRead (toAddressMasked U))
        { ss with accessedAddresses := ss.accessedAddresses.insert (toAddressMasked U) }) := by
  simp only [extCost] at hg ⊢
  have hz : extendMemory M.size [((0 : U256), (0 : U256))] = ⟨0, 0⟩ := by
    simp [extendMemory]
  step At.extcodesize hfork (by code_fact) (by code_fact) hcode hcold (by gas_ok)
  step unR 0x15 instruction_iszero
  step unR 0x15 instruction_iszero
  step pushAnyR 2
  step jumpi0R (by decide)
  step pushR 1 (0 : U256)
  step dupR 0
  refine (At.revert (Nat.le_trans (by decide) hfork) (by code_fact)
    (by code_fact) (by rw [hz]; gas_ok)).consequence (fun _ h => h) ?_
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  refine ⟨hr, he, ?_, ?_, hs, hss⟩
  · rw [ho]; simp [memoryReadBytes]
  · rw [hgas, hz]; gas_ok

/-- After a call that failed (flag 0), from 7204: the code reverts with no output
(`Deprecated.failTail` at this pc). -/
theorem failTailA (hfork : .berlin ≤ fork) {M : ByteArray}
    {rest : List U256} (hrest : rest.length ≤ 16) {gas : Nat} (hg : 25 ≤ gas) :
    Gas.SpecG fork (At CODE message 7204 (0 :: rest) M gas state substate)
      (Halted true .empty (gas - 25) state substate) := by
  have hz : extendMemory M.size [((0 : U256), (0 : U256))] = ⟨0, 0⟩ := by
    simp [extendMemory]
  step unR 0x15 instruction_iszero
  step unR 0x15 instruction_iszero
  step pushAnyR 2
  step jumpi0R isZero2_zero
  step pushR 1 (0 : U256)
  step dupR 0
  refine (Gas.revertG (Nat.le_trans (by decide) hfork) (by code_fact)
    (by code_fact) (by rw [hz]; gas_ok)).consequence (fun _ h => h) ?_
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  refine ⟨hr, he, ?_, ?_, hs, hss⟩
  · rw [ho]; simp [memoryReadBytes]
  · rw [hgas, hz]; gas_ok

/-- The return block at 2132 on a memory of 192 bytes (no growth): it writes the top word at the
free memory pointer 0x60 and returns those 32 bytes (`Deprecated.retBig` for 192 bytes). -/
theorem retAl {M : ByteArray} (hM : M.size = 192)
    (hptr : loadWord (memoryReadBytes M 64 32) 0 32 = 0x60) {v x : U256} {gas : Nat}
    (hg : 50 ≤ gas) :
    Gas.SpecG fork (At CODE message 2132 [v, x] M gas state substate)
      (Halted false (wordBytes v) (gas - 50) state substate) := by
  have hext0 : extendMemory M.size [((0x40 : U256), (32 : U256))] = ⟨0, 0⟩ := by
    rw [hM]; decide
  have hext1 : extendMemory M.size [((0x60 : U256), (32 : U256))] = ⟨0, 0⟩ := by
    rw [hM]; decide
  have hfit : 96 + (wordBytes v).size ≤ M.size := by rw [size_wordBytes, hM]; decide
  have hM' : (memoryWrite M 96 (wordBytes v)).size = 192 := by rw [size_memoryWrite hfit, hM]
  have hext2 : extendMemory (memoryWrite M 96 (wordBytes v)).size
      [((0x40 : U256), (32 : U256))] = ⟨0, 0⟩ := by
    rw [hM']; decide
  have hread2 : memoryReadBytes (memoryWrite M 96 (wordBytes v)) 64 32 = memoryReadBytes M 64 32 :=
    memoryReadBytes_memoryWrite_of_disjoint hfit (.inl (by decide))
  step jumpdestR
  step pushR 1 (0x40 : U256)
  step Gas.mloadG (by code_fact) (by code_fact) (by rw [hext0]; gas_ok)
  step Gas.reshapeG (s' := [0x60, v, x]) (m' := M) (g' := gas - 7)
    (by rw [hext0, memoryExtend_zero]; exact congrArg (· :: [v, x]) hptr)
    (by rw [hext0, memoryExtend_zero]) (by rw [hext0]; gas_ok)
  step dupR 0
  step dupR 2
  step dupR 1
  step Gas.mstoreG (by code_fact) (by code_fact) (by rw [hext1]; gas_ok)
  step Gas.reshapeG (s' := [0x60, 0x60, v, x]) (m' := memoryWrite M 96 (wordBytes v)) (g' := gas - 19)
    rfl (by rw [hext1, memoryExtend_zero]; rfl) (by rw [hext1]; gas_ok)
  step pushR 1 (0x20 : U256)
  step binR 0x01 instruction_add
  step swapR 1
  norm
  step popR
  step popR
  step pushR 1 (0x40 : U256)
  step Gas.mloadG (by code_fact) (by code_fact) (by rw [hext2]; gas_ok)
  step Gas.reshapeG (s' := [0x60, 0x80, x]) (m' := memoryWrite M 96 (wordBytes v)) (g' := gas - 38)
    (by rw [hext2, memoryExtend_zero, show (0x40 : U256).toNat = 64 from rfl, hread2, hptr]
        rfl) (by rw [hext2, memoryExtend_zero])
    (by rw [hext2]; gas_ok)
  step dupR 0
  step swapR 1
  norm
  step binR 0x03 instruction_sub
  step swapR 0
  norm
  have hext3 : extendMemory (memoryWrite M 96 (wordBytes v)).size
      [((0x60 : U256), (0x20 : U256))] = ⟨0, 0⟩ := by
    rw [hM']; decide
  refine Gas.SpecG.reshape (s' := [0x60, 0x20, x]) (by rfl) rfl rfl ?_
  refine (Gas.returnG (by code_fact) (by code_fact) (by rw [hext3]; gas_ok)).consequence
    (fun _ h => h) ?_
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  refine ⟨hr, he, ?_, ?_, hs, hss⟩
  · rw [ho, hext3, memoryExtend_zero]
    have h := memoryReadBytes_memoryWrite (memory := M) (start := 96) (value := wordBytes v) hfit
    rw [size_wordBytes] at h
    exact h
  · rw [hgas, hext3]
    gas_ok

/-- After a call that succeeded (flag 1), from 7204: the code reads the word at 0x60 and returns
it through 2132. -/
theorem okTailA {M : ByteArray} (hM : M.size = 192)
    (hptr : loadWord (memoryReadBytes M 64 32) 0 32 = 0x60) {U a b x : U256} {gas : Nat}
    (hg : 128 ≤ gas) :
    Gas.SpecG fork (At CODE message 7204 [1, 0xa4, 0xdd62ed3e, U, 0, b, a, 0x0854, x] M gas state
        substate)
      (Halted false (wordBytes (resWord M)) (gas - 128) state substate) := by
  have hext0 : extendMemory M.size [((0x40 : U256), (32 : U256))] = ⟨0, 0⟩ := by
    rw [hM]; decide
  have hext1 : extendMemory M.size [((0x60 : U256), (32 : U256))] = ⟨0, 0⟩ := by
    rw [hM]; decide
  step unR 0x15 instruction_iszero
  step unR 0x15 instruction_iszero
  step pushR 2 (0x1c2e : U256)
  step jumpiR (by decide)
  step jumpdestR
  step popR
  step popR
  step popR
  step pushR 1 (0x40 : U256)
  step Gas.mloadG (by code_fact) (by code_fact) (by rw [hext0]; gas_ok)
  step Gas.reshapeG (s' := [0x60, 0, b, a, 0x0854, x]) (m' := M) (g' := gas - 32)
    (by rw [hext0, memoryExtend_zero]; exact congrArg (· :: [0, b, a, 0x0854, x]) hptr)
    (by rw [hext0, memoryExtend_zero]) (by rw [hext0]; gas_ok)
  step dupR 0
  step Gas.mloadG (by code_fact) (by code_fact) (by rw [hext1]; gas_ok)
  step Gas.reshapeG (s' := [resWord M, 0x60, 0, b, a, 0x0854, x]) (m' := M) (g' := gas - 38)
    (by rw [hext1, memoryExtend_zero]; rfl) (by rw [hext1, memoryExtend_zero])
    (by rw [hext1]; gas_ok)
  step swapR 0
  norm
  step popR
  step swapR 0
  norm
  step popR
  step pushR 2 (0x1c4c : U256)
  step jumpR
  at_pc 7244
  step jumpdestR
  step swapR 2
  norm
  step swapR 1
  norm
  step popR
  step popR
  step jumpR
  refine (repc (pc' := 2132) (by decide)).seq ?_
  refine (retAl hM hptr (gas := gas - 78) (by gas_ok)).consequence (fun _ h => h) ?_
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  exact ⟨hr, he, ho, by rw [hgas]; gas_ok, hs, hss⟩

theorem size_outMemOfA {B : ByteArray} (hB : B.size = 192) (o : ByteArray) :
    (outMemOf B o).size = 192 := by
  rw [outMemOf, memoryExtend_zero, size_memoryWrite (by rw [ByteArray.size_extract, hB]; omega),
    hB]

theorem mload_outMemOfA {B : ByteArray} (hB : B.size = 192)
    (hptr : loadWord (memoryReadBytes B 64 32) 0 32 = 0x60) (o : ByteArray) :
    loadWord (memoryReadBytes (outMemOf B o) 64 32) 0 32 = 0x60 := by
  rw [outMemOf, memoryExtend_zero, memoryReadBytes_memoryWrite_of_disjoint
    (by rw [ByteArray.size_extract, hB]; omega) (.inl (by decide))]
  exact hptr

theorem resWord_outMemOfA {B : ByteArray} (hB : B.size = 192) {o : ByteArray}
    (ho : 32 ≤ o.size) : resWord (outMemOf B o) = loadWord o 0 32 := by
  have hm : min 32 o.size = 32 := Nat.min_eq_left ho
  have hs : (o.extract 0 32).size = 32 := by rw [ByteArray.size_extract]; omega
  have hfit : 96 + (o.extract 0 32).size ≤ (memoryExtend B 0).size := by
    rw [hs, memoryExtend_zero, hB]; decide
  have h := memoryReadBytes_memoryWrite hfit
  rw [hs] at h
  rw [resWord, outMemOf, hm, h]
  unfold loadWord bufferRead
  congr 2
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  rw [EthLib.Base.byteAt_extract, ite_eq_left (by omega), Nat.zero_add]

/-- The gas of the path from pc 0 to the CALL, for `allowance`. -/
abbrev preCostAl (fork : Fork) (c10 cU : Bool) : Nat := 1187 + slotCost c10 + extCost fork cU

/-- The gas that the code asks CALL to pass on, for a frame that starts with `gas`. -/
abbrev askedOfAl (fork : Fork) (gas : Nat) (c10 cU : Bool) : U256 :=
  asked (gas - (1184 + slotCost c10 + extCost fork cU))

/-- What CALL pays and passes on (EIP-150, EIP-2929; the address is warm after EXTCODESIZE). -/
abbrev callGasAl (fork : Fork) (gas : Nat) (c10 cU : Bool) (R : Nat) :
    MessageCallGas :=
  messageCallGas fork 0 (askedOfAl fork gas c10 cU).toNat (gas - preCostAl fork c10 cU) 0 (100 + R)

/-- The call data that the code forwards: the selector of `allowance`, then the owner and the
spender words (each masked to 160 bits). -/
abbrev dataAl (message : Message fork) : ByteArray :=
  SEL_A ++ wordBytes (addrArg message.data 0) ++ wordBytes (addrArg message.data 1)

/-- The memory before the call. -/
abbrev memAl (message : Message fork) : ByteArray :=
  M3A (addrArg message.data 0) (addrArg message.data 1)

/-- From pc 0 to the CALL at 7203, when deprecated and the upgraded account has code. -/
theorem preCallAl (hfork : .berlin ≤ fork)
    (hsize : 4 ≤ message.data.size) (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0xdd62ed3e) (hv : message.value = 0)
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0) {c : ByteArray}
    (hcode : state.getCode (state.getAccount (upAddr state message)).codeHash = .ok c)
    (hsz : 0 < c.size) (hszl : c.size < 2 ^ 256) {c10 cU : Bool}
    (hc10 : coldIn substate message.currentTarget 10 = c10)
    (hcU : decide (upAddr state message ∉ substate.accessedAddresses) = cU)
    {gas : Nat} (hg : preCostAl fork c10 cU ≤ gas) :
    Hoare fork (At CODE message 0 [] .empty gas state substate)
      (At CODE message 7203
        [askedOfAl fork gas c10 cU, upWord (storageAt state message.currentTarget 10), 0, 0x60, 0x44,
          0x60, 0x20, 0xa4, 0xdd62ed3e, upWord (storageAt state message.currentTarget 10), 0,
          addrArg message.data 1, addrArg message.data 0, BitVec.ofNat 256 2132,
          BitVec.ofNat 256 (selector message.data)]
        (memAl message) (gas - preCostAl fork c10 cU) (callState state message)
        (callSub substate state message)) := by
  simp only [preCostAl, askedOfAl, extCost] at hg ⊢
  refine Gas.Triple.seqL ((toEntry (t := 26) (e := 2046) (by decide) hsize hsize' hsel (by omega)).seq
    (entry2 (r := 2132) (b := 6925) (by decide) hv (by omega))) ?_
  step depSetA hfork (by simp) hdep hc10 (by gas_ok)
  step fwdArgsA (state := state) hfork (by simp only [addrArg, mask_mask])
    (by simp only [addrArg, mask_mask]) (by gas_ok)
  step At.reshape (g' := gas - (1159 + slotCost c10)) rfl rfl (by gas_ok)
  refine (toCallA (gas := gas - (1159 + slotCost c10))
    (st := readSlot state message.currentTarget 10)
    (ss := accessSlot substate message.currentTarget 10) (message := message)
    (M := memAl message)
    (rest := [upWord (storageAt state message.currentTarget 10), 0, 0x60, 0x44, 0x60, 0x20, 0xa4,
      0xdd62ed3e, upWord (storageAt state message.currentTarget 10), 0, addrArg message.data 1,
      addrArg message.data 0, BitVec.ofNat 256 2132, BitVec.ofNat 256 (selector message.data)])
    hfork (by simp) hcode hsz hszl hcU (by simp only [extCost]; gas_ok)).seq ?_
  refine At.reshape ?_ rfl (by simp only [extCost]; gas_ok)
  simp only [List.cons.injEq, and_true]
  congr 1
  unfold extCost; omega

/-- `spec_depAl` with the bound `htail` (at least 128 gas left after the price of the CALL) replaced by
`hcg`: every ended forwarded message that meets `callee`, sent with the gas the CALL gives from
the caller frame at the CALL (`CallFrom`, round 30), leaves at least 128 gas for the code after
the CALL, the gas the CALL keeps plus the gas left in the ended frame.
Stated as a `SpecOn` (round 26): the frames that end the runner's messages meet
`callee`, the runner may fail with any error, and the run ends as stated or at a failure of the
runner on a forwarded message (`SendsVia`); `.toUnder` gives EthLib's `SpecUnder`. -/
theorem spec_depAl_g (hfork : .berlin ≤ fork)
    (hsize : 4 ≤ message.data.size) (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0xdd62ed3e) (hv : message.value = 0)
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0) {c : ByteArray}
    (hcode : state.getCode (state.getAccount (upAddr state message)).codeHash = .ok c)
    (hsz : 0 < c.size) (hszl : c.size < 2 ^ 256)
    {r : Route} (hroute : Routes fork state c r)
    (hdepth : message.depth + 1 ≤ STACK_DEPTH_LIMIT) {c10 cU : Bool}
    (hc10 : coldIn substate message.currentTarget 10 = c10)
    (hcU : decide (upAddr state message ∉ substate.accessedAddresses) = cU)
    {gas : Nat} (hg : preCostAl fork c10 cU + 100 + callR substate state message r ≤ gas)
    {callee : Evm fork Nat → Message fork → Evm fork Nat → Prop}
    (hcg : ∀ caller msg child, callee caller msg child →
      SendsVia message (upAddr state message) c r (dataAl message) msg →
      CallFrom (callGasAl fork gas c10 cU (callR substate state message r)).subCall
        (atCallState (callState state message) (upAddr state message) r message.currentTarget)
        (atCallSub (callSub substate state message) (upAddr state message) r) caller msg →
      128 ≤ gas - preCostAl fork c10 cU - (callGasAl fork gas c10 cU (callR substate state message r)).cost + child.gas) :
    SpecOn fork callee (fun caller msg => SendsVia message (upAddr state message) c r (dataAl message) msg ∧
      CallFrom (callGasAl fork gas c10 cU (callR substate state message r)).subCall (atCallState (callState state message) (upAddr state message) r message.currentTarget) (atCallSub (callSub substate state message) (upAddr state message) r) caller msg)
      (At CODE message 0 [] .empty gas state substate)
      fun evm => ∃ caller msg child, callee caller msg child ∧
        SendsVia message (upAddr state message) c r (dataAl message) msg ∧
        msg.gas = (callGasAl fork gas c10 cU (callR substate state message r)).subCall ∧
        caller.state = (routeState ((callState state message).recordAccountRead
          (upAddr state message)) r).recordAccountRead message.currentTarget ∧
        caller.substate = routeSub { callSub substate state message with
          accessedAddresses :=
            (callSub substate state message).accessedAddresses.insert (upAddr state message) } r ∧
        (child.error = none →
          Halted false (wordBytes (resWord (outMemOf (memAl message) child.output)))
            (gas - preCostAl fork c10 cU - (callGasAl fork gas c10 cU (callR substate state message r)).cost + child.gas - 128)
            (incorporateChild fork caller child).state
            (incorporateChild fork caller child).substate evm) ∧
        (child.error ≠ none →
          Halted true .empty
            (gas - preCostAl fork c10 cU - (callGasAl fork gas c10 cU (callR substate state message r)).cost + child.gas - 25)
            (incorporateChild fork caller child).state
            (incorporateChild fork caller child).substate evm) := by
  have hext : extendMemory (memAl message).size
      [((0x60 : U256), (0x44 : U256)), ((0x60 : U256), (0x20 : U256))] = ⟨0, 0⟩ := by
    rw [size_M3A]; decide
  have hR : routeCost fork ((callSub substate state message).accessedAddresses.insert
      (toAddressMasked (upWord (storageAt state message.currentTarget 10)))) r =
      callR substate state message r := routeCost_insert_insert _ _ _
  have hcall := Complete.callWithRS (fork := fork) (code := CODE) (message := message) (pc := 7203)
    (memory := memAl message) (gas := gas - preCostAl fork c10 cU)
    (state := callState state message)
    (substate := callSub substate state message) (callee := callee)
    (asked := askedOfAl fork gas c10 cU) (to := upWord (storageAt state message.currentTarget 10))
    (i := 0x60) (isz := 0x44) (o := 0x60) (osz := 0x20)
    (rest := [0xa4, 0xdd62ed3e, upWord (storageAt state message.currentTarget 10), 0,
      addrArg message.data 1, addrArg message.data 0, BitVec.ofNat 256 2132,
      BitVec.ofNat 256 (selector message.data)]) (cold := false)
    hfork (by code_fact) (by code_fact) hcode (routes_congr (fun _ => rfl) hroute) hdepth
    (by simp [upAddr])
    (by rw [hext, hR]; simp only [accCost_false]; omega)
  rw [hext, hR] at hcall
  simp only [accCost_false] at hcall
  have hcall := hcall.mono (S' := (fun caller msg => SendsVia message (upAddr state message) c r (dataAl message) msg ∧
      CallFrom (callGasAl fork gas c10 cU (callR substate state message r)).subCall (atCallState (callState state message) (upAddr state message) r message.currentTarget) (atCallSub (callSub substate state message) (upAddr state message) r) caller msg))
    fun _ _ h => by
    obtain ⟨⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩, b1, b2, b3⟩ := h
    exact ⟨⟨a1, a2, a3, a4, a5, a6, by rw [a7, memoryExtend_zero]; exact data_M3A _ _, a8, a9, a10⟩, b3, b1, b2⟩
  refine SpecOn.seq (HoareOn.of_hoare (preCallAl hfork hsize hsize' hsel hv hdep
    hcode hsz hszl hc10 hcU (by omega))) (HoareOn.seq hcall (HoareOn.of_hoare ?_))
  rintro evm ⟨caller, msg, child, hcal, -, hcs, hcss, hmg, hmc, hmt, hmtg, hmca, hmcode, hmdp, hmd, hmv,
    hmdep, hmst, hat⟩
  have hfwd : SendsVia message (upAddr state message) c r (dataAl message) msg := by
    refine ⟨hmc, hmt, hmtg, hmca, hmcode, hmdp, ?_, hmv, hmdep, hmst⟩
    rw [hmd, memoryExtend_zero]; exact data_M3A _ _
  have hT := hcg caller msg child hcal hfwd ⟨hmg, hcs, hcss⟩
  have hB := size_M3A (addrArg message.data 0) (addrArg message.data 1)
  by_cases he : child.error = none
  · simp only [he, Option.isNone_none, ↓reduceIte] at hat
    obtain ⟨after, hreach, hrun, hq⟩ := okTailA (fork := fork) (message := message)
      (state := (incorporateChild fork caller child).state)
      (substate := (incorporateChild fork caller child).substate)
      (U := upWord (storageAt state message.currentTarget 10)) (a := addrArg message.data 0)
      (b := addrArg message.data 1)
      (size_outMemOfA hB child.output) (mload_outMemOfA hB (mload_M3A _ _) child.output)
      (x := BitVec.ofNat 256 (selector message.data))
      (gas := gas - preCostAl fork c10 cU - ((callGasAl fork gas c10 cU (callR substate state message r)).cost + 0) + child.gas)
      (by omega) evm hat
    refine ⟨after, Gas.reaches_toStep hreach, hrun, caller, msg, child, hcal, hfwd, hmg, hcs, hcss, fun _ => ?_,
      fun h => absurd he h⟩
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hq
    exact ⟨h1, h2, h3, by rw [h4]; omega, h5, h6⟩
  · have hz : child.error.isNone = false := by
      cases h : child.error
      · exact absurd h he
      · rfl
    simp only [hz, Bool.false_eq_true, ↓reduceIte] at hat
    obtain ⟨after, hreach, hrun, hq⟩ := failTailA (fork := fork) (message := message)
      (state := (incorporateChild fork caller child).state)
      (substate := (incorporateChild fork caller child).substate) hfork
      (rest := [0xa4, 0xdd62ed3e,
        upWord (storageAt state message.currentTarget 10), 0, addrArg message.data 1,
        addrArg message.data 0, BitVec.ofNat 256 2132, BitVec.ofNat 256 (selector message.data)])
      (by simp)
      (gas := gas - preCostAl fork c10 cU - ((callGasAl fork gas c10 cU (callR substate state message r)).cost + 0) + child.gas)
      (by omega) evm hat
    refine ⟨after, Gas.reaches_toStep hreach, hrun, caller, msg, child, hcal, hfwd, hmg, hcs, hcss,
      fun h => absurd h he, fun _ => ?_⟩
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hq
    exact ⟨h1, h2, h3, by rw [h4]; omega, h5, h6⟩

/-- The specification of `allowance(owner, spender)` when deprecated, for every callee.

Hypotheses as `DeprecatedBalance.spec_depB` with selector 0xdd62ed3e and the gas of this path
(`preCostAl`, `callGasAl`, 128 gas after the price of the CALL). Then under every runner whose
ended messages meet `callee`, the run ends (or the runner aborts) in a stopped frame for which
there are a caller frame, a message `msg` and an ended frame `child` with
`callee caller msg child`, `msg` sent to `ua` along the route `r` (`SendsVia`) with data
`0xdd62ed3e ++ owner ++ spender`
(`dataAl`; argument words 0 and 1 masked to 160 bits) and no value, and: if `child` ended with no
error, the frame returns the 32 bytes of the word at 0x60 after CALL wrote the first
`min 32 (output size)` bytes of `child`'s output there; otherwise it reverts with no output. -/
theorem spec_depAl (hfork : .berlin ≤ fork)
    (hsize : 4 ≤ message.data.size) (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0xdd62ed3e) (hv : message.value = 0)
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0) {c : ByteArray}
    (hcode : state.getCode (state.getAccount (upAddr state message)).codeHash = .ok c)
    (hsz : 0 < c.size) (hszl : c.size < 2 ^ 256)
    {r : Route} (hroute : Routes fork state c r)
    (hdepth : message.depth + 1 ≤ STACK_DEPTH_LIMIT) {c10 cU : Bool}
    (hc10 : coldIn substate message.currentTarget 10 = c10)
    (hcU : decide (upAddr state message ∉ substate.accessedAddresses) = cU)
    {gas : Nat} (hg : preCostAl fork c10 cU + 100 + callR substate state message r ≤ gas)
    (htail : 128 ≤ gas - preCostAl fork c10 cU - (callGasAl fork gas c10 cU (callR substate state message r)).cost)
    {callee : Evm fork Nat → Message fork → Evm fork Nat → Prop} :
    SpecUnder fork callee (At CODE message 0 [] .empty gas state substate)
      fun evm => ∃ caller msg child, callee caller msg child ∧
        SendsVia message (upAddr state message) c r (dataAl message) msg ∧
        msg.gas = (callGasAl fork gas c10 cU (callR substate state message r)).subCall ∧
        caller.state = (routeState ((callState state message).recordAccountRead
          (upAddr state message)) r).recordAccountRead message.currentTarget ∧
        caller.substate = routeSub { callSub substate state message with
          accessedAddresses :=
            (callSub substate state message).accessedAddresses.insert (upAddr state message) } r ∧
        (child.error = none →
          Halted false (wordBytes (resWord (outMemOf (memAl message) child.output)))
            (gas - preCostAl fork c10 cU - (callGasAl fork gas c10 cU (callR substate state message r)).cost + child.gas - 128)
            (incorporateChild fork caller child).state
            (incorporateChild fork caller child).substate evm) ∧
        (child.error ≠ none →
          Halted true .empty
            (gas - preCostAl fork c10 cU - (callGasAl fork gas c10 cU (callR substate state message r)).cost + child.gas - 25)
            (incorporateChild fork caller child).state
            (incorporateChild fork caller child).substate evm) := by
  apply SpecOn.toUnder
  apply spec_depAl_g
  all_goals first | assumption | (intro _ _ _ _ _ _; omega)

/-- `allowance(owner, spender)` when deprecated, for a callee that answers `o` (at least 32
bytes) to the forwarded call: the run returns the first word of `o`, with no error. -/
theorem spec_depAl_answers (hfork : .berlin ≤ fork)
    (hsize : 4 ≤ message.data.size) (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0xdd62ed3e) (hv : message.value = 0)
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0) {c : ByteArray}
    (hcode : state.getCode (state.getAccount (upAddr state message)).codeHash = .ok c)
    (hsz : 0 < c.size) (hszl : c.size < 2 ^ 256)
    {r : Route} (hroute : Routes fork state c r)
    (hdepth : message.depth + 1 ≤ STACK_DEPTH_LIMIT) {c10 cU : Bool}
    (hc10 : coldIn substate message.currentTarget 10 = c10)
    (hcU : decide (upAddr state message ∉ substate.accessedAddresses) = cU)
    {gas : Nat} (hg : preCostAl fork c10 cU + 100 + callR substate state message r ≤ gas)
    (htail : 128 ≤ gas - preCostAl fork c10 cU - (callGasAl fork gas c10 cU (callR substate state message r)).cost)
    {callee : Evm fork Nat → Message fork → Evm fork Nat → Prop} {o : ByteArray}
    (hans : AnswersD message (upAddr state message) c r (dataAl message) o callee)
    (ho : 32 ≤ o.size) :
    SpecUnder fork callee (At CODE message 0 [] .empty gas state substate)
      fun evm => evm.error = none ∧ evm.output = wordBytes (loadWord o 0 32) := by
  refine (spec_depAl hfork hsize hsize' hsel hv hdep hcode hsz hszl hroute hdepth hc10 hcU hg
    htail).consequence (fun _ h => h) ?_
  rintro evm ⟨caller, msg, child, hcal, hfwd, -, -, -, hok, -⟩
  obtain ⟨he, hout⟩ := hans caller msg child hcal hfwd
  obtain ⟨-, herr, hevm, -⟩ := hok he
  refine ⟨by simpa using herr, ?_⟩
  rw [hevm, hout, resWord_outMemOfA (size_M3A _ _) ho]

/-- `allowance(owner, spender)` when deprecated, for a callee whose answer fails: the run reverts
with no output. -/
theorem spec_depAl_fails (hfork : .berlin ≤ fork)
    (hsize : 4 ≤ message.data.size) (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0xdd62ed3e) (hv : message.value = 0)
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0) {c : ByteArray}
    (hcode : state.getCode (state.getAccount (upAddr state message)).codeHash = .ok c)
    (hsz : 0 < c.size) (hszl : c.size < 2 ^ 256)
    {r : Route} (hroute : Routes fork state c r)
    (hdepth : message.depth + 1 ≤ STACK_DEPTH_LIMIT) {c10 cU : Bool}
    (hc10 : coldIn substate message.currentTarget 10 = c10)
    (hcU : decide (upAddr state message ∉ substate.accessedAddresses) = cU)
    {gas : Nat} (hg : preCostAl fork c10 cU + 100 + callR substate state message r ≤ gas)
    (htail : 128 ≤ gas - preCostAl fork c10 cU - (callGasAl fork gas c10 cU (callR substate state message r)).cost)
    {callee : Evm fork Nat → Message fork → Evm fork Nat → Prop}
    (hfail : ∀ caller msg child, callee caller msg child →
      SendsVia message (upAddr state message) c r (dataAl message) msg → child.error ≠ none) :
    SpecUnder fork callee (At CODE message 0 [] .empty gas state substate)
      fun evm => evm.error = some .revert ∧ evm.output = .empty := by
  refine (spec_depAl hfork hsize hsize' hsel hv hdep hcode hsz hszl hroute hdepth hc10 hcU hg
    htail).consequence (fun _ h => h) ?_
  rintro evm ⟨caller, msg, child, hcal, hfwd, -, -, -, -, hko⟩
  obtain ⟨-, herr, hevm, -⟩ := hko (hfail caller msg child hcal hfwd)
  exact ⟨by simpa using herr, hevm⟩

/-- `allowance(owner, spender)` when deprecated, run by the interpreter's own message runner: for
every upgraded code `c` with a specification (as `meets_of_spec` takes it) whose stopped frames
end with no error and the output `o` (at least 32 bytes), the run returns the first word of `o`,
or the runner aborts. -/
theorem runFrame_depAl_process (hfork : .berlin ≤ fork)
    (hsize : 4 ≤ message.data.size) (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0xdd62ed3e) (hv : message.value = 0)
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0) {c : ByteArray}
    (hcode : state.getCode (state.getAccount (upAddr state message)).codeHash = .ok c)
    (hsz : 0 < c.size) (hszl : c.size < 2 ^ 256)
    {r : Route} (hroute : Routes fork state c r)
    (hpre : Precompiles.isPrecompile fork (routeAddr (upAddr state message) r).toU256.toNat = false)
    (hdepth : message.depth + 1 ≤ STACK_DEPTH_LIMIT) {c10 cU : Bool}
    (hc10 : coldIn substate message.currentTarget 10 = c10)
    (hcU : decide (upAddr state message ∉ substate.accessedAddresses) = cU)
    {gas : Nat} (hg : preCostAl fork c10 cU + 100 + callR substate state message r ≤ gas)
    (htail : 128 ≤ gas - preCostAl fork c10 cU - (callGasAl fork gas c10 cU (callR substate state message r)).cost)
    {G : Message fork → State.TransactionState → Substate → Prop}
    {Q : Message fork → State.TransactionState → Substate → Evm fork Nat → Prop}
    (hspec : ∀ msg st ss, msg.code = routeCode c r → G msg st ss →
      Spec fork (At (routeCode c r) msg 0 [] .empty msg.gas (startState fork msg st) ss)
        (Q msg st ss))
    (hG : ∀ msg st ss, SendsVia message (upAddr state message) c r (dataAl message) msg →
      G msg st ss)
    {o : ByteArray} (hQ : ∀ msg st ss stopped, Q msg st ss stopped →
      stopped.error = none ∧ stopped.output = o) (ho : 32 ≤ o.size)
    {bound : Nat} {evm : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    (∃ stopped, runFrame (step fork) (step_decreases fork) bound (processRunner fork bound) evm
        within = .ok stopped ∧ stopped.error = none ∧
      stopped.output = wordBytes (loadWord o 0 32)) ∨
    ∃ e, runFrame (step fork) (step_decreases fork) bound (processRunner fork bound) evm
        within = .error e ∧ e.aborts = true :=
  (spec_depAl_answers hfork hsize hsize' hsel hv hdep hcode hsz hszl hroute hdepth hc10 hcU
    hg htail (answersD_runsAs hQ hG hpre) ho).runFrame (meets_of_specAt hspec bound) start within

/-- The specification of `allowance(owner, spender)` when deprecated and the upgraded address has
no code: the run reverts with no output before any call. Gas `1184 + price(slot 10) +
price(address)`. -/
theorem spec_depAlNoCode (hfork : .berlin ≤ fork)
    (hsize : 4 ≤ message.data.size) (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0xdd62ed3e) (hv : message.value = 0)
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0)
    (hcode : state.getCode (state.getAccount (upAddr state message)).codeHash = .ok .empty)
    {c10 cU : Bool} (hc10 : coldIn substate message.currentTarget 10 = c10)
    (hcU : decide (upAddr state message ∉ substate.accessedAddresses) = cU)
    {gas : Nat} (hg : 1184 + slotCost c10 + extCost fork cU ≤ gas) :
    Spec fork (At CODE message 0 [] .empty gas state substate)
      (Halted true .empty (gas - (1184 + slotCost c10 + extCost fork cU)) (callState state message)
        (callSub substate state message)) := by
  simp only [extCost] at hg ⊢
  refine Gas.Triple.seqL ((toEntry (t := 26) (e := 2046) (by decide) hsize hsize' hsel (by omega)).seq
    (entry2 (r := 2132) (b := 6925) (by decide) hv (by omega))) ?_
  step depSetA hfork (by simp) hdep hc10 (by gas_ok)
  step fwdArgsA (state := state) hfork (by simp only [addrArg, mask_mask])
    (by simp only [addrArg, mask_mask]) (by gas_ok)
  step At.reshape (g' := gas - (1159 + slotCost c10)) rfl rfl (by gas_ok)
  refine (noCodeA (gas := gas - (1159 + slotCost c10))
    (st := readSlot state message.currentTarget 10)
    (ss := accessSlot substate message.currentTarget 10) (message := message)
    (M := memAl message)
    (rest := [upWord (storageAt state message.currentTarget 10), 0, 0x60, 0x44, 0x60, 0x20, 0xa4,
      0xdd62ed3e, upWord (storageAt state message.currentTarget 10), 0, addrArg message.data 1,
      addrArg message.data 0, BitVec.ofNat 256 2132, BitVec.ofNat 256 (selector message.data)])
    hfork (by simp) hcode hcU (by simp only [extCost]; gas_ok)).consequence
    (fun _ h => h) ?_
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  exact ⟨hr, he, ho, by rw [hgas]; simp only [extCost]; gas_ok, hs, hss⟩

/-- `spec_depAlNoCode` for the interpreter loop. -/
theorem runFrame_depAlNoCode (hfork : .berlin ≤ fork)
    (hsize : 4 ≤ message.data.size) (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0xdd62ed3e) (hv : message.value = 0)
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0)
    (hcode : state.getCode (state.getAccount (upAddr state message)).codeHash = .ok .empty)
    {c10 cU : Bool} (hc10 : coldIn substate message.currentTarget 10 = c10)
    (hcU : decide (upAddr state message ∉ substate.accessedAddresses) = cU)
    {gas : Nat} (hg : 1184 + slotCost c10 + extCost fork cU ≤ gas)
    {bound : Nat} {runChild : MessageRunner fork Nat bound} {evm : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    ∃ stopped, runFrame (step fork) (step_decreases fork) bound runChild evm within =
      .ok stopped ∧
      (Halted true .empty (gas - (1184 + slotCost c10 + extCost fork cU)) (callState state message)
          (callSub substate state message)) stopped :=
  (spec_depAlNoCode hfork hsize hsize' hsel hv hdep hcode hc10 hcU hg).runFrame start within

end UsdtVerify.DeprecatedAllowance
