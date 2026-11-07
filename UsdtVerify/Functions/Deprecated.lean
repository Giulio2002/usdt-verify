import UsdtVerify.Functions.TotalSupply
import EthLib.Execution.Proofs.Evm.Logic.Call
import UsdtVerify.Spec.Write
import EthLib.Execution.Proofs.Evm.Logic.Callee

/-!
# totalSupply() when deprecated: the forward to the upgraded contract

The path of a call with selector 0x18160ddd, no value, and byte 20 of slot 10 (`deprecated`) set.

- At 3565, the getter reads slot 10 and tests byte 20; the flag is set, so it goes on at 3589.
- At 3589, it reads slot 10 again and keeps its low 160 bits: `upgradedAddress`.
- It writes 0 at 0x80 and the selector 0x18160ddd, shifted left by 224 bits, at 0x60.
- At 3719, EXTCODESIZE of the address; at 3725 a JUMPI reverts when the size is 0.
- At 3734, GAS; at 3736, CALL with gas `gasleft - 710`, value 0, input 4 bytes at 0x60, output
  32 bytes at 0x60.
- At 3742, a JUMPI reverts (empty output) when the call failed.
- At 3747, the code reads the word at 0x60 and returns to 797, which returns that word.
-/

namespace UsdtVerify.Deprecated

open EthLib.Base (Fork U256 toAddressMasked)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate}

/-- A set flag makes the ISZERO of its test word 0. -/
theorem isZero_flag_set {w : U256} (h : byte20 w ≠ 0) :
    isZero (bitwiseAnd (0xff : U256) (div w (exp (0x0100 : U256) (0x14 : U256)))) = 0 := by
  rw [flag_eq]
  have hb : byte20 w < 256 := Nat.mod_lt _ (by decide)
  have hne : (BitVec.ofNat 256 (byte20 w) : U256) ≠ 0 := by
    intro hz
    have := congrArg BitVec.toNat hz
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
    exact h this
  unfold isZero
  exact ite_eq_right hne

/-- The deprecation check at 3565 (totalSupply) or 4665 (balanceOf) with the flag set: it reads slot
10 and goes on at 3589 or 4689. -/
theorem depSet (hfork : .berlin ≤ fork) {p q : Nat}
    (hp : (p = 3565 ∧ q = 3589) ∨ (p = 4665 ∧ q = 4689)) {M : ByteArray} {rest : List U256}
    (hrest : rest.length ≤ 16) {c10 : Bool}
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0)
    (hc10 : coldIn substate message.currentTarget 10 = c10)
    {gas : Nat} (hg : 109 + slotCost c10 ≤ gas) :
    Hoare fork (At CODE message p rest M gas state substate)
      (At CODE message q (0 :: rest) M (gas - (109 + slotCost c10))
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
    step jumpi0R (isZero_flag_set hdep)
    exact (repc (by decide)).seq (reshape rfl rfl (by gas_ok))

/-- The memory after the write of 0 at 0x80 (160 bytes). -/
def M1 : ByteArray := memoryWrite (memoryExtend MEM0 64) 128 (wordBytes 0)

/-- The selector word that the code writes at 0x60: 0x18160ddd shifted left by 224 bits. -/
def SELW : U256 :=
  mul (0x0100000000000000000000000000000000000000000000000000000000 : U256)
    (bitwiseAnd (0xffffffff : U256) (0x18160ddd : U256))

/-- The memory before the call: the selector word at 0x60 (160 bytes). -/
def M2 : ByteArray := memoryWrite M1 96 (wordBytes SELW)

/-- The call data that the code forwards: the 4 bytes of the selector of `totalSupply()`. -/
def SEL_TS : ByteArray := ⟨#[0x18, 0x16, 0x0d, 0xdd]⟩

theorem size_M1 : M1.size = 160 := by decide +kernel

theorem size_M2 : M2.size = 160 := by decide +kernel

theorem mload_M1 : loadWord (memoryReadBytes (memoryExtend M1 0) 64 32) 0 32 = 0x60 := by
  decide +kernel

theorem mload_M2 : loadWord (memoryReadBytes (memoryExtend M2 0) 64 32) 0 32 = 0x60 := by
  decide +kernel

theorem data_M2 : memoryReadBytes (memoryExtend M2 0) 96 4 = SEL_TS := by decide +kernel

/-- The upgraded address as the code computes it: the low 160 bits of slot 10. -/
abbrev upWord (w : U256) : U256 := bitwiseAnd ADDR_MASK w

theorem up_eq (w : U256) :
    bitwiseAnd ADDR_MASK (bitwiseAnd ADDR_MASK (div w (exp (0x0100 : U256) (0 : U256)))) =
      upWord w := by
  have he : exp (0x0100 : U256) (0 : U256) = 1 := by decide +kernel
  have hd : div w 1 = w := by
    apply BitVec.eq_of_toNat_eq
    simp [div]
  rw [he, hd]
  simp only [upWord, bitwiseAnd, ← BitVec.and_assoc, BitVec.and_self]

/-- From 3589: the code reads slot 10 again (warm), keeps the address, writes the call data at
0x60 and pushes the operands of CALL, up to EXTCODESIZE at 3719. -/
theorem fwdArgs (hfork : .berlin ≤ fork) {rest : List U256} (hrest : rest.length ≤ 4)
    {gas : Nat} (hg : 237 ≤ gas) :
    Hoare fork (At CODE message 3589 (0 :: rest) MEM0 gas
        (readSlot state message.currentTarget 10) (accessSlot substate message.currentTarget 10))
      (At CODE message 3719
        ([upWord (storageAt state message.currentTarget 10),
          upWord (storageAt state message.currentTarget 10), 0, 0x60, 4, 0x60, 0x20, 0x64,
          0x18160ddd, upWord (storageAt state message.currentTarget 10), 0] ++ rest) M2
        (gas - 237) (readSlot state message.currentTarget 10)
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
  step reshape (s' := [upWord (storageAt state message.currentTarget 10), 0] ++ rest)
    (m' := MEM0) (g' := gas - 145)
    (by rw [up_eq, ← storageAt_readSlot state message.currentTarget message.currentTarget 10 10]
        rfl) rfl (by gas_ok)
  step pushR 4 (0x18160ddd : U256)
  step pushR 1 (0 : U256)
  step pushR 1 (0x40 : U256)
  have hx0 : extendMemory MEM0.size [((0x40 : U256), (32 : U256))] = ⟨0, 0⟩ := by
    rw [size_MEM0]; decide
  step mload (by code_fact) (by code_fact) (by rw [hx0]; gas_ok)
  step reshape (s' := [0x60, 0, 0x18160ddd, upWord (storageAt state message.currentTarget 10), 0]
      ++ rest) (m' := MEM0) (g' := gas - 157)
    (by rw [hx0, memoryExtend_zero, show (0x40 : U256).toNat = 64 from rfl, mload_MEM0]; rfl)
    (by rw [hx0, memoryExtend_zero]) (by rw [hx0]; gas_ok)
  step pushR 1 (0x20 : U256)
  step binR 0x01 instruction_add
  step reshape (s' := [0x80, 0, 0x18160ddd, upWord (storageAt state message.currentTarget 10), 0]
      ++ rest) (m' := MEM0) (g' := gas - 163) rfl rfl (by gas_ok)
  have hx1 : extendMemory MEM0.size [((0x80 : U256), (32 : U256))] = ⟨6, 64⟩ := by
    rw [size_MEM0]; decide
  step mstore (by code_fact) (by code_fact) (by rw [hx1]; gas_ok)
  step reshape (s' := [0x18160ddd, upWord (storageAt state message.currentTarget 10), 0] ++ rest)
    (m' := M1) (g' := gas - 172) rfl (by rw [hx1]; rfl) (by rw [hx1]; gas_ok)
  step pushR 1 (0x40 : U256)
  have hx2 : extendMemory M1.size [((0x40 : U256), (32 : U256))] = ⟨0, 0⟩ := by
    rw [size_M1]; decide
  step mload (by code_fact) (by code_fact) (by rw [hx2]; gas_ok)
  step reshape (s' := [0x60, 0x18160ddd, upWord (storageAt state message.currentTarget 10), 0]
      ++ rest) (m' := M1) (g' := gas - 178)
    (by rw [hx2, show (0x40 : U256).toNat = 64 from rfl, mload_M1]; rfl)
    (by rw [hx2, memoryExtend_zero]) (by rw [hx2]; gas_ok)
  step dupR 1
  step pushR 4 (0xffffffff : U256)
  step binR 0x16 Local.instruction_and
  step pushR 29 (0x0100000000000000000000000000000000000000000000000000000000 : U256)
  step binR 0x02 Local.instruction_mul
  step dupR 1
  have hx3 : extendMemory M1.size [((0x60 : U256), (32 : U256))] = ⟨0, 0⟩ := by
    rw [size_M1]; decide
  step mstore (by code_fact) (by code_fact) (by rw [hx3]; gas_ok)
  step reshape (s' := [0x60, 0x18160ddd, upWord (storageAt state message.currentTarget 10), 0]
      ++ rest) (m' := M2) (g' := gas - 201) rfl (by rw [hx3, memoryExtend_zero]; rfl)
    (by rw [hx3]; gas_ok)
  step pushR 1 (0x04 : U256)
  step binR 0x01 instruction_add
  have h64 : add (0x04 : U256) (0x60 : U256) = 0x64 := by decide
  rw [h64]
  step pushR 1 (0x20 : U256)
  step pushR 1 (0x40 : U256)
  have hx4 : extendMemory M2.size [((0x40 : U256), (32 : U256))] = ⟨0, 0⟩ := by
    rw [size_M2]; decide
  step mload (by code_fact) (by code_fact) (by rw [hx4]; gas_ok)
  step reshape (s' := [0x60, 0x20, 0x64, 0x18160ddd,
      upWord (storageAt state message.currentTarget 10), 0] ++ rest) (m' := M2) (g' := gas - 216)
    (by rw [hx4, show (0x40 : U256).toNat = 64 from rfl, mload_M2]; rfl)
    (by rw [hx4, memoryExtend_zero]) (by rw [hx4]; gas_ok)
  step dupR 0
  step dupR 3
  step binR 0x03 Local.instruction_sub
  have h4 : sub (0x64 : U256) (0x60 : U256) = 0x04 := by decide
  rw [h4]
  step dupR 1
  step pushR 1 (0 : U256)
  step dupR 7
  step dupR 0
  exact restate (by decide) (by simp) rfl (by gas_ok)
    (readSlot_readSlot state message.currentTarget 10)
    (accessSlot_accessSlot substate message.currentTarget 10)

theorem isZero2_ne {x : U256} (h : x ≠ 0) : isZero (isZero x) ≠ 0 := by
  have h1 : isZero x = 0 := by unfold isZero; exact ite_eq_right h
  rw [h1]; decide

theorem isZero2_zero : isZero (isZero (0 : U256)) = 0 := by decide

theorem ofNat_size_ne {n : Nat} (h0 : 0 < n) (hlt : n < 2 ^ 256) : (BitVec.ofNat 256 n) ≠ 0 := by
  intro hz
  have := congrArg BitVec.toNat hz
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] at this
  simp at this; omega

/-- The price of EXTCODESIZE from Berlin: 2600 for a cold address, 100 for a warm one. -/
abbrev accCost (cold : Bool) : Nat := if cold then 2600 else 100

/-- The gas that the code asks to pass on: what GAS pushes, minus 710 (as a word). -/
abbrev asked (g : Nat) : U256 := sub (BitVec.ofNat 256 g) (0x02c6 : U256)

/-- From 3719 (totalSupply), 4874 (balanceOf), 5739 (transfer), 3213 (approve) or 4200
(transferFrom): EXTCODESIZE of the address; the code is not empty, so the JUMPI goes on, then GAS
and the subtraction of 710 give the gas that CALL asks for, at the CALL 17 bytes on. -/
theorem toCall (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam) {p q : Nat}
    (hp : (p = 3719 ∧ q = 3736) ∨ (p = 4874 ∧ q = 4891) ∨ (p = 5739 ∧ q = 5756) ∨
      (p = 3213 ∧ q = 3230) ∨ (p = 4200 ∧ q = 4217)) {U : U256}
    {rest : List U256} (hrest : rest.length ≤ 16) {M : ByteArray} {st : State.TransactionState}
    {ss : Substate} {cU : Bool} {c : ByteArray}
    (hcode : st.getCode (st.getAccount (toAddressMasked U)).codeHash = .ok c)
    (hsz : 0 < c.size) (hszl : c.size < 2 ^ 256)
    (hcold : decide (toAddressMasked U ∉ ss.accessedAddresses) = cU)
    {gas : Nat} (hg : accCost cU + 28 ≤ gas) :
    Hoare fork (At CODE message p (U :: rest) M gas st ss)
      (At CODE message q (asked (gas - (accCost cU + 25)) :: rest) M (gas - (accCost cU + 28))
        (st.recordAccountRead (toAddressMasked U))
        { ss with accessedAddresses := ss.accessedAddresses.insert (toAddressMasked U) }) := by
  simp only [accCost] at hg ⊢
  have he : ∀ g : Nat, (g - if cU = true then 2600 else 100) - OPCODE_ISZERO - OPCODE_ISZERO - 3 -
      10 - 1 - 3 - 2 = g - ((if cU = true then 2600 else 100) + 25) := by intro g; gas_ok
  rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals
    step Logic.extcodesize hfork hglam (by code_fact) (by code_fact) hcode hcold (by gas_ok)
    step unR 0x15 instruction_iszero
    step unR 0x15 instruction_iszero
    step pushAnyR 2
    step jumpiR (isZero2_ne (ofNat_size_ne hsz hszl))
    step jumpdestR
    step pushR 2 (0x02c6 : U256)
    step Logic.gas_rule (by code_fact) (by code_fact) (by gas_ok) (by stk_ok)
    step binR 0x03 Local.instruction_sub
    refine (repc (by decide)).seq (reshape ?_ rfl (by gas_ok))
    rw [he]

/-- The return block at 797 on a memory of 160 bytes (no growth): it writes the top word at the
free memory pointer 0x60 and returns those 32 bytes. -/
theorem retBig {p : Nat} (hp : p = 797 ∨ p = 1511) {M : ByteArray} (hM : M.size = 160)
    (hptr : loadWord (memoryReadBytes M 64 32) 0 32 = 0x60) {v x : U256} {gas : Nat}
    (hg : 50 ≤ gas) :
    Spec fork (At CODE message p [v, x] M gas state substate)
      (Halted false (wordBytes v) (gas - 50) state substate) := by
  have hext0 : extendMemory M.size [((0x40 : U256), (32 : U256))] = ⟨0, 0⟩ := by
    rw [hM]; decide
  have hext1 : extendMemory M.size [((0x60 : U256), (32 : U256))] = ⟨0, 0⟩ := by
    rw [hM]; decide
  have hfit : 96 + (wordBytes v).size ≤ M.size := by rw [size_wordBytes, hM]; decide
  have hM' : (memoryWrite M 96 (wordBytes v)).size = 160 := by rw [size_memoryWrite hfit, hM]
  have hext2 : extendMemory (memoryWrite M 96 (wordBytes v)).size
      [((0x40 : U256), (32 : U256))] = ⟨0, 0⟩ := by
    rw [hM']; decide
  have hread2 : memoryReadBytes (memoryWrite M 96 (wordBytes v)) 64 32 = memoryReadBytes M 64 32 :=
    memoryReadBytes_memoryWrite_of_disjoint hfit (.inl (by decide))
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
    step reshape (s' := [0x60, 0x60, v, x]) (m' := memoryWrite M 96 (wordBytes v)) (g' := gas - 19)
      rfl (by rw [hext1, memoryExtend_zero]; rfl) (by rw [hext1]; gas_ok)
    step pushR 1 (0x20 : U256)
    step binR 0x01 instruction_add
    step swapR 1
    norm
    step popR
    step popR
    step pushR 1 (0x40 : U256)
    step mload (by code_fact) (by code_fact) (by rw [hext2]; gas_ok)
    step reshape (s' := [0x60, 0x80, x]) (m' := memoryWrite M 96 (wordBytes v)) (g' := gas - 38)
      (by rw [hext2, memoryExtend_zero, show (0x40 : U256).toNat = 64 from rfl, hread2, hptr]
          rfl) (by rw [hext2, memoryExtend_zero])
      (by rw [hext2]; gas_ok)
    step dupR 0
    step swapR 1
    norm
    step binR 0x03 Local.instruction_sub
    step swapR 0
    norm
    have hext3 : extendMemory (memoryWrite M 96 (wordBytes v)).size
        [((0x60 : U256), (0x20 : U256))] = ⟨0, 0⟩ := by
      rw [hM']; decide
    refine Spec.reshape (s' := [0x60, 0x20, x]) (by rfl) rfl rfl ?_
    refine (Logic.«return» (by code_fact) (by code_fact) (by rw [hext3]; gas_ok)).consequence
      (fun _ h => h) ?_
    rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
    refine ⟨hr, he, ?_, ?_, hs, hss⟩
    · rw [ho, hext3, memoryExtend_zero]
      have h := memoryReadBytes_memoryWrite (memory := M) (start := 96) (value := wordBytes v) hfit
      rw [size_wordBytes] at h
      exact h
    · rw [hgas, hext3]
      gas_ok

/-- The word that the code reads back at 0x60 after the call, from a memory `M`. -/
abbrev resWord (M : ByteArray) : U256 := loadWord (memoryReadBytes M 96 32) 0 32

/-- After a call that succeeded (flag 1), from 3737: the code reads the word at 0x60 and returns
it through 797. -/
theorem okTail {M : ByteArray} (hM : M.size = 160)
    (hptr : loadWord (memoryReadBytes M 64 32) 0 32 = 0x60) {x : U256} {gas : Nat}
    (hg : 121 ≤ gas) :
    Spec fork (At CODE message 3737 [1, 0x64, 0x18160ddd, U, 0, 0x031d, x] M gas state substate)
      (Halted false (wordBytes (resWord M)) (gas - 121) state substate) := by
  have hext0 : extendMemory M.size [((0x40 : U256), (32 : U256))] = ⟨0, 0⟩ := by
    rw [hM]; decide
  have hext1 : extendMemory M.size [((0x60 : U256), (32 : U256))] = ⟨0, 0⟩ := by
    rw [hM]; decide
  step unR 0x15 instruction_iszero
  step unR 0x15 instruction_iszero
  step pushR 2 (0x0ea3 : U256)
  step jumpiR (by decide)
  step jumpdestR
  step popR
  step popR
  step popR
  step pushR 1 (0x40 : U256)
  step mload (by code_fact) (by code_fact) (by rw [hext0]; gas_ok)
  step reshape (s' := [0x60, 0, 0x031d, x]) (m' := M) (g' := gas - 32)
    (by rw [hext0, memoryExtend_zero]; exact congrArg (· :: [0, 0x031d, x]) hptr)
    (by rw [hext0, memoryExtend_zero]) (by rw [hext0]; gas_ok)
  step dupR 0
  step mload (by code_fact) (by code_fact) (by rw [hext1]; gas_ok)
  step reshape (s' := [resWord M, 0x60, 0, 0x031d, x]) (m' := M) (g' := gas - 38)
    (by rw [hext1, memoryExtend_zero]; rfl) (by rw [hext1, memoryExtend_zero])
    (by rw [hext1]; gas_ok)
  step swapR 0
  norm
  step popR
  step swapR 0
  norm
  step popR
  step pushR 2 (0x0eba : U256)
  step jumpR
  at_pc 3770
  step jumpdestR
  step swapR 0
  norm
  step jumpR
  refine (repc (pc' := 797) (by decide)).seq ?_
  refine (retBig (Or.inl rfl) hM hptr (gas := gas - 71) (by gas_ok)).consequence (fun _ h => h) ?_
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  exact ⟨hr, he, ho, by rw [hgas]; gas_ok, hs, hss⟩

/-- After a call that failed (flag 0), from 3737 (totalSupply), 4892 (balanceOf), 5757
(transfer), 3231 (approve) or 4218 (transferFrom): the code reverts with no output. -/
theorem failTail (hfork : .berlin ≤ fork) {p : Nat}
    (hp : p = 3737 ∨ p = 4892 ∨ p = 5757 ∨ p = 3231 ∨ p = 4218) {M : ByteArray}
    {rest : List U256} (hrest : rest.length ≤ 16) {gas : Nat} (hg : 25 ≤ gas) :
    Spec fork (At CODE message p (0 :: rest) M gas state substate)
      (Halted true .empty (gas - 25) state substate) := by
  have hz : extendMemory M.size [((0 : U256), (0 : U256))] = ⟨0, 0⟩ := by
    simp [extendMemory]
  rcases hp with rfl | rfl | rfl | rfl | rfl
  all_goals
    step unR 0x15 instruction_iszero
    step unR 0x15 instruction_iszero
    step pushAnyR 2
    step jumpi0R isZero2_zero
    step pushR 1 (0 : U256)
    step dupR 0
    refine (Logic.revert (Nat.le_trans (by decide) hfork) (by code_fact)
      (by code_fact) (by rw [hz]; gas_ok)).consequence (fun _ h => h) ?_
    rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
    refine ⟨hr, he, ?_, ?_, hs, hss⟩
    · rw [ho]; simp [memoryReadBytes]
    · rw [hgas, hz]; gas_ok

/-- The upgraded address: the low 160 bits of slot 10, as an address. -/
abbrev upAddr (state : State.TransactionState) (message : Message fork) : EthLib.Base.Address :=
  toAddressMasked (upWord (storageAt state message.currentTarget 10))

/-- The gas of the path from pc 0 to the CALL. -/
abbrev preCost (c10 cU : Bool) : Nat := 602 + slotCost c10 + accCost cU

/-- The gas that the code asks CALL to pass on, for a frame that starts with `gas`. -/
abbrev askedOf (gas : Nat) (c10 cU : Bool) : U256 :=
  asked (gas - (599 + slotCost c10 + accCost cU))

/-- What CALL pays and passes on (EIP-150, EIP-2929; the address is warm after EXTCODESIZE). -/
abbrev callGas (fork : Fork) (gas : Nat) (c10 cU : Bool) : MessageCallGas :=
  messageCallGas fork 0 (askedOf gas c10 cU).toNat (gas - preCost c10 cU) 0 100

/-- The state when the code calls: slot 10 and the upgraded account recorded read. -/
abbrev callState (state : State.TransactionState) (message : Message fork) :
    State.TransactionState :=
  (readSlot state message.currentTarget 10).recordAccountRead (upAddr state message)

/-- The substate when the code calls: slot 10 and the upgraded address accessed. -/
abbrev callSub (substate : Substate) (state : State.TransactionState) (message : Message fork) :
    Substate :=
  { accessSlot substate message.currentTarget 10 with
    accessedAddresses := substate.accessedAddresses.insert (upAddr state message) }

/-- From pc 0 to the CALL at 3736, when deprecated and the upgraded account has code. -/
theorem preCall (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    (hsize : 4 ≤ message.data.size) (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x18160ddd) (hv : message.value = 0)
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0) {c : ByteArray}
    (hcode : state.getCode (state.getAccount (upAddr state message)).codeHash = .ok c)
    (hsz : 0 < c.size) (hszl : c.size < 2 ^ 256) {c10 cU : Bool}
    (hc10 : coldIn substate message.currentTarget 10 = c10)
    (hcU : decide (upAddr state message ∉ substate.accessedAddresses) = cU)
    {gas : Nat} (hg : preCost c10 cU ≤ gas) :
    Hoare fork (At CODE message 0 [] .empty gas state substate)
      (At CODE message 3736
        [askedOf gas c10 cU, upWord (storageAt state message.currentTarget 10), 0, 0x60, 4, 0x60,
          0x20, 0x64, 0x18160ddd, upWord (storageAt state message.currentTarget 10), 0, 0x031d,
          BitVec.ofNat 256 (selector message.data)]
        M2 (gas - preCost c10 cU) (callState state message) (callSub substate state message)) := by
  simp only [preCost, askedOf, accCost] at hg ⊢
  have ht : tested (BitVec.ofNat 256 (selector message.data)) ENTRIES = 6 := by
    rw [hsel]; decide
  have hb : branch (BitVec.ofNat 256 (selector message.data)) 54 (entrySize 4 2) ENTRIES = 778 := by
    rw [hsel]; decide
  have h1 := dispatch (state := state) (substate := substate) hsize hsize' (gas := gas)
    (by rw [ht]; gas_ok)
  rw [ht, hb] at h1
  refine h1.seq ?_
  step TotalSupply.entry hv (by gas_ok)
  step depSet hfork (Or.inl ⟨rfl, rfl⟩) (by simp) hdep hc10 (by gas_ok)
  step fwdArgs (state := state) hfork (by simp) (by gas_ok)
  step reshape (g' := gas - (574 + slotCost c10)) rfl rfl (by gas_ok)
  refine (toCall (gas := gas - (574 + slotCost c10)) (st := readSlot state message.currentTarget 10)
    (ss := accessSlot substate message.currentTarget 10) (message := message) (M := M2)
    (rest := [upWord (storageAt state message.currentTarget 10), 0, 0x60, 4, 0x60, 0x20, 0x64,
      0x18160ddd, upWord (storageAt state message.currentTarget 10), 0, 0x031d,
      BitVec.ofNat 256 (selector message.data)]) hfork hglam (Or.inl ⟨rfl, rfl⟩) (by simp) hcode
    hsz hszl hcU (by simp only [accCost]; gas_ok)).seq ?_
  refine reshape ?_ rfl (by simp only [accCost]; gas_ok)
  simp only [List.cons.injEq, and_true]
  congr 1
  unfold accCost; omega

/-- The memory after the call: CALL writes the first `min 32 o.size` bytes of the output `o` of the
callee at 0x60. -/
abbrev outMem (o : ByteArray) : ByteArray := memoryWrite (memoryExtend M2 0) 96 (o.extract 0 (min 32 o.size))

theorem size_outMem (o : ByteArray) : (outMem o).size = 160 := by
  rw [outMem, memoryExtend_zero, size_memoryWrite (by rw [ByteArray.size_extract, size_M2]; omega),
    size_M2]

theorem mload_outMem (o : ByteArray) :
    loadWord (memoryReadBytes (outMem o) 64 32) 0 32 = 0x60 := by
  have h := mload_M2
  rw [memoryExtend_zero] at h
  rw [outMem, memoryExtend_zero, memoryReadBytes_memoryWrite_of_disjoint
    (by rw [ByteArray.size_extract, size_M2]; omega) (.inl (by decide))]
  exact h

/-- The message that the code sends: from the contract to the upgraded address `ua`, with the
code `c` of that address, the 4 bytes of the selector of `totalSupply()` as data and no value. -/
def Forwarded (message : Message fork) (ua : EthLib.Base.Address) (c : ByteArray)
    (msg : Message fork) : Prop :=
  msg.caller = message.currentTarget ∧ msg.currentTarget = ua ∧ msg.target = some ua ∧
    msg.codeAddress = some ua ∧ msg.code = c ∧ msg.data = SEL_TS ∧ msg.value = 0 ∧
    msg.depth = message.depth + 1 ∧ msg.isStatic = message.isStatic

/-- The specification of `totalSupply()` when deprecated, for every callee.

Hypotheses: Berlin ≤ fork < Glamsterdam; call data of 4 to 2^256 - 1 bytes with selector
0x18160ddd; no value; byte 20 of slot 10 (`deprecated`) is not 0; the upgraded address `ua` (the
low 160 bits of slot 10) holds a code `c` of 1 to 2^256 - 1 bytes, which is no delegation from
Pectra; the depth leaves room for one more frame; `c10` and `cU` are whether slot 10 and `ua` are
cold; there is the gas of the path to the CALL and of the CALL (`hg`), and after the price of the
CALL at least 121 gas is left (`htail`).

Then under every runner whose ended messages meet `callee`, the run ends (or the runner aborts)
in a stopped frame for which there are a caller frame, a message `msg` and an ended frame `child`
with `callee caller msg child`, such that `msg` is the forward of the call to `ua` (`Forwarded`:
data = the 4 selector bytes, no value) with the gas of EIP-150 (`callGas`), and:
- if `child` ended with no error, the frame returns the 32 bytes of the word at 0x60 after CALL
  wrote the first `min 32 (size of the output)` bytes of `child`'s output there (`resWord`);
- otherwise it reverts with no output.
Gas left, state and substate are given exactly. -/
theorem spec_dep (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    (hsize : 4 ≤ message.data.size) (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x18160ddd) (hv : message.value = 0)
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0) {c : ByteArray}
    (hcode : state.getCode (state.getAccount (upAddr state message)).codeHash = .ok c)
    (hsz : 0 < c.size) (hszl : c.size < 2 ^ 256)
    (hdel : .pectra ≤ fork → delegatedAddress c = none)
    (hdepth : message.depth + 1 ≤ STACK_DEPTH_LIMIT) {c10 cU : Bool}
    (hc10 : coldIn substate message.currentTarget 10 = c10)
    (hcU : decide (upAddr state message ∉ substate.accessedAddresses) = cU)
    {gas : Nat} (hg : preCost c10 cU + 100 ≤ gas)
    (htail : 121 ≤ gas - preCost c10 cU - (callGas fork gas c10 cU).cost)
    {callee : Evm fork Nat → Message fork → Evm fork Nat → Prop} :
    SpecUnder fork callee (At CODE message 0 [] .empty gas state substate)
      fun evm => ∃ caller msg child, callee caller msg child ∧
        Forwarded message (upAddr state message) c msg ∧
        msg.gas = (callGas fork gas c10 cU).subCall ∧
        caller.state = ((callState state message).recordAccountRead (upAddr state message)).recordAccountRead
          message.currentTarget ∧
        caller.substate = { callSub substate state message with
          accessedAddresses :=
            (callSub substate state message).accessedAddresses.insert (upAddr state message) } ∧
        (child.error = none →
          Halted false (wordBytes (resWord (outMem child.output)))
            (gas - preCost c10 cU - (callGas fork gas c10 cU).cost + child.gas - 121)
            (incorporateChild fork caller child).state
            (incorporateChild fork caller child).substate evm) ∧
        (child.error ≠ none →
          Halted true .empty
            (gas - preCost c10 cU - (callGas fork gas c10 cU).cost + child.gas - 25)
            (incorporateChild fork caller child).state
            (incorporateChild fork caller child).substate evm) := by
  have hext : extendMemory M2.size [((0x60 : U256), (4 : U256)), ((0x60 : U256), (0x20 : U256))] =
      ⟨0, 0⟩ := by
    rw [size_M2]; decide
  have hcall := callWith (fork := fork) (code := CODE) (message := message) (pc := 3736)
    (memory := M2) (gas := gas - preCost c10 cU) (state := callState state message)
    (substate := callSub substate state message) (callee := callee)
    (asked := askedOf gas c10 cU) (to := upWord (storageAt state message.currentTarget 10))
    (inputStart := 0x60) (inputSize := 4) (outputStart := 0x60) (outputSize := 0x20)
    (rest := [0x64, 0x18160ddd, upWord (storageAt state message.currentTarget 10), 0, 0x031d,
      BitVec.ofNat 256 (selector message.data)]) (cold := false) hfork hglam
    (by code_fact) (by code_fact) hcode hdel hdepth (by simp [upAddr])
    (by rw [hext]; simp only [Bool.false_eq_true, ↓reduceIte]; omega)
  rw [hext] at hcall
  simp only [Bool.false_eq_true, ↓reduceIte] at hcall
  refine SpecUnder.seq (HoareUnder.of_hoare (preCall hfork hglam hsize hsize' hsel hv hdep hcode hsz
    hszl hc10 hcU (by omega))) (HoareUnder.seq hcall (HoareUnder.of_hoare ?_))
  rintro evm ⟨caller, msg, child, hcal, -, hcs, hcss, hmg, hmc, hmt, hmtg, hmca, hmcode, hmd, hmv,
    hmdep, hmst, hat⟩
  have hfwd : Forwarded message (upAddr state message) c msg := by
    refine ⟨hmc, hmt, hmtg, hmca, hmcode, ?_, hmv, hmdep, hmst⟩
    rw [hmd]; exact data_M2
  by_cases he : child.error = none
  · simp only [he, Option.isNone_none, ↓reduceIte] at hat
    obtain ⟨after, hreach, hrun, hq⟩ := okTail (fork := fork) (message := message)
      (state := (incorporateChild fork caller child).state)
      (substate := (incorporateChild fork caller child).substate) (U := upWord (storageAt state
        message.currentTarget 10)) (size_outMem child.output) (mload_outMem child.output)
      (x := BitVec.ofNat 256 (selector message.data))
      (gas := gas - preCost c10 cU - ((callGas fork gas c10 cU).cost + 0) + child.gas)
      (by omega) evm hat
    refine ⟨after, hreach, hrun, caller, msg, child, hcal, hfwd, hmg, hcs, hcss, fun _ => ?_,
      fun h => absurd he h⟩
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hq
    exact ⟨h1, h2, h3, by rw [h4]; omega, h5, h6⟩
  · have hz : child.error.isNone = false := by
      cases h : child.error
      · exact absurd h he
      · rfl
    simp only [hz, Bool.false_eq_true, ↓reduceIte] at hat
    obtain ⟨after, hreach, hrun, hq⟩ := failTail (fork := fork) (message := message)
      (state := (incorporateChild fork caller child).state)
      (substate := (incorporateChild fork caller child).substate) hfork (Or.inl rfl)
      (rest := [0x64, 0x18160ddd, upWord (storageAt state
        message.currentTarget 10), 0, 0x031d, BitVec.ofNat 256 (selector message.data)])
      (by simp)
      (gas := gas - preCost c10 cU - ((callGas fork gas c10 cU).cost + 0) + child.gas)
      (by omega) evm hat
    refine ⟨after, hreach, hrun, caller, msg, child, hcal, hfwd, hmg, hcs, hcss,
      fun h => absurd h he, fun _ => ?_⟩
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hq
    exact ⟨h1, h2, h3, by rw [h4]; omega, h5, h6⟩

/-- With an output of at least 32 bytes, the word read back is the first word of the output. -/
theorem resWord_outMem {o : ByteArray} (ho : 32 ≤ o.size) : resWord (outMem o) = loadWord o 0 32 := by
  have hm : min 32 o.size = 32 := Nat.min_eq_left ho
  have hs : (o.extract 0 32).size = 32 := by rw [ByteArray.size_extract]; omega
  have hfit : 96 + (o.extract 0 32).size ≤ (memoryExtend M2 0).size := by
    rw [hs, memoryExtend_zero, size_M2]; decide
  have h := memoryReadBytes_memoryWrite hfit
  rw [hs] at h
  rw [resWord, outMem, hm, h]
  unfold loadWord bufferRead
  congr 2
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  rw [EthLib.Base.byteAt_extract, ite_eq_left (by omega), Nat.zero_add]

/-- A callee assumption that pins the answer to the forwarded call: every message forwarded to
`ua` with the code `c` ends with no error and the output `o`. -/
def Answers (message : Message fork) (ua : EthLib.Base.Address) (c o : ByteArray)
    (callee : Evm fork Nat → Message fork → Evm fork Nat → Prop) : Prop :=
  ∀ caller msg child, callee caller msg child → Forwarded message ua c msg →
    child.error = none ∧ child.output = o

/-- A callee assumption under which the forwarded call fails: every message forwarded to `ua`
with the code `c` ends with an error. -/
def Fails (message : Message fork) (ua : EthLib.Base.Address) (c : ByteArray)
    (callee : Evm fork Nat → Message fork → Evm fork Nat → Prop) : Prop :=
  ∀ caller msg child, callee caller msg child → Forwarded message ua c msg → child.error ≠ none

/-- `totalSupply()` when deprecated, for a callee that answers `o` (at least 32 bytes): the run
returns the first 32 bytes of `o` as a word (`wordBytes (loadWord o 0 32)`), with no error. -/
theorem spec_dep_answers (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    (hsize : 4 ≤ message.data.size) (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x18160ddd) (hv : message.value = 0)
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0) {c : ByteArray}
    (hcode : state.getCode (state.getAccount (upAddr state message)).codeHash = .ok c)
    (hsz : 0 < c.size) (hszl : c.size < 2 ^ 256)
    (hdel : .pectra ≤ fork → delegatedAddress c = none)
    (hdepth : message.depth + 1 ≤ STACK_DEPTH_LIMIT) {c10 cU : Bool}
    (hc10 : coldIn substate message.currentTarget 10 = c10)
    (hcU : decide (upAddr state message ∉ substate.accessedAddresses) = cU)
    {gas : Nat} (hg : preCost c10 cU + 100 ≤ gas)
    (htail : 121 ≤ gas - preCost c10 cU - (callGas fork gas c10 cU).cost)
    {callee : Evm fork Nat → Message fork → Evm fork Nat → Prop} {o : ByteArray}
    (hans : Answers message (upAddr state message) c o callee) (ho : 32 ≤ o.size) :
    SpecUnder fork callee (At CODE message 0 [] .empty gas state substate)
      fun evm => evm.error = none ∧ evm.output = wordBytes (loadWord o 0 32) := by
  refine (spec_dep hfork hglam hsize hsize' hsel hv hdep hcode hsz hszl hdel hdepth hc10 hcU hg
    htail).consequence (fun _ h => h) ?_
  rintro evm ⟨caller, msg, child, hcal, hfwd, -, -, -, hok, -⟩
  obtain ⟨he, hout⟩ := hans caller msg child hcal hfwd
  obtain ⟨-, herr, hevm, -⟩ := hok he
  refine ⟨by simpa using herr, ?_⟩
  rw [hevm, hout, resWord_outMem ho]

/-- `totalSupply()` when deprecated, for a callee whose answer fails: the run reverts with no
output. -/
theorem spec_dep_fails (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    (hsize : 4 ≤ message.data.size) (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x18160ddd) (hv : message.value = 0)
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0) {c : ByteArray}
    (hcode : state.getCode (state.getAccount (upAddr state message)).codeHash = .ok c)
    (hsz : 0 < c.size) (hszl : c.size < 2 ^ 256)
    (hdel : .pectra ≤ fork → delegatedAddress c = none)
    (hdepth : message.depth + 1 ≤ STACK_DEPTH_LIMIT) {c10 cU : Bool}
    (hc10 : coldIn substate message.currentTarget 10 = c10)
    (hcU : decide (upAddr state message ∉ substate.accessedAddresses) = cU)
    {gas : Nat} (hg : preCost c10 cU + 100 ≤ gas)
    (htail : 121 ≤ gas - preCost c10 cU - (callGas fork gas c10 cU).cost)
    {callee : Evm fork Nat → Message fork → Evm fork Nat → Prop}
    (hfail : Fails message (upAddr state message) c callee) :
    SpecUnder fork callee (At CODE message 0 [] .empty gas state substate)
      fun evm => evm.error = some .revert ∧ evm.output = .empty := by
  refine (spec_dep hfork hglam hsize hsize' hsel hv hdep hcode hsz hszl hdel hdepth hc10 hcU hg
    htail).consequence (fun _ h => h) ?_
  rintro evm ⟨caller, msg, child, hcal, hfwd, -, -, -, -, hko⟩
  obtain ⟨-, herr, hevm, -⟩ := hko (hfail caller msg child hcal hfwd)
  exact ⟨by simpa using herr, hevm⟩

/-- The interpreter loop under a runner that meets an answering callee assumption: the run of a
deprecated `totalSupply()` call returns the first word of `o`, or the runner aborts. -/
theorem runFrame_dep_answers (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    (hsize : 4 ≤ message.data.size) (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x18160ddd) (hv : message.value = 0)
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0) {c : ByteArray}
    (hcode : state.getCode (state.getAccount (upAddr state message)).codeHash = .ok c)
    (hsz : 0 < c.size) (hszl : c.size < 2 ^ 256)
    (hdel : .pectra ≤ fork → delegatedAddress c = none)
    (hdepth : message.depth + 1 ≤ STACK_DEPTH_LIMIT) {c10 cU : Bool}
    (hc10 : coldIn substate message.currentTarget 10 = c10)
    (hcU : decide (upAddr state message ∉ substate.accessedAddresses) = cU)
    {gas : Nat} (hg : preCost c10 cU + 100 ≤ gas)
    (htail : 121 ≤ gas - preCost c10 cU - (callGas fork gas c10 cU).cost)
    {callee : Evm fork Nat → Message fork → Evm fork Nat → Prop} {o : ByteArray}
    (hans : Answers message (upAddr state message) c o callee) (ho : 32 ≤ o.size)
    {bound : Nat} {runChild : MessageRunner fork Nat bound} (meets : Meets callee runChild)
    {evm : Evm fork Nat} (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    (∃ stopped, runFrame (step fork) (step_decreases fork) bound runChild evm within =
      .ok stopped ∧ stopped.error = none ∧ stopped.output = wordBytes (loadWord o 0 32)) ∨
    ∃ e, runFrame (step fork) (step_decreases fork) bound runChild evm within = .error e ∧
      e.aborts = true :=
  (spec_dep_answers hfork hglam hsize hsize' hsel hv hdep hcode hsz hszl hdel hdepth hc10 hcU hg
    htail hans ho).runFrame meets start within

/-- EthLib's callee assumption `RunsAs c G Q` answers `o` when every stopped frame of `Q` has no
error and the output `o`, the forwarded messages meet `G`, and `ua` is no precompile. -/
theorem answers_runsAs {ua : EthLib.Base.Address} {c o : ByteArray}
    {G : Message fork → State.TransactionState → Substate → Prop}
    {Q : Message fork → State.TransactionState → Substate → Evm fork Nat → Prop}
    (hQ : ∀ msg st ss stopped, Q msg st ss stopped → stopped.error = none ∧ stopped.output = o)
    (hG : ∀ msg st ss, Forwarded message ua c msg → G msg st ss)
    (hpre : Precompiles.isPrecompile fork ua.toU256.toNat = false) :
    Answers message ua c o (RunsAs c G Q) := by
  intro caller msg child hrun hfwd'
  have ⟨_, _, hmt, hmca, hmc, _, hmv, _, _⟩ := hfwd'
  obtain ⟨stopped, hq, hchild⟩ := hrun hmc (by simp [hmt]) (by simp [hmv])
    (by simp [precompileAddress, hmca, hpre]) (hG _ _ _ hfwd')
  obtain ⟨he, ho⟩ := hQ _ _ _ _ hq
  rw [hchild, rollbackOnError_of_error_eq_none he]
  exact ⟨he, ho⟩

/-- `totalSupply()` when deprecated, run by the interpreter's own message runner (`processRunner`,
which runs the callee's code): for every upgraded code `c` with a specification (as EthLib's
`meets_of_spec` takes it) whose stopped frames end with no error and the output `o` of at least 32
bytes, the run returns the first word of `o`, or the runner aborts. -/
theorem runFrame_dep_process (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    (hsize : 4 ≤ message.data.size) (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x18160ddd) (hv : message.value = 0)
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0) {c : ByteArray}
    (hcode : state.getCode (state.getAccount (upAddr state message)).codeHash = .ok c)
    (hsz : 0 < c.size) (hszl : c.size < 2 ^ 256)
    (hdel : .pectra ≤ fork → delegatedAddress c = none)
    (hpre : Precompiles.isPrecompile fork (upAddr state message).toU256.toNat = false)
    (hdepth : message.depth + 1 ≤ STACK_DEPTH_LIMIT) {c10 cU : Bool}
    (hc10 : coldIn substate message.currentTarget 10 = c10)
    (hcU : decide (upAddr state message ∉ substate.accessedAddresses) = cU)
    {gas : Nat} (hg : preCost c10 cU + 100 ≤ gas)
    (htail : 121 ≤ gas - preCost c10 cU - (callGas fork gas c10 cU).cost)
    {G : Message fork → State.TransactionState → Substate → Prop}
    {Q : Message fork → State.TransactionState → Substate → Evm fork Nat → Prop}
    (hspec : ∀ msg st ss, msg.code = c → G msg st ss →
      Spec fork (At c msg 0 [] .empty msg.gas (startState fork msg st) ss) (Q msg st ss))
    (hG : ∀ msg st ss, Forwarded message (upAddr state message) c msg → G msg st ss)
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
  runFrame_dep_answers hfork hglam hsize hsize' hsel hv hdep hcode hsz hszl hdel hdepth hc10 hcU
    hg htail (answers_runsAs hQ hG hpre) ho (meets_of_spec hspec bound) start within

/-- From 3719 (totalSupply), 4874 (balanceOf), 5739 (transfer), 3213 (approve) or 4200
(transferFrom), when the upgraded address has no code: EXTCODESIZE pushes 0 and the code reverts
with no output (Solidity's `extcodesize` check). -/
theorem noCode (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam) {p : Nat}
    (hp : p = 3719 ∨ p = 4874 ∨ p = 5739 ∨ p = 3213 ∨ p = 4200) {U : U256} {rest : List U256}
    (hrest : rest.length ≤ 16) {M : ByteArray} {st : State.TransactionState} {ss : Substate} {cU : Bool}
    (hcode : st.getCode (st.getAccount (toAddressMasked U)).codeHash = .ok .empty)
    (hcold : decide (toAddressMasked U ∉ ss.accessedAddresses) = cU)
    {gas : Nat} (hg : accCost cU + 25 ≤ gas) :
    Spec fork (At CODE message p (U :: rest) M gas st ss)
      (Halted true .empty (gas - (accCost cU + 25)) (st.recordAccountRead (toAddressMasked U))
        { ss with accessedAddresses := ss.accessedAddresses.insert (toAddressMasked U) }) := by
  simp only [accCost] at hg ⊢
  have hz : extendMemory M.size [((0 : U256), (0 : U256))] = ⟨0, 0⟩ := by
    simp [extendMemory]
  rcases hp with rfl | rfl | rfl | rfl | rfl
  all_goals
    step Logic.extcodesize hfork hglam (by code_fact) (by code_fact) hcode hcold (by gas_ok)
    step unR 0x15 instruction_iszero
    step unR 0x15 instruction_iszero
    step pushAnyR 2
    step jumpi0R (by decide)
    step pushR 1 (0 : U256)
    step dupR 0
    refine (Logic.revert (Nat.le_trans (by decide) hfork) (by code_fact)
      (by code_fact) (by rw [hz]; gas_ok)).consequence (fun _ h => h) ?_
    rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
    refine ⟨hr, he, ?_, ?_, hs, hss⟩
    · rw [ho]; simp [memoryReadBytes]
    · rw [hgas, hz]; gas_ok

/-- The specification of `totalSupply()` when deprecated and the upgraded address has no code
(empty code in the state): the run reverts with no output before any call, after reading slot 10
and the upgraded account. Gas `599 + price(slot 10) + price(upgraded address)`. -/
theorem spec_depNoCode (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    (hsize : 4 ≤ message.data.size) (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x18160ddd) (hv : message.value = 0)
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0)
    (hcode : state.getCode (state.getAccount (upAddr state message)).codeHash = .ok .empty)
    {c10 cU : Bool} (hc10 : coldIn substate message.currentTarget 10 = c10)
    (hcU : decide (upAddr state message ∉ substate.accessedAddresses) = cU)
    {gas : Nat} (hg : 599 + slotCost c10 + accCost cU ≤ gas) :
    Spec fork (At CODE message 0 [] .empty gas state substate)
      (Halted true .empty (gas - (599 + slotCost c10 + accCost cU)) (callState state message)
        (callSub substate state message)) := by
  simp only [accCost] at hg ⊢
  have ht : tested (BitVec.ofNat 256 (selector message.data)) ENTRIES = 6 := by
    rw [hsel]; decide
  have hb : branch (BitVec.ofNat 256 (selector message.data)) 54 (entrySize 4 2) ENTRIES = 778 := by
    rw [hsel]; decide
  have h1 := dispatch (state := state) (substate := substate) hsize hsize' (gas := gas)
    (by rw [ht]; gas_ok)
  rw [ht, hb] at h1
  refine h1.seq ?_
  step TotalSupply.entry hv (by gas_ok)
  step depSet hfork (Or.inl ⟨rfl, rfl⟩) (by simp) hdep hc10 (by gas_ok)
  step fwdArgs (state := state) hfork (by simp) (by gas_ok)
  step reshape (g' := gas - (574 + slotCost c10)) rfl rfl (by gas_ok)
  refine (noCode (gas := gas - (574 + slotCost c10)) (st := readSlot state message.currentTarget 10)
    (ss := accessSlot substate message.currentTarget 10) (message := message) (M := M2)
    (rest := [upWord (storageAt state message.currentTarget 10), 0, 0x60, 4, 0x60, 0x20, 0x64,
      0x18160ddd, upWord (storageAt state message.currentTarget 10), 0, 0x031d,
      BitVec.ofNat 256 (selector message.data)]) hfork hglam (Or.inl rfl) (by simp) hcode
    hcU (by simp only [accCost]; gas_ok)).consequence (fun _ h => h) ?_
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  exact ⟨hr, he, ho, by rw [hgas]; simp only [accCost]; gas_ok, hs, hss⟩

end UsdtVerify.Deprecated
