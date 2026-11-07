import UsdtVerify.Functions.SetParamsSpec

/-!
# deprecate(address) and transferOwnership(address): the blocks

TetherToken / Ownable:
```
function deprecate(address _upgradedAddress) public onlyOwner {
    deprecated = true;
    upgradedAddress = _upgradedAddress;
    Deprecate(_upgradedAddress);
}
function transferOwnership(address newOwner) public onlyOwner {
    if (newOwner != address(0)) {
        owner = newOwner;
    }
}
```
`deprecated` is byte 20 of slot 10 and `upgradedAddress` its low 160 bits; `owner` is the low
160 bits of slot 0 (with `paused` in byte 20).

- deprecate: entry 553, body 2646, check at 2650, flag write at 2737, address write at 2765
  (tail at 2770), log at 2830, back to 608 (STOP).
- transferOwnership: entry 2374, body 7605, check at 7609, test at 7696, address write at 7751
  (tail at 7755), 7815, back to 2429 (STOP).
-/

namespace UsdtVerify.AddrWrite

open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts
open Transfer TransferOk Owner Admin Issue Pause

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate}

/-- A word with its low 160 bits replaced by those of `a`: `(a & mask) | (~mask & w)`. -/
def withAddr (w a : U256) : U256 := bitwiseOr (bitwiseAnd ADDR_MASK a) (bitwiseAnd (bitwiseNot ADDR_MASK) w)

theorem mask_bit (j : Nat) : (ADDR_MASK).getLsbD j = decide (j < 160) := by
  rw [BitVec.getLsbD_ofNat, Nat.testBit_two_pow_sub_one]
  by_cases h : j < 160 <;> simp [h] <;> omega

/-- The bits of `withAddr w a`: those of `a` below 160, those of `w` from 160 on. -/
theorem bit_withAddr (w a : U256) (i : Nat) :
    (withAddr w a).getLsbD i = if i < 160 then a.getLsbD i else w.getLsbD i := by
  by_cases h' : 256 ≤ i
  · rw [BitVec.getLsbD_of_ge _ i h', BitVec.getLsbD_of_ge w i h']
    simp [show ¬ i < 160 by omega]
  have h : i < 256 := by omega
  simp only [withAddr, bitwiseOr, bitwiseAnd, bitwiseNot, BitVec.getLsbD_or, BitVec.getLsbD_and,
    BitVec.getLsbD_not, mask_bit, h, decide_true, Bool.true_and]
  by_cases hi : i < 160 <;> simp [hi]

/-- `withAddr` sets the address part (the low 160 bits) to that of `a`. -/
theorem addr_withAddr (w a : U256) : bitwiseAnd ADDR_MASK (withAddr w a) = bitwiseAnd ADDR_MASK a := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [bitwiseAnd, BitVec.getLsbD_and, mask_bit, bit_withAddr]
  by_cases h : i < 160 <;> simp [h]

/-- `withAddr` keeps byte 20 (bits 160 to 167). -/
theorem byte20_withAddr (w a : U256) : byte20 (withAddr w a) = byte20 w := by
  apply byte20_of_bits _ (Nat.mod_lt _ (by decide))
  intro j hj
  rw [bit_withAddr]
  simp only [show ¬ (160 + j < 160) from by omega, ite_false]
  show w.toNat.testBit (160 + j) = (w.toNat / 2 ^ 160 % 2 ^ 8).testBit j
  rw [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.add_comm]
  simp [hj]

theorem mul_mask_one : mul ADDR_MASK 1 = ADDR_MASK := by decide
theorem mul_one' (x : U256) : mul x 1 = x := by simp [mul]

/-- The shared tail of the two address writes, at 2770 (slot 10) and 7755 (slot 0): with
`0 :: k :: a :: a` on the stack, slot `k` (warm) gets its low 160 bits from `a`. -/
theorem addrTail (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam) {p : Nat}
    (hp : p = 2770 ∨ p = 7755) {k a : U256} {rest : List U256} (hrest : rest.length ≤ 16)
    (hstatic : message.isStatic = false) (hacc : hasAccount state message.currentTarget)
    (hk : coldIn substate message.currentTarget k = false) {M : ByteArray} {gas : Nat}
    (hstip : 2457 ≤ gas)
    (hg : 158 + sstoreCost fork (originalAt state message.currentTarget k)
      (storageAt state message.currentTarget k)
      (withAddr (storageAt state message.currentTarget k) a) false ≤ gas) :
    Hoare fork (At CODE message p (0 :: k :: a :: a :: rest) M gas state substate)
      (At CODE message (p + 60) (a :: rest) M
        (gas - (158 + sstoreCost fork (originalAt state message.currentTarget k)
          (storageAt state message.currentTarget k)
          (withAddr (storageAt state message.currentTarget k) a) false))
        (writeSlot state message.currentTarget k
          (withAddr (storageAt state message.currentTarget k) a))
        (storeSub fork substate message.currentTarget k (originalAt state message.currentTarget k)
          (storageAt state message.currentTarget k)
          (withAddr (storageAt state message.currentTarget k) a))) := by
  have hexp : exponentBytes (0 : U256) = 0 := by decide
  unfold withAddr at hg ⊢
  rcases hp with rfl | rfl
  all_goals
    step pushR 2 (0x0100 : U256)
    step Local.exp (Nat.le_trans (by decide) hfork) (by code_fact) (by code_fact) (by gas_ok)
    rw [BlackList.exp0]
    step dupR 1
    step sload hfork (cold := false) (by code_fact) (by code_fact) hk (by gas_ok)
    rw [getStorage_eq]
    step dupR 1
    step pushR 20 ADDR_MASK
    step binR 0x02 Local.instruction_mul
    rw [mul_mask_one]
    step unR 0x19 Local.instruction_not
    step binR 0x16 Local.instruction_and
    step swapR 0
    norm
    step dupR 3
    step pushR 20 ADDR_MASK
    step binR 0x16 Local.instruction_and
    step binR 0x02 Local.instruction_mul
    rw [mul_one']
    step binR 0x17 Local.instruction_or
    step swapR 0
    norm
    step sstoreW hfork hglam (by code_fact) (by code_fact) hstatic (hasAccount_readSlot hacc)
      (coldIn_accessSlot_self _ _ _) (by gas_ok)
      (by rw [originalAt_readSlot, storageAt_readSlot]; gas_ok)
    rw [originalAt_readSlot, storageAt_readSlot, writeSlot_readSlot _ _ hacc, storeSub_accessSlot]
    step popR
    exact restate (by decide) rfl rfl (by gas_ok) rfl rfl

/-- At 2737 (deprecate): `deprecated = true`, slot 10 with byte 20 set to 1. -/
theorem depFlag (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam) {a : U256}
    {rest : List U256} (hrest : rest.length ≤ 16) (hstatic : message.isStatic = false)
    (hacc : hasAccount state message.currentTarget) {c10 : Bool}
    (hc10 : coldIn substate message.currentTarget 10 = c10) {M : ByteArray} {gas : Nat}
    (hstip : 2417 + slotCost c10 ≤ gas)
    (hg : 118 + slotCost c10 + sstoreCost fork (originalAt state message.currentTarget 10)
      (storageAt state message.currentTarget 10)
      (withPaused (storageAt state message.currentTarget 10) 1) false ≤ gas) :
    Hoare fork (At CODE message 2737 (a :: rest) M gas state substate)
      (At CODE message 2765 (a :: rest) M
        (gas - (118 + slotCost c10 + sstoreCost fork (originalAt state message.currentTarget 10)
          (storageAt state message.currentTarget 10)
          (withPaused (storageAt state message.currentTarget 10) 1) false))
        (writeSlot state message.currentTarget 10
          (withPaused (storageAt state message.currentTarget 10) 1))
        (storeSub fork substate message.currentTarget 10
          (originalAt state message.currentTarget 10) (storageAt state message.currentTarget 10)
          (withPaused (storageAt state message.currentTarget 10) 1))) := by
  have hexp : exponentBytes (0x14 : U256) = 1 := by decide
  have hb : isZero (isZero (1 : U256)) = 1 := by decide
  unfold withPaused at hg ⊢
  step jumpdestR
  step pushR 1 (0x01 : U256)
  step pushR 1 (0x0a : U256)
  step pushR 1 (0x14 : U256)
  step pushR 2 (0x0100 : U256)
  step Local.exp (Nat.le_trans (by decide) hfork) (by code_fact) (by code_fact) (by gas_ok)
  rw [exp20]
  step dupR 1
  step sload hfork (cold := c10) (by code_fact) (by code_fact) hc10 (by gas_ok)
  rw [getStorage_eq]
  step dupR 1
  step pushR 1 (0xff : U256)
  step binR 0x02 Local.instruction_mul
  step unR 0x19 Local.instruction_not
  step binR 0x16 Local.instruction_and
  step swapR 0
  norm
  step dupR 3
  step unR 0x15 instruction_iszero
  step unR 0x15 instruction_iszero
  rw [hb]
  step binR 0x02 Local.instruction_mul
  step binR 0x17 Local.instruction_or
  step swapR 0
  norm
  step sstoreW hfork hglam (by code_fact) (by code_fact) hstatic (hasAccount_readSlot hacc)
    (coldIn_accessSlot_self _ _ _) (by gas_ok)
    (by rw [originalAt_readSlot, storageAt_readSlot]; gas_ok)
  rw [originalAt_readSlot, storageAt_readSlot, writeSlot_readSlot _ _ hacc, storeSub_accessSlot]
  step popR
  exact restate (by decide) rfl rfl (by gas_ok) rfl rfl


/-- At 2765 (deprecate): `DUP1 PUSH1 0a PUSH1 00` sets up the address write of slot 10. -/
theorem depPrefix {a : U256} {rest : List U256} (hrest : rest.length ≤ 16) {M : ByteArray}
    {gas : Nat} (hg : 9 ≤ gas) :
    Hoare fork (At CODE message 2765 (a :: rest) M gas state substate)
      (At CODE message 2770 (0 :: 0x0a :: a :: a :: rest) M (gas - 9) state substate) := by
  step dupR 0
  step pushR 1 (0x0a : U256)
  step pushR 1 (0 : U256)
  exact restate (by decide) rfl rfl (by gas_ok) rfl rfl

/-- At 7696 (transferOwnership): the test `newOwner == address(0)`, before the JUMPI at 7750. -/
theorem ownTest {n : U256} {rest : List U256} (hrest : rest.length ≤ 16) {M : ByteArray}
    {gas : Nat} (hg : 28 ≤ gas) :
    Hoare fork (At CODE message 7696 (n :: rest) M gas state substate)
      (At CODE message 7747 (isZero (isZero (equal (bitwiseAnd ADDR_MASK n)
          (bitwiseAnd ADDR_MASK 0))) :: n :: rest) M (gas - 28) state substate) := by
  step jumpdestR
  step pushR 1 (0 : U256)
  step pushR 20 ADDR_MASK
  step binR 0x16 Local.instruction_and
  step dupR 1
  step pushR 20 ADDR_MASK
  step binR 0x16 Local.instruction_and
  step binR 0x14 instruction_eq
  step unR 0x15 instruction_iszero
  step unR 0x15 instruction_iszero
  exact restate (by decide) rfl rfl (by gas_ok) rfl rfl

/-- `newOwner` masked to 160 bits is 0: the code skips the write and stops. -/
theorem ownSkip {n x : U256} (hn : bitwiseAnd ADDR_MASK n = 0) {M : ByteArray} {gas : Nat}
    (hg : 25 ≤ gas) :
    Spec fork (At CODE message 7747 (isZero (isZero (equal (bitwiseAnd ADDR_MASK n)
        (bitwiseAnd ADDR_MASK 0))) :: [n, 0x097d, x]) M gas state substate)
      (Local.Stopped (gas - 25) state substate) := by
  have ht : isZero (isZero (equal (bitwiseAnd ADDR_MASK n) (bitwiseAnd ADDR_MASK 0))) ≠ 0 := by
    rw [hn]; decide
  step pushAnyR 2
  step jumpiR ht
  at_pc 7815
  step jumpdestR
  step popR
  step jumpR
  at_pc 2429
  step jumpdestR
  refine (Local.stop (by code_fact) (by code_fact)).consequence (fun _ h => h) ?_
  rintro evm ⟨hr, he, hgas, hs, hss⟩
  exact ⟨hr, he, by rw [hgas]; gas_ok, hs, hss⟩

/-- `newOwner` masked to 160 bits is not 0: the code sets up the write of slot 0. -/
theorem ownGo {n : U256} (hn : bitwiseAnd ADDR_MASK n ≠ 0) {rest : List U256}
    (hrest : rest.length ≤ 16) {M : ByteArray} {gas : Nat} (hg : 22 ≤ gas) :
    Hoare fork (At CODE message 7747 (isZero (isZero (equal (bitwiseAnd ADDR_MASK n)
        (bitwiseAnd ADDR_MASK 0))) :: n :: rest) M gas state substate)
      (At CODE message 7755 (0 :: 0 :: n :: n :: rest) M (gas - 22) state substate) := by
  have ht : isZero (isZero (equal (bitwiseAnd ADDR_MASK n) (bitwiseAnd ADDR_MASK 0))) = 0 := by
    have h0 : bitwiseAnd ADDR_MASK (0 : U256) = 0 := by decide
    rw [h0]; simp only [equal, isZero]; split <;> first | (exfalso; contradiction) | decide
  step pushAnyR 2
  step jumpi0R ht
  step dupR 0
  step pushR 1 (0 : U256)
  step dupR 0
  exact restate (by decide) rfl rfl (by gas_ok) rfl rfl

/-- At 7815 (transferOwnership after the write): back to 2429 and STOP. -/
theorem ownEnd {n x : U256} {M : ByteArray} {gas : Nat} (hg : 12 ≤ gas) :
    Spec fork (At CODE message 7815 [n, 0x097d, x] M gas state substate)
      (Local.Stopped (gas - 12) state substate) := by
  step jumpdestR
  step popR
  step jumpR
  at_pc 2429
  step jumpdestR
  refine (Local.stop (by code_fact) (by code_fact)).consequence (fun _ h => h) ?_
  rintro evm ⟨hr, he, hgas, hs, hss⟩
  exact ⟨hr, he, by rw [hgas]; gas_ok, hs, hss⟩

end UsdtVerify.AddrWrite
