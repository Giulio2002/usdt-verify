import UsdtVerify.Evm.Stuck
import UsdtVerify.Evm.Write
import UsdtVerify.Usdt.Proofs.Common
import EthLib.Execution.Proofs.Evm.Logic.Log
import UsdtVerify.Usdt.Proofs.Owner

/-!
# pause() and unpause()

Pausable's `pause() onlyOwner whenNotPaused` sets `paused = true` and logs `Pause()`;
`unpause() onlyOwner whenPaused` sets `paused = false` and logs `Unpause()`.
`paused` is byte 20 of slot 0, packed above `owner` (the low 160 bits).

- pause: entry 1533, body 4936, check at 4940, `whenNotPaused` at 5027, write at 5055, back to
  1552 (STOP).
- unpause: entry 1201, body 4333, check at 4337, `whenPaused` at 4424, write at 4451, back to
  1220 (STOP).
-/

namespace UsdtVerify.Pause

open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts
open Owner

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate}

/-- The entry of a function without arguments: the value check, then a jump to the body `b`
with the return address `r`. -/
theorem entry0 {e r b : Nat} (hp : (e = 1533 ∧ r = 0x0610 ∧ b = 4936) ∨
      (e = 1201 ∧ r = 0x04c4 ∧ b = 4333))
    (hv : message.value = 0) {x : U256} {M : ByteArray} {gas : Nat} (hg : 34 ≤ gas) :
    Gas.HoareG fork (At CODE message e [x] M gas state substate)
      (At CODE message b [BitVec.ofNat 256 r, x] M (gas - 34) state substate) := by
  rcases hp with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
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

/-- `2 ^ 160`, the unit of byte 20. -/
abbrev B20 : U256 := BitVec.ofNat 256 (2 ^ 160)

/-- Slot 0 with byte 20 (the `paused` flag) replaced by the low bit of `b`, the other bytes kept:
`(w & ~(0xff << 160)) | (b << 160)`, as the code computes it for `b` 0 or 1. -/
def withPaused (w b : U256) : U256 :=
  bitwiseOr (mul b B20) (bitwiseAnd (bitwiseNot (mul 0xff B20)) w)

theorem exp20 : exp (0x0100 : U256) (0x14 : U256) = B20 := by decide +kernel

/-- The flag test of the code, twice negated: nonzero exactly when byte 20 is not 0. -/
theorem isZero2_flag {w : U256} (h : byte20 w ≠ 0) :
    isZero (isZero (bitwiseAnd (0xff : U256) (div w (exp (0x0100 : U256) (0x14 : U256))))) ≠ 0 := by
  have h3 := isZero3_flag h
  intro h2
  rw [h2] at h3
  exact absurd h3 (by decide)

theorem isZero2_flag_eq {w : U256} (h : byte20 w = 0) :
    isZero (isZero (bitwiseAnd (0xff : U256) (div w (exp (0x0100 : U256) (0x14 : U256))))) = 0 := by
  rw [flag_eq, h]
  decide

/-! ## The flag checks -/

/-- At 5027 (`whenNotPaused` of pause): reads slot 0 and tests byte 20; the triple ISZERO of the
flag is the test word, before the JUMPI at 5050. -/
theorem pauseTest (hfork : .berlin ≤ fork) {rest : List U256} (hrest : rest.length ≤ 16)
    {M : ByteArray} {c0 : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0) {gas : Nat}
    (hg : 99 + slotCost c0 ≤ gas) :
    Gas.HoareG fork (At CODE message 5027 rest M gas state substate)
      (At CODE message 5047 (isZero (isZero (isZero (bitwiseAnd (0xff : U256)
          (div (storageAt state message.currentTarget 0) (exp (0x0100 : U256) (0x14 : U256)))))) ::
          rest) M (gas - (99 + slotCost c0))
        (readSlot state message.currentTarget 0) (accessSlot substate message.currentTarget 0)) := by
  have hexp : exponentBytes (0x14 : U256) = 1 := by decide
  step jumpdestR
  step pushR 1 (0 : U256)
  step pushR 1 (0x14 : U256)
  step swapR 0
  norm
  step Gas.sloadG hfork (cold := c0) (by code_fact) (by code_fact) hc0 (by gas_ok)
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
  step unR 0x15 instruction_iszero
  step unR 0x15 instruction_iszero
  exact restate (by decide) rfl rfl (by gas_ok) rfl rfl

/-- At 4424 (`whenPaused` of unpause): the same test with two ISZERO, before the JUMPI at 4446. -/
theorem unpauseTest (hfork : .berlin ≤ fork) {rest : List U256} (hrest : rest.length ≤ 16)
    {M : ByteArray} {c0 : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0) {gas : Nat}
    (hg : 96 + slotCost c0 ≤ gas) :
    Gas.HoareG fork (At CODE message 4424 rest M gas state substate)
      (At CODE message 4443 (isZero (isZero (bitwiseAnd (0xff : U256)
          (div (storageAt state message.currentTarget 0) (exp (0x0100 : U256) (0x14 : U256))))) ::
          rest) M (gas - (96 + slotCost c0))
        (readSlot state message.currentTarget 0) (accessSlot substate message.currentTarget 0)) := by
  have hexp : exponentBytes (0x14 : U256) = 1 := by decide
  step jumpdestR
  step pushR 1 (0 : U256)
  step pushR 1 (0x14 : U256)
  step swapR 0
  norm
  step Gas.sloadG hfork (cold := c0) (by code_fact) (by code_fact) hc0 (by gas_ok)
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
  step unR 0x15 instruction_iszero
  exact restate (by decide) rfl rfl (by gas_ok) rfl rfl

/-- The JUMPI of a flag check: a nonzero test word goes on at the destination `d`. -/
theorem flagPass {p d : Nat} (hp : (p = 5047 ∧ d = 5055) ∨ (p = 4443 ∧ d = 4451)) {t : U256}
    (ht : t ≠ 0) {rest : List U256} (hrest : rest.length ≤ 16) {M : ByteArray} {gas : Nat}
    (hg : 13 ≤ gas) :
    Gas.HoareG fork (At CODE message p (t :: rest) M gas state substate)
      (At CODE message d rest M (gas - 13) state substate) := by
  rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals
    step pushAnyR 2
    step jumpiR ht
    exact restate (by decide) rfl rfl (by gas_ok) rfl rfl

/-- The JUMPI of a flag check: a zero test word reverts with no output. -/
theorem flagRevert (hfork : .berlin ≤ fork) {p : Nat} (hp : p = 5047 ∨ p = 4443) {t : U256}
    (ht : t = 0) {rest : List U256} (hrest : rest.length ≤ 16) {M : ByteArray} (hM : M.size = 96)
    {gas : Nat} (hg : 19 ≤ gas) :
    Gas.SpecG fork (At CODE message p (t :: rest) M gas state substate)
      (Halted true .empty (gas - 19) state substate) := by
  have hz : extendMemory M.size [((0 : U256), (0 : U256))] = ⟨0, 0⟩ := by
    rw [hM]; decide
  rcases hp with rfl | rfl
  all_goals
    step pushAnyR 2
    step jumpi0R ht
    step pushR 1 (0 : U256)
    step dupR 0
    refine (Gas.revertG (Nat.le_trans (by decide) hfork) (by code_fact) (by code_fact)
      (by rw [hz]; gas_ok)).consequence (fun _ h => h) ?_
    rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
    refine ⟨hr, he, ?_, ?_, hs, hss⟩
    · rw [ho]; simp [memoryReadBytes]
    · rw [hgas, hz]; gas_ok

/-! ## The writes and the logs -/

/-- The topic of `Pause()`. -/
abbrev PAUSE_TOPIC : U256 :=
  0x6985a02210a168e66602d3235cb6db0e70f92b3ba4d376a33c0f3d9434bff625

/-- The topic of `Unpause()`. -/
abbrev UNPAUSE_TOPIC : U256 :=
  0x7805862f689e2f13df9f062ff482ad3ad112aca9e0847911ed832e158c525b33

/-- A log of the contract `c` with the one topic `t` and no data. -/
abbrev log0 (c : EthLib.Base.Address) (t : U256) : Blocks.Log :=
  { address := c, topics := [t].map U256.toBeBytes, data := .empty }

/-- From the `PUSH32` of the topic: the log with no data, the jump back to `r`, and the STOP
there. -/
theorem logStop {p : Nat} {t : U256} {r : Nat}
    (hp : (p = 5083 ∧ t = PAUSE_TOPIC ∧ r = 0x0610) ∨ (p = 4478 ∧ t = UNPAUSE_TOPIC ∧ r = 0x04c4))
    {x : U256} (hstatic : message.isStatic = false) {M : ByteArray} (hM : M.size = 96)
    (hptr : loadWord (memoryReadBytes M 64 32) 0 32 = 0x60) {gas : Nat} (hg : 786 ≤ gas) :
    Gas.SpecG fork (At CODE message p [BitVec.ofNat 256 r, x] M gas state substate)
      (Halted false .empty (gas - 786) state
        { substate with logs := substate.logs.push (log0 message.currentTarget t) }) := by
  have hext0 : extendMemory M.size [((0x40 : U256), (32 : U256))] = ⟨0, 0⟩ := by
    rw [hM]; decide
  have hext3 : extendMemory M.size [((0x60 : U256), (0 : U256))] = ⟨0, 0⟩ := by
    rw [hM]; decide
  have hlog : logCost (1 : Fin 5).val (0 : U256) = 750 := by decide
  have hsub : sub (0x60 : U256) 0x60 = 0 := by decide
  rcases hp with ⟨rfl, ht, rfl⟩ | ⟨rfl, ht, rfl⟩
  all_goals
    step Gas.pushG (n := 32) (word := t) (by decide) (by code_fact) (by code_fact)
      (decode_push 32 (by decide)) (by rw [ht, pushData_CODE]; decide) (by gas_ok) (by stk_ok)
    step pushR 1 (0x40 : U256)
    step Gas.mloadG (by code_fact) (by code_fact) (by rw [hext0]; gas_ok)
    step Gas.reshapeG (s' := (0x60 : U256) :: _) (m' := M)
      (by rw [hext0, memoryExtend_zero]; exact congrArg (· :: _) hptr)
      (by rw [hext0, memoryExtend_zero]) (by rw [hext0])
    step pushR 1 (0x40 : U256)
    step Gas.mloadG (by code_fact) (by code_fact) (by rw [hext0]; gas_ok)
    step Gas.reshapeG (s' := (0x60 : U256) :: _) (m' := M)
      (by rw [hext0, memoryExtend_zero]; exact congrArg (· :: _) hptr)
      (by rw [hext0, memoryExtend_zero]) (by rw [hext0])
    step dupR 0
    step swapR 1
    norm
    step binR 0x03 Local.instruction_sub
    step swapR 0
    norm
    rw [hsub]
    step Gas.reshapeG (s' := 0x60 :: 0 :: ([_] ++ [_, x])) rfl rfl rfl
    step Gas.logG (n := 1) (byte := 0xa1) rfl (by code_fact) (by code_fact) rfl hstatic
      (by rw [hlog, hext3]; gas_ok)
    step Gas.reshapeG rfl (by rw [hext3, memoryExtend_zero]) (by rw [hlog, hext3])
    step jumpR
    step jumpdestR
    refine (Gas.stopG (by code_fact) (by code_fact)).consequence (fun _ h => h) ?_
    rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
    refine ⟨hr, he, ho, by rw [hgas]; gas_ok, hs, ?_⟩
    rw [hss, hext3, memoryExtend_zero]
    simp [memoryReadBytes, log0]

-- The shared part of the two writes, from the `EXP` of `256 ^ 20` to the `SSTORE`.
set_option hygiene false in
macro "flag_pre" : tactic => `(tactic| (
  step Gas.expLG (Nat.le_trans (by decide) hfork) (by code_fact) (by code_fact) (by gas_ok)
  rw [exp20]
  step dupR 1
  step Gas.sloadG hfork (cold := false) (by code_fact) (by code_fact) hc0 (by gas_ok)
  rw [show state.getStorage message.currentTarget (U256.toBeBytes 0) =
    storageAt state message.currentTarget 0 from rfl]
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
  norm))

-- The shared part of the two writes, from the `EXP` of `256 ^ 20` to the `POP` after `SSTORE`.
set_option hygiene false in
macro "flag_write" : tactic => `(tactic| (
  flag_pre
  step Gas.sstoreWG hfork (by code_fact) (by code_fact) hstatic (hasAccount_readSlot hacc)
    (coldIn_accessSlot_self _ _ _) (by gas_ok)
    (by rw [originalAt_readSlot, storageAt_readSlot]; gas_ok)
  rw [originalAt_readSlot, storageAt_readSlot]
  step popR
  exact restate (by decide) rfl rfl (by gas_ok) rfl rfl))

/-- At 5055 (pause), the code writes slot 0 with byte 20 set to 1. -/
theorem pauseWrite (hfork : .berlin ≤ fork) {rest : List U256}
    (hrest : rest.length ≤ 16) (hstatic : message.isStatic = false)
    (hacc : hasAccount state message.currentTarget)
    (hc0 : coldIn substate message.currentTarget 0 = false) {M : ByteArray} {gas : Nat}
    (hstip : 2517 ≤ gas)
    (hg : 218 + Gas.writeCost fork (originalAt state message.currentTarget 0)
      (storageAt state message.currentTarget 0)
      (withPaused (storageAt state message.currentTarget 0) 1) false ≤ gas) :
    Gas.HoareG fork (At CODE message 5055 rest M gas state substate)
      (At CODE message 5083 rest M
        (gas - (218 + Gas.writeCost fork (originalAt state message.currentTarget 0)
          (storageAt state message.currentTarget 0)
          (withPaused (storageAt state message.currentTarget 0) 1) false))
        (writeSlot (readSlot state message.currentTarget 0) message.currentTarget 0
          (withPaused (storageAt state message.currentTarget 0) 1))
        (storeSub fork (accessSlot substate message.currentTarget 0) message.currentTarget 0
          (originalAt state message.currentTarget 0) (storageAt state message.currentTarget 0)
          (withPaused (storageAt state message.currentTarget 0) 1))) := by
  have hexp : exponentBytes (0x14 : U256) = 1 := by decide
  have hb : isZero (isZero (1 : U256)) = 1 := by decide
  unfold withPaused at hg ⊢
  step jumpdestR
  step pushR 1 (0x01 : U256)
  step pushR 1 (0 : U256)
  step pushR 1 (0x14 : U256)
  step pushR 2 (0x0100 : U256)
  flag_write

/-- At 4451 (unpause), the code writes slot 0 with byte 20 set to 0. -/
theorem unpauseWrite (hfork : .berlin ≤ fork) {rest : List U256}
    (hrest : rest.length ≤ 16) (hstatic : message.isStatic = false)
    (hacc : hasAccount state message.currentTarget)
    (hc0 : coldIn substate message.currentTarget 0 = false) {M : ByteArray} {gas : Nat}
    (hstip : 2517 ≤ gas)
    (hg : 218 + Gas.writeCost fork (originalAt state message.currentTarget 0)
      (storageAt state message.currentTarget 0)
      (withPaused (storageAt state message.currentTarget 0) 0) false ≤ gas) :
    Gas.HoareG fork (At CODE message 4451 rest M gas state substate)
      (At CODE message 4478 rest M
        (gas - (218 + Gas.writeCost fork (originalAt state message.currentTarget 0)
          (storageAt state message.currentTarget 0)
          (withPaused (storageAt state message.currentTarget 0) 0) false))
        (writeSlot (readSlot state message.currentTarget 0) message.currentTarget 0
          (withPaused (storageAt state message.currentTarget 0) 0))
        (storeSub fork (accessSlot substate message.currentTarget 0) message.currentTarget 0
          (originalAt state message.currentTarget 0) (storageAt state message.currentTarget 0)
          (withPaused (storageAt state message.currentTarget 0) 0))) := by
  have hexp : exponentBytes (0x14 : U256) = 1 := by decide
  have hb : isZero (isZero (0 : U256)) = 0 := by decide
  unfold withPaused at hg ⊢
  step jumpdestR
  step pushR 1 (0 : U256)
  step dupR 0
  step pushR 1 (0x14 : U256)
  step pushR 2 (0x0100 : U256)
  flag_write

/-- At 5055 (pause), in a static frame or with no account for `C`: the run reaches the `SSTORE`
of slot 0, which is `Stuck`. -/
theorem pauseWriteBad (hfork : .berlin ≤ fork) {rest : List U256}
    (hrest : rest.length ≤ 16)
    (hbad : message.isStatic = true ∨ ¬hasAccount state message.currentTarget)
    (hc0 : coldIn substate message.currentTarget 0 = false) {M : ByteArray} {gas : Nat}
    (hg : 218 ≤ gas) :
    Gas.HoareG fork (At CODE message 5055 rest M gas state substate) Gas.Stuck := by
  have hexp : exponentBytes (0x14 : U256) = 1 := by decide
  have hb : isZero (isZero (1 : U256)) = 1 := by decide
  step jumpdestR
  step pushR 1 (0x01 : U256)
  step pushR 1 (0 : U256)
  step pushR 1 (0x14 : U256)
  step pushR 2 (0x0100 : U256)
  flag_pre
  exact Gas.sstoreStuckW (by code_fact) (by code_fact) hbad

/-- At 4451 (unpause), in a static frame or with no account for `C`: the run reaches the
`SSTORE` of slot 0, which is `Stuck`. -/
theorem unpauseWriteBad (hfork : .berlin ≤ fork) {rest : List U256}
    (hrest : rest.length ≤ 16)
    (hbad : message.isStatic = true ∨ ¬hasAccount state message.currentTarget)
    (hc0 : coldIn substate message.currentTarget 0 = false) {M : ByteArray} {gas : Nat}
    (hg : 218 ≤ gas) :
    Gas.HoareG fork (At CODE message 4451 rest M gas state substate) Gas.Stuck := by
  have hexp : exponentBytes (0x14 : U256) = 1 := by decide
  have hb : isZero (isZero (0 : U256)) = 0 := by decide
  step jumpdestR
  step pushR 1 (0 : U256)
  step dupR 0
  step pushR 1 (0x14 : U256)
  step pushR 2 (0x0100 : U256)
  flag_pre
  exact Gas.sstoreStuckW (by code_fact) (by code_fact) hbad

/-! ## The word written to slot 0 -/

/-- Bit `j` of the number 1. -/
theorem testBit_one' (j : Nat) : Nat.testBit 1 j = decide (j = 0) := by
  rcases j with _ | j
  · rfl
  · simp [Nat.testBit_succ]

theorem one_bit (j : Nat) : (1 : U256).getLsbD j = decide (j = 0) := testBit_one' j

/-- Byte 20 of a word, from its bits 160 to 167. -/
theorem byte20_of_bits {x : U256} (b : Nat) (hb : b < 256)
    (h : ∀ j, j < 8 → x.getLsbD (160 + j) = b.testBit j) : byte20 x = b := by
  unfold byte20
  apply Nat.eq_of_testBit_eq
  intro j
  change (x.toNat / 2 ^ 160 % 2 ^ 8).testBit j = b.testBit j
  rw [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  by_cases hj : j < 8
  · simp only [hj, decide_true, Bool.true_and]
    rw [Nat.add_comm, ← h j hj]
    rfl
  · simp only [hj, decide_false, Bool.false_and]
    have h8 : 2 ^ 8 ≤ 2 ^ j := Nat.pow_le_pow_right (by decide) (by omega)
    exact (Nat.testBit_lt_two_pow (show b < 2 ^ j by omega)).symm

theorem mul_one_B20 : mul (1 : U256) B20 = (1 : U256) <<< 160 := by decide +kernel
theorem mul_zero_B20 : mul (0 : U256) B20 = 0 := by decide +kernel
theorem mul_ff_B20 : mul (0xff : U256) B20 = (0xff : U256) <<< 160 := by decide +kernel

theorem ff_bit (j : Nat) : (0xff : U256).getLsbD j = decide (j < 8) := by
  rw [show (0xff : U256) = BitVec.ofNat 256 (2 ^ 8 - 1) by decide, BitVec.getLsbD_ofNat,
    Nat.testBit_two_pow_sub_one]
  by_cases h : j < 8 <;> simp [h] <;> omega

/-- The bits of `withPaused w b` for `b` 0 or 1: bit 160 is `b`, bits 161 to 167 are 0, and the
other bits are those of `w`. -/
theorem bit_withPaused (w b : U256) (hb : b = 0 ∨ b = 1) (i : Nat) :
    (withPaused w b).getLsbD i =
      ((decide (i = 160) && decide (b = 1)) || (!(decide (160 ≤ i ∧ i < 168)) && w.getLsbD i)) := by
  rcases hb with rfl | rfl
  · simp only [withPaused, bitwiseOr, bitwiseAnd, bitwiseNot, mul_zero_B20, mul_ff_B20]
    simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft,
      ff_bit]
    by_cases h : i < 256
    · by_cases h1 : 160 ≤ i <;> by_cases h2 : i < 168 <;> simp [h, h1, h2] <;> omega
    · simp [h, BitVec.getLsbD_of_ge w i (by omega)]
  · simp only [withPaused, bitwiseOr, bitwiseAnd, bitwiseNot, mul_one_B20, mul_ff_B20]
    simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft,
      ff_bit, one_bit]
    by_cases h : i < 256
    · cases w.getLsbD i <;> simp [h]
      all_goals
        revert h
        revert i
        decide +kernel
    · simp [h, BitVec.getLsbD_of_ge w i (by omega)]; omega

/-- Byte 20 of `withPaused w b` is `b`. -/
theorem byte20_withPaused (w b : U256) (hb : b = 0 ∨ b = 1) : byte20 (withPaused w b) = b.toNat := by
  have hlt : b.toNat < 256 := by rcases hb with rfl | rfl <;> decide
  apply byte20_of_bits _ hlt
  intro j hj
  rw [bit_withPaused w b hb]
  rcases hb with rfl | rfl
  · simp
    intro h
    omega
  · have h8 : 160 + j < 168 := by omega
    simp [h8, testBit_one']

/-- `withPaused` keeps the owner (the low 160 bits). -/
theorem owner_withPaused (w b : U256) (hb : b = 0 ∨ b = 1) :
    bitwiseAnd ADDR_MASK (withPaused w b) = bitwiseAnd ADDR_MASK w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hm : ∀ j, (ADDR_MASK).getLsbD j = decide (j < 160) := by
    intro j
    rw [BitVec.getLsbD_ofNat, Nat.testBit_two_pow_sub_one]
    by_cases h : j < 160 <;> simp [h] <;> omega
  simp only [bitwiseAnd, BitVec.getLsbD_and, hm, bit_withPaused w b hb]
  by_cases hw : w.getLsbD i <;> simp [hw] <;> omega

end UsdtVerify.Pause
