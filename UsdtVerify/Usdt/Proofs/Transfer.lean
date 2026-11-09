import UsdtVerify.Evm.Stuck
import UsdtVerify.Evm.Write
import UsdtVerify.Usdt.Proofs.SafeMath
import EthLib.Execution.Proofs.Evm.Logic.Rules
import EthLib.Execution.Proofs.Evm.Logic.Log

/-!
# transfer(address,uint256): the blocks

Proves the Hoare triples of the blocks of transfer, and its success path from 9883 with a fee
of 0.

The specifications that compose these blocks are in Usdt/Spec/Transfer.lean.

The parts below keep their own headers:

- transfer(address,uint256)
- transfer(address,uint256): the blocks of the success path, from 9883
- transfer(address,uint256): the success path from 9883, with a fee of 0
-/

section

/-!
## transfer(address,uint256)

- At 1866, the entry checks that the call has no value, reads argument word 0 masked to 160 bits
  (the recipient) and argument word 1 (the amount), and jumps to 5364 with return address 1930.
- At 5364, the code reads slot 0 and tests byte 20 (the `paused` flag); when it is set, it reverts.

The reverts that these blocks give (paused, blacklisted, short call data) are stated from pc 0 in
Usdt/Spec/Transfer.lean.
-/

namespace UsdtVerify.Transfer

open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate}

/-- From 1866, a call with no value goes to 5364 with the amount, the recipient and 1930. -/
theorem entry (hv : message.value = 0) {x : U256} {gas : Nat} (hg : 98 ≤ gas) :
    Gas.HoareG fork (At CODE message 1866 [x] MEM0 gas state substate)
      (At CODE message 5364 [wordArg message.data 1, addrArg message.data 0, 0x078a, x] MEM0
        (gas - 98) state substate) := by
  step jumpdestR
  step Gas.callvalueG (by code_fact) (by code_fact) (by gas_ok) (by stk_ok)
  step unR 0x15 instruction_iszero
  step pushR 2 (0x0755 : U256)
  step jumpiR (by simp [hv, isZero])
  step jumpdestR
  step pushR 2 (0x078a : U256)
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
  step dupR 0
  step Gas.calldataloadG (by code_fact) (by code_fact) (by gas_ok)
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
  step pushR 2 (0x14f4 : U256)
  step jumpR
  exact (repc (by decide)).seq (Gas.reshapeG rfl rfl (by gas_ok))

/-- At 5364, when byte 20 of slot 0 is set, the code reverts with no output. -/
theorem pausedRevert (hfork : .berlin ≤ fork) {rest : List U256} (hrest : rest.length ≤ 16)
    {c0 : Bool} (hpaused : byte20 (storageAt state message.currentTarget 0) ≠ 0)
    (hc0 : coldIn substate message.currentTarget 0 = c0) {gas : Nat}
    (hg : 118 + slotCost c0 ≤ gas) :
    Gas.SpecG fork (At CODE message 5364 rest MEM0 gas state substate)
      (Halted true .empty (gas - (118 + slotCost c0)) (readSlot state message.currentTarget 0)
        (accessSlot substate message.currentTarget 0)) := by
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
  step pushR 2 (0x1510 : U256)
  step jumpi0R (isZero3_flag hpaused)
  step pushR 1 (0 : U256)
  step dupR 0
  have hz : extendMemory MEM0.size [((0 : U256), (0 : U256))] = ⟨0, 0⟩ := by
    rw [size_MEM0]; decide
  refine (Gas.revertG (Nat.le_trans (by decide) hfork) (by code_fact) (by code_fact)
    (by rw [hz]; gas_ok)).consequence (fun _ h => h) ?_
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  refine ⟨hr, he, ?_, ?_, hs, hss⟩
  · rw [ho]; simp [memoryReadBytes]
  · rw [hgas, hz]; gas_ok

/-- At 5364, when byte 20 of slot 0 is 0 (not paused), the code goes on to 5392. -/
theorem notPaused (hfork : .berlin ≤ fork) {rest : List U256} (hrest : rest.length ≤ 16)
    {c0 : Bool} (hnp : byte20 (storageAt state message.currentTarget 0) = 0)
    (hc0 : coldIn substate message.currentTarget 0 = c0) {gas : Nat}
    (hg : 112 + slotCost c0 ≤ gas) {M : ByteArray} :
    Gas.HoareG fork (At CODE message 5364 rest M gas state substate)
      (At CODE message 5392 rest M (gas - (112 + slotCost c0)) (readSlot state message.currentTarget 0)
        (accessSlot substate message.currentTarget 0)) := by
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
  step pushR 2 (0x1510 : U256)
  step jumpiR (isZero3_flag_ne hnp)
  exact (repc (by decide)).seq (Gas.reshapeG rfl rfl (by gas_ok))

/-- The low byte of a word, tested as the code tests a flag at byte 0, gives 0 after triple ISZERO
when it is set. -/
theorem isZero3_byte0 {w : U256} (h : w.toNat % 256 ≠ 0) :
    isZero (isZero (isZero (bitwiseAnd (0xff : U256) (div w (exp (0x0100 : U256) (0 : U256)))))) =
      0 := by
  have he : exp (0x0100 : U256) (0 : U256) = 1 := by decide +kernel
  have hb : w.toNat % 256 < 2 ^ 256 := Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide)
  have hne : bitwiseAnd (0xff : U256) (div w (exp (0x0100 : U256) (0 : U256))) ≠ 0 := by
    intro hz
    have := congrArg BitVec.toNat hz
    simp only [he, bitwiseAnd, div, BitVec.toNat_and, show (1 : U256) ≠ 0 by decide, ite_false,
      BitVec.toNat_ofNat, show BitVec.toNat (1 : U256) = 1 from rfl, Nat.div_one,
      Nat.mod_eq_of_lt w.isLt] at this
    rw [show BitVec.toNat (0xff : U256) = 2 ^ 8 - 1 by rfl, Nat.and_comm,
      Nat.and_two_pow_sub_one_eq_mod] at this
    exact h this
  unfold isZero
  rw [ite_eq_right hne]
  decide

/-- The memory after a lookup in a mapping at base `b`: the key word at 0 and `b` at 32. -/
abbrev MEMK (k b : U256) : ByteArray :=
  memoryWrite (memoryWrite MEM0 0 (wordBytes k)) 32 (wordBytes b)

theorem size_MEMK (k b : U256) : (MEMK k b).size = 96 := by
  rw [MEMK, size_memoryWrite, size_memoryWrite] <;>
    simp [size_memoryWrite, size_MEM0, size_wordBytes]

/-- The key word of the caller, as the code computes it: the caller masked twice. -/
abbrev callerKey (message : Message fork) : U256 :=
  bitwiseAnd ADDR_MASK (bitwiseAnd ADDR_MASK message.caller.toU256)

/-- The slot of `isBlackListed[caller]`: mapping base slot 6. -/
abbrev blackSlot (message : Message fork) : U256 := mapSlot (callerKey message) 6

/-- The test word of the blacklist flag of a word: the triple ISZERO of its low byte. -/
abbrev blackTest (w : U256) : U256 :=
  isZero (isZero (isZero (bitwiseAnd (0xff : U256) (div w (exp (0x0100 : U256) (0 : U256))))))

/-- At 5392, the code reads `isBlackListed[caller]` and reaches the JUMPI at 5476 on its test. -/
theorem blackLookup (hfork : .berlin ≤ fork) {rest : List U256} (hrest : rest.length ≤ 16)
    {cB : Bool} (hcB : coldIn substate message.currentTarget (blackSlot message) = cB) {gas : Nat}
    (hg : 141 + slotCost cB ≤ gas) :
    Gas.HoareG fork (At CODE message 5392 rest MEM0 gas state substate)
      (At CODE message 5476
        ((0x1569 : U256) :: blackTest (storageAt state message.currentTarget (blackSlot message)) ::
          rest) (MEMK (callerKey message) 6) (gas - (141 + slotCost cB))
        (readSlot state message.currentTarget (blackSlot message))
        (accessSlot substate message.currentTarget (blackSlot message))) := by
  have hexp : exponentBytes (0 : U256) = 0 := by decide
  have hs1 : (memoryWrite MEM0 0 (wordBytes (callerKey message))).size = 96 := by
    rw [size_memoryWrite] <;> simp [size_MEM0, size_wordBytes]
  have hext1 : extendMemory MEM0.size [((0 : U256), (32 : U256))] = ⟨0, 0⟩ := by
    rw [size_MEM0]; decide
  have hext2 : extendMemory (memoryWrite MEM0 0 (wordBytes (callerKey message))).size
      [((0x20 : U256), (32 : U256))] = ⟨0, 0⟩ := by
    rw [hs1]; decide
  have hext3 : extendMemory (MEMK (callerKey message) 6).size [((0 : U256), (0x40 : U256))] =
      ⟨0, 0⟩ := by
    rw [size_MEMK]; decide
  have hk : keccak256Cost (0x40 : U256) = 42 := by decide
  have hread : memoryReadBytes (MEMK (callerKey message) 6) 0 64 =
      wordBytes (callerKey message) ++ wordBytes 6 := by
    have h := memoryReadBytes_memoryWrite_memoryWrite (memory := MEM0)
      (a := wordBytes (callerKey message)) (b := wordBytes 6) (s := 0)
      (by simp [size_MEM0, size_wordBytes])
    simpa [size_wordBytes, MEMK] using h
  step jumpdestR
  step pushR 1 (0x06 : U256)
  step pushR 1 (0 : U256)
  step Gas.callerG (by code_fact) (by code_fact) (by gas_ok) (by stk_ok)
  step pushR 20 ADDR_MASK
  step binR 0x16 Local.instruction_and
  step pushR 20 ADDR_MASK
  step binR 0x16 Local.instruction_and
  step dupR 1
  step Gas.mstoreG (by code_fact) (by code_fact) (by rw [hext1]; gas_ok)
  step Gas.reshapeG (m' := memoryWrite MEM0 0 (wordBytes (callerKey message))) rfl
    (by rw [hext1, memoryExtend_zero]; rfl) (by rw [hext1] <;> gas_ok)
  step pushR 1 (0x20 : U256)
  step binR 0x01 instruction_add
  step swapR 0
  norm
  step dupR 1
  step Gas.reshapeG (s' := (0x20 : U256) :: 6 :: 0x20 :: rest) rfl rfl rfl
  step Gas.mstoreG (by code_fact) (by code_fact) (by rw [hext2]; gas_ok)
  step Gas.reshapeG (m' := MEMK (callerKey message) 6) rfl (by rw [hext2, memoryExtend_zero]; rfl)
    (by rw [hext2] <;> gas_ok)
  step pushR 1 (0x20 : U256)
  step binR 0x01 instruction_add
  step pushR 1 (0 : U256)
  step Gas.reshapeG (s' := (0 : U256) :: 0x40 :: rest) rfl rfl rfl
  step Gas.keccak256G (by code_fact) (by code_fact) (by rw [hk, hext3]; gas_ok)
  step Gas.reshapeG (s' := blackSlot message :: rest) (m' := MEMK (callerKey message) 6)
    (by rw [hext3, memoryExtend_zero, show (0 : U256).toNat = 0 from rfl,
      show (0x40 : U256).toNat = 64 from rfl, hread]; rfl)
    (by rw [hext3, memoryExtend_zero]) (by rw [hext3, hk] <;> gas_ok)
  step pushR 1 (0 : U256)
  step swapR 0
  norm
  step Gas.sloadG hfork (cold := cB) (by code_fact) (by code_fact) hcB (by gas_ok)
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
  step pushR 2 (0x1569 : U256)
  exact (repc (by decide)).seq (Gas.reshapeG rfl rfl (by gas_ok))

/-- At 5392, when the low byte of `isBlackListed[caller]` is set, the code reverts. -/
theorem blackRevert (hfork : .berlin ≤ fork) {rest : List U256} (hrest : rest.length ≤ 16)
    {cB : Bool} (hblack : (storageAt state message.currentTarget (blackSlot message)).toNat % 256 ≠ 0)
    (hcB : coldIn substate message.currentTarget (blackSlot message) = cB) {gas : Nat}
    (hg : 157 + slotCost cB ≤ gas) :
    Gas.SpecG fork (At CODE message 5392 rest MEM0 gas state substate)
      (Halted true .empty (gas - (157 + slotCost cB))
        (readSlot state message.currentTarget (blackSlot message))
        (accessSlot substate message.currentTarget (blackSlot message))) := by
  have hz : extendMemory (MEMK (callerKey message) 6).size [((0 : U256), (0 : U256))] = ⟨0, 0⟩ := by
    rw [size_MEMK]; decide
  step blackLookup hfork hrest hcB (by gas_ok)
  step jumpi0R (isZero3_byte0 hblack)
  step pushR 1 (0 : U256)
  step dupR 0
  refine (Gas.revertG (Nat.le_trans (by decide) hfork) (by code_fact) (by code_fact)
    (by rw [hz]; gas_ok)).consequence (fun _ h => h) ?_
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  refine ⟨hr, he, ?_, ?_, hs, hss⟩
  · rw [ho]; simp [memoryReadBytes]
  · rw [hgas, hz]; gas_ok

/-- A clear low byte makes the blacklist test nonzero. -/
theorem blackTest_ne {w : U256} (h : w.toNat % 256 = 0) : blackTest w ≠ 0 := by
  have he : exp (0x0100 : U256) (0 : U256) = 1 := by decide +kernel
  have hz : bitwiseAnd (0xff : U256) (div w (exp (0x0100 : U256) (0 : U256))) = 0 := by
    apply BitVec.eq_of_toNat_eq
    simp only [he, bitwiseAnd, div, BitVec.toNat_and, show (1 : U256) ≠ 0 by decide, ite_false,
      BitVec.toNat_ofNat, show BitVec.toNat (1 : U256) = 1 from rfl, Nat.div_one,
      Nat.mod_eq_of_lt w.isLt]
    rw [show BitVec.toNat (0xff : U256) = 2 ^ 8 - 1 by rfl, Nat.and_comm,
      Nat.and_two_pow_sub_one_eq_mod]
    simpa using h
  simp only [blackTest]
  rw [hz]
  decide

/-- At 5481, when byte 20 of slot 10 is 0 (not deprecated), the code goes to 5775. -/
theorem depInline (hfork : .berlin ≤ fork) {rest : List U256} (hrest : rest.length ≤ 16)
    {c10 : Bool} (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    (hc10 : coldIn substate message.currentTarget 10 = c10) {gas : Nat}
    (hg : 106 + slotCost c10 ≤ gas) {M : ByteArray} :
    Gas.HoareG fork (At CODE message 5481 rest M gas state substate)
      (At CODE message 5775 rest M (gas - (106 + slotCost c10))
        (readSlot state message.currentTarget 10) (accessSlot substate message.currentTarget 10)) := by
  have hexp : exponentBytes (0x14 : U256) = 1 := by decide
  step jumpdestR
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
  step pushR 2 (0x168f : U256)
  step jumpiR (isZero_flag_ne hdep)
  exact (repc (by decide)).seq (Gas.reshapeG rfl rfl (by gas_ok))

/-- At 5775, the code calls the token transfer at 9883 with the amount and the recipient. -/
theorem toBasic {w1 a r s : U256} {gas : Nat} (hg : 21 ≤ gas) {M : ByteArray} :
    Gas.HoareG fork (At CODE message 5775 [w1, a, r, s] M gas state substate)
      (At CODE message 9883 [w1, a, 0x1699, w1, a, r, s] M (gas - 21) state substate) := by
  step jumpdestR
  step pushR 2 (0x1699 : U256)
  step dupR 2
  step dupR 2
  step pushR 2 (0x269b : U256)
  step jumpR
  exact (repc (by decide)).seq (Gas.reshapeG rfl rfl (by gas_ok))

/-- At 9883, call data of fewer than 68 bytes (two argument words) makes the code revert. -/
theorem shortRevert (hfork : .berlin ≤ fork) {rest : List U256} (hrest : rest.length ≤ 16)
    (hshort : message.data.size < 68) {gas : Nat} (hg : 60 ≤ gas) {M : ByteArray}
    (hM : M.size = 96) :
    Gas.SpecG fork (At CODE message 9883 rest M gas state substate)
      (Halted true .empty (gas - 60) state substate) := by
  have hz : extendMemory M.size [((0 : U256), (0 : U256))] = ⟨0, 0⟩ := by rw [hM]; decide
  step jumpdestR
  step pushR 1 (0 : U256)
  step dupR 0
  step pushR 1 (0x40 : U256)
  step pushR 1 (0x04 : U256)
  step dupR 1
  step binR 0x01 instruction_add
  step pushR 1 (0 : U256)
  step Gas.calldatasizeG (by code_fact) (by code_fact) (by gas_ok) (by stk_ok)
  step swapR 0
  norm
  step popR
  step binR 0x10 Local.instruction_lt
  step unR 0x15 instruction_iszero
  step unR 0x15 instruction_iszero
  step unR 0x15 instruction_iszero
  step pushR 2 (0x26b6 : U256)
  refine Triple.seq (Gas.jumpi_of_eq_zeroG (by code_fact) (by code_fact) (by gas_ok) ?_) ?_
  · have h68 : (add (0x40 : U256) (0x04 : U256)).toNat = 68 := by decide
    have hlt : lessThan (BitVec.ofNat 256 message.data.size) (add (0x40 : U256) (0x04 : U256)) = 1 := by
      simp only [lessThan, h68, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show message.data.size < 2 ^ 256 by omega)]
      rw [ite_eq_left hshort]
    rw [hlt]
    decide
  step pushR 1 (0 : U256)
  step dupR 0
  refine (Gas.revertG (Nat.le_trans (by decide) hfork) (by code_fact) (by code_fact)
    (by rw [hz]; gas_ok)).consequence (fun _ h => h) ?_
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  refine ⟨hr, he, ?_, ?_, hs, hss⟩
  · rw [ho]; simp [memoryReadBytes]
  · rw [hgas, hz]; gas_ok

end UsdtVerify.Transfer

end

section

/-!
## transfer(address,uint256): the blocks of the success path, from 9883

BasicToken's `transfer(_to, _value)` at 9883 (0x269b), as the bytecode runs it:

- 9883: the payload check `CALLDATASIZE ≥ 0x44` (two argument words) passes, JUMPI to 9910.
- 9910: `fee = mul(_value, basisPointsRate)` (slot 3), `fee = div(fee, 10000)`.
- 9951: `if (fee > maximumFee) fee = maximumFee` (slot 4, read again when the cap applies).
- 9969: `sendAmount = sub(_value, fee)`.
- 9988: `balances[msg.sender] = sub(balances[msg.sender], _value)` (mapping at slot 2).
- 10140: `balances[_to] = add(balances[_to], sendAmount)`, read after the first write.
- 10289: `if (fee > 0)` credit the owner and log (not covered here: the fee is 0).
- 10647: `Transfer(msg.sender, _to, sendAmount)`, LOG3, and back to 5785, then STOP at 1931.
-/

namespace UsdtVerify.TransferOk

open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts
open Transfer SafeMath

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate}

/-- At 9883, call data of at least 68 bytes passes the payload check. -/
theorem payloadOk (hlong : 68 ≤ message.data.size) (hsz : message.data.size < 2 ^ 256)
    {v a : U256} {rest : List U256} (hrest : rest.length ≤ 20) {gas : Nat} (hg : 54 ≤ gas)
    {M : ByteArray} :
    Gas.HoareG fork (At CODE message 9883 (v :: a :: rest) M gas state substate)
      (At CODE message 9910 (0x40 :: 0 :: 0 :: v :: a :: rest) M (gas - 54) state substate) := by
  have hlt : lessThan (BitVec.ofNat 256 message.data.size) (add (0x40 : U256) (0x04 : U256)) =
      0 := by
    have h68 : (add (0x40 : U256) (0x04 : U256)).toNat = 68 := by decide
    simp only [lessThan, h68, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsz]
    rw [ite_eq_right (by omega)]
  step jumpdestR
  step pushR 1 (0 : U256)
  step dupR 0
  step pushR 1 (0x40 : U256)
  step pushR 1 (0x04 : U256)
  step dupR 1
  step binR 0x01 instruction_add
  step pushR 1 (0 : U256)
  step Gas.calldatasizeG (by code_fact) (by code_fact) (by gas_ok) (by stk_ok)
  step swapR 0
  norm
  step popR
  step binR 0x10 Local.instruction_lt
  step unR 0x15 instruction_iszero
  step unR 0x15 instruction_iszero
  step unR 0x15 instruction_iszero
  step pushR 2 (0x26b6 : U256)
  step jumpiR (by rw [hlt]; decide)
  exact (repc (by decide)).seq (Gas.reshapeG rfl rfl (by gas_ok))

/-- At 9910, the code reads `basisPointsRate` (slot 3) and calls `mul(_value, rate)`. -/
theorem feeCall (hfork : .berlin ≤ fork) {v a : U256} {rest : List U256}
    (hrest : rest.length ≤ 20) {c3 : Bool} (hc3 : coldIn substate message.currentTarget 3 = c3)
    {gas : Nat} (hg : 42 + slotCost c3 ≤ gas) {M : ByteArray} :
    Gas.HoareG fork (At CODE message 9910 (0x40 :: 0 :: 0 :: v :: a :: rest) M gas state substate)
      (At CODE message 10755 (storageAt state message.currentTarget 3 :: v :: 0x26d1 :: 0x2710 ::
        0x26df :: 0x40 :: 0 :: 0 :: v :: a :: rest) M (gas - (42 + slotCost c3))
        (readSlot state message.currentTarget 3) (accessSlot substate message.currentTarget 3)) := by
  step jumpdestR
  step pushR 2 (0x26df : U256)
  step pushR 2 (0x2710 : U256)
  step pushR 2 (0x26d1 : U256)
  step pushR 1 (0x03 : U256)
  step Gas.sloadG hfork (cold := c3) (by code_fact) (by code_fact) hc3 (by gas_ok)
  step dupR 7
  step pushR 2 (0x2a03 : U256)
  step swapR 0
  norm
  step swapR 1
  norm
  step swapR 0
  norm
  step pushR 4 (0xffffffff : U256)
  step binR 0x16 Local.instruction_and
  step jumpR
  exact (repc (by decide)).seq (Gas.reshapeG rfl rfl (by gas_ok))

/-- At 9937, back from `mul`, the code calls `div(product, 10000)`. -/
theorem divCall {m r : U256} {rest : List U256} (hrest : rest.length ≤ 20) {gas : Nat}
    (hg : 27 ≤ gas) {M : ByteArray} :
    Gas.HoareG fork (At CODE message 9937 (m :: 0x2710 :: r :: rest) M gas state substate)
      (At CODE message 10949 (0x2710 :: m :: r :: rest) M (gas - 27) state substate) := by
  step jumpdestR
  step pushR 2 (0x2ac5 : U256)
  step swapR 0
  norm
  step swapR 1
  norm
  step swapR 0
  norm
  step pushR 4 (0xffffffff : U256)
  step binR 0x16 Local.instruction_and
  step jumpR
  exact (repc (by decide)).seq (Gas.reshapeG rfl rfl (by gas_ok))

/-- The fee after the cap: `maximumFee` when the raw fee is above it, else the raw fee. -/
abbrev capped (f0 maxFee : U256) : U256 := if f0.toNat > maxFee.toNat then maxFee else f0

/-- The extra gas of the cap: the second read of slot 4 (warm) and four opcodes. -/
abbrev capCost (f0 maxFee : U256) : Nat := if f0.toNat > maxFee.toNat then 108 else 0

/-- At 9951, with the raw fee `f0`, the code caps it by `maximumFee` (slot 4). -/
theorem capBlock (hfork : .berlin ≤ fork) {f0 v a : U256} {rest : List U256}
    (hrest : rest.length ≤ 20) {c4 : Bool} (hc4 : coldIn substate message.currentTarget 4 = c4)
    {gas : Nat}
    (hg : 31 + slotCost c4 + capCost f0 (storageAt state message.currentTarget 4) ≤ gas)
    {M : ByteArray} :
    Gas.HoareG fork (At CODE message 9951 (f0 :: 0x40 :: 0 :: 0 :: v :: a :: rest) M gas state substate)
      (At CODE message 9969
        (0x40 :: 0 :: capped f0 (storageAt state message.currentTarget 4) :: v :: a :: rest) M
        (gas - (31 + slotCost c4 + capCost f0 (storageAt state message.currentTarget 4)))
        (readSlot state message.currentTarget 4) (accessSlot substate message.currentTarget 4)) := by
  step jumpdestR
  step swapR 2
  norm
  step popR
  step pushR 1 (0x04 : U256)
  step Gas.sloadG hfork (cold := c4) (by code_fact) (by code_fact) hc4 (by gas_ok)
  step dupR 3
  step binR 0x11 Local.instruction_gt
  step unR 0x15 instruction_iszero
  step pushR 2 (0x26f1 : U256)
  by_cases hcap : f0.toNat > (storageAt state message.currentTarget 4).toNat
  · simp only [capCost, capped, hcap, ite_true] at hg ⊢
    step jumpi0R (by simp only [greaterThan]; rw [ite_eq_left hcap]; decide)
    step pushR 1 (0x04 : U256)
    step Gas.sloadG hfork (cold := false) (by code_fact) (by code_fact)
      (coldIn_accessSlot_self _ _ _) (by gas_ok)
    step swapR 2
    norm
    step popR
    exact restate (by decide) rfl rfl (by gas_ok) (readSlot_readSlot _ _ _)
      (accessSlot_accessSlot _ _ _)
  · simp only [capCost, capped, hcap, ite_false] at hg ⊢
    step jumpiR (by simp only [greaterThan]; rw [ite_eq_right hcap]; decide)
    exact (repc (by decide)).seq (Gas.reshapeG rfl rfl (by gas_ok))

/-- At 9969, the code calls `sub(_value, fee)`. -/
theorem sendCall {fee v a : U256} {rest : List U256} (hrest : rest.length ≤ 20) {gas : Nat}
    (hg : 36 ≤ gas) {M : ByteArray} :
    Gas.HoareG fork (At CODE message 9969 (0x40 :: 0 :: fee :: v :: a :: rest) M gas state substate)
      (At CODE message 10976 (fee :: v :: 0x2704 :: 0x40 :: 0 :: fee :: v :: a :: rest) M
        (gas - 36) state substate) := by
  step jumpdestR
  step pushR 2 (0x2704 : U256)
  step dupR 3
  step dupR 5
  step pushR 2 (0x2ae0 : U256)
  step swapR 0
  norm
  step swapR 1
  norm
  step swapR 0
  norm
  step pushR 4 (0xffffffff : U256)
  step binR 0x16 Local.instruction_and
  step jumpR
  exact (repc (by decide)).seq (Gas.reshapeG rfl rfl (by gas_ok))

/-- The memory after a lookup in a mapping at base `b` from memory `M`: key word at 0, `b` at 32. -/
abbrev mapMem (M : ByteArray) (k b : U256) : ByteArray :=
  memoryWrite (memoryWrite M 0 (wordBytes k)) 32 (wordBytes b)

theorem size_mapMem {M : ByteArray} (hM : M.size = 96) (k b : U256) : (mapMem M k b).size = 96 := by
  rw [mapMem, size_memoryWrite, size_memoryWrite] <;> simp [size_memoryWrite, hM, size_wordBytes]

theorem ptr_mapMem {M : ByteArray} (hM : M.size = 96)
    (hptr : loadWord (memoryReadBytes M 64 32) 0 32 = 0x60) (k b : U256) :
    loadWord (memoryReadBytes (mapMem M k b) 64 32) 0 32 = 0x60 := by
  rw [mapMem, memoryReadBytes_memoryWrite_of_disjoint,
    memoryReadBytes_memoryWrite_of_disjoint, hptr] <;>
    simp [size_memoryWrite, hM, size_wordBytes]

/-- The key word of a mapping lookup: the word masked twice to 160 bits. -/
abbrev mkey (x : U256) : U256 := bitwiseAnd ADDR_MASK (bitwiseAnd ADDR_MASK x)

/-- The key word of an address argument is the argument: it is already masked. -/
theorem mkey_addrArg (data : ByteArray) (i : Nat) : mkey (addrArg data i) = addrArg data i := by
  simp only [mkey, addrArg, mask_mask]

/-- The positions of the copies of the lookup tail used here: four in `transfer`, four in
`approve`, nine in `transferFrom`, two in the owner's credit of `transfer`. -/
abbrev HASH_PCS : List Nat := [10000, 10078, 10149, 10227, 8250, 8311, 8391, 8452,
  3807, 8654, 8715, 8899, 8960, 9053, 9131, 9202, 9280, 10340, 10451]

/-- The tail of a lookup in a mapping, at its copies in `HASH_PCS`: with the word `x`, 0
and the base `b` on the stack, it masks `x`, writes the key word at 0 and `b` at 32, and hashes
those 64 bytes. -/
theorem hashTail {p : Nat} (hp : p ∈ HASH_PCS) {x base : U256}
    {rest : List U256} (hrest : rest.length ≤ 900) {M : ByteArray} (hM : M.size = 96) {gas : Nat}
    (hg : 84 ≤ gas) :
    Gas.HoareG fork (At CODE message p (x :: 0 :: base :: rest) M gas state substate)
      (At CODE message (p + 58) (mapSlot ((bitwiseAnd ADDR_MASK (bitwiseAnd ADDR_MASK x))) base :: rest) (mapMem M ((bitwiseAnd ADDR_MASK (bitwiseAnd ADDR_MASK x))) base)
        (gas - 84) state substate) := by
  have hs1 : (memoryWrite M 0 (wordBytes ((bitwiseAnd ADDR_MASK (bitwiseAnd ADDR_MASK x))))).size = 96 := by
    rw [size_memoryWrite] <;> simp [hM, size_wordBytes]
  have hext1 : extendMemory M.size [((0 : U256), (32 : U256))] = ⟨0, 0⟩ := by rw [hM]; decide
  have hext2 : extendMemory (memoryWrite M 0 (wordBytes ((bitwiseAnd ADDR_MASK (bitwiseAnd ADDR_MASK x))))).size
      [((0x20 : U256), (32 : U256))] = ⟨0, 0⟩ := by rw [hs1]; decide
  have hext3 : extendMemory (mapMem M ((bitwiseAnd ADDR_MASK (bitwiseAnd ADDR_MASK x))) base).size [((0 : U256), (0x40 : U256))] =
      ⟨0, 0⟩ := by rw [size_mapMem hM]; decide
  have hk : keccak256Cost (0x40 : U256) = 42 := by decide
  have hread : memoryReadBytes (mapMem M ((bitwiseAnd ADDR_MASK (bitwiseAnd ADDR_MASK x))) base) 0 64 =
      wordBytes ((bitwiseAnd ADDR_MASK (bitwiseAnd ADDR_MASK x))) ++ wordBytes base := by
    have h := memoryReadBytes_memoryWrite_memoryWrite (memory := M) (a := wordBytes ((bitwiseAnd ADDR_MASK (bitwiseAnd ADDR_MASK x))))
      (b := wordBytes base) (s := 0) (by simp [hM, size_wordBytes])
    simpa [size_wordBytes, mapMem] using h
  simp only [HASH_PCS, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl
  all_goals
    step pushR 20 ADDR_MASK
    step binR 0x16 Local.instruction_and
    step pushR 20 ADDR_MASK
    step binR 0x16 Local.instruction_and
    step dupR 1
    step Gas.mstoreG (by code_fact) (by code_fact) (by rw [hext1]; gas_ok)
    step Gas.reshapeG (m' := memoryWrite M 0 (wordBytes ((bitwiseAnd ADDR_MASK (bitwiseAnd ADDR_MASK x))))) rfl
      (by rw [hext1, memoryExtend_zero]; rfl) (by rw [hext1] <;> gas_ok)
    step pushR 1 (0x20 : U256)
    step binR 0x01 instruction_add
    step swapR 0
    norm
    step dupR 1
    step Gas.reshapeG (s' := (0x20 : U256) :: base :: 0x20 :: rest) rfl rfl rfl
    step Gas.mstoreG (by code_fact) (by code_fact) (by rw [hext2]; gas_ok)
    step Gas.reshapeG (m' := mapMem M ((bitwiseAnd ADDR_MASK (bitwiseAnd ADDR_MASK x))) base) rfl (by rw [hext2, memoryExtend_zero]; rfl)
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

/-- The slot of `balances[msg.sender]`: mapping base slot 2. -/
abbrev senderSlot (message : Message fork) : U256 := mapSlot (callerKey message) 2

/-- At 9988, the code keeps `sendAmount`, reads `balances[msg.sender]` and calls
`sub(balance, _value)`. -/
theorem debitCall (hfork : .berlin ≤ fork) {send fee v a : U256} {rest : List U256}
    (hrest : rest.length ≤ 800) {cS : Bool}
    (hcS : coldIn substate message.currentTarget (senderSlot message) = cS) {gas : Nat}
    (hg : 130 + slotCost cS ≤ gas) {M : ByteArray} (hM : M.size = 96) :
    Gas.HoareG fork (At CODE message 9988 (send :: 0x40 :: 0 :: fee :: v :: a :: rest) M gas state
        substate)
      (At CODE message 10976 (v :: storageAt state message.currentTarget (senderSlot message) ::
        0x2758 :: 0x40 :: send :: fee :: v :: a :: rest) (mapMem M (callerKey message) 2)
        (gas - (130 + slotCost cS)) (readSlot state message.currentTarget (senderSlot message))
        (accessSlot substate message.currentTarget (senderSlot message))) := by
  step jumpdestR
  step swapR 1
  norm
  step popR
  step pushR 2 (0x2758 : U256)
  step dupR 4
  step pushR 1 (0x02 : U256)
  step pushR 1 (0 : U256)
  step Gas.callerG (by code_fact) (by code_fact) (by gas_ok) (by stk_ok)
  at_pc 10000
  step hashTail (by decide) (by simp; omega) hM (by gas_ok)
  at_pc 10058
  step Gas.sloadG hfork (cold := cS) (by code_fact) (by code_fact) hcS (by gas_ok)
  step pushR 2 (0x2ae0 : U256)
  step swapR 0
  norm
  step swapR 1
  norm
  step swapR 0
  norm
  step pushR 4 (0xffffffff : U256)
  step binR 0x16 Local.instruction_and
  step jumpR
  exact restate (by decide) rfl rfl (by gas_ok) rfl rfl

-- At 10072, from the `JUMPDEST` to the `SSTORE` of `balances[msg.sender]`.
set_option hygiene false in
macro "debit_pre" : tactic => `(tactic| (
  step jumpdestR
  step pushR 1 (0x02 : U256)
  step pushR 1 (0 : U256)
  step Gas.callerG (by code_fact) (by code_fact) (by gas_ok) (by stk_ok)
  at_pc 10078
  step hashTail (by decide) (by simp; omega) hM (by gas_ok)
  at_pc 10136
  step dupR 1
  step swapR 0
  norm))

/-- At 10072, the code writes the new balance of the sender to `balances[msg.sender]`. -/
theorem debitStore (hfork : .berlin ≤ fork) {nb send fee v a : U256}
    {rest : List U256} (hrest : rest.length ≤ 800) (hstatic : message.isStatic = false)
    (hacc : hasAccount state message.currentTarget) {cS : Bool}
    (hcS : coldIn substate message.currentTarget (senderSlot message) = cS) {gas : Nat}
    (hstip : 2400 ≤ gas)
    (hg : 101 + Gas.writeCost fork (originalAt state message.currentTarget (senderSlot message))
      (storageAt state message.currentTarget (senderSlot message)) nb cS ≤ gas)
    {M : ByteArray} (hM : M.size = 96) :
    Gas.HoareG fork (At CODE message 10072 (nb :: 0x40 :: send :: fee :: v :: a :: rest) M gas state
        substate)
      (At CODE message 10140 (0x40 :: send :: fee :: v :: a :: rest)
        (mapMem M (callerKey message) 2)
        (gas - (101 + Gas.writeCost fork (originalAt state message.currentTarget (senderSlot message))
          (storageAt state message.currentTarget (senderSlot message)) nb cS))
        (writeSlot state message.currentTarget (senderSlot message) nb)
        (storeSub fork substate message.currentTarget (senderSlot message)
          (originalAt state message.currentTarget (senderSlot message))
          (storageAt state message.currentTarget (senderSlot message)) nb)) := by
  simp only [senderSlot, callerKey] at hcS hg ⊢
  debit_pre
  step Gas.sstoreWG hfork (by code_fact) (by code_fact) hstatic hacc hcS (by gas_ok) (by gas_ok)
  step popR
  exact restate (by decide) rfl rfl (by gas_ok) rfl rfl

/-- At 10072, when the `SSTORE` of `balances[msg.sender]` cannot complete (`NoWrite`: a static
frame, no account for `C`, or at most 2300 gas left there): the run reaches it, and it is
`Stuck`. -/
theorem debitStoreBad {nb send fee v a : U256} {rest : List U256} (hrest : rest.length ≤ 800)
    {gas : Nat}
    (hbad : Gas.NoWrite message state (gas - 99))
    (hg : 99 ≤ gas) {M : ByteArray} (hM : M.size = 96) :
    Gas.HoareG fork (At CODE message 10072 (nb :: 0x40 :: send :: fee :: v :: a :: rest) M gas state
        substate) Gas.Stuck := by
  debit_pre
  exact Gas.sstoreNoWrite (by code_fact) (by code_fact) (hbad.le (by gas_ok))

/-- The slot of `balances[_to]` for the recipient word `a`: mapping base slot 2. -/
abbrev recipientSlot (a : U256) : U256 := mapSlot (mkey a) 2

/-- At 10140, the code reads `balances[_to]` and calls `add(balance, sendAmount)`. -/
theorem creditCall (hfork : .berlin ≤ fork) {send fee v a : U256} {rest : List U256}
    (hrest : rest.length ≤ 800) {cT : Bool}
    (hcT : coldIn substate message.currentTarget (recipientSlot a) = cT) {gas : Nat}
    (hg : 125 + slotCost cT ≤ gas) {M : ByteArray} (hM : M.size = 96) :
    Gas.HoareG fork (At CODE message 10140 (0x40 :: send :: fee :: v :: a :: rest) M gas state
        substate)
      (At CODE message 11001 (send :: storageAt state message.currentTarget (recipientSlot a) ::
        0x27ed :: 0x40 :: send :: fee :: v :: a :: rest) (mapMem M (mkey a) 2)
        (gas - (125 + slotCost cT)) (readSlot state message.currentTarget (recipientSlot a))
        (accessSlot substate message.currentTarget (recipientSlot a))) := by
  step pushR 2 (0x27ed : U256)
  step dupR 2
  step pushR 1 (0x02 : U256)
  step pushR 1 (0 : U256)
  step dupR 8
  at_pc 10149
  step hashTail (by decide) (by simp; omega) hM (by gas_ok)
  at_pc 10207
  step Gas.sloadG hfork (cold := cT) (by code_fact) (by code_fact) hcT (by gas_ok)
  step pushR 2 (0x2af9 : U256)
  step swapR 0
  norm
  step swapR 1
  norm
  step swapR 0
  norm
  step pushR 4 (0xffffffff : U256)
  step binR 0x16 Local.instruction_and
  step jumpR
  exact restate (by decide) rfl rfl (by gas_ok) rfl rfl

/-- At 10221, the code writes the new balance of the recipient to `balances[_to]`; with a fee of
0 it skips the owner's credit and goes to the log at 10647. -/
theorem creditStore (hfork : .berlin ≤ fork) {nt send v a : U256}
    {rest : List U256} (hrest : rest.length ≤ 800) (hstatic : message.isStatic = false)
    (hacc : hasAccount state message.currentTarget) {cT : Bool}
    (hcT : coldIn substate message.currentTarget (recipientSlot a) = cT) {gas : Nat}
    (hstip : 2401 ≤ gas)
    (hg : 127 + Gas.writeCost fork (originalAt state message.currentTarget (recipientSlot a))
      (storageAt state message.currentTarget (recipientSlot a)) nt cT ≤ gas)
    {M : ByteArray} (hM : M.size = 96) :
    Gas.HoareG fork (At CODE message 10221 (nt :: 0x40 :: send :: 0 :: v :: a :: rest) M gas state
        substate)
      (At CODE message 10647 (0x40 :: send :: 0 :: v :: a :: rest) (mapMem M (mkey a) 2)
        (gas - (127 + Gas.writeCost fork (originalAt state message.currentTarget (recipientSlot a))
          (storageAt state message.currentTarget (recipientSlot a)) nt cT))
        (writeSlot state message.currentTarget (recipientSlot a) nt)
        (storeSub fork substate message.currentTarget (recipientSlot a)
          (originalAt state message.currentTarget (recipientSlot a))
          (storageAt state message.currentTarget (recipientSlot a)) nt)) := by
  simp only [recipientSlot, mkey] at hcT hg ⊢
  step jumpdestR
  step pushR 1 (0x02 : U256)
  step pushR 1 (0 : U256)
  step dupR 7
  at_pc 10227
  step hashTail (by decide) (by simp; omega) hM (by gas_ok)
  at_pc 10285
  step dupR 1
  step swapR 0
  norm
  step Gas.sstoreWG hfork (by code_fact) (by code_fact) hstatic hacc hcT (by gas_ok) (by gas_ok)
  step popR
  step pushR 1 (0 : U256)
  step dupR 3
  step binR 0x11 Local.instruction_gt
  step unR 0x15 instruction_iszero
  step pushR 2 (0x2997 : U256)
  step jumpiR (by decide)
  exact restate (by decide) rfl rfl (by gas_ok) rfl rfl

/-- At 10221 (fee of 0), when the `SSTORE` of `balances[_to]` cannot complete (`NoWrite`): the run
reaches it, and it is `Stuck`. -/
theorem creditStoreBad {nt send v a : U256} {rest : List U256} (hrest : rest.length ≤ 800)
    {gas : Nat} (hbad : Gas.NoWrite message state (gas - 100)) (hg : 100 ≤ gas) {M : ByteArray}
    (hM : M.size = 96) :
    Gas.HoareG fork (At CODE message 10221 (nt :: 0x40 :: send :: 0 :: v :: a :: rest) M gas state
        substate) Gas.Stuck := by
  step jumpdestR
  step pushR 1 (0x02 : U256)
  step pushR 1 (0 : U256)
  step dupR 7
  at_pc 10227
  step hashTail (by decide) (by simp; omega) hM (by gas_ok)
  at_pc 10285
  step dupR 1
  step swapR 0
  norm
  exact Gas.sstoreNoWrite (by code_fact) (by code_fact) (hbad.le (by gas_ok))

/-- The topic of the event `Transfer(address,address,uint256)`. -/
abbrev TRANSFER_TOPIC : U256 :=
  0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef

/-- The log of `Transfer(from, to, value)` by the contract `c`: three topics and one data word. -/
abbrev transferLog (c : EthLib.Base.Address) (src dst value : U256) : Blocks.Log :=
  { address := c
    topics := [TRANSFER_TOPIC, src, dst].map U256.toBeBytes
    data := wordBytes value }

/-- At 10647, the code logs `Transfer(msg.sender, _to, sendAmount)` and returns to 5785. -/
theorem logBlock {send fee v a : U256} {rest : List U256} (hrest : rest.length ≤ 900)
    (hstatic : message.isStatic = false) {gas : Nat} (hg : 1850 ≤ gas) {M : ByteArray}
    (hM : M.size = 96) (hptr : loadWord (memoryReadBytes M 64 32) 0 32 = 0x60) :
    Gas.HoareG fork (At CODE message 10647 (0x40 :: send :: fee :: v :: a :: 0x1699 :: rest) M gas
        state substate)
      (At CODE message 5785 rest (M ++ wordBytes send) (gas - 1850) state
        { substate with logs := substate.logs.push (transferLog message.currentTarget
          (bitwiseAnd ADDR_MASK message.caller.toU256) (bitwiseAnd ADDR_MASK a) send) }) := by
  have hext0 : extendMemory M.size [((0x40 : U256), (32 : U256))] = ⟨0, 0⟩ := by
    rw [hM]; decide
  have hext1 : extendMemory M.size [((0x60 : U256), (32 : U256))] = ⟨3, 32⟩ := by
    rw [hM]; decide
  have hsz : (M ++ wordBytes send).size = 128 := by
    rw [ByteArray.size_append, hM, size_wordBytes]
  have hext2 : extendMemory (M ++ wordBytes send).size [((0x40 : U256), (32 : U256))] =
      ⟨0, 0⟩ := by rw [hsz]; decide
  have hext3 : extendMemory (M ++ wordBytes send).size [((0x60 : U256), (0x20 : U256))] =
      ⟨0, 0⟩ := by rw [hsz]; decide
  have hmem1 : memoryWrite (memoryExtend M 32) (0x60 : U256).toNat (wordBytes send) =
      M ++ wordBytes send := by
    have h := memoryWrite_extend_end (memory := M) (value := wordBytes send)
    rwa [size_wordBytes, hM] at h
  have hread2 : memoryReadBytes (M ++ wordBytes send) 64 32 = memoryReadBytes M 64 32 := by
    simp only [memoryReadBytes, ByteArray.extract_append, hM]
    simp
  have hlog : logCost (3 : Fin 5).val (0x20 : U256) = 1756 := by decide
  step jumpdestR
  step dupR 4
  step pushR 20 ADDR_MASK
  step binR 0x16 Local.instruction_and
  step Gas.callerG (by code_fact) (by code_fact) (by gas_ok) (by stk_ok)
  step pushR 20 ADDR_MASK
  step binR 0x16 Local.instruction_and
  step pushR 32 TRANSFER_TOPIC
  step dupR 4
  step pushR 1 (0x40 : U256)
  step Gas.mloadG (by code_fact) (by code_fact) (by rw [hext0]; gas_ok)
  step Gas.reshapeG (s' := 0x60 :: send :: TRANSFER_TOPIC :: bitwiseAnd ADDR_MASK message.caller.toU256 ::
      bitwiseAnd ADDR_MASK a :: 0x40 :: send :: fee :: v :: a :: 0x1699 :: rest) (m' := M)
    (by rw [hext0, memoryExtend_zero]; exact congrArg (· :: _) hptr)
    (by rw [hext0, memoryExtend_zero]) (by rw [hext0])
  step dupR 0
  step dupR 2
  step dupR 1
  step Gas.mstoreG (by code_fact) (by code_fact) (by rw [hext1]; gas_ok)
  step Gas.reshapeG (m' := M ++ wordBytes send) rfl (by rw [hext1]; exact hmem1) (by rw [hext1])
  step pushR 1 (0x20 : U256)
  step binR 0x01 instruction_add
  step swapR 1
  norm
  step popR
  step popR
  step pushR 1 (0x40 : U256)
  step Gas.mloadG (by code_fact) (by code_fact) (by rw [hext2]; gas_ok)
  step Gas.reshapeG (s' := 0x60 :: 0x80 :: TRANSFER_TOPIC :: bitwiseAnd ADDR_MASK message.caller.toU256 ::
      bitwiseAnd ADDR_MASK a :: 0x40 :: send :: fee :: v :: a :: 0x1699 :: rest)
    (m' := M ++ wordBytes send)
    (by rw [hext2, memoryExtend_zero, show (0x40 : U256).toNat = 64 from rfl, hread2, hptr]; rfl)
    (by rw [hext2, memoryExtend_zero]) (by rw [hext2])
  step dupR 0
  step swapR 1
  norm
  step binR 0x03 instruction_sub
  step swapR 0
  norm
  step Gas.reshapeG (s' := 0x60 :: 0x20 :: ([TRANSFER_TOPIC, bitwiseAnd ADDR_MASK message.caller.toU256,
      bitwiseAnd ADDR_MASK a] ++ (0x40 :: send :: fee :: v :: a :: 0x1699 :: rest))) rfl rfl rfl
  step Gas.logG (n := 3) (byte := 0xa3) rfl (by code_fact) (by code_fact) rfl hstatic
    (by rw [hlog, hext3]; gas_ok)
  step Gas.reshapeG rfl (by rw [hext3, memoryExtend_zero]) (by rw [hlog, hext3])
  step popR
  step popR
  step popR
  step popR
  step popR
  step jumpR
  refine restate (by decide) rfl rfl (by gas_ok) rfl ?_
  rw [hext3, memoryExtend_zero, show (0x60 : U256).toNat = 96 from rfl,
    show (0x20 : U256).toNat = 32 from rfl, read_after hM _ (size_wordBytes send)]

/-- At 5785, the code returns to 1930, where it stops. -/
theorem endBlock {w a sel : U256} {gas : Nat} (hg : 15 ≤ gas) {M : ByteArray} :
    Gas.SpecG fork (At CODE message 5785 [w, a, 0x078a, sel] M gas state substate)
      (Halted false .empty (gas - 15) state substate) := by
  step jumpdestR
  step jumpdestR
  step popR
  step popR
  step jumpR
  step repc (pc' := 1930) (by decide)
  step jumpdestR
  refine (Gas.stopG (by code_fact) (by code_fact)).consequence (fun _ h => h) ?_
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  exact ⟨hr, he, ho, by rw [hgas]; gas_ok, hs, hss⟩

end UsdtVerify.TransferOk

end

section

/-!
## transfer(address,uint256): the success path from 9883, with a fee of 0

`body` composes the blocks of `TransferOk` from BasicToken's `transfer` at 9883 to the STOP at
1931, for a call whose fee, as the bytecode computes it, is 0.

The states and substates along the path are named below; the recipient's balance is read in the
state after the sender's write (`debited`), as the bytecode reads it.
-/

namespace UsdtVerify.TransferOk

open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts
open Transfer SafeMath

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate}

/-- The raw fee of `_value = v`: `mul(v, basisPointsRate) / 10000` (slot 3). -/
abbrev rawFee (state : State.TransactionState) (message : Message fork) (v : U256) : U256 :=
  div (mul v (storageAt state message.currentTarget 3)) 0x2710

/-- The fee of `_value = v`, as the bytecode computes it: the raw fee, capped by `maximumFee`
(slot 4). -/
abbrev feeOf (state : State.TransactionState) (message : Message fork) (v : U256) : U256 :=
  capped (rawFee state message v) (storageAt state message.currentTarget 4)

/-- The state after the reads of slots 3, 4 and `balances[msg.sender]`. -/
abbrev reads3 (state : State.TransactionState) (message : Message fork) :
    State.TransactionState :=
  readSlot (readSlot (readSlot state message.currentTarget 3) message.currentTarget 4)
    message.currentTarget (senderSlot message)

/-- The substate after the accesses of slots 3, 4 and `balances[msg.sender]`. -/
abbrev access3 (substate : Substate) (message : Message fork) : Substate :=
  accessSlot (accessSlot (accessSlot substate message.currentTarget 3) message.currentTarget 4)
    message.currentTarget (senderSlot message)

/-- The sender's balance before the call. -/
abbrev balS (state : State.TransactionState) (message : Message fork) : U256 :=
  storageAt state message.currentTarget (senderSlot message)

/-- The state after the sender's write: `balances[msg.sender] = balS - v`. -/
abbrev debited (state : State.TransactionState) (message : Message fork) (v : U256) :
    State.TransactionState :=
  writeSlot (reads3 state message) message.currentTarget (senderSlot message)
    (sub (balS state message) v)

/-- The substate after the sender's write. -/
abbrev debitedSub (fork : Fork) (substate : Substate) (state : State.TransactionState)
    (message : Message fork) (v : U256) : Substate :=
  storeSub fork (access3 substate message) message.currentTarget (senderSlot message)
    (originalAt state message.currentTarget (senderSlot message)) (balS state message)
    (sub (balS state message) v)

/-- The recipient's balance, read after the sender's write. -/
abbrev balT (state : State.TransactionState) (message : Message fork) (v a : U256) : U256 :=
  storageAt (debited state message v) message.currentTarget (recipientSlot a)

/-- The state after the recipient's write: `balances[_to] = balT + v`. -/
abbrev credited (state : State.TransactionState) (message : Message fork) (v a : U256) :
    State.TransactionState :=
  writeSlot (readSlot (debited state message v) message.currentTarget (recipientSlot a))
    message.currentTarget (recipientSlot a) (add (balT state message v a) v)

/-- The substate after the recipient's write and the Transfer log. -/
abbrev creditedSub (fork : Fork) (substate : Substate) (state : State.TransactionState)
    (message : Message fork) (v a : U256) : Substate :=
  storeSub fork (accessSlot (debitedSub fork substate state message v) message.currentTarget
      (recipientSlot a)) message.currentTarget (recipientSlot a)
    (originalAt state message.currentTarget (recipientSlot a)) (balT state message v a)
    (add (balT state message v a) v)

/-- The substate at the end: the Transfer log appended. -/
abbrev loggedSub (fork : Fork) (substate : Substate) (state : State.TransactionState)
    (message : Message fork) (v a : U256) : Substate :=
  { creditedSub fork substate state message v a with
    logs := (creditedSub fork substate state message v a).logs.push
      (transferLog message.currentTarget (bitwiseAnd ADDR_MASK message.caller.toU256)
        (bitwiseAnd ADDR_MASK a) v) }

/-- The price of the sender's write (the slot is warm: the code has just read it). -/
abbrev debitCost (fork : Fork) (state : State.TransactionState) (message : Message fork)
    (v : U256) : Nat :=
  Gas.writeCost fork (originalAt state message.currentTarget (senderSlot message))
    (balS state message) (sub (balS state message) v) false

/-- The price of the recipient's write (warm too). -/
abbrev creditCost (fork : Fork) (state : State.TransactionState) (message : Message fork)
    (v a : U256) : Nat :=
  Gas.writeCost fork (originalAt state message.currentTarget (recipientSlot a))
    (balT state message v a) (add (balT state message v a) v) false

/-- The coldness accessed by the reads: `c3`, `c4`, the sender's slot `cS`, the recipient's `cT`. -/
abbrev readCost (c3 c4 cS cT : Bool) : Nat :=
  slotCost c3 + slotCost c4 + slotCost cS + slotCost cT

theorem coldIn_storeSub {fork : Fork} {ss : Substate} {target : EthLib.Base.Address}
    {n m o c w : U256} :
    coldIn (storeSub fork (accessSlot ss target n) target n o c w) target m =
      coldIn (accessSlot ss target n) target m := by
  show coldIn (accessSlot (accessSlot ss target n) target n) target m = _
  rw [accessSlot_accessSlot]

/-- From 9883, with a fee of 0, the success path of `transfer` up to the STOP at 1931. -/
theorem body (hfork : .berlin ≤ fork)
    (hlong : 68 ≤ message.data.size) (hsz : message.data.size < 2 ^ 256)
    (hstatic : message.isStatic = false) (hacc : hasAccount state message.currentTarget)
    {v a sel : U256} {M : ByteArray} (hM : M.size = 96)
    (hptr : loadWord (memoryReadBytes M 64 32) 0 32 = 0x60)
    (hov : v.toNat * (storageAt state message.currentTarget 3).toNat < 2 ^ 256)
    (hfee : feeOf state message v = 0)
    (hbal : v.toNat ≤ (balS state message).toNat)
    (hto : (balT state message v a).toNat + v.toNat < 2 ^ 256)
    {c3 c4 cS cT : Bool} (hc3 : coldIn substate message.currentTarget 3 = c3)
    (hc4 : coldIn (accessSlot substate message.currentTarget 3) message.currentTarget 4 = c4)
    (hcS : coldIn (accessSlot (accessSlot substate message.currentTarget 3) message.currentTarget 4)
      message.currentTarget (senderSlot message) = cS)
    (hcT : coldIn (access3 substate message) message.currentTarget (recipientSlot a) = cT)
    {gas : Nat}
    (hstip1 : 530 + slotCost c3 + slotCost c4 + slotCost cS + mulCost v +
      capCost (rawFee state message v) (storageAt state message.currentTarget 4) + 2400 ≤ gas)
    (hstip2 : 837 + readCost c3 c4 cS cT + mulCost v +
      capCost (rawFee state message v) (storageAt state message.currentTarget 4) +
      debitCost fork state message v + 2401 ≤ gas)
    (hg : 2829 + readCost c3 c4 cS cT + mulCost v +
      capCost (rawFee state message v) (storageAt state message.currentTarget 4) +
      debitCost fork state message v + creditCost fork state message v a ≤ gas) :
    Gas.SpecG fork (At CODE message 9883 [v, a, 0x1699, v, a, 0x078a, sel] M gas state substate)
      (Halted false .empty (gas - (2829 + readCost c3 c4 cS cT + mulCost v +
        capCost (rawFee state message v) (storageAt state message.currentTarget 4) +
        debitCost fork state message v + creditCost fork state message v a))
        (credited state message v a) (loggedSub fork substate state message v a)) := by
  simp only [readCost, debitCost, creditCost, rawFee, feeOf, balS, balT, debited, reads3] at hstip1 hstip2 hg hfee hbal hto ⊢
  have hacc3 : hasAccount (reads3 state message) message.currentTarget :=
    hasAccount_readSlot (hasAccount_readSlot (hasAccount_readSlot hacc))
  have hacc4 : hasAccount (readSlot (debited state message v) message.currentTarget
      (recipientSlot a)) message.currentTarget :=
    hasAccount_readSlot (hasAccount_writeSlot hacc3)
  simp only [debited, reads3, balS] at hacc3 hacc4
  step payloadOk hlong hsz (by simp) (by gas_ok)
  step feeCall hfork (by simp) hc3 (by gas_ok)
  step mulBlock (by simp) (by valid_dest) hov (by gas_ok)
  at_pc 9937
  step divCall (by simp) (by gas_ok)
  step divBlock (by simp) (by valid_dest) (by decide) (by gas_ok)
  at_pc 9951
  step capBlock hfork (by simp) hc4 (by simp only [storageAt_readSlot]; gas_ok)
  simp only [storageAt_readSlot]
  step Gas.reshapeG (s' := (0x40 : U256) :: 0 :: 0 :: v :: a :: [0x1699, v, a, 0x078a, sel])
    (by rw [hfee]) rfl rfl
  step sendCall (by simp) (by gas_ok)
  step subBlock (by simp) (by valid_dest) (by simp) (by gas_ok)
  at_pc 9988
  step Gas.reshapeG (s' := v :: (0x40 : U256) :: 0 :: 0 :: v :: a :: [0x1699, v, a, 0x078a, sel])
    (by simp [sub]) rfl rfl
  step debitCall hfork (by simp) hcS (by gas_ok) hM
  simp only [storageAt_readSlot]
  step subBlock (by simp) (by valid_dest) hbal (by gas_ok)
  at_pc 10072
  step debitStore hfork (by simp) hstatic hacc3 (coldIn_accessSlot_self _ _ _) (by gas_ok)
    (by simp only [storageAt_readSlot, originalAt_readSlot]; gas_ok) (size_mapMem hM _ _)
  simp only [storageAt_readSlot, originalAt_readSlot]
  step creditCall hfork (by simp) (cT := cT) (by rw [coldIn_storeSub]; exact hcT) (by gas_ok)
    (size_mapMem (size_mapMem hM _ _) _ _)
  step addBlock (by simp) (by valid_dest) hto (by gas_ok)
  at_pc 10221
  step creditStore hfork (by simp) hstatic hacc4 (coldIn_accessSlot_self _ _ _) (by gas_ok)
    (by simp only [storageAt_readSlot, originalAt_readSlot, originalAt_writeSlot hacc3]; gas_ok)
    (size_mapMem (size_mapMem (size_mapMem hM _ _) _ _) _ _)
  simp only [storageAt_readSlot, originalAt_readSlot, originalAt_writeSlot hacc3]
  step logBlock (by simp) hstatic (by gas_ok)
    (size_mapMem (size_mapMem (size_mapMem (size_mapMem hM _ _) _ _) _ _) _ _)
    (ptr_mapMem (size_mapMem (size_mapMem (size_mapMem hM _ _) _ _) _ _)
      (ptr_mapMem (size_mapMem (size_mapMem hM _ _) _ _)
        (ptr_mapMem (size_mapMem hM _ _) (ptr_mapMem hM hptr _ _) _ _) _ _) _ _)
  refine (endBlock (by gas_ok)).consequence (fun _ h => h) ?_
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  exact ⟨hr, he, ho, by rw [hgas]; gas_ok, hs, hss⟩

/-- From 9883, with a fee of 0, a frame that may write and an account for `C`, with more than
2300 gas left at the `SSTORE` of the sender's balance but at most 2300 at the `SSTORE` of the
recipient's balance (`hlow`): the run reaches the second one, which is `Stuck`. -/
theorem bodyLow2 (hfork : .berlin ≤ fork)
    (hlong : 68 ≤ message.data.size) (hsz : message.data.size < 2 ^ 256)
    (hstatic : message.isStatic = false) (hacc : hasAccount state message.currentTarget)
    {v a sel : U256} {M : ByteArray} (hM : M.size = 96)
    (hov : v.toNat * (storageAt state message.currentTarget 3).toNat < 2 ^ 256)
    (hfee : feeOf state message v = 0)
    (hbal : v.toNat ≤ (balS state message).toNat)
    (hto : (balT state message v a).toNat + v.toNat < 2 ^ 256)
    {c3 c4 cS cT : Bool} (hc3 : coldIn substate message.currentTarget 3 = c3)
    (hc4 : coldIn (accessSlot substate message.currentTarget 3) message.currentTarget 4 = c4)
    (hcS : coldIn (accessSlot (accessSlot substate message.currentTarget 3) message.currentTarget 4)
      message.currentTarget (senderSlot message) = cS)
    (hcT : coldIn (access3 substate message) message.currentTarget (recipientSlot a) = cT)
    {gas : Nat}
    (hstip1 : 530 + slotCost c3 + slotCost c4 + slotCost cS + mulCost v +
      capCost (rawFee state message v) (storageAt state message.currentTarget 4) + 2400 ≤ gas)
    (hg : 937 + readCost c3 c4 cS cT + mulCost v +
      capCost (rawFee state message v) (storageAt state message.currentTarget 4) +
      debitCost fork state message v ≤ gas)
    (hlow : gas < 837 + readCost c3 c4 cS cT + mulCost v +
      capCost (rawFee state message v) (storageAt state message.currentTarget 4) +
      debitCost fork state message v + 2401) :
    Gas.HoareG fork (At CODE message 9883 [v, a, 0x1699, v, a, 0x078a, sel] M gas state substate)
      Gas.Stuck := by
  simp only [readCost, debitCost, rawFee, feeOf, balS, balT, debited, reads3] at hstip1 hg hlow hfee hbal hto ⊢
  have hacc3 : hasAccount (reads3 state message) message.currentTarget :=
    hasAccount_readSlot (hasAccount_readSlot (hasAccount_readSlot hacc))
  simp only [reads3] at hacc3
  step payloadOk hlong hsz (by simp) (by gas_ok)
  step feeCall hfork (by simp) hc3 (by gas_ok)
  step mulBlock (by simp) (by valid_dest) hov (by gas_ok)
  at_pc 9937
  step divCall (by simp) (by gas_ok)
  step divBlock (by simp) (by valid_dest) (by decide) (by gas_ok)
  at_pc 9951
  step capBlock hfork (by simp) hc4 (by simp only [storageAt_readSlot]; gas_ok)
  simp only [storageAt_readSlot]
  step Gas.reshapeG (s' := (0x40 : U256) :: 0 :: 0 :: v :: a :: [0x1699, v, a, 0x078a, sel])
    (by rw [hfee]) rfl rfl
  step sendCall (by simp) (by gas_ok)
  step subBlock (by simp) (by valid_dest) (by simp) (by gas_ok)
  at_pc 9988
  step Gas.reshapeG (s' := v :: (0x40 : U256) :: 0 :: 0 :: v :: a :: [0x1699, v, a, 0x078a, sel])
    (by simp [sub]) rfl rfl
  step debitCall hfork (by simp) hcS (by gas_ok) hM
  simp only [storageAt_readSlot]
  step subBlock (by simp) (by valid_dest) hbal (by gas_ok)
  at_pc 10072
  step debitStore hfork (by simp) hstatic hacc3 (coldIn_accessSlot_self _ _ _) (by gas_ok)
    (by simp only [storageAt_readSlot, originalAt_readSlot]; gas_ok) (size_mapMem hM _ _)
  simp only [storageAt_readSlot, originalAt_readSlot]
  step creditCall hfork (by simp) (cT := cT) (by rw [coldIn_storeSub]; exact hcT) (by gas_ok)
    (size_mapMem (size_mapMem hM _ _) _ _)
  step addBlock (by simp) (by valid_dest) hto (by gas_ok)
  at_pc 10221
  refine creditStoreBad (by simp) (.of_low hfork ?_) ?_
    (size_mapMem (size_mapMem (size_mapMem hM _ _) _ _) _ _)
  · gas_ok
  · gas_ok

end UsdtVerify.TransferOk

end
