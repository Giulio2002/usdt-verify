import UsdtVerify.Functions.Common

/-!
# transfer(address,uint256)

- At 1866, the entry checks that the call has no value, reads argument word 0 masked to 160 bits
  (the recipient) and argument word 1 (the amount), and jumps to 5364 with return address 1930.
- At 5364, the code reads slot 0 and tests byte 20 (the `paused` flag); when it is set, it reverts.

Proved here: the revert when paused.
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
    Hoare fork (At CODE message 1866 [x] MEM0 gas state substate)
      (At CODE message 5364 [wordArg message.data 1, addrArg message.data 0, 0x078a, x] MEM0
        (gas - 98) state substate) := by
  step jumpdestR
  step Logic.callvalue (by code_fact) (by code_fact) (by gas_ok) (by stk_ok)
  step unR 0x15 instruction_iszero
  step pushR 2 (0x0755 : U256)
  step jumpiR (by simp [hv, isZero])
  step jumpdestR
  step pushR 2 (0x078a : U256)
  step pushR 1 (0x04 : U256)
  step dupR 0
  step dupR 0
  step calldataload (by code_fact) (by code_fact) (by gas_ok)
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
  step calldataload (by code_fact) (by code_fact) (by gas_ok)
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
  exact (repc (by decide)).seq (reshape rfl rfl (by gas_ok))

/-- At 5364, when byte 20 of slot 0 is set, the code reverts with no output. -/
theorem pausedRevert (hfork : .berlin ≤ fork) {rest : List U256} (hrest : rest.length ≤ 16)
    {c0 : Bool} (hpaused : byte20 (storageAt state message.currentTarget 0) ≠ 0)
    (hc0 : coldIn substate message.currentTarget 0 = c0) {gas : Nat}
    (hg : 118 + slotCost c0 ≤ gas) :
    Spec fork (At CODE message 5364 rest MEM0 gas state substate)
      (Halted true .empty (gas - (118 + slotCost c0)) (readSlot state message.currentTarget 0)
        (accessSlot substate message.currentTarget 0)) := by
  have hexp : exponentBytes (0x14 : U256) = 1 := by decide
  step jumpdestR
  step pushR 1 (0 : U256)
  step pushR 1 (0x14 : U256)
  step swapR 0
  norm
  step sload hfork (cold := c0) (by code_fact) (by code_fact) hc0 (by gas_ok)
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
  step unR 0x15 instruction_iszero
  step unR 0x15 instruction_iszero
  step pushR 2 (0x1510 : U256)
  step jumpi0R (isZero3_flag hpaused)
  step pushR 1 (0 : U256)
  step dupR 0
  have hz : extendMemory MEM0.size [((0 : U256), (0 : U256))] = ⟨0, 0⟩ := by
    rw [size_MEM0]; decide
  refine (Logic.revert (Nat.le_trans (by decide) hfork) (by code_fact) (by code_fact)
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
    Hoare fork (At CODE message 5364 rest M gas state substate)
      (At CODE message 5392 rest M (gas - (112 + slotCost c0)) (readSlot state message.currentTarget 0)
        (accessSlot substate message.currentTarget 0)) := by
  have hexp : exponentBytes (0x14 : U256) = 1 := by decide
  step jumpdestR
  step pushR 1 (0 : U256)
  step pushR 1 (0x14 : U256)
  step swapR 0
  norm
  step sload hfork (cold := c0) (by code_fact) (by code_fact) hc0 (by gas_ok)
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
  step unR 0x15 instruction_iszero
  step unR 0x15 instruction_iszero
  step pushR 2 (0x1510 : U256)
  step jumpiR (isZero3_flag_ne hnp)
  exact (repc (by decide)).seq (reshape rfl rfl (by gas_ok))

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
  rw [if_neg hne]
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
    Hoare fork (At CODE message 5392 rest MEM0 gas state substate)
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
  step caller (by code_fact) (by code_fact) (by gas_ok) (by stk_ok)
  step pushR 20 ADDR_MASK
  step binR 0x16 Local.instruction_and
  step pushR 20 ADDR_MASK
  step binR 0x16 Local.instruction_and
  step dupR 1
  step mstore (by code_fact) (by code_fact) (by rw [hext1]; gas_ok)
  step reshape (m' := memoryWrite MEM0 0 (wordBytes (callerKey message))) rfl
    (by rw [hext1, memoryExtend_zero]; rfl) (by rw [hext1] <;> gas_ok)
  step pushR 1 (0x20 : U256)
  step binR 0x01 instruction_add
  step swapR 0
  norm
  step dupR 1
  step reshape (s' := (0x20 : U256) :: 6 :: 0x20 :: rest) rfl rfl rfl
  step mstore (by code_fact) (by code_fact) (by rw [hext2]; gas_ok)
  step reshape (m' := MEMK (callerKey message) 6) rfl (by rw [hext2, memoryExtend_zero]; rfl)
    (by rw [hext2] <;> gas_ok)
  step pushR 1 (0x20 : U256)
  step binR 0x01 instruction_add
  step pushR 1 (0 : U256)
  step reshape (s' := (0 : U256) :: 0x40 :: rest) rfl rfl rfl
  step keccak256 (by code_fact) (by code_fact) (by rw [hk, hext3]; gas_ok)
  step reshape (s' := blackSlot message :: rest) (m' := MEMK (callerKey message) 6)
    (by rw [hext3, memoryExtend_zero, show (0 : U256).toNat = 0 from rfl,
      show (0x40 : U256).toNat = 64 from rfl, hread]; rfl)
    (by rw [hext3, memoryExtend_zero]) (by rw [hext3, hk] <;> gas_ok)
  step pushR 1 (0 : U256)
  step swapR 0
  norm
  step sload hfork (cold := cB) (by code_fact) (by code_fact) hcB (by gas_ok)
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
  step unR 0x15 instruction_iszero
  step unR 0x15 instruction_iszero
  step pushR 2 (0x1569 : U256)
  exact (repc (by decide)).seq (reshape rfl rfl (by gas_ok))

/-- At 5392, when the low byte of `isBlackListed[caller]` is set, the code reverts. -/
theorem blackRevert (hfork : .berlin ≤ fork) {rest : List U256} (hrest : rest.length ≤ 16)
    {cB : Bool} (hblack : (storageAt state message.currentTarget (blackSlot message)).toNat % 256 ≠ 0)
    (hcB : coldIn substate message.currentTarget (blackSlot message) = cB) {gas : Nat}
    (hg : 157 + slotCost cB ≤ gas) :
    Spec fork (At CODE message 5392 rest MEM0 gas state substate)
      (Halted true .empty (gas - (157 + slotCost cB))
        (readSlot state message.currentTarget (blackSlot message))
        (accessSlot substate message.currentTarget (blackSlot message))) := by
  have hz : extendMemory (MEMK (callerKey message) 6).size [((0 : U256), (0 : U256))] = ⟨0, 0⟩ := by
    rw [size_MEMK]; decide
  step blackLookup hfork hrest hcB (by gas_ok)
  step jumpi0R (isZero3_byte0 hblack)
  step pushR 1 (0 : U256)
  step dupR 0
  refine (Logic.revert (Nat.le_trans (by decide) hfork) (by code_fact) (by code_fact)
    (by rw [hz]; gas_ok)).consequence (fun _ h => h) ?_
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  refine ⟨hr, he, ?_, ?_, hs, hss⟩
  · rw [ho]; simp [memoryReadBytes]
  · rw [hgas, hz]; gas_ok

/-- The gas of the paused path, besides the read of slot 0. -/
abbrev PAUSED_COST : Nat := 762

/-- The specification of a `transfer(address,uint256)` call while paused, from Berlin.

The call data starts with the selector 0xa9059cbb and has at least 4 bytes, the call has no
value, and byte 20 of slot 0 (the `paused` flag) is not 0.

Then the run reverts with no output, after reading slot 0 (762 gas and the price of the read). -/
theorem spec_paused (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xa9059cbb)
    (hv : message.value = 0) (hpaused : byte20 (storageAt state message.currentTarget 0) ≠ 0)
    {c0 : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0) {gas : Nat}
    (hg : PAUSED_COST + slotCost c0 ≤ gas) :
    Spec fork (At CODE message 0 [] .empty gas state substate)
      (Halted true .empty (gas - (PAUSED_COST + slotCost c0))
        (readSlot state message.currentTarget 0) (accessSlot substate message.currentTarget 0)) := by
  simp only [PAUSED_COST] at hg ⊢
  have ht : tested (BitVec.ofNat 256 (selector message.data)) ENTRIES = 22 := by
    rw [hsel]; decide
  have hb : branch (BitVec.ofNat 256 (selector message.data)) 54 (entrySize 4 2) ENTRIES =
      1866 := by
    rw [hsel]; decide
  have h1 := dispatch (state := state) (substate := substate) hsize hsize' (gas := gas)
    (by rw [ht]; gas_ok)
  rw [ht, hb] at h1
  have h2 := entry (state := state) (substate := substate) hv
    (x := BitVec.ofNat 256 (selector message.data)) (gas := gas - 62 - 22 * 22) (by gas_ok)
  have h3 := pausedRevert (message := message) (state := state) (substate := substate) hfork
    (rest := [wordArg message.data 1, addrArg message.data 0, 0x078a,
      BitVec.ofNat 256 (selector message.data)]) (by simp) hpaused hc0
    (gas := gas - 62 - 22 * 22 - 98) (by gas_ok)
  refine Spec.seq (h1.seq h2) (h3.consequence (fun _ h => h) ?_)
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  exact ⟨hr, he, ho, by rw [hgas]; gas_ok, hs, hss⟩

/-- The loop of the interpreter runs a `transfer` call while paused to a revert.

It holds for every bound on the gas of messages and every runner of messages. -/
theorem runFrame_paused (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xa9059cbb)
    (hv : message.value = 0) (hpaused : byte20 (storageAt state message.currentTarget 0) ≠ 0)
    {c0 : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0) {gas : Nat}
    (hg : PAUSED_COST + slotCost c0 ≤ gas) {bound : Nat}
    {runChild : MessageRunner fork Nat bound} {evm : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    ∃ stopped, runFrame (step fork) (step_decreases fork) bound runChild evm within =
      .ok stopped ∧
      Halted true .empty (gas - (PAUSED_COST + slotCost c0))
        (readSlot state message.currentTarget 0) (accessSlot substate message.currentTarget 0)
        stopped :=
  (spec_paused hfork hsize hsize' hsel hv hpaused hc0 hg).runFrame start within

/-- The gas of the blacklisted path, besides the reads of slot 0 and of the blacklist slot. -/
abbrev BLACK_COST : Nat := 913

/-- The specification of a `transfer(address,uint256)` call from a blacklisted caller, from Berlin.

The call data starts with the selector 0xa9059cbb and has at least 4 bytes, the call has no
value, and byte 20 of slot 0 (the `paused` flag) is 0.

The low byte of the slot `keccak256(c ++ w6)` is not 0, where `c` is the caller's address as a
word and `w6` is the word 6 (the `isBlackListed` mapping at base slot 6).

Then the run reverts with no output, after reading slot 0 and that slot; `cB` is whether the
blacklist slot is cold once slot 0 has been accessed. -/
theorem spec_blacklisted (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xa9059cbb)
    (hv : message.value = 0) (hnp : byte20 (storageAt state message.currentTarget 0) = 0)
    (hblack : (storageAt state message.currentTarget (blackSlot message)).toNat % 256 ≠ 0)
    {c0 cB : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hcB : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget
      (blackSlot message) = cB)
    {gas : Nat} (hg : BLACK_COST + slotCost c0 + slotCost cB ≤ gas) :
    Spec fork (At CODE message 0 [] .empty gas state substate)
      (Halted true .empty (gas - (BLACK_COST + slotCost c0 + slotCost cB))
        (readSlot (readSlot state message.currentTarget 0) message.currentTarget (blackSlot message))
        (accessSlot (accessSlot substate message.currentTarget 0) message.currentTarget
          (blackSlot message))) := by
  simp only [BLACK_COST] at hg ⊢
  have ht : tested (BitVec.ofNat 256 (selector message.data)) ENTRIES = 22 := by
    rw [hsel]; decide
  have hb : branch (BitVec.ofNat 256 (selector message.data)) 54 (entrySize 4 2) ENTRIES =
      1866 := by
    rw [hsel]; decide
  have h1 := dispatch (state := state) (substate := substate) hsize hsize' (gas := gas)
    (by rw [ht]; gas_ok)
  rw [ht, hb] at h1
  have h2 := entry (state := state) (substate := substate) hv
    (x := BitVec.ofNat 256 (selector message.data)) (gas := gas - 62 - 22 * 22) (by gas_ok)
  have h3 := notPaused (message := message) (state := state) (substate := substate) hfork
    (rest := [wordArg message.data 1, addrArg message.data 0, 0x078a,
      BitVec.ofNat 256 (selector message.data)]) (by simp) hnp hc0 (M := MEM0)
    (gas := gas - 62 - 22 * 22 - 98) (by gas_ok)
  have h4 := blackRevert (message := message) (state := readSlot state message.currentTarget 0)
    (substate := accessSlot substate message.currentTarget 0) hfork
    (rest := [wordArg message.data 1, addrArg message.data 0, 0x078a,
      BitVec.ofNat 256 (selector message.data)]) (by simp)
    (by rw [storageAt_readSlot]; exact hblack) hcB
    (gas := gas - 62 - 22 * 22 - 98 - (112 + slotCost c0)) (by gas_ok)
  refine Spec.seq (h1.seq (h2.seq h3)) (h4.consequence (fun _ h => h) ?_)
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  exact ⟨hr, he, ho, by rw [hgas]; gas_ok, hs, hss⟩

/-- The loop of the interpreter runs a `transfer` call from a blacklisted caller to a revert.

It holds for every bound on the gas of messages and every runner of messages. -/
theorem runFrame_blacklisted (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xa9059cbb)
    (hv : message.value = 0) (hnp : byte20 (storageAt state message.currentTarget 0) = 0)
    (hblack : (storageAt state message.currentTarget (blackSlot message)).toNat % 256 ≠ 0)
    {c0 cB : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hcB : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget
      (blackSlot message) = cB)
    {gas : Nat} (hg : BLACK_COST + slotCost c0 + slotCost cB ≤ gas) {bound : Nat}
    {runChild : MessageRunner fork Nat bound} {evm : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    ∃ stopped, runFrame (step fork) (step_decreases fork) bound runChild evm within =
      .ok stopped ∧
      Halted true .empty (gas - (BLACK_COST + slotCost c0 + slotCost cB))
        (readSlot (readSlot state message.currentTarget 0) message.currentTarget (blackSlot message))
        (accessSlot (accessSlot substate message.currentTarget 0) message.currentTarget
          (blackSlot message)) stopped :=
  (spec_blacklisted hfork hsize hsize' hsel hv hnp hblack hc0 hcB hg).runFrame start within

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
    Hoare fork (At CODE message 5481 rest M gas state substate)
      (At CODE message 5775 rest M (gas - (106 + slotCost c10))
        (readSlot state message.currentTarget 10) (accessSlot substate message.currentTarget 10)) := by
  have hexp : exponentBytes (0x14 : U256) = 1 := by decide
  step jumpdestR
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
  step pushR 2 (0x168f : U256)
  step jumpiR (isZero_flag_ne hdep)
  exact (repc (by decide)).seq (reshape rfl rfl (by gas_ok))

/-- At 5775, the code calls the token transfer at 9883 with the amount and the recipient. -/
theorem toBasic {w1 a r s : U256} {gas : Nat} (hg : 21 ≤ gas) {M : ByteArray} :
    Hoare fork (At CODE message 5775 [w1, a, r, s] M gas state substate)
      (At CODE message 9883 [w1, a, 0x1699, w1, a, r, s] M (gas - 21) state substate) := by
  step jumpdestR
  step pushR 2 (0x1699 : U256)
  step dupR 2
  step dupR 2
  step pushR 2 (0x269b : U256)
  step jumpR
  exact (repc (by decide)).seq (reshape rfl rfl (by gas_ok))

/-- At 9883, call data of fewer than 68 bytes (two argument words) makes the code revert. -/
theorem shortRevert (hfork : .berlin ≤ fork) {rest : List U256} (hrest : rest.length ≤ 16)
    (hshort : message.data.size < 68) {gas : Nat} (hg : 60 ≤ gas) {M : ByteArray}
    (hM : M.size = 96) :
    Spec fork (At CODE message 9883 rest M gas state substate)
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
  step Logic.calldatasize (by code_fact) (by code_fact) (by gas_ok) (by stk_ok)
  step swapR 0
  norm
  step popR
  step binR 0x10 Local.instruction_lt
  step unR 0x15 instruction_iszero
  step unR 0x15 instruction_iszero
  step unR 0x15 instruction_iszero
  step pushR 2 (0x26b6 : U256)
  refine Triple.seq (Logic.jumpi_of_eq_zero (by code_fact) (by code_fact) (by gas_ok) ?_) ?_
  · have h68 : (add (0x40 : U256) (0x04 : U256)).toNat = 68 := by decide
    have hlt : lessThan (BitVec.ofNat 256 message.data.size) (add (0x40 : U256) (0x04 : U256)) = 1 := by
      simp only [lessThan, h68, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show message.data.size < 2 ^ 256 by omega)]
      rw [if_pos hshort]
    rw [hlt]
    decide
  step pushR 1 (0 : U256)
  step dupR 0
  refine (Logic.revert (Nat.le_trans (by decide) hfork) (by code_fact) (by code_fact)
    (by rw [hz]; gas_ok)).consequence (fun _ h => h) ?_
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  refine ⟨hr, he, ?_, ?_, hs, hss⟩
  · rw [ho]; simp [memoryReadBytes]
  · rw [hgas, hz]; gas_ok

/-- The gas of the short-payload path, besides the reads of slots 0, 10 and the blacklist slot. -/
abbrev SHORT_COST : Nat := 1094

/-- The state after the reads of the short-payload path: slot 0, the blacklist slot, slot 10. -/
abbrev shortState (state : State.TransactionState) (message : Message fork) :
    State.TransactionState :=
  readSlot (readSlot (readSlot state message.currentTarget 0) message.currentTarget
    (blackSlot message)) message.currentTarget 10

/-- The substate after the accesses of the short-payload path. -/
abbrev shortSubstate (substate : Substate) (message : Message fork) : Substate :=
  accessSlot (accessSlot (accessSlot substate message.currentTarget 0) message.currentTarget
    (blackSlot message)) message.currentTarget 10

/-- The specification of a `transfer(address,uint256)` call whose call data is too short.

The call data starts with the selector 0xa9059cbb and has from 4 to 67 bytes, the call has no
value, the contract is not paused (byte 20 of slot 0 is 0), the caller is not blacklisted (the low
byte of `isBlackListed[caller]` is 0), and the contract is not deprecated (byte 20 of slot 10 is 0).

Then the payload check of two argument words fails and the run reverts with no output.

`cB` and `c10` are the coldness of the blacklist slot and of slot 10 when the code reads them. -/
theorem spec_short (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hshort : message.data.size < 68) (hsel : selector message.data = 0xa9059cbb)
    (hv : message.value = 0) (hnp : byte20 (storageAt state message.currentTarget 0) = 0)
    (hnb : (storageAt state message.currentTarget (blackSlot message)).toNat % 256 = 0)
    (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    {c0 cB c10 : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hcB : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget
      (blackSlot message) = cB)
    (hc10 : coldIn (accessSlot (accessSlot substate message.currentTarget 0) message.currentTarget
      (blackSlot message)) message.currentTarget 10 = c10)
    {gas : Nat} (hg : SHORT_COST + slotCost c0 + slotCost cB + slotCost c10 ≤ gas) :
    Spec fork (At CODE message 0 [] .empty gas state substate)
      (Halted true .empty (gas - (SHORT_COST + slotCost c0 + slotCost cB + slotCost c10))
        (shortState state message) (shortSubstate substate message)) := by
  simp only [SHORT_COST] at hg ⊢
  have hsize' : message.data.size < 2 ^ 256 := by omega
  have ht : tested (BitVec.ofNat 256 (selector message.data)) ENTRIES = 22 := by
    rw [hsel]; decide
  have hb : branch (BitVec.ofNat 256 (selector message.data)) 54 (entrySize 4 2) ENTRIES =
      1866 := by
    rw [hsel]; decide
  have h1 := dispatch (state := state) (substate := substate) hsize hsize' (gas := gas)
    (by rw [ht]; gas_ok)
  rw [ht, hb] at h1
  refine Spec.seq h1 ?_
  step entry hv (by gas_ok)
  step notPaused hfork (by simp) hnp hc0 (by gas_ok)
  step blackLookup hfork (by simp) hcB (by gas_ok)
  step jumpiR (blackTest_ne (by rw [storageAt_readSlot]; exact hnb))
  step repc (pc' := 5481) (by decide)
  step depInline hfork (by simp) (by rw [storageAt_readSlot, storageAt_readSlot]; exact hdep) hc10
    (by gas_ok)
  step toBasic (by gas_ok)
  refine ((shortRevert hfork (by simp) hshort (by gas_ok) (size_MEMK _ _))).consequence
    (fun _ h => h) ?_
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  exact ⟨hr, he, ho, by rw [hgas]; gas_ok, hs, hss⟩

/-- The loop of the interpreter runs a `transfer` call with too short call data to a revert.

It holds for every bound on the gas of messages and every runner of messages. -/
theorem runFrame_short (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hshort : message.data.size < 68) (hsel : selector message.data = 0xa9059cbb)
    (hv : message.value = 0) (hnp : byte20 (storageAt state message.currentTarget 0) = 0)
    (hnb : (storageAt state message.currentTarget (blackSlot message)).toNat % 256 = 0)
    (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    {c0 cB c10 : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hcB : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget
      (blackSlot message) = cB)
    (hc10 : coldIn (accessSlot (accessSlot substate message.currentTarget 0) message.currentTarget
      (blackSlot message)) message.currentTarget 10 = c10)
    {gas : Nat} (hg : SHORT_COST + slotCost c0 + slotCost cB + slotCost c10 ≤ gas) {bound : Nat}
    {runChild : MessageRunner fork Nat bound} {evm : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    ∃ stopped, runFrame (step fork) (step_decreases fork) bound runChild evm within =
      .ok stopped ∧
      Halted true .empty (gas - (SHORT_COST + slotCost c0 + slotCost cB + slotCost c10))
        (shortState state message) (shortSubstate substate message) stopped :=
  (spec_short hfork hsize hshort hsel hv hnp hnb hdep hc0 hcB hc10 hg).runFrame start within

end UsdtVerify.Transfer
