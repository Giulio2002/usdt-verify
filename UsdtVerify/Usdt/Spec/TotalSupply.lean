import UsdtVerify.Usdt.Proofs.Common

/-!
# totalSupply()

The path of a call with selector 0x18160ddd, no value, and the contract not deprecated.

- At 778, the entry checks that the call has no value and calls the getter at 3565.
- At 3565, the getter reads slot 10 and tests byte 20 of it (the `deprecated` flag).
- When that byte is 0, it reads slot 1 and returns to 797.
- At 797, the code writes the word at the free memory pointer and returns those 32 bytes.
-/

namespace UsdtVerify.TotalSupply

open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate}

/-- From 778, a call with no value goes to the getter at 3565 with return address 797. -/
theorem entry (hv : message.value = 0) {x : U256} {gas : Nat} (hg : 34 ≤ gas) :
    Gas.HoareG fork (At CODE message 778 [x] MEM0 gas state substate)
      (At CODE message 3565 [0x031d, x] MEM0 (gas - 34) state substate) := by
  step jumpdestR
  step Gas.callvalueG (by code_fact) (by code_fact) (by gas_ok) (by stk_ok)
  step unR 0x15 instruction_iszero
  step pushR 2 (0x0315 : U256)
  step jumpiR (by simp [hv, isZero])
  step jumpdestR
  step pushR 2 (0x031d : U256)
  step pushR 2 (0x0ded : U256)
  step jumpR
  exact (repc (by decide)).seq (Gas.reshapeG rfl rfl (by gas_ok))

/-- The getter at 3565: when byte 20 of slot 10 is 0, it reads slot 1 and returns to 797.

It reads both slots, so it records them as read and accessed, and pays for each. -/
theorem getter (hfork : .berlin ≤ fork) {x : U256} {c10 c1 : Bool}
    (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    (hc10 : coldIn substate message.currentTarget 10 = c10)
    (hc1 : coldIn substate message.currentTarget 1 = c1)
    {gas : Nat} (hg : 130 + slotCost c10 + slotCost c1 ≤ gas) :
    Gas.HoareG fork (At CODE message 3565 [0x031d, x] MEM0 gas state substate)
      (At CODE message 797 [storageAt state message.currentTarget 1, x] MEM0
        (gas - (130 + slotCost c10 + slotCost c1))
        (readSlot (readSlot state message.currentTarget 10) message.currentTarget 1)
        (accessSlot (accessSlot substate message.currentTarget 10) message.currentTarget 1)) := by
  have hc1' : coldIn (accessSlot substate message.currentTarget 10) message.currentTarget 1 = c1 := by
    rw [coldIn_accessSlot (by decide), hc1]
  step depCheck hfork (Or.inl ⟨rfl, rfl⟩) (rest := [0x031d, x]) (by simp) hdep hc10 (by gas_ok)
  step jumpdestR
  step pushR 1 (1 : U256)
  step Gas.sloadG hfork (cold := c1) (by code_fact) (by code_fact) hc1' (by gas_ok)
  step swapR 0
  norm
  step popR
  step jumpdestR
  step swapR 0
  norm
  step jumpR
  refine (repc (by decide)).seq (Gas.reshapeG ?_ rfl (by gas_ok))
  show [_, x] = _
  congr 1

/-- The gas of the whole path, besides the two reads of storage. -/
abbrev COST : Nat := 411

/-- The specification of `totalSupply()`, from Berlin, with the one-counter meter.

The call data starts with the selector 0x18160ddd and has at least 4 bytes, and the call has no
value.

Byte 20 of slot 10 of the contract (the `deprecated` flag) is 0.

Then the run returns the 32 bytes of slot 1, and records slots 10 and 1 as read and accessed.

It pays 411 gas and the price of each read, cold or warm, by EIP-2929. -/
theorem spec (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x18160ddd)
    (hv : message.value = 0) (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    {c10 c1 : Bool} (hc10 : coldIn substate message.currentTarget 10 = c10)
    (hc1 : coldIn substate message.currentTarget 1 = c1)
    {gas : Nat} (hg : COST + slotCost c10 + slotCost c1 ≤ gas) :
    Gas.SpecG fork (At CODE message 0 [] .empty gas state substate)
      (Halted false (wordBytes (storageAt state message.currentTarget 1))
        (gas - (COST + slotCost c10 + slotCost c1))
        (readSlot (readSlot state message.currentTarget 10) message.currentTarget 1)
        (accessSlot (accessSlot substate message.currentTarget 10) message.currentTarget 1)) := by
  simp only [COST] at hg ⊢
  have ht : tested (BitVec.ofNat 256 (selector message.data)) ENTRIES = 6 := by
    rw [hsel]; decide
  have hb : branch (BitVec.ofNat 256 (selector message.data)) 54 (entrySize 4 2) ENTRIES = 778 := by
    rw [hsel]; decide
  have h1 := dispatch (state := state) (substate := substate) hsize hsize' (gas := gas)
    (by rw [ht]; gas_ok)
  rw [ht, hb] at h1
  have h2 := entry (state := state) (substate := substate) hv
    (x := BitVec.ofNat 256 (selector message.data)) (gas := gas - 62 - 22 * 6) (by gas_ok)
  have h3 := getter (substate := substate) hfork
    (x := BitVec.ofNat 256 (selector message.data)) hdep hc10 hc1
    (gas := gas - 62 - 22 * 6 - 34) (by gas_ok)
  have h4 := ret (message := message) (p := 797) (by decide) size_MEM0 mload_MEM0
    (state := readSlot (readSlot state message.currentTarget 10) message.currentTarget 1)
    (substate := accessSlot (accessSlot substate message.currentTarget 10) message.currentTarget 1)
    (v := storageAt state message.currentTarget 1) (rest := [BitVec.ofNat 256 (selector message.data)])
    (by simp)
    (gas := gas - 62 - 22 * 6 - 34 - (130 + slotCost c10 + slotCost c1)) (by gas_ok)
  refine Gas.SpecG.seq (h1.seq (h2.seq h3)) (h4.consequence (fun _ h => h) ?_)
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  exact ⟨hr, he, ho, by rw [hgas]; gas_ok, hs, hss⟩

/-- The loop of the interpreter runs a `totalSupply()` call to its specification.

It holds for every bound on the gas of messages and every runner of messages. -/
theorem runFrame_spec (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x18160ddd)
    (hv : message.value = 0) (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    {c10 c1 : Bool} (hc10 : coldIn substate message.currentTarget 10 = c10)
    (hc1 : coldIn substate message.currentTarget 1 = c1)
    {gas : Nat} (hg : COST + slotCost c10 + slotCost c1 ≤ gas) {bound : Nat}
    {runChild : MessageRunner fork Nat bound} {evm : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    ∃ stopped, runFrame (step fork) (step_decreases fork) bound runChild evm within =
      .ok stopped ∧
      Halted false (wordBytes (storageAt state message.currentTarget 1))
        (gas - (COST + slotCost c10 + slotCost c1))
        (readSlot (readSlot state message.currentTarget 10) message.currentTarget 1)
        (accessSlot (accessSlot substate message.currentTarget 10) message.currentTarget 1)
        stopped :=
  (spec hfork hsize hsize' hsel hv hdep hc10 hc1 hg).runFrame start within

end UsdtVerify.TotalSupply
