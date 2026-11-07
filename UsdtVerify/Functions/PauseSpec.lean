import UsdtVerify.Functions.Pause

/-!
# pause() and unpause(): the specifications from pc 0

Write `C` for the contract, `w0` for slot 0 of `C` (the owner in its low 160 bits, `paused` in
byte 20), and `owner = w0 & (2^160 - 1)`.

- `spec_pause_notOwner` / `spec_unpause_notOwner`: a caller other than `owner` gets a revert with
  no output.
- `spec_pause_paused`: `pause()` when byte 20 of `w0` is not 0 reverts (`whenNotPaused`).
- `spec_unpause_notPaused`: `unpause()` when byte 20 of `w0` is 0 reverts (`whenPaused`).
- `spec_pause` / `spec_unpause`: the owner's call stops, after one write of slot 0
  (`withPaused w0 1` or `withPaused w0 0`) and the log `Pause()` or `Unpause()`.
-/

namespace UsdtVerify.PauseSpec

open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts
open Owner Pause

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate}

/-- From pc 0 to the start of the body `b` of pause (entry 17) or unpause (entry 12). -/
theorem toBody {sel e r b t : Nat}
    (hp : (sel = 0x8456cb59 ∧ e = 1533 ∧ r = 0x0610 ∧ b = 4936 ∧ t = 18) ∨
      (sel = 0x3f4ba83a ∧ e = 1201 ∧ r = 0x04c4 ∧ b = 4333 ∧ t = 13))
    (hsize : 4 ≤ message.data.size) (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = sel) (hv : message.value = 0) {gas : Nat}
    (hg : 103 + 22 * t ≤ gas) :
    Gas.HoareG fork (At CODE message 0 [] .empty gas state substate)
      (At CODE message (b + 4) [0, 0, BitVec.ofNat 256 r, BitVec.ofNat 256 (selector message.data)]
        MEM0 (gas - (103 + 22 * t)) state substate) := by
  have ht : tested (BitVec.ofNat 256 (selector message.data)) ENTRIES = t ∧
      branch (BitVec.ofNat 256 (selector message.data)) 54 (entrySize 4 2) ENTRIES = e := by
    rw [hsel]
    rcases hp with ⟨rfl, rfl, -, -, rfl⟩ | ⟨rfl, rfl, -, -, rfl⟩ <;> decide
  have h1 := dispatch (state := state) (substate := substate) hsize hsize' (gas := gas)
    (by rw [ht.1]; omega)
  rw [ht.1, ht.2] at h1
  refine h1.seq ?_
  have hb : b ∈ BODIES := by
    rcases hp with ⟨-, -, -, rfl, -⟩ | ⟨-, -, -, rfl, -⟩ <;> decide
  have he : (e = 1533 ∧ r = 0x0610 ∧ b = 4936) ∨ (e = 1201 ∧ r = 0x04c4 ∧ b = 4333) := by
    rcases hp with ⟨-, h1, h2, h3, -⟩ | ⟨-, h1, h2, h3, -⟩
    · exact Or.inl ⟨h1, h2, h3⟩
    · exact Or.inr ⟨h1, h2, h3⟩
  refine (entry0 he hv (by omega)).seq ?_
  refine (prefix9 hb (by simp) (by omega)).seq ?_
  exact restate rfl rfl rfl (by omega) rfl rfl

/-- `pause()` from a caller other than the owner reverts with no output. -/
theorem spec_pause_notOwner (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x8456cb59)
    (hv : message.value = 0) (hown : callerWord message ≠ ownerOf state message.currentTarget)
    {c0 : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0) {gas : Nat}
    (hg : 574 + slotCost c0 ≤ gas) :
    Gas.SpecG fork (At CODE message 0 [] .empty gas state substate)
      (Halted true .empty (gas - (574 + slotCost c0)) (readSlot state message.currentTarget 0)
        (accessSlot substate message.currentTarget 0)) := by
  refine Gas.SpecG.seq (toBody (Or.inl ⟨rfl, rfl, rfl, rfl, rfl⟩) hsize hsize' hsel hv (by omega)) ?_
  refine (ownerRevert hfork (mem_CHECKS (by decide)) (by simp) size_MEM0 hc0 hown
    (by gas_ok)).consequence (fun _ h => h) ?_
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  exact ⟨hr, he, ho, by rw [hgas]; gas_ok, hs, hss⟩

/-- `unpause()` from a caller other than the owner reverts with no output. -/
theorem spec_unpause_notOwner (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x3f4ba83a)
    (hv : message.value = 0) (hown : callerWord message ≠ ownerOf state message.currentTarget)
    {c0 : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0) {gas : Nat}
    (hg : 464 + slotCost c0 ≤ gas) :
    Gas.SpecG fork (At CODE message 0 [] .empty gas state substate)
      (Halted true .empty (gas - (464 + slotCost c0)) (readSlot state message.currentTarget 0)
        (accessSlot substate message.currentTarget 0)) := by
  refine Gas.SpecG.seq (toBody (Or.inr ⟨rfl, rfl, rfl, rfl, rfl⟩) hsize hsize' hsel hv (by omega)) ?_
  refine (ownerRevert hfork (mem_CHECKS (by decide)) (by simp) size_MEM0 hc0 hown
    (by gas_ok)).consequence (fun _ h => h) ?_
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  exact ⟨hr, he, ho, by rw [hgas]; gas_ok, hs, hss⟩

/-- `pause()` by the owner when already paused (byte 20 of slot 0 not 0) reverts with no output. -/
theorem spec_pause_paused (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x8456cb59)
    (hv : message.value = 0) (hown : callerWord message = ownerOf state message.currentTarget)
    (hp : byte20 (storageAt state message.currentTarget 0) ≠ 0)
    {c0 : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0) {gas : Nat}
    (hg : 786 + slotCost c0 ≤ gas) :
    Gas.SpecG fork (At CODE message 0 [] .empty gas state substate)
      (Halted true .empty (gas - (786 + slotCost c0)) (readSlot state message.currentTarget 0)
        (accessSlot substate message.currentTarget 0)) := by
  refine Gas.SpecG.seq (toBody (Or.inl ⟨rfl, rfl, rfl, rfl, rfl⟩) hsize hsize' hsel hv (by omega)) ?_
  step ownerOk hfork (mem_CHECKS (by decide)) (by simp) hc0 hown (by gas_ok)
  at_pc 5027
  step pauseTest hfork (by simp) (coldIn_accessSlot_self _ _ _) (by gas_ok)
  rw [readSlot_readSlot, accessSlot_accessSlot, storageAt_readSlot]
  refine (flagRevert hfork (Or.inl rfl) (isZero3_flag hp) (by simp) size_MEM0
    (by gas_ok)).consequence (fun _ h => h) ?_
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  exact ⟨hr, he, ho, by rw [hgas]; gas_ok, hs, hss⟩

/-- `unpause()` by the owner when not paused (byte 20 of slot 0 is 0) reverts with no output. -/
theorem spec_unpause_notPaused (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x3f4ba83a)
    (hv : message.value = 0) (hown : callerWord message = ownerOf state message.currentTarget)
    (hnp : byte20 (storageAt state message.currentTarget 0) = 0)
    {c0 : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0) {gas : Nat}
    (hg : 673 + slotCost c0 ≤ gas) :
    Gas.SpecG fork (At CODE message 0 [] .empty gas state substate)
      (Halted true .empty (gas - (673 + slotCost c0)) (readSlot state message.currentTarget 0)
        (accessSlot substate message.currentTarget 0)) := by
  refine Gas.SpecG.seq (toBody (Or.inr ⟨rfl, rfl, rfl, rfl, rfl⟩) hsize hsize' hsel hv (by omega)) ?_
  step ownerOk hfork (mem_CHECKS (by decide)) (by simp) hc0 hown (by gas_ok)
  at_pc 4424
  step unpauseTest hfork (by simp) (coldIn_accessSlot_self _ _ _) (by gas_ok)
  rw [readSlot_readSlot, accessSlot_accessSlot, storageAt_readSlot]
  refine (flagRevert hfork (Or.inr rfl) (isZero2_flag_eq hnp) (by simp) size_MEM0
    (by gas_ok)).consequence (fun _ h => h) ?_
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  exact ⟨hr, he, ho, by rw [hgas]; gas_ok, hs, hss⟩

/-- The gas of `pause()` besides the read of slot 0 and the write. -/
abbrev PAUSE_COST : Nat := 1784

/-- The gas of `unpause()` besides the read of slot 0 and the write. -/
abbrev UNPAUSE_COST : Nat := 1671

/-- The price of the write of slot 0 to `withPaused w0 b` (the slot is warm then). -/
abbrev flagCost (fork : Fork) (state : State.TransactionState) (message : Message fork)
    (b : U256) : Nat :=
  sstoreCost fork (originalAt state message.currentTarget 0)
    (storageAt state message.currentTarget 0)
    (withPaused (storageAt state message.currentTarget 0) b) false

/-- The specification of `pause()` by the owner, when not paused.

Hypotheses: Berlin ≤ fork < Glamsterdam; a frame that may write, of an existing account `C`;
call data of 4 to 2^256 - 1 bytes with selector 0x8456cb59; no value; the caller (masked to 160
bits) is the low 160 bits of slot 0; byte 20 of slot 0 is 0; enough gas, and more than 2300
left at the SSTORE.

Then the run stops normally, with slot 0 written to `withPaused w0 1` (byte 20 set to 1, the
other bytes kept: `byte20_withPaused`, `owner_withPaused`), slot 0 accessed, the refund of that
write added, and the log `Pause()` (topic 0x6985a022…, no data) appended. Gas left:
`gas - (1784 + price(slot 0) + price(write))`. -/
theorem spec_pause (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    (hstatic : message.isStatic = false) (hacc : hasAccount state message.currentTarget)
    (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x8456cb59)
    (hv : message.value = 0) (hown : callerWord message = ownerOf state message.currentTarget)
    (hnp : byte20 (storageAt state message.currentTarget 0) = 0)
    {c0 : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0) {gas : Nat}
    (hstip : 3297 + slotCost c0 ≤ gas)
    (hg : PAUSE_COST + slotCost c0 + flagCost fork state message 1 ≤ gas) :
    Gas.SpecG fork (At CODE message 0 [] .empty gas state substate)
      (Halted false .empty (gas - (PAUSE_COST + slotCost c0 + flagCost fork state message 1))
        (writeSlot state message.currentTarget 0
          (withPaused (storageAt state message.currentTarget 0) 1))
        { storeSub fork substate message.currentTarget 0
            (originalAt state message.currentTarget 0) (storageAt state message.currentTarget 0)
            (withPaused (storageAt state message.currentTarget 0) 1) with
          logs := substate.logs.push (log0 message.currentTarget PAUSE_TOPIC) }) := by
  simp only [PAUSE_COST, flagCost] at hg ⊢
  refine Gas.SpecG.seq (toBody (Or.inl ⟨rfl, rfl, rfl, rfl, rfl⟩) hsize hsize' hsel hv (by omega)) ?_
  step ownerOk hfork (mem_CHECKS (by decide)) (by simp) hc0 hown (by gas_ok)
  at_pc 5027
  step pauseTest hfork (by simp) (coldIn_accessSlot_self _ _ _) (by gas_ok)
  rw [readSlot_readSlot, accessSlot_accessSlot, storageAt_readSlot]
  step flagPass (Or.inl ⟨rfl, rfl⟩) (isZero3_flag_ne hnp) (by simp) (by gas_ok)
  step pauseWrite hfork hglam (by simp) hstatic (hasAccount_readSlot hacc)
    (coldIn_accessSlot_self _ _ _) (by gas_ok)
    (by rw [originalAt_readSlot, storageAt_readSlot]; gas_ok)
  rw [originalAt_readSlot, storageAt_readSlot, readSlot_readSlot, writeSlot_readSlot _ _ hacc,
    accessSlot_accessSlot, storeSub_accessSlot]
  refine (logStop (Or.inl ⟨rfl, rfl, rfl⟩) hstatic size_MEM0 mload_MEM0
    (by gas_ok)).consequence (fun _ h => h) ?_
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  exact ⟨hr, he, ho, by rw [hgas]; gas_ok, hs, hss⟩

/-- The specification of `unpause()` by the owner, when paused.

The same as `spec_pause`, with selector 0x3f4ba83a, byte 20 of slot 0 not 0, slot 0 written to
`withPaused w0 0` (byte 20 set to 0), the log `Unpause()` (topic 0x7805862f…, no data), and gas
left `gas - (1671 + price(slot 0) + price(write))`. -/
theorem spec_unpause (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    (hstatic : message.isStatic = false) (hacc : hasAccount state message.currentTarget)
    (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x3f4ba83a)
    (hv : message.value = 0) (hown : callerWord message = ownerOf state message.currentTarget)
    (hp : byte20 (storageAt state message.currentTarget 0) ≠ 0)
    {c0 : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0) {gas : Nat}
    (hstip : 3184 + slotCost c0 ≤ gas)
    (hg : UNPAUSE_COST + slotCost c0 + flagCost fork state message 0 ≤ gas) :
    Gas.SpecG fork (At CODE message 0 [] .empty gas state substate)
      (Halted false .empty (gas - (UNPAUSE_COST + slotCost c0 + flagCost fork state message 0))
        (writeSlot state message.currentTarget 0
          (withPaused (storageAt state message.currentTarget 0) 0))
        { storeSub fork substate message.currentTarget 0
            (originalAt state message.currentTarget 0) (storageAt state message.currentTarget 0)
            (withPaused (storageAt state message.currentTarget 0) 0) with
          logs := substate.logs.push (log0 message.currentTarget UNPAUSE_TOPIC) }) := by
  simp only [UNPAUSE_COST, flagCost] at hg ⊢
  refine Gas.SpecG.seq (toBody (Or.inr ⟨rfl, rfl, rfl, rfl, rfl⟩) hsize hsize' hsel hv (by omega)) ?_
  step ownerOk hfork (mem_CHECKS (by decide)) (by simp) hc0 hown (by gas_ok)
  at_pc 4424
  step unpauseTest hfork (by simp) (coldIn_accessSlot_self _ _ _) (by gas_ok)
  rw [readSlot_readSlot, accessSlot_accessSlot, storageAt_readSlot]
  step flagPass (Or.inr ⟨rfl, rfl⟩) (isZero2_flag hp) (by simp) (by gas_ok)
  step unpauseWrite hfork hglam (by simp) hstatic (hasAccount_readSlot hacc)
    (coldIn_accessSlot_self _ _ _) (by gas_ok)
    (by rw [originalAt_readSlot, storageAt_readSlot]; gas_ok)
  rw [originalAt_readSlot, storageAt_readSlot, readSlot_readSlot, writeSlot_readSlot _ _ hacc,
    accessSlot_accessSlot, storeSub_accessSlot]
  refine (logStop (Or.inr ⟨rfl, rfl, rfl⟩) hstatic size_MEM0 mload_MEM0
    (by gas_ok)).consequence (fun _ h => h) ?_
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  exact ⟨hr, he, ho, by rw [hgas]; gas_ok, hs, hss⟩

end UsdtVerify.PauseSpec
