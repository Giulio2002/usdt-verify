import UsdtVerify.Functions.AddrWrite

/-!
# deprecate(address) and transferOwnership(address): the specifications from pc 0

Write `a` for argument word 0 masked to 160 bits (`addrArg data 0`), `w10` for slot 10 and `w0`
for slot 0.

- `spec_deprecate_notOwner` / `spec_transferOwnership_notOwner`: a caller other than the owner
  gets a revert.
- `spec_deprecate` (owner): STOP; slot 10 := `withPaused w10 1`, then slot 10 :=
  `withAddr (withPaused w10 1) a`; log `Deprecate(a)`. `deprecate_effects`: byte 20 of slot 10
  is 1 and its low 160 bits are `a`; every other slot is unchanged.
- `spec_transferOwnership_zero` (owner, `a = 0`): STOP, nothing written.
  `spec_transferOwnership` (owner, `a ≠ 0`): STOP; slot 0 := `withAddr w0 a`; no log.
  `transferOwnership_effects`: the owner is then `a`, `paused` (byte 20) is kept, every other
  slot is unchanged.
-/

namespace UsdtVerify.AddrWriteSpec

open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts
open Transfer TransferOk Owner Admin Issue Pause BlackList BlackListSpec AddrWrite

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate}

theorem spec_deprecate_notOwner (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x0753c30c)
    (hv : message.value = 0) (hown : callerWord message ≠ ownerOf state message.currentTarget)
    {c0 : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0) {gas : Nat}
    (hg : 262 + slotCost c0 ≤ gas) :
    Spec fork (At CODE message 0 [] .empty gas state substate)
      (Halted true .empty (gas - (262 + slotCost c0)) (readSlot state message.currentTarget 0)
        (accessSlot substate message.currentTarget 0)) := by
  refine Spec.seq (toBody1 (e := 553) (r := 0x0260) (b := 2646) (t := 2) (by decide) (by decide)
    (by rw [hsel]; decide) hsize hsize' hv (by omega)) ?_
  refine (ownerRevert hfork (mem_CHECKS (by decide)) (by simp) size_MEM0 hc0 hown
    (by gas_ok)).consequence (fun _ h => h) ?_
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  exact ⟨hr, he, ho, by rw [hgas]; gas_ok, hs, hss⟩

theorem spec_transferOwnership_notOwner (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xf2fde38b)
    (hv : message.value = 0) (hown : callerWord message ≠ ownerOf state message.currentTarget)
    {c0 : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0) {gas : Nat}
    (hg : 900 + slotCost c0 ≤ gas) :
    Spec fork (At CODE message 0 [] .empty gas state substate)
      (Halted true .empty (gas - (900 + slotCost c0)) (readSlot state message.currentTarget 0)
        (accessSlot substate message.currentTarget 0)) := by
  refine Spec.seq (toBody1 (e := 2374) (r := 0x097d) (b := 7605) (t := 31) (by decide)
    (by decide) (by rw [hsel]; decide) hsize hsize' hv (by omega)) ?_
  refine (ownerRevert hfork (mem_CHECKS (by decide)) (by simp) size_MEM0 hc0 hown
    (by gas_ok)).consequence (fun _ h => h) ?_
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  exact ⟨hr, he, ho, by rw [hgas]; gas_ok, hs, hss⟩

/-- `transferOwnership(0)` by the owner: the run stops, after reading slot 0 only. -/
theorem spec_transferOwnership_zero (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xf2fde38b)
    (hv : message.value = 0) (hown : callerWord message = ownerOf state message.currentTarget)
    (hz : addrArg message.data 0 = 0)
    {c0 : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0) {gas : Nat}
    (hg : 947 + slotCost c0 ≤ gas) :
    Spec fork (At CODE message 0 [] .empty gas state substate)
      (Halted false .empty (gas - (947 + slotCost c0)) (readSlot state message.currentTarget 0)
        (accessSlot substate message.currentTarget 0)) := by
  refine Spec.seq (toBody1 (e := 2374) (r := 0x097d) (b := 7605) (t := 31) (by decide)
    (by decide) (by rw [hsel]; decide) hsize hsize' hv (by omega)) ?_
  step ownerOk hfork (mem_CHECKS (by decide)) (by simp) hc0 hown (by gas_ok)
  at_pc 7696
  step ownTest (by simp) (by gas_ok)
  refine (ownSkip (by rw [addrArg, mask_mask, ← addrArg]; exact hz) (by gas_ok)).consequence (fun _ h => h) ?_
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  exact ⟨hr, he, ho, by rw [hgas]; gas_ok, hs, hss⟩

/-- The price of the write of slot 0 in transferOwnership (warm). -/
abbrev ownCost (fork : Fork) (state : State.TransactionState) (message : Message fork) : Nat :=
  sstoreCost fork (originalAt state message.currentTarget 0) (storageAt state message.currentTarget 0)
    (withAddr (storageAt state message.currentTarget 0) (addrArg message.data 0)) false

/-- The specification of `transferOwnership(a)` by the owner with `a ≠ 0`: the run stops after
one write, slot 0 := `withAddr w0 a` (the owner replaced, `paused` kept), no log; gas left
`gas - (1114 + price(slot 0) + price(write))`; more than 2300 gas at the SSTORE. -/
theorem spec_transferOwnership (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    (hstatic : message.isStatic = false) (hacc : hasAccount state message.currentTarget)
    (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xf2fde38b)
    (hv : message.value = 0) (hown : callerWord message = ownerOf state message.currentTarget)
    (hnz : addrArg message.data 0 ≠ 0)
    {c0 : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0) {gas : Nat}
    (hstip : 3401 + slotCost c0 ≤ gas)
    (hg : 1114 + slotCost c0 + ownCost fork state message ≤ gas) :
    Spec fork (At CODE message 0 [] .empty gas state substate)
      (Halted false .empty (gas - (1114 + slotCost c0 + ownCost fork state message))
        (writeSlot state message.currentTarget 0
          (withAddr (storageAt state message.currentTarget 0) (addrArg message.data 0)))
        (storeSub fork substate message.currentTarget 0 (originalAt state message.currentTarget 0)
          (storageAt state message.currentTarget 0)
          (withAddr (storageAt state message.currentTarget 0) (addrArg message.data 0)))) := by
  simp only [ownCost] at hg ⊢
  refine Spec.seq (toBody1 (e := 2374) (r := 0x097d) (b := 7605) (t := 31) (by decide)
    (by decide) (by rw [hsel]; decide) hsize hsize' hv (by omega)) ?_
  step ownerOk hfork (mem_CHECKS (by decide)) (by simp) hc0 hown (by gas_ok)
  at_pc 7696
  step ownTest (by simp) (by gas_ok)
  step ownGo (by rw [addrArg, mask_mask, ← addrArg]; exact hnz) (by simp) (by gas_ok)
  step addrTail hfork hglam (Or.inr rfl) (by simp) hstatic (hasAccount_readSlot hacc)
    (coldIn_accessSlot_self _ _ _) (by gas_ok)
    (by rw [originalAt_readSlot, storageAt_readSlot]; gas_ok)
  rw [originalAt_readSlot, storageAt_readSlot, writeSlot_readSlot _ _ hacc, storeSub_accessSlot]
  refine (ownEnd (by gas_ok)).consequence (fun _ h => h) ?_
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  exact ⟨hr, he, ho, by rw [hgas]; gas_ok, hs, hss⟩

/-- After `transferOwnership(a)` with `a ≠ 0`: the owner is `a`, `paused` is kept, every other
slot is unchanged. -/
theorem transferOwnership_effects (hacc : hasAccount state message.currentTarget) :
    ownerOf (writeSlot state message.currentTarget 0
        (withAddr (storageAt state message.currentTarget 0) (addrArg message.data 0)))
        message.currentTarget = addrArg message.data 0 ∧
    byte20 (storageAt (writeSlot state message.currentTarget 0
        (withAddr (storageAt state message.currentTarget 0) (addrArg message.data 0)))
        message.currentTarget 0) = byte20 (storageAt state message.currentTarget 0) ∧
    ∀ n, n ≠ 0 → storageAt (writeSlot state message.currentTarget 0
        (withAddr (storageAt state message.currentTarget 0) (addrArg message.data 0)))
        message.currentTarget n = storageAt state message.currentTarget n := by
  refine ⟨?_, ?_, fun n hn => storageAt_writeSlot_of_ne hacc hn⟩
  · rw [ownerOf, storageAt_writeSlot_self hacc, addr_withAddr, addrArg, mask_mask]
  · rw [storageAt_writeSlot_self hacc, byte20_withAddr]

/-- Slot 10 after `deprecate(a)`: the flag set, then the address replaced. -/
abbrev depWord (state : State.TransactionState) (message : Message fork) : U256 :=
  withAddr (withPaused (storageAt state message.currentTarget 10) 1) (addrArg message.data 0)

/-- The state at the end of deprecate: slot 0 read, slot 10 written twice. -/
abbrev depState (state : State.TransactionState) (message : Message fork) :
    State.TransactionState :=
  writeSlot (writeSlot (readSlot state message.currentTarget 0) message.currentTarget 10
    (withPaused (storageAt state message.currentTarget 10) 1)) message.currentTarget 10
    (depWord state message)

/-- The substate at the end of deprecate: the two writes and the log `Deprecate(a)`. -/
abbrev depSub (fork : Fork) (substate : Substate) (state : State.TransactionState)
    (message : Message fork) : Substate :=
  { storeSub fork (storeSub fork (accessSlot substate message.currentTarget 0) message.currentTarget
      10 (originalAt state message.currentTarget 10) (storageAt state message.currentTarget 10)
      (withPaused (storageAt state message.currentTarget 10) 1)) message.currentTarget 10
      (originalAt state message.currentTarget 10)
      (withPaused (storageAt state message.currentTarget 10) 1) (depWord state message) with
    logs := substate.logs.push (log1W message.currentTarget DEPRECATE_TOPIC (addrArg message.data 0)) }

/-- The prices of the two writes of slot 10 in deprecate (cold or warm first, warm second). -/
abbrev depCost (fork : Fork) (state : State.TransactionState) (message : Message fork) : Nat :=
  sstoreCost fork (originalAt state message.currentTarget 10)
    (storageAt state message.currentTarget 10)
    (withPaused (storageAt state message.currentTarget 10) 1) false +
  sstoreCost fork (originalAt state message.currentTarget 10)
    (withPaused (storageAt state message.currentTarget 10) 1) (depWord state message) false

/-- The specification of `deprecate(a)` by the owner.

Hypotheses: Berlin ≤ fork < Glamsterdam; a frame that may write, of an existing account `C`;
call data of 4 to 2^256 - 1 bytes with selector 0x0753c30c; no value; the caller is the owner;
enough gas, and more than 2300 left at each SSTORE.

Then the run stops normally: slot 10 := `withPaused w10 1` (deprecated), then slot 10 :=
`withAddr (withPaused w10 1) a` (upgradedAddress); one log `Deprecate(a)` (topic 0xcc358699…,
data the word `a`); gas left `gas - (1628 + price(slot 0) + price(slot 10) + the two writes)`. -/
theorem spec_deprecate (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    (hstatic : message.isStatic = false) (hacc : hasAccount state message.currentTarget)
    (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x0753c30c)
    (hv : message.value = 0) (hown : callerWord message = ownerOf state message.currentTarget)
    {c0 c10 : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hc10 : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget 10 = c10)
    {gas : Nat}
    (hstip : 2840 + slotCost c0 + slotCost c10 + sstoreCost fork
      (originalAt state message.currentTarget 10) (storageAt state message.currentTarget 10)
      (withPaused (storageAt state message.currentTarget 10) 1) false ≤ gas)
    (hg : 1628 + slotCost c0 + slotCost c10 + depCost fork state message ≤ gas) :
    Spec fork (At CODE message 0 [] .empty gas state substate)
      (Halted false .empty (gas - (1628 + slotCost c0 + slotCost c10 + depCost fork state message))
        (depState state message) (depSub fork substate state message)) := by
  simp only [depCost, depWord] at hg ⊢
  have hacc0 := hasAccount_readSlot (n := 0) (other := message.currentTarget) hacc
  refine Spec.seq (toBody1 (e := 553) (r := 0x0260) (b := 2646) (t := 2) (by decide) (by decide)
    (by rw [hsel]; decide) hsize hsize' hv (by omega)) ?_
  step ownerOk hfork (mem_CHECKS (by decide)) (by simp) hc0 hown (by gas_ok)
  at_pc 2737
  step depFlag hfork hglam (by simp) hstatic hacc0 hc10 (by gas_ok)
    (by rw [originalAt_readSlot, storageAt_readSlot]; gas_ok)
  rw [originalAt_readSlot, storageAt_readSlot]
  refine Triple.seq (depPrefix ?hr1 ?hg1) ?_
  case hr1 => simp
  case hg1 => gas_ok
  refine Triple.seq (addrTail hfork hglam (Or.inl rfl) ?hr2 hstatic (hasAccount_writeSlot hacc0)
    ?hk2 ?hs2 ?hg2) ?_
  case hr2 => simp
  case hk2 => exact coldIn_accessSlot_self _ _ _
  case hs2 => gas_ok
  case hg2 =>
    rw [originalAt_writeSlot hacc0, originalAt_readSlot, storageAt_writeSlot_self hacc0]; gas_ok
  rw [originalAt_writeSlot hacc0, originalAt_readSlot, storageAt_writeSlot_self hacc0]
  refine (listLog (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)) hstatic size_MEM0 mload_MEM0
    (by gas_ok)).consequence (fun _ h => h) ?_
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  refine ⟨hr, he, ho, by rw [hgas]; gas_ok, hs, ?_⟩
  rw [hss, mkey_addrArg0]

/-- After `deprecate(a)`: byte 20 of slot 10 (`deprecated`) is 1, its low 160 bits
(`upgradedAddress`) are `a`, and every other slot is unchanged. -/
theorem deprecate_effects (hacc : hasAccount state message.currentTarget) :
    byte20 (storageAt (depState state message) message.currentTarget 10) = 1 ∧
    bitwiseAnd ADDR_MASK (storageAt (depState state message) message.currentTarget 10) =
      addrArg message.data 0 ∧
    ∀ n, n ≠ 10 → storageAt (depState state message) message.currentTarget n =
      storageAt state message.currentTarget n := by
  have hacc0 := hasAccount_readSlot (n := 0) (other := message.currentTarget) hacc
  have hacc1 := hasAccount_writeSlot (n := 10)
    (v := withPaused (storageAt state message.currentTarget 10) 1) hacc0
  refine ⟨?_, ?_, ?_⟩
  · rw [depState, storageAt_writeSlot_self hacc1, depWord, byte20_withAddr,
      byte20_withPaused _ _ (Or.inr rfl)]
    rfl
  · rw [depState, storageAt_writeSlot_self hacc1, depWord, addr_withAddr, addrArg, mask_mask]
  · intro n hn
    rw [depState, storageAt_writeSlot_of_ne hacc1 hn, storageAt_writeSlot_of_ne hacc0 hn,
      storageAt_readSlot]

end UsdtVerify.AddrWriteSpec
