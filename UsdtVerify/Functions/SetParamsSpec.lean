import UsdtVerify.Functions.SetParams

/-!
# setParams(uint256, uint256): the specifications from pc 0

Write `b` for argument word 0 (`newBasisPoints`), `m` for argument word 1 (`newMaxFee`),
`d` for slot 9 (`decimals`), `f = m * 10^d` (EVM words; `exp 10 d` is computed modulo 2^256).

- `spec_notOwner`: a caller other than the owner gets a revert.
- `spec_bpHigh`: the owner, `b ≥ 20` ⇒ REVERT. `spec_feeHigh`: `b < 20`, `m ≥ 50` ⇒ REVERT.
- `spec_setParams`: the owner, `b < 20`, `m < 50`, `m * 10^d < 2^256` ⇒ STOP; slot 3 := `b`,
  slot 4 := `f`; log `Params(b, f)`.

The overflow of `m * 10^d` (SafeMath's assert, INVALID) is not covered; it needs `d ≥ 75`.
-/

namespace UsdtVerify.SetParamsSpec

open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts
open Transfer TransferOk Owner Admin Issue SafeMath SetParams

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate}

/-- From pc 0 to the owner check of setParams (entry 22 of the table). -/
theorem toBody (hsize : 4 ≤ message.data.size) (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0xc0324c77) (hv : message.value = 0) {gas : Nat}
    (hg : 667 ≤ gas) :
    Hoare fork (At CODE message 0 [] .empty gas state substate)
      (At CODE message 5794 [0, 0, wordArg message.data 1, wordArg message.data 0, 0x07b6,
          BitVec.ofNat 256 (selector message.data)]
        MEM0 (gas - 667) state substate) := by
  have ht : tested (BitVec.ofNat 256 (selector message.data)) ENTRIES = 23 ∧
      branch (BitVec.ofNat 256 (selector message.data)) 54 (entrySize 4 2) ENTRIES = 1932 := by
    rw [hsel]; decide
  have h1 := dispatch (state := state) (substate := substate) hsize hsize' (gas := gas)
    (by rw [ht.1]; omega)
  rw [ht.1, ht.2] at h1
  refine h1.seq ?_
  refine (entry2 hv (by omega)).seq ?_
  refine (prefix9 (b := 5790) (by decide) (by simp) (by omega)).seq ?_
  exact restate rfl rfl rfl (by omega) rfl rfl

/-- `setParams(b, m)` from a caller other than the owner reverts with no output. -/
theorem spec_notOwner (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xc0324c77)
    (hv : message.value = 0) (hown : callerWord message ≠ ownerOf state message.currentTarget)
    {c0 : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0) {gas : Nat}
    (hg : 742 + slotCost c0 ≤ gas) :
    Spec fork (At CODE message 0 [] .empty gas state substate)
      (Halted true .empty (gas - (742 + slotCost c0)) (readSlot state message.currentTarget 0)
        (accessSlot substate message.currentTarget 0)) := by
  refine Spec.seq (toBody hsize hsize' hsel hv (by omega)) ?_
  refine (ownerRevert hfork (mem_CHECKS (by decide)) (by simp) size_MEM0 hc0 hown
    (by gas_ok)).consequence (fun _ h => h) ?_
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  exact ⟨hr, he, ho, by rw [hgas]; gas_ok, hs, hss⟩

/-- `setParams(b, m)` by the owner with `b ≥ 20` reverts with no output. -/
theorem spec_bpHigh (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xc0324c77)
    (hv : message.value = 0) (hown : callerWord message = ownerOf state message.currentTarget)
    (hb : 20 ≤ (wordArg message.data 0).toNat)
    {c0 : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0) {gas : Nat}
    (hg : 771 + slotCost c0 ≤ gas) :
    Spec fork (At CODE message 0 [] .empty gas state substate)
      (Halted true .empty (gas - (771 + slotCost c0)) (readSlot state message.currentTarget 0)
        (accessSlot substate message.currentTarget 0)) := by
  refine Spec.seq (toBody hsize hsize' hsel hv (by omega)) ?_
  step ownerOk hfork (mem_CHECKS (by decide)) (by simp) hc0 hown (by gas_ok)
  at_pc 5881
  step test1 (by simp) (by gas_ok)
  refine (fail hfork (Or.inl rfl) (lt_eq (by simp; omega)) (by simp) size_MEM0
    (by gas_ok)).consequence (fun _ h => h) ?_
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  exact ⟨hr, he, ho, by rw [hgas]; gas_ok, hs, hss⟩

/-- `setParams(b, m)` by the owner with `b < 20` and `m ≥ 50` reverts with no output. -/
theorem spec_feeHigh (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xc0324c77)
    (hv : message.value = 0) (hown : callerWord message = ownerOf state message.currentTarget)
    (hb : (wordArg message.data 0).toNat < 20) (hm : 50 ≤ (wordArg message.data 1).toNat)
    {c0 : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0) {gas : Nat}
    (hg : 800 + slotCost c0 ≤ gas) :
    Spec fork (At CODE message 0 [] .empty gas state substate)
      (Halted true .empty (gas - (800 + slotCost c0)) (readSlot state message.currentTarget 0)
        (accessSlot substate message.currentTarget 0)) := by
  refine Spec.seq (toBody hsize hsize' hsel hv (by omega)) ?_
  step ownerOk hfork (mem_CHECKS (by decide)) (by simp) hc0 hown (by gas_ok)
  at_pc 5881
  step test1 (by simp) (by gas_ok)
  step pass (Or.inl ⟨rfl, rfl⟩) (lt_ne (by simpa using hb)) (by simp) (by gas_ok)
  step test2 (by simp) (by gas_ok)
  refine (fail hfork (Or.inr rfl) (lt_eq (by simp; omega)) (by simp) size_MEM0
    (by gas_ok)).consequence (fun _ h => h) ?_
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  exact ⟨hr, he, ho, by rw [hgas]; gas_ok, hs, hss⟩

/-- `f = m * 10^d`, as the code computes it. -/
abbrev feeWord (state : State.TransactionState) (message : Message fork) : U256 :=
  mul (wordArg message.data 1) (exp (0x0a : U256) (storageAt state message.currentTarget 9))

/-- The state at the end of setParams: slot 0 read, slot 3 written, slot 9 read, slot 4 written,
slots 3 and 4 read. -/
abbrev paramsState (state : State.TransactionState) (message : Message fork) :
    State.TransactionState :=
  readSlot (readSlot (writeSlot (readSlot (writeSlot (readSlot state message.currentTarget 0)
    message.currentTarget 3 (wordArg message.data 0)) message.currentTarget 9)
    message.currentTarget 4 (feeWord state message)) message.currentTarget 3) message.currentTarget 4

/-- The substate at the end of setParams: the accesses, the refunds of both writes, and the
log `Params(b, f)`. -/
abbrev paramsSub (fork : Fork) (substate : Substate) (state : State.TransactionState)
    (message : Message fork) : Substate :=
  { accessSlot (accessSlot (storeSub fork (accessSlot (storeSub fork
      (accessSlot substate message.currentTarget 0) message.currentTarget 3
      (originalAt state message.currentTarget 3) (storageAt state message.currentTarget 3)
      (wordArg message.data 0)) message.currentTarget 9) message.currentTarget 4
      (originalAt state message.currentTarget 4) (storageAt state message.currentTarget 4)
      (feeWord state message)) message.currentTarget 3) message.currentTarget 4 with
    logs := substate.logs.push (paramsLog message.currentTarget (wordArg message.data 0)
      (feeWord state message)) }

/-- The variable part of the gas of setParams: the reads of slots 0 and 9, `10 ** d`, `mul`, and
the two writes (slots 3 and 4, cold or warm). -/
abbrev paramsCost (fork : Fork) (state : State.TransactionState) (message : Message fork)
    (c0 c3 c9 c4 : Bool) : Nat :=
  slotCost c0 + sstoreCost fork (originalAt state message.currentTarget 3)
    (storageAt state message.currentTarget 3) (wordArg message.data 0) c3 + slotCost c9 +
    50 * exponentBytes (storageAt state message.currentTarget 9) +
    mulCost (wordArg message.data 1) +
    sstoreCost fork (originalAt state message.currentTarget 4)
      (storageAt state message.currentTarget 4) (feeWord state message) c4

/-- The specification of a successful `setParams(b, m)`.

Hypotheses: Berlin ≤ fork < Glamsterdam; a frame that may write, of an existing account `C`;
call data of 4 to 2^256 - 1 bytes with selector 0xc0324c77; no value; the caller is the owner;
`b < 20`, `m < 50`, `m * 10^d < 2^256`; enough gas, and more than 2300 left at each SSTORE.

Then the run stops normally: slot 3 := `b`, slot 4 := `f = m * 10^d`; one log `Params(b, f)`
(topic 0xb044a1e4…, data the two words); gas left `gas - (2425 + paramsCost)`. -/
theorem spec_setParams (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    (hstatic : message.isStatic = false) (hacc : hasAccount state message.currentTarget)
    (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xc0324c77)
    (hv : message.value = 0) (hown : callerWord message = ownerOf state message.currentTarget)
    (hb : (wordArg message.data 0).toNat < 20) (hm : (wordArg message.data 1).toNat < 50)
    (hov : (wordArg message.data 1).toNat *
      (exp (0x0a : U256) (storageAt state message.currentTarget 9)).toNat < 2 ^ 256)
    {c0 c3 c9 c4 : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hc3 : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget 3 = c3)
    (hc9 : coldIn (accessSlot (accessSlot substate message.currentTarget 0) message.currentTarget 3)
      message.currentTarget 9 = c9)
    (hc4 : coldIn (accessSlot (accessSlot (accessSlot substate message.currentTarget 0)
      message.currentTarget 3) message.currentTarget 9) message.currentTarget 4 = c4)
    {gas : Nat}
    (hstip : 3168 + slotCost c0 + sstoreCost fork (originalAt state message.currentTarget 3)
      (storageAt state message.currentTarget 3) (wordArg message.data 0) c3 + slotCost c9 +
      50 * exponentBytes (storageAt state message.currentTarget 9) +
      mulCost (wordArg message.data 1) ≤ gas)
    (hg : 2425 + paramsCost fork state message c0 c3 c9 c4 ≤ gas) :
    Spec fork (At CODE message 0 [] .empty gas state substate)
      (Halted false .empty (gas - (2425 + paramsCost fork state message c0 c3 c9 c4))
        (paramsState state message) (paramsSub fork substate state message)) := by
  simp only [paramsCost, feeWord] at hg ⊢
  have hacc0 := hasAccount_readSlot (n := 0) (other := message.currentTarget) hacc
  have hacc1 := hasAccount_writeSlot (n := 3) (v := wordArg message.data 0) hacc0
  have hacc2 := hasAccount_readSlot (n := 9) (other := message.currentTarget) hacc1
  have h9 : storageAt (writeSlot (readSlot state message.currentTarget 0) message.currentTarget 3
      (wordArg message.data 0)) message.currentTarget 9 = storageAt state message.currentTarget 9 := by
    rw [storageAt_writeSlot_of_ne hacc0 (by decide), storageAt_readSlot]
  have hc9' : coldIn (storeSub fork (accessSlot substate message.currentTarget 0)
      message.currentTarget 3 (originalAt state message.currentTarget 3)
      (storageAt state message.currentTarget 3) (wordArg message.data 0)) message.currentTarget 9 =
      c9 := hc9
  have hc4' : coldIn (accessSlot (storeSub fork (accessSlot substate message.currentTarget 0)
      message.currentTarget 3 (originalAt state message.currentTarget 3)
      (storageAt state message.currentTarget 3) (wordArg message.data 0)) message.currentTarget 9)
      message.currentTarget 4 = c4 := hc4
  refine Spec.seq (toBody hsize hsize' hsel hv (by omega)) ?_
  step ownerOk hfork (mem_CHECKS (by decide)) (by simp) hc0 hown (by gas_ok)
  at_pc 5881
  step test1 (by simp) (by gas_ok)
  step pass (Or.inl ⟨rfl, rfl⟩) (lt_ne (by simpa using hb)) (by simp) (by gas_ok)
  step test2 (by simp) (by gas_ok)
  step pass (Or.inr ⟨rfl, rfl⟩) (lt_ne (by simpa using hm)) (by simp) (by gas_ok)
  step write3 hfork hglam (by simp) hstatic hacc0 hc3 (by gas_ok)
    (by rw [originalAt_readSlot, storageAt_readSlot]; gas_ok)
  rw [originalAt_readSlot, storageAt_readSlot]
  refine Triple.seq (mulCall hfork (c9 := c9) hc9' (by rw [h9]; exact hov) ?hgm) ?_
  case hgm => rw [h9]; gas_ok
  rw [h9]
  step write4 hfork hglam (by simp) hstatic hacc2 (c4 := c4) hc4' (by gas_ok)
    (by rw [originalAt_readSlot, storageAt_readSlot, originalAt_writeSlot hacc0,
      originalAt_readSlot, storageAt_writeSlot_of_ne hacc0 (by decide), storageAt_readSlot]; gas_ok)
  rw [originalAt_readSlot, storageAt_readSlot, originalAt_writeSlot hacc0,
    originalAt_readSlot, storageAt_writeSlot_of_ne hacc0 (by decide), storageAt_readSlot]
  have hacc3 := hasAccount_writeSlot (n := 4)
    (v := mul (wordArg message.data 1) (exp (0x0a : U256) (storageAt state message.currentTarget 9)))
    hacc2
  have hR3 : storageAt (writeSlot (readSlot (writeSlot (readSlot state message.currentTarget 0)
      message.currentTarget 3 (wordArg message.data 0)) message.currentTarget 9)
      message.currentTarget 4 (mul (wordArg message.data 1)
        (exp (0x0a : U256) (storageAt state message.currentTarget 9)))) message.currentTarget 3 =
      wordArg message.data 0 := by
    rw [storageAt_writeSlot_of_ne hacc2 (by decide), storageAt_readSlot,
      storageAt_writeSlot_self hacc0]
  have hR4 : storageAt (writeSlot (readSlot (writeSlot (readSlot state message.currentTarget 0)
      message.currentTarget 3 (wordArg message.data 0)) message.currentTarget 9)
      message.currentTarget 4 (mul (wordArg message.data 1)
        (exp (0x0a : U256) (storageAt state message.currentTarget 9)))) message.currentTarget 4 =
      mul (wordArg message.data 1) (exp (0x0a : U256) (storageAt state message.currentTarget 9)) :=
    storageAt_writeSlot_self hacc2
  refine (paramsLogBlock hstatic ?c3 ?c4
    size_MEM0 mload_MEM0 hfork (by gas_ok)).consequence (fun _ h => h) ?_
  case c3 =>
    exact TransferFee.coldIn_storeSub_false (TransferFrom.coldIn_accessSlot_false
      (coldIn_accessSlot_self _ _ _))
  case c4 => exact coldIn_accessSlot_self _ _ _
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  refine ⟨hr, he, ho, by rw [hgas]; gas_ok, hs, ?_⟩
  rw [hss, hR3, hR4]

/-- After `setParams(b, m)`: slot 3 is `b`, slot 4 is `m * 10^d`, every other slot is unchanged.
With `b < 20` and `m < 50` from the `require`s. -/
theorem params_effects (hacc : hasAccount state message.currentTarget) :
    storageAt (paramsState state message) message.currentTarget 3 = wordArg message.data 0 ∧
    storageAt (paramsState state message) message.currentTarget 4 = feeWord state message ∧
    ∀ n, n ≠ 3 → n ≠ 4 →
      storageAt (paramsState state message) message.currentTarget n =
        storageAt state message.currentTarget n := by
  have hacc0 := hasAccount_readSlot (n := 0) (other := message.currentTarget) hacc
  have hacc2 := hasAccount_readSlot (n := 9) (other := message.currentTarget)
    (hasAccount_writeSlot (n := 3) (v := wordArg message.data 0) hacc0)
  refine ⟨?_, ?_, ?_⟩
  · simp only [paramsState, storageAt_readSlot]
    rw [storageAt_writeSlot_of_ne hacc2 (by decide), storageAt_readSlot,
      storageAt_writeSlot_self hacc0]
  · simp only [paramsState, storageAt_readSlot]
    rw [storageAt_writeSlot_self hacc2]
  · intro n h3 h4
    simp only [paramsState, storageAt_readSlot]
    rw [storageAt_writeSlot_of_ne hacc2 h4, storageAt_readSlot, storageAt_writeSlot_of_ne hacc0 h3,
      storageAt_readSlot]

end UsdtVerify.SetParamsSpec
