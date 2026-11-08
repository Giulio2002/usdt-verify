import UsdtVerify.Usdt.Sanity.Transfer

/-!
# Sanity: the hypotheses of approve, issue, redeem and destroyBlackFunds hold together

At every fork from Berlin, for every block, transaction, contract address `C` and substate, each
theorem below exhibits a call to `C` running `CODE`, a start state (`sState`: one account, at `C`,
with the listed slots), and a gas, from which the run ends with no error under the interpreter's
own runner `processRunner`. Each proof applies the success theorem named, so every hypothesis of
that theorem holds there.

- `approve_set_sat` (`Approve.runFrame_set`, the Summary's `approve_set`): `approve(s, 1)` by any
  caller, from the state with every slot 0.
- `issue_sat` (`IssueSpec.runFrame_issue`): `issue(1)` by the owner `CALLER_A`, slot 0 holding
  its address.
- `redeem_sat` (`IssueSpec.runFrame_redeem`): `redeem(1)` by the owner, `_totalSupply` 1 and the
  owner's balance 1.
- `destroy_sat` (`DestroySpec.runFrame_spec`, the Summary's `destroyBlackFunds`):
  `destroyBlackFunds(a)` by the owner, for any word `a`, `isBlackListed[a]` holding 1.

No fact about keccak is used: in each state every slot holds one of a few words, and each check
passes for each of them (whatever slots the keccak outputs collide with).
`CALLER_A` is the address of twenty bytes 0x01: its word is nonzero, below 2^160, with low byte 1.
-/

namespace UsdtVerify.Sanity

open EthLib.Base (Fork U256 Address)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open Owner Issue IssueSpec Destroy DestroySpec BlackList

variable {fork : Fork}

/-- The selectors of `approve`, `issue`, `redeem`, `destroyBlackFunds`. -/
def SEL_A : ByteArray := ⟨#[0x09, 0x5e, 0xa7, 0xb3]⟩
def SEL_I : ByteArray := ⟨#[0xcc, 0x87, 0x2b, 0x66]⟩
def SEL_R : ByteArray := ⟨#[0xdb, 0x00, 0x6a, 0x75]⟩
def SEL_D : ByteArray := ⟨#[0xf3, 0xbd, 0xc2, 0x28]⟩

theorem size_SEL_A : SEL_A.size = 4 := by decide
theorem size_SEL_I : SEL_I.size = 4 := by decide
theorem size_SEL_R : SEL_R.size = 4 := by decide
theorem size_SEL_D : SEL_D.size = 4 := by decide

/-- The address of twenty bytes 0x01. -/
def CALLER_A : Address := Vector.replicate 20 1

/-- The word of `CALLER_A`. -/
def W_A : U256 := BitVec.ofNat 256 0x0101010101010101010101010101010101010101

theorem word_A : bitwiseAnd ADDR_MASK CALLER_A.toU256 = W_A := by decide +kernel

theorem mask_W_A : bitwiseAnd ADDR_MASK W_A = W_A := by decide +kernel

/-! ## approve -/

/-- The message of `approve(s, 1)` from `caller` to `C`. -/
abbrev mA (b : BlockEnvironment fork) (t : TransactionEnvironment fork) (C caller : Address)
    (s : U256) : Message fork :=
  sMsg b t C caller CODE (data2 SEL_A s 1)

/-- **The hypotheses of `approve_set` hold together**, from the state with every slot 0. -/
theorem approve_set_sat (hfork : .berlin ≤ fork) (b : BlockEnvironment fork)
    (t : TransactionEnvironment fork) (C caller : Address) (sp : U256) (ss : Substate) :
    ∃ gas s, ∃ within : GasMeter.gasHeld (sFrame (mA b t C caller sp) (sState C []) ss
        gas).gas ≤ gas,
      runFrame (step fork) (step_decreases fork) gas (processRunner fork gas)
        (sFrame (mA b t C caller sp) (sState C []) ss gas) within = .ok s ∧
      s.error = none := by
  have hv : wordArg (mA b t C caller sp).data 1 = 1 := wordArg_data2_1 size_SEL_A sp 1
  obtain ⟨s, hrun, hH⟩ := Approve.runFrame_set (fork := fork) (message := mA b t C caller sp)
    (state := sState C []) (substate := ss) hfork rfl (hasAccount_sState C [])
    (by rw [show (mA b t C caller sp).data = data2 SEL_A sp 1 from rfl, size_data2 size_SEL_A]
        exact Nat.le_refl _)
    (by rw [show (mA b t C caller sp).data = data2 SEL_A sp 1 from rfl, size_data2 size_SEL_A]
        decide)
    (by rw [show (mA b t C caller sp).data = data2 SEL_A sp 1 from rfl,
          selector_data2 size_SEL_A]; decide)
    rfl (by show byte20 (storageAt (sState C []) C 10) = 0; rw [storageAt_sState_nil]; decide)
    (by rw [hv]; decide)
    (storageAt_sState_nil _ _) rfl rfl
    (gas := 10000 + Gas.writeCost fork (originalAt (sState C []) C (Approve.allowArg
      (mA b t C caller sp))) 0 1 false)
    (by have := slotCost_le (coldIn ss C 10)
        have := slotCost_le (coldIn (accessSlot ss C 10) C (Approve.allowArg (mA b t C caller sp)))
        simp only [show (mA b t C caller sp).currentTarget = C from rfl]; omega)
    (by have := slotCost_le (coldIn ss C 10)
        have := slotCost_le (coldIn (accessSlot ss C 10) C (Approve.allowArg (mA b t C caller sp)))
        simp only [show (mA b t C caller sp).currentTarget = C from rfl, hv]; omega)
    (bound := 10000 + Gas.writeCost fork (originalAt (sState C []) C (Approve.allowArg
      (mA b t C caller sp))) 0 1 false) (runChild := processRunner fork _)
    (evm := sFrame (mA b t C caller sp) (sState C []) ss (10000 + Gas.writeCost fork
      (originalAt (sState C []) C (Approve.allowArg (mA b t C caller sp))) 0 1 false))
    (at_sFrame _ rfl _ _ _) (Nat.le_refl _)
  exact ⟨_, s, Nat.le_refl _, hrun, by obtain ⟨-, he, -⟩ := hH; simpa using he⟩

/-! ## issue -/

/-- The message of `issue(1)` (or another one-word owner call) from `CALLER_A` to `C`. -/
abbrev mO (b : BlockEnvironment fork) (t : TransactionEnvironment fork) (C : Address)
    (sel : ByteArray) (a : U256) : Message fork :=
  sMsg b t C CALLER_A CODE (data1 sel a)

/-- Slot 0 holds the owner `CALLER_A` (not paused); the slots of `kvs` next. -/
abbrev sO (C : Address) (kvs : List (U256 × U256)) : State.TransactionState :=
  sState C ((0, W_A) :: kvs)

theorem owner_sO (C : Address) (kvs : List (U256 × U256)) :
    ownerOf (sO C kvs) C = W_A := by
  simp [ownerOf, storageAt_sState_cons, mask_W_A]

theorem callerWord_mO (b : BlockEnvironment fork) (t : TransactionEnvironment fork)
    (C : Address) (sel : ByteArray) (a : U256) : callerWord (mO b t C sel a) = W_A :=
  word_A

/-- **The hypotheses of `issue` hold together**: `issue(1)` by the owner. -/
theorem issue_sat (hfork : .berlin ≤ fork) (b : BlockEnvironment fork)
    (t : TransactionEnvironment fork) (C : Address) (ss : Substate) :
    ∃ gas s, ∃ within : GasMeter.gasHeld (sFrame (mO b t C SEL_I 1) (sO C []) ss gas).gas ≤ gas,
      runFrame (step fork) (step_decreases fork) gas (processRunner fork gas)
        (sFrame (mO b t C SEL_I 1) (sO C []) ss gas) within = .ok s ∧ s.error = none := by
  have hv : wordArg (mO b t C SEL_I 1).data 0 = 1 := wordArg_data1 size_SEL_I 1
  have hct : (mO b t C SEL_I 1).currentTarget = C := rfl
  have hw : ∀ n, storageAt (sO C []) C n = W_A ∨ storageAt (sO C []) C n = 0 :=
    word_or_zero C 0 W_A
  have hsmall : ∀ n, (storageAt (sO C []) C n).toNat + 1 < 2 ^ 256 := by
    intro n; rcases hw n with h | h <;> rw [h] <;> decide
  obtain ⟨s, hrun, hH⟩ := IssueSpec.runFrame_issue (fork := fork) (message := mO b t C SEL_I 1)
    (state := sO C []) (substate := ss) hfork rfl (hasAccount_sState C _)
    (by rw [show (mO b t C SEL_I 1).data = data1 SEL_I 1 from rfl, size_data1 size_SEL_I]
        decide)
    (by rw [show (mO b t C SEL_I 1).data = data1 SEL_I 1 from rfl, size_data1 size_SEL_I]
        decide)
    (by rw [show (mO b t C SEL_I 1).data = data1 SEL_I 1 from rfl, selector_data1 size_SEL_I]
        decide)
    rfl (by rw [callerWord_mO, hct, owner_sO])
    (by rw [hv, hct]; exact ⟨by decide, hsmall 1⟩) (by rw [hv, hct]; exact hsmall _)
    rfl rfl rfl
    (gas := 20000 + issueCostO fork (sO C []) (mO b t C SEL_I 1) +
      issueCostT fork (sO C []) (mO b t C SEL_I 1))
    (by have := slotCost_le (coldIn ss C 0)
        have := slotCost_le (coldIn (accessSlot ss C 0) C 1)
        have := slotCost_le (coldIn (accessSlot (accessSlot ss C 0) C 1) C
          (ownerBal (sO C []) C))
        simp only [hct]; omega)
    (by have := slotCost_le (coldIn ss C 0)
        have := slotCost_le (coldIn (accessSlot ss C 0) C 1)
        have := slotCost_le (coldIn (accessSlot (accessSlot ss C 0) C 1) C
          (ownerBal (sO C []) C))
        simp only [hct]; omega)
    (bound := 20000 + issueCostO fork (sO C []) (mO b t C SEL_I 1) +
      issueCostT fork (sO C []) (mO b t C SEL_I 1)) (runChild := processRunner fork _)
    (evm := sFrame (mO b t C SEL_I 1) (sO C []) ss (20000 +
      issueCostO fork (sO C []) (mO b t C SEL_I 1) + issueCostT fork (sO C []) (mO b t C SEL_I 1)))
    (at_sFrame _ rfl _ _ _) (Nat.le_refl _)
  exact ⟨_, s, Nat.le_refl _, hrun, by obtain ⟨-, he, -⟩ := hH; simpa using he⟩

/-! ## redeem -/

/-- The start state of `redeem_sat`: slot 0 the owner, `_totalSupply` 1, the owner's balance 1. -/
abbrev sR (C : Address) : State.TransactionState := sO C [(1, 1), (mapSlot W_A 2, 1)]

/-- **The hypotheses of `redeem` hold together**: `redeem(1)` by the owner. -/
theorem redeem_sat (hfork : .berlin ≤ fork) (b : BlockEnvironment fork)
    (t : TransactionEnvironment fork) (C : Address) (ss : Substate) :
    ∃ gas s, ∃ within : GasMeter.gasHeld (sFrame (mO b t C SEL_R 1) (sR C) ss gas).gas ≤ gas,
      runFrame (step fork) (step_decreases fork) gas (processRunner fork gas)
        (sFrame (mO b t C SEL_R 1) (sR C) ss gas) within = .ok s ∧ s.error = none := by
  have hv : wordArg (mO b t C SEL_R 1).data 0 = 1 := wordArg_data1 size_SEL_R 1
  have hct : (mO b t C SEL_R 1).currentTarget = C := rfl
  have hT : storageAt (sR C) C 1 = 1 := by
    simp [storageAt_sState_cons]
  have hB : 1 ≤ (storageAt (sR C) C (mapSlot W_A 2)).toNat := by
    simp only [storageAt_sState_cons]
    split
    · decide
    · split
      · decide
      · simp
  obtain ⟨s, hrun, hH⟩ := IssueSpec.runFrame_redeem (fork := fork) (message := mO b t C SEL_R 1)
    (state := sR C) (substate := ss) hfork rfl (hasAccount_sState C _)
    (by rw [show (mO b t C SEL_R 1).data = data1 SEL_R 1 from rfl, size_data1 size_SEL_R]
        decide)
    (by rw [show (mO b t C SEL_R 1).data = data1 SEL_R 1 from rfl, size_data1 size_SEL_R]
        decide)
    (by rw [show (mO b t C SEL_R 1).data = data1 SEL_R 1 from rfl, selector_data1 size_SEL_R]
        decide)
    rfl (by rw [callerWord_mO, hct, owner_sO])
    (by rw [hv, hct, hT]; decide) (by rw [hv, hct, ownerBal, owner_sO]; exact hB)
    rfl rfl rfl
    (gas := 20000 + redeemCostT fork (sR C) (mO b t C SEL_R 1) +
      redeemCostO fork (sR C) (mO b t C SEL_R 1))
    (by have := slotCost_le (coldIn ss C 0)
        have := slotCost_le (coldIn (accessSlot ss C 0) C 1)
        have := slotCost_le (coldIn (accessSlot (accessSlot ss C 0) C 1) C (ownerBal (sR C) C))
        simp only [hct]; omega)
    (by have := slotCost_le (coldIn ss C 0)
        have := slotCost_le (coldIn (accessSlot ss C 0) C 1)
        have := slotCost_le (coldIn (accessSlot (accessSlot ss C 0) C 1) C (ownerBal (sR C) C))
        simp only [hct]; omega)
    (bound := 20000 + redeemCostT fork (sR C) (mO b t C SEL_R 1) +
      redeemCostO fork (sR C) (mO b t C SEL_R 1)) (runChild := processRunner fork _)
    (evm := sFrame (mO b t C SEL_R 1) (sR C) ss (20000 + redeemCostT fork (sR C)
      (mO b t C SEL_R 1) + redeemCostO fork (sR C) (mO b t C SEL_R 1)))
    (at_sFrame _ rfl _ _ _) (Nat.le_refl _)
  exact ⟨_, s, Nat.le_refl _, hrun, by obtain ⟨-, he, -⟩ := hH; simpa using he⟩

/-! ## destroyBlackFunds -/

/-- The start state of `destroy_sat`: slot 0 the owner, `isBlackListed[a]` holding 1. -/
abbrev sD (C : Address) (a : U256) : State.TransactionState :=
  sO C [(listSlot (bitwiseAnd ADDR_MASK a), 1)]

/-- **The hypotheses of `destroyBlackFunds` hold together**: `destroyBlackFunds(a)` by the
owner, for any word `a`, with `a` blacklisted. -/
theorem destroy_sat (hfork : .berlin ≤ fork) (b : BlockEnvironment fork)
    (t : TransactionEnvironment fork) (C : Address) (a : U256) (ss : Substate) :
    ∃ gas s, ∃ within : GasMeter.gasHeld (sFrame (mO b t C SEL_D a) (sD C a) ss gas).gas ≤ gas,
      runFrame (step fork) (step_decreases fork) gas (processRunner fork gas)
        (sFrame (mO b t C SEL_D a) (sD C a) ss gas) within = .ok s ∧ s.error = none := by
  have hct : (mO b t C SEL_D a).currentTarget = C := rfl
  have ha : addrArg (mO b t C SEL_D a).data 0 = bitwiseAnd ADDR_MASK a := by
    show bitwiseAnd ADDR_MASK (wordArg (data1 SEL_D a) 0) = _
    rw [wordArg_data1 size_SEL_D]
  have hl : (storageAt (sD C a) C (listSlot (bitwiseAnd ADDR_MASK a))).toNat % 256 ≠ 0 := by
    simp only [storageAt_sState_cons]
    split
    · rw [W_A]; decide
    · simp
  have h10 : byte20 (storageAt (sD C a) C 10) = 0 := by
    simp only [storageAt_sState_cons, storageAt_sState_nil]
    split
    · decide
    · split <;> decide
  obtain ⟨s, hrun, hH⟩ := DestroySpec.runFrame_spec (fork := fork) (message := mO b t C SEL_D a)
    (state := sD C a) (substate := ss) hfork rfl (hasAccount_sState C _)
    (by rw [show (mO b t C SEL_D a).data = data1 SEL_D a from rfl, size_data1 size_SEL_D]
        decide)
    (by rw [show (mO b t C SEL_D a).data = data1 SEL_D a from rfl, size_data1 size_SEL_D]
        decide)
    (by rw [show (mO b t C SEL_D a).data = data1 SEL_D a from rfl, selector_data1 size_SEL_D]
        decide)
    rfl (by rw [callerWord_mO, hct, owner_sO]) (by rw [ha, hct]; exact hl) (by rw [hct]; exact h10)
    rfl rfl rfl rfl rfl
    (gas := 20000 + costB fork (sD C a) (mO b t C SEL_D a) + costT fork (sD C a) (mO b t C SEL_D a))
    (by have := slotCost_le (coldIn ss C 0)
        have := slotCost_le (coldIn (accessSlot ss C 0) C (listSlot (addrArg (mO b t C SEL_D a).data 0)))
        have := slotCost_le (coldIn (preSub ss (mO b t C SEL_D a)) C 10)
        have := slotCost_le (coldIn (accessSlot (preSub ss (mO b t C SEL_D a)) C 10) C
          (balSlot (mO b t C SEL_D a)))
        simp only [hct]; omega)
    (by have := slotCost_le (coldIn ss C 0)
        have := slotCost_le (coldIn (accessSlot ss C 0) C (listSlot (addrArg (mO b t C SEL_D a).data 0)))
        have := slotCost_le (coldIn (preSub ss (mO b t C SEL_D a)) C 10)
        have := slotCost_le (coldIn (accessSlot (preSub ss (mO b t C SEL_D a)) C 10) C
          (balSlot (mO b t C SEL_D a)))
        have := slotCost_le (coldIn (readSub ss (mO b t C SEL_D a)) C 1)
        simp only [hct]; omega)
    (by have := slotCost_le (coldIn ss C 0)
        have := slotCost_le (coldIn (accessSlot ss C 0) C (listSlot (addrArg (mO b t C SEL_D a).data 0)))
        have := slotCost_le (coldIn (preSub ss (mO b t C SEL_D a)) C 10)
        have := slotCost_le (coldIn (accessSlot (preSub ss (mO b t C SEL_D a)) C 10) C
          (balSlot (mO b t C SEL_D a)))
        have := slotCost_le (coldIn (readSub ss (mO b t C SEL_D a)) C 1)
        simp only [hct]; omega)
    (bound := 20000 + costB fork (sD C a) (mO b t C SEL_D a) +
      costT fork (sD C a) (mO b t C SEL_D a)) (runChild := processRunner fork _)
    (evm := sFrame (mO b t C SEL_D a) (sD C a) ss (20000 + costB fork (sD C a) (mO b t C SEL_D a) +
      costT fork (sD C a) (mO b t C SEL_D a)))
    (at_sFrame _ rfl _ _ _) (Nat.le_refl _)
  exact ⟨_, s, Nat.le_refl _, hrun, by obtain ⟨-, he, -⟩ := hH; simpa using he⟩

end UsdtVerify.Sanity
