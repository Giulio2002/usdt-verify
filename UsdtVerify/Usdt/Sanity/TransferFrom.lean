import UsdtVerify.Usdt.Sanity.Security

/-!
# Sanity: the hypotheses of `transferFrom_ok` and `transferFrom_bound` hold together

`transferFrom_ok_sat`: at every fork from Berlin, for every block, transaction, contract address
`C`, caller, words `f`, `to` and substate, the call `transferFrom(f, to, 1)` from `caller` to `C`
running `CODE`, from the state `sF` (one account, at `C`; `allowed[f][caller]` and `balances[f]`
hold 256, every other slot 0), with enough gas, ends with no error under `processRunner`.
The proof applies `TransferFrom.runFrame_ok` (the Summary's `transferFrom_ok`).
`transferFrom_bound_applies`: `Security.transferFrom_bound` applies to that run, under
`KeccakSep`.

No fact about keccak is used: every slot of `C` holds 0 or 256 at the start, and each check
passes whatever slots the keccak outputs collide with.
-/

namespace UsdtVerify.Sanity

open EthLib.Base (Fork U256 Address)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open Transfer TransferOk TransferFrom SafeMath Security

variable {fork : Fork}

def SEL_F : ByteArray := ⟨#[0x23, 0xb8, 0x72, 0xdd]⟩

theorem size_SEL_F : SEL_F.size = 4 := by decide

/-- The message of `transferFrom(f, to, 1)` from `caller` to `C`. -/
abbrev mF (b : BlockEnvironment fork) (t : TransactionEnvironment fork) (C caller : Address)
    (f to : U256) : Message fork :=
  sMsg b t C caller CODE (data3 SEL_F f to 1)

/-- The start state of `transferFrom_ok_sat`: `allowed[f][caller]` and `balances[f]` hold 256. -/
abbrev sF (b : BlockEnvironment fork) (t : TransactionEnvironment fork) (C caller : Address)
    (f to : U256) : State.TransactionState :=
  sState C [(allowFrom (mF b t C caller f to) (bitwiseAnd ADDR_MASK f), 256),
    (recipientSlot (bitwiseAnd ADDR_MASK f), 256)]

theorem stipCostF_le (S : State.TransactionState) (M : Message fork)
    (c0 cB c10 cA c3 c4 cF cT : Bool) :
    stipCostF fork S M c0 cB c10 cA c3 c4 cF cT ≤
      stipCostF fork S M true true true true true true true true := by
  have := slotCost_le c0; have := slotCost_le cB; have := slotCost_le c10
  have := slotCost_le cA; have := slotCost_le c3; have := slotCost_le c4
  have := slotCost_le cF; have := slotCost_le cT
  simp only [stipCostF, show slotCost true = 2100 from rfl]; omega

theorem okCostF_le (S : State.TransactionState) (M : Message fork)
    (c0 cB c10 cA c3 c4 cF cT : Bool) :
    okCostF fork S M c0 cB c10 cA c3 c4 cF cT ≤
      okCostF fork S M true true true true true true true true := by
  have := slotCost_le c0; have := slotCost_le cB; have := slotCost_le c10
  have := slotCost_le cA; have := slotCost_le c3; have := slotCost_le c4
  have := slotCost_le cF; have := slotCost_le cT
  simp only [okCostF, show slotCost true = 2100 from rfl]; omega

/-- The gas of `transferFrom_ok_sat`. -/
abbrev gF (b : BlockEnvironment fork) (t : TransactionEnvironment fork) (C caller : Address)
    (f to : U256) : Nat :=
  stipCostF fork (sF b t C caller f to) (mF b t C caller f to) true true true true true true
    true true +
  okCostF fork (sF b t C caller f to) (mF b t C caller f to) true true true true true true
    true true

/-- **The hypotheses of `transferFrom_ok` hold together.** -/
theorem transferFrom_ok_sat (hfork : .berlin ≤ fork) (b : BlockEnvironment fork)
    (t : TransactionEnvironment fork) (C caller : Address) (f to : U256) (ss : Substate) :
    OkRun (mF b t C caller f to) (sF b t C caller f to) ss := by
  have hacc := hasAccount_sState C [(allowFrom (mF b t C caller f to) (bitwiseAnd ADDR_MASK f),
    256), (recipientSlot (bitwiseAnd ADDR_MASK f), 256)]
  have hct : (mF b t C caller f to).currentTarget = C := rfl
  have hv : valArg (mF b t C caller f to) = 1 := wordArg_data3_2 size_SEL_F f to 1
  have hf : fromArg (mF b t C caller f to) = bitwiseAnd ADDR_MASK f :=
    addrArg_data3_0 size_SEL_F f to 1
  have hw : ∀ n, storageAt (sF b t C caller f to) C n = 256 ∨
      storageAt (sF b t C caller f to) C n = 0 := by
    intro n
    simp only [storageAt_sState_cons, storageAt_sState_nil]
    split
    · exact Or.inl rfl
    · split
      · exact Or.inl rfl
      · exact Or.inr rfl
  have hle : ∀ n, (storageAt (sF b t C caller f to) C n).toNat ≤ 256 := by
    intro n; rcases hw n with h | h <;> rw [h] <;> decide
  have hrd : ∀ n, storageAt (checkState (sF b t C caller f to) (mF b t C caller f to)) C n =
      storageAt (sF b t C caller f to) C n := by
    intro n; simp only [checkState, storageAt_readSlot]
  have hA : allowOf (checkState (sF b t C caller f to) (mF b t C caller f to))
      (mF b t C caller f to) (bitwiseAnd ADDR_MASK f) = 256 := by
    simp only [allowOf, hct, hrd, storageAt_sState_cons, ite_true]
  -- the state after the allowance step
  have hAS : allowedF (checkState (sF b t C caller f to) (mF b t C caller f to))
      (mF b t C caller f to) 1 (bitwiseAnd ADDR_MASK f) =
      writeSlot (readsF (checkState (sF b t C caller f to) (mF b t C caller f to))
        (mF b t C caller f to) (bitwiseAnd ADDR_MASK f)) C
        (allowFrom (mF b t C caller f to) (bitwiseAnd ADDR_MASK f)) 255 := by
    simp only [allowedF, hA, allowState, hct]
    rw [ite_eq_right_of_eq_false _ _ (eq_false (by decide))]
    rfl
  have haccR : hasAccount (readsF (checkState (sF b t C caller f to) (mF b t C caller f to))
      (mF b t C caller f to) (bitwiseAnd ADDR_MASK f)) C := hacc
  have hbf : balFrom (checkState (sF b t C caller f to) (mF b t C caller f to))
      (mF b t C caller f to) 1 (bitwiseAnd ADDR_MASK f) = 255 ∨
      balFrom (checkState (sF b t C caller f to) (mF b t C caller f to))
      (mF b t C caller f to) 1 (bitwiseAnd ADDR_MASK f) = 256 := by
    simp only [balFrom, hAS, hct]
    by_cases he : recipientSlot (bitwiseAnd ADDR_MASK f) =
        allowFrom (mF b t C caller f to) (bitwiseAnd ADDR_MASK f)
    · rw [he, storageAt_writeSlot_self haccR]; exact Or.inl rfl
    · rw [storageAt_writeSlot_of_ne haccR he]
      simp only [readsF, storageAt_readSlot, hrd, storageAt_sState_cons, ite_true, ite_self]
      first | exact Or.inr rfl | trivial
  have hleA : ∀ n, (storageAt (allowedF (checkState (sF b t C caller f to)
      (mF b t C caller f to)) (mF b t C caller f to) 1 (bitwiseAnd ADDR_MASK f)) C n).toNat ≤
      256 := by
    rw [hAS]
    refine le_writeSlot haccR (fun n => ?_) (by decide)
    simp only [readsF, storageAt_readSlot, hrd]; exact hle n
  obtain ⟨s, hrun, hH⟩ := TransferFrom.runFrame_ok (fork := fork)
    (message := mF b t C caller f to) (state := sF b t C caller f to) (substate := ss)
    hfork rfl hacc
    (by rw [show (mF b t C caller f to).data = data3 SEL_F f to 1 from rfl,
          size_data3 size_SEL_F]; exact Nat.le_refl _)
    (by rw [show (mF b t C caller f to).data = data3 SEL_F f to 1 from rfl,
          size_data3 size_SEL_F]; decide)
    (by rw [show (mF b t C caller f to).data = data3 SEL_F f to 1 from rfl,
          selector_data3 size_SEL_F]; decide)
    rfl (byte20_256_or_0 (hw 0)) (low_256_or_0 (hw _)) (byte20_256_or_0 (hw 10))
    (by rw [hv, show (1 : U256).toNat = 1 from rfl, Nat.one_mul]; exact BitVec.isLt _)
    (by
      simp only [feeOf, rawFee, capped, hv, hct, hrd]
      rcases hw 3 with h3 | h3 <;> rcases hw 4 with h4 | h4 <;> rw [h3, h4] <;> decide)
    (by rw [hf, hA, hv]; right; decide)
    (by rw [hf, hv]; rcases hbf with h | h <;> rw [h] <;> decide)
    (by
      rw [hf, hv]
      simp only [balTo, debitedF, hct]
      have hacc2 : hasAccount (readSlot (allowedF (checkState (sF b t C caller f to)
          (mF b t C caller f to)) (mF b t C caller f to) 1 (bitwiseAnd ADDR_MASK f)) C
          (recipientSlot (bitwiseAnd ADDR_MASK f))) C := by
        rw [hAS]; exact hasAccount_writeSlot haccR
      have := le_writeSlot (k := recipientSlot (bitwiseAnd ADDR_MASK f))
        (v := sub (balFrom (checkState (sF b t C caller f to) (mF b t C caller f to))
          (mF b t C caller f to) 1 (bitwiseAnd ADDR_MASK f)) 1) hacc2
        (fun n => by simp only [storageAt_readSlot]; exact hleA n)
        (by rcases hbf with h | h <;> rw [h] <;> decide)
        (recipientSlot (toArg (mF b t C caller f to)))
      have h2 : (256 : Nat) + (1 : U256).toNat < 2 ^ 256 := by decide
      omega)
    rfl rfl rfl rfl rfl rfl rfl rfl
    (gas := gF b t C caller f to)
    (Nat.le_trans (stipCostF_le _ _ _ _ _ _ _ _ _ _) (Nat.le_add_right _ _))
    (Nat.le_trans (okCostF_le _ _ _ _ _ _ _ _ _ _) (Nat.le_add_left _ _))
    (bound := gF b t C caller f to) (runChild := processRunner fork _)
    (evm := sFrame (mF b t C caller f to) (sF b t C caller f to) ss (gF b t C caller f to))
    (at_sFrame _ rfl _ _ _) (Nat.le_refl _)
  exact ⟨gF b t C caller f to, _, at_sFrame _ rfl _ _ _, Nat.le_refl _, s, hrun,
    by obtain ⟨-, he, -⟩ := hH; simpa using he⟩

/-- `transferFrom_bound` applies to the run of `transferFrom_ok_sat`. -/
theorem transferFrom_bound_applies (K : Invariant.KeccakSep) (hfork : .berlin ≤ fork)
    (b : BlockEnvironment fork) (t : TransactionEnvironment fork) (C caller : Address)
    (f to : U256) (ss : Substate) :
    ∃ s : Evm fork Nat, s.error = none ∧
      (storageAt (sF b t C caller f to) C (allowFrom (mF b t C caller f to)
          (fromArg (mF b t C caller f to))) = MAX_UINT ∨
        (valArg (mF b t C caller f to)).toNat ≤ (storageAt (sF b t C caller f to) C
          (allowFrom (mF b t C caller f to) (fromArg (mF b t C caller f to)))).toNat) := by
  obtain ⟨g, evm, hat, w, s, hr, he⟩ := transferFrom_ok_sat hfork b t C caller f to ss
  have hw : ∀ n, storageAt (sF b t C caller f to) C n = 256 ∨
      storageAt (sF b t C caller f to) C n = 0 := by
    intro n
    simp only [storageAt_sState_cons, storageAt_sState_nil]
    split
    · exact Or.inl rfl
    · split
      · exact Or.inl rfl
      · exact Or.inr rfl
  exact ⟨s, he, (transferFrom_bound (message := mF b t C caller f to)
    (state := sF b t C caller f to) K hfork
    (by rw [show (mF b t C caller f to).data = data3 SEL_F f to 1 from rfl,
          size_data3 size_SEL_F]; decide)
    (by rw [show (mF b t C caller f to).data = data3 SEL_F f to 1 from rfl,
          selector_data3 size_SEL_F]; decide)
    (byte20_256_or_0 (hw 10)) hat w hr he).1⟩

end UsdtVerify.Sanity
