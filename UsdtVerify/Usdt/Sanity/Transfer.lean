import UsdtVerify.Evm.Sample
import UsdtVerify.Usdt.Sanity.Runner

/-!
# Sanity: the hypotheses of `transfer_ok` hold together

`transfer_ok_sat`: at every fork from Berlin, for every block, transaction, contract address `C`,
caller, recipient word `to` and substate, the call `transfer(to, 1)` from `caller` to `C` running
`CODE`, from the state `sT` (one account, at `C`; slot `balances[caller]` holds 256, every other
slot 0), with enough gas, ends with no error under the interpreter's own runner `processRunner`.
The proof applies `TransferOk.runFrame_ok` (the Summary's `transfer_ok`), so every hypothesis of
that theorem holds there.

No fact about keccak is used: every slot of `C` holds 0 or 256, and each check passes for both
words (256 has low byte 0 and byte 20 equal to 0, and `1 * 256 / 10000 = 0`).
-/

namespace UsdtVerify.Sanity

open EthLib.Base (Fork U256 Address)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open Transfer TransferOk SafeMath

variable {fork : Fork}

/-- The selector of `transfer(address,uint256)`. -/
def SEL_T : ByteArray := ⟨#[0xa9, 0x05, 0x9c, 0xbb]⟩

theorem size_SEL_T : SEL_T.size = 4 := by decide

/-- The call data of `transfer(to, v)`. -/
def dataT (to v : U256) : ByteArray := SEL_T ++ wordBytes to ++ wordBytes v

theorem size_dataT (to v : U256) : (dataT to v).size = 68 := by
  simp [dataT, ByteArray.size_append, size_wordBytes, size_SEL_T]

theorem selector_dataT (to v : U256) : selector (dataT to v) = 0xa9059cbb := by
  rw [dataT, selector_append _ (by rw [ByteArray.size_append, size_SEL_T]; omega),
    selector_append _ (by simp [size_SEL_T])]
  decide

theorem wordArg_dataT (to v : U256) : wordArg (dataT to v) 1 = v := by
  have := loadWord_append_wordBytes (SEL_T ++ wordBytes to) v
  rwa [ByteArray.size_append, size_SEL_T, size_wordBytes] at this

/-- The message of `transfer(to, 1)` from `caller` to `C`. -/
abbrev mT (b : BlockEnvironment fork) (t : TransactionEnvironment fork) (C caller : Address)
    (to : U256) : Message fork :=
  sMsg b t C caller CODE (dataT to 1)

/-- The start state of `transfer_ok_sat`: `balances[caller]` holds 256, every other slot 0. -/
abbrev sT (b : BlockEnvironment fork) (t : TransactionEnvironment fork) (C caller : Address)
    (to : U256) : State.TransactionState :=
  sState C [(senderSlot (mT b t C caller to), 256)]

/-- The gas of `transfer_ok_sat`: the cost of the path, plus 10000. -/
abbrev gT (b : BlockEnvironment fork) (t : TransactionEnvironment fork) (C caller : Address)
    (to : U256) (ss : Substate) : Nat :=
  okCost fork (sT b t C caller to) (mT b t C caller to) (coldIn ss C 0)
    (coldIn (accessSlot ss C 0) C (blackSlot (mT b t C caller to)))
    (coldIn (accessSlot (accessSlot ss C 0) C (blackSlot (mT b t C caller to))) C 10)
    (coldIn (shortSubstate ss (mT b t C caller to)) C 3)
    (coldIn (accessSlot (shortSubstate ss (mT b t C caller to)) C 3) C 4)
    (coldIn (accessSlot (accessSlot (shortSubstate ss (mT b t C caller to)) C 3) C 4) C
      (senderSlot (mT b t C caller to)))
    (coldIn (access3 (shortSubstate ss (mT b t C caller to)) (mT b t C caller to)) C
      (recipientSlot (addrArg (mT b t C caller to).data 0))) + 10000

/-- Every slot of a state with one set slot holds that word or 0. -/
theorem word_or_zero (C : Address) (k w n : U256) :
    storageAt (sState C [(k, w)]) C n = w ∨ storageAt (sState C [(k, w)]) C n = 0 := by
  rw [storageAt_sState_cons, storageAt_sState_nil]
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem byte20_256_or_0 {w : U256} (h : w = 256 ∨ w = 0) : byte20 w = 0 := by
  rcases h with h | h <;> subst h <;> decide

theorem low_256_or_0 {w : U256} (h : w = 256 ∨ w = 0) : w.toNat % 256 = 0 := by
  rcases h with h | h <;> subst h <;> decide

/-- **The hypotheses of `transfer_ok` hold together.** -/
theorem transfer_ok_sat (hfork : .berlin ≤ fork) (b : BlockEnvironment fork)
    (t : TransactionEnvironment fork) (C caller : Address) (to : U256) (ss : Substate) :
    ∃ gas s, ∃ within : GasMeter.gasHeld (sFrame (mT b t C caller to) (sT b t C caller to) ss
        gas).gas ≤ gas,
      runFrame (step fork) (step_decreases fork) gas (processRunner fork gas)
        (sFrame (mT b t C caller to) (sT b t C caller to) ss gas) within = .ok s ∧
      s.error = none := by
  have hacc := hasAccount_sState C [(senderSlot (mT b t C caller to), 256)]
  have hw : ∀ n, storageAt (sT b t C caller to) C n = 256 ∨ storageAt (sT b t C caller to) C n = 0 :=
    word_or_zero C (senderSlot (mT b t C caller to)) 256
  have hct : (mT b t C caller to).currentTarget = C := rfl
  have hv : wordArg (mT b t C caller to).data 1 = 1 := wordArg_dataT to 1
  have hrd : ∀ n, storageAt (shortState (sT b t C caller to) (mT b t C caller to)) C n =
      storageAt (sT b t C caller to) C n := by
    intro n; simp only [shortState, storageAt_readSlot]
  have hself : storageAt (sT b t C caller to) C (senderSlot (mT b t C caller to)) = 256 := by
    rw [storageAt_sState_cons]; simp
  obtain ⟨s, hrun, hH⟩ := TransferOk.runFrame_ok (fork := fork) (message := mT b t C caller to)
    (state := sT b t C caller to) (substate := ss) hfork rfl hacc
    (by rw [show (mT b t C caller to).data = dataT to 1 from rfl, size_dataT]; exact Nat.le_refl _)
    (by rw [show (mT b t C caller to).data = dataT to 1 from rfl, size_dataT]; decide)
    (selector_dataT to 1) rfl
    (byte20_256_or_0 (hw 0)) (low_256_or_0 (hw _)) (byte20_256_or_0 (hw 10))
    (by rw [hv, show (1 : U256).toNat = 1 from rfl, Nat.one_mul]; exact BitVec.isLt _)
    (by
      simp only [feeOf, rawFee, capped, hv, hct, hrd]
      rcases hw 3 with h3 | h3 <;> rcases hw 4 with h4 | h4 <;> rw [h3, h4] <;> decide)
    (by
      simp only [balS, hrd, show (mT b t C caller to).currentTarget = C from rfl, hself, hv]
      decide)
    (by
      simp only [balT, debited, hv]
      have hacc3 : hasAccount (reads3 (shortState (sT b t C caller to) (mT b t C caller to))
          (mT b t C caller to)) C := hacc
      by_cases he : recipientSlot (addrArg (mT b t C caller to).data 0) =
          senderSlot (mT b t C caller to)
      · rw [he, show (mT b t C caller to).currentTarget = C from rfl,
          storageAt_writeSlot_self hacc3]
        simp only [balS, hrd, show (mT b t C caller to).currentTarget = C from rfl, hself]
        decide
      · rw [show (mT b t C caller to).currentTarget = C from rfl,
          storageAt_writeSlot_of_ne hacc3 he]
        simp only [reads3, storageAt_readSlot, hrd]
        rcases hw (recipientSlot (addrArg (mT b t C caller to).data 0)) with h | h <;>
          rw [h] <;> decide)
    rfl rfl rfl rfl rfl rfl rfl
    (gas := gT b t C caller to ss)
    (by simp only [gT, okCost, readCost, hct, hv]; omega) (by simp only [gT, okCost, readCost, hct, hv]; omega)
    (Nat.le_add_right _ _) (bound := gT b t C caller to ss)
    (runChild := processRunner fork _)
    (evm := sFrame (mT b t C caller to) (sT b t C caller to) ss (gT b t C caller to ss))
    (at_sFrame _ rfl _ _ _) (Nat.le_refl _)
  exact ⟨_, s, Nat.le_refl _, hrun, by obtain ⟨-, he, -⟩ := hH; simpa using he⟩

end UsdtVerify.Sanity
