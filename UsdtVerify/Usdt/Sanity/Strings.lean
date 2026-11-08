import UsdtVerify.Usdt.Sanity.TransferFrom

/-!
# Sanity: the words of "Tether USD" and "USDT" are of `StrForm`

`StrForm` (Complete/Getters.lean) is a hypothesis of `ok_name`, `ok_symbol`, `effect_call`,
`inv_call`, `inv_call_ns`, `inv_call_all` and the security theorems, on slots 7 and 8.

- `strForm_name`, `strForm_symbol`: `NAME_WORD` and `SYMBOL_WORD` (Spec/Strings.lean: the words
  that Solidity stores for the strings "Tether USD" and "USDT", short form, lengths 10 and 4)
  are of `StrForm`.
- `inv_mainnet`: under `KeccakSep`, `Inv` holds in the state `sM` (one account, at `C`; slot 7
  holds `NAME_WORD`, slot 8 `SYMBOL_WORD`, every other slot 0).
- `strings_applies`: under `KeccakSep`, `inv_call_all` and `supply_call` apply to the run of
  `approve(s, 0)` from `sM`: the run ends with no error, `Inv` holds at its end, and slot 1
  changes as `SupplyStep` says. The proof discharges every other hypothesis of both theorems.
-/

namespace UsdtVerify.Sanity

open EthLib.Base (Fork U256 Address)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open Complete Security Invariant Strings

variable {fork : Fork}

theorem strForm_name : StrForm NAME_WORD := Or.inr (Or.inl ⟨10, by decide, by decide, by decide⟩)

theorem strForm_symbol : StrForm SYMBOL_WORD :=
  Or.inr (Or.inl ⟨4, by decide, by decide, by decide⟩)

/-- Slot 7 holds `NAME_WORD`, slot 8 `SYMBOL_WORD`, every other slot 0. -/
abbrev sM (C : Address) : State.TransactionState := sState C [(7, NAME_WORD), (8, SYMBOL_WORD)]

theorem sM_7 (C : Address) : storageAt (sM C) C 7 = NAME_WORD := by
  simp [storageAt_sState_cons]

theorem sM_8 (C : Address) : storageAt (sM C) C 8 = SYMBOL_WORD := by
  simp [storageAt_sState_cons]

theorem sM_other (C : Address) {n : U256} (h7 : (7 : U256) ≠ n) (h8 : (8 : U256) ≠ n) :
    storageAt (sM C) C n = 0 := by
  rw [storageAt_sState_cons, storageAt_sState_cons, storageAt_sState_nil,
    ite_eq_right_of_eq_false _ _ (eq_false h7), ite_eq_right_of_eq_false _ _ (eq_false h8)]

/-- Under `KeccakSep`, `Inv` holds in `sM`: no balance slot is slot 7 or 8. -/
theorem inv_mainnet (K : KeccakSep) (C : Address) : Invariant.Inv C (sM C) := by
  unfold Invariant.Inv sumBal tot
  have hb : ∀ x : U256, storageAt (sM C) C (mapSlot x 2) = 0 := fun x =>
    sM_other C (fun h => K.fixed x 7 (by decide) h.symm) (fun h => K.fixed x 8 (by decide) h.symm)
  rw [sumTo_congr (g := fun _ => 0) _ (fun i _ => by simp only [bal, hb]; rfl), DepInv.sumTo_zero,
    sM_other C (by decide) (by decide)]
  rfl

/-- **The mainnet words in use**: under `KeccakSep`, `inv_call_all` and `supply_call` apply to
`approve(s, 0)` from `sM`, with slots 7 and 8 holding the words of "Tether USD" and "USDT". -/
theorem strings_applies (K : KeccakSep) (hfork : .berlin ≤ fork) (b : BlockEnvironment fork)
    (t : TransactionEnvironment fork) (C caller : Address) (sp : U256) (ss : Substate) :
    ∃ s : Evm fork Nat, s.error = none ∧ Invariant.Inv C s.state ∧
      SupplyStep (mA0 b t C caller sp) (sM C) s.state := by
  have h10 : storageAt (sM C) C 10 = 0 := sM_other C (by decide) (by decide)
  have hdep : byte20 (storageAt (sM C) C 10) = 0 := by rw [h10]; decide
  obtain ⟨g, evm, hat, w, s, hr, he⟩ := approve_zero_run hfork b t C caller sp ss _ hdep
  have hsz : (mA0 b t C caller sp).data.size < 2 ^ 256 := by
    rw [show (mA0 b t C caller sp).data = data2 SEL_A sp 0 from rfl, size_data2 size_SEL_A]
    decide
  have h7 : StrForm (storageAt (sM C) C 7) := by rw [sM_7]; exact strForm_name
  have h8 : StrForm (storageAt (sM C) C 8) := by rw [sM_8]; exact strForm_symbol
  exact ⟨s, he, inv_call_all (message := mA0 b t C caller sp) (state := sM C) K hfork
      (fun h => by cases h) hsz h7 h8 (fun h => absurd hdep h) (fun h => absurd hdep h)
      (inv_mainnet K C) hat w hr he,
    supply_call (message := mA0 b t C caller sp) (state := sM C) K hfork hsz hdep h7 h8
      hat w hr he⟩

end UsdtVerify.Sanity
