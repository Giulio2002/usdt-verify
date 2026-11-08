import UsdtVerify.Evm.GasRules
import UsdtVerify.Usdt.Spec.Dispatch

/-!
# Completeness of the dispatcher

Every call data falls in one of three cases (`selector_cases`): fewer than 4 bytes; 4 bytes or
more whose selector is no key of the table; or the selector is the key of entry `i` of the
table, for some `i : Fin 32`.

The fallback and nonpayable reverts of `Usdt/Spec/Dispatch.lean` are stated over `StepG`; with
`SpecG.not_ok` they cover every gas, out of gas included.

- `runFrame_ok_dispatch`: from Berlin, for a fresh frame of `CODE` at pc 0 with call data of
  size below `2^256`, any gas, any gas bound and any message runner: if the loop of the
  interpreter ends with no error, then the call data has 4 bytes or more, its selector is the
  key of some entry `i` of the table, and the call value is 0.
-/

namespace UsdtVerify.Complete

open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open UsdtVerify.Gas
open GasCosts

/-- Every call data has fewer than 4 bytes, or a selector that is no key of the table, or the
selector of entry `i` of the table. -/
theorem selector_cases (data : ByteArray) :
    data.size < 4 ∨
      (4 ≤ data.size ∧ BitVec.ofNat 256 (selector data) ∉ ENTRIES.map Prod.fst) ∨
      (4 ≤ data.size ∧ ∃ i : Fin 32, selector data = ENTRIES[i].1.toNat) := by
  by_cases hs : data.size < 4
  · exact .inl hs
  by_cases hm : BitVec.ofNat 256 (selector data) ∈ ENTRIES.map Prod.fst
  · refine .inr (.inr ⟨by omega, ?_⟩)
    obtain ⟨e, he, hk⟩ := List.mem_map.mp hm
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
    have hlen : ENTRIES.length = 32 := rfl
    refine ⟨⟨i, hlen ▸ hi⟩, ?_⟩
    have hlt : selector data < 2 ^ 256 :=
      Nat.lt_of_lt_of_le (selector_lt data) (by decide)
    show selector data = (ENTRIES[i]).1.toNat
    rw [hk, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  · exact .inr (.inl ⟨by omega, hm⟩)

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate}

/-! ## Completeness of the dispatcher -/

theorem halted_true_error {out : ByteArray} {g : Nat} {st : State.TransactionState}
    {ss : Substate} (e : Evm fork Nat) (h : Halted true out g st ss e) : e.error ≠ none := by
  rw [h.2.1]; simp

/-- From Berlin, a fresh frame of `CODE` at pc 0, with any gas, and call data of size below
`2^256`: if the loop of the interpreter ends with no error, for any gas bound and any message
runner, then the call data has at least 4 bytes, its selector is the key of some entry `i` of the
table, and the call value is 0. -/
theorem runFrame_ok_dispatch (hfork : .berlin ≤ fork) (hsize' : message.data.size < 2 ^ 256)
    {gas : Nat} {bound : Nat} {runChild : MessageRunner fork Nat bound} {evm : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) {s : Evm fork Nat}
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) :
    4 ≤ message.data.size ∧ message.value = 0 ∧
      ∃ i : Fin 32, selector message.data = ENTRIES[i].1.toNat := by
  rcases selector_cases message.data with hs | ⟨hs, hunk⟩ | ⟨hs, i, hi⟩
  · exact absurd hok (SpecG.not_ok (Fallback.spec_short hfork hs (gas := gas + 46) (by omega))
      halted_true_error (at_sh start 46) within hrun)
  · exact absurd hok (SpecG.not_ok (Fallback.spec_unknown hfork hs hsize' hunk (gas := gas + 773)
      (by omega)) halted_true_error (at_sh start 773) within hrun)
  · refine ⟨hs, ?_, i, hi⟩
    by_cases hv : message.value = 0
    · exact hv
    exact absurd hok (SpecG.not_ok (Nonpayable.spec hfork hs hsize' i hi hv
      (gas := gas + (87 + 22 * (i.val + 1))) (by omega)) halted_true_error
      (at_sh start _) within hrun)

end UsdtVerify.Complete
