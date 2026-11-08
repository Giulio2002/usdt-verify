import UsdtVerify.Evm.GasRules
import UsdtVerify.Usdt.Spec.Dispatch

/-!
# Completeness of the dispatcher

Every call data falls in one of three cases (`selector_cases`): fewer than 4 bytes; 4 bytes or
more whose selector is no key of the table; or the selector is the key of entry `i` of the
table, for some `i : Fin 32`.

The prelude, the table, the fallback revert and the nonpayable revert are proved again here over
`StepG` (the same blocks as `Usdt/Map.lean` and `Usdt/Spec/Dispatch.lean`,
with the rules of `Evm/GasRules.lean`). With `SpecG.not_ok` this covers every gas, out of gas included.

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

/-! ## Step macros over `StepG` -/

macro "push1G' " b:term : term =>
  `(push1G (byte := $b) (by code_fact) (by code_fact) (by code_fact) (by gas_ok) (by stk_ok))

macro "pushG' " n:term:max w:term:max : term =>
  `(pushG (n := $n) (word := $w) (by decide) (by code_fact) (by code_fact)
    (decode_push $n (by decide)) (by code_fact) (by gas_ok) (by stk_ok))

macro "pushAnyG' " n:term:max : term =>
  `(pushG (n := $n) (by decide) (by code_fact) (by code_fact)
    (decode_push $n (by decide)) (by rw [pushData_CODE]) (by gas_ok) (by stk_ok))

macro "binG' " b:term:max i:term:max : term =>
  `(binaryG (byte := $b) (by code_fact) (by code_fact) (ofByte_of_decode rfl (Fork.frontier_le _))
    $i (by gas_ok))

macro "unG' " b:term:max i:term:max : term =>
  `(unaryG (byte := $b) (by code_fact) (by code_fact) (ofByte_of_decode rfl (Fork.frontier_le _))
    $i (by gas_ok))

macro "swapG' " n:term:max : term => `(swapG $n (by code_fact) (by code_fact) rfl (by gas_ok))

macro "dupG' " n:term:max : term =>
  `(dupG $n (by code_fact) (by code_fact) rfl (by gas_ok) (by stk_ok))

macro "jumpdestG'" : term => `(jumpdestG (by code_fact) (by code_fact) (by gas_ok))

macro "jumpiG' " h:term:max : term =>
  `(jumpi_takenG (by code_fact) (by code_fact) (by gas_ok) $h (by valid_dest))

macro "jumpi0G' " h:term:max : term =>
  `(jumpi_of_eq_zeroG (by code_fact) (by code_fact) (by gas_ok) $h)

/-! ## The prelude and the table over `StepG` -/

/-- `prelude` over `StepG`. -/
theorem preludeG (hsize : 4 ≤ message.data.size) (hsize' : message.data.size < 2 ^ 256)
    {gas : Nat} (hg : 62 ≤ gas) :
    HoareG fork (At CODE message 0 [] .empty gas state substate)
      (At CODE message 54 [BitVec.ofNat 256 (selector message.data)] MEM0 (gas - 62) state
        substate) := by
  have hext : extendMemory ByteArray.empty.size [((BitVec.ofNat 256 (0x40 : UInt8).toNat : U256),
      (32 : U256))] = ⟨9, 96⟩ := by decide
  step push1G' 0x60
  step push1G' 0x40
  step mstoreG (by code_fact) (by code_fact) (by simp only [hext]; omega)
  step reshapeG rfl (by rw [hext]) (show _ = gas - 18 by simp only [hext]; omega)
  step push1G' 0x04
  step calldatasizeG (by code_fact) (by code_fact) (by gas_ok) (by stk_ok)
  step binG' 0x10 Local.instruction_lt
  step pushG' 2 0x0196
  refine Triple.seq (jumpi_of_eq_zeroG (by code_fact) (by code_fact) (by gas_ok) ?_) ?_
  · have h4 : (BitVec.ofNat 256 (UInt8.toNat 4) : U256).toNat = 4 := by decide
    simp only [lessThan, h4, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsize']
    split <;> first | omega | rfl
  step push1G' 0x00
  step calldataloadG (by code_fact) (by code_fact) (by gas_ok)
  step pushG' 29 (BitVec.ofNat 256 (2 ^ 224))
  step swapG' 0
  step binG' 0x04 Local.instruction_div
  step pushG' 4 (BitVec.ofNat 256 0xffffffff)
  step binG' 0x16 Local.instruction_and
  refine reshapeG ?_ (by rfl) (by gas_ok)
  have h0 : (BitVec.ofNat 256 (UInt8.toNat 0) : U256).toNat = 0 := by decide
  simp only [h0, List.cons.injEq, and_true]
  exact selector_word message.data

/-- `dispatch` over `StepG`. -/
theorem dispatchG (hsize : 4 ≤ message.data.size) (hsize' : message.data.size < 2 ^ 256)
    {gas : Nat} (hg : 62 + 22 * tested (BitVec.ofNat 256 (selector message.data)) ENTRIES ≤ gas) :
    HoareG fork (At CODE message 0 [] .empty gas state substate)
      (At CODE message (branch (BitVec.ofNat 256 (selector message.data)) 54 (entrySize 4 2) ENTRIES)
        [BitVec.ofNat 256 (selector message.data)] MEM0
        (gas - 62 - 22 * tested (BitVec.ofNat 256 (selector message.data)) ENTRIES) state
        substate) :=
  (preludeG hsize hsize' (by omega)).seq
    (branchTableG (by decide) (by decide) (by simp [STACK_LIMIT]) table (by omega))

/-! ## The reverts over `StepG` -/

/-- `Fallback.revert406` over `StepG`. -/
theorem revert406G (hfork : .berlin ≤ fork) {rest : List U256} (hrest : rest.length ≤ 16)
    {M : ByteArray} {gas : Nat} (hg : 7 ≤ gas) :
    SpecG fork (At CODE message 406 rest M gas state substate)
      (Halted true .empty (gas - 7) state substate) := by
  have hz : extendMemory M.size [((0 : U256), (0 : U256))] = ⟨0, 0⟩ := by
    simp [extendMemory]
  step jumpdestG'
  step pushG' 1 (0 : U256)
  step dupG' 0
  refine (revertG (Nat.le_trans (by decide) hfork) (by code_fact)
    (by code_fact) (by rw [hz]; gas_ok)).consequence (fun _ h => h) ?_
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  refine ⟨hr, he, ?_, ?_, hs, hss⟩
  · rw [ho]; simp [memoryReadBytes]
  · rw [hgas, hz]; gas_ok

/-- `Fallback.spec_unknown` over `StepG`. -/
theorem spec_unknownG (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256)
    (hunk : BitVec.ofNat 256 (selector message.data) ∉ ENTRIES.map Prod.fst)
    {gas : Nat} (hg : 773 ≤ gas) :
    SpecG fork (At CODE message 0 [] .empty gas state substate)
      (Halted true .empty (gas - 773) state substate) := by
  have hne : ∀ e ∈ ENTRIES, e.1 ≠ BitVec.ofNat 256 (selector message.data) := by
    intro e he heq
    exact hunk (List.mem_map.mpr ⟨e, he, heq⟩)
  have ht := tested_of_forall_ne hne
  have hb := branch_of_forall_ne (pc := 54) (size := entrySize 4 2) hne
  have hlen : ENTRIES.length = 32 := rfl
  rw [hlen] at ht hb
  have h1 := dispatchG (fork := fork) (state := state) (substate := substate) hsize hsize'
    (gas := gas) (by rw [ht]; omega)
  rw [ht, hb] at h1
  refine SpecG.seq (h1.seq (repcG (pc' := 406) (by decide))) ?_
  refine (revert406G hfork (by simp) (by omega)).consequence (fun _ h => h) ?_
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  exact ⟨hr, he, ho, by rw [hgas]; omega, hs, hss⟩

/-- `Fallback.spec_short` over `StepG`. -/
theorem spec_shortG (hfork : .berlin ≤ fork) (hsize : message.data.size < 4)
    {gas : Nat} (hg : 46 ≤ gas) :
    SpecG fork (At CODE message 0 [] .empty gas state substate)
      (Halted true .empty (gas - 46) state substate) := by
  have hext : extendMemory ByteArray.empty.size [((BitVec.ofNat 256 (0x40 : UInt8).toNat : U256),
      (32 : U256))] = ⟨9, 96⟩ := by decide
  step push1G' 0x60
  step push1G' 0x40
  step mstoreG (by code_fact) (by code_fact) (by simp only [hext]; omega)
  step reshapeG rfl (by rw [hext]) (show _ = gas - 18 by simp only [hext]; omega)
  step push1G' 0x04
  step calldatasizeG (by code_fact) (by code_fact) (by gas_ok) (by stk_ok)
  step binG' 0x10 Local.instruction_lt
  step pushG' 2 0x0196
  step jumpiG' (by
    have h4 : (BitVec.ofNat 256 (UInt8.toNat 4) : U256).toNat = 4 := by decide
    simp only [lessThan, h4, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show message.data.size < 2 ^ 256 by omega)]
    rw [ite_eq_left hsize]
    decide)
  refine (repcG (pc' := 406) (by decide)).seq ?_
  refine (revert406G hfork (by simp) (by gas_ok)).consequence (fun _ h => h) ?_
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  exact ⟨hr, he, ho, by rw [hgas]; gas_ok, hs, hss⟩

/-- `Nonpayable.valueRevert` over `StepG`. -/
theorem valueRevertG (hfork : .berlin ≤ fork) {e : Nat} (he : e ∈ Nonpayable.DESTS)
    (hv : message.value ≠ 0) {x : U256} {gas : Nat} (hg : 25 ≤ gas) :
    SpecG fork (At CODE message e [x] MEM0 gas state substate)
      (Halted true .empty (gas - 25) state substate) := by
  have hz : extendMemory MEM0.size [((0 : U256), (0 : U256))] = ⟨0, 0⟩ := by
    rw [size_MEM0]; decide
  have hc : isZero message.value = 0 := by
    unfold isZero
    split
    · contradiction
    · rfl
  simp only [Nonpayable.DESTS, ENTRIES, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl
  all_goals
    step jumpdestG'
    step callvalueG (by code_fact) (by code_fact) (by gas_ok) (by stk_ok)
    step unG' 0x15 instruction_iszero
    step pushAnyG' 2
    step jumpi0G' hc
    step pushG' 1 (0 : U256)
    step dupG' 0
    refine (revertG (Nat.le_trans (by decide) hfork) (by code_fact) (by code_fact)
      (by rw [hz]; gas_ok)).consequence (fun _ h => h) ?_
    rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
    refine ⟨hr, he, ?_, ?_, hs, hss⟩
    · rw [ho]; simp [memoryReadBytes]
    · rw [hgas, hz]; gas_ok

/-- `Nonpayable.spec` over `StepG`. -/
theorem nonpayableG (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (i : Fin 32)
    (hsel : selector message.data = ENTRIES[i].1.toNat) (hv : message.value ≠ 0) {gas : Nat}
    (hg : 87 + 22 * (i.val + 1) ≤ gas) :
    SpecG fork (At CODE message 0 [] .empty gas state substate)
      (Halted true .empty (gas - (87 + 22 * (i.val + 1))) state substate) := by
  obtain ⟨ht, hb⟩ := Nonpayable.table_entry i
  rw [← hsel] at ht hb
  have h1 := dispatchG (fork := fork) (state := state) (substate := substate) hsize hsize'
    (gas := gas) (by rw [ht]; omega)
  rw [ht, hb] at h1
  have h2 := valueRevertG (fork := fork) (state := state) (substate := substate) hfork
    (e := ENTRIES[i].2.toNat) (List.mem_map.2 ⟨ENTRIES[i], List.getElem_mem _, rfl⟩) hv
    (x := BitVec.ofNat 256 (selector message.data)) (gas := gas - 62 - 22 * (i.val + 1))
    (by omega)
  refine SpecG.seq h1 (h2.consequence (fun _ h => h) ?_)
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  exact ⟨hr, he, ho, by rw [hgas]; omega, hs, hss⟩

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
  · exact absurd hok (SpecG.not_ok (spec_shortG hfork hs (gas := gas + 46) (by omega))
      halted_true_error (at_sh start 46) within hrun)
  · exact absurd hok (SpecG.not_ok (spec_unknownG hfork hs hsize' hunk (gas := gas + 773)
      (by omega)) halted_true_error (at_sh start 773) within hrun)
  · refine ⟨hs, ?_, i, hi⟩
    by_cases hv : message.value = 0
    · exact hv
    exact absurd hok (SpecG.not_ok (nonpayableG hfork hs hsize' i hi hv
      (gas := gas + (87 + 22 * (i.val + 1))) (by omega)) halted_true_error
      (at_sh start _) within hrun)

end UsdtVerify.Complete
