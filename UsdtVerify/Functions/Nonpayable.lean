import UsdtVerify.Functions.Common

/-!
# The nonpayable revert

Every entry of the selector table starts with the same eleven bytes, a copy per function:
`JUMPDEST CALLVALUE ISZERO PUSH2 (entry + 11) JUMPI PUSH1 0 DUP1 REVERT`.
With a nonzero call value the JUMPI falls through and the run reverts with no output.

- `valueRevert`: the block at any of the 32 destinations of the table.
- `spec` / `runFrame_spec`: from pc 0, a call whose selector is the key of entry `i` of the table
  and whose value is not 0 reverts, with no output, the state and substate unchanged, and
  `87 + 22 * (i + 1)` gas spent.
-/

namespace UsdtVerify.Nonpayable

open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate}

/-- The destinations of the selector table, the entry points of the 32 functions. -/
def DESTS : List Nat := ENTRIES.map (·.2.toNat)

/-- At each entry point, a call with a nonzero value reverts with no output for 25 gas. -/
theorem valueRevert (hfork : .berlin ≤ fork) {e : Nat} (he : e ∈ DESTS)
    (hv : message.value ≠ 0) {x : U256} {gas : Nat} (hg : 25 ≤ gas) :
    Gas.SpecG fork (At CODE message e [x] MEM0 gas state substate)
      (Halted true .empty (gas - 25) state substate) := by
  have hz : extendMemory MEM0.size [((0 : U256), (0 : U256))] = ⟨0, 0⟩ := by
    rw [size_MEM0]; decide
  have hc : isZero message.value = 0 := by
    unfold isZero
    split
    · contradiction
    · rfl
  simp only [DESTS, ENTRIES, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl
  all_goals
    step jumpdestR
    step Gas.callvalueG (by code_fact) (by code_fact) (by gas_ok) (by stk_ok)
    step unR 0x15 instruction_iszero
    step pushAnyR 2
    step jumpi0R hc
    step pushR 1 (0 : U256)
    step dupR 0
    refine (Gas.revertG (Nat.le_trans (by decide) hfork) (by code_fact) (by code_fact)
      (by rw [hz]; gas_ok)).consequence (fun _ h => h) ?_
    rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
    refine ⟨hr, he, ?_, ?_, hs, hss⟩
    · rw [ho]; simp [memoryReadBytes]
    · rw [hgas, hz]; gas_ok

/-- The table tests `i + 1` entries for the key of entry `i`, and goes to its destination. -/
theorem table_entry : ∀ i : Fin 32,
    tested (BitVec.ofNat 256 (ENTRIES[i].1.toNat)) ENTRIES = i.val + 1 ∧
      branch (BitVec.ofNat 256 (ENTRIES[i].1.toNat)) 54 (entrySize 4 2) ENTRIES =
        ENTRIES[i].2.toNat := by
  decide +kernel

/-- The nonpayable revert of every function, from Berlin.

The call data has `4 ≤ size < 2^256`, its selector is the key of entry `i` of the table
(`ENTRIES`, in the order of the bytecode; see docs/MAP.md), and the call value is not 0.

Then the run reverts with empty output, before any read of storage: the state and substate are
the ones the frame started with, and the run pays `87 + 22 * (i + 1)` gas: 62 for the prelude,
22 for each entry tested, and 25 at the entry. -/
theorem spec (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (i : Fin 32)
    (hsel : selector message.data = ENTRIES[i].1.toNat) (hv : message.value ≠ 0) {gas : Nat}
    (hg : 87 + 22 * (i.val + 1) ≤ gas) :
    Gas.SpecG fork (At CODE message 0 [] .empty gas state substate)
      (Halted true .empty (gas - (87 + 22 * (i.val + 1))) state substate) := by
  obtain ⟨ht, hb⟩ := table_entry i
  rw [← hsel] at ht hb
  have h1 := dispatch (state := state) (substate := substate) hsize hsize' (gas := gas)
    (by rw [ht]; omega)
  rw [ht, hb] at h1
  have h2 := valueRevert (state := state) (substate := substate) hfork
    (e := ENTRIES[i].2.toNat) (List.mem_map.2 ⟨ENTRIES[i], List.getElem_mem _, rfl⟩) hv
    (x := BitVec.ofNat 256 (selector message.data)) (gas := gas - 62 - 22 * (i.val + 1))
    (by omega)
  refine Gas.SpecG.seq h1 (h2.consequence (fun _ h => h) ?_)
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  exact ⟨hr, he, ho, by rw [hgas]; omega, hs, hss⟩

/-- The loop of the interpreter runs a call with a nonzero value to the revert, for every bound on
the gas of messages and every runner of messages. -/
theorem runFrame_spec (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (i : Fin 32)
    (hsel : selector message.data = ENTRIES[i].1.toNat) (hv : message.value ≠ 0) {gas : Nat}
    (hg : 87 + 22 * (i.val + 1) ≤ gas) {bound : Nat}
    {runChild : MessageRunner fork Nat bound} {evm : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    ∃ stopped, runFrame (step fork) (step_decreases fork) bound runChild evm within =
      .ok stopped ∧
      Halted true .empty (gas - (87 + 22 * (i.val + 1))) state substate stopped :=
  (spec hfork hsize hsize' i hsel hv hg).runFrame start within

end UsdtVerify.Nonpayable
