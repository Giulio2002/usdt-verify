import UsdtVerify.Functions.Common

/-!
# The fallback: a call that names no function

TetherToken (Solidity 0.4.17) has no fallback function. Read off the bytecode:

- At 5, `PUSH1 4 CALLDATASIZE LT PUSH2 0x0196 JUMPI` sends a call with fewer than 4 bytes of call
  data to 406.
- The selector table (54 to 405) falls through to 406 when no entry has the selector.
- At 406, `JUMPDEST PUSH1 0 DUP1 REVERT`: the run reverts with no output.

Neither path checks the call value: a call with value that names no function also reverts.

- `spec_unknown`: 4 bytes or more whose first four are no key of the table ⇒ REVERT, no output,
  state and substate unchanged, gas 773 (`62 + 22 * 32` through the table, then 7).
- `spec_short`: fewer than 4 bytes ⇒ REVERT, no output, state and substate unchanged, gas 46.
-/

namespace UsdtVerify.Fallback

open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate}

/-- The block at 406: `JUMPDEST PUSH1 0 DUP1 REVERT`, a revert with no output. -/
theorem revert406 (hfork : .berlin ≤ fork) {rest : List U256} (hrest : rest.length ≤ 16)
    {M : ByteArray} {gas : Nat} (hg : 7 ≤ gas) :
    Spec fork (At CODE message 406 rest M gas state substate)
      (Halted true .empty (gas - 7) state substate) := by
  have hz : extendMemory M.size [((0 : U256), (0 : U256))] = ⟨0, 0⟩ := by
    simp [extendMemory]
  step jumpdestR
  step pushR 1 (0 : U256)
  step dupR 0
  refine (Logic.revert (Nat.le_trans (by decide) hfork) (by code_fact)
    (by code_fact) (by rw [hz]; gas_ok)).consequence (fun _ h => h) ?_
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  refine ⟨hr, he, ?_, ?_, hs, hss⟩
  · rw [ho]; simp [memoryReadBytes]
  · rw [hgas, hz]; gas_ok

/-- A call of 4 bytes or more whose selector is no key of the table: the table falls through to
406 and the run reverts with no output, for any call value. -/
theorem spec_unknown (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256)
    (hunk : BitVec.ofNat 256 (selector message.data) ∉ ENTRIES.map Prod.fst)
    {gas : Nat} (hg : 773 ≤ gas) :
    Spec fork (At CODE message 0 [] .empty gas state substate)
      (Halted true .empty (gas - 773) state substate) := by
  have hne : ∀ e ∈ ENTRIES, e.1 ≠ BitVec.ofNat 256 (selector message.data) := by
    intro e he heq
    exact hunk (List.mem_map.mpr ⟨e, he, heq⟩)
  have ht := tested_of_forall_ne hne
  have hb := branch_of_forall_ne (pc := 54) (size := entrySize 4 2) hne
  have hlen : ENTRIES.length = 32 := rfl
  rw [hlen] at ht hb
  have h1 := dispatch (state := state) (substate := substate) hsize hsize' (gas := gas)
    (by rw [ht]; omega)
  rw [ht, hb] at h1
  refine Spec.seq (h1.seq (repc (pc' := 406) (by decide))) ?_
  refine (revert406 hfork (by simp) (by omega)).consequence (fun _ h => h) ?_
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  exact ⟨hr, he, ho, by rw [hgas]; omega, hs, hss⟩

/-- A call with fewer than 4 bytes of call data: the prelude jumps to 406 and the run reverts
with no output, for any call value. -/
theorem spec_short (hfork : .berlin ≤ fork) (hsize : message.data.size < 4)
    {gas : Nat} (hg : 46 ≤ gas) :
    Spec fork (At CODE message 0 [] .empty gas state substate)
      (Halted true .empty (gas - 46) state substate) := by
  have hext : extendMemory ByteArray.empty.size [((BitVec.ofNat 256 (0x40 : UInt8).toNat : U256),
      (32 : U256))] = ⟨9, 96⟩ := by decide
  step push1R 0x60
  step push1R 0x40
  step mstore (by code_fact) (by code_fact) (by simp only [hext]; omega)
  step reshape rfl (by rw [hext]) (show _ = gas - 18 by simp only [hext]; omega)
  step push1R 0x04
  step Logic.calldatasize (by code_fact) (by code_fact) (by gas_ok) (by stk_ok)
  step binR 0x10 Local.instruction_lt
  step pushR 2 0x0196
  step jumpiR (by
    have h4 : (BitVec.ofNat 256 (UInt8.toNat 4) : U256).toNat = 4 := by decide
    simp only [lessThan, h4, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show message.data.size < 2 ^ 256 by omega)]
    rw [ite_eq_left hsize]
    decide)
  refine (repc (pc' := 406) (by decide)).seq ?_
  refine (revert406 hfork (by simp) (by gas_ok)).consequence (fun _ h => h) ?_
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  exact ⟨hr, he, ho, by rw [hgas]; gas_ok, hs, hss⟩

/-- `spec_unknown` for the interpreter loop. -/
theorem runFrame_unknown (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256)
    (hunk : BitVec.ofNat 256 (selector message.data) ∉ ENTRIES.map Prod.fst)
    {gas : Nat} (hg : 773 ≤ gas)
    {bound : Nat} {runChild : MessageRunner fork Nat bound} {evm : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    ∃ stopped, runFrame (step fork) (step_decreases fork) bound runChild evm within =
      .ok stopped ∧ (Halted true .empty (gas - 773) state substate) stopped :=
  (spec_unknown hfork hsize hsize' hunk hg).runFrame start within

/-- `spec_short` for the interpreter loop. -/
theorem runFrame_short (hfork : .berlin ≤ fork) (hsize : message.data.size < 4)
    {gas : Nat} (hg : 46 ≤ gas)
    {bound : Nat} {runChild : MessageRunner fork Nat bound} {evm : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    ∃ stopped, runFrame (step fork) (step_decreases fork) bound runChild evm within =
      .ok stopped ∧ (Halted true .empty (gas - 46) state substate) stopped :=
  (spec_short hfork hsize hg).runFrame start within

end UsdtVerify.Fallback
