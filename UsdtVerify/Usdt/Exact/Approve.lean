import UsdtVerify.Usdt.Exact.Getters
import UsdtVerify.Usdt.Complete.Approve

/-!
# Exact success condition of approve, not deprecated

From Berlin, a fresh frame of `CODE` at pc 0 with call data below `2^256` bytes, the selector
0x095ea7b3 and byte 20 of slot 10 equal to 0 (`hdep`), any gas bound and any message runner.

- `approve_ok_iff`: with the gas of the success path (`approveCost`, and `approveStip`, more than
  2300 gas left at the SSTORE), the run ends with no error if and only if `ApproveGuard` holds.
- `approve_low`: with less gas than `approveCost`, no run ends with no error.
  A gas between `approveCost` and `approveStip` is not covered.
-/

namespace UsdtVerify.Exact

open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open UsdtVerify.Gas
open Complete Approve

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate} {bound : Nat} {runChild : MessageRunner fork Nat bound}
  {evm : Evm fork Nat} {gas : Nat}

/-- The cost of the success path of `approve(s, v)`: for `v = 0` the write of 0 over the
allowance, otherwise the write of `v` over an allowance of 0 (after one more read). -/
abbrev approveCost (fork : Fork) (state : State.TransactionState) (message : Message fork)
    (c10 cA : Bool) : Nat :=
  if wordArg message.data 1 = 0 then
    2560 + slotCost c10 + Gas.writeCost fork
      (originalAt state message.currentTarget (allowArg message))
      (storageAt state message.currentTarget (allowArg message)) 0 cA
  else
    2753 + slotCost c10 + slotCost cA + Gas.writeCost fork
      (originalAt state message.currentTarget (allowArg message)) 0
      (wordArg message.data 1) false

/-- The gas that the success path of `approve(s, v)` needs so that more than 2300 is left at its
SSTORE. -/
abbrev approveStip (message : Message fork) (c10 cA : Bool) : Nat :=
  if wordArg message.data 1 = 0 then 2997 + slotCost c10 else 3190 + slotCost c10 + slotCost cA

section

variable (hfork : .berlin ≤ fork) (hsize' : message.data.size < 2 ^ 256)
  (start : At CODE message 0 [] .empty gas state substate evm)
  (within : GasMeter.gasHeld evm.gas ≤ bound)
  (hsel : selector message.data = 0x095ea7b3)
  (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
  {c10 cA : Bool} (hc10 : coldIn substate message.currentTarget 10 = c10)
  (hcA : coldIn (accessSlot substate message.currentTarget 10) message.currentTarget
    (allowArg message) = cA)
include hfork hsize' start hsel hdep hc10 hcA

theorem approve_comp (s : Evm fork Nat)
    (hs : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) : ApproveGuard state message := by
  obtain ⟨hst, hacc, hl, -, h⟩ := ok_approve hfork hsize' hsel hdep hc10 hcA start within hs hok
  refine ⟨callOk_of_run hfork hsize' start within s hs hok, ⟨hst, hacc⟩, hl, fun hz => ?_⟩
  rcases h with ⟨h0, -⟩ | ⟨-, ha, -⟩
  · exact absurd h0 hz
  · exact ha

/-- `approve(s, v)`, not deprecated, succeeds exactly when `ApproveGuard` holds, with the gas of its
success path. -/
theorem approve_ok_iff (hstip : approveStip message c10 cA ≤ gas)
    (hg : approveCost fork state message c10 cA ≤ gas) :
    RunsOk fork bound runChild evm within ↔ ApproveGuard state message := by
  refine runsOk_iff (Q := fun e => e.error = none) (fun ⟨⟨h4, hv⟩, ⟨hst, hacc⟩, hl, ha⟩ => ?_)
    (fun _ h => h) start within (approve_comp hfork hsize' start within hsel hdep hc10 hcA)
  by_cases hz : wordArg message.data 1 = 0
  · simp only [approveCost, approveStip, hz, ↓reduceIte] at hg hstip
    exact (spec_zero hfork hst hacc hl hsize' hsel hv hdep hz hc10 hcA hstip hg).consequence
      (fun _ h => h) halted_false_ok
  · simp only [approveCost, approveStip, hz, ↓reduceIte] at hg hstip
    exact (spec_set hfork hst hacc hl hsize' hsel hv hdep hz (ha hz) hc10 hcA hstip
      hg).consequence (fun _ h => h) halted_false_ok

theorem approve_low (hg : gas < approveCost fork state message c10 cA) :
    ¬ RunsOk fork bound runChild evm within := by
  by_cases hz : wordArg message.data 1 = 0
  · simp only [approveCost, hz, ↓reduceIte] at hg
    exact not_runsOk_low2 hg (fun ⟨⟨h4, hv⟩, ⟨hst, hacc⟩, hl, _⟩ _ =>
        spec_zero hfork hst hacc hl hsize' hsel hv hdep hz hc10 hcA)
      start within (approve_comp hfork hsize' start within hsel hdep hc10 hcA)
  · simp only [approveCost, hz, ↓reduceIte] at hg
    exact not_runsOk_low2 hg (fun ⟨⟨h4, hv⟩, ⟨hst, hacc⟩, hl, ha⟩ _ =>
        spec_set hfork hst hacc hl hsize' hsel hv hdep hz (ha hz) hc10 hcA)
      start within (approve_comp hfork hsize' start within hsel hdep hc10 hcA)

end

end UsdtVerify.Exact
