import UsdtVerify.Usdt.Refill.Approve
import UsdtVerify.Usdt.Exact.Approve
import UsdtVerify.Evm.Shadow

/-!
# Exact success conditions over EthLib's EIP-8037 meter

EthLib runs Glamsterdam transactions with the meter `StateGasMeter`. The theorems here are about
the loop of the interpreter over that meter, for any gas bound and message runner, from a frame
`m` whose `toNat` (its fields, with its execution gas left as the gas) is the fresh frame of `CODE`
with `gas` gas.

- `ok_approve_any`: a run of `approve` that ends with no error meets `ApproveGuard`, and its
  output, state and substate are those of `ok_approve`. Any reservoir; SSTORE may refill.
- `approve_iff_gas_sgm`: with reservoir 0, and when the write of the allowance refills nothing
  (`hnr`), the run ends with no error if and only if `ApproveGuard` holds and the gas is at least
  the larger of `approveCost` and `approveStip`.
- `approve_ok_sgm`: in that case, the execution gas left is `gas - approveCost`.

The write of `approve(s, v)` refills, from Glamsterdam, exactly when `v = 0`, the allowance slot
was 0 at the start of the transaction, and it is not 0 at the call (`sstoreStateRefill`).
-/

namespace UsdtVerify.Exact

open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open UsdtVerify.Gas
open UsdtVerify.Meter
open UsdtVerify.Refill
open UsdtVerify.Shadow
open Complete Approve

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate} {bound : Nat} {runChild : MessageRunner fork StateGasMeter bound}
  {m s : Evm fork StateGasMeter} {gas : Nat}

/-- **approve over the EIP-8037 meter, any reservoir.** A run of the loop over `StateGasMeter`
from `m`, for any gas bound and message runner, that ends with no error meets `ApproveGuard`;
its output is empty, and its state and substate are those of the path of `ok_approve`. -/
theorem ok_approve_any (hfork : .berlin ≤ fork) (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x095ea7b3)
    (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    (start : At CODE message 0 [] .empty gas state substate (toNat m))
    {within : GasMeter.gasHeld m.gas ≤ bound}
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild m within = .ok s)
    (hok : s.error = none) :
    ApproveGuard state message ∧ s.output = .empty ∧
      ((wordArg message.data 1 = 0 ∧
        s.state = writeSlot (readSlot state message.currentTarget 10) message.currentTarget
          (allowArg message) 0 ∧
        s.substate = { storeSub fork (accessSlot substate message.currentTarget 10)
            message.currentTarget (allowArg message)
            (originalAt state message.currentTarget (allowArg message))
            (storageAt state message.currentTarget (allowArg message)) 0 with
          logs := substate.logs.push (approvalLog message.currentTarget
            (bitwiseAnd ADDR_MASK message.caller.toU256)
            (bitwiseAnd ADDR_MASK (addrArg message.data 0)) 0) }) ∨
      (wordArg message.data 1 ≠ 0 ∧
        s.state = writeSlot (readSlot (readSlot state message.currentTarget 10)
          message.currentTarget (allowArg message)) message.currentTarget (allowArg message)
          (wordArg message.data 1) ∧
        s.substate = { storeSub fork (accessSlot (accessSlot substate message.currentTarget 10)
              message.currentTarget (allowArg message)) message.currentTarget
            (allowArg message) (originalAt state message.currentTarget (allowArg message)) 0
            (wordArg message.data 1) with
          logs := substate.logs.push (approvalLog message.currentTarget
            (bitwiseAnd ADDR_MASK message.caller.toU256)
            (bitwiseAnd ADDR_MASK (addrArg message.data 0)) (wordArg message.data 1)) })) := by
  obtain ⟨G, hE⟩ := shadow_ends hfork hrun hok
  have st' := at_sh start (budget m)
  obtain ⟨h4, hv, -⟩ := ends_ok_dispatch hfork hsize' st' hE hok
  obtain ⟨hst, hacc, hl, ho, h⟩ := ok_approve hfork hsize' hsel hdep rfl rfl st' hE hok
  refine ⟨⟨⟨h4, hv⟩, ⟨hst, hacc⟩, hl, fun hz => ?_⟩, ho, ?_⟩
  · rcases h with ⟨h0, -⟩ | ⟨-, ha, -⟩
    · exact absurd h0 hz
    · exact ha
  · rcases h with ⟨h0, -, hs, hss⟩ | ⟨h0, -, -, hs, hss⟩
    · exact .inl ⟨h0, hs, hss⟩
    · exact .inr ⟨h0, hs, hss⟩

section

variable (hfork : .berlin ≤ fork) (hsize' : message.data.size < 2 ^ 256)
  (hsel : selector message.data = 0x095ea7b3)
  (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
  {c10 cA : Bool} (hc10 : coldIn substate message.currentTarget 10 = c10)
  (hcA : coldIn (accessSlot substate message.currentTarget 10) message.currentTarget
    (allowArg message) = cA)
  (start : At CODE message 0 [] .empty gas state substate (toNat m))
  (hres : m.gas.reservoir = 0)
  (hnr : sstoreStateRefill fork (originalAt state message.currentTarget (allowArg message))
    (storageAt state message.currentTarget (allowArg message)) (wordArg message.data 1) = 0)
include hfork hsize' hsel hdep hc10 hcA start hres hnr

omit start hres in
/-- The success path of `approve` over `StepI`, under `ApproveGuard`, with at least the larger of
`approveCost` and `approveStip` gas. -/
theorem approve_specI (hG : ApproveGuard state message) {g : Nat}
    (hm : max (approveCost fork state message c10 cA) (approveStip message c10 cA) ≤ g) :
    HoareI fork (At CODE message 0 [] .empty g state substate)
      (fun e => e.running = false ∧
        Halted false .empty (g - approveCost fork state message c10 cA)
          e.state e.substate e) := by
  obtain ⟨⟨h4, hv⟩, ⟨hst, hacc⟩, hl, ha⟩ := hG
  obtain ⟨hc, hs⟩ := Nat.max_le.mp hm
  by_cases hz : wordArg message.data 1 = 0
  · simp only [approveCost, approveStip, hz, ↓reduceIte] at hc hs
    refine (spec_zeroI hfork hst hacc hl hsize' hsel hv hdep hz hc10 hcA hs hc
      (by rw [hz] at hnr; exact hnr)).consequence (fun _ h => h) ?_
    rintro e ⟨hr, h1, h2, h3, h4, -, -⟩
    simp only [approveCost, hz, ↓reduceIte]
    exact ⟨hr, h1, h2, h3, h4, rfl, rfl⟩
  · simp only [approveCost, approveStip, hz, ↓reduceIte] at hc hs
    refine (spec_setI hfork hst hacc hl hsize' hsel hv hdep hz (ha hz) hc10 hcA hs
      hc).consequence (fun _ h => h) ?_
    rintro e ⟨hr, h1, h2, h3, h4, -, -⟩
    simp only [approveCost, hz, ↓reduceIte]
    exact ⟨hr, h1, h2, h3, h4, rfl, rfl⟩

/-- **approve over the EIP-8037 meter, with enough gas.** From reservoir 0, when the write of
the allowance refills nothing, under `ApproveGuard` and with at least the larger of `approveCost`
and `approveStip` gas, the loop over `StateGasMeter`, for any gas bound and message runner, ends
with no error and `gas - approveCost` execution gas left. -/
theorem approve_ok_sgm (hG : ApproveGuard state message)
    (hm : max (approveCost fork state message c10 cA) (approveStip message c10 cA) ≤ gas)
    (within : GasMeter.gasHeld m.gas ≤ bound) :
    ∃ s, Evm.runFrame (step fork) (step_decreases fork) bound runChild m within = .ok s ∧
      s.error = none ∧ s.gas.gasLeft = gas - approveCost fork state message c10 cA := by
  obtain ⟨s, hs, -, he, -, hg, -⟩ := runFrame_of_specI
    (approve_specI hfork hsize' hsel hdep hc10 hcA hnr hG hm) start hres within
  exact ⟨s, hs, he, hg⟩

/-- **approve over the EIP-8037 meter: the exact success condition.** From reservoir 0, when the
write of the allowance refills nothing (`hnr`), the loop over `StateGasMeter`, for any gas bound
and message runner, ends with no error if and only if `ApproveGuard` holds and the gas is at least
the larger of `approveCost` and `approveStip`. -/
theorem approve_iff_gas_sgm (within : GasMeter.gasHeld m.gas ≤ bound) :
    RunsOkS fork bound runChild m within ↔ ApproveGuard state message ∧
      max (approveCost fork state message c10 cA) (approveStip message c10 cA) ≤ gas := by
  constructor
  · rintro ⟨s, hs, hok⟩
    have hG := (ok_approve_any hfork hsize' hsel hdep start hs hok).1
    have hE : Ends fork (toNat m) (toNat s) :=
      ends_of_specI (approve_specI hfork hsize' hsel hdep hc10 hcA hnr hG
        (g := gas + max (approveCost fork state message c10 cA) (approveStip message c10 cA))
        (Nat.le_add_left _ _)) (at_sh start _) hres hs
    refine ⟨hG, Nat.max_le.mpr ⟨?_, ?_⟩⟩
    · obtain ⟨-, -, -, -, h⟩ := ok_approve hfork hsize' hsel hdep hc10 hcA start hE hok
      by_cases hz : wordArg message.data 1 = 0
      · simp only [approveCost, hz, ↓reduceIte]
        rcases h with ⟨-, ⟨hc, -⟩, -⟩ | ⟨h0, -⟩
        · exact hc
        · exact absurd hz h0
      · simp only [approveCost, hz, ↓reduceIte]
        rcases h with ⟨h0, -⟩ | ⟨-, -, ⟨hc, -⟩, -⟩
        · exact absurd h0 hz
        · exact hc
    · obtain ⟨⟨h4, hv⟩, -, hl, ha⟩ := hG
      refine Nat.le_of_not_lt fun hlt => ?_
      by_cases hz : wordArg message.data 1 = 0
      · simp only [approveStip, hz, ↓reduceIte] at hlt
        by_cases hlo : 696 + slotCost c10 ≤ gas
        · exact no_ok_stuck_atE (bad_zero hfork hl hsize' hsel hv hdep hz hc10
            (.of_low hfork (by omega)) hlo) start hE hok
        · obtain ⟨-, -, -, -, h⟩ := ok_approve hfork hsize' hsel hdep hc10 hcA start hE hok
          rcases h with ⟨-, ⟨hc, -⟩, -⟩ | ⟨h0, -⟩
          · omega
          · exact h0 hz
      · simp only [approveStip, hz, ↓reduceIte] at hlt
        by_cases hlo : 889 + slotCost c10 + slotCost cA ≤ gas
        · exact no_ok_stuck_atE (bad_set hfork hl hsize' hsel hv hdep hz (ha hz) hc10 hcA
            (.of_low hfork (by omega)) hlo) start hE hok
        · obtain ⟨-, -, -, -, h⟩ := ok_approve hfork hsize' hsel hdep hc10 hcA start hE hok
          rcases h with ⟨h0, -⟩ | ⟨-, -, ⟨hc, -⟩, -⟩
          · exact hz h0
          · omega
  · rintro ⟨hG, hm⟩
    obtain ⟨s, hs, he, -⟩ := approve_ok_sgm hfork hsize' hsel hdep hc10 hcA start hres hnr hG hm
      within
    exact ⟨s, hs, he⟩

end

end UsdtVerify.Exact
