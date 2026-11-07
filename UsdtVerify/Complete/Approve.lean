import UsdtVerify.Complete.Exact
import UsdtVerify.Functions.ApproveRevert

/-!
# Completeness of approve(address spender, uint256 v), not deprecated

Every run of an `approve` call (selector 0x095ea7b3) that ends with no error, for any gas, gas
bound and message runner, with the contract not deprecated, is one of the two success paths:
`Approve.spec_zero` (`v = 0`) or `Approve.spec_set` (`v ≠ 0` and the allowance was 0), with the
exact output, gas, state and substate. The checks that the run passed are part of the
conclusion: call data of at least 68 bytes, and for `v ≠ 0` an allowance of 0.

The other cases are excluded by the reverts `Approve.spec_payload` (call data shorter than 68
bytes) and `Approve.spec_revert` (`v ≠ 0` over a nonzero allowance).

Hypotheses beyond the call: Berlin ≤ fork < Glamsterdam, the frame is not static (`hstatic`),
and the contract has an account (`hacc`); the write of the success paths needs both.
-/

namespace UsdtVerify.Complete

open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open UsdtVerify.Gas
open Transfer TransferOk Approve

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate} {bound : Nat} {runChild : MessageRunner fork Nat bound}
  {evm s : Evm fork Nat} {gas : Nat}

/-- Every successful `approve(s, v)` call, not deprecated, is the `v = 0` or the `v ≠ 0` path. -/
theorem ok_approve (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    (hstatic : message.isStatic = false) (hacc : hasAccount state message.currentTarget)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x095ea7b3)
    (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    {c10 cA : Bool} (hc10 : coldIn substate message.currentTarget 10 = c10)
    (hcA : coldIn (accessSlot substate message.currentTarget 10) message.currentTarget
      (allowArg message) = cA)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) :
    68 ≤ message.data.size ∧ s.output = .empty ∧
      ((wordArg message.data 1 = 0 ∧
        s.gas = gas - (2560 + slotCost c10 + sstoreCost fork
          (originalAt state message.currentTarget (allowArg message))
          (storageAt state message.currentTarget (allowArg message)) 0 cA) ∧
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
        storageAt state message.currentTarget (allowArg message) = 0 ∧
        s.gas = gas - (2753 + slotCost c10 + slotCost cA + sstoreCost fork
          (originalAt state message.currentTarget (allowArg message)) 0
          (wordArg message.data 1) false) ∧
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
  obtain ⟨h4, hv, -⟩ := runFrame_ok_dispatch hfork hsize' start within hrun hok
  by_cases hl : message.data.size < 68
  · exact (no_ok (fun g hg => spec_payload hfork h4 hl hsel hv hg)
      (fun _ e h => halted_true_error e h) start within hrun hok).elim
  have hl : 68 ≤ message.data.size := by omega
  by_cases hz : wordArg message.data 1 = 0
  · obtain ⟨-, -, ho, hg, hst, hss⟩ := ok_exact (Nat.le_add_left _ _)
      (B := (2997 + slotCost c10) + (2560 + slotCost c10 + sstoreCost fork
          (originalAt state message.currentTarget (allowArg message))
          (storageAt state message.currentTarget (allowArg message)) 0 cA))
      (fun g hg => spec_zero hfork hglam hstatic hacc hl hsize' hsel hv hdep hz hc10 hcA
        (le_l hg) (le_r hg))
      start within hrun hok
    exact ⟨hl, ho, .inl ⟨hz, hg, hst, hss⟩⟩
  by_cases ha : storageAt state message.currentTarget (allowArg message) ≠ 0
  · exact (no_ok (fun g hg => spec_revert hfork hl hsize' hsel hv hdep hz ha hc10 hcA hg)
      (fun _ e h => halted_true_error e h) start within hrun hok).elim
  have ha : storageAt state message.currentTarget (allowArg message) = 0 := by
    simpa using ha
  obtain ⟨-, -, ho, hg, hst, hss⟩ := ok_exact (Nat.le_add_left _ _)
    (B := (3190 + slotCost c10 + slotCost cA) + (2753 + slotCost c10 + slotCost cA + sstoreCost fork
        (originalAt state message.currentTarget (allowArg message)) 0
        (wordArg message.data 1) false))
    (fun g hg => spec_set hfork hglam hstatic hacc hl hsize' hsel hv hdep hz ha hc10 hcA
      (le_l hg) (le_r hg))
    start within hrun hok
  exact ⟨hl, ho, .inr ⟨hz, ha, hg, hst, hss⟩⟩

end UsdtVerify.Complete
