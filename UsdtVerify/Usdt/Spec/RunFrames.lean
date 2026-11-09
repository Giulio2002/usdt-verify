import UsdtVerify.Usdt.Spec.Issue

/-!
# runFrame forms of `spec_issue` and `spec_redeem`

`runFrame_issue` and `runFrame_redeem` state `spec_issue` and `spec_redeem` for the interpreter
loop `runFrame`, for every gas bound and message runner (EthLib's `Spec.runFrame`). Every other
specification gives its `runFrame` form the same way, by one application of `Spec.runFrame`.
-/

namespace UsdtVerify.IssueSpec

open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts
open Transfer TransferOk Owner Admin BlackList Issue

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate}

/-- `spec_issue` for the interpreter loop. -/
theorem runFrame_issue (hfork : .berlin ≤ fork)
    (hstatic : message.isStatic = false) (hacc : hasAccount state message.currentTarget)
    (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xcc872b66)
    (hv : message.value = 0) (hown : callerWord message = ownerOf state message.currentTarget)
    (hT : 0 < (wordArg message.data 0).toNat ∧
      (storageAt state message.currentTarget 1).toNat + (wordArg message.data 0).toNat < 2 ^ 256)
    (hB : (storageAt state message.currentTarget (ownerBal state message.currentTarget)).toNat +
        (wordArg message.data 0).toNat < 2 ^ 256)
    {c0 c1 cO : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hc1 : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget 1 = c1)
    (hcO : coldIn (accessSlot (accessSlot substate message.currentTarget 0) message.currentTarget 1)
      message.currentTarget (ownerBal state message.currentTarget) = cO)
    {gas : Nat}
    (hstip : 4248 + slotCost c0 + slotCost c1 + slotCost cO + issueCostO fork state message ≤ gas)
    (hg : 3024 + slotCost c0 + slotCost c1 + slotCost cO + issueCostO fork state message +
      issueCostT fork state message ≤ gas)
    {bound : Nat} {runChild : MessageRunner fork Nat bound} {evm : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    ∃ stopped, runFrame (step fork) (step_decreases fork) bound runChild evm within =
      .ok stopped ∧
      (Halted false .empty (gas - (3024 + slotCost c0 + slotCost c1 + slotCost cO +
            issueCostO fork state message + issueCostT fork state message))
          (issueState state message) (issueSub fork substate state message)) stopped :=
  (spec_issue hfork hstatic hacc hsize hsize' hsel hv hown hT hB hc0 hc1 hcO hstip hg).runFrame start within

/-- `spec_redeem` for the interpreter loop. -/
theorem runFrame_redeem (hfork : .berlin ≤ fork)
    (hstatic : message.isStatic = false) (hacc : hasAccount state message.currentTarget)
    (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xdb006a75)
    (hv : message.value = 0) (hown : callerWord message = ownerOf state message.currentTarget)
    (hT : (wordArg message.data 0).toNat ≤ (storageAt state message.currentTarget 1).toNat)
    (hB : (wordArg message.data 0).toNat ≤
      (storageAt state message.currentTarget (ownerBal state message.currentTarget)).toNat)
    {c0 c1 cO : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hc1 : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget 1 = c1)
    (hcO : coldIn (accessSlot (accessSlot substate message.currentTarget 0) message.currentTarget 1)
      message.currentTarget (ownerBal state message.currentTarget) = cO)
    {gas : Nat}
    (hstip : 3838 + slotCost c0 + slotCost c1 + slotCost cO + redeemCostT fork state message ≤ gas)
    (hg : 2614 + slotCost c0 + slotCost c1 + slotCost cO + redeemCostT fork state message +
      redeemCostO fork state message ≤ gas)
    {bound : Nat} {runChild : MessageRunner fork Nat bound} {evm : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    ∃ stopped, runFrame (step fork) (step_decreases fork) bound runChild evm within =
      .ok stopped ∧
      (Halted false .empty (gas - (2614 + slotCost c0 + slotCost c1 + slotCost cO +
            redeemCostT fork state message + redeemCostO fork state message))
          (redeemState state message) (redeemSub fork substate state message)) stopped :=
  (spec_redeem hfork hstatic hacc hsize hsize' hsel hv hown hT hB hc0 hc1 hcO hstip hg).runFrame start within

end UsdtVerify.IssueSpec
