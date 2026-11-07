import UsdtVerify.Complete.Exact
import UsdtVerify.Functions.TotalSupply
import UsdtVerify.Functions.BalanceOf

/-!
# Completeness of totalSupply() and balanceOf(address), not deprecated

From Berlin, a fresh frame of `CODE` at pc 0 with call data below `2^256` bytes, any gas, any
gas bound and any message runner. If the selector is that of the function, byte 20 of slot 10
(the `deprecated` flag) is 0, and the loop of the interpreter ends with no error, then the run is
the path of `TotalSupply.spec` / `BalanceOf.spec`: the output, the exact gas left, the state and
the substate are those of the specification (each read priced cold or warm as the substate
says). The call value and the size of the call data come from `runFrame_ok_dispatch`.
-/

namespace UsdtVerify.Complete

open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open UsdtVerify.Gas

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate} {bound : Nat} {runChild : MessageRunner fork Nat bound}
  {evm s : Evm fork Nat} {gas : Nat}

/-- Every successful `totalSupply()` call, not deprecated, returns slot 1 with the exact gas. -/
theorem ok_totalSupply (hfork : .berlin ≤ fork) (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x18160ddd)
    (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) :
    s.output = wordBytes (storageAt state message.currentTarget 1) ∧
      s.gas = gas - (TotalSupply.COST + slotCost (coldIn substate message.currentTarget 10) +
        slotCost (coldIn substate message.currentTarget 1)) ∧
      s.state = readSlot (readSlot state message.currentTarget 10) message.currentTarget 1 ∧
      s.substate = accessSlot (accessSlot substate message.currentTarget 10)
        message.currentTarget 1 := by
  obtain ⟨h4, hv, -⟩ := runFrame_ok_dispatch hfork hsize' start within hrun hok
  obtain ⟨-, -, ho, hg, hst, hss⟩ := ok_exact (Nat.le_refl _)
    (fun g hg => TotalSupply.spec hfork h4 hsize' hsel hv hdep rfl rfl hg) start within hrun hok
  exact ⟨ho, hg, hst, hss⟩

/-- Every successful `balanceOf(a)` call, not deprecated, returns `balances[a]` with the exact
gas. -/
theorem ok_balanceOf (hfork : .berlin ≤ fork) (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x70a08231)
    (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) :
    s.output = wordBytes (storageAt state message.currentTarget
        (BalanceOf.balanceSlot message.data)) ∧
      s.gas = gas - (BalanceOf.COST + slotCost (coldIn substate message.currentTarget 10) +
        slotCost (coldIn (accessSlot substate message.currentTarget 10) message.currentTarget
          (BalanceOf.balanceSlot message.data))) ∧
      s.state = readSlot (readSlot state message.currentTarget 10) message.currentTarget
        (BalanceOf.balanceSlot message.data) ∧
      s.substate = accessSlot (accessSlot substate message.currentTarget 10)
        message.currentTarget (BalanceOf.balanceSlot message.data) := by
  obtain ⟨h4, hv, -⟩ := runFrame_ok_dispatch hfork hsize' start within hrun hok
  obtain ⟨-, -, ho, hg, hst, hss⟩ := ok_exact (Nat.le_refl _)
    (fun g hg => BalanceOf.spec hfork h4 hsize' hsel hv hdep rfl rfl hg) start within hrun hok
  exact ⟨ho, hg, hst, hss⟩

end UsdtVerify.Complete
