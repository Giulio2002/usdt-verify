import UsdtVerify.Functions.GettersMap
import UsdtVerify.Functions.SetParamsSpec
import UsdtVerify.Functions.PauseSpec
import UsdtVerify.Functions.DeprecatedTransferFrom
import UsdtVerify.Functions.DeprecatedBalance

/-!
# runFrame wrappers of the specifications that lacked one

For each `spec_*` stated as a `Spec` from pc 0, `runFrame_*` states the same about the
interpreter loop `runFrame`, for every gas bound and message runner (EthLib's `Spec.runFrame`).
Generated from the statements of the specifications; each proof is one application.
-/

namespace UsdtVerify.Deprecated

open EthLib.Base (Fork U256 toAddressMasked)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate}

/-- `spec_depNoCode` for the interpreter loop. -/
theorem runFrame_depNoCode (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    (hsize : 4 ≤ message.data.size) (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x18160ddd) (hv : message.value = 0)
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0)
    (hcode : state.getCode (state.getAccount (upAddr state message)).codeHash = .ok .empty)
    {c10 cU : Bool} (hc10 : coldIn substate message.currentTarget 10 = c10)
    (hcU : decide (upAddr state message ∉ substate.accessedAddresses) = cU)
    {gas : Nat} (hg : 599 + slotCost c10 + accCost cU ≤ gas)
    {bound : Nat} {runChild : MessageRunner fork Nat bound} {evm : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    ∃ stopped, runFrame (step fork) (step_decreases fork) bound runChild evm within =
      .ok stopped ∧
      (Halted true .empty (gas - (599 + slotCost c10 + accCost cU)) (callState state message)
          (callSub substate state message)) stopped :=
  (spec_depNoCode hfork hglam hsize hsize' hsel hv hdep hcode hc10 hcU hg).runFrame start within

end UsdtVerify.Deprecated

namespace UsdtVerify.DeprecatedBalance

open EthLib.Base (Fork U256 toAddressMasked)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts
open Deprecated

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate}

/-- `spec_depBNoCode` for the interpreter loop. -/
theorem runFrame_depBNoCode (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    (hsize : 4 ≤ message.data.size) (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x70a08231) (hv : message.value = 0)
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0)
    (hcode : state.getCode (state.getAccount (upAddr state message)).codeHash = .ok .empty)
    {c10 cU : Bool} (hc10 : coldIn substate message.currentTarget 10 = c10)
    (hcU : decide (upAddr state message ∉ substate.accessedAddresses) = cU)
    {gas : Nat} (hg : 921 + slotCost c10 + accCost cU ≤ gas)
    {bound : Nat} {runChild : MessageRunner fork Nat bound} {evm : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    ∃ stopped, runFrame (step fork) (step_decreases fork) bound runChild evm within =
      .ok stopped ∧
      (Halted true .empty (gas - (921 + slotCost c10 + accCost cU)) (callState state message)
          (callSub substate state message)) stopped :=
  (spec_depBNoCode hfork hglam hsize hsize' hsel hv hdep hcode hc10 hcU hg).runFrame start within

end UsdtVerify.DeprecatedBalance

namespace UsdtVerify.DeprecatedTransfer

open EthLib.Base (Fork U256 toAddressMasked)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts
open Deprecated DeprecatedBalance Transfer TransferOk

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate}

/-- `spec_depTNoCode` for the interpreter loop. -/
theorem runFrame_depTNoCode (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    (hsize : 4 ≤ message.data.size) (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0xa9059cbb) (hv : message.value = 0)
    (hnp : byte20 (storageAt state message.currentTarget 0) = 0)
    (hnb : (storageAt state message.currentTarget (blackSlot message)).toNat % 256 = 0)
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0)
    (hcode : state.getCode (state.getAccount (upAddr state message)).codeHash = .ok .empty)
    {c0 cB c10 cU : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hcB : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget
      (blackSlot message) = cB)
    (hc10 : coldIn (accessSlot (accessSlot substate message.currentTarget 0) message.currentTarget
      (blackSlot message)) message.currentTarget 10 = c10)
    (hcU : decide (upAddr state message ∉ substate.accessedAddresses) = cU)
    {gas : Nat} (hg : 1354 + slotCost c0 + slotCost cB + slotCost c10 + accCost cU ≤ gas)
    {bound : Nat} {runChild : MessageRunner fork Nat bound} {evm : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    ∃ stopped, runFrame (step fork) (step_decreases fork) bound runChild evm within =
      .ok stopped ∧
      (Halted true .empty (gas - (1354 + slotCost c0 + slotCost cB + slotCost c10 + accCost cU))
          (callStateT state message) (callSubT substate state message)) stopped :=
  (spec_depTNoCode hfork hglam hsize hsize' hsel hv hnp hnb hdep hcode hc0 hcB hc10 hcU hg).runFrame start within

/-- `spec_depANoCode` for the interpreter loop. -/
theorem runFrame_depANoCode (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    (hlong : 68 ≤ message.data.size) (hsz : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x095ea7b3) (hv : message.value = 0)
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0)
    (hcode : state.getCode (state.getAccount (upAddr state message)).codeHash = .ok .empty)
    {c10 cU : Bool} (hc10 : coldIn substate message.currentTarget 10 = c10)
    (hcU : decide (upAddr state message ∉ substate.accessedAddresses) = cU)
    {gas : Nat} (hg : 721 + slotCost c10 + accCost cU ≤ gas)
    {bound : Nat} {runChild : MessageRunner fork Nat bound} {evm : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    ∃ stopped, runFrame (step fork) (step_decreases fork) bound runChild evm within =
      .ok stopped ∧
      (Halted true .empty (gas - (721 + slotCost c10 + accCost cU)) (callState state message)
          (callSub substate state message)) stopped :=
  (spec_depANoCode hfork hglam hlong hsz hsel hv hdep hcode hc10 hcU hg).runFrame start within

end UsdtVerify.DeprecatedTransfer

namespace UsdtVerify.DeprecatedTransferFrom

open EthLib.Base (Fork U256 toAddressMasked)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts
open Deprecated DeprecatedBalance DeprecatedTransfer TransferOk TransferFrom

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate}

/-- `spec_depFNoCode` for the interpreter loop. -/
theorem runFrame_depFNoCode (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    (hsize : 4 ≤ message.data.size) (hsz : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x23b872dd) (hv : message.value = 0)
    (hnp : byte20 (storageAt state message.currentTarget 0) = 0)
    (hnb : (storageAt state message.currentTarget (blackFrom (fromArg message))).toNat % 256 = 0)
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0)
    (hcode : state.getCode (state.getAccount (upAddr state message)).codeHash = .ok .empty)
    {c0 cB c10 cU : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hcB : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget
      (blackFrom (fromArg message)) = cB)
    (hc10 : coldIn (accessSlot (accessSlot substate message.currentTarget 0) message.currentTarget
      (blackFrom (fromArg message))) message.currentTarget 10 = c10)
    (hcU : decide (upAddr state message ∉ substate.accessedAddresses) = cU)
    {gas : Nat} (hg : 1090 + slotCost c0 + slotCost cB + slotCost c10 + accCost cU ≤ gas)
    {bound : Nat} {runChild : MessageRunner fork Nat bound} {evm : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    ∃ stopped, runFrame (step fork) (step_decreases fork) bound runChild evm within =
      .ok stopped ∧
      (Halted true .empty (gas - (1090 + slotCost c0 + slotCost cB + slotCost c10 + accCost cU))
          (callStateF state message) (callSubF substate state message)) stopped :=
  (spec_depFNoCode hfork hglam hsize hsz hsel hv hnp hnb hdep hcode hc0 hcB hc10 hcU hg).runFrame start within

end UsdtVerify.DeprecatedTransferFrom

namespace UsdtVerify.PauseSpec

open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts
open Owner Pause

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate}

/-- `spec_pause_notOwner` for the interpreter loop. -/
theorem runFrame_pause_notOwner (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x8456cb59)
    (hv : message.value = 0) (hown : callerWord message ≠ ownerOf state message.currentTarget)
    {c0 : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0) {gas : Nat}
    (hg : 574 + slotCost c0 ≤ gas)
    {bound : Nat} {runChild : MessageRunner fork Nat bound} {evm : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    ∃ stopped, runFrame (step fork) (step_decreases fork) bound runChild evm within =
      .ok stopped ∧
      (Halted true .empty (gas - (574 + slotCost c0)) (readSlot state message.currentTarget 0)
          (accessSlot substate message.currentTarget 0)) stopped :=
  (spec_pause_notOwner hfork hsize hsize' hsel hv hown hc0 hg).runFrame start within

/-- `spec_unpause_notOwner` for the interpreter loop. -/
theorem runFrame_unpause_notOwner (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x3f4ba83a)
    (hv : message.value = 0) (hown : callerWord message ≠ ownerOf state message.currentTarget)
    {c0 : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0) {gas : Nat}
    (hg : 464 + slotCost c0 ≤ gas)
    {bound : Nat} {runChild : MessageRunner fork Nat bound} {evm : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    ∃ stopped, runFrame (step fork) (step_decreases fork) bound runChild evm within =
      .ok stopped ∧
      (Halted true .empty (gas - (464 + slotCost c0)) (readSlot state message.currentTarget 0)
          (accessSlot substate message.currentTarget 0)) stopped :=
  (spec_unpause_notOwner hfork hsize hsize' hsel hv hown hc0 hg).runFrame start within

/-- `spec_pause_paused` for the interpreter loop. -/
theorem runFrame_pause_paused (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x8456cb59)
    (hv : message.value = 0) (hown : callerWord message = ownerOf state message.currentTarget)
    (hp : byte20 (storageAt state message.currentTarget 0) ≠ 0)
    {c0 : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0) {gas : Nat}
    (hg : 786 + slotCost c0 ≤ gas)
    {bound : Nat} {runChild : MessageRunner fork Nat bound} {evm : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    ∃ stopped, runFrame (step fork) (step_decreases fork) bound runChild evm within =
      .ok stopped ∧
      (Halted true .empty (gas - (786 + slotCost c0)) (readSlot state message.currentTarget 0)
          (accessSlot substate message.currentTarget 0)) stopped :=
  (spec_pause_paused hfork hsize hsize' hsel hv hown hp hc0 hg).runFrame start within

/-- `spec_unpause_notPaused` for the interpreter loop. -/
theorem runFrame_unpause_notPaused (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x3f4ba83a)
    (hv : message.value = 0) (hown : callerWord message = ownerOf state message.currentTarget)
    (hnp : byte20 (storageAt state message.currentTarget 0) = 0)
    {c0 : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0) {gas : Nat}
    (hg : 673 + slotCost c0 ≤ gas)
    {bound : Nat} {runChild : MessageRunner fork Nat bound} {evm : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    ∃ stopped, runFrame (step fork) (step_decreases fork) bound runChild evm within =
      .ok stopped ∧
      (Halted true .empty (gas - (673 + slotCost c0)) (readSlot state message.currentTarget 0)
          (accessSlot substate message.currentTarget 0)) stopped :=
  (spec_unpause_notPaused hfork hsize hsize' hsel hv hown hnp hc0 hg).runFrame start within

/-- `spec_pause` for the interpreter loop. -/
theorem runFrame_pause (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    (hstatic : message.isStatic = false) (hacc : hasAccount state message.currentTarget)
    (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x8456cb59)
    (hv : message.value = 0) (hown : callerWord message = ownerOf state message.currentTarget)
    (hnp : byte20 (storageAt state message.currentTarget 0) = 0)
    {c0 : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0) {gas : Nat}
    (hstip : 3297 + slotCost c0 ≤ gas)
    (hg : PAUSE_COST + slotCost c0 + flagCost fork state message 1 ≤ gas)
    {bound : Nat} {runChild : MessageRunner fork Nat bound} {evm : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    ∃ stopped, runFrame (step fork) (step_decreases fork) bound runChild evm within =
      .ok stopped ∧
      (Halted false .empty (gas - (PAUSE_COST + slotCost c0 + flagCost fork state message 1))
          (writeSlot state message.currentTarget 0
            (withPaused (storageAt state message.currentTarget 0) 1))
          { storeSub fork substate message.currentTarget 0
              (originalAt state message.currentTarget 0) (storageAt state message.currentTarget 0)
              (withPaused (storageAt state message.currentTarget 0) 1) with
            logs := substate.logs.push (log0 message.currentTarget PAUSE_TOPIC) }) stopped :=
  (spec_pause hfork hglam hstatic hacc hsize hsize' hsel hv hown hnp hc0 hstip hg).runFrame start within

/-- `spec_unpause` for the interpreter loop. -/
theorem runFrame_unpause (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    (hstatic : message.isStatic = false) (hacc : hasAccount state message.currentTarget)
    (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x3f4ba83a)
    (hv : message.value = 0) (hown : callerWord message = ownerOf state message.currentTarget)
    (hp : byte20 (storageAt state message.currentTarget 0) ≠ 0)
    {c0 : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0) {gas : Nat}
    (hstip : 3184 + slotCost c0 ≤ gas)
    (hg : UNPAUSE_COST + slotCost c0 + flagCost fork state message 0 ≤ gas)
    {bound : Nat} {runChild : MessageRunner fork Nat bound} {evm : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    ∃ stopped, runFrame (step fork) (step_decreases fork) bound runChild evm within =
      .ok stopped ∧
      (Halted false .empty (gas - (UNPAUSE_COST + slotCost c0 + flagCost fork state message 0))
          (writeSlot state message.currentTarget 0
            (withPaused (storageAt state message.currentTarget 0) 0))
          { storeSub fork substate message.currentTarget 0
              (originalAt state message.currentTarget 0) (storageAt state message.currentTarget 0)
              (withPaused (storageAt state message.currentTarget 0) 0) with
            logs := substate.logs.push (log0 message.currentTarget UNPAUSE_TOPIC) }) stopped :=
  (spec_unpause hfork hglam hstatic hacc hsize hsize' hsel hv hown hp hc0 hstip hg).runFrame start within

end UsdtVerify.PauseSpec

namespace UsdtVerify.BlackListSpec

open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts
open Transfer TransferOk Owner Admin BlackList

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate}

/-- `spec_add_notOwner` for the interpreter loop. -/
theorem runFrame_add_notOwner (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x0ecb93c0)
    (hv : message.value = 0) (hown : callerWord message ≠ ownerOf state message.currentTarget)
    {c0 : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0) {gas : Nat}
    (hg : 328 + slotCost c0 ≤ gas)
    {bound : Nat} {runChild : MessageRunner fork Nat bound} {evm : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    ∃ stopped, runFrame (step fork) (step_decreases fork) bound runChild evm within =
      .ok stopped ∧
      (Halted true .empty (gas - (328 + slotCost c0)) (readSlot state message.currentTarget 0)
          (accessSlot substate message.currentTarget 0)) stopped :=
  (spec_add_notOwner hfork hsize hsize' hsel hv hown hc0 hg).runFrame start within

/-- `spec_remove_notOwner` for the interpreter loop. -/
theorem runFrame_remove_notOwner (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xe4997dc5)
    (hv : message.value = 0) (hown : callerWord message ≠ ownerOf state message.currentTarget)
    {c0 : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0) {gas : Nat}
    (hg : 856 + slotCost c0 ≤ gas)
    {bound : Nat} {runChild : MessageRunner fork Nat bound} {evm : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    ∃ stopped, runFrame (step fork) (step_decreases fork) bound runChild evm within =
      .ok stopped ∧
      (Halted true .empty (gas - (856 + slotCost c0)) (readSlot state message.currentTarget 0)
          (accessSlot substate message.currentTarget 0)) stopped :=
  (spec_remove_notOwner hfork hsize hsize' hsel hv hown hc0 hg).runFrame start within

/-- `spec_add` for the interpreter loop. -/
theorem runFrame_add (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    (hstatic : message.isStatic = false) (hacc : hasAccount state message.currentTarget)
    (hsize : 4 ≤ message.data.size) (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x0ecb93c0) (hv : message.value = 0)
    (hown : callerWord message = ownerOf state message.currentTarget)
    {c0 cB : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hcB : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget
      (listSlot (addrArg message.data 0)) = cB) {gas : Nat}
    (hstip : 2779 + slotCost c0 + slotCost cB ≤ gas)
    (hg : 1567 + slotCost c0 + slotCost cB + listCost fork state message 1 ≤ gas)
    {bound : Nat} {runChild : MessageRunner fork Nat bound} {evm : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    ∃ stopped, runFrame (step fork) (step_decreases fork) bound runChild evm within =
      .ok stopped ∧
      (Halted false .empty (gas - (1567 + slotCost c0 + slotCost cB + listCost fork state message 1))
          (listState state message 1) (listSub fork substate state message 1 ADDED_TOPIC)) stopped :=
  (spec_add hfork hglam hstatic hacc hsize hsize' hsel hv hown hc0 hcB hstip hg).runFrame start within

/-- `spec_remove` for the interpreter loop. -/
theorem runFrame_remove (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    (hstatic : message.isStatic = false) (hacc : hasAccount state message.currentTarget)
    (hsize : 4 ≤ message.data.size) (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0xe4997dc5) (hv : message.value = 0)
    (hown : callerWord message = ownerOf state message.currentTarget)
    {c0 cB : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hcB : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget
      (listSlot (addrArg message.data 0)) = cB) {gas : Nat}
    (hstip : 3307 + slotCost c0 + slotCost cB ≤ gas)
    (hg : 2095 + slotCost c0 + slotCost cB + listCost fork state message 0 ≤ gas)
    {bound : Nat} {runChild : MessageRunner fork Nat bound} {evm : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    ∃ stopped, runFrame (step fork) (step_decreases fork) bound runChild evm within =
      .ok stopped ∧
      (Halted false .empty (gas - (2095 + slotCost c0 + slotCost cB + listCost fork state message 0))
          (listState state message 0) (listSub fork substate state message 0 REMOVED_TOPIC)) stopped :=
  (spec_remove hfork hglam hstatic hacc hsize hsize' hsel hv hown hc0 hcB hstip hg).runFrame start within

end UsdtVerify.BlackListSpec

namespace UsdtVerify.IssueSpec

open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts
open Transfer TransferOk Owner Admin BlackList Issue

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate}

/-- `spec_issue_notOwner` for the interpreter loop. -/
theorem runFrame_issue_notOwner (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xcc872b66)
    (hv : message.value = 0) (hown : callerWord message ≠ ownerOf state message.currentTarget)
    {c0 : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0) {gas : Nat}
    (hg : 740 + slotCost c0 ≤ gas)
    {bound : Nat} {runChild : MessageRunner fork Nat bound} {evm : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    ∃ stopped, runFrame (step fork) (step_decreases fork) bound runChild evm within =
      .ok stopped ∧
      (Halted true .empty (gas - (740 + slotCost c0)) (readSlot state message.currentTarget 0)
          (accessSlot substate message.currentTarget 0)) stopped :=
  (spec_issue_notOwner hfork hsize hsize' hsel hv hown hc0 hg).runFrame start within

/-- `spec_redeem_notOwner` for the interpreter loop. -/
theorem runFrame_redeem_notOwner (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xdb006a75)
    (hv : message.value = 0) (hown : callerWord message ≠ ownerOf state message.currentTarget)
    {c0 : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0) {gas : Nat}
    (hg : 762 + slotCost c0 ≤ gas)
    {bound : Nat} {runChild : MessageRunner fork Nat bound} {evm : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    ∃ stopped, runFrame (step fork) (step_decreases fork) bound runChild evm within =
      .ok stopped ∧
      (Halted true .empty (gas - (762 + slotCost c0)) (readSlot state message.currentTarget 0)
          (accessSlot substate message.currentTarget 0)) stopped :=
  (spec_redeem_notOwner hfork hsize hsize' hsel hv hown hc0 hg).runFrame start within

/-- `spec_issue_req1` for the interpreter loop. -/
theorem runFrame_issue_req1 (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xcc872b66)
    (hv : message.value = 0) (hown : callerWord message = ownerOf state message.currentTarget)
    (hT : ¬ (0 < (wordArg message.data 0).toNat ∧
      (storageAt state message.currentTarget 1).toNat + (wordArg message.data 0).toNat < 2 ^ 256))
    {c0 c1 : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hc1 : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget 1 = c1)
    {gas : Nat} (hg : 875 + slotCost c0 + slotCost c1 ≤ gas)
    {bound : Nat} {runChild : MessageRunner fork Nat bound} {evm : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    ∃ stopped, runFrame (step fork) (step_decreases fork) bound runChild evm within =
      .ok stopped ∧
      (Halted true .empty (gas - (875 + slotCost c0 + slotCost c1))
          (readSlot (readSlot state message.currentTarget 0) message.currentTarget 1)
          (accessSlot (accessSlot substate message.currentTarget 0) message.currentTarget 1)) stopped :=
  (spec_issue_req1 hfork hsize hsize' hsel hv hown hT hc0 hc1 hg).runFrame start within

/-- `spec_redeem_req1` for the interpreter loop. -/
theorem runFrame_redeem_req1 (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xdb006a75)
    (hv : message.value = 0) (hown : callerWord message = ownerOf state message.currentTarget)
    (hT : (storageAt state message.currentTarget 1).toNat < (wordArg message.data 0).toNat)
    {c0 c1 : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hc1 : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget 1 = c1)
    {gas : Nat} (hg : 794 + slotCost c0 + slotCost c1 ≤ gas)
    {bound : Nat} {runChild : MessageRunner fork Nat bound} {evm : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    ∃ stopped, runFrame (step fork) (step_decreases fork) bound runChild evm within =
      .ok stopped ∧
      (Halted true .empty (gas - (794 + slotCost c0 + slotCost c1))
          (readSlot (readSlot state message.currentTarget 0) message.currentTarget 1)
          (accessSlot (accessSlot substate message.currentTarget 0) message.currentTarget 1)) stopped :=
  (spec_redeem_req1 hfork hsize hsize' hsel hv hown hT hc0 hc1 hg).runFrame start within

/-- `spec_issue_req2` for the interpreter loop. -/
theorem runFrame_issue_req2 (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xcc872b66)
    (hv : message.value = 0) (hown : callerWord message = ownerOf state message.currentTarget)
    (hT : 0 < (wordArg message.data 0).toNat ∧
      (storageAt state message.currentTarget 1).toNat + (wordArg message.data 0).toNat < 2 ^ 256)
    (hB : ¬ (0 < (wordArg message.data 0).toNat ∧
      (storageAt state message.currentTarget (ownerBal state message.currentTarget)).toNat +
        (wordArg message.data 0).toNat < 2 ^ 256))
    {c0 c1 cO : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hc1 : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget 1 = c1)
    (hcO : coldIn (accessSlot (accessSlot substate message.currentTarget 0) message.currentTarget 1)
      message.currentTarget (ownerBal state message.currentTarget) = cO)
    {gas : Nat} (hg : 1462 + slotCost c0 + slotCost c1 + slotCost cO ≤ gas)
    {bound : Nat} {runChild : MessageRunner fork Nat bound} {evm : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    ∃ stopped, runFrame (step fork) (step_decreases fork) bound runChild evm within =
      .ok stopped ∧
      (Halted true .empty (gas - (1462 + slotCost c0 + slotCost c1 + slotCost cO))
          (reqState state message.currentTarget) (reqSub substate state message.currentTarget)) stopped :=
  (spec_issue_req2 hfork hsize hsize' hsel hv hown hT hB hc0 hc1 hcO hg).runFrame start within

/-- `spec_issue` for the interpreter loop. -/
theorem runFrame_issue (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
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
  (spec_issue hfork hglam hstatic hacc hsize hsize' hsel hv hown hT hB hc0 hc1 hcO hstip hg).runFrame start within

/-- `spec_redeem_req2` for the interpreter loop. -/
theorem runFrame_redeem_req2 (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xdb006a75)
    (hv : message.value = 0) (hown : callerWord message = ownerOf state message.currentTarget)
    (hT : (wordArg message.data 0).toNat ≤ (storageAt state message.currentTarget 1).toNat)
    (hB : (storageAt state message.currentTarget (ownerBal state message.currentTarget)).toNat <
      (wordArg message.data 0).toNat)
    {c0 c1 cO : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hc1 : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget 1 = c1)
    (hcO : coldIn (accessSlot (accessSlot substate message.currentTarget 0) message.currentTarget 1)
      message.currentTarget (ownerBal state message.currentTarget) = cO)
    {gas : Nat} (hg : 1052 + slotCost c0 + slotCost c1 + slotCost cO ≤ gas)
    {bound : Nat} {runChild : MessageRunner fork Nat bound} {evm : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    ∃ stopped, runFrame (step fork) (step_decreases fork) bound runChild evm within =
      .ok stopped ∧
      (Halted true .empty (gas - (1052 + slotCost c0 + slotCost c1 + slotCost cO))
          (reqState state message.currentTarget) (reqSub substate state message.currentTarget)) stopped :=
  (spec_redeem_req2 hfork hsize hsize' hsel hv hown hT hB hc0 hc1 hcO hg).runFrame start within

/-- `spec_redeem` for the interpreter loop. -/
theorem runFrame_redeem (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
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
  (spec_redeem hfork hglam hstatic hacc hsize hsize' hsel hv hown hT hB hc0 hc1 hcO hstip hg).runFrame start within

end UsdtVerify.IssueSpec

namespace UsdtVerify.SetParamsSpec

open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts
open Transfer TransferOk Owner Admin Issue SafeMath SetParams

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate}

/-- `spec_notOwner` for the interpreter loop. -/
theorem runFrame_notOwner (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xc0324c77)
    (hv : message.value = 0) (hown : callerWord message ≠ ownerOf state message.currentTarget)
    {c0 : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0) {gas : Nat}
    (hg : 742 + slotCost c0 ≤ gas)
    {bound : Nat} {runChild : MessageRunner fork Nat bound} {evm : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    ∃ stopped, runFrame (step fork) (step_decreases fork) bound runChild evm within =
      .ok stopped ∧
      (Halted true .empty (gas - (742 + slotCost c0)) (readSlot state message.currentTarget 0)
          (accessSlot substate message.currentTarget 0)) stopped :=
  (spec_notOwner hfork hsize hsize' hsel hv hown hc0 hg).runFrame start within

/-- `spec_bpHigh` for the interpreter loop. -/
theorem runFrame_bpHigh (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xc0324c77)
    (hv : message.value = 0) (hown : callerWord message = ownerOf state message.currentTarget)
    (hb : 20 ≤ (wordArg message.data 0).toNat)
    {c0 : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0) {gas : Nat}
    (hg : 771 + slotCost c0 ≤ gas)
    {bound : Nat} {runChild : MessageRunner fork Nat bound} {evm : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    ∃ stopped, runFrame (step fork) (step_decreases fork) bound runChild evm within =
      .ok stopped ∧
      (Halted true .empty (gas - (771 + slotCost c0)) (readSlot state message.currentTarget 0)
          (accessSlot substate message.currentTarget 0)) stopped :=
  (spec_bpHigh hfork hsize hsize' hsel hv hown hb hc0 hg).runFrame start within

/-- `spec_feeHigh` for the interpreter loop. -/
theorem runFrame_feeHigh (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xc0324c77)
    (hv : message.value = 0) (hown : callerWord message = ownerOf state message.currentTarget)
    (hb : (wordArg message.data 0).toNat < 20) (hm : 50 ≤ (wordArg message.data 1).toNat)
    {c0 : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0) {gas : Nat}
    (hg : 800 + slotCost c0 ≤ gas)
    {bound : Nat} {runChild : MessageRunner fork Nat bound} {evm : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    ∃ stopped, runFrame (step fork) (step_decreases fork) bound runChild evm within =
      .ok stopped ∧
      (Halted true .empty (gas - (800 + slotCost c0)) (readSlot state message.currentTarget 0)
          (accessSlot substate message.currentTarget 0)) stopped :=
  (spec_feeHigh hfork hsize hsize' hsel hv hown hb hm hc0 hg).runFrame start within

/-- `spec_setParams` for the interpreter loop. -/
theorem runFrame_setParams (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    (hstatic : message.isStatic = false) (hacc : hasAccount state message.currentTarget)
    (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xc0324c77)
    (hv : message.value = 0) (hown : callerWord message = ownerOf state message.currentTarget)
    (hb : (wordArg message.data 0).toNat < 20) (hm : (wordArg message.data 1).toNat < 50)
    (hov : (wordArg message.data 1).toNat *
      (exp (0x0a : U256) (storageAt state message.currentTarget 9)).toNat < 2 ^ 256)
    {c0 c3 c9 c4 : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hc3 : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget 3 = c3)
    (hc9 : coldIn (accessSlot (accessSlot substate message.currentTarget 0) message.currentTarget 3)
      message.currentTarget 9 = c9)
    (hc4 : coldIn (accessSlot (accessSlot (accessSlot substate message.currentTarget 0)
      message.currentTarget 3) message.currentTarget 9) message.currentTarget 4 = c4)
    {gas : Nat}
    (hstip : 3168 + slotCost c0 + sstoreCost fork (originalAt state message.currentTarget 3)
      (storageAt state message.currentTarget 3) (wordArg message.data 0) c3 + slotCost c9 +
      50 * exponentBytes (storageAt state message.currentTarget 9) +
      mulCost (wordArg message.data 1) ≤ gas)
    (hg : 2425 + paramsCost fork state message c0 c3 c9 c4 ≤ gas)
    {bound : Nat} {runChild : MessageRunner fork Nat bound} {evm : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    ∃ stopped, runFrame (step fork) (step_decreases fork) bound runChild evm within =
      .ok stopped ∧
      (Halted false .empty (gas - (2425 + paramsCost fork state message c0 c3 c9 c4))
          (paramsState state message) (paramsSub fork substate state message)) stopped :=
  (spec_setParams hfork hglam hstatic hacc hsize hsize' hsel hv hown hb hm hov hc0 hc3 hc9 hc4 hstip hg).runFrame start within

end UsdtVerify.SetParamsSpec

namespace UsdtVerify.AddrWriteSpec

open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts
open Transfer TransferOk Owner Admin Issue Pause BlackList BlackListSpec AddrWrite

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate}

/-- `spec_deprecate_notOwner` for the interpreter loop. -/
theorem runFrame_deprecate_notOwner (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x0753c30c)
    (hv : message.value = 0) (hown : callerWord message ≠ ownerOf state message.currentTarget)
    {c0 : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0) {gas : Nat}
    (hg : 262 + slotCost c0 ≤ gas)
    {bound : Nat} {runChild : MessageRunner fork Nat bound} {evm : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    ∃ stopped, runFrame (step fork) (step_decreases fork) bound runChild evm within =
      .ok stopped ∧
      (Halted true .empty (gas - (262 + slotCost c0)) (readSlot state message.currentTarget 0)
          (accessSlot substate message.currentTarget 0)) stopped :=
  (spec_deprecate_notOwner hfork hsize hsize' hsel hv hown hc0 hg).runFrame start within

/-- `spec_transferOwnership_notOwner` for the interpreter loop. -/
theorem runFrame_transferOwnership_notOwner (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xf2fde38b)
    (hv : message.value = 0) (hown : callerWord message ≠ ownerOf state message.currentTarget)
    {c0 : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0) {gas : Nat}
    (hg : 900 + slotCost c0 ≤ gas)
    {bound : Nat} {runChild : MessageRunner fork Nat bound} {evm : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    ∃ stopped, runFrame (step fork) (step_decreases fork) bound runChild evm within =
      .ok stopped ∧
      (Halted true .empty (gas - (900 + slotCost c0)) (readSlot state message.currentTarget 0)
          (accessSlot substate message.currentTarget 0)) stopped :=
  (spec_transferOwnership_notOwner hfork hsize hsize' hsel hv hown hc0 hg).runFrame start within

/-- `spec_transferOwnership_zero` for the interpreter loop. -/
theorem runFrame_transferOwnership_zero (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xf2fde38b)
    (hv : message.value = 0) (hown : callerWord message = ownerOf state message.currentTarget)
    (hz : addrArg message.data 0 = 0)
    {c0 : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0) {gas : Nat}
    (hg : 947 + slotCost c0 ≤ gas)
    {bound : Nat} {runChild : MessageRunner fork Nat bound} {evm : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    ∃ stopped, runFrame (step fork) (step_decreases fork) bound runChild evm within =
      .ok stopped ∧
      (Halted false .empty (gas - (947 + slotCost c0)) (readSlot state message.currentTarget 0)
          (accessSlot substate message.currentTarget 0)) stopped :=
  (spec_transferOwnership_zero hfork hsize hsize' hsel hv hown hz hc0 hg).runFrame start within

/-- `spec_transferOwnership` for the interpreter loop. -/
theorem runFrame_transferOwnership (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    (hstatic : message.isStatic = false) (hacc : hasAccount state message.currentTarget)
    (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xf2fde38b)
    (hv : message.value = 0) (hown : callerWord message = ownerOf state message.currentTarget)
    (hnz : addrArg message.data 0 ≠ 0)
    {c0 : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0) {gas : Nat}
    (hstip : 3401 + slotCost c0 ≤ gas)
    (hg : 1114 + slotCost c0 + ownCost fork state message ≤ gas)
    {bound : Nat} {runChild : MessageRunner fork Nat bound} {evm : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    ∃ stopped, runFrame (step fork) (step_decreases fork) bound runChild evm within =
      .ok stopped ∧
      (Halted false .empty (gas - (1114 + slotCost c0 + ownCost fork state message))
          (writeSlot state message.currentTarget 0
            (withAddr (storageAt state message.currentTarget 0) (addrArg message.data 0)))
          (storeSub fork substate message.currentTarget 0 (originalAt state message.currentTarget 0)
            (storageAt state message.currentTarget 0)
            (withAddr (storageAt state message.currentTarget 0) (addrArg message.data 0)))) stopped :=
  (spec_transferOwnership hfork hglam hstatic hacc hsize hsize' hsel hv hown hnz hc0 hstip hg).runFrame start within

/-- `spec_deprecate` for the interpreter loop. -/
theorem runFrame_deprecate (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    (hstatic : message.isStatic = false) (hacc : hasAccount state message.currentTarget)
    (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x0753c30c)
    (hv : message.value = 0) (hown : callerWord message = ownerOf state message.currentTarget)
    {c0 c10 : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hc10 : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget 10 = c10)
    {gas : Nat}
    (hstip : 2840 + slotCost c0 + slotCost c10 + sstoreCost fork
      (originalAt state message.currentTarget 10) (storageAt state message.currentTarget 10)
      (withPaused (storageAt state message.currentTarget 10) 1) false ≤ gas)
    (hg : 1628 + slotCost c0 + slotCost c10 + depCost fork state message ≤ gas)
    {bound : Nat} {runChild : MessageRunner fork Nat bound} {evm : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    ∃ stopped, runFrame (step fork) (step_decreases fork) bound runChild evm within =
      .ok stopped ∧
      (Halted false .empty (gas - (1628 + slotCost c0 + slotCost c10 + depCost fork state message))
          (depState state message) (depSub fork substate state message)) stopped :=
  (spec_deprecate hfork hglam hstatic hacc hsize hsize' hsel hv hown hc0 hc10 hstip hg).runFrame start within

end UsdtVerify.AddrWriteSpec

namespace UsdtVerify.Destroy

open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts
open Transfer TransferOk Owner Admin BlackList Issue

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate}

/-- `spec_notOwner` for the interpreter loop. -/
theorem runFrame_notOwner (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xf3bdc228)
    (hv : message.value = 0) (hown : callerWord message ≠ ownerOf state message.currentTarget)
    {c0 : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0) {gas : Nat}
    (hg : 925 + slotCost c0 ≤ gas)
    {bound : Nat} {runChild : MessageRunner fork Nat bound} {evm : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    ∃ stopped, runFrame (step fork) (step_decreases fork) bound runChild evm within =
      .ok stopped ∧
      (Halted true .empty (gas - (925 + slotCost c0)) (readSlot state message.currentTarget 0)
          (accessSlot substate message.currentTarget 0)) stopped :=
  (spec_notOwner hfork hsize hsize' hsel hv hown hc0 hg).runFrame start within

/-- `spec_notListed` for the interpreter loop. -/
theorem runFrame_notListed (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xf3bdc228)
    (hv : message.value = 0) (hown : callerWord message = ownerOf state message.currentTarget)
    (hnl : (storageAt state message.currentTarget (listSlot (addrArg message.data 0))).toNat % 256 = 0)
    {c0 cL : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hcL : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget
      (listSlot (addrArg message.data 0)) = cL) {gas : Nat}
    (hg : 1074 + slotCost c0 + slotCost cL ≤ gas)
    {bound : Nat} {runChild : MessageRunner fork Nat bound} {evm : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    ∃ stopped, runFrame (step fork) (step_decreases fork) bound runChild evm within =
      .ok stopped ∧
      (Halted true .empty (gas - (1074 + slotCost c0 + slotCost cL))
          (readSlot (readSlot state message.currentTarget 0) message.currentTarget
            (listSlot (addrArg message.data 0)))
          (accessSlot (accessSlot substate message.currentTarget 0) message.currentTarget
            (listSlot (addrArg message.data 0)))) stopped :=
  (spec_notListed hfork hsize hsize' hsel hv hown hnl hc0 hcL hg).runFrame start within

end UsdtVerify.Destroy

namespace UsdtVerify.Getters

open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts
open Transfer TransferOk Owner Admin BlackList Issue

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate}

/-- `spec_slot` for the interpreter loop. -/
theorem runFrame_slot (hfork : .berlin ≤ fork) {sel t e r b k : Nat}
    (hp : (sel, t, e, r, b, k) ∈ SLOT_GETTERS) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = sel)
    (hv : message.value = 0) {ck : Bool}
    (hck : coldIn substate message.currentTarget (BitVec.ofNat 256 k) = ck) {gas : Nat}
    (hg : 164 + 22 * t + slotCost ck ≤ gas)
    {bound : Nat} {runChild : MessageRunner fork Nat bound} {evm : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    ∃ stopped, runFrame (step fork) (step_decreases fork) bound runChild evm within =
      .ok stopped ∧
      (Halted false (wordBytes (storageAt state message.currentTarget (BitVec.ofNat 256 k)))
          (gas - (164 + 22 * t + slotCost ck))
          (readSlot state message.currentTarget (BitVec.ofNat 256 k))
          (accessSlot substate message.currentTarget (BitVec.ofNat 256 k))) stopped :=
  (spec_slot hfork hp hsize hsize' hsel hv hck hg).runFrame start within

/-- `spec_decimals` for the interpreter loop. -/
theorem runFrame_decimals (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x313ce567)
    (hv : message.value = 0) {c : Bool} (hc : coldIn substate message.currentTarget 9 = c)
    {gas : Nat} (hg : 384 + slotCost c ≤ gas)
    {bound : Nat} {runChild : MessageRunner fork Nat bound} {evm : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    ∃ stopped, runFrame (step fork) (step_decreases fork) bound runChild evm within =
      .ok stopped ∧
      (Halted false (wordBytes (storageAt state message.currentTarget 9)) (gas - (384 + slotCost c))
          (readSlot state message.currentTarget 9) (accessSlot substate message.currentTarget 9)) stopped :=
  (spec_decimals hfork hsize hsize' hsel hv hc hg).runFrame start within

/-- `spec_maximumFee` for the interpreter loop. -/
theorem runFrame_maximumFee (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x35390714)
    (hv : message.value = 0) {c : Bool} (hc : coldIn substate message.currentTarget 4 = c)
    {gas : Nat} (hg : 406 + slotCost c ≤ gas)
    {bound : Nat} {runChild : MessageRunner fork Nat bound} {evm : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    ∃ stopped, runFrame (step fork) (step_decreases fork) bound runChild evm within =
      .ok stopped ∧
      (Halted false (wordBytes (storageAt state message.currentTarget 4)) (gas - (406 + slotCost c))
          (readSlot state message.currentTarget 4) (accessSlot substate message.currentTarget 4)) stopped :=
  (spec_maximumFee hfork hsize hsize' hsel hv hc hg).runFrame start within

/-- `spec_totalSupplyVar` for the interpreter loop. -/
theorem runFrame_totalSupplyVar (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x3eaaf86b)
    (hv : message.value = 0) {c : Bool} (hc : coldIn substate message.currentTarget 1 = c)
    {gas : Nat} (hg : 428 + slotCost c ≤ gas)
    {bound : Nat} {runChild : MessageRunner fork Nat bound} {evm : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    ∃ stopped, runFrame (step fork) (step_decreases fork) bound runChild evm within =
      .ok stopped ∧
      (Halted false (wordBytes (storageAt state message.currentTarget 1)) (gas - (428 + slotCost c))
          (readSlot state message.currentTarget 1) (accessSlot substate message.currentTarget 1)) stopped :=
  (spec_totalSupplyVar hfork hsize hsize' hsel hv hc hg).runFrame start within

/-- `spec_basisPointsRate` for the interpreter loop. -/
theorem runFrame_basisPointsRate (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xdd644f72)
    (hv : message.value = 0) {c : Bool} (hc : coldIn substate message.currentTarget 3 = c)
    {gas : Nat} (hg : 758 + slotCost c ≤ gas)
    {bound : Nat} {runChild : MessageRunner fork Nat bound} {evm : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    ∃ stopped, runFrame (step fork) (step_decreases fork) bound runChild evm within =
      .ok stopped ∧
      (Halted false (wordBytes (storageAt state message.currentTarget 3)) (gas - (758 + slotCost c))
          (readSlot state message.currentTarget 3) (accessSlot substate message.currentTarget 3)) stopped :=
  (spec_basisPointsRate hfork hsize hsize' hsel hv hc hg).runFrame start within

/-- `spec_maxUint` for the interpreter loop. -/
theorem runFrame_maxUint (hsize : 4 ≤ message.data.size) (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0xe5b5019a) (hv : message.value = 0) {gas : Nat}
    (hg : 824 ≤ gas)
    {bound : Nat} {runChild : MessageRunner fork Nat bound} {evm : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    ∃ stopped, runFrame (step fork) (step_decreases fork) bound runChild evm within =
      .ok stopped ∧
      (Halted false (wordBytes (BitVec.ofNat 256 (2 ^ 256 - 1))) (gas - 824) state substate) stopped :=
  (spec_maxUint hsize hsize' hsel hv hg).runFrame start within

/-- `spec_flag` for the interpreter loop. -/
theorem runFrame_flag (hfork : .berlin ≤ fork) {sel t e r b k : Nat}
    (hp : (sel, t, e, r, b, k) ∈ FLAG_GETTERS) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = sel)
    (hv : message.value = 0) {ck : Bool}
    (hck : coldIn substate message.currentTarget (BitVec.ofNat 256 k) = ck) {gas : Nat}
    (hg : 262 + 22 * t + slotCost ck ≤ gas)
    {bound : Nat} {runChild : MessageRunner fork Nat bound} {evm : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    ∃ stopped, runFrame (step fork) (step_decreases fork) bound runChild evm within =
      .ok stopped ∧
      (Halted false (wordBytes (if byte20 (storageAt state message.currentTarget
            (BitVec.ofNat 256 k)) = 0 then 0 else 1))
          (gas - (262 + 22 * t + slotCost ck))
          (readSlot state message.currentTarget (BitVec.ofNat 256 k))
          (accessSlot substate message.currentTarget (BitVec.ofNat 256 k))) stopped :=
  (spec_flag hfork hp hsize hsize' hsel hv hck hg).runFrame start within

/-- `spec_deprecated` for the interpreter loop. -/
theorem runFrame_deprecated (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x0e136b19)
    (hv : message.value = 0) {c : Bool} (hc : coldIn substate message.currentTarget 10 = c)
    {gas : Nat} (hg : 350 + slotCost c ≤ gas)
    {bound : Nat} {runChild : MessageRunner fork Nat bound} {evm : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    ∃ stopped, runFrame (step fork) (step_decreases fork) bound runChild evm within =
      .ok stopped ∧
      (Halted false (wordBytes (if byte20 (storageAt state message.currentTarget 10) = 0 then 0
            else 1)) (gas - (350 + slotCost c))
          (readSlot state message.currentTarget 10) (accessSlot substate message.currentTarget 10)) stopped :=
  (spec_deprecated hfork hsize hsize' hsel hv hc hg).runFrame start within

/-- `spec_upgradedAddress` for the interpreter loop. -/
theorem runFrame_upgradedAddress (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x26976e3f)
    (hv : message.value = 0) {c : Bool} (hc : coldIn substate message.currentTarget 10 = c)
    {gas : Nat} (hg : 388 + slotCost c ≤ gas)
    {bound : Nat} {runChild : MessageRunner fork Nat bound} {evm : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    ∃ stopped, runFrame (step fork) (step_decreases fork) bound runChild evm within =
      .ok stopped ∧
      (Halted false (wordBytes (bitwiseAnd ADDR_MASK (storageAt state message.currentTarget 10)))
          (gas - (388 + slotCost c))
          (readSlot state message.currentTarget 10) (accessSlot substate message.currentTarget 10)) stopped :=
  (spec_upgradedAddress hfork hsize hsize' hsel hv hc hg).runFrame start within

/-- `spec_owner` for the interpreter loop. -/
theorem runFrame_owner (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x8da5cb5b)
    (hv : message.value = 0) {c : Bool} (hc : coldIn substate message.currentTarget 0 = c)
    {gas : Nat} (hg : 652 + slotCost c ≤ gas)
    {bound : Nat} {runChild : MessageRunner fork Nat bound} {evm : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    ∃ stopped, runFrame (step fork) (step_decreases fork) bound runChild evm within =
      .ok stopped ∧
      (Halted false (wordBytes (ownerOf state message.currentTarget))
          (gas - (652 + slotCost c))
          (readSlot state message.currentTarget 0) (accessSlot substate message.currentTarget 0)) stopped :=
  (spec_owner hfork hsize hsize' hsel hv hc hg).runFrame start within

/-- `spec_getOwner` for the interpreter loop. -/
theorem runFrame_getOwner (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x893d20e8)
    (hv : message.value = 0) {c : Bool} (hc : coldIn substate message.currentTarget 0 = c)
    {gas : Nat} (hg : 638 + slotCost c ≤ gas)
    {bound : Nat} {runChild : MessageRunner fork Nat bound} {evm : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    ∃ stopped, runFrame (step fork) (step_decreases fork) bound runChild evm within =
      .ok stopped ∧
      (Halted false (wordBytes (ownerOf state message.currentTarget))
          (gas - (638 + slotCost c))
          (readSlot state message.currentTarget 0) (accessSlot substate message.currentTarget 0)) stopped :=
  (spec_getOwner hfork hsize hsize' hsel hv hc hg).runFrame start within

end UsdtVerify.Getters

namespace UsdtVerify.GettersMap

open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts
open Transfer TransferOk Owner Admin BlackList Issue Getters

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate}

/-- `spec_balances` for the interpreter loop. -/
theorem runFrame_balances (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x27e235e3)
    (hv : message.value = 0) {c : Bool}
    (hc : coldIn substate message.currentTarget (mapSlot (addrArg message.data 0) 2) = c)
    {gas : Nat} (hg : 478 + slotCost c ≤ gas)
    {bound : Nat} {runChild : MessageRunner fork Nat bound} {evm : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    ∃ stopped, runFrame (step fork) (step_decreases fork) bound runChild evm within =
      .ok stopped ∧
      (Halted false (wordBytes (storageAt state message.currentTarget
            (mapSlot (addrArg message.data 0) 2)))
          (gas - (478 + slotCost c))
          (readSlot state message.currentTarget (mapSlot (addrArg message.data 0) 2))
          (accessSlot substate message.currentTarget (mapSlot (addrArg message.data 0) 2))) stopped :=
  (spec_balances hfork hsize hsize' hsel hv hc hg).runFrame start within

/-- `spec_isBlackListed` for the interpreter loop. -/
theorem runFrame_isBlackListed (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xe47d6060)
    (hv : message.value = 0) {c : Bool}
    (hc : coldIn substate message.currentTarget (mapSlot (addrArg message.data 0) 6) = c)
    {gas : Nat} (hg : 933 + slotCost c ≤ gas)
    {bound : Nat} {runChild : MessageRunner fork Nat bound} {evm : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    ∃ stopped, runFrame (step fork) (step_decreases fork) bound runChild evm within =
      .ok stopped ∧
      (Halted false (wordBytes (if (storageAt state message.currentTarget
            (mapSlot (addrArg message.data 0) 6)).toNat % 256 = 0 then 0 else 1))
          (gas - (933 + slotCost c))
          (readSlot state message.currentTarget (mapSlot (addrArg message.data 0) 6))
          (accessSlot substate message.currentTarget (mapSlot (addrArg message.data 0) 6))) stopped :=
  (spec_isBlackListed hfork hsize hsize' hsel hv hc hg).runFrame start within

/-- `spec_getBlackListStatus` for the interpreter loop. -/
theorem runFrame_getBlackListStatus (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x59bf1abe)
    (hv : message.value = 0) {c : Bool}
    (hc : coldIn substate message.currentTarget (mapSlot (addrArg message.data 0) 6) = c)
    {gas : Nat} (hg : 663 + slotCost c ≤ gas)
    {bound : Nat} {runChild : MessageRunner fork Nat bound} {evm : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    ∃ stopped, runFrame (step fork) (step_decreases fork) bound runChild evm within =
      .ok stopped ∧
      (Halted false (wordBytes (if (storageAt state message.currentTarget
            (mapSlot (addrArg message.data 0) 6)).toNat % 256 = 0 then 0 else 1))
          (gas - (663 + slotCost c))
          (readSlot state message.currentTarget (mapSlot (addrArg message.data 0) 6))
          (accessSlot substate message.currentTarget (mapSlot (addrArg message.data 0) 6))) stopped :=
  (spec_getBlackListStatus hfork hsize hsize' hsel hv hc hg).runFrame start within

/-- `spec_allowed` for the interpreter loop. -/
theorem runFrame_allowed (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x5c658165)
    (hv : message.value = 0) {c : Bool}
    (hc : coldIn substate message.currentTarget (allowSlot message.data) = c)
    {gas : Nat} (hg : 705 + slotCost c ≤ gas)
    {bound : Nat} {runChild : MessageRunner fork Nat bound} {evm : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    ∃ stopped, runFrame (step fork) (step_decreases fork) bound runChild evm within =
      .ok stopped ∧
      (Halted false (wordBytes (storageAt state message.currentTarget (allowSlot message.data)))
          (gas - (705 + slotCost c))
          (readSlot state message.currentTarget (allowSlot message.data))
          (accessSlot substate message.currentTarget (allowSlot message.data))) stopped :=
  (spec_allowed hfork hsize hsize' hsel hv hc hg).runFrame start within

/-- `spec_allowance` for the interpreter loop. -/
theorem runFrame_allowance (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xdd62ed3e)
    (hv : message.value = 0) (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    {c10 c : Bool} (hc10 : coldIn substate message.currentTarget 10 = c10)
    (hc : coldIn (accessSlot substate message.currentTarget 10) message.currentTarget
      (allowSlot message.data) = c)
    {gas : Nat} (hg : 1156 + slotCost c10 + slotCost c ≤ gas)
    {bound : Nat} {runChild : MessageRunner fork Nat bound} {evm : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    ∃ stopped, runFrame (step fork) (step_decreases fork) bound runChild evm within =
      .ok stopped ∧
      (Halted false (wordBytes (storageAt state message.currentTarget (allowSlot message.data)))
          (gas - (1156 + slotCost c10 + slotCost c))
          (readSlot (readSlot state message.currentTarget 10) message.currentTarget
            (allowSlot message.data))
          (accessSlot (accessSlot substate message.currentTarget 10) message.currentTarget
            (allowSlot message.data))) stopped :=
  (spec_allowance hfork hsize hsize' hsel hv hdep hc10 hc hg).runFrame start within

end UsdtVerify.GettersMap
