import UsdtVerify.Evm.Meter
import UsdtVerify.Usdt.Invariant.Calls
import UsdtVerify.Usdt.Complete.Transfer
import UsdtVerify.Usdt.Complete.Approve
import UsdtVerify.Usdt.Complete.TransferFrom

/-!
# The results not deprecated, for EthLib's EIP-8037 meter

EthLib runs Glamsterdam transactions with the meter `StateGasMeter` (EIP-8037). Through
`Meter.ends_of_sgm`, every theorem that takes `hrun : Ends fork evm s` applies to a run of the
interpreter loop over that meter, for any gas bound and message runner, from a frame `m` whose
`toNat` is the fresh frame of `CODE`, under two hypotheses:

- `hres`: the reservoir of `m` is 0. EthLib's `allocateGas` gives it to the first frame of every
  transaction with a gas limit of at most 2^24 (`Meter.allocateGas_reservoir`).
- `hnr`: no SSTORE that the steps from `m` reach refills state gas (`Meter.NoRefillAt`: the
  refill of `sstoreStateRefill` is 0, so no slot that was 0 at the start of the transaction and is
  not 0 now is written back to 0).

The conclusion is then about `toNat s`: the fields of the end frame `s`, with its execution gas
left as gas. The theorems that apply this way: `ends_ok_dispatch`, the non-deprecated
completeness theorems `ok_X` (Usdt/Complete/Read, Getters, Owner, Approve, Transfer,
TransferFrom), the per-function `inv_X` and `inv_call`. Stated here:
`inv_call_sgm`, `ok_transfer_sgm`, `ok_approve_sgm`, `ok_transferFrom_sgm`.

Not covered: the deprecated paths (their CALL is not a `simulated` opcode), and the `X_ok_iff` /
`X_iff_gas` theorems, which state that a run with enough gas succeeds.
-/

namespace UsdtVerify.Complete

open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open UsdtVerify.Gas
open UsdtVerify.Meter

open Invariant Transfer TransferOk TransferFee SafeMath Approve TransferFrom

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate} {bound : Nat} {runChild : MessageRunner fork StateGasMeter bound}
  {m s : Evm fork StateGasMeter} {gas : Nat}

/-- **Every successful call keeps the invariant, over the EIP-8037 meter** (not deprecated).

`inv_call` for a run of the interpreter loop over `StateGasMeter`, for any gas bound and message
runner, from a frame `m` with reservoir 0 whose `toNat` is the fresh frame of `CODE`, where no
SSTORE that the steps reach refills state gas. -/
theorem inv_call_sgm (K : SepOn (callKeys message state)) (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    (h7 : StrForm (storageAt state message.currentTarget 7))
    (h8 : StrForm (storageAt state message.currentTarget 8))
    (hI : Inv message.currentTarget state)
    (start : At CODE message 0 [] .empty gas state substate (toNat m))
    (hres : m.gas.reservoir = 0) (hnr : ∀ x, Reaches (Step fork) m x → NoRefillAt x)
    {within : GasMeter.gasHeld m.gas ≤ bound}
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild m within = .ok s)
    (hok : s.error = none) : Inv message.currentTarget s.state :=
  have he : Ends fork (toNat m) (toNat s) := ends_of_sgm hrun hres hnr
  inv_call (evm := toNat m) (s := toNat s) K hfork hsize' hdep h7 h8 hI start he hok

/-- `ok_transfer` over the meter `StateGasMeter`, from reservoir 0 with no refill: the same
conclusion, with the execution gas left `s.gas.gasLeft` as the gas. -/
theorem ok_transfer_sgm (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xa9059cbb)
    (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    {c0 cB c10 c3 c4 cS cT cO : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hcB : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget
      (blackSlot message) = cB)
    (hc10 : coldIn (accessSlot (accessSlot substate message.currentTarget 0) message.currentTarget
      (blackSlot message)) message.currentTarget 10 = c10)
    (hc3 : coldIn (shortSubstate substate message) message.currentTarget 3 = c3)
    (hc4 : coldIn (accessSlot (shortSubstate substate message) message.currentTarget 3)
      message.currentTarget 4 = c4)
    (hcS : coldIn (accessSlot (accessSlot (shortSubstate substate message) message.currentTarget 3)
      message.currentTarget 4) message.currentTarget (senderSlot message) = cS)
    (hcT : coldIn (access3 (shortSubstate substate message) message) message.currentTarget
      (recipientSlot (addrArg message.data 0)) = cT)
    (hcO : coldIn (creditedSubFee fork (shortSubstate substate message) (shortState state message)
      message (wordArg message.data 1) (addrArg message.data 0)) message.currentTarget
      (ownerSlot (ownerWord (shortState state message) message (wordArg message.data 1)
        (addrArg message.data 0))) = cO)
    (start : At CODE message 0 [] .empty gas state substate (toNat m))
    (hres : m.gas.reservoir = 0) (hnr : ∀ x, Reaches (Step fork) m x → NoRefillAt x)
    {within : GasMeter.gasHeld m.gas ≤ bound}
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild m within = .ok s)
    (hok : s.error = none) :
    message.isStatic = false ∧ hasAccount state message.currentTarget ∧
    68 ≤ message.data.size ∧ byte20 (storageAt state message.currentTarget 0) = 0 ∧
      (storageAt state message.currentTarget (blackSlot message)).toNat % 256 = 0 ∧
      (wordArg message.data 1).toNat *
        (storageAt (shortState state message) message.currentTarget 3).toNat < 2 ^ 256 ∧
      (feeOf (shortState state message) message (wordArg message.data 1)).toNat ≤
        (wordArg message.data 1).toNat ∧
      (wordArg message.data 1).toNat ≤ (balS (shortState state message) message).toNat ∧
      (balT (shortState state message) message (wordArg message.data 1)
        (addrArg message.data 0)).toNat +
        (sendOf (shortState state message) message (wordArg message.data 1)).toNat < 2 ^ 256 ∧
      s.output = .empty ∧
      ((feeOf (shortState state message) message (wordArg message.data 1) = 0 ∧
        (okCost fork state message c0 cB c10 c3 c4 cS cT ≤ gas ∧
          s.gas.gasLeft = gas - okCost fork state message c0 cB c10 c3 c4 cS cT) ∧
        s.state = credited (shortState state message) message (wordArg message.data 1)
          (addrArg message.data 0) ∧
        s.substate = loggedSub fork (shortSubstate substate message) (shortState state message)
          message (wordArg message.data 1) (addrArg message.data 0)) ∨
      (feeOf (shortState state message) message (wordArg message.data 1) ≠ 0 ∧
        (balO (shortState state message) message (wordArg message.data 1)
          (addrArg message.data 0)).toNat +
          (feeOf (shortState state message) message (wordArg message.data 1)).toNat < 2 ^ 256 ∧
        (feeCost fork state message c0 cB c10 c3 c4 cS cT cO ≤ gas ∧
          s.gas.gasLeft = gas - feeCost fork state message c0 cB c10 c3 c4 cS cT cO) ∧
        s.state = feeState (shortState state message) message (wordArg message.data 1)
          (addrArg message.data 0) ∧
        s.substate = feeSub fork (shortSubstate substate message) (shortState state message)
          message (wordArg message.data 1) (addrArg message.data 0))) :=
  ok_transfer hfork hsize' hsel hdep hc0 hcB hc10 hc3 hc4 hcS hcT hcO
    start (ends_of_sgm hrun hres hnr) hok

/-- `ok_approve` over the meter `StateGasMeter`, from reservoir 0 with no refill: the same
conclusion, with the execution gas left `s.gas.gasLeft` as the gas. -/
theorem ok_approve_sgm (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x095ea7b3)
    (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    {c10 cA : Bool} (hc10 : coldIn substate message.currentTarget 10 = c10)
    (hcA : coldIn (accessSlot substate message.currentTarget 10) message.currentTarget
      (allowArg message) = cA)
    (start : At CODE message 0 [] .empty gas state substate (toNat m))
    (hres : m.gas.reservoir = 0) (hnr : ∀ x, Reaches (Step fork) m x → NoRefillAt x)
    {within : GasMeter.gasHeld m.gas ≤ bound}
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild m within = .ok s)
    (hok : s.error = none) :
    message.isStatic = false ∧ hasAccount state message.currentTarget ∧
    68 ≤ message.data.size ∧ s.output = .empty ∧
      ((wordArg message.data 1 = 0 ∧
        ((2560 + slotCost c10 + Gas.writeCost fork (originalAt state message.currentTarget (allowArg message)) (storageAt state message.currentTarget (allowArg message)) 0 cA) ≤ gas ∧
          s.gas.gasLeft = gas - (2560 + slotCost c10 + Gas.writeCost fork (originalAt state message.currentTarget (allowArg message)) (storageAt state message.currentTarget (allowArg message)) 0 cA)) ∧
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
        ((2753 + slotCost c10 + slotCost cA + Gas.writeCost fork (originalAt state message.currentTarget (allowArg message)) 0 (wordArg message.data 1) false) ≤ gas ∧
          s.gas.gasLeft = gas - (2753 + slotCost c10 + slotCost cA + Gas.writeCost fork (originalAt state message.currentTarget (allowArg message)) 0 (wordArg message.data 1) false)) ∧
        s.state = writeSlot (readSlot (readSlot state message.currentTarget 10)
          message.currentTarget (allowArg message)) message.currentTarget (allowArg message)
          (wordArg message.data 1) ∧
        s.substate = { storeSub fork (accessSlot (accessSlot substate message.currentTarget 10)
              message.currentTarget (allowArg message)) message.currentTarget
            (allowArg message) (originalAt state message.currentTarget (allowArg message)) 0
            (wordArg message.data 1) with
          logs := substate.logs.push (approvalLog message.currentTarget
            (bitwiseAnd ADDR_MASK message.caller.toU256)
            (bitwiseAnd ADDR_MASK (addrArg message.data 0)) (wordArg message.data 1)) })) :=
  ok_approve hfork hsize' hsel hdep hc10 hcA
    start (ends_of_sgm hrun hres hnr) hok

/-- `ok_transferFrom` over the meter `StateGasMeter`, from reservoir 0 with no refill: the same
conclusion, with the execution gas left `s.gas.gasLeft` as the gas. -/
theorem ok_transferFrom_sgm (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x23b872dd)
    (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    {c0 cB c10 cA c3 c4 cF cT cO : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hcB : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget
      (blackFrom (fromArg message)) = cB)
    (hc10 : coldIn (accessSlot (accessSlot substate message.currentTarget 0) message.currentTarget
      (blackFrom (fromArg message))) message.currentTarget 10 = c10)
    (hcA : coldIn (checkSub substate message) message.currentTarget
      (allowFrom message (fromArg message)) = cA)
    (hc3 : coldIn (accessSlot (checkSub substate message) message.currentTarget
      (allowFrom message (fromArg message))) message.currentTarget 3 = c3)
    (hc4 : coldIn (accessSlot (accessSlot (checkSub substate message) message.currentTarget
      (allowFrom message (fromArg message))) message.currentTarget 3) message.currentTarget 4 = c4)
    (hcF : coldIn (allowedSubF fork (checkSub substate message) (checkState state message) message
      (valArg message) (fromArg message)) message.currentTarget (recipientSlot (fromArg message)) =
        cF)
    (hcT : coldIn (accessSlot (allowedSubF fork (checkSub substate message)
      (checkState state message) message (valArg message) (fromArg message)) message.currentTarget
      (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (toArg message)) = cT)
    (hcO : coldIn (creditedSubFeeF fork (checkSub substate message) (checkState state message)
      message (valArg message) (toArg message) (fromArg message)) message.currentTarget
      (ownerSlot (ownerWordF (checkState state message) message (valArg message) (toArg message)
        (fromArg message))) = cO)
    (start : At CODE message 0 [] .empty gas state substate (toNat m))
    (hres : m.gas.reservoir = 0) (hnr : ∀ x, Reaches (Step fork) m x → NoRefillAt x)
    {within : GasMeter.gasHeld m.gas ≤ bound}
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild m within = .ok s)
    (hok : s.error = none) :
    message.isStatic = false ∧ hasAccount state message.currentTarget ∧
    100 ≤ message.data.size ∧ byte20 (storageAt state message.currentTarget 0) = 0 ∧
      (storageAt state message.currentTarget (blackFrom (fromArg message))).toNat % 256 = 0 ∧
      (valArg message).toNat *
        (storageAt (checkState state message) message.currentTarget 3).toNat < 2 ^ 256 ∧
      (allowOf (checkState state message) message (fromArg message) = MAX_UINT ∨
        (valArg message).toNat ≤
          (allowOf (checkState state message) message (fromArg message)).toNat) ∧
      (feeOf (checkState state message) message (valArg message)).toNat ≤
        (valArg message).toNat ∧
      (valArg message).toNat ≤
        (balFrom (checkState state message) message (valArg message) (fromArg message)).toNat ∧
      (balTo (checkState state message) message (valArg message) (toArg message)
        (fromArg message)).toNat +
        (sendOf (checkState state message) message (valArg message)).toNat < 2 ^ 256 ∧
      s.output = .empty ∧
      ((feeOf (checkState state message) message (valArg message) = 0 ∧
        (okCostF fork state message c0 cB c10 cA c3 c4 cF cT ≤ gas ∧
          s.gas.gasLeft = gas - okCostF fork state message c0 cB c10 cA c3 c4 cF cT) ∧
        s.state = creditedF (checkState state message) message (valArg message) (toArg message)
          (fromArg message) ∧
        s.substate = loggedSubF fork (checkSub substate message) (checkState state message)
          message (valArg message) (toArg message) (fromArg message)) ∨
      (feeOf (checkState state message) message (valArg message) ≠ 0 ∧
        (balOF (checkState state message) message (valArg message) (toArg message)
          (fromArg message)).toNat +
          (feeOf (checkState state message) message (valArg message)).toNat < 2 ^ 256 ∧
        (feeCostF fork state message c0 cB c10 cA c3 c4 cF cT cO ≤ gas ∧
          s.gas.gasLeft = gas - feeCostF fork state message c0 cB c10 cA c3 c4 cF cT cO) ∧
        s.state = feeStateF (checkState state message) message (valArg message) (toArg message)
          (fromArg message) ∧
        s.substate = feeSubF fork (checkSub substate message) (checkState state message) message
          (valArg message) (toArg message) (fromArg message))) :=
  ok_transferFrom hfork hsize' hsel hdep hc0 hcB hc10 hcA hc3 hc4 hcF hcT hcO
    start (ends_of_sgm hrun hres hnr) hok

end UsdtVerify.Complete
