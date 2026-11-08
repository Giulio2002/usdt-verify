import UsdtVerify.Usdt.Spec.Pause
import UsdtVerify.Usdt.Spec.BlackList
import UsdtVerify.Usdt.Spec.Issue
import UsdtVerify.Usdt.Spec.SetParams
import UsdtVerify.Usdt.Spec.AddrWrite
import UsdtVerify.Usdt.Spec.Destroy
import UsdtVerify.Usdt.Spec.Approve
import UsdtVerify.Usdt.Spec.Transfer
import UsdtVerify.Usdt.Spec.TransferFrom

/-!
# When each function succeeds, in plain terms

Each condition below is the exact success condition of a function: the theorems of
`Usdt/Exact/` prove that, with the gas of the success path, the run ends with no error if and
only if the condition holds.

- `CallOk`: the call data has at least 4 bytes and the call has no value.
  Every function of the table is nonpayable, so every success condition contains it.
  Each getter (name and symbol under `StrForm`, totalSupply, balanceOf and allowance when not
  deprecated) succeeds exactly when `CallOk` holds.
- `CanWrite`: the frame is not static and the contract has an account.
- `IsOwner`: the caller, as a word, is the low 160 bits of slot 0.
- The owner functions: `PauseGuard`, `UnpauseGuard`, `OwnerWriteGuard` (addBlackList, removeBlackList,
  deprecate), `IssueGuard`, `RedeemGuard`, `SetParamsGuard`, `TransferOwnershipGuard`,
  `DestroyBlackFundsGuard` (when not deprecated).
- `ApproveGuard` (approve when not deprecated).
- `TransferGuard`, `TransferFromGuard` (transfer, transferFrom when not deprecated).
- When deprecated, a function that forwards succeeds exactly when the forward is made and the
  upgraded contract's answer is as the theorem's runner hypothesis says: `ForwardOk` (`CallOk`,
  the upgraded code `c` is not empty, the depth leaves room for the call), with
  `TransferDepGuard`, `ApproveDepGuard`, `TransferFromDepGuard`, `DestroyDepGuard` for the checks
  before the forward.
  Its terms are those the bytecode computes, read in the state after the checks of the prelude
  (reads only, so each slot holds the word it holds in the start state); the recipient's balance is
  read after the write of the sender's, and the owner's after the write of the recipient's.
-/

namespace UsdtVerify

open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm

variable {fork : Fork}

/-- The call data has at least 4 bytes and the call has no value. -/
def CallOk (message : Message fork) : Prop := 4 ≤ message.data.size ∧ message.value = 0

/-- The frame is not static and the contract has an account in the state. -/
def CanWrite (state : State.TransactionState) (message : Message fork) : Prop :=
  message.isStatic = false ∧ hasAccount state message.currentTarget

/-- The caller, as a word, is the owner: the low 160 bits of slot 0. -/
def IsOwner (state : State.TransactionState) (message : Message fork) : Prop :=
  Owner.callerWord message = Owner.ownerOf state message.currentTarget

/-! ## The owner functions -/

section
variable (state : State.TransactionState) (message : Message fork)

/-- `pause()` succeeds exactly when: `CallOk`, `CanWrite`, `IsOwner`, and not paused (byte 20 of
slot 0 is 0). -/
def PauseGuard : Prop :=
  CallOk message ∧ CanWrite state message ∧ IsOwner state message ∧
    byte20 (storageAt state message.currentTarget 0) = 0

/-- `unpause()` succeeds exactly when: `CallOk`, `CanWrite`, `IsOwner`, and paused (byte 20 of
slot 0 is not 0). -/
def UnpauseGuard : Prop :=
  CallOk message ∧ CanWrite state message ∧ IsOwner state message ∧
    byte20 (storageAt state message.currentTarget 0) ≠ 0

/-- `addBlackList(a)`, `removeBlackList(a)` and `deprecate(a)` succeed exactly when: `CallOk`,
`CanWrite` and `IsOwner`. -/
def OwnerWriteGuard : Prop :=
  CallOk message ∧ CanWrite state message ∧ IsOwner state message

/-- `issue(a)` succeeds exactly when: `CallOk`, `CanWrite`, `IsOwner`, `0 < a`,
`_totalSupply + a < 2^256` and `balances[owner] + a < 2^256` (`a` the argument word, slot 1, the
balance slot of the owner). -/
def IssueGuard : Prop :=
  CallOk message ∧ CanWrite state message ∧ IsOwner state message ∧
    0 < (wordArg message.data 0).toNat ∧
    (storageAt state message.currentTarget 1).toNat + (wordArg message.data 0).toNat < 2 ^ 256 ∧
    (storageAt state message.currentTarget (Issue.ownerBal state message.currentTarget)).toNat +
      (wordArg message.data 0).toNat < 2 ^ 256

/-- `redeem(a)` succeeds exactly when: `CallOk`, `CanWrite`, `IsOwner`, `a ≤ _totalSupply` and
`a ≤ balances[owner]`. -/
def RedeemGuard : Prop :=
  CallOk message ∧ CanWrite state message ∧ IsOwner state message ∧
    (wordArg message.data 0).toNat ≤ (storageAt state message.currentTarget 1).toNat ∧
    (wordArg message.data 0).toNat ≤
      (storageAt state message.currentTarget (Issue.ownerBal state message.currentTarget)).toNat

/-- `setParams(b, m)` succeeds exactly when: `CallOk`, `CanWrite`, `IsOwner`, `b < 20`, `m < 50`
and `m * 10^decimals < 2^256` (`10^decimals` the EVM word `exp 10 (slot 9)`). -/
def SetParamsGuard : Prop :=
  CallOk message ∧ CanWrite state message ∧ IsOwner state message ∧
    (wordArg message.data 0).toNat < 20 ∧ (wordArg message.data 1).toNat < 50 ∧
    (wordArg message.data 1).toNat *
      (exp (0x0a : U256) (storageAt state message.currentTarget 9)).toNat < 2 ^ 256

/-- `transferOwnership(a)` succeeds exactly when: `CallOk`, `IsOwner`, and `CanWrite` if the
address `a` is not 0 (with `a = 0` nothing is written). -/
def TransferOwnershipGuard : Prop :=
  CallOk message ∧ IsOwner state message ∧ (addrArg message.data 0 ≠ 0 → CanWrite state message)

/-- `destroyBlackFunds(a)`, not deprecated, succeeds exactly when: `CallOk`, `CanWrite`,
`IsOwner`, and `a` blacklisted (the low byte of `isBlackListed[a]` is not 0). -/
def DestroyBlackFundsGuard : Prop :=
  CallOk message ∧ CanWrite state message ∧ IsOwner state message ∧
    (storageAt state message.currentTarget (BlackList.listSlot (addrArg message.data 0))).toNat %
      256 ≠ 0

end

/-! ## approve -/

/-- `approve(s, v)`, not deprecated, succeeds exactly when: `CallOk`, `CanWrite`, at least 68
bytes of call data, and, if `v ≠ 0`, the allowance `allowed[caller][s]` is 0. -/
def ApproveGuard (state : State.TransactionState) (message : Message fork) : Prop :=
  CallOk message ∧ CanWrite state message ∧ 68 ≤ message.data.size ∧
    (wordArg message.data 1 ≠ 0 →
      storageAt state message.currentTarget (Approve.allowArg message) = 0)

/-! ## transfer -/

open TransferOk TransferFee in
/-- `transfer(a, v)`, not deprecated, succeeds exactly when: `CallOk`, `CanWrite`, at least 68
bytes of call data, not paused (byte 20 of slot 0 is 0), the caller not blacklisted (the low byte
of `isBlackListed[caller]` is 0), `v * basisPointsRate < 2^256`, `fee ≤ v` (`fee` =
`min(v * basisPointsRate / 10000, maximumFee)`), `v ≤ balances[caller]`,
`balances[a] + (v - fee) < 2^256` (read after the sender's write), and, if `fee ≠ 0`,
`balances[owner] + fee < 2^256` (read after the recipient's write). -/
def TransferGuard (state : State.TransactionState) (message : Message fork) : Prop :=
  CallOk message ∧ CanWrite state message ∧ 68 ≤ message.data.size ∧
    byte20 (storageAt state message.currentTarget 0) = 0 ∧
    (storageAt state message.currentTarget (Transfer.blackSlot message)).toNat % 256 = 0 ∧
    (wordArg message.data 1).toNat *
      (storageAt (Transfer.shortState state message) message.currentTarget 3).toNat < 2 ^ 256 ∧
    (feeOf (Transfer.shortState state message) message (wordArg message.data 1)).toNat ≤
      (wordArg message.data 1).toNat ∧
    (wordArg message.data 1).toNat ≤ (balS (Transfer.shortState state message) message).toNat ∧
    (balT (Transfer.shortState state message) message (wordArg message.data 1)
      (addrArg message.data 0)).toNat +
      (sendOf (Transfer.shortState state message) message (wordArg message.data 1)).toNat <
        2 ^ 256 ∧
    (feeOf (Transfer.shortState state message) message (wordArg message.data 1) ≠ 0 →
      (balO (Transfer.shortState state message) message (wordArg message.data 1)
        (addrArg message.data 0)).toNat +
        (feeOf (Transfer.shortState state message) message (wordArg message.data 1)).toNat <
          2 ^ 256)

/-! ## transferFrom -/

open TransferOk TransferFee TransferFrom in
/-- `transferFrom(f, t, v)`, not deprecated, succeeds exactly when: `CallOk`, `CanWrite`, at
least 100 bytes of call data, not paused, `f` not blacklisted (the caller's status is not read),
`v * basisPointsRate < 2^256`, the allowance `allowed[f][caller]` is `MAX_UINT` or at least `v`,
`fee ≤ v`, `v ≤ balances[f]` (read after the write of the allowance), `balances[t] + (v - fee) <
2^256` (read after the write of `balances[f]`), and, if `fee ≠ 0`, `balances[owner] + fee <
2^256` (read after the write of `balances[t]`). -/
def TransferFromGuard (state : State.TransactionState) (message : Message fork) : Prop :=
  CallOk message ∧ CanWrite state message ∧ 100 ≤ message.data.size ∧
    byte20 (storageAt state message.currentTarget 0) = 0 ∧
    (storageAt state message.currentTarget (blackFrom (fromArg message))).toNat % 256 = 0 ∧
    (valArg message).toNat *
      (storageAt (checkState state message) message.currentTarget 3).toNat < 2 ^ 256 ∧
    (allowOf (checkState state message) message (fromArg message) = MAX_UINT ∨
      (valArg message).toNat ≤
        (allowOf (checkState state message) message (fromArg message)).toNat) ∧
    (feeOf (checkState state message) message (valArg message)).toNat ≤ (valArg message).toNat ∧
    (valArg message).toNat ≤
      (balFrom (checkState state message) message (valArg message) (fromArg message)).toNat ∧
    (balTo (checkState state message) message (valArg message) (toArg message)
      (fromArg message)).toNat +
      (sendOf (checkState state message) message (valArg message)).toNat < 2 ^ 256 ∧
    (feeOf (checkState state message) message (valArg message) ≠ 0 →
      (balOF (checkState state message) message (valArg message) (toArg message)
        (fromArg message)).toNat +
        (feeOf (checkState state message) message (valArg message)).toNat < 2 ^ 256)

/-! ## When deprecated -/

/-- The forward is made: `CallOk`, the code `c` of the upgraded address is not empty, and the
depth leaves room for one more frame. -/
def ForwardOk (message : Message fork) (c : ByteArray) : Prop :=
  CallOk message ∧ 0 < c.size ∧ message.depth + 1 ≤ STACK_DEPTH_LIMIT

/-- The checks of `transfer(a, v)` before the forward: `ForwardOk`, not paused, the caller not
blacklisted. -/
def TransferDepGuard (state : State.TransactionState) (message : Message fork) (c : ByteArray) :
    Prop :=
  ForwardOk message c ∧ byte20 (storageAt state message.currentTarget 0) = 0 ∧
    (storageAt state message.currentTarget (Transfer.blackSlot message)).toNat % 256 = 0

/-- The checks of `approve(s, v)` before the forward: `ForwardOk`, at least 68 bytes of call
data. -/
def ApproveDepGuard (message : Message fork) (c : ByteArray) : Prop :=
  ForwardOk message c ∧ 68 ≤ message.data.size

/-- The checks of `transferFrom(f, t, v)` before the forward: `ForwardOk`, not paused, `f` not
blacklisted. -/
def TransferFromDepGuard (state : State.TransactionState) (message : Message fork)
    (c : ByteArray) : Prop :=
  ForwardOk message c ∧ byte20 (storageAt state message.currentTarget 0) = 0 ∧
    (storageAt state message.currentTarget
      (TransferFrom.blackFrom (TransferFrom.fromArg message))).toNat % 256 = 0

/-- The checks of `destroyBlackFunds(a)` when deprecated, besides the answer: `ForwardOk`,
`IsOwner`, `a` blacklisted, and the frame not static (the code writes after the forward). -/
def DestroyDepGuard (state : State.TransactionState) (message : Message fork) (c : ByteArray) :
    Prop :=
  ForwardOk message c ∧ IsOwner state message ∧
    (storageAt state message.currentTarget (BlackList.listSlot (addrArg message.data 0))).toNat %
      256 ≠ 0 ∧
    message.isStatic = false

end UsdtVerify
