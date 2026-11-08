import UsdtVerify.Evm.Storage
import EthLib.Execution.Proofs.Evm.Logic.Rules
import EthLib.Base.Proofs.U256

/-!
# Storage writes, stated over slots

GENERIC: nothing here is about a particular contract.

- `writeSlot state target n v`: the state after SSTORE of `v` in slot `n` of `target` (the read
  of the slot recorded, then the write), when `target` has an account.
- `storeSub`: the substate after that SSTORE (the slot accessed, the refund added).
- `setStorage_writeSlot`: the write of a slot, when the account exists (used by `Gas.sstoreWG`).
- Reading or accessing a slot twice is reading or accessing it once.
-/

namespace UsdtVerify

open EthLib.Base (Fork U256 Address)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic

/-- The word of slot `n` of `target` before the transaction (EIP-2200 prices writes by it). -/
abbrev originalAt (state : State.TransactionState) (target : Address) (n : U256) : U256 :=
  state.getStorageOriginal target (U256.toBeBytes n)

/-- Whether `target` has an account in the state. -/
abbrev hasAccount (state : State.TransactionState) (target : Address) : Prop :=
  (state.getAccountOptional target).isSome = true

/-- The state after SSTORE of `v` in slot `n` of `target`: the read recorded, then the write.

The write needs the account of `target`; without one the state is left (never used then). -/
def writeSlot (state : State.TransactionState) (target : Address) (n v : U256) :
    State.TransactionState :=
  match (state.recordStorageRead target (U256.toBeBytes n)).setStorage target
      (U256.toBeBytes n) v with
  | .ok s => s
  | .error _ => state

theorem setStorage_writeSlot {state : State.TransactionState} {target : Address} {n v : U256}
    (h : hasAccount state target) :
    (state.recordStorageRead target (U256.toBeBytes n)).setStorage target (U256.toBeBytes n) v =
      .ok (writeSlot state target n v) := by
  unfold writeSlot State.TransactionState.setStorage
  have h' : ((state.recordStorageRead target (U256.toBeBytes n)).getAccountOptional
      target).isNone = false := by
    rw [(State.TransactionState.recordStorageRead_reads state target target (U256.toBeBytes n)
      (U256.toBeBytes n) default).1]
    simpa [Option.isNone_iff_eq_none, Option.isSome_iff_ne_none] using h
  simp only [h', Bool.false_eq_true, ite_false]

theorem toBeBytes_ne {m n : U256} (h : m ≠ n) : U256.toBeBytes m ≠ U256.toBeBytes n := by
  intro he
  apply h
  rw [← EthLib.Base.U256.fromBeBytes_toBeBytes m, he, EthLib.Base.U256.fromBeBytes_toBeBytes]

theorem storageAt_writeSlot_self {state : State.TransactionState} {target : Address} {n v : U256}
    (h : hasAccount state target) : storageAt (writeSlot state target n v) target n = v :=
  State.TransactionState.getStorage_setStorage_self (setStorage_writeSlot h)

theorem storageAt_writeSlot_of_ne {state : State.TransactionState} {target : Address}
    {n m v : U256} (h : hasAccount state target) (hne : m ≠ n) :
    storageAt (writeSlot state target n v) target m = storageAt state target m := by
  have := State.TransactionState.getStorage_setStorage_of_ne (setStorage_writeSlot (v := v) h)
    (other := target) (otherKey := U256.toBeBytes m) (Or.inr (toBeBytes_ne hne))
  rw [storageAt, this]
  rfl

theorem originalAt_writeSlot {state : State.TransactionState} {target : Address} {n m v : U256}
    {other : Address} (h : hasAccount state target) :
    originalAt (writeSlot state target n v) other m = originalAt state other m := by
  have := State.TransactionState.getStorageOriginal_setStorage
    (setStorage_writeSlot (n := n) (v := v) h)
  rw [originalAt, this]
  rfl

theorem hasAccount_writeSlot {state : State.TransactionState} {target : Address} {n v : U256}
    (h : hasAccount state target) : hasAccount (writeSlot state target n v) target := by
  rw [hasAccount, State.TransactionState.getAccountOptional_setStorage (setStorage_writeSlot h),
    (State.TransactionState.recordStorageRead_reads state target target (U256.toBeBytes n)
      (U256.toBeBytes n) default).1]
  exact h

theorem hasAccount_readSlot {state : State.TransactionState} {target other : Address} {n : U256}
    (h : hasAccount state target) : hasAccount (readSlot state other n) target := by
  rw [hasAccount, (State.TransactionState.recordStorageRead_reads state other target
    (U256.toBeBytes n) (U256.toBeBytes n) default).1]
  exact h

theorem originalAt_readSlot {state : State.TransactionState} {target other : Address}
    {n m : U256} : originalAt (readSlot state other n) target m = originalAt state target m :=
  (State.TransactionState.recordStorageRead_reads state other target _ (U256.toBeBytes m)
    default).2.2.1

/-- The substate after SSTORE of `new` in slot `n` of `target`, over the words `orig` (before
the transaction) and `cur` (before the write): the slot accessed and the refund added. -/
abbrev storeSub (fork : Fork) (substate : Substate) (target : Address) (n : U256)
    (orig cur new : U256) : Substate :=
  { accessSlot substate target n with
    refundCounter := substate.refundCounter + sstoreRefund fork orig cur new }

variable {fork : Fork} {code : ByteArray} {message : Message fork} {pc : Nat}
  {memory : ByteArray} {gas : Nat} {state : State.TransactionState} {substate : Substate}

/-- Recording a read twice is recording it once (EthLib's `recordStorageRead_recordStorageRead`). -/
theorem readSlot_readSlot (state : State.TransactionState) (target : Address) (n : U256) :
    readSlot (readSlot state target n) target n = readSlot state target n :=
  State.TransactionState.recordStorageRead_recordStorageRead state target (U256.toBeBytes n)

/-- Accessing a slot twice is accessing it once (EthLib's `insert_insert_getD_self`). -/
theorem accessSlot_accessSlot (substate : Substate) (target : Address) (n : U256) :
    accessSlot (accessSlot substate target n) target n = accessSlot substate target n := by
  simp only [accessSlot]
  rw [insert_insert_getD_self]

/-- An accessed slot is warm. -/
theorem coldIn_accessSlot_self (substate : Substate) (target : Address) (n : U256) :
    coldIn (accessSlot substate target n) target n = false := by
  simp [coldIn, Std.ExtTreeMap.getD_insert_self]

end UsdtVerify
