import UsdtVerify.Evm.Local.Rules
import EthLib.Execution.Proofs.Evm.Logic.Steps
import EthLib.Execution.Proofs.State.Tracker

/-!
# Storage, stated over slots

Defines the word in a storage slot, the reads and accesses of a slot, the slot of a mapping entry
and byte 20 of a word, and proves that a read keeps every word and an access keeps other slots
as cold as they were.

- `storageAt state target n`: the word in slot `n` of the account `target`.
- `coldIn`, `readSlot`, `accessSlot`: whether a slot is cold; the state and substate after SLOAD.
- `mapSlot key base`: the slot of `key` in a mapping at base slot `base`.
- `byte20 w`: byte 20 of a word, from the least significant end (bits 160 to 167).
-/

namespace UsdtVerify

open EthLib.Base (U256 Address)
open EthLib.Execution

/-- The word in slot `n` of the account `target`. -/
abbrev storageAt (state : State.TransactionState) (target : Address) (n : U256) : U256 :=
  state.getStorage target (U256.toBeBytes n)

/-- Whether slot `n` of `target` is cold in a substate: not accessed yet. -/
abbrev coldIn (substate : Evm.Substate) (target : Address) (n : U256) : Bool :=
  decide (U256.toBeBytes n ∉ substate.accessedStorageKeys.getD target ∅)

/-- The state after SLOAD of slot `n` of `target`: the slot is recorded as read. -/
abbrev readSlot (state : State.TransactionState) (target : Address) (n : U256) :
    State.TransactionState :=
  state.recordStorageRead target (U256.toBeBytes n)

/-- The substate after SLOAD of slot `n` of `target`: the slot is accessed, by EIP-2929. -/
abbrev accessSlot (substate : Evm.Substate) (target : Address) (n : U256) : Evm.Substate :=
  { substate with
    accessedStorageKeys := substate.accessedStorageKeys.insert target
      ((substate.accessedStorageKeys.getD target ∅).insert (U256.toBeBytes n)) }

/-- Reading a slot leaves every slot's word as it is. -/
theorem storageAt_readSlot (state : State.TransactionState) (target other : Address)
    (n m : U256) : storageAt (readSlot state target n) other m = storageAt state other m :=
  (State.TransactionState.recordStorageRead_reads state target other _ _ default).2.1

/-- Accessing a slot leaves another slot as cold or warm as it was. -/
theorem coldIn_accessSlot {substate : Evm.Substate} {target : Address} {n m : U256}
    (h : U256.toBeBytes m ≠ U256.toBeBytes n) :
    coldIn (accessSlot substate target n) target m = coldIn substate target m := by
  simp [coldIn, Std.ExtTreeMap.getD_insert_self, Std.ExtTreeSet.mem_insert, Ne.symm h]

/-- The slot of `key` in a mapping at base slot `base`: the hash of the key word, then the base. -/
def mapSlot (key base : U256) : U256 := Evm.keccak (Evm.wordBytes key ++ Evm.wordBytes base)

/-- Byte 20 of a word, counting from the least significant byte: bits 160 to 167. -/
def byte20 (w : U256) : Nat := w.toNat / 2 ^ 160 % 256

end UsdtVerify
