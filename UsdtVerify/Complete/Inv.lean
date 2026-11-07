import UsdtVerify.Invariant

/-!
# The invariant over every successful call (contract not deprecated)

`inv_X` for each of the 32 functions of the table, and `inv_call` for any call: from Berlin on
(Glamsterdam included, round 17), a fresh frame of `CODE` at pc 0, ANY call data (below 2^256 bytes), ANY
value, ANY gas, any gas bound and any message runner. If the loop of the interpreter ends with no
error and `Inv C state` holds at the start (`C` the contract: the sum of the 2^160 balance words
equals `_totalSupply`), then `Inv C s.state` holds at the end.

Named hypotheses: `K : KeccakSep` (keccak separates the slots, not proved); `hdep` (byte 20 of
slot 10 is 0: not deprecated; the deprecated paths call the upgraded contract); `h7`, `h8`
(`StrForm` of slots 7 and 8, used only by name() and symbol()).

The frame may be static and the contract may have no account. The reachability lemmas `reach_*`
of a writing path need an account of the contract; it comes from the conclusion of `ok_X`: a
successful run of a writing path was in a frame that is not static, of a contract with an
account (otherwise its first SSTORE is `Gas.Stuck`: Complete/Transfer.lean, TransferFrom.lean,
Approve.lean, Owner.lean). The read-only
paths only record reads.

The value, the call data size and the selector are not hypotheses: `runFrame_ok_dispatch` gives
value 0, at least 4 bytes and a selector of the table for every successful run.
-/

namespace UsdtVerify.Complete

open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open UsdtVerify.Gas
open Invariant

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate} {bound : Nat} {runChild : MessageRunner fork Nat bound}
  {evm s : Evm fork Nat} {gas : Nat}

/-- A successful `decimals` call keeps `Inv`. -/
theorem inv_decimals (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x313ce567)
    (hI : Inv message.currentTarget state)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) : Inv message.currentTarget s.state := by
  obtain ⟨-, -, hst, -⟩ := ok_decimals hfork hsize' hsel start within hrun hok
  rw [hst]; simp only [inv_readSlot]; exact hI

/-- A successful `maximumFee` call keeps `Inv`. -/
theorem inv_maximumFee (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x35390714)
    (hI : Inv message.currentTarget state)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) : Inv message.currentTarget s.state := by
  obtain ⟨-, -, hst, -⟩ := ok_maximumFee hfork hsize' hsel start within hrun hok
  rw [hst]; simp only [inv_readSlot]; exact hI

/-- A successful `totalSupplyVar` call keeps `Inv`. -/
theorem inv_totalSupplyVar (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x3eaaf86b)
    (hI : Inv message.currentTarget state)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) : Inv message.currentTarget s.state := by
  obtain ⟨-, -, hst, -⟩ := ok_totalSupplyVar hfork hsize' hsel start within hrun hok
  rw [hst]; simp only [inv_readSlot]; exact hI

/-- A successful `basisPointsRate` call keeps `Inv`. -/
theorem inv_basisPointsRate (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0xdd644f72)
    (hI : Inv message.currentTarget state)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) : Inv message.currentTarget s.state := by
  obtain ⟨-, -, hst, -⟩ := ok_basisPointsRate hfork hsize' hsel start within hrun hok
  rw [hst]; simp only [inv_readSlot]; exact hI

/-- A successful `deprecated` call keeps `Inv`. -/
theorem inv_deprecated (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x0e136b19)
    (hI : Inv message.currentTarget state)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) : Inv message.currentTarget s.state := by
  obtain ⟨-, -, hst, -⟩ := ok_deprecated hfork hsize' hsel start within hrun hok
  rw [hst]; simp only [inv_readSlot]; exact hI

/-- A successful `paused` call keeps `Inv`. -/
theorem inv_paused (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x5c975abb)
    (hI : Inv message.currentTarget state)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) : Inv message.currentTarget s.state := by
  obtain ⟨-, -, hst, -⟩ := ok_paused hfork hsize' hsel start within hrun hok
  rw [hst]; simp only [inv_readSlot]; exact hI

/-- A successful `upgradedAddress` call keeps `Inv`. -/
theorem inv_upgradedAddress (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x26976e3f)
    (hI : Inv message.currentTarget state)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) : Inv message.currentTarget s.state := by
  obtain ⟨-, -, hst, -⟩ := ok_upgradedAddress hfork hsize' hsel start within hrun hok
  rw [hst]; simp only [inv_readSlot]; exact hI

/-- A successful `owner` call keeps `Inv`. -/
theorem inv_owner (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x8da5cb5b)
    (hI : Inv message.currentTarget state)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) : Inv message.currentTarget s.state := by
  obtain ⟨-, -, hst, -⟩ := ok_owner hfork hsize' hsel start within hrun hok
  rw [hst]; simp only [inv_readSlot]; exact hI

/-- A successful `getOwner` call keeps `Inv`. -/
theorem inv_getOwner (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x893d20e8)
    (hI : Inv message.currentTarget state)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) : Inv message.currentTarget s.state := by
  obtain ⟨-, -, hst, -⟩ := ok_getOwner hfork hsize' hsel start within hrun hok
  rw [hst]; simp only [inv_readSlot]; exact hI

/-- A successful `balances` call keeps `Inv`. -/
theorem inv_balances (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x27e235e3)
    (hI : Inv message.currentTarget state)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) : Inv message.currentTarget s.state := by
  obtain ⟨-, -, hst, -⟩ := ok_balances hfork hsize' hsel start within hrun hok
  rw [hst]; simp only [inv_readSlot]; exact hI

/-- A successful `isBlackListed` call keeps `Inv`. -/
theorem inv_isBlackListed (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0xe47d6060)
    (hI : Inv message.currentTarget state)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) : Inv message.currentTarget s.state := by
  obtain ⟨-, -, hst, -⟩ := ok_isBlackListed hfork hsize' hsel start within hrun hok
  rw [hst]; simp only [inv_readSlot]; exact hI

/-- A successful `getBlackListStatus` call keeps `Inv`. -/
theorem inv_getBlackListStatus (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x59bf1abe)
    (hI : Inv message.currentTarget state)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) : Inv message.currentTarget s.state := by
  obtain ⟨-, -, hst, -⟩ := ok_getBlackListStatus hfork hsize' hsel start within hrun hok
  rw [hst]; simp only [inv_readSlot]; exact hI

/-- A successful `allowed` call keeps `Inv`. -/
theorem inv_allowed (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x5c658165)
    (hI : Inv message.currentTarget state)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) : Inv message.currentTarget s.state := by
  obtain ⟨-, -, hst, -⟩ := ok_allowed hfork hsize' hsel start within hrun hok
  rw [hst]; simp only [inv_readSlot]; exact hI

/-- A successful `allowance` call keeps `Inv`. -/
theorem inv_allowance (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0xdd62ed3e)
    (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    (hI : Inv message.currentTarget state)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) : Inv message.currentTarget s.state := by
  obtain ⟨-, -, hst, -⟩ := ok_allowance hfork hsize' hsel hdep start within hrun hok
  rw [hst]; simp only [inv_readSlot]; exact hI

/-- A successful `totalSupply` call keeps `Inv`. -/
theorem inv_totalSupply (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x18160ddd)
    (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    (hI : Inv message.currentTarget state)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) : Inv message.currentTarget s.state := by
  obtain ⟨-, -, hst, -⟩ := ok_totalSupply hfork hsize' hsel hdep start within hrun hok
  rw [hst]; simp only [inv_readSlot]; exact hI

/-- A successful `balanceOf` call keeps `Inv`. -/
theorem inv_balanceOf (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x70a08231)
    (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    (hI : Inv message.currentTarget state)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) : Inv message.currentTarget s.state := by
  obtain ⟨-, -, hst, -⟩ := ok_balanceOf hfork hsize' hsel hdep start within hrun hok
  rw [hst]; simp only [inv_readSlot]; exact hI

/-- A successful `maxUint` call keeps `Inv`. -/
theorem inv_maxUint (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0xe5b5019a)
    (hI : Inv message.currentTarget state)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) : Inv message.currentTarget s.state := by
  obtain ⟨-, -, hst, -⟩ := ok_maxUint hfork hsize' hsel start within hrun hok
  rw [hst]; exact hI

/-- A successful `name` call keeps `Inv`. -/
theorem inv_name (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x06fdde03)
    (hform : StrForm (storageAt state message.currentTarget 7))
    (hI : Inv message.currentTarget state)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) : Inv message.currentTarget s.state := by
  rcases ok_name hfork hsize' hsel hform start within hrun hok with
    ⟨-, -, -, hst, -⟩ | ⟨-, -, -, -, -, -, hst, -⟩ | ⟨-, -, -, -, hst, -⟩ <;>
  · rw [hst]; simp only [inv_readSlot, inv_rdSt]; exact hI

/-- A successful `symbol` call keeps `Inv`. -/
theorem inv_symbol (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x95d89b41)
    (hform : StrForm (storageAt state message.currentTarget 8))
    (hI : Inv message.currentTarget state)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) : Inv message.currentTarget s.state := by
  rcases ok_symbol hfork hsize' hsel hform start within hrun hok with
    ⟨-, -, -, hst, -⟩ | ⟨-, -, -, -, -, -, hst, -⟩ | ⟨-, -, -, -, hst, -⟩ <;>
  · rw [hst]; simp only [inv_readSlot, inv_rdSt]; exact hI

/-- A successful `transfer` call keeps `Inv`. -/
theorem inv_transfer (K : KeccakSep) (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0xa9059cbb)
    (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    (hI : Inv message.currentTarget state)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) : Inv message.currentTarget s.state := by
  obtain ⟨-, hacc, -, -, -, -, hfv, hbal, hto, -, h⟩ := ok_transfer hfork hsize' hsel hdep
    rfl rfl rfl rfl rfl rfl rfl rfl start within hrun hok
  rcases h with ⟨hfee, -, hst, -⟩ | ⟨-, hown, -, hst, -⟩
  · rw [hst]; rw [sendOf_zero hfee] at hto; exact steps_inv K (reach_transfer_ok hacc hbal hto) hI
  · rw [hst]; exact steps_inv K (reach_transfer_fee hacc hfv hbal hto hown) hI

/-- A successful `transferFrom` call keeps `Inv`. -/
theorem inv_transferFrom (K : KeccakSep) (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x23b872dd)
    (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    (hI : Inv message.currentTarget state)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) : Inv message.currentTarget s.state := by
  obtain ⟨-, hacc, -, -, -, -, -, hfv, hbal, hto, -, h⟩ := ok_transferFrom hfork hsize'
    hsel hdep rfl rfl rfl rfl rfl rfl rfl rfl rfl start within hrun hok
  rcases h with ⟨hfee, -, hst, -⟩ | ⟨-, hown, -, hst, -⟩
  · rw [hst]; rw [sendOf_zero hfee] at hto
    exact steps_inv K (reach_transferFrom_ok hacc hbal hto) hI
  · rw [hst]; exact steps_inv K (reach_transferFrom_fee hacc hfv hbal hto hown) hI

/-- A successful `approve` call keeps `Inv`. -/
theorem inv_approve (K : KeccakSep) (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x095ea7b3)
    (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    (hI : Inv message.currentTarget state)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) : Inv message.currentTarget s.state := by
  obtain ⟨-, hacc, -, -, h⟩ := ok_approve hfork hsize' hsel hdep rfl rfl start within
    hrun hok
  rcases h with ⟨-, -, hst, -⟩ | ⟨-, -, -, hst, -⟩
  · rw [hst]; exact steps_inv K (reach_approve_zero hacc) hI
  · rw [hst]; exact steps_inv K (reach_approve_set hacc) hI

/-- A successful `pause` call keeps `Inv`. -/
theorem inv_pause (K : KeccakSep) (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x8456cb59)
    (hI : Inv message.currentTarget state)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) : Inv message.currentTarget s.state := by
  obtain ⟨-, hacc, -, -, -, -, hst, -⟩ := ok_pause hfork hsize' hsel rfl start within hrun hok
  rw [hst]; exact steps_inv K (reach_pause hacc 1) hI

/-- A successful `unpause` call keeps `Inv`. -/
theorem inv_unpause (K : KeccakSep) (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x3f4ba83a)
    (hI : Inv message.currentTarget state)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) : Inv message.currentTarget s.state := by
  obtain ⟨-, hacc, -, -, -, -, hst, -⟩ := ok_unpause hfork hsize' hsel rfl start within hrun
    hok
  rw [hst]; exact steps_inv K (reach_pause hacc 0) hI

/-- A successful `addBlackList` call keeps `Inv`. -/
theorem inv_addBlackList (K : KeccakSep) (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x0ecb93c0)
    (hI : Inv message.currentTarget state)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) : Inv message.currentTarget s.state := by
  obtain ⟨-, hacc, -, -, -, hst, -⟩ := ok_addBlackList hfork hsize' hsel rfl rfl start
    within hrun hok
  rw [hst]; exact steps_inv K (reach_list hacc 1) hI

/-- A successful `removeBlackList` call keeps `Inv`. -/
theorem inv_removeBlackList (K : KeccakSep) (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0xe4997dc5)
    (hI : Inv message.currentTarget state)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) : Inv message.currentTarget s.state := by
  obtain ⟨-, hacc, -, -, -, hst, -⟩ := ok_removeBlackList hfork hsize' hsel rfl rfl start
    within hrun hok
  rw [hst]; exact steps_inv K (reach_list hacc 0) hI

/-- A successful `issue` call keeps `Inv`. -/
theorem inv_issue (K : KeccakSep) (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0xcc872b66)
    (hI : Inv message.currentTarget state)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) : Inv message.currentTarget s.state := by
  obtain ⟨-, hacc, -, h0, hT, hB, -, -, hst, -⟩ := ok_issue hfork hsize' hsel rfl rfl rfl
    start within hrun hok
  rw [hst]; exact steps_inv K (reach_issue hacc ⟨h0, hT⟩ hB) hI

/-- A successful `redeem` call keeps `Inv`. -/
theorem inv_redeem (K : KeccakSep) (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0xdb006a75)
    (hI : Inv message.currentTarget state)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) : Inv message.currentTarget s.state := by
  obtain ⟨-, hacc, -, hT, hB, -, -, hst, -⟩ := ok_redeem hfork hsize' hsel rfl rfl rfl
    start within hrun hok
  rw [hst]; exact steps_inv K (reach_redeem hacc hT hB) hI

/-- A successful `setParams` call keeps `Inv`. -/
theorem inv_setParams (K : KeccakSep) (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0xc0324c77)
    (hI : Inv message.currentTarget state)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) : Inv message.currentTarget s.state := by
  obtain ⟨-, hacc, -, -, -, -, -, -, hst, -⟩ := ok_setParams hfork hsize' hsel rfl rfl rfl
    rfl start within hrun hok
  rw [hst]; exact steps_inv K (reach_setParams hacc) hI

/-- A successful `deprecate` call keeps `Inv`. -/
theorem inv_deprecate (K : KeccakSep) (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x0753c30c)
    (hI : Inv message.currentTarget state)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) : Inv message.currentTarget s.state := by
  obtain ⟨-, hacc, -, -, -, hst, -⟩ := ok_deprecate hfork hsize' hsel rfl rfl start within
    hrun hok
  rw [hst]; exact steps_inv K (reach_deprecate hacc) hI

/-- A successful `transferOwnership` call keeps `Inv`. -/
theorem inv_transferOwnership (K : KeccakSep) (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0xf2fde38b)
    (hI : Inv message.currentTarget state)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) : Inv message.currentTarget s.state := by
  obtain ⟨-, -, h⟩ := ok_transferOwnership hfork hsize' hsel rfl start within hrun
    hok
  rcases h with ⟨-, -, hst, -⟩ | ⟨-, -, hacc, -, hst, -⟩
  · rw [hst]; simp only [inv_readSlot]; exact hI
  · rw [hst]; exact steps_inv K (reach_transferOwnership hacc) hI

/-- A successful `destroyBlackFunds` call keeps `Inv`. -/
theorem inv_destroyBlackFunds (K : KeccakSep) (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0xf3bdc228)
    (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    (hI : Inv message.currentTarget state)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) : Inv message.currentTarget s.state := by
  obtain ⟨-, hacc, -, -, -, -, hst, -⟩ := ok_destroyBlackFunds hfork hsize' hsel hdep rfl
    rfl rfl rfl rfl start within hrun hok
  rw [hst]; exact steps_inv K (reach_destroy hacc) hI


/-- **Every successful call keeps the invariant** (contract not deprecated).

From Berlin on (Glamsterdam included), a fresh frame of `CODE` at pc 0 with any call data below
2^256 bytes, any value, any gas, any gas bound and any message runner, static or not, with or
without an account of the contract. Under `KeccakSep`, not deprecated, and with string slots 7
and 8 of `StrForm`: if `Inv C state` holds and the interpreter loop ends with no error, then
`Inv C s.state` holds. -/
theorem inv_call (K : KeccakSep) (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    (h7 : StrForm (storageAt state message.currentTarget 7))
    (h8 : StrForm (storageAt state message.currentTarget 8))
    (hI : Inv message.currentTarget state)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) : Inv message.currentTarget s.state := by
  obtain ⟨-, -, i, hi⟩ := runFrame_ok_dispatch hfork hsize' start within hrun hok
  match i, hi with
  | ⟨0, _⟩, hi => exact inv_name hfork hsize' (hi.trans rfl) h7 hI start within hrun hok
  | ⟨1, _⟩, hi => exact inv_deprecate K hfork hsize' (hi.trans rfl) hI start within hrun hok
  | ⟨2, _⟩, hi => exact inv_approve K hfork hsize' (hi.trans rfl) hdep hI start within hrun hok
  | ⟨3, _⟩, hi => exact inv_deprecated hfork hsize' (hi.trans rfl) hI start within hrun hok
  | ⟨4, _⟩, hi => exact inv_addBlackList K hfork hsize' (hi.trans rfl) hI start within hrun hok
  | ⟨5, _⟩, hi => exact inv_totalSupply hfork hsize' (hi.trans rfl) hdep hI start within hrun hok
  | ⟨6, _⟩, hi => exact inv_transferFrom K hfork hsize' (hi.trans rfl) hdep hI start within hrun hok
  | ⟨7, _⟩, hi => exact inv_upgradedAddress hfork hsize' (hi.trans rfl) hI start within hrun hok
  | ⟨8, _⟩, hi => exact inv_balances hfork hsize' (hi.trans rfl) hI start within hrun hok
  | ⟨9, _⟩, hi => exact inv_decimals hfork hsize' (hi.trans rfl) hI start within hrun hok
  | ⟨10, _⟩, hi => exact inv_maximumFee hfork hsize' (hi.trans rfl) hI start within hrun hok
  | ⟨11, _⟩, hi => exact inv_totalSupplyVar hfork hsize' (hi.trans rfl) hI start within hrun hok
  | ⟨12, _⟩, hi => exact inv_unpause K hfork hsize' (hi.trans rfl) hI start within hrun hok
  | ⟨13, _⟩, hi => exact inv_getBlackListStatus hfork hsize' (hi.trans rfl) hI start within hrun hok
  | ⟨14, _⟩, hi => exact inv_allowed hfork hsize' (hi.trans rfl) hI start within hrun hok
  | ⟨15, _⟩, hi => exact inv_paused hfork hsize' (hi.trans rfl) hI start within hrun hok
  | ⟨16, _⟩, hi => exact inv_balanceOf hfork hsize' (hi.trans rfl) hdep hI start within hrun hok
  | ⟨17, _⟩, hi => exact inv_pause K hfork hsize' (hi.trans rfl) hI start within hrun hok
  | ⟨18, _⟩, hi => exact inv_getOwner hfork hsize' (hi.trans rfl) hI start within hrun hok
  | ⟨19, _⟩, hi => exact inv_owner hfork hsize' (hi.trans rfl) hI start within hrun hok
  | ⟨20, _⟩, hi => exact inv_symbol hfork hsize' (hi.trans rfl) h8 hI start within hrun hok
  | ⟨21, _⟩, hi => exact inv_transfer K hfork hsize' (hi.trans rfl) hdep hI start within hrun hok
  | ⟨22, _⟩, hi => exact inv_setParams K hfork hsize' (hi.trans rfl) hI start within hrun hok
  | ⟨23, _⟩, hi => exact inv_issue K hfork hsize' (hi.trans rfl) hI start within hrun hok
  | ⟨24, _⟩, hi => exact inv_redeem K hfork hsize' (hi.trans rfl) hI start within hrun hok
  | ⟨25, _⟩, hi => exact inv_allowance hfork hsize' (hi.trans rfl) hdep hI start within hrun hok
  | ⟨26, _⟩, hi => exact inv_basisPointsRate hfork hsize' (hi.trans rfl) hI start within hrun hok
  | ⟨27, _⟩, hi => exact inv_isBlackListed hfork hsize' (hi.trans rfl) hI start within hrun hok
  | ⟨28, _⟩, hi => exact inv_removeBlackList K hfork hsize' (hi.trans rfl) hI start within hrun hok
  | ⟨29, _⟩, hi => exact inv_maxUint hfork hsize' (hi.trans rfl) hI start within hrun hok
  | ⟨30, _⟩, hi => exact inv_transferOwnership K hfork hsize' (hi.trans rfl) hI start within hrun hok
  | ⟨31, _⟩, hi => exact inv_destroyBlackFunds K hfork hsize' (hi.trans rfl) hdep hI start within hrun hok
  | ⟨n + 32, h⟩, _ => exact absurd h (by omega)

end UsdtVerify.Complete
