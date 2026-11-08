import UsdtVerify.Evm.Exact
import UsdtVerify.Usdt.Complete.Dispatch
import UsdtVerify.Usdt.Spec.Getters
import UsdtVerify.Usdt.Spec.Strings

/-!
# Completeness of the getters and of name() / symbol()

For each getter (decimals, maximumFee, _totalSupply, basisPointsRate, deprecated, paused,
upgradedAddress, owner, getOwner, MAX_UINT, balances, isBlackListed, getBlackListStatus,
allowed, and allowance when not deprecated): every run of a call with its selector that ends with
no error, for any gas, gas bound and message runner, is the path of its specification, with the
exact output, gas, state (only reads) and substate. Hypotheses: Berlin ≤ fork, size < 2^256, the
selector; `hdep` (not deprecated) for allowance.

name() and symbol(): the same, under the named hypothesis `StrForm w` on the slot word `w`
(slot 7, resp. 8): the low byte is 0 (empty string), or `2 n` with 1 ≤ n ≤ 31 (short form), or
`w` is odd with 32 ≤ w / 2 < 2^180 (long form). These are the shapes that Solidity writes (a
long string of 2^180 bytes or more cannot be stored); the other words are not covered by a
specification, so `StrForm` stays a hypothesis.
-/

namespace UsdtVerify.Complete

open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open UsdtVerify.Gas
open Transfer TransferOk Owner StringsGen

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate} {bound : Nat} {runChild : MessageRunner fork Nat bound}
  {evm s : Evm fork Nat} {gas : Nat}

/-- Every successful `decimals` call is the path of `Getters.spec_decimals`. -/
theorem ok_decimals (hfork : .berlin ≤ fork) (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x313ce567)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) :
    s.output = wordBytes (storageAt state message.currentTarget 9) ∧
      ((384 + slotCost (coldIn substate message.currentTarget 9)) ≤ gas ∧
        s.gas = gas - (384 + slotCost (coldIn substate message.currentTarget 9))) ∧
      s.state = (readSlot state message.currentTarget 9) ∧ s.substate = (accessSlot substate message.currentTarget 9) := by
  obtain ⟨h4, hv, -⟩ := runFrame_ok_dispatch hfork hsize' start within hrun hok
  obtain ⟨hcg, -, ho, hg, hst, hss⟩ := ok_exact (Nat.le_refl _)
    (fun g hg => Getters.spec_decimals hfork h4 hsize' hsel hv rfl hg) start within hrun hok
  exact ⟨ho, ⟨hcg, hg⟩, hst, hss⟩

/-- Every successful `maximumFee` call is the path of `Getters.spec_maximumFee`. -/
theorem ok_maximumFee (hfork : .berlin ≤ fork) (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x35390714)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) :
    s.output = wordBytes (storageAt state message.currentTarget 4) ∧
      ((406 + slotCost (coldIn substate message.currentTarget 4)) ≤ gas ∧
        s.gas = gas - (406 + slotCost (coldIn substate message.currentTarget 4))) ∧
      s.state = (readSlot state message.currentTarget 4) ∧ s.substate = (accessSlot substate message.currentTarget 4) := by
  obtain ⟨h4, hv, -⟩ := runFrame_ok_dispatch hfork hsize' start within hrun hok
  obtain ⟨hcg, -, ho, hg, hst, hss⟩ := ok_exact (Nat.le_refl _)
    (fun g hg => Getters.spec_maximumFee hfork h4 hsize' hsel hv rfl hg) start within hrun hok
  exact ⟨ho, ⟨hcg, hg⟩, hst, hss⟩

/-- Every successful `totalSupplyVar` call is the path of `Getters.spec_totalSupplyVar`. -/
theorem ok_totalSupplyVar (hfork : .berlin ≤ fork) (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x3eaaf86b)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) :
    s.output = wordBytes (storageAt state message.currentTarget 1) ∧
      ((428 + slotCost (coldIn substate message.currentTarget 1)) ≤ gas ∧
        s.gas = gas - (428 + slotCost (coldIn substate message.currentTarget 1))) ∧
      s.state = (readSlot state message.currentTarget 1) ∧ s.substate = (accessSlot substate message.currentTarget 1) := by
  obtain ⟨h4, hv, -⟩ := runFrame_ok_dispatch hfork hsize' start within hrun hok
  obtain ⟨hcg, -, ho, hg, hst, hss⟩ := ok_exact (Nat.le_refl _)
    (fun g hg => Getters.spec_totalSupplyVar hfork h4 hsize' hsel hv rfl hg) start within hrun hok
  exact ⟨ho, ⟨hcg, hg⟩, hst, hss⟩

/-- Every successful `basisPointsRate` call is the path of `Getters.spec_basisPointsRate`. -/
theorem ok_basisPointsRate (hfork : .berlin ≤ fork) (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0xdd644f72)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) :
    s.output = wordBytes (storageAt state message.currentTarget 3) ∧
      ((758 + slotCost (coldIn substate message.currentTarget 3)) ≤ gas ∧
        s.gas = gas - (758 + slotCost (coldIn substate message.currentTarget 3))) ∧
      s.state = (readSlot state message.currentTarget 3) ∧ s.substate = (accessSlot substate message.currentTarget 3) := by
  obtain ⟨h4, hv, -⟩ := runFrame_ok_dispatch hfork hsize' start within hrun hok
  obtain ⟨hcg, -, ho, hg, hst, hss⟩ := ok_exact (Nat.le_refl _)
    (fun g hg => Getters.spec_basisPointsRate hfork h4 hsize' hsel hv rfl hg) start within hrun hok
  exact ⟨ho, ⟨hcg, hg⟩, hst, hss⟩

/-- Every successful `deprecated` call is the path of `Getters.spec_deprecated`. -/
theorem ok_deprecated (hfork : .berlin ≤ fork) (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x0e136b19)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) :
    s.output = wordBytes (if byte20 (storageAt state message.currentTarget 10) = 0 then 0 else 1) ∧
      ((350 + slotCost (coldIn substate message.currentTarget 10)) ≤ gas ∧
        s.gas = gas - (350 + slotCost (coldIn substate message.currentTarget 10))) ∧
      s.state = (readSlot state message.currentTarget 10) ∧ s.substate = (accessSlot substate message.currentTarget 10) := by
  obtain ⟨h4, hv, -⟩ := runFrame_ok_dispatch hfork hsize' start within hrun hok
  obtain ⟨hcg, -, ho, hg, hst, hss⟩ := ok_exact (Nat.le_refl _)
    (fun g hg => Getters.spec_deprecated hfork h4 hsize' hsel hv rfl hg) start within hrun hok
  exact ⟨ho, ⟨hcg, hg⟩, hst, hss⟩

/-- Every successful `paused` call is the path of `Getters.spec_paused`. -/
theorem ok_paused (hfork : .berlin ≤ fork) (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x5c975abb)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) :
    s.output = wordBytes (if byte20 (storageAt state message.currentTarget 0) = 0 then 0 else 1) ∧
      ((614 + slotCost (coldIn substate message.currentTarget 0)) ≤ gas ∧
        s.gas = gas - (614 + slotCost (coldIn substate message.currentTarget 0))) ∧
      s.state = (readSlot state message.currentTarget 0) ∧ s.substate = (accessSlot substate message.currentTarget 0) := by
  obtain ⟨h4, hv, -⟩ := runFrame_ok_dispatch hfork hsize' start within hrun hok
  obtain ⟨hcg, -, ho, hg, hst, hss⟩ := ok_exact (Nat.le_refl _)
    (fun g hg => Getters.spec_paused hfork h4 hsize' hsel hv rfl hg) start within hrun hok
  exact ⟨ho, ⟨hcg, hg⟩, hst, hss⟩

/-- Every successful `upgradedAddress` call is the path of `Getters.spec_upgradedAddress`. -/
theorem ok_upgradedAddress (hfork : .berlin ≤ fork) (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x26976e3f)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) :
    s.output = wordBytes (bitwiseAnd ADDR_MASK (storageAt state message.currentTarget 10)) ∧
      ((388 + slotCost (coldIn substate message.currentTarget 10)) ≤ gas ∧
        s.gas = gas - (388 + slotCost (coldIn substate message.currentTarget 10))) ∧
      s.state = (readSlot state message.currentTarget 10) ∧ s.substate = (accessSlot substate message.currentTarget 10) := by
  obtain ⟨h4, hv, -⟩ := runFrame_ok_dispatch hfork hsize' start within hrun hok
  obtain ⟨hcg, -, ho, hg, hst, hss⟩ := ok_exact (Nat.le_refl _)
    (fun g hg => Getters.spec_upgradedAddress hfork h4 hsize' hsel hv rfl hg) start within hrun hok
  exact ⟨ho, ⟨hcg, hg⟩, hst, hss⟩

/-- Every successful `owner` call is the path of `Getters.spec_owner`. -/
theorem ok_owner (hfork : .berlin ≤ fork) (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x8da5cb5b)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) :
    s.output = wordBytes (ownerOf state message.currentTarget) ∧
      ((652 + slotCost (coldIn substate message.currentTarget 0)) ≤ gas ∧
        s.gas = gas - (652 + slotCost (coldIn substate message.currentTarget 0))) ∧
      s.state = (readSlot state message.currentTarget 0) ∧ s.substate = (accessSlot substate message.currentTarget 0) := by
  obtain ⟨h4, hv, -⟩ := runFrame_ok_dispatch hfork hsize' start within hrun hok
  obtain ⟨hcg, -, ho, hg, hst, hss⟩ := ok_exact (Nat.le_refl _)
    (fun g hg => Getters.spec_owner hfork h4 hsize' hsel hv rfl hg) start within hrun hok
  exact ⟨ho, ⟨hcg, hg⟩, hst, hss⟩

/-- Every successful `getOwner` call is the path of `Getters.spec_getOwner`. -/
theorem ok_getOwner (hfork : .berlin ≤ fork) (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x893d20e8)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) :
    s.output = wordBytes (ownerOf state message.currentTarget) ∧
      ((638 + slotCost (coldIn substate message.currentTarget 0)) ≤ gas ∧
        s.gas = gas - (638 + slotCost (coldIn substate message.currentTarget 0))) ∧
      s.state = (readSlot state message.currentTarget 0) ∧ s.substate = (accessSlot substate message.currentTarget 0) := by
  obtain ⟨h4, hv, -⟩ := runFrame_ok_dispatch hfork hsize' start within hrun hok
  obtain ⟨hcg, -, ho, hg, hst, hss⟩ := ok_exact (Nat.le_refl _)
    (fun g hg => Getters.spec_getOwner hfork h4 hsize' hsel hv rfl hg) start within hrun hok
  exact ⟨ho, ⟨hcg, hg⟩, hst, hss⟩

/-- Every successful `maxUint` call is the path of `Getters.spec_maxUint`. -/
theorem ok_maxUint (hfork : .berlin ≤ fork) (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0xe5b5019a)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) :
    s.output = wordBytes (BitVec.ofNat 256 (2 ^ 256 - 1)) ∧
      ((824) ≤ gas ∧ s.gas = gas - (824)) ∧
      s.state = state ∧ s.substate = substate := by
  obtain ⟨h4, hv, -⟩ := runFrame_ok_dispatch hfork hsize' start within hrun hok
  obtain ⟨hcg, -, ho, hg, hst, hss⟩ := ok_exact (Nat.le_refl _)
    (fun g hg => Getters.spec_maxUint h4 hsize' hsel hv hg) start within hrun hok
  exact ⟨ho, ⟨hcg, hg⟩, hst, hss⟩

/-- Every successful `balances` call is the path of `GettersMap.spec_balances`. -/
theorem ok_balances (hfork : .berlin ≤ fork) (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x27e235e3)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) :
    s.output = wordBytes (storageAt state message.currentTarget (mapSlot (addrArg message.data 0) 2)) ∧
      ((478 + slotCost (coldIn substate message.currentTarget (mapSlot (addrArg message.data 0) 2))) ≤ gas ∧
        s.gas = gas - (478 + slotCost (coldIn substate message.currentTarget (mapSlot (addrArg message.data 0) 2)))) ∧
      s.state = (readSlot state message.currentTarget (mapSlot (addrArg message.data 0) 2)) ∧ s.substate = (accessSlot substate message.currentTarget (mapSlot (addrArg message.data 0) 2)) := by
  obtain ⟨h4, hv, -⟩ := runFrame_ok_dispatch hfork hsize' start within hrun hok
  obtain ⟨hcg, -, ho, hg, hst, hss⟩ := ok_exact (Nat.le_refl _)
    (fun g hg => GettersMap.spec_balances hfork h4 hsize' hsel hv rfl hg) start within hrun hok
  exact ⟨ho, ⟨hcg, hg⟩, hst, hss⟩

/-- Every successful `isBlackListed` call is the path of `GettersMap.spec_isBlackListed`. -/
theorem ok_isBlackListed (hfork : .berlin ≤ fork) (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0xe47d6060)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) :
    s.output = wordBytes (if (storageAt state message.currentTarget (mapSlot (addrArg message.data 0) 6)).toNat % 256 = 0 then 0 else 1) ∧
      ((933 + slotCost (coldIn substate message.currentTarget (mapSlot (addrArg message.data 0) 6))) ≤ gas ∧
        s.gas = gas - (933 + slotCost (coldIn substate message.currentTarget (mapSlot (addrArg message.data 0) 6)))) ∧
      s.state = (readSlot state message.currentTarget (mapSlot (addrArg message.data 0) 6)) ∧ s.substate = (accessSlot substate message.currentTarget (mapSlot (addrArg message.data 0) 6)) := by
  obtain ⟨h4, hv, -⟩ := runFrame_ok_dispatch hfork hsize' start within hrun hok
  obtain ⟨hcg, -, ho, hg, hst, hss⟩ := ok_exact (Nat.le_refl _)
    (fun g hg => GettersMap.spec_isBlackListed hfork h4 hsize' hsel hv rfl hg) start within hrun hok
  exact ⟨ho, ⟨hcg, hg⟩, hst, hss⟩

/-- Every successful `getBlackListStatus` call is the path of `GettersMap.spec_getBlackListStatus`. -/
theorem ok_getBlackListStatus (hfork : .berlin ≤ fork) (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x59bf1abe)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) :
    s.output = wordBytes (if (storageAt state message.currentTarget (mapSlot (addrArg message.data 0) 6)).toNat % 256 = 0 then 0 else 1) ∧
      ((663 + slotCost (coldIn substate message.currentTarget (mapSlot (addrArg message.data 0) 6))) ≤ gas ∧
        s.gas = gas - (663 + slotCost (coldIn substate message.currentTarget (mapSlot (addrArg message.data 0) 6)))) ∧
      s.state = (readSlot state message.currentTarget (mapSlot (addrArg message.data 0) 6)) ∧ s.substate = (accessSlot substate message.currentTarget (mapSlot (addrArg message.data 0) 6)) := by
  obtain ⟨h4, hv, -⟩ := runFrame_ok_dispatch hfork hsize' start within hrun hok
  obtain ⟨hcg, -, ho, hg, hst, hss⟩ := ok_exact (Nat.le_refl _)
    (fun g hg => GettersMap.spec_getBlackListStatus hfork h4 hsize' hsel hv rfl hg) start within hrun hok
  exact ⟨ho, ⟨hcg, hg⟩, hst, hss⟩

/-- Every successful `allowed` call is the path of `GettersMap.spec_allowed`. -/
theorem ok_allowed (hfork : .berlin ≤ fork) (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x5c658165)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) :
    s.output = wordBytes (storageAt state message.currentTarget (GettersMap.allowSlot message.data)) ∧
      ((705 + slotCost (coldIn substate message.currentTarget (GettersMap.allowSlot message.data))) ≤ gas ∧
        s.gas = gas - (705 + slotCost (coldIn substate message.currentTarget (GettersMap.allowSlot message.data)))) ∧
      s.state = (readSlot state message.currentTarget (GettersMap.allowSlot message.data)) ∧ s.substate = (accessSlot substate message.currentTarget (GettersMap.allowSlot message.data)) := by
  obtain ⟨h4, hv, -⟩ := runFrame_ok_dispatch hfork hsize' start within hrun hok
  obtain ⟨hcg, -, ho, hg, hst, hss⟩ := ok_exact (Nat.le_refl _)
    (fun g hg => GettersMap.spec_allowed hfork h4 hsize' hsel hv rfl hg) start within hrun hok
  exact ⟨ho, ⟨hcg, hg⟩, hst, hss⟩

/-- Every successful `allowance` call is the path of `GettersMap.spec_allowance`. -/
theorem ok_allowance (hfork : .berlin ≤ fork) (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0xdd62ed3e)
    (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) :
    s.output = wordBytes (storageAt state message.currentTarget (GettersMap.allowSlot message.data)) ∧
      ((1156 + slotCost (coldIn substate message.currentTarget 10) + slotCost (coldIn (accessSlot substate message.currentTarget 10) message.currentTarget (GettersMap.allowSlot message.data))) ≤ gas ∧
        s.gas = gas - (1156 + slotCost (coldIn substate message.currentTarget 10) + slotCost (coldIn (accessSlot substate message.currentTarget 10) message.currentTarget (GettersMap.allowSlot message.data)))) ∧
      s.state = (readSlot (readSlot state message.currentTarget 10) message.currentTarget (GettersMap.allowSlot message.data)) ∧ s.substate = (accessSlot (accessSlot substate message.currentTarget 10) message.currentTarget (GettersMap.allowSlot message.data)) := by
  obtain ⟨h4, hv, -⟩ := runFrame_ok_dispatch hfork hsize' start within hrun hok
  obtain ⟨hcg, -, ho, hg, hst, hss⟩ := ok_exact (Nat.le_refl _)
    (fun g hg => GettersMap.spec_allowance hfork h4 hsize' hsel hv hdep rfl rfl hg) start within hrun hok
  exact ⟨ho, ⟨hcg, hg⟩, hst, hss⟩


/-- The slot words of a `string` that Solidity writes: empty (low byte 0), short (low byte `2 n`,
1 ≤ n ≤ 31), or long (odd, `32 ≤ w / 2`), the long length below 2^180. A named hypothesis of
`ok_name` / `ok_symbol`. -/
def StrForm (w : U256) : Prop :=
  w.toNat % 256 = 0 ∨ (∃ n, w.toNat % 256 = 2 * n ∧ 1 ≤ n ∧ n ≤ 31) ∨
    (w.toNat % 2 = 1 ∧ 32 ≤ w.toNat / 2 ∧ w.toNat / 2 < 2 ^ 180)

/-- The length of a long string in slot word `w`. -/
abbrev strN (w : U256) : Nat := w.toNat / 2

/-- Every successful `name()` call, for a slot word of `StrForm`, is the empty, the short or
the long path. -/
theorem ok_name (hfork : .berlin ≤ fork) (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x06fdde03) (hform : StrForm (storageAt state message.currentTarget 7))
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) :
    ((storageAt state message.currentTarget 7).toNat % 256 = 0 ∧ s.output = wordBytes 0x20 ++ wordBytes 0 ∧
      ((643 + slotCost (coldIn substate message.currentTarget 7)) ≤ gas ∧
        s.gas = gas - (643 + slotCost (coldIn substate message.currentTarget 7))) ∧
      s.state = readSlot state message.currentTarget 7 ∧ s.substate = accessSlot substate message.currentTarget 7) ∨
    (∃ n, (storageAt state message.currentTarget 7).toNat % 256 = 2 * n ∧ 1 ≤ n ∧ n ≤ 31 ∧
      s.output = wordBytes 0x20 ++ wordBytes (BitVec.ofNat 256 n) ++
        wordBytes (Strings.topBytes (storageAt state message.currentTarget 7) n) ∧
      ((1010 + slotCost (coldIn substate message.currentTarget 7)) ≤ gas ∧
        s.gas = gas - (1010 + slotCost (coldIn substate message.currentTarget 7))) ∧
      s.state = readSlot state message.currentTarget 7 ∧ s.substate = accessSlot substate message.currentTarget 7) ∨
    ((storageAt state message.currentTarget 7).toNat % 2 = 1 ∧ 32 ≤ (strN (storageAt state message.currentTarget 7)) ∧
      s.output = wordBytes 0x20 ++ wordBytes (StringsGen.wd (strN (storageAt state message.currentTarget 7))) ++
        StringsGen.strData (fun i => storageAt state message.currentTarget
          (StringsGen.slotJ (keccak (wordBytes 7)) i)) (strN (storageAt state message.currentTarget 7)) ∧
      ((62 + 22 * 1 + 34 + (102 + slotCost (coldIn substate message.currentTarget 7)) + 281 + (50 * (((strN (storageAt state message.currentTarget 7)) + 31) / 32 - 1) + 96 + rdGas (accessSlot substate message.currentTarget 7) message.currentTarget (keccak (wordBytes 7)) (((strN (storageAt state message.currentTarget 7)) + 31) / 32) + (mg (128 + 32 * (((strN (storageAt state message.currentTarget 7)) + 31) / 32)) - mg 128)) + retCost (128 + 32 * (((strN (storageAt state message.currentTarget 7)) + 31) / 32)) (strN (storageAt state message.currentTarget 7))) ≤ gas ∧
        s.gas = gas - (62 + 22 * 1 + 34 + (102 + slotCost (coldIn substate message.currentTarget 7)) + 281 + (50 * (((strN (storageAt state message.currentTarget 7)) + 31) / 32 - 1) + 96 + rdGas (accessSlot substate message.currentTarget 7) message.currentTarget (keccak (wordBytes 7)) (((strN (storageAt state message.currentTarget 7)) + 31) / 32) + (mg (128 + 32 * (((strN (storageAt state message.currentTarget 7)) + 31) / 32)) - mg 128)) + retCost (128 + 32 * (((strN (storageAt state message.currentTarget 7)) + 31) / 32)) (strN (storageAt state message.currentTarget 7)))) ∧
      s.state = StringsGen.rdSt (readSlot state message.currentTarget 7) message.currentTarget (keccak (wordBytes 7))
        (((strN (storageAt state message.currentTarget 7)) + 31) / 32) ∧
      s.substate = StringsGen.rdSs (accessSlot substate message.currentTarget 7) message.currentTarget
        (keccak (wordBytes 7)) (((strN (storageAt state message.currentTarget 7)) + 31) / 32)) := by
  obtain ⟨h4, hv, -⟩ := runFrame_ok_dispatch hfork hsize' start within hrun hok
  rcases hform with h0 | ⟨n, hn, h1, h31⟩ | ⟨hodd, h32, hN⟩
  · obtain ⟨hcg, -, ho, hg, hst, hss⟩ := ok_exact (Nat.le_refl _)
      (fun g hg => StringsGen.spec_nameEmpty hfork h4 hsize' hsel hv h0 rfl hg) start within hrun hok
    exact .inl ⟨h0, ho, ⟨hcg, hg⟩, hst, hss⟩
  · obtain ⟨hcg, -, ho, hg, hst, hss⟩ := ok_exact (Nat.le_refl _)
      (fun g hg => Strings.spec_name hfork h4 hsize' hsel hv hn h1 h31 rfl hg) start within hrun hok
    exact .inr (.inl ⟨n, hn, h1, h31, ho, ⟨hcg, hg⟩, hst, hss⟩)
  · obtain ⟨hcg, -, ho, hg, hst, hss⟩ := ok_exact (Nat.le_refl _)
      (fun g hg => StringsGen.spec_nameLong hfork h4 hsize' hsel hv hodd rfl h32 hN rfl hg) start within hrun hok
    exact .inr (.inr ⟨hodd, h32, ho, ⟨hcg, hg⟩, hst, hss⟩)

/-- Every successful `symbol()` call, for a slot word of `StrForm`, is the empty, the short or
the long path. -/
theorem ok_symbol (hfork : .berlin ≤ fork) (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x95d89b41) (hform : StrForm (storageAt state message.currentTarget 8))
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) :
    ((storageAt state message.currentTarget 8).toNat % 256 = 0 ∧ s.output = wordBytes 0x20 ++ wordBytes 0 ∧
      ((1083 + slotCost (coldIn substate message.currentTarget 8)) ≤ gas ∧
        s.gas = gas - (1083 + slotCost (coldIn substate message.currentTarget 8))) ∧
      s.state = readSlot state message.currentTarget 8 ∧ s.substate = accessSlot substate message.currentTarget 8) ∨
    (∃ n, (storageAt state message.currentTarget 8).toNat % 256 = 2 * n ∧ 1 ≤ n ∧ n ≤ 31 ∧
      s.output = wordBytes 0x20 ++ wordBytes (BitVec.ofNat 256 n) ++
        wordBytes (Strings.topBytes (storageAt state message.currentTarget 8) n) ∧
      ((1450 + slotCost (coldIn substate message.currentTarget 8)) ≤ gas ∧
        s.gas = gas - (1450 + slotCost (coldIn substate message.currentTarget 8))) ∧
      s.state = readSlot state message.currentTarget 8 ∧ s.substate = accessSlot substate message.currentTarget 8) ∨
    ((storageAt state message.currentTarget 8).toNat % 2 = 1 ∧ 32 ≤ (strN (storageAt state message.currentTarget 8)) ∧
      s.output = wordBytes 0x20 ++ wordBytes (StringsGen.wd (strN (storageAt state message.currentTarget 8))) ++
        StringsGen.strData (fun i => storageAt state message.currentTarget
          (StringsGen.slotJ (keccak (wordBytes 8)) i)) (strN (storageAt state message.currentTarget 8)) ∧
      ((62 + 22 * 21 + 34 + (102 + slotCost (coldIn substate message.currentTarget 8)) + 281 + (50 * (((strN (storageAt state message.currentTarget 8)) + 31) / 32 - 1) + 96 + rdGas (accessSlot substate message.currentTarget 8) message.currentTarget (keccak (wordBytes 8)) (((strN (storageAt state message.currentTarget 8)) + 31) / 32) + (mg (128 + 32 * (((strN (storageAt state message.currentTarget 8)) + 31) / 32)) - mg 128)) + retCost (128 + 32 * (((strN (storageAt state message.currentTarget 8)) + 31) / 32)) (strN (storageAt state message.currentTarget 8))) ≤ gas ∧
        s.gas = gas - (62 + 22 * 21 + 34 + (102 + slotCost (coldIn substate message.currentTarget 8)) + 281 + (50 * (((strN (storageAt state message.currentTarget 8)) + 31) / 32 - 1) + 96 + rdGas (accessSlot substate message.currentTarget 8) message.currentTarget (keccak (wordBytes 8)) (((strN (storageAt state message.currentTarget 8)) + 31) / 32) + (mg (128 + 32 * (((strN (storageAt state message.currentTarget 8)) + 31) / 32)) - mg 128)) + retCost (128 + 32 * (((strN (storageAt state message.currentTarget 8)) + 31) / 32)) (strN (storageAt state message.currentTarget 8)))) ∧
      s.state = StringsGen.rdSt (readSlot state message.currentTarget 8) message.currentTarget (keccak (wordBytes 8))
        (((strN (storageAt state message.currentTarget 8)) + 31) / 32) ∧
      s.substate = StringsGen.rdSs (accessSlot substate message.currentTarget 8) message.currentTarget
        (keccak (wordBytes 8)) (((strN (storageAt state message.currentTarget 8)) + 31) / 32)) := by
  obtain ⟨h4, hv, -⟩ := runFrame_ok_dispatch hfork hsize' start within hrun hok
  rcases hform with h0 | ⟨n, hn, h1, h31⟩ | ⟨hodd, h32, hN⟩
  · obtain ⟨hcg, -, ho, hg, hst, hss⟩ := ok_exact (Nat.le_refl _)
      (fun g hg => StringsGen.spec_symbolEmpty hfork h4 hsize' hsel hv h0 rfl hg) start within hrun hok
    exact .inl ⟨h0, ho, ⟨hcg, hg⟩, hst, hss⟩
  · obtain ⟨hcg, -, ho, hg, hst, hss⟩ := ok_exact (Nat.le_refl _)
      (fun g hg => Strings.spec_symbol hfork h4 hsize' hsel hv hn h1 h31 rfl hg) start within hrun hok
    exact .inr (.inl ⟨n, hn, h1, h31, ho, ⟨hcg, hg⟩, hst, hss⟩)
  · obtain ⟨hcg, -, ho, hg, hst, hss⟩ := ok_exact (Nat.le_refl _)
      (fun g hg => StringsGen.spec_symbolLong hfork h4 hsize' hsel hv hodd rfl h32 hN rfl hg) start within hrun hok
    exact .inr (.inr ⟨hodd, h32, ho, ⟨hcg, hg⟩, hst, hss⟩)

end UsdtVerify.Complete
