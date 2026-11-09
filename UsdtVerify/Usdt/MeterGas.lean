import UsdtVerify.Usdt.MeterOwner

/-!
# The gas of the writing functions at any reservoir, over EthLib's EIP-8037 meter

From a frame `m` whose `toNat` is the fresh frame of `CODE` with `gas` execution gas, at any
reservoir, for any gas bound and message runner: a run of the loop over `StateGasMeter` that ends
with no error, when the writes of the path that can refill do not (the hypotheses of
`X_iff_gas_sgm`), ends with its execution gas left and its reservoir adding up to
`gas + m.gas.reservoir - cost`, where `cost` is the cost of the success path (`X_gas_any`).

The state gas of the path is taken from the reservoir first, so the execution gas left alone is
not fixed by this: it is `gas - cost` when the reservoir is 0 (`X_ok_sgm`).

Through `gas_eq_any` (Evm/Shadow.lean): the run of the meter `Nat` with more gas that
`shadow_runQ` gives keeps the difference between its gas and the sum of the two parts of the
meter, as long as no SSTORE refills.
-/

namespace UsdtVerify.Exact

open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open UsdtVerify.Gas
open UsdtVerify.Meter
open UsdtVerify.Refill
open UsdtVerify.Shadow
open Complete Approve Transfer TransferOk TransferFee SafeMath TransferFrom

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate} {bound : Nat} {runChild : MessageRunner fork StateGasMeter bound}
  {m s : Evm fork StateGasMeter} {gas : Nat}

/-- A triple to a normal halt with `g - cost` gas, as a triple to stopped frames with that gas. -/
theorem halted_gas {P : Evm fork Nat → Prop} {g cost : Nat}
    (h : HoareI fork P (fun e => e.running = false ∧
      Halted false .empty (g - cost) e.state e.substate e)) :
    HoareI fork P (fun e => e.running = false ∧ e.gas = g - cost) :=
  h.consequence (fun _ h => h) fun _ ⟨hr, h⟩ => ⟨hr, h.2.2.2.1⟩

/-- **approve over the EIP-8037 meter, any reservoir: the gas.** -/
theorem approve_gas_any (hfork : .berlin ≤ fork) (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x095ea7b3)
    (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    {c10 cA : Bool} (hc10 : coldIn substate message.currentTarget 10 = c10)
    (hcA : coldIn (accessSlot substate message.currentTarget 10) message.currentTarget
      (allowArg message) = cA)
    (start : At CODE message 0 [] .empty gas state substate (toNat m))
    (hnr : sstoreStateRefill fork (originalAt state message.currentTarget (allowArg message))
      (storageAt state message.currentTarget (allowArg message)) (wordArg message.data 1) = 0)
    {within : GasMeter.gasHeld m.gas ≤ bound}
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild m within = .ok s)
    (hok : s.error = none) :
    s.gas.gasLeft + s.gas.reservoir + approveCost fork state message c10 cA =
      gas + m.gas.reservoir := by
  have hG := (ok_approve_any hfork hsize' hsel hdep start hrun hok).1
  exact gas_eq_any hfork (Nat.le_max_left _ _) (fun g hg => halted_gas
    (approve_specI hfork hsize' hsel hdep hc10 hcA hnr hG hg)) start hrun hok

/-- **transfer over the EIP-8037 meter, any reservoir: the gas.** -/
theorem transfer_gas_any (hfork : .berlin ≤ fork) (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0xa9059cbb)
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
    (hnrD : sstoreStateRefill fork (originalAt state message.currentTarget (senderSlot message))
      (balS (shortState state message) message)
      (sub (balS (shortState state message) message) (wordArg message.data 1)) = 0)
    {within : GasMeter.gasHeld m.gas ≤ bound}
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild m within = .ok s)
    (hok : s.error = none) :
    s.gas.gasLeft + s.gas.reservoir + transferCost fork state message c0 cB c10 c3 c4 cS cT cO =
      gas + m.gas.reservoir := by
  have hG := (ok_transfer_any hfork hsize' hsel hdep start hrun hok).1
  exact gas_eq_any hfork (Nat.le_max_left _ _) (fun g hg => halted_gas
    (transfer_specI hfork hsize' hsel hdep hc0 hcB hc10 hc3 hc4 hcS hcT hcO hnrD hG hg)) start
    hrun hok

/-- **transferFrom over the EIP-8037 meter, any reservoir: the gas.** -/
theorem transferFrom_gas_any (hfork : .berlin ≤ fork) (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x23b872dd)
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
    (hnrA : allowOf (checkState state message) message (fromArg message) ≠ MAX_UINT →
      sstoreStateRefill fork
        (originalAt state message.currentTarget (allowFrom message (fromArg message)))
        (allowOf (checkState state message) message (fromArg message))
        (sub (allowOf (checkState state message) message (fromArg message)) (valArg message)) = 0)
    (hnrD : sstoreStateRefill fork
      (originalAt state message.currentTarget (recipientSlot (fromArg message)))
      (balFrom (checkState state message) message (valArg message) (fromArg message))
      (sub (balFrom (checkState state message) message (valArg message) (fromArg message))
        (valArg message)) = 0)
    {within : GasMeter.gasHeld m.gas ≤ bound}
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild m within = .ok s)
    (hok : s.error = none) :
    s.gas.gasLeft + s.gas.reservoir +
      transferFromCost fork state message c0 cB c10 cA c3 c4 cF cT cO = gas + m.gas.reservoir := by
  have hG := (ok_transferFrom_any hfork hsize' hsel hdep start hrun hok).1
  exact gas_eq_any hfork (Nat.le_max_left _ _) (fun g hg => halted_gas
    (transferFrom_specI hfork hsize' hsel hdep hc0 hcB hc10 hcA hc3 hc4 hcF hcT hcO hnrA hnrD hG
      hg)) start hrun hok

section Owner

open Owner Admin Pause BlackList Issue SetParams AddrWrite
open PauseSpec BlackListSpec IssueSpec SetParamsSpec AddrWriteSpec DestroySpec

variable (hfork : .berlin ≤ fork) (hsize' : message.data.size < 2 ^ 256)
  (start : At CODE message 0 [] .empty gas state substate (toNat m))
  {within : GasMeter.gasHeld m.gas ≤ bound}
  (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild m within = .ok s)
  (hok : s.error = none)
include hfork hsize' start hrun hok

/-- **pause over the EIP-8037 meter, any reservoir: the gas.** -/
theorem pause_gas_any (hsel : selector message.data = 0x8456cb59) {c0 : Bool}
    (hc0 : coldIn substate message.currentTarget 0 = c0) :
    s.gas.gasLeft + s.gas.reservoir + (PAUSE_COST + slotCost c0 + flagCost fork state message 1) =
      gas + m.gas.reservoir := by
  obtain ⟨G, hE⟩ := shadow_ends hfork hrun hok
  have st' := at_addGas start (budget m)
  obtain ⟨h4, hv, -⟩ := ends_ok_dispatch hfork hsize' st' hE hok
  obtain ⟨hst, hacc, hown, hp, -⟩ := ok_pause hfork hsize' hsel rfl st' hE hok
  exact gas_eq_any hfork (Nat.le_max_left _ _) (fun g hg => halted_gas
    (pause_specI hfork hsize' hsel hc0 ⟨⟨h4, hv⟩, ⟨hst, hacc⟩, hown, hp⟩ hg)) start hrun hok

/-- **unpause over the EIP-8037 meter, any reservoir: the gas.** -/
theorem unpause_gas_any (hsel : selector message.data = 0x3f4ba83a) {c0 : Bool}
    (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hnr : sstoreStateRefill fork (originalAt state message.currentTarget 0)
      (storageAt state message.currentTarget 0)
      (withPaused (storageAt state message.currentTarget 0) 0) = 0) :
    s.gas.gasLeft + s.gas.reservoir +
      (UNPAUSE_COST + slotCost c0 + flagCost fork state message 0) = gas + m.gas.reservoir := by
  obtain ⟨G, hE⟩ := shadow_ends hfork hrun hok
  have st' := at_addGas start (budget m)
  obtain ⟨h4, hv, -⟩ := ends_ok_dispatch hfork hsize' st' hE hok
  obtain ⟨hst, hacc, hown, hp, -⟩ := ok_unpause hfork hsize' hsel rfl st' hE hok
  exact gas_eq_any hfork (Nat.le_max_left _ _) (fun g hg => halted_gas
    (unpause_specI hfork hsize' hsel hc0 hnr ⟨⟨h4, hv⟩, ⟨hst, hacc⟩, hown, hp⟩ hg)) start hrun hok

/-- **addBlackList over the EIP-8037 meter, any reservoir: the gas.** -/
theorem addBlackList_gas_any (hsel : selector message.data = 0x0ecb93c0) {c0 cB : Bool}
    (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hcB : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget
      (listSlot (addrArg message.data 0)) = cB) :
    s.gas.gasLeft + s.gas.reservoir +
      (1567 + slotCost c0 + slotCost cB + listCost fork state message 1) =
        gas + m.gas.reservoir := by
  obtain ⟨G, hE⟩ := shadow_ends hfork hrun hok
  have st' := at_addGas start (budget m)
  obtain ⟨h4, hv, -⟩ := ends_ok_dispatch hfork hsize' st' hE hok
  obtain ⟨hst, hacc, hown, -⟩ := ok_addBlackList hfork hsize' hsel rfl rfl st' hE hok
  exact gas_eq_any hfork (Nat.le_max_left _ _) (fun g hg => halted_gas
    (addBlackList_specI hfork hsize' hc0 hcB hsel ⟨⟨h4, hv⟩, ⟨hst, hacc⟩, hown⟩ hg)) start hrun hok

/-- **removeBlackList over the EIP-8037 meter, any reservoir: the gas.** -/
theorem removeBlackList_gas_any (hsel : selector message.data = 0xe4997dc5) {c0 cB : Bool}
    (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hcB : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget
      (listSlot (addrArg message.data 0)) = cB)
    (hnr : sstoreStateRefill fork
      (originalAt state message.currentTarget (listSlot (addrArg message.data 0)))
      (storageAt state message.currentTarget (listSlot (addrArg message.data 0)))
      (setLow (storageAt state message.currentTarget (listSlot (addrArg message.data 0))) 0) = 0) :
    s.gas.gasLeft + s.gas.reservoir +
      (2095 + slotCost c0 + slotCost cB + listCost fork state message 0) =
        gas + m.gas.reservoir := by
  obtain ⟨G, hE⟩ := shadow_ends hfork hrun hok
  have st' := at_addGas start (budget m)
  obtain ⟨h4, hv, -⟩ := ends_ok_dispatch hfork hsize' st' hE hok
  obtain ⟨hst, hacc, hown, -⟩ := ok_removeBlackList hfork hsize' hsel rfl rfl st' hE hok
  exact gas_eq_any hfork (Nat.le_max_left _ _) (fun g hg => halted_gas
    (removeBlackList_specI hfork hsize' hc0 hcB hnr hsel ⟨⟨h4, hv⟩, ⟨hst, hacc⟩, hown⟩ hg)) start
    hrun hok

/-- **deprecate over the EIP-8037 meter, any reservoir: the gas.** -/
theorem deprecate_gas_any (hsel : selector message.data = 0x0753c30c) {c0 c10 : Bool}
    (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hc10 : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget 10 = c10) :
    s.gas.gasLeft + s.gas.reservoir +
      (1628 + slotCost c0 + slotCost c10 + depCost fork state message) =
        gas + m.gas.reservoir := by
  obtain ⟨G, hE⟩ := shadow_ends hfork hrun hok
  have st' := at_addGas start (budget m)
  obtain ⟨h4, hv, -⟩ := ends_ok_dispatch hfork hsize' st' hE hok
  obtain ⟨hst, hacc, hown, -⟩ := ok_deprecate hfork hsize' hsel rfl rfl st' hE hok
  exact gas_eq_any hfork (Nat.le_max_left _ _) (fun g hg => halted_gas
    (deprecate_specI hfork hsize' hsel hc0 hc10 ⟨⟨h4, hv⟩, ⟨hst, hacc⟩, hown⟩ hg)) start hrun hok

/-- **transferOwnership over the EIP-8037 meter, any reservoir: the gas.** -/
theorem transferOwnership_gas_any (hsel : selector message.data = 0xf2fde38b) {c0 : Bool}
    (hc0 : coldIn substate message.currentTarget 0 = c0) :
    s.gas.gasLeft + s.gas.reservoir + ownershipCost fork state message c0 =
      gas + m.gas.reservoir := by
  obtain ⟨G, hE⟩ := shadow_ends hfork hrun hok
  have st' := at_addGas start (budget m)
  obtain ⟨h4, hv, -⟩ := ends_ok_dispatch hfork hsize' st' hE hok
  obtain ⟨hown, -, h⟩ := ok_transferOwnership hfork hsize' hsel rfl st' hE hok
  have hG : TransferOwnershipGuard state message := by
    refine ⟨⟨h4, hv⟩, hown, fun hz => ?_⟩
    rcases h with ⟨h0, -⟩ | ⟨-, hst, hacc, -⟩
    · exact absurd h0 hz
    · exact ⟨hst, hacc⟩
  exact gas_eq_any hfork (Nat.le_max_left _ _) (fun g hg => halted_gas
    (transferOwnership_specI hfork hsize' hsel hc0 hG hg)) start hrun hok

/-- **issue over the EIP-8037 meter, any reservoir: the gas.** -/
theorem issue_gas_any (hsel : selector message.data = 0xcc872b66) {c0 c1 cO : Bool}
    (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hc1 : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget 1 = c1)
    (hcO : coldIn (accessSlot (accessSlot substate message.currentTarget 0) message.currentTarget 1)
      message.currentTarget (ownerBal state message.currentTarget) = cO)
    (hnrT : sstoreStateRefill fork (originalAt state message.currentTarget 1)
      (storageAt (issueState1 state message) message.currentTarget 1)
      (add (storageAt (issueState1 state message) message.currentTarget 1)
        (wordArg message.data 0)) = 0) :
    s.gas.gasLeft + s.gas.reservoir + (3024 + slotCost c0 + slotCost c1 + slotCost cO +
      issueCostO fork state message + issueCostT fork state message) = gas + m.gas.reservoir := by
  obtain ⟨G, hE⟩ := shadow_ends hfork hrun hok
  have st' := at_addGas start (budget m)
  obtain ⟨h4, hv, -⟩ := ends_ok_dispatch hfork hsize' st' hE hok
  obtain ⟨hst, hacc, hown, h0, hT, hB, -⟩ := ok_issue hfork hsize' hsel rfl rfl rfl st' hE hok
  exact gas_eq_any hfork (Nat.le_max_left _ _) (fun g hg => halted_gas
    (issue_specI hfork hsize' hc0 hc1 hcO hsel hnrT ⟨⟨h4, hv⟩, ⟨hst, hacc⟩, hown, h0, hT, hB⟩
      hg)) start hrun hok

/-- **redeem over the EIP-8037 meter, any reservoir: the gas.** -/
theorem redeem_gas_any (hsel : selector message.data = 0xdb006a75) {c0 c1 cO : Bool}
    (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hc1 : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget 1 = c1)
    (hcO : coldIn (accessSlot (accessSlot substate message.currentTarget 0) message.currentTarget 1)
      message.currentTarget (ownerBal state message.currentTarget) = cO)
    (hnrT : sstoreStateRefill fork (originalAt state message.currentTarget 1)
      (storageAt state message.currentTarget 1)
      (sub (storageAt state message.currentTarget 1) (wordArg message.data 0)) = 0)
    (hnrO : sstoreStateRefill fork
      (originalAt state message.currentTarget (ownerBal state message.currentTarget))
      (storageAt (redeemState1 state message) message.currentTarget
        (ownerBal state message.currentTarget))
      (sub (storageAt (redeemState1 state message) message.currentTarget
        (ownerBal state message.currentTarget)) (wordArg message.data 0)) = 0) :
    s.gas.gasLeft + s.gas.reservoir + (2614 + slotCost c0 + slotCost c1 + slotCost cO +
      redeemCostT fork state message + redeemCostO fork state message) =
        gas + m.gas.reservoir := by
  obtain ⟨G, hE⟩ := shadow_ends hfork hrun hok
  have st' := at_addGas start (budget m)
  obtain ⟨h4, hv, -⟩ := ends_ok_dispatch hfork hsize' st' hE hok
  obtain ⟨hst, hacc, hown, hT, hB, -⟩ := ok_redeem hfork hsize' hsel rfl rfl rfl st' hE hok
  exact gas_eq_any hfork (Nat.le_max_left _ _) (fun g hg => halted_gas
    (redeem_specI hfork hsize' hc0 hc1 hcO hsel hnrT hnrO ⟨⟨h4, hv⟩, ⟨hst, hacc⟩, hown, hT, hB⟩
      hg)) start hrun hok

/-- **setParams over the EIP-8037 meter, any reservoir: the gas.** -/
theorem setParams_gas_any (hsel : selector message.data = 0xc0324c77) {c0 c3 c9 c4 : Bool}
    (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hc3 : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget 3 = c3)
    (hc9 : coldIn (accessSlot (accessSlot substate message.currentTarget 0) message.currentTarget 3)
      message.currentTarget 9 = c9)
    (hc4 : coldIn (accessSlot (accessSlot (accessSlot substate message.currentTarget 0)
      message.currentTarget 3) message.currentTarget 9) message.currentTarget 4 = c4)
    (hnr3 : sstoreStateRefill fork (originalAt state message.currentTarget 3)
      (storageAt state message.currentTarget 3) (wordArg message.data 0) = 0)
    (hnr4 : sstoreStateRefill fork (originalAt state message.currentTarget 4)
      (storageAt state message.currentTarget 4) (feeWord state message) = 0) :
    s.gas.gasLeft + s.gas.reservoir + (2425 + paramsCost fork state message c0 c3 c9 c4) =
      gas + m.gas.reservoir := by
  obtain ⟨G, hE⟩ := shadow_ends hfork hrun hok
  have st' := at_addGas start (budget m)
  obtain ⟨h4, hv, -⟩ := ends_ok_dispatch hfork hsize' st' hE hok
  obtain ⟨hst, hacc, hown, hb, hmm, hov, -⟩ :=
    ok_setParams hfork hsize' hsel rfl rfl rfl rfl st' hE hok
  exact gas_eq_any hfork (Nat.le_max_left _ _) (fun g hg => halted_gas
    (setParams_specI hfork hsize' hsel hc0 hc3 hc9 hc4 hnr3 hnr4
      ⟨⟨h4, hv⟩, ⟨hst, hacc⟩, hown, hb, hmm, hov⟩ hg)) start hrun hok

/-- **destroyBlackFunds over the EIP-8037 meter, any reservoir: the gas.** Not deprecated. -/
theorem destroyBlackFunds_gas_any (hsel : selector message.data = 0xf3bdc228)
    (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    {c0 cL c10 cB c1 : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hcL : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget
      (listSlot (addrArg message.data 0)) = cL)
    (hc10 : coldIn (preSub substate message) message.currentTarget 10 = c10)
    (hcB : coldIn (accessSlot (preSub substate message) message.currentTarget 10)
      message.currentTarget (balSlot message) = cB)
    (hc1 : coldIn (readSub substate message) message.currentTarget 1 = c1)
    (hnrB : sstoreStateRefill fork (originalAt state message.currentTarget (balSlot message))
      (dirty state message) 0 = 0)
    (hnrT : sstoreStateRefill fork (originalAt state message.currentTarget 1)
      (storageAt (state1 state message) message.currentTarget 1)
      (sub (storageAt (state1 state message) message.currentTarget 1) (dirty state message)) = 0) :
    s.gas.gasLeft + s.gas.reservoir + (2865 + slotCost c0 + slotCost cL + slotCost c10 +
      slotCost cB + slotCost c1 + costB fork state message + costT fork state message) =
        gas + m.gas.reservoir := by
  obtain ⟨G, hE⟩ := shadow_ends hfork hrun hok
  have st' := at_addGas start (budget m)
  obtain ⟨h4, hv, -⟩ := ends_ok_dispatch hfork hsize' st' hE hok
  obtain ⟨hst, hacc, hown, hl, -⟩ :=
    ok_destroyBlackFunds hfork hsize' hsel hdep rfl rfl rfl rfl rfl st' hE hok
  exact gas_eq_any hfork (Nat.le_max_left _ _) (fun g hg => halted_gas
    (destroyBlackFunds_specI hfork hsize' hsel hdep hc0 hcL hc10 hcB hc1 hnrB hnrT
      ⟨⟨h4, hv⟩, ⟨hst, hacc⟩, hown, hl⟩ hg)) start hrun hok

end Owner

end UsdtVerify.Exact
