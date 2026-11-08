import UsdtVerify.Usdt.Exact.Getters
import UsdtVerify.Usdt.Complete.Owner

/-!
# Exact success conditions of the owner functions

From Berlin, a fresh frame of `CODE` at pc 0 with call data below `2^256` bytes and the
selector of the function, any gas bound and any message runner.

- `*_ok_iff`: with the gas of the success path (its cost, and the bound of more than 2300 gas
  left at each SSTORE that the specification takes), the run ends with no error if and only if
  the condition of `Usdt/Spec/Guards.lean` holds.
- `*_low`: with less gas than the cost of the success path, no run ends with no error.
  A gas between the cost and a stipend bound is not covered.

The functions: pause, unpause, addBlackList, removeBlackList, issue, redeem, setParams,
deprecate, transferOwnership, and destroyBlackFunds when not deprecated (`hdep`).
-/

namespace UsdtVerify.Exact

open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open UsdtVerify.Gas
open Complete Owner Pause BlackList Issue SetParams AddrWrite SafeMath
open PauseSpec BlackListSpec IssueSpec SetParamsSpec AddrWriteSpec DestroySpec

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate} {bound : Nat} {runChild : MessageRunner fork Nat bound}
  {evm : Evm fork Nat} {gas : Nat}

section

variable (hfork : .berlin ≤ fork) (hsize' : message.data.size < 2 ^ 256)
  (start : At CODE message 0 [] .empty gas state substate evm)
  (within : GasMeter.gasHeld evm.gas ≤ bound)
include hfork hsize' start

/-! ## pause, unpause -/

section
variable (hsel : selector message.data = 0x8456cb59) {c0 : Bool}
  (hc0 : coldIn substate message.currentTarget 0 = c0)
include hsel hc0

theorem pause_comp (s : Evm fork Nat)
    (hs : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) : PauseGuard state message :=
  let ⟨hst, hacc, hown, hp, _⟩ := ok_pause hfork hsize' hsel hc0 start within hs hok
  ⟨callOk_of_run hfork hsize' start within s hs hok, ⟨hst, hacc⟩, hown, hp⟩

/-- `pause()` succeeds exactly when `PauseGuard` holds, with the gas of its success path. -/
theorem pause_ok_iff (hstip : 3297 + slotCost c0 ≤ gas)
    (hg : PAUSE_COST + slotCost c0 + flagCost fork state message 1 ≤ gas) :
    RunsOk fork bound runChild evm within ↔ PauseGuard state message :=
  runsOk_iff (fun ⟨⟨h4, hv⟩, ⟨hst, hacc⟩, hown, hp⟩ =>
      spec_pause hfork hst hacc h4 hsize' hsel hv hown hp hc0 hstip hg)
    halted_false_ok start within (pause_comp hfork hsize' start within hsel hc0)

theorem pause_low (hg : gas < PAUSE_COST + slotCost c0 + flagCost fork state message 1) :
    ¬ RunsOk fork bound runChild evm within :=
  not_runsOk_low2 hg (fun ⟨⟨h4, hv⟩, ⟨hst, hacc⟩, hown, hp⟩ _ =>
      spec_pause hfork hst hacc h4 hsize' hsel hv hown hp hc0)
    start within (pause_comp hfork hsize' start within hsel hc0)

end

section
variable (hsel : selector message.data = 0x3f4ba83a) {c0 : Bool}
  (hc0 : coldIn substate message.currentTarget 0 = c0)
include hsel hc0

theorem unpause_comp (s : Evm fork Nat)
    (hs : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) : UnpauseGuard state message :=
  let ⟨hst, hacc, hown, hp, _⟩ := ok_unpause hfork hsize' hsel hc0 start within hs hok
  ⟨callOk_of_run hfork hsize' start within s hs hok, ⟨hst, hacc⟩, hown, hp⟩

/-- `unpause()` succeeds exactly when `UnpauseGuard` holds, with the gas of its success path. -/
theorem unpause_ok_iff (hstip : 3184 + slotCost c0 ≤ gas)
    (hg : UNPAUSE_COST + slotCost c0 + flagCost fork state message 0 ≤ gas) :
    RunsOk fork bound runChild evm within ↔ UnpauseGuard state message :=
  runsOk_iff (fun ⟨⟨h4, hv⟩, ⟨hst, hacc⟩, hown, hp⟩ =>
      spec_unpause hfork hst hacc h4 hsize' hsel hv hown hp hc0 hstip hg)
    halted_false_ok start within (unpause_comp hfork hsize' start within hsel hc0)

theorem unpause_low (hg : gas < UNPAUSE_COST + slotCost c0 + flagCost fork state message 0) :
    ¬ RunsOk fork bound runChild evm within :=
  not_runsOk_low2 hg (fun ⟨⟨h4, hv⟩, ⟨hst, hacc⟩, hown, hp⟩ _ =>
      spec_unpause hfork hst hacc h4 hsize' hsel hv hown hp hc0)
    start within (unpause_comp hfork hsize' start within hsel hc0)

end

/-! ## addBlackList, removeBlackList -/

section
variable {c0 cB : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
  (hcB : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget
    (listSlot (addrArg message.data 0)) = cB)
include hc0 hcB

theorem addBlackList_comp (hsel : selector message.data = 0x0ecb93c0) (s : Evm fork Nat)
    (hs : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) : OwnerWriteGuard state message :=
  let ⟨hst, hacc, hown, _⟩ := ok_addBlackList hfork hsize' hsel hc0 hcB start within hs hok
  ⟨callOk_of_run hfork hsize' start within s hs hok, ⟨hst, hacc⟩, hown⟩

/-- `addBlackList(a)` succeeds exactly when `OwnerWriteGuard` holds, with the gas of its success
path. -/
theorem addBlackList_ok_iff (hsel : selector message.data = 0x0ecb93c0)
    (hstip : 2779 + slotCost c0 + slotCost cB ≤ gas)
    (hg : 1567 + slotCost c0 + slotCost cB + listCost fork state message 1 ≤ gas) :
    RunsOk fork bound runChild evm within ↔ OwnerWriteGuard state message :=
  runsOk_iff (fun ⟨⟨h4, hv⟩, ⟨hst, hacc⟩, hown⟩ =>
      spec_add hfork hst hacc h4 hsize' hsel hv hown hc0 hcB hstip hg)
    halted_false_ok start within (addBlackList_comp hfork hsize' start within hc0 hcB hsel)

theorem addBlackList_low (hsel : selector message.data = 0x0ecb93c0)
    (hg : gas < 1567 + slotCost c0 + slotCost cB + listCost fork state message 1) :
    ¬ RunsOk fork bound runChild evm within :=
  not_runsOk_low2 hg (fun ⟨⟨h4, hv⟩, ⟨hst, hacc⟩, hown⟩ _ =>
      spec_add hfork hst hacc h4 hsize' hsel hv hown hc0 hcB)
    start within (addBlackList_comp hfork hsize' start within hc0 hcB hsel)

theorem removeBlackList_comp (hsel : selector message.data = 0xe4997dc5) (s : Evm fork Nat)
    (hs : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) : OwnerWriteGuard state message :=
  let ⟨hst, hacc, hown, _⟩ := ok_removeBlackList hfork hsize' hsel hc0 hcB start within hs hok
  ⟨callOk_of_run hfork hsize' start within s hs hok, ⟨hst, hacc⟩, hown⟩

/-- `removeBlackList(a)` succeeds exactly when `OwnerWriteGuard` holds, with the gas of its success
path. -/
theorem removeBlackList_ok_iff (hsel : selector message.data = 0xe4997dc5)
    (hstip : 3307 + slotCost c0 + slotCost cB ≤ gas)
    (hg : 2095 + slotCost c0 + slotCost cB + listCost fork state message 0 ≤ gas) :
    RunsOk fork bound runChild evm within ↔ OwnerWriteGuard state message :=
  runsOk_iff (fun ⟨⟨h4, hv⟩, ⟨hst, hacc⟩, hown⟩ =>
      spec_remove hfork hst hacc h4 hsize' hsel hv hown hc0 hcB hstip hg)
    halted_false_ok start within (removeBlackList_comp hfork hsize' start within hc0 hcB hsel)

theorem removeBlackList_low (hsel : selector message.data = 0xe4997dc5)
    (hg : gas < 2095 + slotCost c0 + slotCost cB + listCost fork state message 0) :
    ¬ RunsOk fork bound runChild evm within :=
  not_runsOk_low2 hg (fun ⟨⟨h4, hv⟩, ⟨hst, hacc⟩, hown⟩ _ =>
      spec_remove hfork hst hacc h4 hsize' hsel hv hown hc0 hcB)
    start within (removeBlackList_comp hfork hsize' start within hc0 hcB hsel)

end

/-! ## issue, redeem -/

section
variable {c0 c1 cO : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
  (hc1 : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget 1 = c1)
  (hcO : coldIn (accessSlot (accessSlot substate message.currentTarget 0) message.currentTarget 1)
    message.currentTarget (ownerBal state message.currentTarget) = cO)
include hc0 hc1 hcO

theorem issue_comp (hsel : selector message.data = 0xcc872b66) (s : Evm fork Nat)
    (hs : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) : IssueGuard state message :=
  let ⟨hst, hacc, hown, h0, hT, hB, _⟩ :=
    ok_issue hfork hsize' hsel hc0 hc1 hcO start within hs hok
  ⟨callOk_of_run hfork hsize' start within s hs hok, ⟨hst, hacc⟩, hown, h0, hT, hB⟩

/-- `issue(a)` succeeds exactly when `IssueGuard` holds, with the gas of its success path. -/
theorem issue_ok_iff (hsel : selector message.data = 0xcc872b66)
    (hstip : 4248 + slotCost c0 + slotCost c1 + slotCost cO + issueCostO fork state message ≤ gas)
    (hg : 3024 + slotCost c0 + slotCost c1 + slotCost cO + issueCostO fork state message +
      issueCostT fork state message ≤ gas) :
    RunsOk fork bound runChild evm within ↔ IssueGuard state message :=
  runsOk_iff (fun ⟨⟨h4, hv⟩, ⟨hst, hacc⟩, hown, h0, hT, hB⟩ =>
      spec_issue hfork hst hacc h4 hsize' hsel hv hown ⟨h0, hT⟩ hB hc0 hc1 hcO hstip hg)
    halted_false_ok start within (issue_comp hfork hsize' start within hc0 hc1 hcO hsel)

theorem issue_low (hsel : selector message.data = 0xcc872b66)
    (hg : gas < 3024 + slotCost c0 + slotCost c1 + slotCost cO + issueCostO fork state message +
      issueCostT fork state message) :
    ¬ RunsOk fork bound runChild evm within :=
  not_runsOk_low2 hg (fun ⟨⟨h4, hv⟩, ⟨hst, hacc⟩, hown, h0, hT, hB⟩ _ =>
      spec_issue hfork hst hacc h4 hsize' hsel hv hown ⟨h0, hT⟩ hB hc0 hc1 hcO)
    start within (issue_comp hfork hsize' start within hc0 hc1 hcO hsel)

theorem redeem_comp (hsel : selector message.data = 0xdb006a75) (s : Evm fork Nat)
    (hs : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) : RedeemGuard state message :=
  let ⟨hst, hacc, hown, hT, hB, _⟩ :=
    ok_redeem hfork hsize' hsel hc0 hc1 hcO start within hs hok
  ⟨callOk_of_run hfork hsize' start within s hs hok, ⟨hst, hacc⟩, hown, hT, hB⟩

/-- `redeem(a)` succeeds exactly when `RedeemGuard` holds, with the gas of its success path. -/
theorem redeem_ok_iff (hsel : selector message.data = 0xdb006a75)
    (hstip : 3838 + slotCost c0 + slotCost c1 + slotCost cO + redeemCostT fork state message ≤
      gas)
    (hg : 2614 + slotCost c0 + slotCost c1 + slotCost cO + redeemCostT fork state message +
      redeemCostO fork state message ≤ gas) :
    RunsOk fork bound runChild evm within ↔ RedeemGuard state message :=
  runsOk_iff (fun ⟨⟨h4, hv⟩, ⟨hst, hacc⟩, hown, hT, hB⟩ =>
      spec_redeem hfork hst hacc h4 hsize' hsel hv hown hT hB hc0 hc1 hcO hstip hg)
    halted_false_ok start within (redeem_comp hfork hsize' start within hc0 hc1 hcO hsel)

theorem redeem_low (hsel : selector message.data = 0xdb006a75)
    (hg : gas < 2614 + slotCost c0 + slotCost c1 + slotCost cO + redeemCostT fork state message +
      redeemCostO fork state message) :
    ¬ RunsOk fork bound runChild evm within :=
  not_runsOk_low2 hg (fun ⟨⟨h4, hv⟩, ⟨hst, hacc⟩, hown, hT, hB⟩ _ =>
      spec_redeem hfork hst hacc h4 hsize' hsel hv hown hT hB hc0 hc1 hcO)
    start within (redeem_comp hfork hsize' start within hc0 hc1 hcO hsel)

end

/-! ## setParams -/

section
variable (hsel : selector message.data = 0xc0324c77) {c0 c3 c9 c4 : Bool}
  (hc0 : coldIn substate message.currentTarget 0 = c0)
  (hc3 : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget 3 = c3)
  (hc9 : coldIn (accessSlot (accessSlot substate message.currentTarget 0) message.currentTarget 3)
    message.currentTarget 9 = c9)
  (hc4 : coldIn (accessSlot (accessSlot (accessSlot substate message.currentTarget 0)
    message.currentTarget 3) message.currentTarget 9) message.currentTarget 4 = c4)
include hsel hc0 hc3 hc9 hc4

theorem setParams_comp (s : Evm fork Nat)
    (hs : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) : SetParamsGuard state message :=
  let ⟨hst, hacc, hown, hb, hm, hov, _⟩ :=
    ok_setParams hfork hsize' hsel hc0 hc3 hc9 hc4 start within hs hok
  ⟨callOk_of_run hfork hsize' start within s hs hok, ⟨hst, hacc⟩, hown, hb, hm, hov⟩

/-- `setParams(b, m)` succeeds exactly when `SetParamsGuard` holds, with the gas of its success
path. -/
theorem setParams_ok_iff
    (hstip : 3168 + slotCost c0 + Gas.writeCost fork (originalAt state message.currentTarget 3)
      (storageAt state message.currentTarget 3) (wordArg message.data 0) c3 + slotCost c9 +
      50 * exponentBytes (storageAt state message.currentTarget 9) +
      mulCost (wordArg message.data 1) ≤ gas)
    (hg : 2425 + paramsCost fork state message c0 c3 c9 c4 ≤ gas) :
    RunsOk fork bound runChild evm within ↔ SetParamsGuard state message :=
  runsOk_iff (fun ⟨⟨h4, hv⟩, ⟨hst, hacc⟩, hown, hb, hm, hov⟩ =>
      spec_setParams hfork hst hacc h4 hsize' hsel hv hown hb hm hov hc0 hc3 hc9 hc4 hstip hg)
    halted_false_ok start within
    (setParams_comp hfork hsize' start within hsel hc0 hc3 hc9 hc4)

theorem setParams_low (hg : gas < 2425 + paramsCost fork state message c0 c3 c9 c4) :
    ¬ RunsOk fork bound runChild evm within :=
  not_runsOk_low2 hg (fun ⟨⟨h4, hv⟩, ⟨hst, hacc⟩, hown, hb, hm, hov⟩ _ =>
      spec_setParams hfork hst hacc h4 hsize' hsel hv hown hb hm hov hc0 hc3 hc9 hc4)
    start within (setParams_comp hfork hsize' start within hsel hc0 hc3 hc9 hc4)

end

/-! ## deprecate, transferOwnership -/

section
variable (hsel : selector message.data = 0x0753c30c) {c0 c10 : Bool}
  (hc0 : coldIn substate message.currentTarget 0 = c0)
  (hc10 : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget 10 = c10)
include hsel hc0 hc10

theorem deprecate_comp (s : Evm fork Nat)
    (hs : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) : OwnerWriteGuard state message :=
  let ⟨hst, hacc, hown, _⟩ := ok_deprecate hfork hsize' hsel hc0 hc10 start within hs hok
  ⟨callOk_of_run hfork hsize' start within s hs hok, ⟨hst, hacc⟩, hown⟩

/-- `deprecate(a)` succeeds exactly when `OwnerWriteGuard` holds, with the gas of its success
path. -/
theorem deprecate_ok_iff
    (hstip : 2840 + slotCost c0 + slotCost c10 + Gas.writeCost fork
      (originalAt state message.currentTarget 10) (storageAt state message.currentTarget 10)
      (withPaused (storageAt state message.currentTarget 10) 1) false ≤ gas)
    (hg : 1628 + slotCost c0 + slotCost c10 + depCost fork state message ≤ gas) :
    RunsOk fork bound runChild evm within ↔ OwnerWriteGuard state message :=
  runsOk_iff (fun ⟨⟨h4, hv⟩, ⟨hst, hacc⟩, hown⟩ =>
      spec_deprecate hfork hst hacc h4 hsize' hsel hv hown hc0 hc10 hstip hg)
    halted_false_ok start within (deprecate_comp hfork hsize' start within hsel hc0 hc10)

theorem deprecate_low (hg : gas < 1628 + slotCost c0 + slotCost c10 + depCost fork state message) :
    ¬ RunsOk fork bound runChild evm within :=
  not_runsOk_low2 hg (fun ⟨⟨h4, hv⟩, ⟨hst, hacc⟩, hown⟩ _ =>
      spec_deprecate hfork hst hacc h4 hsize' hsel hv hown hc0 hc10)
    start within (deprecate_comp hfork hsize' start within hsel hc0 hc10)

end

section
variable (hsel : selector message.data = 0xf2fde38b) {c0 : Bool}
  (hc0 : coldIn substate message.currentTarget 0 = c0)
include hsel hc0

theorem transferOwnership_comp (s : Evm fork Nat)
    (hs : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) : TransferOwnershipGuard state message := by
  obtain ⟨hown, -, h⟩ := ok_transferOwnership hfork hsize' hsel hc0 start within hs hok
  refine ⟨callOk_of_run hfork hsize' start within s hs hok, hown, fun hz => ?_⟩
  rcases h with ⟨h0, -⟩ | ⟨-, hst, hacc, -⟩
  · exact absurd h0 hz
  · exact ⟨hst, hacc⟩

/-- The cost of the success path of `transferOwnership(a)`: `947 + price(slot 0)` for `a = 0`,
`1114 + price(slot 0) + price(write of slot 0)` otherwise. -/
abbrev ownershipCost (fork : Fork) (state : State.TransactionState) (message : Message fork)
    (c0 : Bool) : Nat :=
  if addrArg message.data 0 = 0 then 947 + slotCost c0
  else 1114 + slotCost c0 + ownCost fork state message

/-- `transferOwnership(a)` succeeds exactly when `TransferOwnershipGuard` holds, with the gas of its
success path (`ownershipCost`, and for `a ≠ 0` more than 2300 gas left at the SSTORE). -/
theorem transferOwnership_ok_iff (hstip : addrArg message.data 0 ≠ 0 → 3401 + slotCost c0 ≤ gas)
    (hg : ownershipCost fork state message c0 ≤ gas) :
    RunsOk fork bound runChild evm within ↔ TransferOwnershipGuard state message := by
  refine runsOk_iff (Q := fun e => e.error = none) (fun ⟨⟨h4, hv⟩, hown, hw⟩ => ?_)
    (fun _ h => h) start within (transferOwnership_comp hfork hsize' start within hsel hc0)
  by_cases hz : addrArg message.data 0 = 0
  · simp only [ownershipCost, hz, ↓reduceIte] at hg
    exact (spec_transferOwnership_zero hfork h4 hsize' hsel hv hown hz hc0 hg).consequence
      (fun _ h => h) halted_false_ok
  · simp only [ownershipCost, hz, ↓reduceIte] at hg
    obtain ⟨hst, hacc⟩ := hw hz
    exact (spec_transferOwnership hfork hst hacc h4 hsize' hsel hv hown hz hc0 (hstip hz)
      hg).consequence (fun _ h => h) halted_false_ok

theorem transferOwnership_low (hg : gas < ownershipCost fork state message c0) :
    ¬ RunsOk fork bound runChild evm within := by
  by_cases hz : addrArg message.data 0 = 0
  · simp only [ownershipCost, hz, ↓reduceIte] at hg
    exact not_runsOk_low (Nat.le_refl _) hg (fun ⟨⟨h4, hv⟩, hown, _⟩ _ =>
        spec_transferOwnership_zero hfork h4 hsize' hsel hv hown hz hc0)
      start within (transferOwnership_comp hfork hsize' start within hsel hc0)
  · simp only [ownershipCost, hz, ↓reduceIte] at hg
    exact not_runsOk_low2 hg (fun ⟨⟨h4, hv⟩, hown, hw⟩ _ =>
        spec_transferOwnership hfork (hw hz).1 (hw hz).2 h4 hsize' hsel hv hown hz hc0)
      start within (transferOwnership_comp hfork hsize' start within hsel hc0)

end

/-! ## destroyBlackFunds, not deprecated -/

section
variable (hsel : selector message.data = 0xf3bdc228)
  (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
  {c0 cL c10 cB c1 : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
  (hcL : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget
    (listSlot (addrArg message.data 0)) = cL)
  (hc10 : coldIn (preSub substate message) message.currentTarget 10 = c10)
  (hcB : coldIn (accessSlot (preSub substate message) message.currentTarget 10)
    message.currentTarget (balSlot message) = cB)
  (hc1 : coldIn (readSub substate message) message.currentTarget 1 = c1)
include hsel hdep hc0 hcL hc10 hcB hc1

theorem destroyBlackFunds_comp (s : Evm fork Nat)
    (hs : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) : DestroyBlackFundsGuard state message :=
  let ⟨hst, hacc, hown, hl, _⟩ :=
    ok_destroyBlackFunds hfork hsize' hsel hdep hc0 hcL hc10 hcB hc1 start within hs hok
  ⟨callOk_of_run hfork hsize' start within s hs hok, ⟨hst, hacc⟩, hown, hl⟩

/-- `destroyBlackFunds(a)`, not deprecated, succeeds exactly when `DestroyBlackFundsGuard` holds,
with the gas of its success path. -/
theorem destroyBlackFunds_ok_iff
    (hstip1 : 3763 + slotCost c0 + slotCost cL + slotCost c10 + slotCost cB ≤ gas)
    (hstip2 : 3796 + slotCost c0 + slotCost cL + slotCost c10 + slotCost cB +
      costB fork state message + slotCost c1 ≤ gas)
    (hg : 2865 + slotCost c0 + slotCost cL + slotCost c10 + slotCost cB + slotCost c1 +
      costB fork state message + costT fork state message ≤ gas) :
    RunsOk fork bound runChild evm within ↔ DestroyBlackFundsGuard state message :=
  runsOk_iff (fun ⟨⟨h4, hv⟩, ⟨hst, hacc⟩, hown, hl⟩ =>
      DestroySpec.spec hfork hst hacc h4 hsize' hsel hv hown hl hdep hc0 hcL hc10 hcB hc1
        hstip1 hstip2 hg)
    halted_false_ok start within
    (destroyBlackFunds_comp hfork hsize' start within hsel hdep hc0 hcL hc10 hcB hc1)

theorem destroyBlackFunds_low
    (hg : gas < 2865 + slotCost c0 + slotCost cL + slotCost c10 + slotCost cB + slotCost c1 +
      costB fork state message + costT fork state message) :
    ¬ RunsOk fork bound runChild evm within :=
  not_runsOk_low3 hg (fun ⟨⟨h4, hv⟩, ⟨hst, hacc⟩, hown, hl⟩ _ =>
      DestroySpec.spec hfork hst hacc h4 hsize' hsel hv hown hl hdep hc0 hcL hc10 hcB hc1)
    start within (destroyBlackFunds_comp hfork hsize' start within hsel hdep hc0 hcL hc10 hcB hc1)

end

end

end UsdtVerify.Exact
