import UsdtVerify.Usdt.Exact.Getters
import UsdtVerify.Evm.Dom
import UsdtVerify.Usdt.Complete.Owner

/-!
# Exact success conditions of the owner functions

From Berlin, a fresh frame of `CODE` at pc 0 with call data below `2^256` bytes and the
selector of the function, any gas bound and any message runner.

- `*_ok_iff`: with the gas of the success path (its cost, and the bound of more than 2300 gas
  left at each SSTORE that the specification takes), the run ends with no error if and only if
  the condition of `Usdt/Spec/Guards.lean` holds.
- `*_low`: with less gas than the cost of the success path, no run ends with no error.
- `*_mid` (round 26): with at least the cost but less than the stipend bound, no run ends with no
  error: an SSTORE is reached with at most 2300 gas left (EIP-2200, `Gas.NoWrite`). With two
  SSTOREs the proof splits on which one is reached so (`low_*2`, `DestroySpec.low2`).
- `*_iff_gas` (round 26): for every gas, the run ends with no error if and only if the condition
  holds and the gas is at least the larger of the cost and the stipend bound (for
  destroyBlackFunds, the larger of the cost and its two stipend bounds; for transferOwnership,
  `ownershipStip`, none when `a = 0`).

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
  let ⟨hst, hacc, hown, hp, _⟩ := ok_pause hfork hsize' hsel hc0 start (Ends.run hs) hok
  ⟨callOk_of_run hfork hsize' start within s hs hok, ⟨hst, hacc⟩, hown, hp⟩

/-- `pause()` succeeds exactly when `PauseGuard` holds, with the gas of its success path. -/
theorem pause_ok_iff (hstip : 3297 + slotCost c0 ≤ gas)
    (hg : PAUSE_COST + slotCost c0 + flagCost fork state message 1 ≤ gas) :
    RunsOk fork bound runChild evm within ↔ PauseGuard state message :=
  runsOk_iff (fun ⟨⟨h4, hv⟩, ⟨hst, hacc⟩, hown, hp⟩ =>
      spec_pause hfork hst hacc h4 hsize' hsel hv hown hp hc0 hstip hg)
    halted_false_ok start within (pause_comp hfork hsize' start within hsel hc0)

/-- `pause` over the EIP-8037 meter at any reservoir, with refills allowed (round 42): under
`PauseGuard` and the gas of `pause_ok_iff`, the loop over `StateGasMeter` from a frame `m` whose
`toNat` is the fresh frame, for any gas bound and message runner, ends with no error. -/
theorem pause_ok_dom (hstip : 3297 + slotCost c0 ≤ gas)
    (hg : PAUSE_COST + slotCost c0 + flagCost fork state message 1 ≤ gas)
    {m : Evm fork StateGasMeter} (hm : evm = Meter.toNat m) {boundS : Nat}
    {runS : MessageRunner fork StateGasMeter boundS} (withinS : GasMeter.gasHeld m.gas ≤ boundS)
    (hG : PauseGuard state message) : Shadow.RunsOkS fork boundS runS m withinS := by
  have key : ∃ Q : Evm fork Nat → Prop,
      SpecG fork (At CODE message 0 [] .empty gas state substate) Q ∧
        ∀ e, Q e → e.error = none := by
    obtain ⟨⟨h4, hv⟩, ⟨hst, hacc⟩, hown, hp⟩ := hG
    exact ⟨_, spec_pause hfork hst hacc h4 hsize' hsel hv hown hp hc0 hstip hg, halted_false_ok⟩
  obtain ⟨Q, h, hQ⟩ := key
  exact Shadow.runsOkS_of_specG hfork h hQ (hm ▸ start) withinS


theorem pause_low (hg : gas < PAUSE_COST + slotCost c0 + flagCost fork state message 1) :
    ¬ RunsOk fork bound runChild evm within :=
  not_runsOk_low2 hg (fun ⟨⟨h4, hv⟩, ⟨hst, hacc⟩, hown, hp⟩ _ =>
      spec_pause hfork hst hacc h4 hsize' hsel hv hown hp hc0)
    start within (pause_comp hfork hsize' start within hsel hc0)

theorem pause_mid (hg : PAUSE_COST + slotCost c0 + flagCost fork state message 1 ≤ gas)
    (hlt : gas < 3297 + slotCost c0) : ¬ RunsOk fork bound runChild evm within :=
  not_runsOk_stuck (fun ⟨⟨h4, hv⟩, _, hown, hp⟩ =>
      bad_pause hfork h4 hsize' hsel hv hown hp hc0 (.of_low hfork (by omega))
        (by simp only [PAUSE_COST] at hg; omega))
    start within (pause_comp hfork hsize' start within hsel hc0)

/-- `pause()` succeeds exactly when `PauseGuard` holds and the gas is at least the larger of the
cost of its success path and `3297 + price(slot 0)`. -/
theorem pause_iff_gas :
    RunsOk fork bound runChild evm within ↔ PauseGuard state message ∧
      max (PAUSE_COST + slotCost c0 + flagCost fork state message 1) (3297 + slotCost c0) ≤
        gas :=
  iff_max (fun hg hs => pause_ok_iff hfork hsize' start within hsel hc0 hs hg)
    (pause_low hfork hsize' start within hsel hc0) (pause_mid hfork hsize' start within hsel hc0)
    (fun h => of_runsOk h (pause_comp hfork hsize' start within hsel hc0))

end

section
variable (hsel : selector message.data = 0x3f4ba83a) {c0 : Bool}
  (hc0 : coldIn substate message.currentTarget 0 = c0)
include hsel hc0

theorem unpause_comp (s : Evm fork Nat)
    (hs : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) : UnpauseGuard state message :=
  let ⟨hst, hacc, hown, hp, _⟩ := ok_unpause hfork hsize' hsel hc0 start (Ends.run hs) hok
  ⟨callOk_of_run hfork hsize' start within s hs hok, ⟨hst, hacc⟩, hown, hp⟩

/-- `unpause()` succeeds exactly when `UnpauseGuard` holds, with the gas of its success path. -/
theorem unpause_ok_iff (hstip : 3184 + slotCost c0 ≤ gas)
    (hg : UNPAUSE_COST + slotCost c0 + flagCost fork state message 0 ≤ gas) :
    RunsOk fork bound runChild evm within ↔ UnpauseGuard state message :=
  runsOk_iff (fun ⟨⟨h4, hv⟩, ⟨hst, hacc⟩, hown, hp⟩ =>
      spec_unpause hfork hst hacc h4 hsize' hsel hv hown hp hc0 hstip hg)
    halted_false_ok start within (unpause_comp hfork hsize' start within hsel hc0)

/-- `unpause` over the EIP-8037 meter at any reservoir, with refills allowed (round 42): under
`UnpauseGuard` and the gas of `unpause_ok_iff`, the loop over `StateGasMeter` from a frame `m` whose
`toNat` is the fresh frame, for any gas bound and message runner, ends with no error. -/
theorem unpause_ok_dom (hstip : 3184 + slotCost c0 ≤ gas)
    (hg : UNPAUSE_COST + slotCost c0 + flagCost fork state message 0 ≤ gas)
    {m : Evm fork StateGasMeter} (hm : evm = Meter.toNat m) {boundS : Nat}
    {runS : MessageRunner fork StateGasMeter boundS} (withinS : GasMeter.gasHeld m.gas ≤ boundS)
    (hG : UnpauseGuard state message) : Shadow.RunsOkS fork boundS runS m withinS := by
  have key : ∃ Q : Evm fork Nat → Prop,
      SpecG fork (At CODE message 0 [] .empty gas state substate) Q ∧
        ∀ e, Q e → e.error = none := by
    obtain ⟨⟨h4, hv⟩, ⟨hst, hacc⟩, hown, hp⟩ := hG
    exact ⟨_, spec_unpause hfork hst hacc h4 hsize' hsel hv hown hp hc0 hstip hg, halted_false_ok⟩
  obtain ⟨Q, h, hQ⟩ := key
  exact Shadow.runsOkS_of_specG hfork h hQ (hm ▸ start) withinS


theorem unpause_low (hg : gas < UNPAUSE_COST + slotCost c0 + flagCost fork state message 0) :
    ¬ RunsOk fork bound runChild evm within :=
  not_runsOk_low2 hg (fun ⟨⟨h4, hv⟩, ⟨hst, hacc⟩, hown, hp⟩ _ =>
      spec_unpause hfork hst hacc h4 hsize' hsel hv hown hp hc0)
    start within (unpause_comp hfork hsize' start within hsel hc0)

theorem unpause_mid (hg : UNPAUSE_COST + slotCost c0 + flagCost fork state message 0 ≤ gas)
    (hlt : gas < 3184 + slotCost c0) : ¬ RunsOk fork bound runChild evm within :=
  not_runsOk_stuck (fun ⟨⟨h4, hv⟩, _, hown, hp⟩ =>
      bad_unpause hfork h4 hsize' hsel hv hown hp hc0 (.of_low hfork (by omega))
        (by simp only [UNPAUSE_COST] at hg; omega))
    start within (unpause_comp hfork hsize' start within hsel hc0)

/-- `unpause()` succeeds exactly when `UnpauseGuard` holds and the gas is at least the larger of
the cost of its success path and `3184 + price(slot 0)`. -/
theorem unpause_iff_gas :
    RunsOk fork bound runChild evm within ↔ UnpauseGuard state message ∧
      max (UNPAUSE_COST + slotCost c0 + flagCost fork state message 0) (3184 + slotCost c0) ≤
        gas :=
  iff_max (fun hg hs => unpause_ok_iff hfork hsize' start within hsel hc0 hs hg)
    (unpause_low hfork hsize' start within hsel hc0)
    (unpause_mid hfork hsize' start within hsel hc0)
    (fun h => of_runsOk h (unpause_comp hfork hsize' start within hsel hc0))

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
  let ⟨hst, hacc, hown, _⟩ := ok_addBlackList hfork hsize' hsel hc0 hcB start (Ends.run hs) hok
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

/-- `addBlackList` over the EIP-8037 meter at any reservoir, with refills allowed (round 42): under
`OwnerWriteGuard` and the gas of `addBlackList_ok_iff`, the loop over `StateGasMeter` from a frame `m` whose
`toNat` is the fresh frame, for any gas bound and message runner, ends with no error. -/
theorem addBlackList_ok_dom (hsel : selector message.data = 0x0ecb93c0)
    (hstip : 2779 + slotCost c0 + slotCost cB ≤ gas)
    (hg : 1567 + slotCost c0 + slotCost cB + listCost fork state message 1 ≤ gas)
    {m : Evm fork StateGasMeter} (hm : evm = Meter.toNat m) {boundS : Nat}
    {runS : MessageRunner fork StateGasMeter boundS} (withinS : GasMeter.gasHeld m.gas ≤ boundS)
    (hG : OwnerWriteGuard state message) : Shadow.RunsOkS fork boundS runS m withinS := by
  have key : ∃ Q : Evm fork Nat → Prop,
      SpecG fork (At CODE message 0 [] .empty gas state substate) Q ∧
        ∀ e, Q e → e.error = none := by
    obtain ⟨⟨h4, hv⟩, ⟨hst, hacc⟩, hown⟩ := hG
    exact ⟨_, spec_add hfork hst hacc h4 hsize' hsel hv hown hc0 hcB hstip hg, halted_false_ok⟩
  obtain ⟨Q, h, hQ⟩ := key
  exact Shadow.runsOkS_of_specG hfork h hQ (hm ▸ start) withinS


theorem addBlackList_low (hsel : selector message.data = 0x0ecb93c0)
    (hg : gas < 1567 + slotCost c0 + slotCost cB + listCost fork state message 1) :
    ¬ RunsOk fork bound runChild evm within :=
  not_runsOk_low2 hg (fun ⟨⟨h4, hv⟩, ⟨hst, hacc⟩, hown⟩ _ =>
      spec_add hfork hst hacc h4 hsize' hsel hv hown hc0 hcB)
    start within (addBlackList_comp hfork hsize' start within hc0 hcB hsel)

theorem addBlackList_mid (hsel : selector message.data = 0x0ecb93c0)
    (hg : 1567 + slotCost c0 + slotCost cB + listCost fork state message 1 ≤ gas)
    (hlt : gas < 2779 + slotCost c0 + slotCost cB) : ¬ RunsOk fork bound runChild evm within :=
  not_runsOk_stuck (fun ⟨⟨h4, hv⟩, _, hown⟩ =>
      bad_add hfork h4 hsize' hsel hv hown hc0 hcB (.of_low hfork (by omega)) (by omega))
    start within (addBlackList_comp hfork hsize' start within hc0 hcB hsel)

/-- `addBlackList(a)` succeeds exactly when `OwnerWriteGuard` holds and the gas is at least the
larger of the cost of its success path and `2779 + price(slot 0) + price(isBlackListed[a])`. -/
theorem addBlackList_iff_gas (hsel : selector message.data = 0x0ecb93c0) :
    RunsOk fork bound runChild evm within ↔ OwnerWriteGuard state message ∧
      max (1567 + slotCost c0 + slotCost cB + listCost fork state message 1)
        (2779 + slotCost c0 + slotCost cB) ≤ gas :=
  iff_max (fun hg hs => addBlackList_ok_iff hfork hsize' start within hc0 hcB hsel hs hg)
    (addBlackList_low hfork hsize' start within hc0 hcB hsel)
    (addBlackList_mid hfork hsize' start within hc0 hcB hsel)
    (fun h => of_runsOk h (addBlackList_comp hfork hsize' start within hc0 hcB hsel))

theorem removeBlackList_comp (hsel : selector message.data = 0xe4997dc5) (s : Evm fork Nat)
    (hs : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) : OwnerWriteGuard state message :=
  let ⟨hst, hacc, hown, _⟩ := ok_removeBlackList hfork hsize' hsel hc0 hcB start (Ends.run hs) hok
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

/-- `removeBlackList` over the EIP-8037 meter at any reservoir, with refills allowed (round 42): under
`OwnerWriteGuard` and the gas of `removeBlackList_ok_iff`, the loop over `StateGasMeter` from a frame `m` whose
`toNat` is the fresh frame, for any gas bound and message runner, ends with no error. -/
theorem removeBlackList_ok_dom (hsel : selector message.data = 0xe4997dc5)
    (hstip : 3307 + slotCost c0 + slotCost cB ≤ gas)
    (hg : 2095 + slotCost c0 + slotCost cB + listCost fork state message 0 ≤ gas)
    {m : Evm fork StateGasMeter} (hm : evm = Meter.toNat m) {boundS : Nat}
    {runS : MessageRunner fork StateGasMeter boundS} (withinS : GasMeter.gasHeld m.gas ≤ boundS)
    (hG : OwnerWriteGuard state message) : Shadow.RunsOkS fork boundS runS m withinS := by
  have key : ∃ Q : Evm fork Nat → Prop,
      SpecG fork (At CODE message 0 [] .empty gas state substate) Q ∧
        ∀ e, Q e → e.error = none := by
    obtain ⟨⟨h4, hv⟩, ⟨hst, hacc⟩, hown⟩ := hG
    exact ⟨_, spec_remove hfork hst hacc h4 hsize' hsel hv hown hc0 hcB hstip hg, halted_false_ok⟩
  obtain ⟨Q, h, hQ⟩ := key
  exact Shadow.runsOkS_of_specG hfork h hQ (hm ▸ start) withinS


theorem removeBlackList_low (hsel : selector message.data = 0xe4997dc5)
    (hg : gas < 2095 + slotCost c0 + slotCost cB + listCost fork state message 0) :
    ¬ RunsOk fork bound runChild evm within :=
  not_runsOk_low2 hg (fun ⟨⟨h4, hv⟩, ⟨hst, hacc⟩, hown⟩ _ =>
      spec_remove hfork hst hacc h4 hsize' hsel hv hown hc0 hcB)
    start within (removeBlackList_comp hfork hsize' start within hc0 hcB hsel)

theorem removeBlackList_mid (hsel : selector message.data = 0xe4997dc5)
    (hg : 2095 + slotCost c0 + slotCost cB + listCost fork state message 0 ≤ gas)
    (hlt : gas < 3307 + slotCost c0 + slotCost cB) : ¬ RunsOk fork bound runChild evm within :=
  not_runsOk_stuck (fun ⟨⟨h4, hv⟩, _, hown⟩ =>
      bad_remove hfork h4 hsize' hsel hv hown hc0 hcB (.of_low hfork (by omega)) (by omega))
    start within (removeBlackList_comp hfork hsize' start within hc0 hcB hsel)

/-- `removeBlackList(a)` succeeds exactly when `OwnerWriteGuard` holds and the gas is at least the
larger of the cost of its success path and `3307 + price(slot 0) + price(isBlackListed[a])`. -/
theorem removeBlackList_iff_gas (hsel : selector message.data = 0xe4997dc5) :
    RunsOk fork bound runChild evm within ↔ OwnerWriteGuard state message ∧
      max (2095 + slotCost c0 + slotCost cB + listCost fork state message 0)
        (3307 + slotCost c0 + slotCost cB) ≤ gas :=
  iff_max (fun hg hs => removeBlackList_ok_iff hfork hsize' start within hc0 hcB hsel hs hg)
    (removeBlackList_low hfork hsize' start within hc0 hcB hsel)
    (removeBlackList_mid hfork hsize' start within hc0 hcB hsel)
    (fun h => of_runsOk h (removeBlackList_comp hfork hsize' start within hc0 hcB hsel))

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
    ok_issue hfork hsize' hsel hc0 hc1 hcO start (Ends.run hs) hok
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

/-- `issue` over the EIP-8037 meter at any reservoir, with refills allowed (round 42): under
`IssueGuard` and the gas of `issue_ok_iff`, the loop over `StateGasMeter` from a frame `m` whose
`toNat` is the fresh frame, for any gas bound and message runner, ends with no error. -/
theorem issue_ok_dom (hsel : selector message.data = 0xcc872b66)
    (hstip : 4248 + slotCost c0 + slotCost c1 + slotCost cO + issueCostO fork state message ≤ gas)
    (hg : 3024 + slotCost c0 + slotCost c1 + slotCost cO + issueCostO fork state message +
      issueCostT fork state message ≤ gas)
    {m : Evm fork StateGasMeter} (hm : evm = Meter.toNat m) {boundS : Nat}
    {runS : MessageRunner fork StateGasMeter boundS} (withinS : GasMeter.gasHeld m.gas ≤ boundS)
    (hG : IssueGuard state message) : Shadow.RunsOkS fork boundS runS m withinS := by
  have key : ∃ Q : Evm fork Nat → Prop,
      SpecG fork (At CODE message 0 [] .empty gas state substate) Q ∧
        ∀ e, Q e → e.error = none := by
    obtain ⟨⟨h4, hv⟩, ⟨hst, hacc⟩, hown, h0, hT, hB⟩ := hG
    exact ⟨_, spec_issue hfork hst hacc h4 hsize' hsel hv hown ⟨h0, hT⟩ hB hc0 hc1 hcO hstip hg, halted_false_ok⟩
  obtain ⟨Q, h, hQ⟩ := key
  exact Shadow.runsOkS_of_specG hfork h hQ (hm ▸ start) withinS


theorem issue_low (hsel : selector message.data = 0xcc872b66)
    (hg : gas < 3024 + slotCost c0 + slotCost c1 + slotCost cO + issueCostO fork state message +
      issueCostT fork state message) :
    ¬ RunsOk fork bound runChild evm within :=
  not_runsOk_low2 hg (fun ⟨⟨h4, hv⟩, ⟨hst, hacc⟩, hown, h0, hT, hB⟩ _ =>
      spec_issue hfork hst hacc h4 hsize' hsel hv hown ⟨h0, hT⟩ hB hc0 hc1 hcO)
    start within (issue_comp hfork hsize' start within hc0 hc1 hcO hsel)

theorem issue_mid (hsel : selector message.data = 0xcc872b66)
    (hg : 3024 + slotCost c0 + slotCost c1 + slotCost cO + issueCostO fork state message +
      issueCostT fork state message ≤ gas)
    (hlt : gas < 4248 + slotCost c0 + slotCost c1 + slotCost cO + issueCostO fork state message) :
    ¬ RunsOk fork bound runChild evm within := by
  refine not_runsOk_stuck (fun ⟨⟨h4, hv⟩, ⟨hst, hacc⟩, hown, h0, hT, hB⟩ => ?_) start within
    (issue_comp hfork hsize' start within hc0 hc1 hcO hsel)
  by_cases h1 : gas < 4115 + slotCost c0 + slotCost c1 + slotCost cO
  · exact bad_issue hfork h4 hsize' hsel hv hown ⟨h0, hT⟩ hB hc0 hc1 hcO
      (.of_low hfork (by omega)) (by omega)
  · exact low_issue2 hfork hst hacc h4 hsize' hsel hv hown ⟨h0, hT⟩ hB hc0 hc1 hcO (by omega)
      (by omega) hlt

/-- `issue(a)` succeeds exactly when `IssueGuard` holds and the gas is at least the larger of the
cost of its success path and its stipend bound (more than 2300 gas left at the second SSTORE,
hence at the first). -/
theorem issue_iff_gas (hsel : selector message.data = 0xcc872b66) :
    RunsOk fork bound runChild evm within ↔ IssueGuard state message ∧
      max (3024 + slotCost c0 + slotCost c1 + slotCost cO + issueCostO fork state message +
        issueCostT fork state message)
        (4248 + slotCost c0 + slotCost c1 + slotCost cO + issueCostO fork state message) ≤ gas :=
  iff_max (fun hg hs => issue_ok_iff hfork hsize' start within hc0 hc1 hcO hsel hs hg)
    (issue_low hfork hsize' start within hc0 hc1 hcO hsel)
    (issue_mid hfork hsize' start within hc0 hc1 hcO hsel)
    (fun h => of_runsOk h (issue_comp hfork hsize' start within hc0 hc1 hcO hsel))

theorem redeem_comp (hsel : selector message.data = 0xdb006a75) (s : Evm fork Nat)
    (hs : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) : RedeemGuard state message :=
  let ⟨hst, hacc, hown, hT, hB, _⟩ :=
    ok_redeem hfork hsize' hsel hc0 hc1 hcO start (Ends.run hs) hok
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

/-- `redeem` over the EIP-8037 meter at any reservoir, with refills allowed (round 42): under
`RedeemGuard` and the gas of `redeem_ok_iff`, the loop over `StateGasMeter` from a frame `m` whose
`toNat` is the fresh frame, for any gas bound and message runner, ends with no error. -/
theorem redeem_ok_dom (hsel : selector message.data = 0xdb006a75)
    (hstip : 3838 + slotCost c0 + slotCost c1 + slotCost cO + redeemCostT fork state message ≤
      gas)
    (hg : 2614 + slotCost c0 + slotCost c1 + slotCost cO + redeemCostT fork state message +
      redeemCostO fork state message ≤ gas)
    {m : Evm fork StateGasMeter} (hm : evm = Meter.toNat m) {boundS : Nat}
    {runS : MessageRunner fork StateGasMeter boundS} (withinS : GasMeter.gasHeld m.gas ≤ boundS)
    (hG : RedeemGuard state message) : Shadow.RunsOkS fork boundS runS m withinS := by
  have key : ∃ Q : Evm fork Nat → Prop,
      SpecG fork (At CODE message 0 [] .empty gas state substate) Q ∧
        ∀ e, Q e → e.error = none := by
    obtain ⟨⟨h4, hv⟩, ⟨hst, hacc⟩, hown, hT, hB⟩ := hG
    exact ⟨_, spec_redeem hfork hst hacc h4 hsize' hsel hv hown hT hB hc0 hc1 hcO hstip hg, halted_false_ok⟩
  obtain ⟨Q, h, hQ⟩ := key
  exact Shadow.runsOkS_of_specG hfork h hQ (hm ▸ start) withinS


theorem redeem_low (hsel : selector message.data = 0xdb006a75)
    (hg : gas < 2614 + slotCost c0 + slotCost c1 + slotCost cO + redeemCostT fork state message +
      redeemCostO fork state message) :
    ¬ RunsOk fork bound runChild evm within :=
  not_runsOk_low2 hg (fun ⟨⟨h4, hv⟩, ⟨hst, hacc⟩, hown, hT, hB⟩ _ =>
      spec_redeem hfork hst hacc h4 hsize' hsel hv hown hT hB hc0 hc1 hcO)
    start within (redeem_comp hfork hsize' start within hc0 hc1 hcO hsel)

theorem redeem_mid (hsel : selector message.data = 0xdb006a75)
    (hg : 2614 + slotCost c0 + slotCost c1 + slotCost cO + redeemCostT fork state message +
      redeemCostO fork state message ≤ gas)
    (hlt : gas < 3838 + slotCost c0 + slotCost c1 + slotCost cO + redeemCostT fork state message) :
    ¬ RunsOk fork bound runChild evm within := by
  refine not_runsOk_stuck (fun ⟨⟨h4, hv⟩, ⟨hst, hacc⟩, hown, hT, hB⟩ => ?_) start within
    (redeem_comp hfork hsize' start within hc0 hc1 hcO hsel)
  by_cases h1 : gas < 3479 + slotCost c0 + slotCost c1 + slotCost cO
  · exact bad_redeem hfork h4 hsize' hsel hv hown hT hB hc0 hc1 hcO
      (.of_low hfork (by omega)) (by omega)
  · exact low_redeem2 hfork hst hacc h4 hsize' hsel hv hown hT hB hc0 hc1 hcO (by omega)
      (by omega) hlt

/-- `redeem(a)` succeeds exactly when `RedeemGuard` holds and the gas is at least the larger of the
cost of its success path and its stipend bound (more than 2300 gas left at the second SSTORE,
hence at the first). -/
theorem redeem_iff_gas (hsel : selector message.data = 0xdb006a75) :
    RunsOk fork bound runChild evm within ↔ RedeemGuard state message ∧
      max (2614 + slotCost c0 + slotCost c1 + slotCost cO + redeemCostT fork state message +
        redeemCostO fork state message)
        (3838 + slotCost c0 + slotCost c1 + slotCost cO + redeemCostT fork state message) ≤ gas :=
  iff_max (fun hg hs => redeem_ok_iff hfork hsize' start within hc0 hc1 hcO hsel hs hg)
    (redeem_low hfork hsize' start within hc0 hc1 hcO hsel)
    (redeem_mid hfork hsize' start within hc0 hc1 hcO hsel)
    (fun h => of_runsOk h (redeem_comp hfork hsize' start within hc0 hc1 hcO hsel))

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
    ok_setParams hfork hsize' hsel hc0 hc3 hc9 hc4 start (Ends.run hs) hok
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

/-- `setParams` over the EIP-8037 meter at any reservoir, with refills allowed (round 42): under
`SetParamsGuard` and the gas of `setParams_ok_iff`, the loop over `StateGasMeter` from a frame `m` whose
`toNat` is the fresh frame, for any gas bound and message runner, ends with no error. -/
theorem setParams_ok_dom
    (hstip : 3168 + slotCost c0 + Gas.writeCost fork (originalAt state message.currentTarget 3)
      (storageAt state message.currentTarget 3) (wordArg message.data 0) c3 + slotCost c9 +
      50 * exponentBytes (storageAt state message.currentTarget 9) +
      mulCost (wordArg message.data 1) ≤ gas)
    (hg : 2425 + paramsCost fork state message c0 c3 c9 c4 ≤ gas)
    {m : Evm fork StateGasMeter} (hm : evm = Meter.toNat m) {boundS : Nat}
    {runS : MessageRunner fork StateGasMeter boundS} (withinS : GasMeter.gasHeld m.gas ≤ boundS)
    (hG : SetParamsGuard state message) : Shadow.RunsOkS fork boundS runS m withinS := by
  have key : ∃ Q : Evm fork Nat → Prop,
      SpecG fork (At CODE message 0 [] .empty gas state substate) Q ∧
        ∀ e, Q e → e.error = none := by
    obtain ⟨⟨h4, hv⟩, ⟨hst, hacc⟩, hown, hb, hm, hov⟩ := hG
    exact ⟨_, spec_setParams hfork hst hacc h4 hsize' hsel hv hown hb hm hov hc0 hc3 hc9 hc4 hstip hg, halted_false_ok⟩
  obtain ⟨Q, h, hQ⟩ := key
  exact Shadow.runsOkS_of_specG hfork h hQ (hm ▸ start) withinS


theorem setParams_low (hg : gas < 2425 + paramsCost fork state message c0 c3 c9 c4) :
    ¬ RunsOk fork bound runChild evm within :=
  not_runsOk_low2 hg (fun ⟨⟨h4, hv⟩, ⟨hst, hacc⟩, hown, hb, hm, hov⟩ _ =>
      spec_setParams hfork hst hacc h4 hsize' hsel hv hown hb hm hov hc0 hc3 hc9 hc4)
    start within (setParams_comp hfork hsize' start within hsel hc0 hc3 hc9 hc4)

theorem setParams_mid (hg : 2425 + paramsCost fork state message c0 c3 c9 c4 ≤ gas)
    (hlt : gas < 3168 + slotCost c0 + Gas.writeCost fork (originalAt state message.currentTarget 3)
      (storageAt state message.currentTarget 3) (wordArg message.data 0) c3 + slotCost c9 +
      50 * exponentBytes (storageAt state message.currentTarget 9) +
      mulCost (wordArg message.data 1)) :
    ¬ RunsOk fork bound runChild evm within := by
  refine not_runsOk_stuck (fun ⟨⟨h4, hv⟩, ⟨hst, hacc⟩, hown, hb, hm, hov⟩ => ?_) start within
    (setParams_comp hfork hsize' start within hsel hc0 hc3 hc9 hc4)
  simp only [paramsCost] at hg
  by_cases h1 : gas < 3108 + slotCost c0
  · exact bad_setParams hfork h4 hsize' hsel hv hown hb hm hc0 (.of_low hfork (by omega))
      (by omega)
  · exact low_setParams2 hfork hst hacc h4 hsize' hsel hv hown hb hm hov hc0 hc3 hc9 (by omega)
      (by omega) hlt

/-- `setParams(b, m)` succeeds exactly when `SetParamsGuard` holds and the gas is at least the
larger of the cost of its success path and its stipend bound (more than 2300 gas left at the
second SSTORE, hence at the first). -/
theorem setParams_iff_gas :
    RunsOk fork bound runChild evm within ↔ SetParamsGuard state message ∧
      max (2425 + paramsCost fork state message c0 c3 c9 c4)
        (3168 + slotCost c0 + Gas.writeCost fork (originalAt state message.currentTarget 3)
          (storageAt state message.currentTarget 3) (wordArg message.data 0) c3 + slotCost c9 +
          50 * exponentBytes (storageAt state message.currentTarget 9) +
          mulCost (wordArg message.data 1)) ≤ gas :=
  iff_max (fun hg hs => setParams_ok_iff hfork hsize' start within hsel hc0 hc3 hc9 hc4 hs hg)
    (setParams_low hfork hsize' start within hsel hc0 hc3 hc9 hc4)
    (setParams_mid hfork hsize' start within hsel hc0 hc3 hc9 hc4)
    (fun h => of_runsOk h (setParams_comp hfork hsize' start within hsel hc0 hc3 hc9 hc4))

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
  let ⟨hst, hacc, hown, _⟩ := ok_deprecate hfork hsize' hsel hc0 hc10 start (Ends.run hs) hok
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

/-- `deprecate` over the EIP-8037 meter at any reservoir, with refills allowed (round 42): under
`OwnerWriteGuard` and the gas of `deprecate_ok_iff`, the loop over `StateGasMeter` from a frame `m` whose
`toNat` is the fresh frame, for any gas bound and message runner, ends with no error. -/
theorem deprecate_ok_dom
    (hstip : 2840 + slotCost c0 + slotCost c10 + Gas.writeCost fork
      (originalAt state message.currentTarget 10) (storageAt state message.currentTarget 10)
      (withPaused (storageAt state message.currentTarget 10) 1) false ≤ gas)
    (hg : 1628 + slotCost c0 + slotCost c10 + depCost fork state message ≤ gas)
    {m : Evm fork StateGasMeter} (hm : evm = Meter.toNat m) {boundS : Nat}
    {runS : MessageRunner fork StateGasMeter boundS} (withinS : GasMeter.gasHeld m.gas ≤ boundS)
    (hG : OwnerWriteGuard state message) : Shadow.RunsOkS fork boundS runS m withinS := by
  have key : ∃ Q : Evm fork Nat → Prop,
      SpecG fork (At CODE message 0 [] .empty gas state substate) Q ∧
        ∀ e, Q e → e.error = none := by
    obtain ⟨⟨h4, hv⟩, ⟨hst, hacc⟩, hown⟩ := hG
    exact ⟨_, spec_deprecate hfork hst hacc h4 hsize' hsel hv hown hc0 hc10 hstip hg, halted_false_ok⟩
  obtain ⟨Q, h, hQ⟩ := key
  exact Shadow.runsOkS_of_specG hfork h hQ (hm ▸ start) withinS


theorem deprecate_low (hg : gas < 1628 + slotCost c0 + slotCost c10 + depCost fork state message) :
    ¬ RunsOk fork bound runChild evm within :=
  not_runsOk_low2 hg (fun ⟨⟨h4, hv⟩, ⟨hst, hacc⟩, hown⟩ _ =>
      spec_deprecate hfork hst hacc h4 hsize' hsel hv hown hc0 hc10)
    start within (deprecate_comp hfork hsize' start within hsel hc0 hc10)

theorem deprecate_mid (hg : 1628 + slotCost c0 + slotCost c10 + depCost fork state message ≤ gas)
    (hlt : gas < 2840 + slotCost c0 + slotCost c10 + Gas.writeCost fork
      (originalAt state message.currentTarget 10) (storageAt state message.currentTarget 10)
      (withPaused (storageAt state message.currentTarget 10) 1) false) :
    ¬ RunsOk fork bound runChild evm within := by
  refine not_runsOk_stuck (fun ⟨⟨h4, hv⟩, ⟨hst, hacc⟩, hown⟩ => ?_) start within
    (deprecate_comp hfork hsize' start within hsel hc0 hc10)
  simp only [depCost] at hg
  by_cases h1 : gas < 2673 + slotCost c0 + slotCost c10
  · exact bad_deprecate hfork h4 hsize' hsel hv hown hc0 hc10 (.of_low hfork (by omega))
      (by omega)
  · exact low_deprecate2 hfork hst hacc h4 hsize' hsel hv hown hc0 hc10 (by omega) (by omega) hlt

/-- `deprecate(a)` succeeds exactly when `OwnerWriteGuard` holds and the gas is at least the larger
of the cost of its success path and its stipend bound (more than 2300 gas left at the second
SSTORE, hence at the first). -/
theorem deprecate_iff_gas :
    RunsOk fork bound runChild evm within ↔ OwnerWriteGuard state message ∧
      max (1628 + slotCost c0 + slotCost c10 + depCost fork state message)
        (2840 + slotCost c0 + slotCost c10 + Gas.writeCost fork
          (originalAt state message.currentTarget 10) (storageAt state message.currentTarget 10)
          (withPaused (storageAt state message.currentTarget 10) 1) false) ≤ gas :=
  iff_max (fun hg hs => deprecate_ok_iff hfork hsize' start within hsel hc0 hc10 hs hg)
    (deprecate_low hfork hsize' start within hsel hc0 hc10)
    (deprecate_mid hfork hsize' start within hsel hc0 hc10)
    (fun h => of_runsOk h (deprecate_comp hfork hsize' start within hsel hc0 hc10))

end

section
variable (hsel : selector message.data = 0xf2fde38b) {c0 : Bool}
  (hc0 : coldIn substate message.currentTarget 0 = c0)
include hsel hc0

theorem transferOwnership_comp (s : Evm fork Nat)
    (hs : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) : TransferOwnershipGuard state message := by
  obtain ⟨hown, -, h⟩ := ok_transferOwnership hfork hsize' hsel hc0 start (Ends.run hs) hok
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

/-- `transferOwnership` over the EIP-8037 meter at any reservoir, with refills allowed (round 42): under
`TransferOwnershipGuard` and the gas of `transferOwnership_ok_iff`, the loop over `StateGasMeter` from a frame `m` whose
`toNat` is the fresh frame, for any gas bound and message runner, ends with no error. -/
theorem transferOwnership_ok_dom (hstip : addrArg message.data 0 ≠ 0 → 3401 + slotCost c0 ≤ gas)
    (hg : ownershipCost fork state message c0 ≤ gas)
    {m : Evm fork StateGasMeter} (hm : evm = Meter.toNat m) {boundS : Nat}
    {runS : MessageRunner fork StateGasMeter boundS} (withinS : GasMeter.gasHeld m.gas ≤ boundS)
    (hG : TransferOwnershipGuard state message) : Shadow.RunsOkS fork boundS runS m withinS := by
  have key : ∃ Q : Evm fork Nat → Prop,
      SpecG fork (At CODE message 0 [] .empty gas state substate) Q ∧
        ∀ e, Q e → e.error = none := by
    obtain ⟨⟨h4, hv⟩, hown, hw⟩ := hG
    refine ⟨fun e => e.error = none, ?_, fun _ h => h⟩
    by_cases hz : addrArg message.data 0 = 0
    · simp only [ownershipCost, hz, ↓reduceIte] at hg
      exact (spec_transferOwnership_zero hfork h4 hsize' hsel hv hown hz hc0 hg).consequence
        (fun _ h => h) halted_false_ok
    · simp only [ownershipCost, hz, ↓reduceIte] at hg
      obtain ⟨hst, hacc⟩ := hw hz
      exact (spec_transferOwnership hfork hst hacc h4 hsize' hsel hv hown hz hc0 (hstip hz)
        hg).consequence (fun _ h => h) halted_false_ok
  obtain ⟨Q, h, hQ⟩ := key
  exact Shadow.runsOkS_of_specG hfork h hQ (hm ▸ start) withinS


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

/-- The gas that the success path of `transferOwnership(a)` needs so that more than 2300 is left
at its SSTORE: none for `a = 0` (no SSTORE), `3401 + price(slot 0)` otherwise. -/
abbrev ownershipStip (message : Message fork) (c0 : Bool) : Nat :=
  if addrArg message.data 0 = 0 then 0 else 3401 + slotCost c0

theorem transferOwnership_mid (hg : ownershipCost fork state message c0 ≤ gas)
    (hlt : gas < ownershipStip message c0) : ¬ RunsOk fork bound runChild evm within := by
  refine not_runsOk_stuck (fun ⟨⟨h4, hv⟩, hown, _⟩ => ?_) start within
    (transferOwnership_comp hfork hsize' start within hsel hc0)
  by_cases hz : addrArg message.data 0 = 0
  · simp only [ownershipStip, hz, ↓reduceIte] at hlt
    omega
  · simp only [ownershipCost, ownershipStip, hz, ↓reduceIte] at hg hlt
    exact bad_transferOwnership hfork h4 hsize' hsel hv hown hz hc0 (.of_low hfork (by omega))
      (by omega)

/-- `transferOwnership(a)` succeeds exactly when `TransferOwnershipGuard` holds and the gas is at
least the larger of `ownershipCost` and `ownershipStip`. -/
theorem transferOwnership_iff_gas :
    RunsOk fork bound runChild evm within ↔ TransferOwnershipGuard state message ∧
      max (ownershipCost fork state message c0) (ownershipStip message c0) ≤ gas :=
  iff_max (fun hg hs => transferOwnership_ok_iff hfork hsize' start within hsel hc0
      (fun hz => by simpa only [ownershipStip, hz, ↓reduceIte] using hs) hg)
    (transferOwnership_low hfork hsize' start within hsel hc0)
    (transferOwnership_mid hfork hsize' start within hsel hc0)
    (fun h => of_runsOk h (transferOwnership_comp hfork hsize' start within hsel hc0))

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
    ok_destroyBlackFunds hfork hsize' hsel hdep hc0 hcL hc10 hcB hc1 start (Ends.run hs) hok
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

/-- `destroyBlackFunds` over the EIP-8037 meter at any reservoir, with refills allowed (round 42): under
`DestroyBlackFundsGuard` and the gas of `destroyBlackFunds_ok_iff`, the loop over `StateGasMeter` from a frame `m` whose
`toNat` is the fresh frame, for any gas bound and message runner, ends with no error. -/
theorem destroyBlackFunds_ok_dom
    (hstip1 : 3763 + slotCost c0 + slotCost cL + slotCost c10 + slotCost cB ≤ gas)
    (hstip2 : 3796 + slotCost c0 + slotCost cL + slotCost c10 + slotCost cB +
      costB fork state message + slotCost c1 ≤ gas)
    (hg : 2865 + slotCost c0 + slotCost cL + slotCost c10 + slotCost cB + slotCost c1 +
      costB fork state message + costT fork state message ≤ gas)
    {m : Evm fork StateGasMeter} (hm : evm = Meter.toNat m) {boundS : Nat}
    {runS : MessageRunner fork StateGasMeter boundS} (withinS : GasMeter.gasHeld m.gas ≤ boundS)
    (hG : DestroyBlackFundsGuard state message) : Shadow.RunsOkS fork boundS runS m withinS := by
  have key : ∃ Q : Evm fork Nat → Prop,
      SpecG fork (At CODE message 0 [] .empty gas state substate) Q ∧
        ∀ e, Q e → e.error = none := by
    obtain ⟨⟨h4, hv⟩, ⟨hst, hacc⟩, hown, hl⟩ := hG
    exact ⟨_, DestroySpec.spec hfork hst hacc h4 hsize' hsel hv hown hl hdep hc0 hcL hc10 hcB hc1
        hstip1 hstip2 hg, halted_false_ok⟩
  obtain ⟨Q, h, hQ⟩ := key
  exact Shadow.runsOkS_of_specG hfork h hQ (hm ▸ start) withinS


theorem destroyBlackFunds_low
    (hg : gas < 2865 + slotCost c0 + slotCost cL + slotCost c10 + slotCost cB + slotCost c1 +
      costB fork state message + costT fork state message) :
    ¬ RunsOk fork bound runChild evm within :=
  not_runsOk_low3 hg (fun ⟨⟨h4, hv⟩, ⟨hst, hacc⟩, hown, hl⟩ _ =>
      DestroySpec.spec hfork hst hacc h4 hsize' hsel hv hown hl hdep hc0 hcL hc10 hcB hc1)
    start within (destroyBlackFunds_comp hfork hsize' start within hsel hdep hc0 hcL hc10 hcB hc1)

theorem destroyBlackFunds_mid
    (hg : 2865 + slotCost c0 + slotCost cL + slotCost c10 + slotCost cB + slotCost c1 +
      costB fork state message + costT fork state message ≤ gas)
    (hlt : gas < max (3763 + slotCost c0 + slotCost cL + slotCost c10 + slotCost cB)
      (3796 + slotCost c0 + slotCost cL + slotCost c10 + slotCost cB +
        costB fork state message + slotCost c1)) :
    ¬ RunsOk fork bound runChild evm within := by
  refine not_runsOk_stuck (fun ⟨⟨h4, hv⟩, ⟨hst, hacc⟩, hown, hl⟩ => ?_) start within
    (destroyBlackFunds_comp hfork hsize' start within hsel hdep hc0 hcL hc10 hcB hc1)
  by_cases h1 : gas < 3763 + slotCost c0 + slotCost cL + slotCost c10 + slotCost cB
  · exact DestroySpec.bad hfork h4 hsize' hsel hv hown hl hdep hc0 hcL hc10 hcB
      (.of_low hfork (by omega)) (by omega)
  · exact DestroySpec.low2 hfork hst hacc h4 hsize' hsel hv hown hl hdep hc0 hcL hc10 hcB hc1
      (by omega) (by omega) (by omega)

/-- `destroyBlackFunds(a)`, not deprecated, succeeds exactly when `DestroyBlackFundsGuard` holds
and the gas is at least the largest of the cost of its success path and its two stipend
bounds. -/
theorem destroyBlackFunds_iff_gas :
    RunsOk fork bound runChild evm within ↔ DestroyBlackFundsGuard state message ∧
      max (2865 + slotCost c0 + slotCost cL + slotCost c10 + slotCost cB + slotCost c1 +
        costB fork state message + costT fork state message)
        (max (3763 + slotCost c0 + slotCost cL + slotCost c10 + slotCost cB)
          (3796 + slotCost c0 + slotCost cL + slotCost c10 + slotCost cB +
            costB fork state message + slotCost c1)) ≤ gas :=
  iff_max (fun hg hs => destroyBlackFunds_ok_iff hfork hsize' start within hsel hdep hc0 hcL hc10
      hcB hc1 (Nat.max_le.mp hs).1 (Nat.max_le.mp hs).2 hg)
    (destroyBlackFunds_low hfork hsize' start within hsel hdep hc0 hcL hc10 hcB hc1)
    (destroyBlackFunds_mid hfork hsize' start within hsel hdep hc0 hcL hc10 hcB hc1)
    (fun h => of_runsOk h
      (destroyBlackFunds_comp hfork hsize' start within hsel hdep hc0 hcL hc10 hcB hc1))

end

end

end UsdtVerify.Exact
