import UsdtVerify.Complete.Exact
import UsdtVerify.Functions.PauseSpec
import UsdtVerify.Functions.BlackListSpec
import UsdtVerify.Functions.IssueSpec
import UsdtVerify.Functions.SetParamsFault
import UsdtVerify.Functions.AddrWriteSpec
import UsdtVerify.Functions.Destroy
import UsdtVerify.Functions.DestroySpec

/-!
# Completeness of the owner functions

pause, unpause, addBlackList, removeBlackList, issue, redeem, setParams, deprecate,
transferOwnership, and destroyBlackFunds (not deprecated). For each: every run of a call with the
selector of the function that ends with no error, for any gas, gas bound and message runner, is
the success path of its specification, with the exact output (empty), gas, state and substate.
The checks that the run passed are part of the conclusion (the caller is the owner, and the
`require`s of the function).

The other cases are excluded by the reverts (`*_notOwner`, `spec_pause_paused`,
`spec_unpause_notPaused`, `spec_issue_req1/2`, `spec_redeem_req1/2`, `spec_bpHigh`,
`spec_feeHigh`, `Destroy.spec_notListed`) and, for setParams, by the INVALID of the overflow of
`m * 10^d` (`SetParamsSpec.spec_mulOv`).

Hypotheses beyond the call: Berlin ≤ fork (Glamsterdam included); destroyBlackFunds also takes
`hdep` (byte 20 of slot 10 is 0: the deprecated path calls out, see DeprecatedDestroy.lean).
The frame may be static and the contract may have no account: once the reverts are excluded,
each writing path reaches its first SSTORE, which in a static frame or with no account is
`Gas.Stuck`, so no such run ends with no error, and each conclusion (for transferOwnership, its
`a ≠ 0` case) states `message.isStatic = false` and an account of the contract (`Gas.no_ok_stuck` with `bad_pause`,
`bad_unpause`, `bad_add`, `bad_remove`, `bad_issue`, `bad_redeem`, `bad_setParams`,
`bad_deprecate`, `bad_transferOwnership`, `DestroySpec.bad`). For setParams this comes before
the overflow of `m * 10^d`, which follows the write of slot 3.
-/

namespace UsdtVerify.Complete

open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open UsdtVerify.Gas
open Transfer TransferOk Owner Admin Pause BlackList Issue SafeMath SetParams AddrWrite
open PauseSpec BlackListSpec IssueSpec SetParamsSpec AddrWriteSpec DestroySpec

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate} {bound : Nat} {runChild : MessageRunner fork Nat bound}
  {evm s : Evm fork Nat} {gas : Nat}

theorem not_ne {a b : U256} (h : ¬ a ≠ b) : a = b := by simpa using h

/-- Every successful `pause()` call is the owner's, when not paused
The conclusion states that the frame is not static and the contract has an account:
otherwise the SSTORE of slot 0 is `Gas.Stuck`
(`bad_pause`). -/
theorem ok_pause (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x8456cb59)
    {c0 : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) :
    message.isStatic = false ∧ hasAccount state message.currentTarget ∧
    callerWord message = ownerOf state message.currentTarget ∧
      byte20 (storageAt state message.currentTarget 0) = 0 ∧ s.output = .empty ∧
      s.gas = gas - (PAUSE_COST + slotCost c0 + flagCost fork state message 1) ∧
      s.state = writeSlot state message.currentTarget 0
          (withPaused (storageAt state message.currentTarget 0) 1) ∧
      s.substate = { storeSub fork substate message.currentTarget 0
            (originalAt state message.currentTarget 0) (storageAt state message.currentTarget 0)
            (withPaused (storageAt state message.currentTarget 0) 1) with
          logs := substate.logs.push (log0 message.currentTarget PAUSE_TOPIC) } := by
  obtain ⟨h4, hv, -⟩ := runFrame_ok_dispatch hfork hsize' start within hrun hok
  by_cases hown : callerWord message ≠ ownerOf state message.currentTarget
  · exact (no_ok (fun g hg => spec_pause_notOwner hfork h4 hsize' hsel hv hown hc0 hg)
      (fun _ e h => halted_true_error e h) start within hrun hok).elim
  have hown := not_ne hown
  by_cases hp : byte20 (storageAt state message.currentTarget 0) ≠ 0
  · exact (no_ok (fun g hg => spec_pause_paused hfork h4 hsize' hsel hv hown hp hc0 hg)
      (fun _ e h => halted_true_error e h) start within hrun hok).elim
  have hp : byte20 (storageAt state message.currentTarget 0) = 0 := by omega
  by_cases hgood : ¬(message.isStatic = false ∧ hasAccount state message.currentTarget)
  · exact (Gas.no_ok_stuck (fun g hg => bad_pause hfork (Gas.bad_of_not hgood) h4 hsize' hsel hv
      hown hp hc0 hg) start within hrun hok).elim
  obtain ⟨hstatic, hacc⟩ := Classical.not_not.mp hgood
  obtain ⟨-, -, ho, hg, hst, hss⟩ := ok_exact2
    (fun g h1 h2 => spec_pause hfork hstatic hacc h4 hsize' hsel hv hown hp hc0 h1 h2)
    start within hrun hok
  exact ⟨hstatic, hacc, hown, hp, ho, hg, hst, hss⟩

/-- Every successful `unpause()` call is the owner's, when paused
The conclusion states that the frame is not static and the contract has an account:
otherwise the SSTORE of slot 0 is `Gas.Stuck`
(`bad_unpause`). -/
theorem ok_unpause (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x3f4ba83a)
    {c0 : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) :
    message.isStatic = false ∧ hasAccount state message.currentTarget ∧
    callerWord message = ownerOf state message.currentTarget ∧
      byte20 (storageAt state message.currentTarget 0) ≠ 0 ∧ s.output = .empty ∧
      s.gas = gas - (UNPAUSE_COST + slotCost c0 + flagCost fork state message 0) ∧
      s.state = writeSlot state message.currentTarget 0
          (withPaused (storageAt state message.currentTarget 0) 0) ∧
      s.substate = { storeSub fork substate message.currentTarget 0
            (originalAt state message.currentTarget 0) (storageAt state message.currentTarget 0)
            (withPaused (storageAt state message.currentTarget 0) 0) with
          logs := substate.logs.push (log0 message.currentTarget UNPAUSE_TOPIC) } := by
  obtain ⟨h4, hv, -⟩ := runFrame_ok_dispatch hfork hsize' start within hrun hok
  by_cases hown : callerWord message ≠ ownerOf state message.currentTarget
  · exact (no_ok (fun g hg => spec_unpause_notOwner hfork h4 hsize' hsel hv hown hc0 hg)
      (fun _ e h => halted_true_error e h) start within hrun hok).elim
  have hown := not_ne hown
  by_cases hp : byte20 (storageAt state message.currentTarget 0) = 0
  · exact (no_ok (fun g hg => spec_unpause_notPaused hfork h4 hsize' hsel hv hown hp hc0 hg)
      (fun _ e h => halted_true_error e h) start within hrun hok).elim
  by_cases hgood : ¬(message.isStatic = false ∧ hasAccount state message.currentTarget)
  · exact (Gas.no_ok_stuck (fun g hg => bad_unpause hfork (Gas.bad_of_not hgood) h4 hsize' hsel
      hv hown hp hc0 hg) start within hrun hok).elim
  obtain ⟨hstatic, hacc⟩ := Classical.not_not.mp hgood
  obtain ⟨-, -, ho, hg, hst, hss⟩ := ok_exact2
    (fun g h1 h2 => spec_unpause hfork hstatic hacc h4 hsize' hsel hv hown hp hc0 h1 h2)
    start within hrun hok
  exact ⟨hstatic, hacc, hown, hp, ho, hg, hst, hss⟩

/-- Every successful `addBlackList(a)` call is the owner's
The conclusion states that the frame is not static and the contract has an account:
otherwise the SSTORE of `isBlackListed[a]` is
`Gas.Stuck` (`bad_add`). -/
theorem ok_addBlackList (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x0ecb93c0)
    {c0 cB : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hcB : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget
      (listSlot (addrArg message.data 0)) = cB)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) :
    message.isStatic = false ∧ hasAccount state message.currentTarget ∧
    callerWord message = ownerOf state message.currentTarget ∧ s.output = .empty ∧
      s.gas = gas - (1567 + slotCost c0 + slotCost cB + listCost fork state message 1) ∧
      s.state = listState state message 1 ∧
      s.substate = listSub fork substate state message 1 ADDED_TOPIC := by
  obtain ⟨h4, hv, -⟩ := runFrame_ok_dispatch hfork hsize' start within hrun hok
  by_cases hown : callerWord message ≠ ownerOf state message.currentTarget
  · exact (no_ok (fun g hg => spec_add_notOwner hfork h4 hsize' hsel hv hown hc0 hg)
      (fun _ e h => halted_true_error e h) start within hrun hok).elim
  have hown := not_ne hown
  by_cases hgood : ¬(message.isStatic = false ∧ hasAccount state message.currentTarget)
  · exact (Gas.no_ok_stuck (fun g hg => bad_add hfork (Gas.bad_of_not hgood) h4 hsize' hsel hv
      hown hc0 hcB hg) start within hrun hok).elim
  obtain ⟨hstatic, hacc⟩ := Classical.not_not.mp hgood
  obtain ⟨-, -, ho, hg, hst, hss⟩ := ok_exact2
    (fun g h1 h2 => spec_add hfork hstatic hacc h4 hsize' hsel hv hown hc0 hcB h1 h2)
    start within hrun hok
  exact ⟨hstatic, hacc, hown, ho, hg, hst, hss⟩

/-- Every successful `removeBlackList(a)` call is the owner's
The conclusion states that the frame is not static and the contract has an account:
otherwise the SSTORE of `isBlackListed[a]` is
`Gas.Stuck` (`bad_remove`). -/
theorem ok_removeBlackList (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xe4997dc5)
    {c0 cB : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hcB : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget
      (listSlot (addrArg message.data 0)) = cB)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) :
    message.isStatic = false ∧ hasAccount state message.currentTarget ∧
    callerWord message = ownerOf state message.currentTarget ∧ s.output = .empty ∧
      s.gas = gas - (2095 + slotCost c0 + slotCost cB + listCost fork state message 0) ∧
      s.state = listState state message 0 ∧
      s.substate = listSub fork substate state message 0 REMOVED_TOPIC := by
  obtain ⟨h4, hv, -⟩ := runFrame_ok_dispatch hfork hsize' start within hrun hok
  by_cases hown : callerWord message ≠ ownerOf state message.currentTarget
  · exact (no_ok (fun g hg => spec_remove_notOwner hfork h4 hsize' hsel hv hown hc0 hg)
      (fun _ e h => halted_true_error e h) start within hrun hok).elim
  have hown := not_ne hown
  by_cases hgood : ¬(message.isStatic = false ∧ hasAccount state message.currentTarget)
  · exact (Gas.no_ok_stuck (fun g hg => bad_remove hfork (Gas.bad_of_not hgood) h4 hsize' hsel hv
      hown hc0 hcB hg) start within hrun hok).elim
  obtain ⟨hstatic, hacc⟩ := Classical.not_not.mp hgood
  obtain ⟨-, -, ho, hg, hst, hss⟩ := ok_exact2
    (fun g h1 h2 => spec_remove hfork hstatic hacc h4 hsize' hsel hv hown hc0 hcB h1 h2)
    start within hrun hok
  exact ⟨hstatic, hacc, hown, ho, hg, hst, hss⟩

/-- Every successful `issue(a)` call is the owner's, with `0 < a` and no overflow of
`_totalSupply + a` nor of `balances[owner] + a`
The conclusion states that the frame is not static and the contract has an account:
otherwise the SSTORE of `balances[owner]` is
`Gas.Stuck` (`bad_issue`). -/
theorem ok_issue (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xcc872b66)
    {c0 c1 cO : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hc1 : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget 1 = c1)
    (hcO : coldIn (accessSlot (accessSlot substate message.currentTarget 0) message.currentTarget 1)
      message.currentTarget (ownerBal state message.currentTarget) = cO)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) :
    message.isStatic = false ∧ hasAccount state message.currentTarget ∧
    callerWord message = ownerOf state message.currentTarget ∧
      0 < (wordArg message.data 0).toNat ∧
      (storageAt state message.currentTarget 1).toNat + (wordArg message.data 0).toNat < 2 ^ 256 ∧
      (storageAt state message.currentTarget (ownerBal state message.currentTarget)).toNat +
        (wordArg message.data 0).toNat < 2 ^ 256 ∧
      s.output = .empty ∧
      s.gas = gas - (3024 + slotCost c0 + slotCost c1 + slotCost cO +
          issueCostO fork state message + issueCostT fork state message) ∧
      s.state = issueState state message ∧ s.substate = issueSub fork substate state message := by
  obtain ⟨h4, hv, -⟩ := runFrame_ok_dispatch hfork hsize' start within hrun hok
  by_cases hown : callerWord message ≠ ownerOf state message.currentTarget
  · exact (no_ok (fun g hg => spec_issue_notOwner hfork h4 hsize' hsel hv hown hc0 hg)
      (fun _ e h => halted_true_error e h) start within hrun hok).elim
  have hown := not_ne hown
  by_cases hT : ¬ (0 < (wordArg message.data 0).toNat ∧
      (storageAt state message.currentTarget 1).toNat + (wordArg message.data 0).toNat < 2 ^ 256)
  · exact (no_ok (fun g hg => spec_issue_req1 hfork h4 hsize' hsel hv hown hT hc0 hc1 hg)
      (fun _ e h => halted_true_error e h) start within hrun hok).elim
  have hT := Classical.not_not.mp hT
  by_cases hB : ¬ (0 < (wordArg message.data 0).toNat ∧
      (storageAt state message.currentTarget (ownerBal state message.currentTarget)).toNat +
        (wordArg message.data 0).toNat < 2 ^ 256)
  · exact (no_ok (fun g hg => spec_issue_req2 hfork h4 hsize' hsel hv hown hT hB hc0 hc1 hcO hg)
      (fun _ e h => halted_true_error e h) start within hrun hok).elim
  have hB := Classical.not_not.mp hB
  by_cases hgood : ¬(message.isStatic = false ∧ hasAccount state message.currentTarget)
  · exact (Gas.no_ok_stuck (fun g hg => bad_issue hfork (Gas.bad_of_not hgood) h4 hsize' hsel hv
      hown hT hB.2 hc0 hc1 hcO hg) start within hrun hok).elim
  obtain ⟨hstatic, hacc⟩ := Classical.not_not.mp hgood
  obtain ⟨-, -, ho, hg, hst, hss⟩ := ok_exact2
    (fun g h1 h2 => spec_issue hfork hstatic hacc h4 hsize' hsel hv hown hT hB.2 hc0 hc1 hcO
      h1 h2)
    start within hrun hok
  exact ⟨hstatic, hacc, hown, hT.1, hT.2, hB.2, ho, hg, hst, hss⟩

/-- Every successful `redeem(a)` call is the owner's, with `a ≤ _totalSupply` and
`a ≤ balances[owner]`
The conclusion states that the frame is not static and the contract has an account:
otherwise the SSTORE of `_totalSupply` is
`Gas.Stuck` (`bad_redeem`). -/
theorem ok_redeem (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xdb006a75)
    {c0 c1 cO : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hc1 : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget 1 = c1)
    (hcO : coldIn (accessSlot (accessSlot substate message.currentTarget 0) message.currentTarget 1)
      message.currentTarget (ownerBal state message.currentTarget) = cO)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) :
    message.isStatic = false ∧ hasAccount state message.currentTarget ∧
    callerWord message = ownerOf state message.currentTarget ∧
      (wordArg message.data 0).toNat ≤ (storageAt state message.currentTarget 1).toNat ∧
      (wordArg message.data 0).toNat ≤
        (storageAt state message.currentTarget (ownerBal state message.currentTarget)).toNat ∧
      s.output = .empty ∧
      s.gas = gas - (2614 + slotCost c0 + slotCost c1 + slotCost cO +
          redeemCostT fork state message + redeemCostO fork state message) ∧
      s.state = redeemState state message ∧ s.substate = redeemSub fork substate state message := by
  obtain ⟨h4, hv, -⟩ := runFrame_ok_dispatch hfork hsize' start within hrun hok
  by_cases hown : callerWord message ≠ ownerOf state message.currentTarget
  · exact (no_ok (fun g hg => spec_redeem_notOwner hfork h4 hsize' hsel hv hown hc0 hg)
      (fun _ e h => halted_true_error e h) start within hrun hok).elim
  have hown := not_ne hown
  by_cases hT : (storageAt state message.currentTarget 1).toNat < (wordArg message.data 0).toNat
  · exact (no_ok (fun g hg => spec_redeem_req1 hfork h4 hsize' hsel hv hown hT hc0 hc1 hg)
      (fun _ e h => halted_true_error e h) start within hrun hok).elim
  have hT := Nat.le_of_not_lt hT
  by_cases hB : (storageAt state message.currentTarget (ownerBal state message.currentTarget)).toNat <
      (wordArg message.data 0).toNat
  · exact (no_ok (fun g hg => spec_redeem_req2 hfork h4 hsize' hsel hv hown hT hB hc0 hc1 hcO hg)
      (fun _ e h => halted_true_error e h) start within hrun hok).elim
  have hB := Nat.le_of_not_lt hB
  by_cases hgood : ¬(message.isStatic = false ∧ hasAccount state message.currentTarget)
  · exact (Gas.no_ok_stuck (fun g hg => bad_redeem hfork (Gas.bad_of_not hgood) h4 hsize' hsel hv
      hown hT hB hc0 hc1 hcO hg) start within hrun hok).elim
  obtain ⟨hstatic, hacc⟩ := Classical.not_not.mp hgood
  obtain ⟨-, -, ho, hg, hst, hss⟩ := ok_exact2
    (fun g h1 h2 => spec_redeem hfork hstatic hacc h4 hsize' hsel hv hown hT hB hc0 hc1 hcO
      h1 h2)
    start within hrun hok
  exact ⟨hstatic, hacc, hown, hT, hB, ho, hg, hst, hss⟩

/-- Every successful `setParams(b, m)` call is the owner's, with `b < 20`, `m < 50` and no
overflow of `m * 10^d`
The conclusion states that the frame is not static and the contract has an account:
otherwise the SSTORE of slot 3 is `Gas.Stuck`
(`bad_setParams`). -/
theorem ok_setParams (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xc0324c77)
    {c0 c3 c9 c4 : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hc3 : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget 3 = c3)
    (hc9 : coldIn (accessSlot (accessSlot substate message.currentTarget 0) message.currentTarget 3)
      message.currentTarget 9 = c9)
    (hc4 : coldIn (accessSlot (accessSlot (accessSlot substate message.currentTarget 0)
      message.currentTarget 3) message.currentTarget 9) message.currentTarget 4 = c4)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) :
    message.isStatic = false ∧ hasAccount state message.currentTarget ∧
    callerWord message = ownerOf state message.currentTarget ∧
      (wordArg message.data 0).toNat < 20 ∧ (wordArg message.data 1).toNat < 50 ∧
      (wordArg message.data 1).toNat *
        (exp (0x0a : U256) (storageAt state message.currentTarget 9)).toNat < 2 ^ 256 ∧
      s.output = .empty ∧
      s.gas = gas - (2425 + paramsCost fork state message c0 c3 c9 c4) ∧
      s.state = paramsState state message ∧ s.substate = paramsSub fork substate state message := by
  obtain ⟨h4, hv, -⟩ := runFrame_ok_dispatch hfork hsize' start within hrun hok
  by_cases hown : callerWord message ≠ ownerOf state message.currentTarget
  · exact (no_ok (fun g hg => SetParamsSpec.spec_notOwner hfork h4 hsize' hsel hv hown hc0 hg)
      (fun _ e h => halted_true_error e h) start within hrun hok).elim
  have hown := not_ne hown
  by_cases hb : 20 ≤ (wordArg message.data 0).toNat
  · exact (no_ok (fun g hg => spec_bpHigh hfork h4 hsize' hsel hv hown hb hc0 hg)
      (fun _ e h => halted_true_error e h) start within hrun hok).elim
  have hb := Nat.lt_of_not_le hb
  by_cases hm : 50 ≤ (wordArg message.data 1).toNat
  · exact (no_ok (fun g hg => spec_feeHigh hfork h4 hsize' hsel hv hown hb hm hc0 hg)
      (fun _ e h => halted_true_error e h) start within hrun hok).elim
  have hm := Nat.lt_of_not_le hm
  by_cases hgood : ¬(message.isStatic = false ∧ hasAccount state message.currentTarget)
  · exact (Gas.no_ok_stuck (fun g hg => bad_setParams hfork (Gas.bad_of_not hgood) h4 hsize' hsel
      hv hown hb hm hc0 hg) start within hrun hok).elim
  obtain ⟨hstatic, hacc⟩ := Classical.not_not.mp hgood
  by_cases hov : 2 ^ 256 ≤ (wordArg message.data 1).toNat *
      (exp (0x0a : U256) (storageAt state message.currentTarget 9)).toNat
  · exact (no_ok (fun g hg => SetParamsSpec.spec_mulOv hfork hstatic hacc h4 hsize' hsel hv
      hown hb hm hov hc0 hc3 hc9 hg) (fun _ e h => faulted_error e h) start within hrun hok).elim
  have hov := Nat.lt_of_not_le hov
  obtain ⟨-, -, ho, hg, hst, hss⟩ := ok_exact2
    (fun g h1 h2 => spec_setParams hfork hstatic hacc h4 hsize' hsel hv hown hb hm hov hc0
      hc3 hc9 hc4 h1 h2)
    start within hrun hok
  exact ⟨hstatic, hacc, hown, hb, hm, hov, ho, hg, hst, hss⟩

/-- Every successful `deprecate(a)` call is the owner's
The conclusion states that the frame is not static and the contract has an account:
otherwise the SSTORE of slot 10 is `Gas.Stuck`
(`bad_deprecate`). -/
theorem ok_deprecate (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x0753c30c)
    {c0 c10 : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hc10 : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget 10 = c10)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) :
    message.isStatic = false ∧ hasAccount state message.currentTarget ∧
    callerWord message = ownerOf state message.currentTarget ∧ s.output = .empty ∧
      s.gas = gas - (1628 + slotCost c0 + slotCost c10 + depCost fork state message) ∧
      s.state = depState state message ∧ s.substate = depSub fork substate state message := by
  obtain ⟨h4, hv, -⟩ := runFrame_ok_dispatch hfork hsize' start within hrun hok
  by_cases hown : callerWord message ≠ ownerOf state message.currentTarget
  · exact (no_ok (fun g hg => spec_deprecate_notOwner hfork h4 hsize' hsel hv hown hc0 hg)
      (fun _ e h => halted_true_error e h) start within hrun hok).elim
  have hown := not_ne hown
  by_cases hgood : ¬(message.isStatic = false ∧ hasAccount state message.currentTarget)
  · exact (Gas.no_ok_stuck (fun g hg => bad_deprecate hfork (Gas.bad_of_not hgood) h4 hsize' hsel
      hv hown hc0 hc10 hg) start within hrun hok).elim
  obtain ⟨hstatic, hacc⟩ := Classical.not_not.mp hgood
  obtain ⟨-, -, ho, hg, hst, hss⟩ := ok_exact2
    (fun g h1 h2 => spec_deprecate hfork hstatic hacc h4 hsize' hsel hv hown hc0 hc10 h1 h2)
    start within hrun hok
  exact ⟨hstatic, hacc, hown, ho, hg, hst, hss⟩

/-- Every successful `transferOwnership(a)` call is the owner's: with `a = 0` nothing is written,
otherwise the owner becomes `a`
For `a ≠ 0` the conclusion states that the frame is not static and the contract has an account:
otherwise the SSTORE of slot 0 is `Gas.Stuck` (`bad_transferOwnership`). -/
theorem ok_transferOwnership (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xf2fde38b)
    {c0 : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) :
    callerWord message = ownerOf state message.currentTarget ∧ s.output = .empty ∧
      ((addrArg message.data 0 = 0 ∧ s.gas = gas - (947 + slotCost c0) ∧
        s.state = readSlot state message.currentTarget 0 ∧
        s.substate = accessSlot substate message.currentTarget 0) ∨
      (addrArg message.data 0 ≠ 0 ∧
        message.isStatic = false ∧ hasAccount state message.currentTarget ∧
        s.gas = gas - (1114 + slotCost c0 + ownCost fork state message) ∧
        s.state = writeSlot state message.currentTarget 0
          (withAddr (storageAt state message.currentTarget 0) (addrArg message.data 0)) ∧
        s.substate = storeSub fork substate message.currentTarget 0
          (originalAt state message.currentTarget 0) (storageAt state message.currentTarget 0)
          (withAddr (storageAt state message.currentTarget 0) (addrArg message.data 0)))) := by
  obtain ⟨h4, hv, -⟩ := runFrame_ok_dispatch hfork hsize' start within hrun hok
  by_cases hown : callerWord message ≠ ownerOf state message.currentTarget
  · exact (no_ok (fun g hg => spec_transferOwnership_notOwner hfork h4 hsize' hsel hv hown hc0 hg)
      (fun _ e h => halted_true_error e h) start within hrun hok).elim
  have hown := not_ne hown
  by_cases hz : addrArg message.data 0 = 0
  · obtain ⟨-, -, ho, hg, hst, hss⟩ := ok_exact (Nat.le_refl _)
      (fun g hg => spec_transferOwnership_zero hfork h4 hsize' hsel hv hown hz hc0 hg)
      start within hrun hok
    exact ⟨hown, ho, .inl ⟨hz, hg, hst, hss⟩⟩
  by_cases hgood : ¬(message.isStatic = false ∧ hasAccount state message.currentTarget)
  · exact (Gas.no_ok_stuck (fun g hg => bad_transferOwnership hfork (Gas.bad_of_not hgood) h4
      hsize' hsel hv hown hz hc0 hg) start within hrun hok).elim
  obtain ⟨hstatic, hacc⟩ := Classical.not_not.mp hgood
  obtain ⟨-, -, ho, hg, hst, hss⟩ := ok_exact2
    (fun g h1 h2 => spec_transferOwnership hfork hstatic hacc h4 hsize' hsel hv hown hz hc0
      h1 h2)
    start within hrun hok
  exact ⟨hown, ho, .inr ⟨hz, hstatic, hacc, hg, hst, hss⟩⟩

/-- Every successful `destroyBlackFunds(a)` call, not deprecated, is the owner's, with `a`
blacklisted
The conclusion states that the frame is not static and the contract has an account:
otherwise the SSTORE of `balances[a]` is `Gas.Stuck`
(`DestroySpec.bad`). -/
theorem ok_destroyBlackFunds (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xf3bdc228)
    (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    {c0 cL c10 cB c1 : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hcL : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget
      (listSlot (addrArg message.data 0)) = cL)
    (hc10 : coldIn (preSub substate message) message.currentTarget 10 = c10)
    (hcB : coldIn (accessSlot (preSub substate message) message.currentTarget 10)
      message.currentTarget (balSlot message) = cB)
    (hc1 : coldIn (readSub substate message) message.currentTarget 1 = c1)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) :
    message.isStatic = false ∧ hasAccount state message.currentTarget ∧
    callerWord message = ownerOf state message.currentTarget ∧
      (storageAt state message.currentTarget (listSlot (addrArg message.data 0))).toNat % 256 ≠ 0 ∧
      s.output = .empty ∧
      s.gas = gas - (2865 + slotCost c0 + slotCost cL + slotCost c10 + slotCost cB +
          slotCost c1 + costB fork state message + costT fork state message) ∧
      s.state = destroyState state message ∧ s.substate = destroySub fork substate state message := by
  obtain ⟨h4, hv, -⟩ := runFrame_ok_dispatch hfork hsize' start within hrun hok
  by_cases hown : callerWord message ≠ ownerOf state message.currentTarget
  · exact (no_ok (fun g hg => Destroy.spec_notOwner hfork h4 hsize' hsel hv hown hc0 hg)
      (fun _ e h => halted_true_error e h) start within hrun hok).elim
  have hown := not_ne hown
  by_cases hl : (storageAt state message.currentTarget (listSlot (addrArg message.data 0))).toNat %
      256 = 0
  · exact (no_ok (fun g hg => Destroy.spec_notListed hfork h4 hsize' hsel hv hown hl hc0 hcL hg)
      (fun _ e h => halted_true_error e h) start within hrun hok).elim
  by_cases hgood : ¬(message.isStatic = false ∧ hasAccount state message.currentTarget)
  · exact (Gas.no_ok_stuck (fun g hg => DestroySpec.bad hfork (Gas.bad_of_not hgood) h4 hsize'
      hsel hv hown hl hdep hc0 hcL hc10 hcB hg) start within hrun hok).elim
  obtain ⟨hstatic, hacc⟩ := Classical.not_not.mp hgood
  obtain ⟨-, -, ho, hg, hst, hss⟩ := ok_exact3
    (fun g h1 h2 h3 => DestroySpec.spec hfork hstatic hacc h4 hsize' hsel hv hown hl hdep hc0
      hcL hc10 hcB hc1 h1 h2 h3)
    start within hrun hok
  exact ⟨hstatic, hacc, hown, hl, ho, hg, hst, hss⟩

end UsdtVerify.Complete
