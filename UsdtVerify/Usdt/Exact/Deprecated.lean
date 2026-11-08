import UsdtVerify.Usdt.Exact.Getters
import UsdtVerify.Usdt.Complete.Deprecated.TotalSupply
import UsdtVerify.Usdt.Complete.Deprecated.BalanceOf
import UsdtVerify.Usdt.Complete.Deprecated.Allowance
import UsdtVerify.Usdt.Complete.Deprecated.Transfer
import UsdtVerify.Usdt.Complete.Deprecated.Destroy

/-!
# Exact success conditions of the deprecated paths

From Berlin, a fresh frame of `CODE` at pc 0 with call data below `2^256` bytes and the selector
of the function, byte 20 of slot 10 not 0 (`hdep`), the code `c` of the upgraded address found
in the state (`hcode`; `c.size < 2^256`, `hszl`, for the theorems that give success), the route
`r` of the CALL (`hroute`), any gas bound and any message runner `runChild`.

- `*_dep_ok_iff`: with the gas of the success path up to the CALL and after it (`hg`, `htail`),
  and a runner that never fails (`NoFail`) and ends each message forwarded along the route with
  no error exactly when `A` holds (`hans`), the run ends with no error if and only if the checks
  before the forward hold (`ForwardOk`, or `TransferDepGuard`, `ApproveDepGuard`,
  `TransferFromDepGuard`) and `A` holds. For the six forwards other than destroyBlackFunds it is
  derived from `*_dep_ok_iff_fails` (with `htail`, enough gas is left after the CALL).
- `*_dep_low`: with less gas than the path up to the CALL and the CALL's access (`hg`), no run
  ends with no error, whatever the runner.
- `*_dep_ok_iff_gas` (round 26, the six forwards other than destroyBlackFunds): with `hg` only
  (no `htail`), a runner that never fails, and `hans` saying that a forwarded message ends with
  no error and with enough gas left (the gas the CALL keeps plus the gas left in the ended frame
  at least the gas of the code after the CALL: 121, 126, 128, 51, 53, 53) exactly when `A` holds,
  the run ends with no error if and only if the checks and `A` hold. Together with `*_dep_low`
  this covers every gas.
- `*_dep_ok_or_fails` (round 26, the same six): with `hg` and `htail`, for a runner that may fail with errors that abort
  the run (in place of `NoFail`), success gives the checks and `A`, and the checks and `A` give
  success or a failure of the runner on some message.
- `destroyBlackFunds_dep_ok_iff_gas` (round 26): the same with `hg` only, for destroyBlackFunds,
  whose code after the CALL writes `balances[a]` and slot 1: `hans` makes `A` equivalent to the
  forwarded message ending with no error, in a state with an account of the contract, and with
  enough gas left for the code after the CALL, the larger of its cost (`tailCost`) and its
  stipend bound (`tailStip`: more than 2300 gas left at the second SSTORE). Both are computed over
  the state and substate after the call: the coldness and the original and current words of
  `balances[a]` and slot 1 there. With `destroyBlackFunds_dep_low` this covers every gas, under a
  runner that never fails.
- `*_dep_ok_iff_fails` (round 26, the seven paths): `*_dep_ok_iff_gas` for a runner that may fail
  with any error, in place of `NoFail`: with `hg` only and the same `hans`, and `hfail` (a failure
  of the runner on a message forwarded along the route excludes `A`), the run ends with no error if
  and only if the checks and `A` hold. The `*_dep_ok_iff_gas` theorems are derived from them
  (under `NoFail`, `hfail` holds). The one-sided `*_dep_ok_or_fails` (with `htail`) are kept.
- Round 30 (docs/AUDIT.md, finding 3): in `*_dep_ok_iff`, `*_dep_ok_iff_gas` and
  `*_dep_ok_iff_fails` (the seven paths), `hans` is asked only of the message the CALL sends
  (`SendsVia`) with the gas it gives (`callGas…`), from the caller frame at the CALL, whose
  state and substate are given (`CallFrom`, `atCallState`, `atCallSub`). Before, it was asked of
  every gas, so no runner whose outcome depends on the gas (EthLib's `processRunner` with any
  code that can run out of gas) could meet the `_gas` and `_fails` forms. Now `A` can be a
  condition on that gas. `destroyBlackFunds_dep_ok_iff` is derived from
  `destroyBlackFunds_dep_ok_iff_fails` (`tail_le_max`). `*_dep_ok_or_fails` keep the old `hans`.
  Sanity/ProcessExact.lean instantiates the seven paths with `processRunner` and STOP.
- destroyBlackFunds: `A` is the answer "the forwarded message ends with no error and the contract
  has an account in its end state", and the checks are `DestroyDepGuard`.
-/

namespace UsdtVerify.Exact

open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open UsdtVerify.Gas
open Complete Deprecated DeprecatedBalance DeprecatedAllowance DeprecatedTransfer
open DeprecatedTransferFrom DeprecatedDestroy Transfer TransferFrom Owner BlackList DestroySpec

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate} {bound : Nat} {runChild : MessageRunner fork Nat bound}
  {evm : Evm fork Nat} {gas : Nat}

theorem size_pos_of {n : Nat} (h : BitVec.ofNat 256 n ≠ 0) : 0 < n :=
  Nat.pos_of_ne_zero fun h0 => h (by rw [h0]; rfl)

theorem code_eq {st : State.TransactionState} {a : EthLib.Base.Address} {c c' : ByteArray}
    (h : st.getCode (st.getAccount a).codeHash = .ok c)
    (h' : st.getCode (st.getAccount a).codeHash = .ok c') : c' = c := by
  rw [h] at h'; cases h'; rfl

/-! ## totalSupply -/

section
variable (hfork : .berlin ≤ fork) (hsize' : message.data.size < 2 ^ 256)
  (hsel : selector message.data = 0x18160ddd)
  (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0) {c : ByteArray}
  (hcode : state.getCode (state.getAccount (upAddr state message)).codeHash = .ok c)
  {r : Route} (hroute : Routes fork state c r) {c10 cU : Bool}
  (hc10 : coldIn substate message.currentTarget 10 = c10)
  (hcU : decide (upAddr state message ∉ substate.accessedAddresses) = cU)
  (start : At CODE message 0 [] .empty gas state substate evm)
  (within : GasMeter.gasHeld evm.gas ≤ bound)
include hfork hsize' hsel hdep hcode hroute hc10 hcU start

/-- `totalSupply_dep_ok_iff_gas` for a runner that may fail, with any error (round 26): with `hg` only, the
run succeeds exactly when the checks hold and `A` holds, where `A` is equivalent (`hans`) to the
forwarded call ending with no error and enough gas left for the code after the CALL, and a failure
of the runner on a forwarded message excludes `A` (`hfail`). -/
theorem totalSupply_dep_ok_iff_fails (hszl : c.size < 2 ^ 256)
    (hg : preCost fork c10 cU + 100 + callR substate state message r ≤ gas)
    {A : Prop}
    (hans : ∀ caller msg lt child, runChild caller msg lt = .ok child →
      SendsVia message (upAddr state message) c r SEL_TS msg →
      CallFrom (callGas fork gas c10 cU (callR substate state message r)).subCall
        (atCallState (callState state message) (upAddr state message) r message.currentTarget)
        (atCallSub (callSub substate state message) (upAddr state message) r) caller msg →
      (child.1.error = none ∧ 121 ≤ gas - preCost fork c10 cU -
        (callGas fork gas c10 cU (callR substate state message r)).cost + child.1.gas ↔ A))
    (hfail : ∀ caller msg lt e, runChild caller msg lt = .error e →
      SendsVia message (upAddr state message) c r SEL_TS msg → ¬ A) :
    RunsOk fork bound runChild evm within ↔ ForwardOk message c ∧ A := by
  refine fwd_ok_iff_fails
    (Cl := CallFrom (callGas fork gas c10 cU (callR substate state message r)).subCall
      (atCallState (callState state message) (upAddr state message) r message.currentTarget)
      (atCallSub (callSub substate state message) (upAddr state message) r))
    (Q := fun _ child => child.error = none ∧ 121 ≤ gas - preCost fork c10 cU -
      (callGas fork gas c10 cU (callR substate state message r)).cost + child.gas)
    (fun ⟨⟨h4, hv⟩, hsz, hdepth⟩ =>
    (spec_dep_g hfork h4 hsize' hsel hv hdep hcode hsz hszl hroute hdepth hc10 hcU hg
      fun _ _ _ hcal hfwd hcl => (hcal hfwd hcl).2).consequence (fun _ h => h)
      fun e ⟨_, _, _, hcal, hfwd, hmg, hcs, hcss, hok, _⟩ =>
        halted_false_ok e (hok (hcal hfwd ⟨hmg, hcs, hcss⟩).1))
    within ?_ hans hfail start
  intro s hs hok
  obtain ⟨h4, hv, -⟩ := runFrame_ok_dispatch hfork hsize' start within hs hok
  obtain ⟨c', r', hcode', hroute', hw, -, hdepth, caller, msg, lt, child, hch, he, hfwd, hmg, hcs, hcss,
    hgas, -⟩ := dep_totalSupply_complete hfork hsize' hsel hdep start within hs hok
  obtain rfl := code_eq hcode hcode'
  obtain rfl := routes_unique hroute' hroute
  subst hc10 hcU
  exact ⟨⟨⟨h4, hv⟩, size_pos_of hw, hdepth⟩, caller, msg, lt, child, hch, ⟨he, hgas⟩, hfwd, hmg, hcs, hcss⟩

/-- `totalSupply()` when deprecated succeeds exactly when `ForwardOk` holds and the forwarded
call ends with no error (`A`, by `hans`). -/
theorem totalSupply_dep_ok_iff (hszl : c.size < 2 ^ 256)
    (hg : preCost fork c10 cU + 100 + callR substate state message r ≤ gas)
    (htail : 121 ≤ gas - preCost fork c10 cU -
      (callGas fork gas c10 cU (callR substate state message r)).cost)
    {A : Prop}
    (hans : ∀ caller msg lt child, runChild caller msg lt = .ok child →
      SendsVia message (upAddr state message) c r SEL_TS msg →
      CallFrom (callGas fork gas c10 cU (callR substate state message r)).subCall
        (atCallState (callState state message) (upAddr state message) r message.currentTarget)
        (atCallSub (callSub substate state message) (upAddr state message) r) caller msg →
        (child.1.error = none ↔ A))
    (hnf : NoFailOn runChild (SendsVia message (upAddr state message) c r SEL_TS)) :
    RunsOk fork bound runChild evm within ↔ ForwardOk message c ∧ A :=
  totalSupply_dep_ok_iff_fails hfork hsize' hsel hdep hcode hroute hc10 hcU start within hszl hg
    (fun caller msg lt child hch hfwd hcl =>
      ⟨fun h => (hans caller msg lt child hch hfwd hcl).1 h.1,
      fun hA => ⟨(hans caller msg lt child hch hfwd hcl).2 hA, Nat.le_trans htail (Nat.le_add_right _ _)⟩⟩)
    fun _ _ _ e h hs => absurd h (hnf _ _ _ e hs)

/-- `totalSupply()` when deprecated, with the gas of the path up to the CALL (`hg`) and no bound
on the gas after it: the run succeeds exactly when `ForwardOk` holds and `A` holds, where `A` is
equivalent (`hans`) to the forwarded call ending with no error and leaving, with the gas the CALL
keeps, at least 121 gas for the code after the CALL. -/
theorem totalSupply_dep_ok_iff_gas (hszl : c.size < 2 ^ 256)
    (hg : preCost fork c10 cU + 100 + callR substate state message r ≤ gas)
    {A : Prop}
    (hans : ∀ caller msg lt child, runChild caller msg lt = .ok child →
      SendsVia message (upAddr state message) c r SEL_TS msg →
      CallFrom (callGas fork gas c10 cU (callR substate state message r)).subCall
        (atCallState (callState state message) (upAddr state message) r message.currentTarget)
        (atCallSub (callSub substate state message) (upAddr state message) r) caller msg →
      (child.1.error = none ∧ 121 ≤ gas - preCost fork c10 cU -
        (callGas fork gas c10 cU (callR substate state message r)).cost + child.1.gas ↔ A))
    (hnf : NoFailOn runChild (SendsVia message (upAddr state message) c r SEL_TS)) :
    RunsOk fork bound runChild evm within ↔ ForwardOk message c ∧ A :=
  totalSupply_dep_ok_iff_fails hfork hsize' hsel hdep hcode hroute hc10 hcU start within hszl hg hans
    fun _ _ _ e h hs => absurd h (hnf _ _ _ e hs)

/-- `totalSupply_dep_ok_iff` for a runner that may fail, with errors that abort the run: success gives
the checks and `A`; the checks and `A` give success or a failure of the runner on some
message. -/
theorem totalSupply_dep_ok_or_fails (hszl : c.size < 2 ^ 256)
    (hg : preCost fork c10 cU + 100 + callR substate state message r ≤ gas)
    (htail : 121 ≤ gas - preCost fork c10 cU -
      (callGas fork gas c10 cU (callR substate state message r)).cost)
    {A : Prop}
    (hans : ∀ caller msg lt child, runChild caller msg lt = .ok child →
      SendsVia message (upAddr state message) c r SEL_TS msg → (child.1.error = none ↔ A))
    (hab : ∀ caller msg lt e, runChild caller msg lt = .error e → e.aborts = true) :
    (RunsOk fork bound runChild evm within → ForwardOk message c ∧ A) ∧
      (ForwardOk message c ∧ A → RunsOk fork bound runChild evm within ∨
        ∃ caller msg lt e, runChild caller msg lt = .error e) := by
  refine fwd_ok_or_fails (fun ⟨⟨h4, hv⟩, hsz, hdepth⟩ =>
    (spec_dep hfork h4 hsize' hsel hv hdep hcode hsz hszl hroute hdepth hc10 hcU hg
      htail).consequence (fun _ h => h)
      fun e ⟨_, _, _, hcal, hfwd, _, _, _, hok, _⟩ hA => halted_false_ok e (hok ((hcal hfwd).2 hA)))
    within ?_ hans hab start
  intro s hs hok
  obtain ⟨h4, hv, -⟩ := runFrame_ok_dispatch hfork hsize' start within hs hok
  obtain ⟨c', r', hcode', hroute', hw, -, hdepth, caller, msg, lt, child, hch, he, hfwd, -⟩ :=
    dep_totalSupply_complete hfork hsize' hsel hdep start within hs hok
  obtain rfl := code_eq hcode hcode'
  obtain rfl := routes_unique hroute' hroute
  exact ⟨⟨⟨h4, hv⟩, size_pos_of hw, hdepth⟩, caller, msg, lt, child, hch, he, hfwd⟩

theorem totalSupply_dep_low
    (hg : gas < preCost fork c10 cU + 100 + callR substate state message r) :
    ¬ RunsOk fork bound runChild evm within := by
  rintro ⟨s, hs, hok⟩
  obtain ⟨c', r', hcode', hroute', -, hgc, -⟩ :=
    dep_totalSupply_complete hfork hsize' hsel hdep start within hs hok
  obtain rfl := code_eq hcode hcode'
  obtain rfl := routes_unique hroute' hroute
  subst hc10 hcU
  exact absurd hgc (Nat.not_le.mpr hg)

end

/-! ## balanceOf -/

section
variable (hfork : .berlin ≤ fork) (hsize' : message.data.size < 2 ^ 256)
  (hsel : selector message.data = 0x70a08231)
  (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0) {c : ByteArray}
  (hcode : state.getCode (state.getAccount (upAddr state message)).codeHash = .ok c)
  {r : Route} (hroute : Routes fork state c r) {c10 cU : Bool}
  (hc10 : coldIn substate message.currentTarget 10 = c10)
  (hcU : decide (upAddr state message ∉ substate.accessedAddresses) = cU)
  (start : At CODE message 0 [] .empty gas state substate evm)
  (within : GasMeter.gasHeld evm.gas ≤ bound)
include hfork hsize' hsel hdep hcode hroute hc10 hcU start

/-- `balanceOf_dep_ok_iff_gas` for a runner that may fail, with any error (round 26): with `hg` only, the
run succeeds exactly when the checks hold and `A` holds, where `A` is equivalent (`hans`) to the
forwarded call ending with no error and enough gas left for the code after the CALL, and a failure
of the runner on a forwarded message excludes `A` (`hfail`). -/
theorem balanceOf_dep_ok_iff_fails (hszl : c.size < 2 ^ 256)
    (hg : preCostB fork c10 cU + 100 + callR substate state message r ≤ gas)
    {A : Prop}
    (hans : ∀ caller msg lt child, runChild caller msg lt = .ok child →
      SendsVia message (upAddr state message) c r (dataB message) msg →
      CallFrom (callGasB fork gas c10 cU (callR substate state message r)).subCall
        (atCallState (callState state message) (upAddr state message) r message.currentTarget)
        (atCallSub (callSub substate state message) (upAddr state message) r) caller msg →
        (child.1.error = none ∧ 126 ≤ gas - preCostB fork c10 cU -
      (callGasB fork gas c10 cU (callR substate state message r)).cost + child.1.gas ↔ A))
    (hfail : ∀ caller msg lt e, runChild caller msg lt = .error e →
      SendsVia message (upAddr state message) c r (dataB message) msg → ¬ A) :
    RunsOk fork bound runChild evm within ↔ ForwardOk message c ∧ A := by
  refine fwd_ok_iff_fails
    (Cl := CallFrom (callGasB fork gas c10 cU (callR substate state message r)).subCall
      (atCallState (callState state message) (upAddr state message) r message.currentTarget)
      (atCallSub (callSub substate state message) (upAddr state message) r))
    (Q := fun _ child => child.error = none ∧ 126 ≤ gas - preCostB fork c10 cU -
      (callGasB fork gas c10 cU (callR substate state message r)).cost +
      child.gas)
    (fun ⟨⟨h4, hv⟩, hsz, hdepth⟩ =>
    (spec_depB_g hfork h4 hsize' hsel hv hdep hcode hsz hszl hroute hdepth hc10 hcU hg
      fun _ _ _ hcal hfwd hcl => (hcal hfwd hcl).2).consequence (fun _ h => h)
      fun e ⟨_, _, _, hcal, hfwd, hmg, hcs, hcss, hok, _⟩ =>
        halted_false_ok e (hok (hcal hfwd ⟨hmg, hcs, hcss⟩).1))
    within ?_ hans hfail start
  intro s hs hok
  obtain ⟨h4, hv, -⟩ := runFrame_ok_dispatch hfork hsize' start within hs hok
  obtain ⟨c', r', hcode', hroute', hw, -, hdepth, caller, msg, lt, child, hch, he, hfwd, hmg, hcs, hcss, hgas, -⟩ :=
    dep_balanceOf_complete hfork hsize' hsel hdep start within hs hok
  obtain rfl := code_eq hcode hcode'
  obtain rfl := routes_unique hroute' hroute
  subst hc10 hcU
  exact ⟨⟨⟨h4, hv⟩, size_pos_of hw, hdepth⟩, caller, msg, lt, child, hch, ⟨he, hgas⟩, hfwd, hmg, hcs, hcss⟩

/-- `balanceOf(a)` when deprecated succeeds exactly when `ForwardOk` holds and the forwarded
call ends with no error (`A`, by `hans`). -/
theorem balanceOf_dep_ok_iff (hszl : c.size < 2 ^ 256)
    (hg : preCostB fork c10 cU + 100 + callR substate state message r ≤ gas)
    (htail : 126 ≤ gas - preCostB fork c10 cU -
      (callGasB fork gas c10 cU (callR substate state message r)).cost)
    {A : Prop}
    (hans : ∀ caller msg lt child, runChild caller msg lt = .ok child →
      SendsVia message (upAddr state message) c r (dataB message) msg →
      CallFrom (callGasB fork gas c10 cU (callR substate state message r)).subCall
        (atCallState (callState state message) (upAddr state message) r message.currentTarget)
        (atCallSub (callSub substate state message) (upAddr state message) r) caller msg →
        (child.1.error = none ↔ A))
    (hnf : NoFailOn runChild (SendsVia message (upAddr state message) c r (dataB message))) :
    RunsOk fork bound runChild evm within ↔ ForwardOk message c ∧ A :=
  balanceOf_dep_ok_iff_fails hfork hsize' hsel hdep hcode hroute hc10 hcU start within hszl hg
    (fun caller msg lt child hch hfwd hcl =>
      ⟨fun h => (hans caller msg lt child hch hfwd hcl).1 h.1,
      fun hA => ⟨(hans caller msg lt child hch hfwd hcl).2 hA, Nat.le_trans htail (Nat.le_add_right _ _)⟩⟩)
    fun _ _ _ e h hs => absurd h (hnf _ _ _ e hs)

/-- `balanceOf(a)` when deprecated, with the gas of the path up to the CALL (`hg`) and no bound on
the gas after it: the run succeeds exactly when `ForwardOk` holds and `A` holds, where `A` is
equivalent (`hans`) to the forwarded call ending with no error and leaving, with the gas the CALL
keeps, at least 126 gas for the code after the CALL. -/
theorem balanceOf_dep_ok_iff_gas (hszl : c.size < 2 ^ 256)
    (hg : preCostB fork c10 cU + 100 + callR substate state message r ≤ gas)
    {A : Prop}
    (hans : ∀ caller msg lt child, runChild caller msg lt = .ok child →
      SendsVia message (upAddr state message) c r (dataB message) msg →
      CallFrom (callGasB fork gas c10 cU (callR substate state message r)).subCall
        (atCallState (callState state message) (upAddr state message) r message.currentTarget)
        (atCallSub (callSub substate state message) (upAddr state message) r) caller msg →
        (child.1.error = none ∧ 126 ≤ gas - preCostB fork c10 cU -
      (callGasB fork gas c10 cU (callR substate state message r)).cost + child.1.gas ↔ A))
    (hnf : NoFailOn runChild (SendsVia message (upAddr state message) c r (dataB message))) :
    RunsOk fork bound runChild evm within ↔ ForwardOk message c ∧ A :=
  balanceOf_dep_ok_iff_fails hfork hsize' hsel hdep hcode hroute hc10 hcU start within hszl hg hans
    fun _ _ _ e h hs => absurd h (hnf _ _ _ e hs)

/-- `balanceOf_dep_ok_iff` for a runner that may fail, with errors that abort the run: success gives
the checks and `A`; the checks and `A` give success or a failure of the runner on some
message. -/
theorem balanceOf_dep_ok_or_fails (hszl : c.size < 2 ^ 256)
    (hg : preCostB fork c10 cU + 100 + callR substate state message r ≤ gas)
    (htail : 126 ≤ gas - preCostB fork c10 cU -
      (callGasB fork gas c10 cU (callR substate state message r)).cost)
    {A : Prop}
    (hans : ∀ caller msg lt child, runChild caller msg lt = .ok child →
      SendsVia message (upAddr state message) c r (dataB message) msg →
        (child.1.error = none ↔ A))
    (hab : ∀ caller msg lt e, runChild caller msg lt = .error e → e.aborts = true) :
    (RunsOk fork bound runChild evm within → ForwardOk message c ∧ A) ∧
      (ForwardOk message c ∧ A → RunsOk fork bound runChild evm within ∨
        ∃ caller msg lt e, runChild caller msg lt = .error e) := by
  refine fwd_ok_or_fails (fun ⟨⟨h4, hv⟩, hsz, hdepth⟩ =>
    (spec_depB hfork h4 hsize' hsel hv hdep hcode hsz hszl hroute hdepth hc10 hcU hg
      htail).consequence (fun _ h => h)
      fun e ⟨_, _, _, hcal, hfwd, _, _, _, hok, _⟩ hA => halted_false_ok e (hok ((hcal hfwd).2 hA)))
    within ?_ hans hab start
  intro s hs hok
  obtain ⟨h4, hv, -⟩ := runFrame_ok_dispatch hfork hsize' start within hs hok
  obtain ⟨c', r', hcode', hroute', hw, -, hdepth, caller, msg, lt, child, hch, he, hfwd, -⟩ :=
    dep_balanceOf_complete hfork hsize' hsel hdep start within hs hok
  obtain rfl := code_eq hcode hcode'
  obtain rfl := routes_unique hroute' hroute
  exact ⟨⟨⟨h4, hv⟩, size_pos_of hw, hdepth⟩, caller, msg, lt, child, hch, he, hfwd⟩

theorem balanceOf_dep_low
    (hg : gas < preCostB fork c10 cU + 100 + callR substate state message r) :
    ¬ RunsOk fork bound runChild evm within := by
  rintro ⟨s, hs, hok⟩
  obtain ⟨c', r', hcode', hroute', -, hgc, -⟩ :=
    dep_balanceOf_complete hfork hsize' hsel hdep start within hs hok
  obtain rfl := code_eq hcode hcode'
  obtain rfl := routes_unique hroute' hroute
  subst hc10 hcU
  exact absurd hgc (Nat.not_le.mpr hg)

end

/-! ## allowance -/

section
variable (hfork : .berlin ≤ fork) (hsize' : message.data.size < 2 ^ 256)
  (hsel : selector message.data = 0xdd62ed3e)
  (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0) {c : ByteArray}
  (hcode : state.getCode (state.getAccount (upAddr state message)).codeHash = .ok c)
  {r : Route} (hroute : Routes fork state c r) {c10 cU : Bool}
  (hc10 : coldIn substate message.currentTarget 10 = c10)
  (hcU : decide (upAddr state message ∉ substate.accessedAddresses) = cU)
  (start : At CODE message 0 [] .empty gas state substate evm)
  (within : GasMeter.gasHeld evm.gas ≤ bound)
include hfork hsize' hsel hdep hcode hroute hc10 hcU start

/-- `allowance_dep_ok_iff_gas` for a runner that may fail, with any error (round 26): with `hg` only, the
run succeeds exactly when the checks hold and `A` holds, where `A` is equivalent (`hans`) to the
forwarded call ending with no error and enough gas left for the code after the CALL, and a failure
of the runner on a forwarded message excludes `A` (`hfail`). -/
theorem allowance_dep_ok_iff_fails (hszl : c.size < 2 ^ 256)
    (hg : preCostAl fork c10 cU + 100 + callR substate state message r ≤ gas)
    {A : Prop}
    (hans : ∀ caller msg lt child, runChild caller msg lt = .ok child →
      SendsVia message (upAddr state message) c r (dataAl message) msg →
      CallFrom (callGasAl fork gas c10 cU (callR substate state message r)).subCall
        (atCallState (callState state message) (upAddr state message) r message.currentTarget)
        (atCallSub (callSub substate state message) (upAddr state message) r) caller msg →
        (child.1.error = none ∧ 128 ≤ gas - preCostAl fork c10 cU -
      (callGasAl fork gas c10 cU (callR substate state message r)).cost + child.1.gas ↔ A))
    (hfail : ∀ caller msg lt e, runChild caller msg lt = .error e →
      SendsVia message (upAddr state message) c r (dataAl message) msg → ¬ A) :
    RunsOk fork bound runChild evm within ↔ ForwardOk message c ∧ A := by
  refine fwd_ok_iff_fails
    (Cl := CallFrom (callGasAl fork gas c10 cU (callR substate state message r)).subCall
      (atCallState (callState state message) (upAddr state message) r message.currentTarget)
      (atCallSub (callSub substate state message) (upAddr state message) r))
    (Q := fun _ child => child.error = none ∧ 128 ≤ gas - preCostAl fork c10 cU -
      (callGasAl fork gas c10 cU (callR substate state message r)).cost +
      child.gas)
    (fun ⟨⟨h4, hv⟩, hsz, hdepth⟩ =>
    (spec_depAl_g hfork h4 hsize' hsel hv hdep hcode hsz hszl hroute hdepth hc10 hcU hg
      fun _ _ _ hcal hfwd hcl => (hcal hfwd hcl).2).consequence (fun _ h => h)
      fun e ⟨_, _, _, hcal, hfwd, hmg, hcs, hcss, hok, _⟩ =>
        halted_false_ok e (hok (hcal hfwd ⟨hmg, hcs, hcss⟩).1))
    within ?_ hans hfail start
  intro s hs hok
  obtain ⟨h4, hv, -⟩ := runFrame_ok_dispatch hfork hsize' start within hs hok
  obtain ⟨c', r', hcode', hroute', hw, -, hdepth, caller, msg, lt, child, hch, he, hfwd, hmg, hcs, hcss, hgas, -⟩ :=
    dep_allowance_complete hfork hsize' hsel hdep hc10 hcU start within hs hok
  obtain rfl := code_eq hcode hcode'
  obtain rfl := routes_unique hroute' hroute
  exact ⟨⟨⟨h4, hv⟩, size_pos_of hw, hdepth⟩, caller, msg, lt, child, hch, ⟨he, hgas⟩, hfwd, hmg, hcs, hcss⟩

/-- `allowance(o, s)` when deprecated succeeds exactly when `ForwardOk` holds and the forwarded
call ends with no error (`A`, by `hans`). -/
theorem allowance_dep_ok_iff (hszl : c.size < 2 ^ 256)
    (hg : preCostAl fork c10 cU + 100 + callR substate state message r ≤ gas)
    (htail : 128 ≤ gas - preCostAl fork c10 cU -
      (callGasAl fork gas c10 cU (callR substate state message r)).cost)
    {A : Prop}
    (hans : ∀ caller msg lt child, runChild caller msg lt = .ok child →
      SendsVia message (upAddr state message) c r (dataAl message) msg →
      CallFrom (callGasAl fork gas c10 cU (callR substate state message r)).subCall
        (atCallState (callState state message) (upAddr state message) r message.currentTarget)
        (atCallSub (callSub substate state message) (upAddr state message) r) caller msg →
        (child.1.error = none ↔ A))
    (hnf : NoFailOn runChild (SendsVia message (upAddr state message) c r (dataAl message))) :
    RunsOk fork bound runChild evm within ↔ ForwardOk message c ∧ A :=
  allowance_dep_ok_iff_fails hfork hsize' hsel hdep hcode hroute hc10 hcU start within hszl hg
    (fun caller msg lt child hch hfwd hcl =>
      ⟨fun h => (hans caller msg lt child hch hfwd hcl).1 h.1,
      fun hA => ⟨(hans caller msg lt child hch hfwd hcl).2 hA, Nat.le_trans htail (Nat.le_add_right _ _)⟩⟩)
    fun _ _ _ e h hs => absurd h (hnf _ _ _ e hs)

/-- `allowance(o, s)` when deprecated, with the gas of the path up to the CALL (`hg`) and no bound on
the gas after it: the run succeeds exactly when `ForwardOk` holds and `A` holds, where `A` is
equivalent (`hans`) to the forwarded call ending with no error and leaving, with the gas the CALL
keeps, at least 128 gas for the code after the CALL. -/
theorem allowance_dep_ok_iff_gas (hszl : c.size < 2 ^ 256)
    (hg : preCostAl fork c10 cU + 100 + callR substate state message r ≤ gas)
    {A : Prop}
    (hans : ∀ caller msg lt child, runChild caller msg lt = .ok child →
      SendsVia message (upAddr state message) c r (dataAl message) msg →
      CallFrom (callGasAl fork gas c10 cU (callR substate state message r)).subCall
        (atCallState (callState state message) (upAddr state message) r message.currentTarget)
        (atCallSub (callSub substate state message) (upAddr state message) r) caller msg →
        (child.1.error = none ∧ 128 ≤ gas - preCostAl fork c10 cU -
      (callGasAl fork gas c10 cU (callR substate state message r)).cost + child.1.gas ↔ A))
    (hnf : NoFailOn runChild (SendsVia message (upAddr state message) c r (dataAl message))) :
    RunsOk fork bound runChild evm within ↔ ForwardOk message c ∧ A :=
  allowance_dep_ok_iff_fails hfork hsize' hsel hdep hcode hroute hc10 hcU start within hszl hg hans
    fun _ _ _ e h hs => absurd h (hnf _ _ _ e hs)

/-- `allowance_dep_ok_iff` for a runner that may fail, with errors that abort the run: success gives
the checks and `A`; the checks and `A` give success or a failure of the runner on some
message. -/
theorem allowance_dep_ok_or_fails (hszl : c.size < 2 ^ 256)
    (hg : preCostAl fork c10 cU + 100 + callR substate state message r ≤ gas)
    (htail : 128 ≤ gas - preCostAl fork c10 cU -
      (callGasAl fork gas c10 cU (callR substate state message r)).cost)
    {A : Prop}
    (hans : ∀ caller msg lt child, runChild caller msg lt = .ok child →
      SendsVia message (upAddr state message) c r (dataAl message) msg →
        (child.1.error = none ↔ A))
    (hab : ∀ caller msg lt e, runChild caller msg lt = .error e → e.aborts = true) :
    (RunsOk fork bound runChild evm within → ForwardOk message c ∧ A) ∧
      (ForwardOk message c ∧ A → RunsOk fork bound runChild evm within ∨
        ∃ caller msg lt e, runChild caller msg lt = .error e) := by
  refine fwd_ok_or_fails (fun ⟨⟨h4, hv⟩, hsz, hdepth⟩ =>
    (spec_depAl hfork h4 hsize' hsel hv hdep hcode hsz hszl hroute hdepth hc10 hcU hg
      htail).consequence (fun _ h => h)
      fun e ⟨_, _, _, hcal, hfwd, _, _, _, hok, _⟩ hA => halted_false_ok e (hok ((hcal hfwd).2 hA)))
    within ?_ hans hab start
  intro s hs hok
  obtain ⟨h4, hv, -⟩ := runFrame_ok_dispatch hfork hsize' start within hs hok
  obtain ⟨c', r', hcode', hroute', hw, -, hdepth, caller, msg, lt, child, hch, he, hfwd, -⟩ :=
    dep_allowance_complete hfork hsize' hsel hdep hc10 hcU start within hs hok
  obtain rfl := code_eq hcode hcode'
  obtain rfl := routes_unique hroute' hroute
  exact ⟨⟨⟨h4, hv⟩, size_pos_of hw, hdepth⟩, caller, msg, lt, child, hch, he, hfwd⟩

theorem allowance_dep_low
    (hg : gas < preCostAl fork c10 cU + 100 + callR substate state message r) :
    ¬ RunsOk fork bound runChild evm within := by
  rintro ⟨s, hs, hok⟩
  obtain ⟨c', r', hcode', hroute', -, hgc, -⟩ :=
    dep_allowance_complete hfork hsize' hsel hdep hc10 hcU start within hs hok
  obtain rfl := code_eq hcode hcode'
  obtain rfl := routes_unique hroute' hroute
  exact absurd hgc (Nat.not_le.mpr hg)

end

/-! ## transfer -/

section
variable (hfork : .berlin ≤ fork) (hsize' : message.data.size < 2 ^ 256)
  (hsel : selector message.data = 0xa9059cbb)
  (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0) {c : ByteArray}
  (hcode : state.getCode (state.getAccount (upAddr state message)).codeHash = .ok c)
  {r : Route} (hroute : Routes fork state c r) {c0 cB c10 cU : Bool}
  (hc0 : coldIn substate message.currentTarget 0 = c0)
  (hcB : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget
    (blackSlot message) = cB)
  (hc10 : coldIn (accessSlot (accessSlot substate message.currentTarget 0) message.currentTarget
    (blackSlot message)) message.currentTarget 10 = c10)
  (hcU : decide (upAddr state message ∉ substate.accessedAddresses) = cU)
  (start : At CODE message 0 [] .empty gas state substate evm)
  (within : GasMeter.gasHeld evm.gas ≤ bound)
include hfork hsize' hsel hdep hcode hroute hc0 hcB hc10 hcU start

/-- `transfer_dep_ok_iff_gas` for a runner that may fail, with any error (round 26): with `hg` only, the
run succeeds exactly when the checks hold and `A` holds, where `A` is equivalent (`hans`) to the
forwarded call ending with no error and enough gas left for the code after the CALL, and a failure
of the runner on a forwarded message excludes `A` (`hfail`). -/
theorem transfer_dep_ok_iff_fails (hszl : c.size < 2 ^ 256)
    (hg : preCostT fork c0 cB c10 cU + 100 + callRT substate state message r ≤ gas)
    {A : Prop}
    (hans : ∀ caller msg lt child, runChild caller msg lt = .ok child →
      SendsVia message (upAddr state message) c r (dataT message) msg →
      CallFrom (callGasT fork gas c0 cB c10 cU (callRT substate state message r)).subCall
        (atCallState (callStateT state message) (upAddr state message) r message.currentTarget)
        (atCallSub (callSubT substate state message) (upAddr state message) r) caller msg →
        (child.1.error = none ∧ 51 ≤ gas - preCostT fork c0 cB c10 cU -
      (callGasT fork gas c0 cB c10 cU (callRT substate state message r)).cost + child.1.gas ↔ A))
    (hfail : ∀ caller msg lt e, runChild caller msg lt = .error e →
      SendsVia message (upAddr state message) c r (dataT message) msg → ¬ A) :
    RunsOk fork bound runChild evm within ↔ TransferDepGuard state message c ∧ A := by
  refine fwd_ok_iff_fails
    (Cl := CallFrom (callGasT fork gas c0 cB c10 cU (callRT substate state message r)).subCall
      (atCallState (callStateT state message) (upAddr state message) r message.currentTarget)
      (atCallSub (callSubT substate state message) (upAddr state message) r))
    (Q := fun _ child => child.error = none ∧ 51 ≤ gas - preCostT fork c0 cB c10 cU -
      (callGasT fork gas c0 cB c10 cU (callRT substate state message r)).cost +
      child.gas)
    (fun ⟨⟨⟨h4, hv⟩, hsz, hdepth⟩, hp, hb⟩ =>
    (spec_depT_g ⟨hfork, h4, hsize', hsel, hv, hp, hb, hdep, hcode, hsz, hszl, hroute, hdepth,
      hc0, hcB, hc10, hcU⟩ hg fun _ _ _ hcal hfwd hcl => (hcal hfwd hcl).2).consequence (fun _ h => h)
      fun e ⟨_, _, _, hcal, hfwd, hmg, hcs, hcss, hok, _⟩ =>
        halted_false_ok e (hok (hcal hfwd ⟨hmg, hcs, hcss⟩).1))
    within ?_ hans hfail start
  intro s hs hok
  obtain ⟨h4, hv, -⟩ := runFrame_ok_dispatch hfork hsize' start within hs hok
  obtain ⟨c', r', hcode', hroute', hp, hb, hw, -, hdepth, caller, msg, lt, child, hch, he, hfwd,
    hmg, hcs, hcss, hgas, -⟩ := dep_transfer_complete hfork hsize' hsel hdep hc0 hcB hc10 hcU start within hs hok
  obtain rfl := code_eq hcode hcode'
  obtain rfl := routes_unique hroute' hroute
  exact ⟨⟨⟨⟨h4, hv⟩, size_pos_of hw, hdepth⟩, hp, hb⟩, caller, msg, lt, child, hch, ⟨he, hgas⟩, hfwd, hmg, hcs, hcss⟩

/-- `transfer(a, v)` when deprecated succeeds exactly when `TransferDepGuard` holds and the
forwarded call ends with no error (`A`, by `hans`). -/
theorem transfer_dep_ok_iff (hszl : c.size < 2 ^ 256)
    (hg : preCostT fork c0 cB c10 cU + 100 + callRT substate state message r ≤ gas)
    (htail : 51 ≤ gas - preCostT fork c0 cB c10 cU -
      (callGasT fork gas c0 cB c10 cU (callRT substate state message r)).cost)
    {A : Prop}
    (hans : ∀ caller msg lt child, runChild caller msg lt = .ok child →
      SendsVia message (upAddr state message) c r (dataT message) msg →
      CallFrom (callGasT fork gas c0 cB c10 cU (callRT substate state message r)).subCall
        (atCallState (callStateT state message) (upAddr state message) r message.currentTarget)
        (atCallSub (callSubT substate state message) (upAddr state message) r) caller msg →
        (child.1.error = none ↔ A))
    (hnf : NoFailOn runChild (SendsVia message (upAddr state message) c r (dataT message))) :
    RunsOk fork bound runChild evm within ↔ TransferDepGuard state message c ∧ A :=
  transfer_dep_ok_iff_fails hfork hsize' hsel hdep hcode hroute hc0 hcB hc10 hcU start within hszl hg
    (fun caller msg lt child hch hfwd hcl =>
      ⟨fun h => (hans caller msg lt child hch hfwd hcl).1 h.1,
      fun hA => ⟨(hans caller msg lt child hch hfwd hcl).2 hA, Nat.le_trans htail (Nat.le_add_right _ _)⟩⟩)
    fun _ _ _ e h hs => absurd h (hnf _ _ _ e hs)

/-- `transfer(a, v)` when deprecated, with the gas of the path up to the CALL (`hg`) and no bound on
the gas after it: the run succeeds exactly when `TransferDepGuard` holds and `A` holds, where `A` is
equivalent (`hans`) to the forwarded call ending with no error and leaving, with the gas the CALL
keeps, at least 51 gas for the code after the CALL. -/
theorem transfer_dep_ok_iff_gas (hszl : c.size < 2 ^ 256)
    (hg : preCostT fork c0 cB c10 cU + 100 + callRT substate state message r ≤ gas)
    {A : Prop}
    (hans : ∀ caller msg lt child, runChild caller msg lt = .ok child →
      SendsVia message (upAddr state message) c r (dataT message) msg →
      CallFrom (callGasT fork gas c0 cB c10 cU (callRT substate state message r)).subCall
        (atCallState (callStateT state message) (upAddr state message) r message.currentTarget)
        (atCallSub (callSubT substate state message) (upAddr state message) r) caller msg →
        (child.1.error = none ∧ 51 ≤ gas - preCostT fork c0 cB c10 cU -
      (callGasT fork gas c0 cB c10 cU (callRT substate state message r)).cost + child.1.gas ↔ A))
    (hnf : NoFailOn runChild (SendsVia message (upAddr state message) c r (dataT message))) :
    RunsOk fork bound runChild evm within ↔ TransferDepGuard state message c ∧ A :=
  transfer_dep_ok_iff_fails hfork hsize' hsel hdep hcode hroute hc0 hcB hc10 hcU start within hszl hg hans
    fun _ _ _ e h hs => absurd h (hnf _ _ _ e hs)

/-- `transfer_dep_ok_iff` for a runner that may fail, with errors that abort the run: success gives
the checks and `A`; the checks and `A` give success or a failure of the runner on some
message. -/
theorem transfer_dep_ok_or_fails (hszl : c.size < 2 ^ 256)
    (hg : preCostT fork c0 cB c10 cU + 100 + callRT substate state message r ≤ gas)
    (htail : 51 ≤ gas - preCostT fork c0 cB c10 cU -
      (callGasT fork gas c0 cB c10 cU (callRT substate state message r)).cost)
    {A : Prop}
    (hans : ∀ caller msg lt child, runChild caller msg lt = .ok child →
      SendsVia message (upAddr state message) c r (dataT message) msg →
        (child.1.error = none ↔ A))
    (hab : ∀ caller msg lt e, runChild caller msg lt = .error e → e.aborts = true) :
    (RunsOk fork bound runChild evm within → TransferDepGuard state message c ∧ A) ∧
      (TransferDepGuard state message c ∧ A → RunsOk fork bound runChild evm within ∨
        ∃ caller msg lt e, runChild caller msg lt = .error e) := by
  refine fwd_ok_or_fails (fun ⟨⟨⟨h4, hv⟩, hsz, hdepth⟩, hp, hb⟩ =>
    (spec_depT ⟨hfork, h4, hsize', hsel, hv, hp, hb, hdep, hcode, hsz, hszl, hroute, hdepth,
      hc0, hcB, hc10, hcU⟩ hg htail).consequence (fun _ h => h)
      fun e ⟨_, _, _, hcal, hfwd, _, _, _, hok, _⟩ hA => halted_false_ok e (hok ((hcal hfwd).2 hA)))
    within ?_ hans hab start
  intro s hs hok
  obtain ⟨h4, hv, -⟩ := runFrame_ok_dispatch hfork hsize' start within hs hok
  obtain ⟨c', r', hcode', hroute', hp, hb, hw, -, hdepth, caller, msg, lt, child, hch, he, hfwd,
    -⟩ := dep_transfer_complete hfork hsize' hsel hdep hc0 hcB hc10 hcU start within hs hok
  obtain rfl := code_eq hcode hcode'
  obtain rfl := routes_unique hroute' hroute
  exact ⟨⟨⟨⟨h4, hv⟩, size_pos_of hw, hdepth⟩, hp, hb⟩, caller, msg, lt, child, hch, he, hfwd⟩

theorem transfer_dep_low
    (hg : gas < preCostT fork c0 cB c10 cU + 100 + callRT substate state message r) :
    ¬ RunsOk fork bound runChild evm within := by
  rintro ⟨s, hs, hok⟩
  obtain ⟨c', r', hcode', hroute', -, -, -, hgc, -⟩ :=
    dep_transfer_complete hfork hsize' hsel hdep hc0 hcB hc10 hcU start within hs hok
  obtain rfl := code_eq hcode hcode'
  obtain rfl := routes_unique hroute' hroute
  exact absurd hgc (Nat.not_le.mpr hg)

end

/-! ## approve -/

section
variable (hfork : .berlin ≤ fork) (hsize' : message.data.size < 2 ^ 256)
  (hsel : selector message.data = 0x095ea7b3)
  (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0) {c : ByteArray}
  (hcode : state.getCode (state.getAccount (upAddr state message)).codeHash = .ok c)
  {r : Route} (hroute : Routes fork state c r) {c10 cU : Bool}
  (hc10 : coldIn substate message.currentTarget 10 = c10)
  (hcU : decide (upAddr state message ∉ substate.accessedAddresses) = cU)
  (start : At CODE message 0 [] .empty gas state substate evm)
  (within : GasMeter.gasHeld evm.gas ≤ bound)
include hfork hsize' hsel hdep hcode hroute hc10 hcU start

/-- `approve_dep_ok_iff_gas` for a runner that may fail, with any error (round 26): with `hg` only, the
run succeeds exactly when the checks hold and `A` holds, where `A` is equivalent (`hans`) to the
forwarded call ending with no error and enough gas left for the code after the CALL, and a failure
of the runner on a forwarded message excludes `A` (`hfail`). -/
theorem approve_dep_ok_iff_fails (hszl : c.size < 2 ^ 256)
    (hg : preCostA fork c10 cU + 100 + callR substate state message r ≤ gas)
    {A : Prop}
    (hans : ∀ caller msg lt child, runChild caller msg lt = .ok child →
      SendsVia message (upAddr state message) c r (dataA message) msg →
      CallFrom (callGasA fork gas c10 cU (callR substate state message r)).subCall
        (atCallState (callState state message) (upAddr state message) r message.currentTarget)
        (atCallSub (callSub substate state message) (upAddr state message) r) caller msg →
        (child.1.error = none ∧ 53 ≤ gas - preCostA fork c10 cU -
      (callGasA fork gas c10 cU (callR substate state message r)).cost + child.1.gas ↔ A))
    (hfail : ∀ caller msg lt e, runChild caller msg lt = .error e →
      SendsVia message (upAddr state message) c r (dataA message) msg → ¬ A) :
    RunsOk fork bound runChild evm within ↔ ApproveDepGuard message c ∧ A := by
  refine fwd_ok_iff_fails
    (Cl := CallFrom (callGasA fork gas c10 cU (callR substate state message r)).subCall
      (atCallState (callState state message) (upAddr state message) r message.currentTarget)
      (atCallSub (callSub substate state message) (upAddr state message) r))
    (Q := fun _ child => child.error = none ∧ 53 ≤ gas - preCostA fork c10 cU -
      (callGasA fork gas c10 cU (callR substate state message r)).cost +
      child.gas)
    (fun ⟨⟨⟨_, hv⟩, hsz, hdepth⟩, hl⟩ =>
    (spec_depA_g ⟨hfork, hl, hsize', hsel, hv, hdep, hcode, hsz, hszl, hroute, hdepth, hc10, hcU⟩
      hg fun _ _ _ hcal hfwd hcl => (hcal hfwd hcl).2).consequence (fun _ h => h)
      fun e ⟨_, _, _, hcal, hfwd, hmg, hcs, hcss, hok, _⟩ =>
        halted_false_ok e (hok (hcal hfwd ⟨hmg, hcs, hcss⟩).1))
    within ?_ hans hfail start
  intro s hs hok
  obtain ⟨h4, hv, -⟩ := runFrame_ok_dispatch hfork hsize' start within hs hok
  obtain ⟨c', r', hcode', hroute', hl, hw, -, hdepth, caller, msg, lt, child, hch, he, hfwd, hmg, hcs, hcss, hgas, -⟩ :=
    dep_approve_complete hfork hsize' hsel hdep hc10 hcU start within hs hok
  obtain rfl := code_eq hcode hcode'
  obtain rfl := routes_unique hroute' hroute
  exact ⟨⟨⟨⟨h4, hv⟩, size_pos_of hw, hdepth⟩, hl⟩, caller, msg, lt, child, hch, ⟨he, hgas⟩, hfwd, hmg, hcs, hcss⟩

/-- `approve(s, v)` when deprecated succeeds exactly when `ApproveDepGuard` holds and the
forwarded call ends with no error (`A`, by `hans`). -/
theorem approve_dep_ok_iff (hszl : c.size < 2 ^ 256)
    (hg : preCostA fork c10 cU + 100 + callR substate state message r ≤ gas)
    (htail : 53 ≤ gas - preCostA fork c10 cU -
      (callGasA fork gas c10 cU (callR substate state message r)).cost)
    {A : Prop}
    (hans : ∀ caller msg lt child, runChild caller msg lt = .ok child →
      SendsVia message (upAddr state message) c r (dataA message) msg →
      CallFrom (callGasA fork gas c10 cU (callR substate state message r)).subCall
        (atCallState (callState state message) (upAddr state message) r message.currentTarget)
        (atCallSub (callSub substate state message) (upAddr state message) r) caller msg →
        (child.1.error = none ↔ A))
    (hnf : NoFailOn runChild (SendsVia message (upAddr state message) c r (dataA message))) :
    RunsOk fork bound runChild evm within ↔ ApproveDepGuard message c ∧ A :=
  approve_dep_ok_iff_fails hfork hsize' hsel hdep hcode hroute hc10 hcU start within hszl hg
    (fun caller msg lt child hch hfwd hcl =>
      ⟨fun h => (hans caller msg lt child hch hfwd hcl).1 h.1,
      fun hA => ⟨(hans caller msg lt child hch hfwd hcl).2 hA, Nat.le_trans htail (Nat.le_add_right _ _)⟩⟩)
    fun _ _ _ e h hs => absurd h (hnf _ _ _ e hs)

/-- `approve(s, v)` when deprecated, with the gas of the path up to the CALL (`hg`) and no bound on
the gas after it: the run succeeds exactly when `ApproveDepGuard` holds and `A` holds, where `A` is
equivalent (`hans`) to the forwarded call ending with no error and leaving, with the gas the CALL
keeps, at least 53 gas for the code after the CALL. -/
theorem approve_dep_ok_iff_gas (hszl : c.size < 2 ^ 256)
    (hg : preCostA fork c10 cU + 100 + callR substate state message r ≤ gas)
    {A : Prop}
    (hans : ∀ caller msg lt child, runChild caller msg lt = .ok child →
      SendsVia message (upAddr state message) c r (dataA message) msg →
      CallFrom (callGasA fork gas c10 cU (callR substate state message r)).subCall
        (atCallState (callState state message) (upAddr state message) r message.currentTarget)
        (atCallSub (callSub substate state message) (upAddr state message) r) caller msg →
        (child.1.error = none ∧ 53 ≤ gas - preCostA fork c10 cU -
      (callGasA fork gas c10 cU (callR substate state message r)).cost + child.1.gas ↔ A))
    (hnf : NoFailOn runChild (SendsVia message (upAddr state message) c r (dataA message))) :
    RunsOk fork bound runChild evm within ↔ ApproveDepGuard message c ∧ A :=
  approve_dep_ok_iff_fails hfork hsize' hsel hdep hcode hroute hc10 hcU start within hszl hg hans
    fun _ _ _ e h hs => absurd h (hnf _ _ _ e hs)

/-- `approve_dep_ok_iff` for a runner that may fail, with errors that abort the run: success gives
the checks and `A`; the checks and `A` give success or a failure of the runner on some
message. -/
theorem approve_dep_ok_or_fails (hszl : c.size < 2 ^ 256)
    (hg : preCostA fork c10 cU + 100 + callR substate state message r ≤ gas)
    (htail : 53 ≤ gas - preCostA fork c10 cU -
      (callGasA fork gas c10 cU (callR substate state message r)).cost)
    {A : Prop}
    (hans : ∀ caller msg lt child, runChild caller msg lt = .ok child →
      SendsVia message (upAddr state message) c r (dataA message) msg →
        (child.1.error = none ↔ A))
    (hab : ∀ caller msg lt e, runChild caller msg lt = .error e → e.aborts = true) :
    (RunsOk fork bound runChild evm within → ApproveDepGuard message c ∧ A) ∧
      (ApproveDepGuard message c ∧ A → RunsOk fork bound runChild evm within ∨
        ∃ caller msg lt e, runChild caller msg lt = .error e) := by
  refine fwd_ok_or_fails (fun ⟨⟨⟨_, hv⟩, hsz, hdepth⟩, hl⟩ =>
    (spec_depA ⟨hfork, hl, hsize', hsel, hv, hdep, hcode, hsz, hszl, hroute, hdepth, hc10, hcU⟩
      hg htail).consequence (fun _ h => h)
      fun e ⟨_, _, _, hcal, hfwd, _, _, _, hok, _⟩ hA => halted_false_ok e (hok ((hcal hfwd).2 hA)))
    within ?_ hans hab start
  intro s hs hok
  obtain ⟨h4, hv, -⟩ := runFrame_ok_dispatch hfork hsize' start within hs hok
  obtain ⟨c', r', hcode', hroute', hl, hw, -, hdepth, caller, msg, lt, child, hch, he, hfwd, -⟩ :=
    dep_approve_complete hfork hsize' hsel hdep hc10 hcU start within hs hok
  obtain rfl := code_eq hcode hcode'
  obtain rfl := routes_unique hroute' hroute
  exact ⟨⟨⟨⟨h4, hv⟩, size_pos_of hw, hdepth⟩, hl⟩, caller, msg, lt, child, hch, he, hfwd⟩

theorem approve_dep_low
    (hg : gas < preCostA fork c10 cU + 100 + callR substate state message r) :
    ¬ RunsOk fork bound runChild evm within := by
  rintro ⟨s, hs, hok⟩
  obtain ⟨c', r', hcode', hroute', -, -, hgc, -⟩ :=
    dep_approve_complete hfork hsize' hsel hdep hc10 hcU start within hs hok
  obtain rfl := code_eq hcode hcode'
  obtain rfl := routes_unique hroute' hroute
  exact absurd hgc (Nat.not_le.mpr hg)

end

/-! ## transferFrom -/

section
variable (hfork : .berlin ≤ fork) (hsize' : message.data.size < 2 ^ 256)
  (hsel : selector message.data = 0x23b872dd)
  (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0) {c : ByteArray}
  (hcode : state.getCode (state.getAccount (upAddr state message)).codeHash = .ok c)
  {r : Route} (hroute : Routes fork state c r) {c0 cB c10 cU : Bool}
  (hc0 : coldIn substate message.currentTarget 0 = c0)
  (hcB : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget
    (blackFrom (fromArg message)) = cB)
  (hc10 : coldIn (accessSlot (accessSlot substate message.currentTarget 0) message.currentTarget
    (blackFrom (fromArg message))) message.currentTarget 10 = c10)
  (hcU : decide (upAddr state message ∉ substate.accessedAddresses) = cU)
  (start : At CODE message 0 [] .empty gas state substate evm)
  (within : GasMeter.gasHeld evm.gas ≤ bound)
include hfork hsize' hsel hdep hcode hroute hc0 hcB hc10 hcU start

/-- `transferFrom_dep_ok_iff_gas` for a runner that may fail, with any error (round 26): with `hg` only, the
run succeeds exactly when the checks hold and `A` holds, where `A` is equivalent (`hans`) to the
forwarded call ending with no error and enough gas left for the code after the CALL, and a failure
of the runner on a forwarded message excludes `A` (`hfail`). -/
theorem transferFrom_dep_ok_iff_fails (hszl : c.size < 2 ^ 256)
    (hg : DeprecatedTransferFrom.preCostF fork c0 cB c10 cU + 100 +
      callRF substate state message r ≤ gas)
    {A : Prop}
    (hans : ∀ caller msg lt child, runChild caller msg lt = .ok child →
      SendsVia message (upAddr state message) c r (dataF message) msg →
      CallFrom (callGasF fork gas c0 cB c10 cU (callRF substate state message r)).subCall
        (atCallState (callStateF state message) (upAddr state message) r message.currentTarget)
        (atCallSub (callSubF substate state message) (upAddr state message) r) caller msg →
        (child.1.error = none ∧ 53 ≤ gas - DeprecatedTransferFrom.preCostF fork c0 cB c10 cU -
      (callGasF fork gas c0 cB c10 cU (callRF substate state message r)).cost + child.1.gas ↔ A))
    (hfail : ∀ caller msg lt e, runChild caller msg lt = .error e →
      SendsVia message (upAddr state message) c r (dataF message) msg → ¬ A) :
    RunsOk fork bound runChild evm within ↔ TransferFromDepGuard state message c ∧ A := by
  refine fwd_ok_iff_fails
    (Cl := CallFrom (callGasF fork gas c0 cB c10 cU (callRF substate state message r)).subCall
      (atCallState (callStateF state message) (upAddr state message) r message.currentTarget)
      (atCallSub (callSubF substate state message) (upAddr state message) r))
    (Q := fun _ child => child.error = none ∧ 53 ≤ gas - DeprecatedTransferFrom.preCostF fork c0 cB c10 cU -
      (callGasF fork gas c0 cB c10 cU (callRF substate state message r)).cost +
      child.gas)
    (fun ⟨⟨⟨h4, hv⟩, hsz, hdepth⟩, hp, hb⟩ =>
    (spec_depF_g ⟨hfork, h4, hsize', hsel, hv, hp, hb, hdep, hcode, hsz, hszl, hroute, hdepth,
      hc0, hcB, hc10, hcU⟩ hg fun _ _ _ hcal hfwd hcl => (hcal hfwd hcl).2).consequence (fun _ h => h)
      fun e ⟨_, _, _, hcal, hfwd, hmg, hcs, hcss, hok, _⟩ =>
        halted_false_ok e (hok (hcal hfwd ⟨hmg, hcs, hcss⟩).1))
    within ?_ hans hfail start
  intro s hs hok
  obtain ⟨h4, hv, -⟩ := runFrame_ok_dispatch hfork hsize' start within hs hok
  obtain ⟨c', r', hcode', hroute', hp, hb, hw, -, hdepth, caller, msg, lt, child, hch, he, hfwd,
    hmg, hcs, hcss, hgas, -⟩ := dep_transferFrom_complete hfork hsize' hsel hdep hc0 hcB hc10 hcU start within hs hok
  obtain rfl := code_eq hcode hcode'
  obtain rfl := routes_unique hroute' hroute
  exact ⟨⟨⟨⟨h4, hv⟩, size_pos_of hw, hdepth⟩, hp, hb⟩, caller, msg, lt, child, hch, ⟨he, hgas⟩, hfwd, hmg, hcs, hcss⟩

/-- `transferFrom(f, t, v)` when deprecated succeeds exactly when `TransferFromDepGuard` holds and
the forwarded call ends with no error (`A`, by `hans`). -/
theorem transferFrom_dep_ok_iff (hszl : c.size < 2 ^ 256)
    (hg : DeprecatedTransferFrom.preCostF fork c0 cB c10 cU + 100 +
      callRF substate state message r ≤ gas)
    (htail : 53 ≤ gas - DeprecatedTransferFrom.preCostF fork c0 cB c10 cU -
      (callGasF fork gas c0 cB c10 cU (callRF substate state message r)).cost)
    {A : Prop}
    (hans : ∀ caller msg lt child, runChild caller msg lt = .ok child →
      SendsVia message (upAddr state message) c r (dataF message) msg →
      CallFrom (callGasF fork gas c0 cB c10 cU (callRF substate state message r)).subCall
        (atCallState (callStateF state message) (upAddr state message) r message.currentTarget)
        (atCallSub (callSubF substate state message) (upAddr state message) r) caller msg →
        (child.1.error = none ↔ A))
    (hnf : NoFailOn runChild (SendsVia message (upAddr state message) c r (dataF message))) :
    RunsOk fork bound runChild evm within ↔ TransferFromDepGuard state message c ∧ A :=
  transferFrom_dep_ok_iff_fails hfork hsize' hsel hdep hcode hroute hc0 hcB hc10 hcU start within hszl hg
    (fun caller msg lt child hch hfwd hcl =>
      ⟨fun h => (hans caller msg lt child hch hfwd hcl).1 h.1,
      fun hA => ⟨(hans caller msg lt child hch hfwd hcl).2 hA, Nat.le_trans htail (Nat.le_add_right _ _)⟩⟩)
    fun _ _ _ e h hs => absurd h (hnf _ _ _ e hs)

/-- `transferFrom(f, t, v)` when deprecated, with the gas of the path up to the CALL (`hg`) and no bound on
the gas after it: the run succeeds exactly when `TransferFromDepGuard` holds and `A` holds, where `A` is
equivalent (`hans`) to the forwarded call ending with no error and leaving, with the gas the CALL
keeps, at least 53 gas for the code after the CALL. -/
theorem transferFrom_dep_ok_iff_gas (hszl : c.size < 2 ^ 256)
    (hg : DeprecatedTransferFrom.preCostF fork c0 cB c10 cU + 100 +
      callRF substate state message r ≤ gas)
    {A : Prop}
    (hans : ∀ caller msg lt child, runChild caller msg lt = .ok child →
      SendsVia message (upAddr state message) c r (dataF message) msg →
      CallFrom (callGasF fork gas c0 cB c10 cU (callRF substate state message r)).subCall
        (atCallState (callStateF state message) (upAddr state message) r message.currentTarget)
        (atCallSub (callSubF substate state message) (upAddr state message) r) caller msg →
        (child.1.error = none ∧ 53 ≤ gas - DeprecatedTransferFrom.preCostF fork c0 cB c10 cU -
      (callGasF fork gas c0 cB c10 cU (callRF substate state message r)).cost + child.1.gas ↔ A))
    (hnf : NoFailOn runChild (SendsVia message (upAddr state message) c r (dataF message))) :
    RunsOk fork bound runChild evm within ↔ TransferFromDepGuard state message c ∧ A :=
  transferFrom_dep_ok_iff_fails hfork hsize' hsel hdep hcode hroute hc0 hcB hc10 hcU start within hszl hg hans
    fun _ _ _ e h hs => absurd h (hnf _ _ _ e hs)

/-- `transferFrom_dep_ok_iff` for a runner that may fail, with errors that abort the run: success gives
the checks and `A`; the checks and `A` give success or a failure of the runner on some
message. -/
theorem transferFrom_dep_ok_or_fails (hszl : c.size < 2 ^ 256)
    (hg : DeprecatedTransferFrom.preCostF fork c0 cB c10 cU + 100 +
      callRF substate state message r ≤ gas)
    (htail : 53 ≤ gas - DeprecatedTransferFrom.preCostF fork c0 cB c10 cU -
      (callGasF fork gas c0 cB c10 cU (callRF substate state message r)).cost)
    {A : Prop}
    (hans : ∀ caller msg lt child, runChild caller msg lt = .ok child →
      SendsVia message (upAddr state message) c r (dataF message) msg →
        (child.1.error = none ↔ A))
    (hab : ∀ caller msg lt e, runChild caller msg lt = .error e → e.aborts = true) :
    (RunsOk fork bound runChild evm within → TransferFromDepGuard state message c ∧ A) ∧
      (TransferFromDepGuard state message c ∧ A → RunsOk fork bound runChild evm within ∨
        ∃ caller msg lt e, runChild caller msg lt = .error e) := by
  refine fwd_ok_or_fails (fun ⟨⟨⟨h4, hv⟩, hsz, hdepth⟩, hp, hb⟩ =>
    (spec_depF ⟨hfork, h4, hsize', hsel, hv, hp, hb, hdep, hcode, hsz, hszl, hroute, hdepth,
      hc0, hcB, hc10, hcU⟩ hg htail).consequence (fun _ h => h)
      fun e ⟨_, _, _, hcal, hfwd, _, _, _, hok, _⟩ hA => halted_false_ok e (hok ((hcal hfwd).2 hA)))
    within ?_ hans hab start
  intro s hs hok
  obtain ⟨h4, hv, -⟩ := runFrame_ok_dispatch hfork hsize' start within hs hok
  obtain ⟨c', r', hcode', hroute', hp, hb, hw, -, hdepth, caller, msg, lt, child, hch, he, hfwd,
    -⟩ := dep_transferFrom_complete hfork hsize' hsel hdep hc0 hcB hc10 hcU start within hs hok
  obtain rfl := code_eq hcode hcode'
  obtain rfl := routes_unique hroute' hroute
  exact ⟨⟨⟨⟨h4, hv⟩, size_pos_of hw, hdepth⟩, hp, hb⟩, caller, msg, lt, child, hch, he, hfwd⟩

theorem transferFrom_dep_low
    (hg : gas < DeprecatedTransferFrom.preCostF fork c0 cB c10 cU + 100 +
      callRF substate state message r) :
    ¬ RunsOk fork bound runChild evm within := by
  rintro ⟨s, hs, hok⟩
  obtain ⟨c', r', hcode', hroute', -, -, -, hgc, -⟩ :=
    dep_transferFrom_complete hfork hsize' hsel hdep hc0 hcB hc10 hcU start within hs hok
  obtain rfl := code_eq hcode hcode'
  obtain rfl := routes_unique hroute' hroute
  exact absurd hgc (Nat.not_le.mpr hg)

end

/-! ## destroyBlackFunds -/

section
variable (hfork : .berlin ≤ fork) (hsize' : message.data.size < 2 ^ 256)
  (hsel : selector message.data = 0xf3bdc228)
  (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0) {c : ByteArray}
  (hcode : state.getCode (state.getAccount (upAddr state message)).codeHash = .ok c)
  {r : Route} (hroute : Routes fork state c r) {c0 cL c10 cU : Bool}
  (hc0 : coldIn substate message.currentTarget 0 = c0)
  (hcL : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget
    (listSlot (addrArg message.data 0)) = cL)
  (hc10 : coldIn (preSub substate message) message.currentTarget 10 = c10)
  (hcU : decide (upAddr state message ∉ substate.accessedAddresses) = cU)
  (start : At CODE message 0 [] .empty gas state substate evm)
  (within : GasMeter.gasHeld evm.gas ≤ bound)
include hfork hsize' hsel hdep hcode hroute hc0 hcL hc10 hcU start

/-- `destroyBlackFunds_dep_ok_iff_gas` for a runner that may fail, with any error (round 26): with
`hg` only, the run succeeds exactly when `DestroyDepGuard` holds and `A` holds, where `A` is
equivalent (`hans`) to the forwarded `balanceOf(a)` ending with no error, an account of the
contract and enough gas for the tail, and a failure of the runner on a forwarded message excludes
`A` (`hfail`). -/
theorem destroyBlackFunds_dep_ok_iff_fails (hszl : c.size < 2 ^ 256)
    (hg : preCostD fork c0 cL c10 cU + 100 + callRD substate state message r ≤ gas)
    {A : Prop}
    (hans : ∀ caller msg lt child, runChild caller msg lt = .ok child →
      SendsVia message (upAddr state message) c r (dataB message) msg →
      CallFrom (callGasD fork gas c0 cL c10 cU (callRD substate state message r)).subCall
        (atCallState (callStateD state message) (upAddr state message) r message.currentTarget)
        (atCallSub (callSubD substate state message) (upAddr state message) r) caller msg →
        (child.1.error = none ∧ hasAccount child.1.state message.currentTarget ∧
          max (tailCost fork (incorporateChild fork caller child.1).state message.currentTarget
              (addrArg message.data 0) (resWord (outMemOf (memD message) child.1.output))
              (coldIn (incorporateChild fork caller child.1).substate message.currentTarget
                (balSlot message))
              (coldIn (accessSlot (incorporateChild fork caller child.1).substate
                message.currentTarget (balSlot message)) message.currentTarget 1))
            (tailStip fork (incorporateChild fork caller child.1).state message.currentTarget
              (addrArg message.data 0)
              (coldIn (incorporateChild fork caller child.1).substate message.currentTarget
                (balSlot message))
              (coldIn (accessSlot (incorporateChild fork caller child.1).substate
                message.currentTarget (balSlot message)) message.currentTarget 1)) ≤
            gas - preCostD fork c0 cL c10 cU -
              (callGasD fork gas c0 cL c10 cU (callRD substate state message r)).cost +
              child.1.gas ↔ A))
    (hfail : ∀ caller msg lt e, runChild caller msg lt = .error e →
      SendsVia message (upAddr state message) c r (dataB message) msg → ¬ A) :
    RunsOk fork bound runChild evm within ↔ DestroyDepGuard state message c ∧ A := by
  refine fwd_ok_iff_fails
    (Cl := CallFrom (callGasD fork gas c0 cL c10 cU (callRD substate state message r)).subCall
      (atCallState (callStateD state message) (upAddr state message) r message.currentTarget)
      (atCallSub (callSubD substate state message) (upAddr state message) r))
    (Q := fun caller child =>
      child.error = none ∧ hasAccount child.state message.currentTarget ∧
          max (tailCost fork (incorporateChild fork caller child).state message.currentTarget
              (addrArg message.data 0) (resWord (outMemOf (memD message) child.output))
              (coldIn (incorporateChild fork caller child).substate message.currentTarget
                (balSlot message))
              (coldIn (accessSlot (incorporateChild fork caller child).substate
                message.currentTarget (balSlot message)) message.currentTarget 1))
            (tailStip fork (incorporateChild fork caller child).state message.currentTarget
              (addrArg message.data 0)
              (coldIn (incorporateChild fork caller child).substate message.currentTarget
                (balSlot message))
              (coldIn (accessSlot (incorporateChild fork caller child).substate
                message.currentTarget (balSlot message)) message.currentTarget 1)) ≤
            gas - preCostD fork c0 cL c10 cU -
              (callGasD fork gas c0 cL c10 cU (callRD substate state message r)).cost + child.gas)
    (fun ⟨⟨⟨h4, hv⟩, hsz, hdepth⟩, hown, hl, hst⟩ =>
      (spec_depD_g hfork hst h4 hsize' hsel hv hown hl hdep hcode hsz hszl hroute hdepth hc0 hcL
        hc10 hcU hg fun _ _ _ hcal hfwd hcl =>
          let ⟨he, hacc, hm⟩ := hcal hfwd hcl
          ⟨he, hacc, (Nat.max_le.mp hm).1, (Nat.max_le.mp hm).2⟩).consequence (fun _ h => h)
        fun e ⟨_, _, _, _, _, h⟩ => halted_false_ok e h)
    within ?_ hans hfail start
  intro s hs hok
  obtain ⟨h4, hv, -⟩ := runFrame_ok_dispatch hfork hsize' start within hs hok
  obtain ⟨c', r', hcode', hroute', hown, hl, hw, -, hdepth, caller, msg, lt, child, hch, he, hst,
    hacc, hfwd, hmg, hcs, hcss, hcost, -, -, -, -, -, hstip⟩ :=
    dep_destroy_complete hfork hsize' hsel hdep hc0 hcL hc10 hcU start within hs hok
  obtain rfl := code_eq hcode hcode'
  obtain rfl := routes_unique hroute' hroute
  exact ⟨⟨⟨⟨h4, hv⟩, size_pos_of hw, hdepth⟩, hown, hl, hst⟩, caller, msg, lt, child, hch,
    ⟨he, hacc, Nat.max_le.mpr ⟨hcost, hstip⟩⟩, hfwd, hmg, hcs, hcss⟩

/-- `destroyBlackFunds(a)` when deprecated succeeds exactly when `DestroyDepGuard` holds and the
forwarded `balanceOf(a)` ends with no error in a state where the contract has an account (`A`, by
`hans`). Round 30: derived from `destroyBlackFunds_dep_ok_iff_fails` (with `htail`, the tail has
its gas: `tail_le_max`). -/
theorem destroyBlackFunds_dep_ok_iff (hszl : c.size < 2 ^ 256)
    (hg : preCostD fork c0 cL c10 cU + 100 + callRD substate state message r ≤ gas)
    (htail : TAIL_MAX fork ≤ gas - preCostD fork c0 cL c10 cU -
      (callGasD fork gas c0 cL c10 cU (callRD substate state message r)).cost)
    {A : Prop}
    (hans : ∀ caller msg lt child, runChild caller msg lt = .ok child →
      SendsVia message (upAddr state message) c r (dataB message) msg →
      CallFrom (callGasD fork gas c0 cL c10 cU (callRD substate state message r)).subCall
        (atCallState (callStateD state message) (upAddr state message) r message.currentTarget)
        (atCallSub (callSubD substate state message) (upAddr state message) r) caller msg →
        (child.1.error = none ∧ hasAccount child.1.state message.currentTarget ↔ A))
    (hnf : NoFail runChild) :
    RunsOk fork bound runChild evm within ↔ DestroyDepGuard state message c ∧ A :=
  destroyBlackFunds_dep_ok_iff_fails hfork hsize' hsel hdep hcode hroute hc0 hcL hc10 hcU start
    within hszl hg
    (fun caller msg lt child hch hfwd hcl =>
      ⟨fun h => (hans caller msg lt child hch hfwd hcl).1 ⟨h.1, h.2.1⟩,
        fun hA => ⟨((hans caller msg lt child hch hfwd hcl).2 hA).1,
          ((hans caller msg lt child hch hfwd hcl).2 hA).2,
          Nat.le_trans (tail_le_max hfork _ _ _ _ _ _)
            (Nat.le_trans htail (Nat.le_add_right _ _))⟩⟩)
    fun _ _ _ e h _ => absurd h (hnf _ _ _ e)

/-- `destroyBlackFunds(a)` when deprecated, with the gas of the path up to the CALL (`hg`) and no
bound on the gas after it: the run succeeds exactly when `DestroyDepGuard` holds and `A` holds,
where `A` is equivalent (`hans`) to the forwarded `balanceOf(a)` ending with no error, in a state
where the contract has an account, and leaving, with the gas the CALL keeps, at least the larger
of the cost of the tail (`tailCost`) and its stipend bound (`tailStip`), both computed over the
state and substate after the call (`incorporateChild`): the coldness and the original and
current words of `balances[a]` and slot 1 there. -/
theorem destroyBlackFunds_dep_ok_iff_gas (hszl : c.size < 2 ^ 256)
    (hg : preCostD fork c0 cL c10 cU + 100 + callRD substate state message r ≤ gas)
    {A : Prop}
    (hans : ∀ caller msg lt child, runChild caller msg lt = .ok child →
      SendsVia message (upAddr state message) c r (dataB message) msg →
      CallFrom (callGasD fork gas c0 cL c10 cU (callRD substate state message r)).subCall
        (atCallState (callStateD state message) (upAddr state message) r message.currentTarget)
        (atCallSub (callSubD substate state message) (upAddr state message) r) caller msg →
        (child.1.error = none ∧ hasAccount child.1.state message.currentTarget ∧
          max (tailCost fork (incorporateChild fork caller child.1).state message.currentTarget
              (addrArg message.data 0) (resWord (outMemOf (memD message) child.1.output))
              (coldIn (incorporateChild fork caller child.1).substate message.currentTarget
                (balSlot message))
              (coldIn (accessSlot (incorporateChild fork caller child.1).substate
                message.currentTarget (balSlot message)) message.currentTarget 1))
            (tailStip fork (incorporateChild fork caller child.1).state message.currentTarget
              (addrArg message.data 0)
              (coldIn (incorporateChild fork caller child.1).substate message.currentTarget
                (balSlot message))
              (coldIn (accessSlot (incorporateChild fork caller child.1).substate
                message.currentTarget (balSlot message)) message.currentTarget 1)) ≤
            gas - preCostD fork c0 cL c10 cU -
              (callGasD fork gas c0 cL c10 cU (callRD substate state message r)).cost +
              child.1.gas ↔ A))
    (hnf : NoFailOn runChild (SendsVia message (upAddr state message) c r (dataB message))) :
    RunsOk fork bound runChild evm within ↔ DestroyDepGuard state message c ∧ A :=
  destroyBlackFunds_dep_ok_iff_fails hfork hsize' hsel hdep hcode hroute hc0 hcL hc10 hcU start
    within hszl hg hans fun _ _ _ e h hs => absurd h (hnf _ _ _ e hs)

theorem destroyBlackFunds_dep_low
    (hg : gas < preCostD fork c0 cL c10 cU + 100 + callRD substate state message r) :
    ¬ RunsOk fork bound runChild evm within := by
  rintro ⟨s, hs, hok⟩
  obtain ⟨c', r', hcode', hroute', -, -, -, hgc, -⟩ :=
    dep_destroy_complete hfork hsize' hsel hdep hc0 hcL hc10 hcU start within hs hok
  obtain rfl := code_eq hcode hcode'
  obtain rfl := routes_unique hroute' hroute
  exact absurd hgc (Nat.not_le.mpr hg)

end

end UsdtVerify.Exact
