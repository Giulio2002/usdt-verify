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
in the state (`hcode`, `c.size < 2^256`), the route `r` of the CALL (`hroute`), any gas bound and
any message runner `runChild`.

- `*_dep_ok_iff`: with the gas of the success path up to the CALL and after it (`hg`, `htail`),
  and a runner that never fails (`NoFail`) and ends each message forwarded along the route with
  no error exactly when `A` holds (`hans`), the run ends with no error if and only if the checks
  before the forward hold (`ForwardOk`, or `TransferDepGuard`, `ApproveDepGuard`,
  `TransferFromDepGuard`) and `A` holds.
- `*_dep_low`: with less gas than the path up to the CALL and the CALL's access (`hg`), no run
  ends with no error, whatever the runner.
  A gas between that bound and the bound of `htail` is not covered.
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

/-- `totalSupply()` when deprecated succeeds exactly when `ForwardOk` holds and the forwarded
call ends with no error (`A`, by `hans`). -/
theorem totalSupply_dep_ok_iff (hszl : c.size < 2 ^ 256)
    (hg : preCost fork c10 cU + 100 + callR substate state message r ≤ gas)
    (htail : 121 ≤ gas - preCost fork c10 cU -
      (callGas fork gas c10 cU (callR substate state message r)).cost)
    {A : Prop}
    (hans : ∀ caller msg lt child, runChild caller msg lt = .ok child →
      SendsVia message (upAddr state message) c r SEL_TS msg → (child.1.error = none ↔ A))
    (hnf : NoFail runChild) :
    RunsOk fork bound runChild evm within ↔ ForwardOk message c ∧ A := by
  refine fwd_ok_iff (fun ⟨⟨h4, hv⟩, hsz, hdepth⟩ =>
    (spec_dep hfork h4 hsize' hsel hv hdep hcode hsz hszl hroute hdepth hc10 hcU hg
      htail).consequence (fun _ h => h)
      fun e ⟨_, _, _, hcal, hfwd, _, _, _, hok, _⟩ hA => halted_false_ok e (hok ((hcal hfwd).2 hA)))
    within ?_ hans hnf start
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

/-- `balanceOf(a)` when deprecated succeeds exactly when `ForwardOk` holds and the forwarded
call ends with no error (`A`, by `hans`). -/
theorem balanceOf_dep_ok_iff (hszl : c.size < 2 ^ 256)
    (hg : preCostB fork c10 cU + 100 + callR substate state message r ≤ gas)
    (htail : 126 ≤ gas - preCostB fork c10 cU -
      (callGasB fork gas c10 cU (callR substate state message r)).cost)
    {A : Prop}
    (hans : ∀ caller msg lt child, runChild caller msg lt = .ok child →
      SendsVia message (upAddr state message) c r (dataB message) msg →
        (child.1.error = none ↔ A))
    (hnf : NoFail runChild) :
    RunsOk fork bound runChild evm within ↔ ForwardOk message c ∧ A := by
  refine fwd_ok_iff (fun ⟨⟨h4, hv⟩, hsz, hdepth⟩ =>
    (spec_depB hfork h4 hsize' hsel hv hdep hcode hsz hszl hroute hdepth hc10 hcU hg
      htail).consequence (fun _ h => h)
      fun e ⟨_, _, _, hcal, hfwd, _, _, _, hok, _⟩ hA => halted_false_ok e (hok ((hcal hfwd).2 hA)))
    within ?_ hans hnf start
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

/-- `allowance(o, s)` when deprecated succeeds exactly when `ForwardOk` holds and the forwarded
call ends with no error (`A`, by `hans`). -/
theorem allowance_dep_ok_iff (hszl : c.size < 2 ^ 256)
    (hg : preCostAl fork c10 cU + 100 + callR substate state message r ≤ gas)
    (htail : 128 ≤ gas - preCostAl fork c10 cU -
      (callGasAl fork gas c10 cU (callR substate state message r)).cost)
    {A : Prop}
    (hans : ∀ caller msg lt child, runChild caller msg lt = .ok child →
      SendsVia message (upAddr state message) c r (dataAl message) msg →
        (child.1.error = none ↔ A))
    (hnf : NoFail runChild) :
    RunsOk fork bound runChild evm within ↔ ForwardOk message c ∧ A := by
  refine fwd_ok_iff (fun ⟨⟨h4, hv⟩, hsz, hdepth⟩ =>
    (spec_depAl hfork h4 hsize' hsel hv hdep hcode hsz hszl hroute hdepth hc10 hcU hg
      htail).consequence (fun _ h => h)
      fun e ⟨_, _, _, hcal, hfwd, _, _, _, hok, _⟩ hA => halted_false_ok e (hok ((hcal hfwd).2 hA)))
    within ?_ hans hnf start
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

/-- `transfer(a, v)` when deprecated succeeds exactly when `TransferDepGuard` holds and the
forwarded call ends with no error (`A`, by `hans`). -/
theorem transfer_dep_ok_iff (hszl : c.size < 2 ^ 256)
    (hg : preCostT fork c0 cB c10 cU + 100 + callRT substate state message r ≤ gas)
    (htail : 51 ≤ gas - preCostT fork c0 cB c10 cU -
      (callGasT fork gas c0 cB c10 cU (callRT substate state message r)).cost)
    {A : Prop}
    (hans : ∀ caller msg lt child, runChild caller msg lt = .ok child →
      SendsVia message (upAddr state message) c r (dataT message) msg →
        (child.1.error = none ↔ A))
    (hnf : NoFail runChild) :
    RunsOk fork bound runChild evm within ↔ TransferDepGuard state message c ∧ A := by
  refine fwd_ok_iff (fun ⟨⟨⟨h4, hv⟩, hsz, hdepth⟩, hp, hb⟩ =>
    (spec_depT ⟨hfork, h4, hsize', hsel, hv, hp, hb, hdep, hcode, hsz, hszl, hroute, hdepth,
      hc0, hcB, hc10, hcU⟩ hg htail).consequence (fun _ h => h)
      fun e ⟨_, _, _, hcal, hfwd, _, _, _, hok, _⟩ hA => halted_false_ok e (hok ((hcal hfwd).2 hA)))
    within ?_ hans hnf start
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

/-- `approve(s, v)` when deprecated succeeds exactly when `ApproveDepGuard` holds and the
forwarded call ends with no error (`A`, by `hans`). -/
theorem approve_dep_ok_iff (hszl : c.size < 2 ^ 256)
    (hg : preCostA fork c10 cU + 100 + callR substate state message r ≤ gas)
    (htail : 53 ≤ gas - preCostA fork c10 cU -
      (callGasA fork gas c10 cU (callR substate state message r)).cost)
    {A : Prop}
    (hans : ∀ caller msg lt child, runChild caller msg lt = .ok child →
      SendsVia message (upAddr state message) c r (dataA message) msg →
        (child.1.error = none ↔ A))
    (hnf : NoFail runChild) :
    RunsOk fork bound runChild evm within ↔ ApproveDepGuard message c ∧ A := by
  refine fwd_ok_iff (fun ⟨⟨⟨_, hv⟩, hsz, hdepth⟩, hl⟩ =>
    (spec_depA ⟨hfork, hl, hsize', hsel, hv, hdep, hcode, hsz, hszl, hroute, hdepth, hc10, hcU⟩
      hg htail).consequence (fun _ h => h)
      fun e ⟨_, _, _, hcal, hfwd, _, _, _, hok, _⟩ hA => halted_false_ok e (hok ((hcal hfwd).2 hA)))
    within ?_ hans hnf start
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
        (child.1.error = none ↔ A))
    (hnf : NoFail runChild) :
    RunsOk fork bound runChild evm within ↔ TransferFromDepGuard state message c ∧ A := by
  refine fwd_ok_iff (fun ⟨⟨⟨h4, hv⟩, hsz, hdepth⟩, hp, hb⟩ =>
    (spec_depF ⟨hfork, h4, hsize', hsel, hv, hp, hb, hdep, hcode, hsz, hszl, hroute, hdepth,
      hc0, hcB, hc10, hcU⟩ hg htail).consequence (fun _ h => h)
      fun e ⟨_, _, _, hcal, hfwd, _, _, _, hok, _⟩ hA => halted_false_ok e (hok ((hcal hfwd).2 hA)))
    within ?_ hans hnf start
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

/-- `destroyBlackFunds(a)` when deprecated succeeds exactly when `DestroyDepGuard` holds and the
forwarded `balanceOf(a)` ends with no error in a state where the contract has an account (`A`, by
`hans`). -/
theorem destroyBlackFunds_dep_ok_iff (hszl : c.size < 2 ^ 256)
    (hg : preCostD fork c0 cL c10 cU + 100 + callRD substate state message r ≤ gas)
    (htail : TAIL_MAX fork ≤ gas - preCostD fork c0 cL c10 cU -
      (callGasD fork gas c0 cL c10 cU (callRD substate state message r)).cost)
    {A : Prop}
    (hans : ∀ caller msg lt child, runChild caller msg lt = .ok child →
      SendsVia message (upAddr state message) c r (dataB message) msg →
        (child.1.error = none ∧ hasAccount child.1.state message.currentTarget ↔ A))
    (hnf : NoFail runChild) :
    RunsOk fork bound runChild evm within ↔ DestroyDepGuard state message c ∧ A := by
  constructor
  · rintro ⟨s, hs, hok⟩
    obtain ⟨h4, hv, -⟩ := runFrame_ok_dispatch hfork hsize' start within hs hok
    obtain ⟨c', r', hcode', hroute', hown, hl, hw, -, hdepth, caller, msg, lt, child, hch, he, hst,
      hacc, hfwd, -⟩ := dep_destroy_complete hfork hsize' hsel hdep hc0 hcL hc10 hcU start within hs hok
    obtain rfl := code_eq hcode hcode'
    obtain rfl := routes_unique hroute' hroute
    exact ⟨⟨⟨⟨h4, hv⟩, size_pos_of hw, hdepth⟩, hown, hl, hst⟩,
      (hans caller msg lt child hch hfwd).1 ⟨he, hacc⟩⟩
  · rintro ⟨⟨⟨⟨h4, hv⟩, hsz, hdepth⟩, hown, hl, hst⟩, hA⟩
    let callee : Evm fork Nat → Message fork → Evm fork Nat → Prop := fun _ msg child =>
      SendsVia message (upAddr state message) c r (dataB message) msg →
        child.error = none ∧ hasAccount child.state message.currentTarget
    have meets : Meets callee runChild :=
      ⟨fun caller msg lt child hch hfwd => (hans caller msg lt child hch hfwd).2 hA,
        fun caller msg lt e h => absurd h (hnf caller msg lt e)⟩
    exact runsOk_of_specUnder
      (spec_depD (callee := callee) hfork hst h4 hsize' hsel hv hown hl hdep hcode hsz hszl hroute
        hdepth hc0 hcL hc10 hcU hg htail fun _ _ _ hcal hfwd _ => (hcal hfwd).2)
      meets hnf (fun e ⟨_, _, _, hcal, hfwd, _, _, _, hok, _⟩ =>
        halted_false_ok e (hok (hcal hfwd).1)) start within

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
