import UsdtVerify.Usdt.Sanity.Process

/-!
# Sanity: the deprecated exact theorems under EthLib's `processRunner` (rounds 29, 30)

docs/AUDIT.md, finding 3. The deprecated exact theorems took `NoFail` (the runner fails on no
message at all), false for `processRunner`; since round 29 they take `NoFailOn` the messages their
path sends (`SendsVia`). Their `hans` asked one answer `A` of every forwarded message whatever
its gas, so the `_gas` and `_fails` forms could not be met by `processRunner` for a code whose
outcome depends on the gas. Since round 30, `hans` is asked only of the message the CALL sends
with the gas it gives, from the caller frame of the CALL (`CallFrom`), so `A` can depend on that
gas.

Here the upgraded address holds the one byte STOP (`STOP_CODE`) and is no precompile, from Paris:

- `process_stop_child`: every message the path sends ends under `processRunner` with no error, all
  its gas, the caller's state, the caller's substate as `Substate.child` passes it on, and no
  output;
- `noFailOn_process_stop`: so `processRunner` meets `NoFailOn`;
- `hans_process_stop`: the `hans` of the six `X_dep_ok_iff` with `A = True`;
  `hans_gas_process_stop`: the `hans` of the six `X_dep_ok_iff_gas` with `A` the bound
  `T ≤ K + g` on the gas `g` the CALL gives; `hans_destroy_process_stop`,
  `hans_destroy_gas_process_stop`: the same for destroyBlackFunds, with `A` stated over the
  state and substate of the caller frame at the CALL;
- `X_dep_ok_iff_process_stop` (the seven forwards) and
  `X_dep_ok_iff_gas_process_stop` (the seven): the instances. With the gas of `hg` (and `htail`
  for the first form), a deprecated run under `processRunner` succeeds iff the checks hold (and,
  in the gas-exact form, the gas the CALL gives covers the code after it).
-/

namespace UsdtVerify.Sanity

open EthLib.Base (Fork U256 Address)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open Exact Complete Deprecated DeprecatedBalance DeprecatedAllowance DeprecatedTransfer
open DeprecatedTransferFrom DeprecatedDestroy Transfer TransferFrom Owner BlackList DestroySpec

variable {fork : Fork}

theorem precompile_none_of {msg : Message fork} {ua : Address}
    (hnp : Precompiles.isPrecompile fork ua.toU256.toNat = false)
    (hca : msg.codeAddress = some ua) : precompileAddress fork msg = none := by
  simp only [precompileAddress, hca, hnp]; rfl

/-- From Paris, a message that a deprecated path sends to an upgraded address holding STOP (no
precompile) ends under `processRunner` with no error, with all its gas, the caller's state, the
caller's substate as `Substate.child` passes it on, and no output. -/
theorem process_stop_child (hparis : .paris ≤ fork) {bound : Nat} {message : Message fork}
    {S : State.TransactionState} {ua : Address} {r : Route} {d : ByteArray}
    (hroute : Routes fork S STOP_CODE r)
    (hnp : Precompiles.isPrecompile fork ua.toU256.toNat = false)
    (caller : Evm fork Nat) {msg : Message fork} (lt : msg.gas < bound)
    (hs : SendsVia message ua STOP_CODE r d msg) :
    ∃ child, processRunner fork bound caller msg lt = .ok child ∧ child.1.error = none ∧
      child.1.gas = msg.gas ∧ child.1.state = caller.state ∧
      child.1.substate = caller.substate.child ∧ child.1.output = .empty := by
  rcases r with _ | ⟨dl, c'⟩
  · obtain ⟨-, -, htg, hca, hmc, -, -, hval, -, -⟩ := hs
    have hpre := precompile_none_of (fork := fork) hnp hca
    have hst : startState fork msg caller.state = caller.state := by
      simp only [startState, show ¬fork < Fork.paris from Nat.not_lt.mpr hparis, ite_false]
    have hspec := stop (fork := fork) (code := STOP_CODE) (message := msg) (pc := 0)
      (stack := []) (memory := .empty) (gas := msg.gas) (state := caller.state)
      (substate := caller.substate.child) (by decide) rfl
    obtain ⟨stopped, hq, hmap⟩ := processMessage_of_spec (message := msg) (state := caller.state)
      (substate := caller.substate.child) hspec (fun h => h.2 hval) hpre
      (by rw [hst]; exact at_startFrame hmc _ _)
    have hp : processRunner fork bound caller msg lt =
        processMessage fork msg caller.state caller.substate.child := by
      simp only [processRunner, htg]
    rw [← hp] at hmap
    obtain ⟨-, herr, hout, hgas, hsta, hsub⟩ := hq
    have herr' : stopped.error = none := by simpa using herr
    rw [rollbackOnError_of_error_eq_none herr'] at hmap
    cases hpm : processRunner fork bound caller msg lt with
    | error e => rw [hpm] at hmap; cases hmap
    | ok ended =>
      rw [hpm] at hmap
      have he : ended.1 = stopped := by simpa [Except.map] using hmap
      exact ⟨ended, rfl, by rw [he]; exact herr', by rw [he, hgas], by rw [he, hsta],
        by rw [he, hsub], by rw [he, hout]⟩
  · exact absurd hroute.2.1 (by rw [delegatedAddress_stop]; exact fun h => by cases h)

/-- From Paris, a message that a deprecated path sends to an upgraded address holding STOP (no
precompile) ends under `processRunner` with no error. -/
theorem process_stop_sends (hparis : .paris ≤ fork) {bound : Nat} {message : Message fork}
    {S : State.TransactionState} {ua : Address} {r : Route} {d : ByteArray}
    (hroute : Routes fork S STOP_CODE r)
    (hnp : Precompiles.isPrecompile fork ua.toU256.toNat = false)
    (caller : Evm fork Nat) {msg : Message fork} (lt : msg.gas < bound)
    (hs : SendsVia message ua STOP_CODE r d msg) :
    ∃ child, processRunner fork bound caller msg lt = .ok child ∧ child.1.error = none :=
  let ⟨child, hc, he, _⟩ := process_stop_child hparis hroute hnp caller lt hs
  ⟨child, hc, he⟩

theorem noFailOn_process_stop (hparis : .paris ≤ fork) {bound : Nat} {message : Message fork}
    {S : State.TransactionState} {ua : Address} {r : Route} {d : ByteArray}
    (hroute : Routes fork S STOP_CODE r)
    (hnp : Precompiles.isPrecompile fork ua.toU256.toNat = false)
    {Cl : Evm fork Nat → Message fork → Prop} :
    NoFailOn (processRunner fork bound)
      (fun caller msg => SendsVia message ua STOP_CODE r d msg ∧ Cl caller msg) := by
  intro caller msg lt e hs h
  obtain ⟨child, hc, -⟩ := process_stop_sends hparis hroute hnp caller lt hs.1
  rw [hc] at h; cases h

/-- The `hans` of the six `X_dep_ok_iff` (round 30 form, with `CallFrom`), `A = True`. -/
theorem hans_process_stop (hparis : .paris ≤ fork) {bound : Nat} {message : Message fork}
    {S : State.TransactionState} {ua : Address} {r : Route} {d : ByteArray}
    (hroute : Routes fork S STOP_CODE r)
    (hnp : Precompiles.isPrecompile fork ua.toU256.toNat = false)
    {g : Nat} {st : State.TransactionState} {ss : Substate} :
    ∀ caller msg lt child, processRunner fork bound caller msg lt = .ok child →
      SendsVia message ua STOP_CODE r d msg → CallFrom g st ss caller msg →
      (child.1.error = none ↔ True) := by
  intro caller msg lt child hch hs _
  obtain ⟨child', hc, he, -⟩ := process_stop_child hparis hroute hnp caller lt hs
  rw [hc] at hch; cases hch
  exact ⟨fun _ => trivial, fun _ => he⟩

/-- The `hans` of the six `X_dep_ok_iff_gas` (round 30 form): with STOP the forwarded message
keeps all its gas `g`, so the condition "no error and `T ≤ K` plus the gas left" is `T ≤ K + g`. -/
theorem hans_gas_process_stop (hparis : .paris ≤ fork) {bound : Nat} {message : Message fork}
    {S : State.TransactionState} {ua : Address} {r : Route} {d : ByteArray}
    (hroute : Routes fork S STOP_CODE r)
    (hnp : Precompiles.isPrecompile fork ua.toU256.toNat = false)
    {g : Nat} {st : State.TransactionState} {ss : Substate} (T K : Nat) :
    ∀ caller msg lt child, processRunner fork bound caller msg lt = .ok child →
      SendsVia message ua STOP_CODE r d msg → CallFrom g st ss caller msg →
      (child.1.error = none ∧ T ≤ K + child.1.gas ↔ T ≤ K + g) := by
  rintro caller msg lt child hch hs ⟨hg, -, -⟩
  obtain ⟨child', hc, he, hgas, -⟩ := process_stop_child hparis hroute hnp caller lt hs
  rw [hc] at hch; cases hch
  rw [hgas, ← hg]
  exact ⟨fun h => h.2, fun h => ⟨he, h⟩⟩

/-- The `hans` of `destroyBlackFunds_dep_ok_iff`: with STOP the forwarded message ends with no
error in the caller's state, so `A` is "the caller state at the CALL has an account of `C`". -/
theorem hans_destroy_process_stop (hparis : .paris ≤ fork) {bound : Nat}
    {message : Message fork} {S : State.TransactionState} {ua : Address} {r : Route}
    {d : ByteArray} (hroute : Routes fork S STOP_CODE r)
    (hnp : Precompiles.isPrecompile fork ua.toU256.toNat = false)
    {g : Nat} {st : State.TransactionState} {ss : Substate} (C : Address) :
    ∀ caller msg lt child, processRunner fork bound caller msg lt = .ok child →
      SendsVia message ua STOP_CODE r d msg → CallFrom g st ss caller msg →
      (child.1.error = none ∧ hasAccount child.1.state C ↔ hasAccount st C) := by
  rintro caller msg lt child hch hs ⟨-, hcs, -⟩
  obtain ⟨child', hc, he, -, hsta, -⟩ := process_stop_child hparis hroute hnp caller lt hs
  rw [hc] at hch; cases hch
  rw [hsta, hcs]
  exact ⟨fun h => h.2, fun h => ⟨he, h⟩⟩

theorem incorporate_keys (caller child : Evm fork Nat) (he : child.error = none) :
    (incorporateChild fork caller child).substate.accessedStorageKeys =
      child.substate.accessedStorageKeys := by
  simp [incorporateChild, he]

theorem coldIn_congr {X Y : Substate} (h : X.accessedStorageKeys = Y.accessedStorageKeys)
    (C : Address) (n : U256) : coldIn X C n = coldIn Y C n := by
  simp only [coldIn, h]

theorem coldIn_accessSlot_congr {X Y : Substate}
    (h : X.accessedStorageKeys = Y.accessedStorageKeys) (C C' : Address) (n m : U256) :
    coldIn (accessSlot X C n) C' m = coldIn (accessSlot Y C n) C' m := by
  simp only [coldIn, h]

/-- The `hans` of `destroyBlackFunds_dep_ok_iff_gas` (round 30 form): with STOP the forwarded
message ends with no error, all its gas `g`, no output, the caller's state `st` and the caller's
accesses, so `A` is the condition stated over `st`, the accesses of `ss`, the empty output and
`g`. -/
theorem hans_destroy_gas_process_stop (hparis : .paris ≤ fork) {bound : Nat}
    {message : Message fork} {S : State.TransactionState} {ua : Address} {r : Route}
    {d : ByteArray} (hroute : Routes fork S STOP_CODE r)
    (hnp : Precompiles.isPrecompile fork ua.toU256.toNat = false)
    {g : Nat} {st : State.TransactionState} {ss : Substate} (C : Address) (a n : U256)
    (M : ByteArray) (K : Nat) :
    ∀ caller msg lt child, processRunner fork bound caller msg lt = .ok child →
      SendsVia message ua STOP_CODE r d msg → CallFrom g st ss caller msg →
      (child.1.error = none ∧ hasAccount child.1.state C ∧
          max (tailCost fork (incorporateChild fork caller child.1).state C a
              (resWord (outMemOf M child.1.output))
              (coldIn (incorporateChild fork caller child.1).substate C n)
              (coldIn (accessSlot (incorporateChild fork caller child.1).substate C n) C 1))
            (tailStip fork (incorporateChild fork caller child.1).state C a
              (coldIn (incorporateChild fork caller child.1).substate C n)
              (coldIn (accessSlot (incorporateChild fork caller child.1).substate C n) C 1)) ≤
            K + child.1.gas ↔
        hasAccount st C ∧
          max (tailCost fork st C a (resWord (outMemOf M .empty)) (coldIn ss C n)
              (coldIn (accessSlot ss C n) C 1))
            (tailStip fork st C a (coldIn ss C n) (coldIn (accessSlot ss C n) C 1)) ≤ K + g) := by
  rintro caller msg lt child hch hs ⟨hg, hcs, hcss⟩
  obtain ⟨child', hc, he, hgas, hsta, hsub, hout⟩ := process_stop_child hparis hroute hnp caller lt hs
  have hcc : child' = child := Except.ok.inj (hc.symm.trans hch)
  rw [hcc] at he hgas hsta hsub hout
  have hk : (incorporateChild fork caller child.1).substate.accessedStorageKeys =
      ss.accessedStorageKeys := by
    rw [incorporate_keys _ _ he, hsub, ← hcss]; rfl
  have hst : (incorporateChild fork caller child.1).state = st := by
    rw [← hcs, ← hsta]; unfold incorporateChild; split <;> rfl
  rw [coldIn_congr hk, coldIn_accessSlot_congr hk, hst, hout, hgas, ← hg, hsta, hcs]
  exact ⟨fun h => h.2, fun h => ⟨he, h⟩⟩

/-- **Deprecated totalSupply under `processRunner`.** From Paris, with the upgraded address holding STOP
(no precompile), the gas of `hg` and `htail`, and the other hypotheses of
`Exact.totalSupply_dep_ok_iff`: the run succeeds iff the checks hold. -/
theorem totalSupply_dep_ok_iff_process_stop (hparis : .paris ≤ fork)
    {message : Message fork} {state : State.TransactionState} {substate : Substate}
    {gas bound : Nat} {evm : Evm fork Nat}
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x18160ddd)
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0)
    (hcode : state.getCode (state.getAccount (upAddr state message)).codeHash = .ok STOP_CODE)
    {r : Route} (hroute : Routes fork state STOP_CODE r) {c10 cU : Bool}
    (hc10 : coldIn substate message.currentTarget 10 = c10)
    (hcU : decide (upAddr state message ∉ substate.accessedAddresses) = cU)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hnp : Precompiles.isPrecompile fork (upAddr state message).toU256.toNat = false)
    (hg : preCost fork c10 cU + 100 + callR substate state message r ≤ gas)
    (htail : 121 ≤ gas - preCost fork c10 cU - (callGas fork gas c10 cU (callR substate state message r)).cost) :
    RunsOk fork bound (processRunner fork bound) evm within ↔ ForwardOk message STOP_CODE := by
  have h := Exact.totalSupply_dep_ok_iff (Nat.le_trans (by decide) hparis) hsize' hsel hdep hcode
    hroute hc10 hcU start within (by decide) hg htail (hans_process_stop hparis hroute hnp)
    (noFailOn_process_stop hparis hroute hnp)
  rw [h, and_true]

/-- **Deprecated totalSupply under `processRunner`, every gas from `hg` on (round 30).** The same,
with `hg` only: the run succeeds iff the checks hold and the gas left after the CALL plus the
gas the CALL gives (all of which STOP returns) is at least the 121 gas of the code after the
CALL. -/
theorem totalSupply_dep_ok_iff_gas_process_stop (hparis : .paris ≤ fork)
    {message : Message fork} {state : State.TransactionState} {substate : Substate}
    {gas bound : Nat} {evm : Evm fork Nat}
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x18160ddd)
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0)
    (hcode : state.getCode (state.getAccount (upAddr state message)).codeHash = .ok STOP_CODE)
    {r : Route} (hroute : Routes fork state STOP_CODE r) {c10 cU : Bool}
    (hc10 : coldIn substate message.currentTarget 10 = c10)
    (hcU : decide (upAddr state message ∉ substate.accessedAddresses) = cU)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hnp : Precompiles.isPrecompile fork (upAddr state message).toU256.toNat = false)
    (hg : preCost fork c10 cU + 100 + callR substate state message r ≤ gas) :
    RunsOk fork bound (processRunner fork bound) evm within ↔ ForwardOk message STOP_CODE ∧
      121 ≤ gas - preCost fork c10 cU - (callGas fork gas c10 cU (callR substate state message r)).cost +
        (callGas fork gas c10 cU (callR substate state message r)).subCall :=
  Exact.totalSupply_dep_ok_iff_gas (Nat.le_trans (by decide) hparis) hsize' hsel hdep hcode
    hroute hc10 hcU start within (by decide) hg (hans_gas_process_stop hparis hroute hnp _ _)
    (noFailOn_process_stop hparis hroute hnp)

/-- **Deprecated balanceOf under `processRunner`.** From Paris, with the upgraded address holding STOP
(no precompile), the gas of `hg` and `htail`, and the other hypotheses of
`Exact.balanceOf_dep_ok_iff`: the run succeeds iff the checks hold. -/
theorem balanceOf_dep_ok_iff_process_stop (hparis : .paris ≤ fork)
    {message : Message fork} {state : State.TransactionState} {substate : Substate}
    {gas bound : Nat} {evm : Evm fork Nat}
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x70a08231)
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0)
    (hcode : state.getCode (state.getAccount (upAddr state message)).codeHash = .ok STOP_CODE)
    {r : Route} (hroute : Routes fork state STOP_CODE r) {c10 cU : Bool}
    (hc10 : coldIn substate message.currentTarget 10 = c10)
    (hcU : decide (upAddr state message ∉ substate.accessedAddresses) = cU)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hnp : Precompiles.isPrecompile fork (upAddr state message).toU256.toNat = false)
    (hg : preCostB fork c10 cU + 100 + callR substate state message r ≤ gas)
    (htail : 126 ≤ gas - preCostB fork c10 cU - (callGasB fork gas c10 cU (callR substate state message r)).cost) :
    RunsOk fork bound (processRunner fork bound) evm within ↔ ForwardOk message STOP_CODE := by
  have h := Exact.balanceOf_dep_ok_iff (Nat.le_trans (by decide) hparis) hsize' hsel hdep hcode
    hroute hc10 hcU start within (by decide) hg htail (hans_process_stop hparis hroute hnp)
    (noFailOn_process_stop hparis hroute hnp)
  rw [h, and_true]

/-- **Deprecated balanceOf under `processRunner`, every gas from `hg` on (round 30).** The same,
with `hg` only: the run succeeds iff the checks hold and the gas left after the CALL plus the
gas the CALL gives (all of which STOP returns) is at least the 126 gas of the code after the
CALL. -/
theorem balanceOf_dep_ok_iff_gas_process_stop (hparis : .paris ≤ fork)
    {message : Message fork} {state : State.TransactionState} {substate : Substate}
    {gas bound : Nat} {evm : Evm fork Nat}
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x70a08231)
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0)
    (hcode : state.getCode (state.getAccount (upAddr state message)).codeHash = .ok STOP_CODE)
    {r : Route} (hroute : Routes fork state STOP_CODE r) {c10 cU : Bool}
    (hc10 : coldIn substate message.currentTarget 10 = c10)
    (hcU : decide (upAddr state message ∉ substate.accessedAddresses) = cU)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hnp : Precompiles.isPrecompile fork (upAddr state message).toU256.toNat = false)
    (hg : preCostB fork c10 cU + 100 + callR substate state message r ≤ gas) :
    RunsOk fork bound (processRunner fork bound) evm within ↔ ForwardOk message STOP_CODE ∧
      126 ≤ gas - preCostB fork c10 cU - (callGasB fork gas c10 cU (callR substate state message r)).cost +
        (callGasB fork gas c10 cU (callR substate state message r)).subCall :=
  Exact.balanceOf_dep_ok_iff_gas (Nat.le_trans (by decide) hparis) hsize' hsel hdep hcode
    hroute hc10 hcU start within (by decide) hg (hans_gas_process_stop hparis hroute hnp _ _)
    (noFailOn_process_stop hparis hroute hnp)

/-- **Deprecated allowance under `processRunner`.** From Paris, with the upgraded address holding STOP
(no precompile), the gas of `hg` and `htail`, and the other hypotheses of
`Exact.allowance_dep_ok_iff`: the run succeeds iff the checks hold. -/
theorem allowance_dep_ok_iff_process_stop (hparis : .paris ≤ fork)
    {message : Message fork} {state : State.TransactionState} {substate : Substate}
    {gas bound : Nat} {evm : Evm fork Nat}
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xdd62ed3e)
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0)
    (hcode : state.getCode (state.getAccount (upAddr state message)).codeHash = .ok STOP_CODE)
    {r : Route} (hroute : Routes fork state STOP_CODE r) {c10 cU : Bool}
    (hc10 : coldIn substate message.currentTarget 10 = c10)
    (hcU : decide (upAddr state message ∉ substate.accessedAddresses) = cU)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hnp : Precompiles.isPrecompile fork (upAddr state message).toU256.toNat = false)
    (hg : preCostAl fork c10 cU + 100 + callR substate state message r ≤ gas)
    (htail : 128 ≤ gas - preCostAl fork c10 cU - (callGasAl fork gas c10 cU (callR substate state message r)).cost) :
    RunsOk fork bound (processRunner fork bound) evm within ↔ ForwardOk message STOP_CODE := by
  have h := Exact.allowance_dep_ok_iff (Nat.le_trans (by decide) hparis) hsize' hsel hdep hcode
    hroute hc10 hcU start within (by decide) hg htail (hans_process_stop hparis hroute hnp)
    (noFailOn_process_stop hparis hroute hnp)
  rw [h, and_true]

/-- **Deprecated allowance under `processRunner`, every gas from `hg` on (round 30).** The same,
with `hg` only: the run succeeds iff the checks hold and the gas left after the CALL plus the
gas the CALL gives (all of which STOP returns) is at least the 128 gas of the code after the
CALL. -/
theorem allowance_dep_ok_iff_gas_process_stop (hparis : .paris ≤ fork)
    {message : Message fork} {state : State.TransactionState} {substate : Substate}
    {gas bound : Nat} {evm : Evm fork Nat}
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xdd62ed3e)
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0)
    (hcode : state.getCode (state.getAccount (upAddr state message)).codeHash = .ok STOP_CODE)
    {r : Route} (hroute : Routes fork state STOP_CODE r) {c10 cU : Bool}
    (hc10 : coldIn substate message.currentTarget 10 = c10)
    (hcU : decide (upAddr state message ∉ substate.accessedAddresses) = cU)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hnp : Precompiles.isPrecompile fork (upAddr state message).toU256.toNat = false)
    (hg : preCostAl fork c10 cU + 100 + callR substate state message r ≤ gas) :
    RunsOk fork bound (processRunner fork bound) evm within ↔ ForwardOk message STOP_CODE ∧
      128 ≤ gas - preCostAl fork c10 cU - (callGasAl fork gas c10 cU (callR substate state message r)).cost +
        (callGasAl fork gas c10 cU (callR substate state message r)).subCall :=
  Exact.allowance_dep_ok_iff_gas (Nat.le_trans (by decide) hparis) hsize' hsel hdep hcode
    hroute hc10 hcU start within (by decide) hg (hans_gas_process_stop hparis hroute hnp _ _)
    (noFailOn_process_stop hparis hroute hnp)

/-- **Deprecated transfer under `processRunner`.** From Paris, with the upgraded address holding STOP
(no precompile), the gas of `hg` and `htail`, and the other hypotheses of
`Exact.transfer_dep_ok_iff`: the run succeeds iff the checks hold. -/
theorem transfer_dep_ok_iff_process_stop (hparis : .paris ≤ fork)
    {message : Message fork} {state : State.TransactionState} {substate : Substate}
    {gas bound : Nat} {evm : Evm fork Nat}
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xa9059cbb)
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0)
    (hcode : state.getCode (state.getAccount (upAddr state message)).codeHash = .ok STOP_CODE)
    {r : Route} (hroute : Routes fork state STOP_CODE r) {c0 cB c10 cU : Bool}
    (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hcB : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget
      (blackSlot message) = cB)
    (hc10 : coldIn (accessSlot (accessSlot substate message.currentTarget 0) message.currentTarget
      (blackSlot message)) message.currentTarget 10 = c10)
    (hcU : decide (upAddr state message ∉ substate.accessedAddresses) = cU)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hnp : Precompiles.isPrecompile fork (upAddr state message).toU256.toNat = false)
    (hg : preCostT fork c0 cB c10 cU + 100 + callRT substate state message r ≤ gas)
    (htail : 51 ≤ gas - preCostT fork c0 cB c10 cU - (callGasT fork gas c0 cB c10 cU (callRT substate state message r)).cost) :
    RunsOk fork bound (processRunner fork bound) evm within ↔ TransferDepGuard state message STOP_CODE := by
  have h := Exact.transfer_dep_ok_iff (Nat.le_trans (by decide) hparis) hsize' hsel hdep hcode
    hroute hc0 hcB hc10 hcU start within (by decide) hg htail (hans_process_stop hparis hroute hnp)
    (noFailOn_process_stop hparis hroute hnp)
  rw [h, and_true]

/-- **Deprecated transfer under `processRunner`, every gas from `hg` on (round 30).** The same,
with `hg` only: the run succeeds iff the checks hold and the gas left after the CALL plus the
gas the CALL gives (all of which STOP returns) is at least the 51 gas of the code after the
CALL. -/
theorem transfer_dep_ok_iff_gas_process_stop (hparis : .paris ≤ fork)
    {message : Message fork} {state : State.TransactionState} {substate : Substate}
    {gas bound : Nat} {evm : Evm fork Nat}
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xa9059cbb)
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0)
    (hcode : state.getCode (state.getAccount (upAddr state message)).codeHash = .ok STOP_CODE)
    {r : Route} (hroute : Routes fork state STOP_CODE r) {c0 cB c10 cU : Bool}
    (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hcB : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget
      (blackSlot message) = cB)
    (hc10 : coldIn (accessSlot (accessSlot substate message.currentTarget 0) message.currentTarget
      (blackSlot message)) message.currentTarget 10 = c10)
    (hcU : decide (upAddr state message ∉ substate.accessedAddresses) = cU)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hnp : Precompiles.isPrecompile fork (upAddr state message).toU256.toNat = false)
    (hg : preCostT fork c0 cB c10 cU + 100 + callRT substate state message r ≤ gas) :
    RunsOk fork bound (processRunner fork bound) evm within ↔ TransferDepGuard state message STOP_CODE ∧
      51 ≤ gas - preCostT fork c0 cB c10 cU - (callGasT fork gas c0 cB c10 cU (callRT substate state message r)).cost +
        (callGasT fork gas c0 cB c10 cU (callRT substate state message r)).subCall :=
  Exact.transfer_dep_ok_iff_gas (Nat.le_trans (by decide) hparis) hsize' hsel hdep hcode
    hroute hc0 hcB hc10 hcU start within (by decide) hg (hans_gas_process_stop hparis hroute hnp _ _)
    (noFailOn_process_stop hparis hroute hnp)

/-- **Deprecated approve under `processRunner`.** From Paris, with the upgraded address holding STOP
(no precompile), the gas of `hg` and `htail`, and the other hypotheses of
`Exact.approve_dep_ok_iff`: the run succeeds iff the checks hold. -/
theorem approve_dep_ok_iff_process_stop (hparis : .paris ≤ fork)
    {message : Message fork} {state : State.TransactionState} {substate : Substate}
    {gas bound : Nat} {evm : Evm fork Nat}
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x095ea7b3)
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0)
    (hcode : state.getCode (state.getAccount (upAddr state message)).codeHash = .ok STOP_CODE)
    {r : Route} (hroute : Routes fork state STOP_CODE r) {c10 cU : Bool}
    (hc10 : coldIn substate message.currentTarget 10 = c10)
    (hcU : decide (upAddr state message ∉ substate.accessedAddresses) = cU)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hnp : Precompiles.isPrecompile fork (upAddr state message).toU256.toNat = false)
    (hg : preCostA fork c10 cU + 100 + callR substate state message r ≤ gas)
    (htail : 53 ≤ gas - preCostA fork c10 cU - (callGasA fork gas c10 cU (callR substate state message r)).cost) :
    RunsOk fork bound (processRunner fork bound) evm within ↔ ApproveDepGuard message STOP_CODE := by
  have h := Exact.approve_dep_ok_iff (Nat.le_trans (by decide) hparis) hsize' hsel hdep hcode
    hroute hc10 hcU start within (by decide) hg htail (hans_process_stop hparis hroute hnp)
    (noFailOn_process_stop hparis hroute hnp)
  rw [h, and_true]

/-- **Deprecated approve under `processRunner`, every gas from `hg` on (round 30).** The same,
with `hg` only: the run succeeds iff the checks hold and the gas left after the CALL plus the
gas the CALL gives (all of which STOP returns) is at least the 53 gas of the code after the
CALL. -/
theorem approve_dep_ok_iff_gas_process_stop (hparis : .paris ≤ fork)
    {message : Message fork} {state : State.TransactionState} {substate : Substate}
    {gas bound : Nat} {evm : Evm fork Nat}
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x095ea7b3)
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0)
    (hcode : state.getCode (state.getAccount (upAddr state message)).codeHash = .ok STOP_CODE)
    {r : Route} (hroute : Routes fork state STOP_CODE r) {c10 cU : Bool}
    (hc10 : coldIn substate message.currentTarget 10 = c10)
    (hcU : decide (upAddr state message ∉ substate.accessedAddresses) = cU)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hnp : Precompiles.isPrecompile fork (upAddr state message).toU256.toNat = false)
    (hg : preCostA fork c10 cU + 100 + callR substate state message r ≤ gas) :
    RunsOk fork bound (processRunner fork bound) evm within ↔ ApproveDepGuard message STOP_CODE ∧
      53 ≤ gas - preCostA fork c10 cU - (callGasA fork gas c10 cU (callR substate state message r)).cost +
        (callGasA fork gas c10 cU (callR substate state message r)).subCall :=
  Exact.approve_dep_ok_iff_gas (Nat.le_trans (by decide) hparis) hsize' hsel hdep hcode
    hroute hc10 hcU start within (by decide) hg (hans_gas_process_stop hparis hroute hnp _ _)
    (noFailOn_process_stop hparis hroute hnp)

/-- **Deprecated transferFrom under `processRunner`.** From Paris, with the upgraded address holding STOP
(no precompile), the gas of `hg` and `htail`, and the other hypotheses of
`Exact.transferFrom_dep_ok_iff`: the run succeeds iff the checks hold. -/
theorem transferFrom_dep_ok_iff_process_stop (hparis : .paris ≤ fork)
    {message : Message fork} {state : State.TransactionState} {substate : Substate}
    {gas bound : Nat} {evm : Evm fork Nat}
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x23b872dd)
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0)
    (hcode : state.getCode (state.getAccount (upAddr state message)).codeHash = .ok STOP_CODE)
    {r : Route} (hroute : Routes fork state STOP_CODE r) {c0 cB c10 cU : Bool}
    (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hcB : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget
      (blackFrom (fromArg message)) = cB)
    (hc10 : coldIn (accessSlot (accessSlot substate message.currentTarget 0) message.currentTarget
      (blackFrom (fromArg message))) message.currentTarget 10 = c10)
    (hcU : decide (upAddr state message ∉ substate.accessedAddresses) = cU)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hnp : Precompiles.isPrecompile fork (upAddr state message).toU256.toNat = false)
    (hg : DeprecatedTransferFrom.preCostF fork c0 cB c10 cU + 100 + callRF substate state message r ≤ gas)
    (htail : 53 ≤ gas - DeprecatedTransferFrom.preCostF fork c0 cB c10 cU - (callGasF fork gas c0 cB c10 cU (callRF substate state message r)).cost) :
    RunsOk fork bound (processRunner fork bound) evm within ↔ TransferFromDepGuard state message STOP_CODE := by
  have h := Exact.transferFrom_dep_ok_iff (Nat.le_trans (by decide) hparis) hsize' hsel hdep hcode
    hroute hc0 hcB hc10 hcU start within (by decide) hg htail (hans_process_stop hparis hroute hnp)
    (noFailOn_process_stop hparis hroute hnp)
  rw [h, and_true]

/-- **Deprecated transferFrom under `processRunner`, every gas from `hg` on (round 30).** The same,
with `hg` only: the run succeeds iff the checks hold and the gas left after the CALL plus the
gas the CALL gives (all of which STOP returns) is at least the 53 gas of the code after the
CALL. -/
theorem transferFrom_dep_ok_iff_gas_process_stop (hparis : .paris ≤ fork)
    {message : Message fork} {state : State.TransactionState} {substate : Substate}
    {gas bound : Nat} {evm : Evm fork Nat}
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x23b872dd)
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0)
    (hcode : state.getCode (state.getAccount (upAddr state message)).codeHash = .ok STOP_CODE)
    {r : Route} (hroute : Routes fork state STOP_CODE r) {c0 cB c10 cU : Bool}
    (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hcB : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget
      (blackFrom (fromArg message)) = cB)
    (hc10 : coldIn (accessSlot (accessSlot substate message.currentTarget 0) message.currentTarget
      (blackFrom (fromArg message))) message.currentTarget 10 = c10)
    (hcU : decide (upAddr state message ∉ substate.accessedAddresses) = cU)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hnp : Precompiles.isPrecompile fork (upAddr state message).toU256.toNat = false)
    (hg : DeprecatedTransferFrom.preCostF fork c0 cB c10 cU + 100 + callRF substate state message r ≤ gas) :
    RunsOk fork bound (processRunner fork bound) evm within ↔ TransferFromDepGuard state message STOP_CODE ∧
      53 ≤ gas - DeprecatedTransferFrom.preCostF fork c0 cB c10 cU - (callGasF fork gas c0 cB c10 cU (callRF substate state message r)).cost +
        (callGasF fork gas c0 cB c10 cU (callRF substate state message r)).subCall :=
  Exact.transferFrom_dep_ok_iff_gas (Nat.le_trans (by decide) hparis) hsize' hsel hdep hcode
    hroute hc0 hcB hc10 hcU start within (by decide) hg (hans_gas_process_stop hparis hroute hnp _ _)
    (noFailOn_process_stop hparis hroute hnp)

/-- **Deprecated destroyBlackFunds under `processRunner`, every gas from `hg` on (round 30).**
From Paris, with the upgraded address holding STOP (no precompile) and the hypotheses of
`Exact.destroyBlackFunds_dep_ok_iff_gas`: the run succeeds iff `DestroyDepGuard` holds, the state
of the caller frame at the CALL has an account of the contract, and the gas left after the CALL
plus the gas the CALL gives covers the cost and the stipend bound of the tail, computed over that
state, the accesses of the caller frame at the CALL, and the word read from the empty output. -/
theorem destroyBlackFunds_dep_ok_iff_gas_process_stop (hparis : .paris ≤ fork)
    {message : Message fork} {state : State.TransactionState} {substate : Substate}
    {gas bound : Nat} {evm : Evm fork Nat}
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xf3bdc228)
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0)
    (hcode : state.getCode (state.getAccount (upAddr state message)).codeHash = .ok STOP_CODE)
    {r : Route} (hroute : Routes fork state STOP_CODE r) {c0 cL c10 cU : Bool}
    (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hcL : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget
      (listSlot (addrArg message.data 0)) = cL)
    (hc10 : coldIn (preSub substate message) message.currentTarget 10 = c10)
    (hcU : decide (upAddr state message ∉ substate.accessedAddresses) = cU)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hnp : Precompiles.isPrecompile fork (upAddr state message).toU256.toNat = false)
    (hg : preCostD fork c0 cL c10 cU + 100 + callRD substate state message r ≤ gas) :
    RunsOk fork bound (processRunner fork bound) evm within ↔ DestroyDepGuard state message STOP_CODE ∧
      (hasAccount (atCallState (callStateD state message) (upAddr state message) r
          message.currentTarget) message.currentTarget ∧
        max (tailCost fork (atCallState (callStateD state message) (upAddr state message) r
              message.currentTarget) message.currentTarget (addrArg message.data 0)
              (resWord (outMemOf (memD message) .empty))
              (coldIn (atCallSub (callSubD substate state message) (upAddr state message) r)
                message.currentTarget (balSlot message))
              (coldIn (accessSlot (atCallSub (callSubD substate state message)
                (upAddr state message) r) message.currentTarget (balSlot message))
                message.currentTarget 1))
            (tailStip fork (atCallState (callStateD state message) (upAddr state message) r
              message.currentTarget) message.currentTarget (addrArg message.data 0)
              (coldIn (atCallSub (callSubD substate state message) (upAddr state message) r)
                message.currentTarget (balSlot message))
              (coldIn (accessSlot (atCallSub (callSubD substate state message)
                (upAddr state message) r) message.currentTarget (balSlot message))
                message.currentTarget 1)) ≤
          gas - preCostD fork c0 cL c10 cU -
            (callGasD fork gas c0 cL c10 cU (callRD substate state message r)).cost +
            (callGasD fork gas c0 cL c10 cU (callRD substate state message r)).subCall) :=
  Exact.destroyBlackFunds_dep_ok_iff_gas (Nat.le_trans (by decide) hparis) hsize' hsel hdep hcode
    hroute hc0 hcL hc10 hcU start within (by decide) hg
    (hans_destroy_gas_process_stop hparis hroute hnp _ _ _ _ _)
    (noFailOn_process_stop hparis hroute hnp)

/-- **Deprecated destroyBlackFunds under `processRunner`.** From Paris, with the upgraded address
holding STOP (no precompile), the gas of `hg` and `htail`, and the other hypotheses of
`Exact.destroyBlackFunds_dep_ok_iff`: the run succeeds iff `DestroyDepGuard` holds and the state
of the caller frame at the CALL has an account of the contract. -/
theorem destroyBlackFunds_dep_ok_iff_process_stop (hparis : .paris ≤ fork)
    {message : Message fork} {state : State.TransactionState} {substate : Substate}
    {gas bound : Nat} {evm : Evm fork Nat}
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xf3bdc228)
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0)
    (hcode : state.getCode (state.getAccount (upAddr state message)).codeHash = .ok STOP_CODE)
    {r : Route} (hroute : Routes fork state STOP_CODE r) {c0 cL c10 cU : Bool}
    (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hcL : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget
      (listSlot (addrArg message.data 0)) = cL)
    (hc10 : coldIn (preSub substate message) message.currentTarget 10 = c10)
    (hcU : decide (upAddr state message ∉ substate.accessedAddresses) = cU)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hnp : Precompiles.isPrecompile fork (upAddr state message).toU256.toNat = false)
    (hg : preCostD fork c0 cL c10 cU + 100 + callRD substate state message r ≤ gas)
    (htail : TAIL_MAX fork ≤ gas - preCostD fork c0 cL c10 cU -
      (callGasD fork gas c0 cL c10 cU (callRD substate state message r)).cost) :
    RunsOk fork bound (processRunner fork bound) evm within ↔
      DestroyDepGuard state message STOP_CODE ∧
        hasAccount (atCallState (callStateD state message) (upAddr state message) r
          message.currentTarget) message.currentTarget :=
  Exact.destroyBlackFunds_dep_ok_iff (Nat.le_trans (by decide) hparis) hsize' hsel hdep hcode
    hroute hc0 hcL hc10 hcU start within (by decide) hg htail
    (hans_destroy_process_stop hparis hroute hnp _) (noFailOn_process_stop hparis hroute hnp)

end UsdtVerify.Sanity
