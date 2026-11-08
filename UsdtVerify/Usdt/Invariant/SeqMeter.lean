import UsdtVerify.Usdt.Invariant.Seq
import UsdtVerify.Evm.ProcessMeter
import UsdtVerify.Evm.Shadow

/-!
# The invariant over a finite sequence of calls, over EthLib's EIP-8037 meter

`Usdt/Invariant/Seq.lean` for runs over the meter `StateGasMeter`, when not deprecated (byte 20 of
slot 10 is 0 at the start of the call). These theorems take no hypothesis on the reservoir or on
refills, and none on the gas limit of the transaction: the invariant depends only on the state,
and `shadow_ends` gives, for a run over `StateGasMeter` that ends with no error at any reservoir,
a run of the meter `Nat` with more gas that ends in the same state.

- `inv_call_any`: `inv_call` over `StateGasMeter`, any reservoir, refills allowed.
- `GoodCallS C S S'`: a successful run of a fresh frame of `CODE` over `StateGasMeter`, not
  deprecated, with the hypotheses of `inv_call`.
- `CallsS C`: finite sequences of `GoodCall` (meter `Nat`), `GoodCallS` and `Untouched` steps;
  `inv_callsS`: `Inv C` at the start gives `Inv C` at the end.
- `goodCall_processS`: from Paris, a top-level message to `C` (code `CODE`, no value, no
  precompile, not deprecated) run by EthLib's `processMessage` over `StateGasMeter`, from any
  starting meter, that ends with no error is a `GoodCallS`.
- `process_value_failsS`: from Berlin, such a message with a nonzero value ends with an error.
- `process_stepS`: from Paris, every such message (any value) that `processMessage` ends over
  `StateGasMeter`, from any starting meter, is a `GoodCallS` or an `Untouched` step.
- `goodCall_processS_start`, `process_value_failsS_start`, `process_stepS_start`: the same for
  the fresh meter of the message, which `processMessage` takes by default.

The starting meter is free because EthLib's `processMessageCall` passes the meter left by the
authorizations of the transaction, which is not a fresh meter when they pay state gas.
-/

namespace UsdtVerify.Complete

open EthLib.Base (Fork U256 Address)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open UsdtVerify.Gas
open UsdtVerify.Meter
open UsdtVerify.Shadow
open UsdtVerify.ProcessMeter
open Invariant Deprecated

/-- **Every successful call keeps the invariant, over the EIP-8037 meter, at any reservoir**
(not deprecated). `inv_call` for a run of the interpreter loop over `StateGasMeter`, for any gas
bound and message runner, from a frame `m` whose `toNat` is the fresh frame of `CODE`. No
hypothesis on the reservoir of `m` or on refills. -/
theorem inv_call_any {fork : Fork} {message : Message fork} {state : State.TransactionState}
    {substate : Substate} {bound : Nat} {runChild : MessageRunner fork StateGasMeter bound}
    {m s : Evm fork StateGasMeter} {gas : Nat}
    (K : SepOn (callKeys message state)) (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    (h7 : StrForm (storageAt state message.currentTarget 7))
    (h8 : StrForm (storageAt state message.currentTarget 8))
    (hI : Inv message.currentTarget state)
    (start : At CODE message 0 [] .empty gas state substate (toNat m))
    {within : GasMeter.gasHeld m.gas ≤ bound}
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild m within = .ok s)
    (hok : s.error = none) : Inv message.currentTarget s.state := by
  obtain ⟨G, hE⟩ := shadow_ends hfork hrun hok
  exact inv_call (s := { toNat s with gas := G }) K hfork hsize' hdep h7 h8 hI
    (at_sh start (budget m)) hE hok

/-- One successful run of `CODE` over `StateGasMeter` for a message to `C`, from `S` to `S'`, not
deprecated, under the hypotheses of `inv_call_any`. -/
def GoodCallS (C : Address) (S S' : State.TransactionState) : Prop :=
  ∃ (fork : Fork) (message : Message fork) (substate : Substate) (gas bound : Nat)
    (runChild : MessageRunner fork StateGasMeter bound) (m s : Evm fork StateGasMeter)
    (within : GasMeter.gasHeld m.gas ≤ bound),
    message.currentTarget = C ∧ .berlin ≤ fork ∧ message.data.size < 2 ^ 256 ∧
    SepOn (callKeys message S) ∧ StrForm (storageAt S C 7) ∧ StrForm (storageAt S C 8) ∧
    byte20 (storageAt S C 10) = 0 ∧
    At CODE message 0 [] .empty gas S substate (toNat m) ∧
    Evm.runFrame (step fork) (step_decreases fork) bound runChild m within = .ok s ∧
    s.error = none ∧ S' = s.state

/-- One successful call over `StateGasMeter` keeps `Inv C`. -/
theorem inv_goodCallS {C : Address} {S S' : State.TransactionState}
    (h : GoodCallS C S S') (hI : Inv C S) : Inv C S' := by
  obtain ⟨fork, message, substate, gas, bound, runChild, m, s, within, hC, hfork, hsize, K, h7,
    h8, hdep, start, hrun, hok, rfl⟩ := h
  subst hC
  exact inv_call_any K hfork hsize hdep h7 h8 hI start hrun hok

/-- A finite sequence of successful calls to `C` over the meter `Nat` or over `StateGasMeter`,
and of changes that keep the storage of `C`. -/
inductive CallsS (C : Address) : State.TransactionState → State.TransactionState → Prop
  | nil (S : State.TransactionState) : CallsS C S S
  | call {S S' S'' : State.TransactionState} : GoodCall C S S' → CallsS C S' S'' → CallsS C S S''
  | callS {S S' S'' : State.TransactionState} : GoodCallS C S S' → CallsS C S' S'' →
      CallsS C S S''
  | other {S S' S'' : State.TransactionState} : Untouched C S S' → CallsS C S' S'' →
      CallsS C S S''

/-- `Inv C` along every finite sequence of `CallsS C`. -/
theorem inv_callsS {C : Address} {S S' : State.TransactionState}
    (h : CallsS C S S') (hI : Inv C S) : Inv C S' := by
  induction h with
  | nil => exact hI
  | call hg _ ih => exact ih (inv_goodCall hg hI)
  | callS hg _ ih => exact ih (inv_goodCallS hg hI)
  | other hu _ ih => exact ih ((DepInv.inv_congr hu).mpr hI)

/-- From Paris, a top-level message to `C` (code `CODE`, no value, no precompile, not deprecated),
run by EthLib's `processMessage` over `StateGasMeter` from any starting meter, that ends with no
error, is a `GoodCallS` from its start state to its end state. -/
theorem goodCall_processS {fork : Fork} (hparis : .paris ≤ fork)
    {message : Message fork} {state : State.TransactionState} {substate : Substate}
    (hmc : message.code = CODE)
    (noValue : ¬(message.shouldTransferValue = true ∧ message.value ≠ 0))
    (noPrecompile : precompileAddress fork message = none)
    (hsize : message.data.size < 2 ^ 256) (K : SepOn (callKeys message state))
    (h7 : StrForm (storageAt state message.currentTarget 7))
    (h8 : StrForm (storageAt state message.currentTarget 8))
    (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    {meter : StateGasMeter} {held : GasMeter.gasHeld meter ≤ message.gas}
    {ended : { evm : Evm fork StateGasMeter // GasMeter.gasHeld evm.gas ≤ message.gas }}
    (hproc : processMessage fork message state substate meter held = .ok ended)
    (hok : ended.val.error = none) :
    GoodCallS message.currentTarget state ended.val.state := by
  have hst : startState fork message state = state := by
    simp only [startState, show ¬fork < Fork.paris from Nat.not_lt.mpr hparis, ite_false]
  have hberlin : Fork.berlin ≤ fork := Nat.le_trans (by decide) hparis
  generalize hres : runFrame (step fork) (step_decreases fork) message.gas
    (processRunnerM fork message.gas)
    (startFrame message (startState fork message state) substate meter) held = result
  have hmap := processMessage_map_valM noValue noPrecompile hres
  rw [hproc] at hmap
  rcases result with e | s
  · cases hmap
  · simp only [Except.map, Except.ok.injEq] at hmap
    have hse : s.error = none := by
      rw [← hok, hmap]
      unfold rollbackOnError
      split <;> rfl
    have hend : ended.val = s := by
      rw [hmap]
      unfold rollbackOnError
      simp [hse]
    have start := at_startFrameS hmc (startState fork message state) substate meter
    rw [hst] at start hres
    exact ⟨fork, message, substate, _, message.gas, processRunnerM fork message.gas, _, s, _,
      rfl, hberlin, hsize, K, h7, h8, hdep, start, hres, hse, by rw [hend]⟩

/-- From Berlin, a top-level message whose code is `CODE` (no precompile, call data below 2^256
bytes) with a nonzero value, run by `processMessage` over `StateGasMeter` from any starting meter,
ends with an error, whether it moves the value or not. -/
theorem process_value_failsS {fork : Fork} (hfork : .berlin ≤ fork) {message : Message fork}
    {state : State.TransactionState} {substate : Substate} (hmc : message.code = CODE)
    (noPrecompile : precompileAddress fork message = none) (hsize : message.data.size < 2 ^ 256)
    (hv : message.value ≠ 0) {meter : StateGasMeter} {held : GasMeter.gasHeld meter ≤ message.gas}
    {ended : { evm : Evm fork StateGasMeter // GasMeter.gasHeld evm.gas ≤ message.gas }}
    (hproc : processMessage fork message state substate meter held = .ok ended) :
    ended.val.error ≠ none := by
  have key : ∀ (st : State.TransactionState) (ss : Substate)
      (result : Except EvmError (Evm fork StateGasMeter)),
      runFrame (step fork) (step_decreases fork) message.gas (processRunnerM fork message.gas)
        (startFrame message st ss meter) held = result →
      (processMessage fork message state substate meter held).map Subtype.val =
        result.map (rollbackOnError state) → ended.val.error ≠ none := by
    intro st ss result hres hmap
    rw [hproc] at hmap
    rcases result with e | s
    · cases hmap
    · simp only [Except.map, Except.ok.injEq] at hmap
      rw [hmap]
      have hs : s.error ≠ none := fun hok => by
        obtain ⟨G, hE⟩ := shadow_ends hfork hres hok
        exact hv (ends_ok_dispatch hfork hsize (at_sh (at_startFrameS hmc st ss meter) _) hE hok).2.1
      unfold rollbackOnError
      split
      · exact hs
      · exact hs
  by_cases ht : message.shouldTransferValue = true ∧ message.value ≠ 0
  · cases hm : (startState fork message state).moveEther fork message.caller
      message.currentTarget message.value with
    | error e =>
      exfalso
      rw [processMessage] at hproc
      simp only [Except.map, ht, ne_eq, not_false_eq_true, and_self, ite_true, bind, pure,
        Except.bind, Except.pure, Except.mapError, hm] at hproc
      cases hproc
    | ok moved => exact key moved _ _ rfl (processMessage_map_val_valueM ht hm noPrecompile rfl)
  · exact key _ _ _ rfl (processMessage_map_valM ht noPrecompile rfl)

/-- From Paris, every top-level message to `C` whose code is `CODE` (no precompile, call data below
2^256 bytes, not deprecated), run by EthLib's `processMessage` over `StateGasMeter` from any
starting meter to the end, is a step of `CallsS C`: a `GoodCallS` when it ends with no error (its value is then 0 or not
moved, `process_value_failsS`), and an `Untouched` step when it ends with an error. -/
theorem process_stepS {fork : Fork} (hparis : .paris ≤ fork)
    {message : Message fork} {state : State.TransactionState} {substate : Substate}
    (hmc : message.code = CODE)
    (noPrecompile : precompileAddress fork message = none)
    (hsize : message.data.size < 2 ^ 256) (K : SepOn (callKeys message state))
    (h7 : StrForm (storageAt state message.currentTarget 7))
    (h8 : StrForm (storageAt state message.currentTarget 8))
    (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    {meter : StateGasMeter} {held : GasMeter.gasHeld meter ≤ message.gas}
    {ended : { evm : Evm fork StateGasMeter // GasMeter.gasHeld evm.gas ≤ message.gas }}
    (hproc : processMessage fork message state substate meter held = .ok ended) :
    GoodCallS message.currentTarget state ended.val.state ∨
      Untouched message.currentTarget state ended.val.state := by
  by_cases herr : ended.val.error = none
  · by_cases ht : message.shouldTransferValue = true ∧ message.value ≠ 0
    · exact absurd herr (process_value_failsS (Nat.le_trans (by decide) hparis) hmc noPrecompile
        hsize ht.2 hproc)
    · exact .inl (goodCall_processS hparis hmc ht noPrecompile hsize K h7 h8 hdep hproc herr)
  · exact .inr (fun _ => Local.processMessage_failed_getStorage hproc herr _ _)

/-! ## The fresh meter of the message -/

/-- `goodCall_processS` for the fresh meter of the message. -/
theorem goodCall_processS_start {fork : Fork} (hparis : .paris ≤ fork)
    {message : Message fork} {state : State.TransactionState} {substate : Substate}
    (hmc : message.code = CODE)
    (noValue : ¬(message.shouldTransferValue = true ∧ message.value ≠ 0))
    (noPrecompile : precompileAddress fork message = none)
    (hsize : message.data.size < 2 ^ 256) (K : SepOn (callKeys message state))
    (h7 : StrForm (storageAt state message.currentTarget 7))
    (h8 : StrForm (storageAt state message.currentTarget 8))
    (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    {ended : { evm : Evm fork StateGasMeter // GasMeter.gasHeld evm.gas ≤ message.gas }}
    (hproc : processMessage fork message state substate = .ok ended)
    (hok : ended.val.error = none) :
    GoodCallS message.currentTarget state ended.val.state :=
  goodCall_processS hparis hmc noValue noPrecompile hsize K h7 h8 hdep hproc hok

/-- `process_value_failsS` for the fresh meter of the message. -/
theorem process_value_failsS_start {fork : Fork} (hfork : .berlin ≤ fork)
    {message : Message fork} {state : State.TransactionState} {substate : Substate}
    (hmc : message.code = CODE) (noPrecompile : precompileAddress fork message = none)
    (hsize : message.data.size < 2 ^ 256) (hv : message.value ≠ 0)
    {ended : { evm : Evm fork StateGasMeter // GasMeter.gasHeld evm.gas ≤ message.gas }}
    (hproc : processMessage fork message state substate = .ok ended) :
    ended.val.error ≠ none :=
  process_value_failsS hfork hmc noPrecompile hsize hv hproc

/-- `process_stepS` for the fresh meter of the message. -/
theorem process_stepS_start {fork : Fork} (hparis : .paris ≤ fork)
    {message : Message fork} {state : State.TransactionState} {substate : Substate}
    (hmc : message.code = CODE)
    (noPrecompile : precompileAddress fork message = none)
    (hsize : message.data.size < 2 ^ 256) (K : SepOn (callKeys message state))
    (h7 : StrForm (storageAt state message.currentTarget 7))
    (h8 : StrForm (storageAt state message.currentTarget 8))
    (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    {ended : { evm : Evm fork StateGasMeter // GasMeter.gasHeld evm.gas ≤ message.gas }}
    (hproc : processMessage fork message state substate = .ok ended) :
    GoodCallS message.currentTarget state ended.val.state ∨
      Untouched message.currentTarget state ended.val.state :=
  process_stepS hparis hmc noPrecompile hsize K h7 h8 hdep hproc

end UsdtVerify.Complete
