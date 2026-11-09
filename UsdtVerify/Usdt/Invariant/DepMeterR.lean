import UsdtVerify.Usdt.Invariant.DepMeter
import UsdtVerify.Evm.RunCR

/-!
# The invariant on the deprecated paths over EthLib's EIP-8037 meter, any reservoir (round 44)

Usdt/Invariant/DepMeter.lean (round 39) for a run over `StateGasMeter` from a frame with ANY
reservoir, through `runC_of_sgmR` in place of `runC_of_sgm`.

The CALL of a deprecated path, from a frame with reservoir `r`, sends a message with reservoir `r`
and leaves the caller with reservoir 0 (`RunSR`). The runner assumptions are therefore stated for
the calls from a caller of reservoir 0 with a message of reservoir `r`.

- `KeepsInvAtSR runChild message state r`, `HonestBalanceAtSR runChild message state r`:
  `KeepsInvAtS` and `HonestBalanceAtS` for the messages of reservoir `r` in place of 0.
  At `r = 0` they are `KeepsInvAtS` and `HonestBalanceAtS` (`keepsInvAtSR_zero`,
  `honestBalanceAtSR_zero`).
  `keepsInvAtC_of_SR`, `honestBalanceAtC_of_SR`: at the reservoir of `g0` they give the
  assumptions over `RunC` for the relation `RunSR runChild g0 E`.
- `inv_call_depR`: every deprecated call over `StateGasMeter` from any reservoir `r` that ends with
  no error keeps `Inv`, under `KeepsInvAtSR … r` and, for destroyBlackFunds,
  `HonestBalanceAtSR … r`.
- `inv_call_anyDR`: deprecated or not, with no hypothesis on the reservoir.
- `GoodCallDR`, `inv_goodCallDR`, `CallsDR`, `inv_callsDR`: sequences. `GoodCallDS.toR`,
  `CallsDS.toR`: the round 39 forms are instances.
- `process_stepDR`, `process_stepSDR`: from Paris, a top-level message run by `processMessage` over
  `StateGasMeter` from any starting meter, with the runner assumptions of `processRunner` at the
  reservoir of that meter.
-/

namespace UsdtVerify.Complete

open EthLib.Base (Fork U256 Address)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open UsdtVerify.Gas
open UsdtVerify.Meter (toNat)
open GasCosts
open Invariant Deprecated DeprecatedBalance DeprecatedDestroy DestroySpec

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate} {gas : Nat}
  {bound : Nat} {runChild : MessageRunner fork StateGasMeter bound}

/-- `KeepsInvAtS` for the messages of reservoir `r`: every call that the code of `C` makes from
`state` (`SentVia`, of the `toNat` caller), from a caller of reservoir 0 with a message of
reservoir `r`, and that the runner ends with no error keeps `Inv C` from the caller state to the
child's end state. -/
def KeepsInvAtSR (runChild : MessageRunner fork StateGasMeter bound) (message : Message fork)
    (state : State.TransactionState) (r : Nat) : Prop :=
  ∀ caller msg lt child, SentVia message state (upAddr state message) (toNat caller) msg →
    caller.gas.reservoir = 0 → msg.reservoir = r →
    runChild caller msg lt = .ok child → child.1.error = none →
    Inv message.currentTarget caller.state → Inv message.currentTarget child.1.state

/-- `HonestBalanceAtS` for the messages of reservoir `r`. -/
def HonestBalanceAtSR (runChild : MessageRunner fork StateGasMeter bound) (message : Message fork)
    (state : State.TransactionState) (r : Nat) : Prop :=
  ∀ caller msg lt child, SentVia message state (upAddr state message) (toNat caller) msg →
    caller.gas.reservoir = 0 → msg.reservoir = r →
    runChild caller msg lt = .ok child → msg.data = dataB message → child.1.error = none →
      resWord (outMemOf (memD message) child.1.output) =
        storageAt child.1.state message.currentTarget (balSlot message)

theorem keepsInvAtSR_zero :
    KeepsInvAtSR runChild message state 0 ↔ KeepsInvAtS runChild message state := Iff.rfl

theorem honestBalanceAtSR_zero :
    HonestBalanceAtSR runChild message state 0 ↔ HonestBalanceAtS runChild message state := Iff.rfl

/-- `SentVia` reads no reservoir of the message. -/
theorem sentVia_reservoir {ua : Address} {caller : Evm fork Nat} {msg : Message fork} (r : Nat)
    (h : SentVia message state ua caller msg) :
    SentVia message state ua caller { msg with reservoir := r } := by
  obtain ⟨c, rt, hc, hr, ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩, hv⟩ := h
  exact ⟨c, rt, hc, hr, ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩, hv⟩

theorem keepsInvAtC_of_SR {g0 : StateGasMeter} {E : Nat}
    (h : KeepsInvAtSR runChild message state g0.reservoir) :
    KeepsInvAtC (RunSR runChild g0 E) message state := by
  rintro caller msg child hsv ⟨cS, msgS, lt, chS, hch, rfl, rfl, hchN, hcg⟩ he hI
  have cs : child.state = chS.1.state := by rw [hchN]; rfl
  have ce : child.error = chS.1.error := by rw [hchN]; rfl
  rw [cs]
  exact h cS _ lt chS (sentVia_reservoir _ hsv) (by rw [hcg]) rfl hch (ce ▸ he) hI

theorem honestBalanceAtC_of_SR {g0 : StateGasMeter} {E : Nat}
    (h : HonestBalanceAtSR runChild message state g0.reservoir) :
    HonestBalanceAtC (RunSR runChild g0 E) message state := by
  rintro caller msg child hsv ⟨cS, msgS, lt, chS, hch, rfl, rfl, hchN, hcg⟩ hmd he
  have cs : child.state = chS.1.state := by rw [hchN]; rfl
  have ce : child.error = chS.1.error := by rw [hchN]; rfl
  have co : child.output = chS.1.output := by rw [hchN]; rfl
  rw [cs, co]
  exact h cS _ lt chS (sentVia_reservoir _ hsv) (by rw [hcg]) rfl hch hmd (ce ▸ he)

/-- **Every successful deprecated call over the EIP-8037 meter keeps the invariant, any
reservoir.** From Berlin, from a frame `m` of `StateGasMeter` with any reservoir whose `toNat` is
the fresh frame of `CODE`, call data below 2^256 bytes, the keccak hypothesis `SepOn` of the keys
of the call, slots 7 and 8 of `StrForm`, deprecated (byte 20 of slot 10 not 0), with the runner
assumptions `KeepsInvAtSR` and, for destroyBlackFunds, `HonestBalanceAtSR` at the reservoir of
`m`: if
`Inv C state` holds and the loop of the interpreter, for any gas bound and that runner, ends with
no error, then `Inv C s.state` holds. -/
theorem inv_call_depR {m s : Evm fork StateGasMeter}
    (K : SepOn (callKeys message state)) (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (h7 : StrForm (storageAt state message.currentTarget 7))
    (h8 : StrForm (storageAt state message.currentTarget 8))
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0)
    (hkeeps : KeepsInvAtSR runChild message state m.gas.reservoir)
    (hhonest : selector message.data = 0xf3bdc228 →
      HonestBalanceAtSR runChild message state m.gas.reservoir)
    (hI : Inv message.currentTarget state)
    (start : At CODE message 0 [] .empty gas state substate (toNat m))
    {within : GasMeter.gasHeld m.gas ≤ bound}
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild m within = .ok s)
    (hok : s.error = none) : Inv message.currentTarget s.state := by
  obtain ⟨G, hC⟩ := runC_of_sgmR (g0 := m.gas) hfork hrun hok (.inl rfl) (Nat.le_refl _)
  have hE := endsOk_of_sgm hfork hrun hok
  obtain ⟨G', hEnds⟩ := Shadow.shadow_ends hfork hrun hok
  have start' := at_addGas start (Shadow.budget m)
  have hk := keepsInvAtC_of_SR (E := STORAGE_SET_STATE_GAS * Evm.measure m) hkeeps
  have hsG : ∀ g, ({ toNat s with gas := g } : Evm fork Nat).state = s.state := fun _ => rfl
  have hokG : ∀ g, ({ toNat s with gas := g } : Evm fork Nat).error = none := fun _ => hok
  obtain ⟨_, -, i, hi⟩ := EndsOk.dispatch hfork hsize' start hE
  match i, hi with
  | ⟨0, _⟩, hi => exact hsG G' ▸ inv_name hfork hsize' (hi.trans rfl) h7 hI start' hEnds (hokG G')
  | ⟨1, _⟩, hi => exact hsG G' ▸ inv_deprecate K hfork hsize' (hi.trans rfl) hI start' hEnds (hokG G')
  | ⟨2, _⟩, hi => exact hsG G ▸ inv_of_localC hk hI (dep_approve_localC hfork hsize' (hi.trans rfl) hdep start hC hE (hokG G))
  | ⟨3, _⟩, hi => exact hsG G' ▸ inv_deprecated hfork hsize' (hi.trans rfl) hI start' hEnds (hokG G')
  | ⟨4, _⟩, hi => exact hsG G' ▸ inv_addBlackList K hfork hsize' (hi.trans rfl) hI start' hEnds (hokG G')
  | ⟨5, _⟩, hi => exact hsG G ▸ inv_of_localC hk hI (dep_totalSupply_localC hfork hsize' (hi.trans rfl) hdep start hC hE (hokG G))
  | ⟨6, _⟩, hi => exact hsG G ▸ inv_of_localC hk hI (dep_transferFrom_localC hfork hsize' (hi.trans rfl) hdep start hC hE (hokG G))
  | ⟨7, _⟩, hi => exact hsG G' ▸ inv_upgradedAddress hfork hsize' (hi.trans rfl) hI start' hEnds (hokG G')
  | ⟨8, _⟩, hi => exact hsG G' ▸ inv_balances hfork hsize' (hi.trans rfl) hI start' hEnds (hokG G')
  | ⟨9, _⟩, hi => exact hsG G' ▸ inv_decimals hfork hsize' (hi.trans rfl) hI start' hEnds (hokG G')
  | ⟨10, _⟩, hi => exact hsG G' ▸ inv_maximumFee hfork hsize' (hi.trans rfl) hI start' hEnds (hokG G')
  | ⟨11, _⟩, hi => exact hsG G' ▸ inv_totalSupplyVar hfork hsize' (hi.trans rfl) hI start' hEnds (hokG G')
  | ⟨12, _⟩, hi => exact hsG G' ▸ inv_unpause K hfork hsize' (hi.trans rfl) hI start' hEnds (hokG G')
  | ⟨13, _⟩, hi => exact hsG G' ▸ inv_getBlackListStatus hfork hsize' (hi.trans rfl) hI start' hEnds (hokG G')
  | ⟨14, _⟩, hi => exact hsG G' ▸ inv_allowed hfork hsize' (hi.trans rfl) hI start' hEnds (hokG G')
  | ⟨15, _⟩, hi => exact hsG G' ▸ inv_paused hfork hsize' (hi.trans rfl) hI start' hEnds (hokG G')
  | ⟨16, _⟩, hi => exact hsG G ▸ inv_of_localC hk hI (dep_balanceOf_localC hfork hsize' (hi.trans rfl) hdep start hC hE (hokG G))
  | ⟨17, _⟩, hi => exact hsG G' ▸ inv_pause K hfork hsize' (hi.trans rfl) hI start' hEnds (hokG G')
  | ⟨18, _⟩, hi => exact hsG G' ▸ inv_getOwner hfork hsize' (hi.trans rfl) hI start' hEnds (hokG G')
  | ⟨19, _⟩, hi => exact hsG G' ▸ inv_owner hfork hsize' (hi.trans rfl) hI start' hEnds (hokG G')
  | ⟨20, _⟩, hi => exact hsG G' ▸ inv_symbol hfork hsize' (hi.trans rfl) h8 hI start' hEnds (hokG G')
  | ⟨21, _⟩, hi => exact hsG G ▸ inv_of_localC hk hI (dep_transfer_localC hfork hsize' (hi.trans rfl) hdep start hC hE (hokG G))
  | ⟨22, _⟩, hi => exact hsG G' ▸ inv_setParams K hfork hsize' (hi.trans rfl) hI start' hEnds (hokG G')
  | ⟨23, _⟩, hi => exact hsG G' ▸ inv_issue K hfork hsize' (hi.trans rfl) hI start' hEnds (hokG G')
  | ⟨24, _⟩, hi => exact hsG G' ▸ inv_redeem K hfork hsize' (hi.trans rfl) hI start' hEnds (hokG G')
  | ⟨25, _⟩, hi => exact hsG G ▸ inv_of_localC hk hI (dep_allowance_localC hfork hsize' (hi.trans rfl) hdep start hC hE (hokG G))
  | ⟨26, _⟩, hi => exact hsG G' ▸ inv_basisPointsRate hfork hsize' (hi.trans rfl) hI start' hEnds (hokG G')
  | ⟨27, _⟩, hi => exact hsG G' ▸ inv_isBlackListed hfork hsize' (hi.trans rfl) hI start' hEnds (hokG G')
  | ⟨28, _⟩, hi => exact hsG G' ▸ inv_removeBlackList K hfork hsize' (hi.trans rfl) hI start' hEnds (hokG G')
  | ⟨29, _⟩, hi => exact hsG G' ▸ inv_maxUint hfork hsize' (hi.trans rfl) hI start' hEnds (hokG G')
  | ⟨30, _⟩, hi => exact hsG G' ▸ inv_transferOwnership K hfork hsize' (hi.trans rfl) hI start' hEnds (hokG G')
  | ⟨31, _⟩, hi => exact hsG G ▸ inv_dep_destroyC K hfork hsize' (hi.trans rfl) hdep hk (honestBalanceAtC_of_SR (hhonest (hi.trans rfl))) hI start hC hE (hokG G)
  | ⟨n + 32, h⟩, _ => exact absurd h (by omega)

/-- **Every successful call over the EIP-8037 meter keeps the invariant, deprecated or not, any
reservoir.** `inv_call_any` when not deprecated, `inv_call_depR` when deprecated, with the runner
assumptions at the reservoir of the first frame. No hypothesis on the reservoir. -/
theorem inv_call_anyDR {m s : Evm fork StateGasMeter}
    (K : SepOn (callKeys message state)) (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (h7 : StrForm (storageAt state message.currentTarget 7))
    (h8 : StrForm (storageAt state message.currentTarget 8))
    (hkeeps : byte20 (storageAt state message.currentTarget 10) ≠ 0 →
      KeepsInvAtSR runChild message state m.gas.reservoir)
    (hhonest : byte20 (storageAt state message.currentTarget 10) ≠ 0 →
      selector message.data = 0xf3bdc228 →
      HonestBalanceAtSR runChild message state m.gas.reservoir)
    (hI : Inv message.currentTarget state)
    (start : At CODE message 0 [] .empty gas state substate (toNat m))
    {within : GasMeter.gasHeld m.gas ≤ bound}
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild m within = .ok s)
    (hok : s.error = none) : Inv message.currentTarget s.state := by
  by_cases hdep : byte20 (storageAt state message.currentTarget 10) = 0
  · exact inv_call_any K hfork hsize' hdep h7 h8 hI start hrun hok
  · exact inv_call_depR K hfork hsize' h7 h8 hdep (hkeeps hdep) (hhonest hdep) hI start hrun hok

/-! ## Sequences and `processMessage` -/

/-- One successful run of `CODE` over `StateGasMeter` for a message to `C`, from `S` to `S'`,
deprecated, from any reservoir, under the hypotheses of `inv_call_depR`. -/
def GoodCallDR (C : Address) (S S' : State.TransactionState) : Prop :=
  ∃ (fork : Fork) (message : Message fork) (substate : Substate) (gas bound : Nat)
    (runChild : MessageRunner fork StateGasMeter bound) (m s : Evm fork StateGasMeter)
    (within : GasMeter.gasHeld m.gas ≤ bound),
    message.currentTarget = C ∧ .berlin ≤ fork ∧ message.data.size < 2 ^ 256 ∧
    SepOn (callKeys message S) ∧ StrForm (storageAt S C 7) ∧ StrForm (storageAt S C 8) ∧
    byte20 (storageAt S C 10) ≠ 0 ∧ KeepsInvAtSR runChild message S m.gas.reservoir ∧
    (selector message.data = 0xf3bdc228 → HonestBalanceAtSR runChild message S m.gas.reservoir) ∧
    At CODE message 0 [] .empty gas S substate (toNat m) ∧
    Evm.runFrame (step fork) (step_decreases fork) bound runChild m within = .ok s ∧
    s.error = none ∧ S' = s.state

/-- One successful deprecated call over `StateGasMeter`, any reservoir, keeps `Inv C`. -/
theorem inv_goodCallDR {C : Address} {S S' : State.TransactionState}
    (h : GoodCallDR C S S') (hI : Inv C S) : Inv C S' := by
  obtain ⟨fork, message, substate, gas, bound, runChild, m, s, within, hC, hfork, hsize, K, h7,
    h8, hdep, hk, hh, start, hrun, hok, rfl⟩ := h
  subst hC
  exact inv_call_depR K hfork hsize h7 h8 hdep hk hh hI start hrun hok

/-- A `GoodCallDS` step (reservoir 0) is a `GoodCallDR` step. -/
theorem GoodCallDS.toR {C : Address} {S S' : State.TransactionState} (h : GoodCallDS C S S') :
    GoodCallDR C S S' := by
  obtain ⟨fork, message, substate, gas, bound, runChild, m, s, within, hC, hfork, hsize, K, h7,
    h8, hdep, hk, hh, start, hres, hrun, hok, hS⟩ := h
  exact ⟨fork, message, substate, gas, bound, runChild, m, s, within, hC, hfork, hsize, K, h7, h8,
    hdep, hres ▸ hk, hres ▸ hh, start, hrun, hok, hS⟩

/-- `CallsS` steps and deprecated calls over `StateGasMeter` from any reservoir (`GoodCallDR`). -/
inductive CallsDR (C : Address) : State.TransactionState → State.TransactionState → Prop
  | nil (S : State.TransactionState) : CallsDR C S S
  | calls {S S' S'' : State.TransactionState} : CallsS C S S' → CallsDR C S' S'' →
      CallsDR C S S''
  | callDR {S S' S'' : State.TransactionState} : GoodCallDR C S S' → CallsDR C S' S'' →
      CallsDR C S S''

/-- `Inv C` along every finite sequence of `CallsDR C`. -/
theorem inv_callsDR {C : Address} {S S' : State.TransactionState}
    (h : CallsDR C S S') (hI : Inv C S) : Inv C S' := by
  induction h with
  | nil => exact hI
  | calls hc _ ih => exact ih (inv_callsS hc hI)
  | callDR hg _ ih => exact ih (inv_goodCallDR hg hI)

/-- Every `CallsDS` sequence is a `CallsDR` sequence. -/
theorem CallsDS.toR {C : Address} {S S' : State.TransactionState} (h : CallsDS C S S') :
    CallsDR C S S' := by
  induction h with
  | nil S => exact .nil S
  | calls hc _ ih => exact .calls hc ih
  | callDS hg _ ih => exact .callDR hg.toR ih

/-- **Deprecated top-level messages over the EIP-8037 meter, any reservoir.** From Paris, a
top-level message to `C` (code `CODE`, no precompile, call data below 2^256 bytes, deprecated), with
`SepOn` of the keys of the call and slots 7 and 8 of `StrForm`, run by EthLib's `processMessage`
over `StateGasMeter` to the end from any starting meter, under
`KeepsInvAtSR` and, for destroyBlackFunds, `HonestBalanceAtSR` of `processRunner` at the
reservoir of that meter, is a `GoodCallDR` when it ends with no error and an `Untouched` step when
it ends with an error. -/
theorem process_stepDR {fork : Fork} (hparis : .paris ≤ fork)
    {message : Message fork} {state : State.TransactionState} {substate : Substate}
    (hmc : message.code = CODE)
    (noPrecompile : precompileAddress fork message = none)
    (hsize : message.data.size < 2 ^ 256) (K : SepOn (callKeys message state))
    (h7 : StrForm (storageAt state message.currentTarget 7))
    (h8 : StrForm (storageAt state message.currentTarget 8))
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0)
    {meter : StateGasMeter} {held : GasMeter.gasHeld meter ≤ message.gas}
    (hkeeps : KeepsInvAtSR (processRunner fork message.gas) message state
      meter.reservoir)
    (hhonest : selector message.data = 0xf3bdc228 →
      HonestBalanceAtSR (processRunner fork message.gas) message state
        meter.reservoir)
    {ended : { evm : Evm fork StateGasMeter // GasMeter.gasHeld evm.gas ≤ message.gas }}
    (hproc : processMessage fork message state substate meter held = .ok ended) :
    GoodCallDR message.currentTarget state ended.val.state ∨
      Untouched message.currentTarget state ended.val.state := by
  by_cases herr : ended.val.error = none
  · by_cases ht : message.shouldTransferValue = true ∧ message.value ≠ 0
    · exact absurd herr (process_value_failsS (Nat.le_trans (by decide) hparis) hmc noPrecompile
        hsize ht.2 hproc)
    refine .inl ?_
    have hst : startState fork message state = state := by
      simp only [startState, show ¬fork < Fork.paris from Nat.not_lt.mpr hparis, ite_false]
    have hberlin : Fork.berlin ≤ fork := Nat.le_trans (by decide) hparis
    generalize hres' : runFrame (step fork) (step_decreases fork) message.gas
      (processRunner fork message.gas)
      (startFrame message (startState fork message state) substate meter) held = result
    have hmap := processMessage_map_val ht noPrecompile hres'
    rw [hproc] at hmap
    rcases result with e | s
    · cases hmap
    · simp only [Except.map, Except.ok.injEq] at hmap
      have hse : s.error = none := by
        rw [← herr, hmap]
        unfold rollbackOnError
        split <;> rfl
      have hend : ended.val = s := by
        rw [hmap]
        unfold rollbackOnError
        simp [hse]
      have start := Meter.at_startFrameS hmc (startState fork message state) substate meter
      rw [hst] at start hres'
      exact ⟨fork, message, substate, _, message.gas, processRunner fork message.gas,
        _, s, _, rfl, hberlin, hsize, K, h7, h8, hdep, hkeeps, hhonest, start, hres', hse,
        by rw [hend]⟩
  · exact .inr fun _ =>
      getStorage_processMessage_of_error hproc (Option.isSome_iff_ne_none.mpr herr) _ _

/-- **Every top-level message over the EIP-8037 meter, deprecated or not, any reservoir.** From
Paris, a top-level message to `C` (code `CODE`, no precompile, call data below 2^256 bytes), with
`SepOn` of the keys of the call and slots 7 and 8 of `StrForm`, run by `processMessage` over
`StateGasMeter` from any starting meter is a `GoodCallS` (not deprecated), a
`GoodCallDR` (deprecated, under its hypotheses at the reservoir of the starting meter) or an
`Untouched` step. No hypothesis on the reservoir. -/
theorem process_stepSDR {fork : Fork} (hparis : .paris ≤ fork)
    {message : Message fork} {state : State.TransactionState} {substate : Substate}
    (hmc : message.code = CODE)
    (noPrecompile : precompileAddress fork message = none)
    (hsize : message.data.size < 2 ^ 256) (K : SepOn (callKeys message state))
    (h7 : StrForm (storageAt state message.currentTarget 7))
    (h8 : StrForm (storageAt state message.currentTarget 8))
    {meter : StateGasMeter} {held : GasMeter.gasHeld meter ≤ message.gas}
    (hkeeps : byte20 (storageAt state message.currentTarget 10) ≠ 0 →
      KeepsInvAtSR (processRunner fork message.gas) message state meter.reservoir)
    (hhonest : byte20 (storageAt state message.currentTarget 10) ≠ 0 →
      selector message.data = 0xf3bdc228 →
      HonestBalanceAtSR (processRunner fork message.gas) message state
        meter.reservoir)
    {ended : { evm : Evm fork StateGasMeter // GasMeter.gasHeld evm.gas ≤ message.gas }}
    (hproc : processMessage fork message state substate meter held = .ok ended) :
    GoodCallS message.currentTarget state ended.val.state ∨
      GoodCallDR message.currentTarget state ended.val.state ∨
      Untouched message.currentTarget state ended.val.state := by
  by_cases hdep : byte20 (storageAt state message.currentTarget 10) = 0
  · rcases process_stepS hparis hmc noPrecompile hsize K h7 h8 hdep hproc with h | h
    · exact .inl h
    · exact .inr (.inr h)
  · exact .inr (process_stepDR hparis hmc noPrecompile hsize K h7 h8 hdep (hkeeps hdep)
      (hhonest hdep) hproc)

end UsdtVerify.Complete
