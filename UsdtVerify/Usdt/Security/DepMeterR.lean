import UsdtVerify.Usdt.Security.SeqDepMeter
import UsdtVerify.Usdt.Complete.Deprecated.MeterR

/-!
# The security properties when deprecated, over EthLib's EIP-8037 meter, any reservoir (round 44)

Usdt/Security/DepMeter.lean and Usdt/Security/SeqDepMeter.lean (rounds 39 and 41) for a run over
`StateGasMeter` from a frame with ANY reservoir, through `dep_X_completeR` (round 42) in place of
`dep_X_completeS`. The CALL of a deprecated path from a frame with reservoir `r` sends a message
with reservoir `r` from a caller of reservoir 0, so the runner assumptions are stated for those
calls.

- `FwdAtSR runS message S ua r X Y`, `KeepsAtSR runS message S ua r R`: `FwdAtS` and `KeepsAtS`
  for the messages of reservoir `r` in place of 0 (`keepsAtSR_zero`). `KeepsAtSR.fwd`.
- `effect_allSR`: every run over `StateGasMeter` from any reservoir that ends with no error ends
  in a state described by `EffectDF (FwdAtSR runS message state (upAddr state message) r)`, `r`
  the reservoir of the first frame. No assumption on the runner.
- `paused_call_allSR`, `nonOwner_call_allSR`, `listed_call_allSR`, `allowKept_call_allSR`,
  `supply_call_allSR`: the five `_call_allS` theorems from any reservoir, with the runner
  assumption `KeepsAtSR` at the reservoir of the first frame.
- `owner_only_allSR`: `owner_only` over `StateGasMeter`, deprecated or not, with no hypothesis on
  the reservoir.
- `RunOkRSR`, `RunOkRSR.effect`, `RunOkRS.toR`, `SeqRSR`, `SeqRS.toRSR`, `seqRSR_lift`, and
  `nonOwner_seq_allSR`, `paused_seq_allSR`, `listed_seq_allSR`, `allowKept_seq_allSR`,
  `supply_seq_allSR`: the sequence forms, each call over `StateGasMeter` from any reservoir.
- `runOkRSR_process`, `process_stepSecDR`: from Paris, a top-level message run by
  `processMessage` over `StateGasMeter` from any starting meter, whose runner `processRunner`
  meets `KeepsAtSR … R` at the reservoir of that meter when deprecated, is a `RunOkRSR` step or an
  `Untouched` step.
-/

namespace UsdtVerify.Security

open EthLib.Base (Fork U256 Address)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open UsdtVerify.Meter (toNat)
open Invariant Complete
open Transfer TransferOk TransferFee TransferFrom Owner Issue IssueSpec BlackList BlackListSpec
open SetParamsSpec AddrWriteSpec DestroySpec Pause AddrWrite Approve StringsGen Deprecated

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate} {gas bound : Nat} {runS : MessageRunner fork StateGasMeter bound}

/-- `FwdAtS` for the messages of reservoir `r`: one call that the code of `C` makes from `S` to
`ua` (`SentVia` of the `toNat` caller), from a caller of reservoir 0 with a message of reservoir
`r`, ended with no error, from `X` to `Y`. -/
def FwdAtSR (runS : MessageRunner fork StateGasMeter bound) (message : Message fork)
    (S : State.TransactionState) (ua : Address) (r : Nat) (X Y : State.TransactionState) : Prop :=
  ∃ caller msg lt child, SentVia message S ua (toNat caller) msg ∧
    caller.gas.reservoir = 0 ∧ msg.reservoir = r ∧
    runS caller msg lt = .ok child ∧ child.1.error = none ∧ caller.state = X ∧ child.1.state = Y

/-- `KeepsAtS` for the messages of reservoir `r`: the calls from a caller of reservoir 0 with a
message of reservoir `r`, as the CALL from a frame of reservoir `r` sends them. -/
def KeepsAtSR (runS : MessageRunner fork StateGasMeter bound) (message : Message fork)
    (S : State.TransactionState) (ua : Address) (r : Nat)
    (R : State.TransactionState → State.TransactionState → Prop) : Prop :=
  ∀ caller msg lt child, SentVia message S ua (toNat caller) msg →
    caller.gas.reservoir = 0 → msg.reservoir = r →
    runS caller msg lt = .ok child → child.1.error = none → R caller.state child.1.state

theorem keepsAtSR_zero {S : State.TransactionState} {ua : Address}
    {R : State.TransactionState → State.TransactionState → Prop} :
    KeepsAtSR runS message S ua 0 R ↔ KeepsAtS runS message S ua R := Iff.rfl

theorem KeepsAtSR.fwd {S : State.TransactionState} {ua : Address} {r : Nat}
    {R : State.TransactionState → State.TransactionState → Prop} {X Y : State.TransactionState}
    (hk : KeepsAtSR runS message S ua r R) (h : FwdAtSR runS message S ua r X Y) : R X Y := by
  obtain ⟨caller, msg, lt, child, hs, hcr, hmr, hch, he, rfl, rfl⟩ := h
  exact hk caller msg lt child hs hcr hmr hch he

/-- A forwarded call found by `dep_X_completeR`, as `FwdAtSR`. -/
theorem fwdSR_of {ua : Address} {c : ByteArray} {r : Route} {d : ByteArray} {q : Nat}
    {caller : Evm fork StateGasMeter} {msg : Message fork} {lt : msg.gas < bound}
    {child : { child : Evm fork StateGasMeter // GasMeter.gasHeld child.gas ≤ msg.gas }}
    {S' : State.TransactionState}
    (hcode : state.getCode (state.getAccount ua).codeHash = .ok c) (hroute : Routes fork state c r)
    (hfwd : SendsVia message ua c r d msg) (hv : ReadsAs caller.state state)
    (hcr : caller.gas.reservoir = 0) (hmr : msg.reservoir = q)
    (hch : runS caller msg lt = .ok child) (he : child.1.error = none)
    (hst : S' = (incorporateChild fork caller child.1).state) :
    ∃ X, (∀ n, storageAt X message.currentTarget n = storageAt state message.currentTarget n) ∧
      FwdAtSR runS message state ua q X S' :=
  ⟨caller.state, fun n => storageAt_of_readsAs hv _ n, caller, msg, lt, child,
    sentVia_of_sendsVia hcode hroute hfwd hv, hcr, hmr, hch, he, rfl,
    by rw [hst, state_incorporateChildS]⟩

/-- **The effect of every successful call over the EIP-8037 meter, deprecated or not, any
reservoir.** From Berlin, from a frame `m` of `StateGasMeter` with any reservoir whose `toNat` is
the fresh frame of `CODE`, with slots 7 and 8 of `StrForm`: every run of the loop, for any gas
bound and message runner over `StateGasMeter`, that ends with no error ends in a state described
by `EffectDF` for the calls of that runner with a message of the reservoir of `m` (`FwdAtSR`). No
assumption on the runner. -/
theorem effect_allSR (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (h7 : StrForm (storageAt state message.currentTarget 7))
    (h8 : StrForm (storageAt state message.currentTarget 8))
    {m s : Evm fork StateGasMeter}
    (start : At CODE message 0 [] .empty gas state substate (toNat m))
    {within : GasMeter.gasHeld m.gas ≤ bound}
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runS m within = .ok s)
    (hok : s.error = none) :
    EffectDF (FwdAtSR runS message state (upAddr state message) m.gas.reservoir) message state
      s.state := by
  by_cases hdep : byte20 (storageAt state message.currentTarget 10) = 0
  · exact .loc (effect_local_any hfork hsize' (.inl hdep) h7 h8 start hrun hok)
  by_cases hf : FlagFn (selector message.data)
  case neg => exact .loc (effect_local_any hfork hsize' (.inr hf) h7 h8 start hrun hok)
  have ne : ∀ {a b : Nat}, selector message.data = a → a ≠ b → selector message.data ≠ b :=
    fun h hab e => hab (h.symm.trans e)
  rcases hf with (h | h | h | h | h | h) | h
  · obtain ⟨c, r, hcode, hroute, -, -, -, -, caller, msg, lt, child, hch, he, hcr, hmr, hfwd, -, hcs, -, -,
      -, hst, -⟩ := dep_approve_completeR hfork hsize' h hdep rfl rfl start hrun hok
    obtain ⟨X, hX, hF⟩ := fwdSR_of hcode hroute hfwd (by
      rw [hcs]; reads_as) hcr hmr hch he hst
    exact .fwd hdep (.inl h) (fun e => absurd e (ne h (by decide)))
      (fun e => absurd e (ne h (by decide))) X hX hF
  · obtain ⟨c, r, hcode, hroute, -, -, -, caller, msg, lt, child, hch, he, hcr, hmr, hfwd, -, hcs, -, -,
      -, hst, -⟩ := dep_totalSupply_completeR hfork hsize' h hdep start hrun hok
    obtain ⟨X, hX, hF⟩ := fwdSR_of hcode hroute hfwd (by
      rw [hcs]; reads_as) hcr hmr hch he hst
    exact .fwd hdep (.inr (.inl h)) (fun e => absurd e (ne h (by decide)))
      (fun e => absurd e (ne h (by decide))) X hX hF
  · obtain ⟨c, r, hcode, hroute, hpause, hblack, -, -, -, caller, msg, lt, child, hch, he, hcr, hmr, hfwd, -,
      hcs, -, -, -, hst, -⟩ :=
      dep_transferFrom_completeR hfork hsize' h hdep rfl rfl rfl rfl start hrun hok
    obtain ⟨X, hX, hF⟩ := fwdSR_of hcode hroute hfwd (by
      rw [hcs]; reads_as) hcr hmr hch he hst
    exact .fwd hdep (.inr (.inr (.inl h))) (fun e => absurd e (ne h (by decide)))
      (fun _ => ⟨hpause, hblack⟩) X hX hF
  · obtain ⟨c, r, hcode, hroute, -, -, -, caller, msg, lt, child, hch, he, hcr, hmr, hfwd, -, hcs, -, -,
      -, hst, -⟩ := dep_balanceOf_completeR hfork hsize' h hdep start hrun hok
    obtain ⟨X, hX, hF⟩ := fwdSR_of hcode hroute hfwd (by
      rw [hcs]; reads_as) hcr hmr hch he hst
    exact .fwd hdep (.inr (.inr (.inr (.inl h)))) (fun e => absurd e (ne h (by decide)))
      (fun e => absurd e (ne h (by decide))) X hX hF
  · obtain ⟨c, r, hcode, hroute, hpause, hblack, -, -, -, caller, msg, lt, child, hch, he, hcr, hmr, hfwd, -,
      hcs, -, -, -, hst, -⟩ :=
      dep_transfer_completeR hfork hsize' h hdep rfl rfl rfl rfl start hrun hok
    obtain ⟨X, hX, hF⟩ := fwdSR_of hcode hroute hfwd (by
      rw [hcs]; reads_as) hcr hmr hch he hst
    exact .fwd hdep (.inr (.inr (.inr (.inr (.inl h))))) (fun _ => ⟨hpause, hblack⟩)
      (fun e => absurd e (ne h (by decide))) X hX hF
  · obtain ⟨c, r, hcode, hroute, -, -, -, caller, msg, lt, child, hch, he, hcr, hmr, hfwd, -, hcs, -, -,
      -, hst, -⟩ := dep_allowance_completeR hfork hsize' h hdep rfl rfl start hrun hok
    obtain ⟨X, hX, hF⟩ := fwdSR_of hcode hroute hfwd (by
      rw [hcs]; reads_as) hcr hmr hch he hst
    exact .fwd hdep (.inr (.inr (.inr (.inr (.inr h))))) (fun e => absurd e (ne h (by decide)))
      (fun e => absurd e (ne h (by decide))) X hX hF
  · obtain ⟨c, r, hcode, hroute, howner, hlisted, -, -, -, caller, msg, lt, child, hch, he, hcr, hmr, -,
      hacc', hfwd, -, hcs, -, -, -, hst, -⟩ :=
      dep_destroy_completeR hfork hsize' h hdep rfl rfl rfl rfl start hrun hok
    have hv : ReadsAs caller.state state := by
      rw [hcs]
      reads_as
    refine .dfwd hdep h howner hlisted caller.state child.1.state
      (resWord (DeprecatedBalance.outMemOf (DeprecatedDestroy.memD message) child.1.output))
      (fun n => storageAt_of_readsAs hv _ n)
      ⟨caller, msg, lt, child, sentVia_of_sendsVia hcode hroute hfwd hv, hcr, hmr, hch, he,
        rfl, rfl⟩
      hacc' ?_
    rw [hst, state_incorporateChildS]

/-! ## Single calls over `StateGasMeter` from any reservoir, deprecated or not -/

section Calls

variable {m s : Evm fork StateGasMeter} {within : GasMeter.gasHeld m.gas ≤ bound}

/-- **Pause, one call over the EIP-8037 meter, deprecated or not, any reservoir.**
`paused_call_allS` with no hypothesis on the reservoir, with `KeepsBal` stated for the runner at
the reservoir of the first frame (`KeepsAtSR … BalKept`). -/
theorem paused_call_allSR (K : SepOn (callKeys message state)) (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (hpaused : byte20 (storageAt state message.currentTarget 0) ≠ 0)
    (h7 : StrForm (storageAt state message.currentTarget 7))
    (h8 : StrForm (storageAt state message.currentTarget 8))
    (hkeeps : byte20 (storageAt state message.currentTarget 10) ≠ 0 →
      KeepsAtSR runS message state (upAddr state message) m.gas.reservoir
        (BalKept message.currentTarget))
    (start : At CODE message 0 [] .empty gas state substate (toNat m))
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runS m within = .ok s)
    (hok : s.error = none) :
    BalKept message.currentTarget state s.state ∨
      (callerWord message = ownerOf state message.currentTarget ∧
        (selector message.data = 0xcc872b66 ∨ selector message.data = 0xdb006a75 ∨
          selector message.data = 0xf3bdc228)) :=
  (effect_allSR hfork hsize' h7 h8 start hrun hok).paused K hpaused
    fun hd _ _ hf => (hkeeps hd).fwd hf

/-- **Non-owner, one call over the EIP-8037 meter, deprecated or not, any reservoir.**
`nonOwner_call_allS` with no hypothesis on the reservoir, with `KeepsSlots` stated for the runner
at the reservoir of the first frame. -/
theorem nonOwner_call_allSR (K : SecSep (callKeys message state)) (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (h7 : StrForm (storageAt state message.currentTarget 7))
    (h8 : StrForm (storageAt state message.currentTarget 8))
    (hno : callerWord message ≠ ownerOf state message.currentTarget)
    (hkeeps : byte20 (storageAt state message.currentTarget 10) ≠ 0 →
      KeepsAtSR runS message state (upAddr state message) m.gas.reservoir
        (ProtKept message.currentTarget))
    (start : At CODE message 0 [] .empty gas state substate (toNat m))
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runS m within = .ok s)
    (hok : s.error = none) : ProtKept message.currentTarget state s.state :=
  (effect_allSR hfork hsize' h7 h8 start hrun hok).protKept K hno
    fun hd _ _ hf => (hkeeps hd).fwd hf

/-- **Blacklist, one call over the EIP-8037 meter, deprecated or not, any reservoir.**
`listed_call_allS` with no hypothesis on the reservoir, with `KeepsListed` stated for the runner at
the reservoir of the first frame. -/
theorem listed_call_allSR (K : SepOn (callKeys message state)) (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (h7 : StrForm (storageAt state message.currentTarget 7))
    (h8 : StrForm (storageAt state message.currentTarget 8))
    {a : U256} (ha : a.toNat < 2 ^ 160) (hl : Listed message.currentTarget state a)
    (hsel : (selector message.data ≠ 0xdb006a75 ∧ selector message.data ≠ 0xf3bdc228) ∨
      callerWord message ≠ ownerOf state message.currentTarget)
    (hkeeps : byte20 (storageAt state message.currentTarget 10) ≠ 0 →
      KeepsAtSR runS message state (upAddr state message) m.gas.reservoir
        (ListedNoDec message.currentTarget))
    (start : At CODE message 0 [] .empty gas state substate (toNat m))
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runS m within = .ok s)
    (hok : s.error = none) : NoDec message.currentTarget (mapSlot a 2) state s.state :=
  (effect_allSR hfork hsize' h7 h8 start hrun hok).listed K ha hl hsel
    fun hd _ _ hf => (hkeeps hd).fwd hf

/-- **Allowances, one call over the EIP-8037 meter, deprecated or not, any reservoir.**
`allowKept_call_allS` with no hypothesis on the reservoir, with `KeepsAllow` stated for the runner
at the reservoir of the first frame. -/
theorem allowKept_call_allSR {y z : U256} (K : SecSep (y :: z :: callKeys message state))
    (hfork : .berlin ≤ fork) (hsize' : message.data.size < 2 ^ 256)
    (h7 : StrForm (storageAt state message.currentTarget 7))
    (h8 : StrForm (storageAt state message.currentTarget 8))
    (hsel : selector message.data ≠ 0x095ea7b3 ∧ selector message.data ≠ 0x23b872dd)
    (hkeeps : byte20 (storageAt state message.currentTarget 10) ≠ 0 →
      KeepsAtSR runS message state (upAddr state message) m.gas.reservoir
        (AllowKept message.currentTarget))
    (start : At CODE message 0 [] .empty gas state substate (toNat m))
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runS m within = .ok s)
    (hok : s.error = none) : AllowKeptAt y z message.currentTarget state s.state :=
  (effect_allSR hfork hsize' h7 h8 start hrun hok).allowKept K hsel
    fun hd _ _ hf => (hkeeps hd).fwd hf

/-- **Supply, one call over the EIP-8037 meter, deprecated or not, any reservoir.**
`supply_call_allS` with no hypothesis on the reservoir, with `KeepsSupply` stated for the runner at
the reservoir of the first frame. -/
theorem supply_call_allSR (K : SepOn (callKeys message state)) (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (h7 : StrForm (storageAt state message.currentTarget 7))
    (h8 : StrForm (storageAt state message.currentTarget 8))
    (hkeeps : byte20 (storageAt state message.currentTarget 10) ≠ 0 →
      KeepsAtSR runS message state (upAddr state message) m.gas.reservoir
        (SupplyKept message.currentTarget))
    (start : At CODE message 0 [] .empty gas state substate (toNat m))
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runS m within = .ok s)
    (hok : s.error = none) : SupplyStepD message state s.state :=
  (effect_allSR hfork hsize' h7 h8 start hrun hok).supply K
    fun hd _ _ hf => (hkeeps hd).fwd hf

/-- **Owner functions over the EIP-8037 meter, deprecated or not, any reservoir.** `owner_only`
for a run of the loop over `StateGasMeter`, any gas bound and message runner, no assumption on the
runner, from a frame `m` with any reservoir whose `toNat` is the fresh frame of `CODE`: every run of
one of the ten owner functions that ends with no error is a call by the owner. -/
theorem owner_only_allSR (hfork : .berlin ≤ fork) (hsize' : message.data.size < 2 ^ 256)
    (hsel : OwnerFn (selector message.data))
    (start : At CODE message 0 [] .empty gas state substate (toNat m))
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runS m within = .ok s)
    (hok : s.error = none) : callerWord message = ownerOf state message.currentTarget := by
  by_cases hd : byte20 (storageAt state message.currentTarget 10) = 0 ∨
      selector message.data ≠ 0xf3bdc228
  · exact owner_only_any hfork hsize' hsel hd start hrun hok
  · obtain ⟨hdep, h⟩ := not_or.mp hd
    have hs : selector message.data = 0xf3bdc228 := Classical.byContradiction h
    obtain ⟨_, _, -, -, howner, -⟩ :=
      dep_destroy_completeR hfork hsize' hs hdep rfl rfl rfl rfl start hrun hok
    exact howner

end Calls

/-! ## Sequences -/

/-- One successful run of `CODE` over `StateGasMeter` for a message to `C`, from `S` to `S'`, any
gas bound and runner, from a frame with any reservoir whose `toNat` is the fresh frame of `CODE`:
when `C` is deprecated at `S`, the runner meets `KeepsAtSR … R` at the reservoir of that frame for
the calls the code makes from `S` to the upgraded address. -/
def RunOkRSR (C : Address) (R : State.TransactionState → State.TransactionState → Prop)
    (S S' : State.TransactionState) {fork : Fork} (message : Message fork) : Prop :=
  ∃ (substate : Substate) (gas bound : Nat) (runS : MessageRunner fork StateGasMeter bound)
    (m s : Evm fork StateGasMeter) (within : GasMeter.gasHeld m.gas ≤ bound),
    message.currentTarget = C ∧ .berlin ≤ fork ∧ message.data.size < 2 ^ 256 ∧
    (byte20 (storageAt S C 10) ≠ 0 →
      KeepsAtSR runS message S (upAddr S message) m.gas.reservoir R) ∧
    At CODE message 0 [] .empty gas S substate (toNat m) ∧
    Evm.runFrame (step fork) (step_decreases fork) bound runS m within = .ok s ∧
    s.error = none ∧ S' = s.state

/-- `effect_allSR` for a `RunOkRSR` step, with the runner assumption. -/
theorem RunOkRSR.effect {C : Address} {R : State.TransactionState → State.TransactionState → Prop}
    {S S' : State.TransactionState} {fork : Fork} {message : Message fork}
    (h : RunOkRSR C R S S' message)
    (h7 : StrForm (storageAt S message.currentTarget 7))
    (h8 : StrForm (storageAt S message.currentTarget 8)) :
    message.currentTarget = C ∧ ∃ F : State.TransactionState → State.TransactionState → Prop,
      EffectDF F message S S' ∧ (byte20 (storageAt S C 10) ≠ 0 → ∀ X Y, F X Y → R X Y) := by
  obtain ⟨substate, gas, bound, runS, m, s, within, hC, hfork, hsize, hk, start, hrun, hok,
    rfl⟩ := h
  subst hC
  exact ⟨rfl, _, effect_allSR hfork hsize h7 h8 start hrun hok,
    fun hd _ _ hf => (hk hd).fwd hf⟩

/-- A `RunOkRS` step (reservoir 0 when deprecated) is a `RunOkRSR` step. -/
theorem RunOkRS.toR {C : Address} {R : State.TransactionState → State.TransactionState → Prop}
    {S S' : State.TransactionState} {fork : Fork} {message : Message fork}
    (h : RunOkRS C R S S' message) : RunOkRSR C R S S' message := by
  obtain ⟨substate, gas, bound, runS, m, s, within, hC, hfork, hsize, hk, hres, start, hrun, hok,
    hS⟩ := h
  refine ⟨substate, gas, bound, runS, m, s, within, hC, hfork, hsize, fun hd => ?_, start, hrun,
    hok, hS⟩
  rw [hres hd]
  exact hk hd

/-- A finite sequence of calls to `C` over the meter `Nat` (`RunOkR`) or over `StateGasMeter`
from any reservoir (`RunOkRSR`), each meeting `Q` on its message and its start state, and of
changes that keep every storage word of `C`. -/
inductive SeqRSR (C : Address) (R : State.TransactionState → State.TransactionState → Prop)
    (Q : ∀ {fork : Fork}, Message fork → State.TransactionState → Prop) :
    State.TransactionState → State.TransactionState → Prop
  | nil (S : State.TransactionState) : SeqRSR C R Q S S
  | call {S S' S'' : State.TransactionState} {fork : Fork} {message : Message fork} :
      RunOkR C R S S' message → Q message S → SeqRSR C R Q S' S'' → SeqRSR C R Q S S''
  | callS {S S' S'' : State.TransactionState} {fork : Fork} {message : Message fork} :
      RunOkRSR C R S S' message → Q message S → SeqRSR C R Q S' S'' → SeqRSR C R Q S S''
  | other {S S' S'' : State.TransactionState} : Untouched C S S' → SeqRSR C R Q S' S'' →
      SeqRSR C R Q S S''

/-- Every `SeqRS` sequence is a `SeqRSR` sequence. -/
theorem SeqRS.toRSR {C : Address} {R : State.TransactionState → State.TransactionState → Prop}
    {Q : ∀ {fork : Fork}, Message fork → State.TransactionState → Prop}
    {S S' : State.TransactionState} (h : SeqRS C R Q S S') : SeqRSR C R Q S S' := by
  induction h with
  | nil S => exact .nil S
  | call hr hq _ ih => exact .call hr hq ih
  | callS hr hq _ ih => exact .callS hr.toR hq ih
  | other hu _ ih => exact .other hu ih

/-- `seqRS_lift` for `SeqRSR`. -/
theorem seqRSR_lift {C : Address} {R0 : State.TransactionState → State.TransactionState → Prop}
    {Q : ∀ {fork : Fork}, Message fork → State.TransactionState → Prop}
    {I : State.TransactionState → Prop} {R : State.TransactionState → State.TransactionState → Prop}
    (hQ : ∀ {fork : Fork} {message : Message fork} {S : State.TransactionState}, Q message S →
      Strs message S)
    (hrefl : ∀ S, R S S) (htrans : ∀ {S S' S''}, R S S' → R S' S'' → R S S'')
    (hother : ∀ {S S'}, Untouched C S S' → I S → R S S' ∧ I S')
    (hcall : ∀ {S S'} {fork : Fork} {message : Message fork}
      (F : State.TransactionState → State.TransactionState → Prop),
      message.currentTarget = C → EffectDF F message S S' →
      (byte20 (storageAt S C 10) ≠ 0 → ∀ X Y, F X Y → R0 X Y) →
      Q message S → I S → R S S' ∧ I S')
    {S S' : State.TransactionState} (h : SeqRSR C R0 Q S S') (hI : I S) : R S S' := by
  induction h with
  | nil S => exact hrefl S
  | call hr hq _ ih =>
    obtain ⟨hC, F, he, hk⟩ := hr.effectF (hQ hq).1 (hQ hq).2
    obtain ⟨hR, hI'⟩ := hcall F hC he hk hq hI
    exact htrans hR (ih hI')
  | callS hr hq _ ih =>
    obtain ⟨hC, F, he, hk⟩ := hr.effect (hQ hq).1 (hQ hq).2
    obtain ⟨hR, hI'⟩ := hcall F hC he hk hq hI
    exact htrans hR (ih hI')
  | other hu _ ih =>
    obtain ⟨hR, hI'⟩ := hother hu hI
    exact htrans hR (ih hI')

/-- **Access control over a sequence over both meters, deprecated or not, any reservoir.**
`nonOwner_seq_allS` for `SeqRSR`: the calls over `StateGasMeter` start from any reservoir and their
runners meet `KeepsAtSR … (ProtKept C)` at that reservoir when `C` is deprecated. Every `Protected`
slot keeps its word. -/
theorem nonOwner_seq_allSR {C : Address} {S S' : State.TransactionState}
    (h : SeqRSR C (ProtKept C) NotOwnerS S S') : ProtKept C S S' := by
  refine seqRSR_lift (I := fun _ => True) (R := ProtKept C) (fun hq => hq.2.1) (fun _ _ _ => rfl)
    (fun h1 h2 n hn => (h2 n hn).trans (h1 n hn)) (fun hu _ => ⟨fun n _ => hu n, trivial⟩) ?_ h
    trivial
  intro S S' fork message F hC he hk hq _
  obtain ⟨hno, -, K⟩ := hq
  subst hC
  exact ⟨he.protKept K hno hk, trivial⟩

/-- **Pause over a sequence over both meters, deprecated or not, any reservoir.**
`paused_seq_allS` for `SeqRSR`: from a state where `C` is paused, every balance keeps its word. -/
theorem paused_seq_allSR {C : Address} {S S' : State.TransactionState}
    (h : SeqRSR C (fun X Y => ProtKept C X Y ∧ BalKept C X Y) NotOwnerS S S')
    (hpaused : byte20 (storageAt S C 0) ≠ 0) : BalKept C S S' := by
  refine seqRSR_lift (I := fun X => byte20 (storageAt X C 0) ≠ 0) (R := BalKept C)
    (fun hq => hq.2.1) (fun _ _ _ => rfl) (fun h1 h2 x hx => (h2 x hx).trans (h1 x hx))
    (fun hu hI => ⟨fun _ _ => hu _, by rw [hu]; exact hI⟩) ?_ h hpaused
  intro S S' fork message F hC he hk hq hp
  obtain ⟨hno, -, K⟩ := hq
  subst hC
  have hprot := he.protKept K hno (fun hd X Y hf => (hk hd X Y hf).1)
  refine ⟨?_, by rw [hprot 0 (.inl rfl)]; exact hp⟩
  rcases he.paused K.toSepOn hp (fun hd X Y hf => (hk hd X Y hf).2) with hb | ⟨howner, -⟩
  · exact hb
  · exact absurd howner hno

/-- **Blacklist over a sequence over both meters, deprecated or not, any reservoir.**
`listed_seq_allS` for `SeqRSR`: from a state where the address word `a < 2^160` is blacklisted,
`balances[a]` is not lower at the end. -/
theorem listed_seq_allSR {C : Address} {S S' : State.TransactionState}
    (h : SeqRSR C (fun X Y => ProtKept C X Y ∧ ListedNoDec C X Y) NotOwnerS S S')
    {a : U256} (ha : a.toNat < 2 ^ 160) (hl : Listed C S a) : NoDec C (mapSlot a 2) S S' := by
  refine seqRSR_lift (I := fun X => Listed C X a) (R := NoDec C (mapSlot a 2))
    (fun hq => hq.2.1) (fun _ => NoDec.refl _ _ _) (fun h1 h2 => h1.trans h2)
    (fun hu hI => ⟨NoDec.of_writes (W := fun _ => False) (.of_same hu) id,
      by unfold Listed; rw [hu]; exact hI⟩) ?_ h hl
  intro S S' fork message F hC he hk hq hl
  obtain ⟨hno, -, K⟩ := hq
  subst hC
  have hprot := he.protKept K hno (fun hd X Y hf => (hk hd X Y hf).1)
  refine ⟨he.listed K.toSepOn ha hl (.inr hno) (fun hd X Y hf => (hk hd X Y hf).2), ?_⟩
  unfold Listed
  rw [hprot _ (.inr (.inr (.inr (.inr (.inr ⟨a, ha, rfl⟩)))))]
  exact hl

/-- **Allowances over a sequence over both meters, deprecated or not, any reservoir.**
`allowKept_seq_allS` for `SeqRSR`: the slot of `allowed` keyed by `y` and `z` keeps its word. -/
theorem allowKept_seq_allSR {y z : U256} {C : Address} {S S' : State.TransactionState}
    (h : SeqRSR C (AllowKept C) (@NoAllowFnS y z) S S') : AllowKeptAt y z C S S' := by
  refine seqRSR_lift (I := fun _ => True) (R := AllowKeptAt y z C) (fun hq => hq.2.2.1)
    (fun _ => rfl) (fun h1 h2 => h2.trans h1) (fun hu _ => ⟨hu _, trivial⟩) ?_ h trivial
  intro S S' fork message F hC he hk hq _
  obtain ⟨ha, hf, -, K⟩ := hq
  subst hC
  exact ⟨he.allowKept K ⟨ha, hf⟩ hk, trivial⟩

/-- **Supply over a sequence over both meters, deprecated or not, any reservoir.**
`supply_seq_allS` for `SeqRSR`: slot 1 keeps its word. -/
theorem supply_seq_allSR {C : Address} {S S' : State.TransactionState}
    (h : SeqRSR C (SupplyKept C) NoSupplyFnS S S') : storageAt S' C 1 = storageAt S C 1 := by
  refine seqRSR_lift (I := fun _ => True) (R := fun X Y => storageAt Y C 1 = storageAt X C 1)
    (fun hq => hq.2.2.2.1) (fun _ => rfl) (fun h1 h2 => h2.trans h1)
    (fun hu _ => ⟨hu 1, trivial⟩) ?_ h trivial
  intro S S' fork message F hC he hk hq _
  obtain ⟨hi, hr', hd, -, K⟩ := hq
  subst hC
  refine ⟨?_, trivial⟩
  rcases he.supply K hk with (h1 | ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩) | ⟨e, -⟩
  · exact h1
  · exact absurd e hi
  · exact absurd e hr'
  · exact absurd e hd
  · exact absurd e hd

/-! ## Top-level messages -/

/-- From Paris, a top-level message whose code is `CODE` (no value moved, no precompile, call data
below 2^256 bytes), run by EthLib's `processMessage` over `StateGasMeter` from any starting meter,
whose runner `processRunner` meets `KeepsAtSR … R` at the reservoir of that meter when `C` is
deprecated, that ends with no error, is a `RunOkRSR` step. -/
theorem runOkRSR_process {fork : Fork} (hparis : .paris ≤ fork)
    {message : Message fork} {state : State.TransactionState} {substate : Substate}
    {R : State.TransactionState → State.TransactionState → Prop}
    (hmc : message.code = CODE)
    (noValue : ¬(message.shouldTransferValue = true ∧ message.value ≠ 0))
    (noPrecompile : precompileAddress fork message = none)
    (hsize : message.data.size < 2 ^ 256)
    {meter : StateGasMeter} {held : GasMeter.gasHeld meter ≤ message.gas}
    (hkeeps : byte20 (storageAt state message.currentTarget 10) ≠ 0 →
      KeepsAtSR (processRunner fork message.gas) message state
        (upAddr state message) meter.reservoir R)
    {ended : { evm : Evm fork StateGasMeter // GasMeter.gasHeld evm.gas ≤ message.gas }}
    (hproc : processMessage fork message state substate meter held = .ok ended)
    (hok : ended.val.error = none) :
    RunOkRSR message.currentTarget R state ended.val.state message := by
  have hst : startState fork message state = state := by
    simp only [startState, show ¬fork < Fork.paris from Nat.not_lt.mpr hparis, ite_false]
  have hberlin : Fork.berlin ≤ fork := Nat.le_trans (by decide) hparis
  generalize hr : runFrame (step fork) (step_decreases fork) message.gas
    (processRunner fork message.gas)
    (startFrame message (startState fork message state) substate meter) held = result
  have hmap := processMessage_map_val noValue noPrecompile hr
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
    have start := Meter.at_startFrameS hmc (startState fork message state) substate meter
    rw [hst] at start hr
    exact ⟨substate, _, message.gas, processRunner fork message.gas, _, s, _, rfl,
      hberlin, hsize, hkeeps, start, hr, hse, by rw [hend]⟩

/-- **Top-level messages over the EIP-8037 meter, deprecated or not, any reservoir, as steps of
`SeqRSR`.** From Paris, every top-level message whose code is `CODE` (no precompile, call data
below 2^256 bytes, any value), run by EthLib's `processMessage` over `StateGasMeter` to the end
from any starting meter, whose runner `processRunner` meets `KeepsAtSR … R` at the reservoir of
that meter when `C` is deprecated, is a `RunOkRSR` step when it ends with no error and an
`Untouched` step when it ends with an error. No hypothesis on the reservoir. -/
theorem process_stepSecDR {fork : Fork} (hparis : .paris ≤ fork)
    {message : Message fork} {state : State.TransactionState} {substate : Substate}
    {R : State.TransactionState → State.TransactionState → Prop}
    (hmc : message.code = CODE)
    (noPrecompile : precompileAddress fork message = none)
    (hsize : message.data.size < 2 ^ 256)
    {meter : StateGasMeter} {held : GasMeter.gasHeld meter ≤ message.gas}
    (hkeeps : byte20 (storageAt state message.currentTarget 10) ≠ 0 →
      KeepsAtSR (processRunner fork message.gas) message state
        (upAddr state message) meter.reservoir R)
    {ended : { evm : Evm fork StateGasMeter // GasMeter.gasHeld evm.gas ≤ message.gas }}
    (hproc : processMessage fork message state substate meter held = .ok ended) :
    RunOkRSR message.currentTarget R state ended.val.state message ∨
      Untouched message.currentTarget state ended.val.state := by
  by_cases herr : ended.val.error = none
  · by_cases ht : message.shouldTransferValue = true ∧ message.value ≠ 0
    · exact absurd herr (process_value_failsS (Nat.le_trans (by decide) hparis) hmc noPrecompile
        hsize ht.2 hproc)
    · exact .inl (runOkRSR_process hparis hmc ht noPrecompile hsize hkeeps hproc herr)
  · exact .inr fun _ =>
      getStorage_processMessage_of_error hproc (Option.isSome_iff_ne_none.mpr herr) _ _


/-! ## One top-level message, to each security property (round 49) -/

/-- A top-level message as a `SeqRSR` sequence of one step (or none), under the hypotheses of
`process_stepSecDR` and the condition `Q` of the sequence at its start. -/
theorem seqRSR_process {fork : Fork} (hparis : .paris ≤ fork)
    {message : Message fork} {state : State.TransactionState} {substate : Substate}
    {R : State.TransactionState → State.TransactionState → Prop}
    (hmc : message.code = CODE)
    (noPrecompile : precompileAddress fork message = none)
    (hsize : message.data.size < 2 ^ 256)
    {meter : StateGasMeter} {held : GasMeter.gasHeld meter ≤ message.gas}
    (hkeeps : byte20 (storageAt state message.currentTarget 10) ≠ 0 →
      KeepsAtSR (processRunner fork message.gas) message state
        (upAddr state message) meter.reservoir R)
    {ended : { evm : Evm fork StateGasMeter // GasMeter.gasHeld evm.gas ≤ message.gas }}
    (hproc : processMessage fork message state substate meter held = .ok ended)
    {Q : ∀ {fork : Fork}, Message fork → State.TransactionState → Prop} (hq : Q message state) :
    SeqRSR message.currentTarget R Q state ended.val.state := by
  rcases process_stepSecDR hparis hmc noPrecompile hsize hkeeps hproc with h | h
  · exact .callS h hq (.nil _)
  · exact .other h (.nil _)

/-- **`nonOwner` for one top-level message over the EIP-8037 meter, any reservoir, round 49.**
`nonOwner_seq_allSR` for the sequence of `seqRSR_process`: the property from the start state of the
message to its end state, under the runner hypothesis of `process_stepSecDR` for this property and
the condition of the sequence. -/
theorem nonOwner_processSR {fork : Fork} (hparis : .paris ≤ fork)
    {message : Message fork} {state : State.TransactionState} {substate : Substate}
    (hmc : message.code = CODE)
    (noPrecompile : precompileAddress fork message = none)
    (hsize : message.data.size < 2 ^ 256)
    {meter : StateGasMeter} {held : GasMeter.gasHeld meter ≤ message.gas}
    (hkeeps : byte20 (storageAt state message.currentTarget 10) ≠ 0 →
      KeepsAtSR (processRunner fork message.gas) message state
        (upAddr state message) meter.reservoir
        (ProtKept message.currentTarget))
    {ended : { evm : Evm fork StateGasMeter // GasMeter.gasHeld evm.gas ≤ message.gas }}
    (hproc : processMessage fork message state substate meter held = .ok ended)
    (hq : NotOwnerS message state) :
    ProtKept message.currentTarget state ended.val.state :=
  nonOwner_seq_allSR (seqRSR_process (R := (ProtKept message.currentTarget))
    (Q := NotOwnerS)
    hparis hmc noPrecompile hsize hkeeps hproc hq)

/-- **`paused` for one top-level message over the EIP-8037 meter, any reservoir, round 49.**
`paused_seq_allSR` for the sequence of `seqRSR_process`: the property from the start state of the
message to its end state, under the runner hypothesis of `process_stepSecDR` for this property and
the condition of the sequence. -/
theorem paused_processSR {fork : Fork} (hparis : .paris ≤ fork)
    {message : Message fork} {state : State.TransactionState} {substate : Substate}
    (hmc : message.code = CODE)
    (noPrecompile : precompileAddress fork message = none)
    (hsize : message.data.size < 2 ^ 256)
    {meter : StateGasMeter} {held : GasMeter.gasHeld meter ≤ message.gas}
    (hkeeps : byte20 (storageAt state message.currentTarget 10) ≠ 0 →
      KeepsAtSR (processRunner fork message.gas) message state
        (upAddr state message) meter.reservoir
        (fun X Y => ProtKept message.currentTarget X Y ∧ BalKept message.currentTarget X Y))
    {ended : { evm : Evm fork StateGasMeter // GasMeter.gasHeld evm.gas ≤ message.gas }}
    (hproc : processMessage fork message state substate meter held = .ok ended)
    (hq : NotOwnerS message state)
    (hpaused : byte20 (storageAt state message.currentTarget 0) ≠ 0) :
    BalKept message.currentTarget state ended.val.state :=
  paused_seq_allSR (seqRSR_process (R := (fun X Y => ProtKept message.currentTarget X Y ∧
      BalKept message.currentTarget X Y))
    (Q := NotOwnerS)
    hparis hmc noPrecompile hsize hkeeps hproc hq) hpaused

/-- **`listed` for one top-level message over the EIP-8037 meter, any reservoir, round 49.**
`listed_seq_allSR` for the sequence of `seqRSR_process`: the property from the start state of the
message to its end state, under the runner hypothesis of `process_stepSecDR` for this property and
the condition of the sequence. -/
theorem listed_processSR {fork : Fork} (hparis : .paris ≤ fork)
    {message : Message fork} {state : State.TransactionState} {substate : Substate}
    (hmc : message.code = CODE)
    (noPrecompile : precompileAddress fork message = none)
    (hsize : message.data.size < 2 ^ 256)
    {meter : StateGasMeter} {held : GasMeter.gasHeld meter ≤ message.gas}
    (hkeeps : byte20 (storageAt state message.currentTarget 10) ≠ 0 →
      KeepsAtSR (processRunner fork message.gas) message state
        (upAddr state message) meter.reservoir
        (fun X Y => ProtKept message.currentTarget X Y ∧ ListedNoDec message.currentTarget X Y))
    {ended : { evm : Evm fork StateGasMeter // GasMeter.gasHeld evm.gas ≤ message.gas }}
    (hproc : processMessage fork message state substate meter held = .ok ended)
    (hq : NotOwnerS message state)
    {a : U256} (ha : a.toNat < 2 ^ 160) (hl : Listed message.currentTarget state a) :
    NoDec message.currentTarget (mapSlot a 2) state ended.val.state :=
  listed_seq_allSR (seqRSR_process (R := (fun X Y => ProtKept message.currentTarget X Y ∧
      ListedNoDec message.currentTarget X Y))
    (Q := NotOwnerS)
    hparis hmc noPrecompile hsize hkeeps hproc hq) ha hl

/-- **`allowKept` for one top-level message over the EIP-8037 meter, any reservoir, round 49.**
`allowKept_seq_allSR` for the sequence of `seqRSR_process`: the property from the start state of the
message to its end state, under the runner hypothesis of `process_stepSecDR` for this property and
the condition of the sequence. -/
theorem allowKept_processSR {y z : U256} {fork : Fork} (hparis : .paris ≤ fork)
    {message : Message fork} {state : State.TransactionState} {substate : Substate}
    (hmc : message.code = CODE)
    (noPrecompile : precompileAddress fork message = none)
    (hsize : message.data.size < 2 ^ 256)
    {meter : StateGasMeter} {held : GasMeter.gasHeld meter ≤ message.gas}
    (hkeeps : byte20 (storageAt state message.currentTarget 10) ≠ 0 →
      KeepsAtSR (processRunner fork message.gas) message state
        (upAddr state message) meter.reservoir
        (AllowKept message.currentTarget))
    {ended : { evm : Evm fork StateGasMeter // GasMeter.gasHeld evm.gas ≤ message.gas }}
    (hproc : processMessage fork message state substate meter held = .ok ended)
    (hq : NoAllowFnS y z message state) :
    AllowKeptAt y z message.currentTarget state ended.val.state :=
  allowKept_seq_allSR (seqRSR_process (R := (AllowKept message.currentTarget))
    (Q := @NoAllowFnS y z)
    hparis hmc noPrecompile hsize hkeeps hproc hq)

/-- **`supply` for one top-level message over the EIP-8037 meter, any reservoir, round 49.**
`supply_seq_allSR` for the sequence of `seqRSR_process`: the property from the start state of the
message to its end state, under the runner hypothesis of `process_stepSecDR` for this property and
the condition of the sequence. -/
theorem supply_processSR {fork : Fork} (hparis : .paris ≤ fork)
    {message : Message fork} {state : State.TransactionState} {substate : Substate}
    (hmc : message.code = CODE)
    (noPrecompile : precompileAddress fork message = none)
    (hsize : message.data.size < 2 ^ 256)
    {meter : StateGasMeter} {held : GasMeter.gasHeld meter ≤ message.gas}
    (hkeeps : byte20 (storageAt state message.currentTarget 10) ≠ 0 →
      KeepsAtSR (processRunner fork message.gas) message state
        (upAddr state message) meter.reservoir
        (SupplyKept message.currentTarget))
    {ended : { evm : Evm fork StateGasMeter // GasMeter.gasHeld evm.gas ≤ message.gas }}
    (hproc : processMessage fork message state substate meter held = .ok ended)
    (hq : NoSupplyFnS message state) :
    storageAt ended.val.state message.currentTarget 1 =
      storageAt state message.currentTarget 1 :=
  supply_seq_allSR (seqRSR_process (R := (SupplyKept message.currentTarget))
    (Q := NoSupplyFnS)
    hparis hmc noPrecompile hsize hkeeps hproc hq)

end UsdtVerify.Security
