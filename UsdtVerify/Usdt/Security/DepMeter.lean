import UsdtVerify.Usdt.Security.Meter
import UsdtVerify.Usdt.Complete.Deprecated.Meter

/-!
# The security properties when deprecated, over EthLib's EIP-8037 meter (round 39)

The `_call_all` theorems of Usdt/Security/ (deprecated or not) for a run of the loop over
`StateGasMeter`, for any gas bound and any message runner over `StateGasMeter`, from a frame whose
reservoir is 0 when `C` is deprecated (no hypothesis on the reservoir otherwise).

- `FwdAtS runS message S ua X Y`: `FwdAt` for a runner over `StateGasMeter` (`SentVia` of the
  `toNat` caller). `KeepsAtS runS message S ua R`: `KeepsAt` for such a runner;
  `KeepsAtS.fwd`. Since round 41 both are about calls from a caller and with a message of
  reservoir 0, as the CALL from reservoir 0 sends them (`callStep_child_res0`).
- `EffectDF F message S S'`: `EffectD` with the forwarded call given by a relation `F` on the
  states before and after it.
- `effect_allS`: every run over `StateGasMeter` that ends with no error ends in a state described
  by `EffectDF (FwdAtS runS message state (upAddr state message))`, from `dep_X_completeS` when
  deprecated (reservoir 0) and `effect_local_any` otherwise.
- `EffectDF.paused`, `.protKept`, `.listed`, `.allowKept`, `.supply`: the lemmas `EffectD.X` for
  `EffectDF`.
- `paused_call_allS`, `nonOwner_call_allS`, `listed_call_allS`, `allowKept_call_allS`,
  `supply_call_allS`: the `_call_all` theorems over `StateGasMeter`, with the runner assumptions
  stated by `KeepsAtS` for the same relations (`BalKept`, `ProtKept`, `ListedNoDec`, `AllowKept`,
  `SupplyKept` of `C`).
- `owner_only_allS` (round 41): `owner_only` over `StateGasMeter`, deprecated or not, reservoir 0
  for deprecated destroyBlackFunds.

Usdt/Security/DepMeterR.lean (round 44) has the same results from any reservoir when deprecated.
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

/-- `FwdAt` for a message runner over `StateGasMeter`: one call that the code of `C` makes from
`S` to `ua` (`SentVia` of the `toNat` caller), from a caller and with a message of reservoir 0,
ended with no error, from `X` to `Y`. -/
def FwdAtS (runS : MessageRunner fork StateGasMeter bound) (message : Message fork)
    (S : State.TransactionState) (ua : Address) (X Y : State.TransactionState) : Prop :=
  ∃ caller msg lt child, SentVia message S ua (toNat caller) msg ∧
    caller.gas.reservoir = 0 ∧ msg.reservoir = 0 ∧
    runS caller msg lt = .ok child ∧ child.1.error = none ∧ caller.state = X ∧ child.1.state = Y

/-- `KeepsAt` for a message runner over `StateGasMeter`, for the calls from a caller and with a
message of reservoir 0, as the CALL from reservoir 0 sends them. -/
def KeepsAtS (runS : MessageRunner fork StateGasMeter bound) (message : Message fork)
    (S : State.TransactionState) (ua : Address)
    (R : State.TransactionState → State.TransactionState → Prop) : Prop :=
  ∀ caller msg lt child, SentVia message S ua (toNat caller) msg →
    caller.gas.reservoir = 0 → msg.reservoir = 0 →
    runS caller msg lt = .ok child → child.1.error = none → R caller.state child.1.state

theorem KeepsAtS.fwd {S : State.TransactionState} {ua : Address}
    {R : State.TransactionState → State.TransactionState → Prop} {X Y : State.TransactionState}
    (hk : KeepsAtS runS message S ua R) (h : FwdAtS runS message S ua X Y) : R X Y := by
  obtain ⟨caller, msg, lt, child, hs, hcr, hmr, hch, he, rfl, rfl⟩ := h
  exact hk caller msg lt child hs hcr hmr hch he

/-- `EffectD` with the forwarded call given by the relation `F`. -/
inductive EffectDF (F : State.TransactionState → State.TransactionState → Prop)
    (message : Message fork) (S S' : State.TransactionState) : Prop
  | loc (h : Effect message S S')
  | fwd (hdep : byte20 (storageAt S message.currentTarget 10) ≠ 0)
      (hsel : FwdFn (selector message.data))
      (hT : selector message.data = 0xa9059cbb →
        byte20 (storageAt S message.currentTarget 0) = 0 ∧
        (storageAt S message.currentTarget (blackSlot message)).toNat % 256 = 0)
      (hF : selector message.data = 0x23b872dd →
        byte20 (storageAt S message.currentTarget 0) = 0 ∧
        (storageAt S message.currentTarget (blackFrom (fromArg message))).toNat % 256 = 0)
      (X : State.TransactionState)
      (hX : ∀ n, storageAt X message.currentTarget n = storageAt S message.currentTarget n)
      (hf : F X S')
  | dfwd (hdep : byte20 (storageAt S message.currentTarget 10) ≠ 0)
      (hsel : selector message.data = 0xf3bdc228)
      (howner : callerWord message = ownerOf S message.currentTarget)
      (hlisted : (storageAt S message.currentTarget (listSlot (addrArg message.data 0))).toNat %
        256 ≠ 0)
      (X Y : State.TransactionState) (d : U256)
      (hX : ∀ n, storageAt X message.currentTarget n = storageAt S message.currentTarget n)
      (hf : F X Y)
      (hacc : hasAccount Y message.currentTarget)
      (hst : S' = DeprecatedDestroy.tailState Y message.currentTarget (addrArg message.data 0) d)

theorem state_incorporateChildS (caller child : Evm fork StateGasMeter) :
    (incorporateChild fork caller child).state = child.state := by
  unfold incorporateChild; split <;> rfl

/-- A forwarded call found by `dep_X_completeS`, as `FwdAtS`. -/
theorem fwdS_of {ua : Address} {c : ByteArray} {r : Route} {d : ByteArray}
    {caller : Evm fork StateGasMeter} {msg : Message fork} {lt : msg.gas < bound}
    {child : { child : Evm fork StateGasMeter // GasMeter.gasHeld child.gas ≤ msg.gas }}
    {S' : State.TransactionState}
    (hcode : state.getCode (state.getAccount ua).codeHash = .ok c) (hroute : Routes fork state c r)
    (hfwd : SendsVia message ua c r d msg) (hv : SameView caller.state state)
    (hcr : caller.gas.reservoir = 0) (hmr : msg.reservoir = 0)
    (hch : runS caller msg lt = .ok child) (he : child.1.error = none)
    (hst : S' = (incorporateChild fork caller child.1).state) :
    ∃ X, (∀ n, storageAt X message.currentTarget n = storageAt state message.currentTarget n) ∧
      FwdAtS runS message state ua X S' :=
  ⟨caller.state, fun n => hv.1 _ n, caller, msg, lt, child,
    ⟨c, r, hcode, hroute, sendsVia_data hfwd, hv⟩, hcr, hmr, hch, he, rfl,
    by rw [hst, state_incorporateChildS]⟩

/-- **The effect of every successful call over the EIP-8037 meter, deprecated or not.** From
Berlin, from a frame `m` of `StateGasMeter` whose `toNat` is the fresh frame of `CODE` (reservoir 0
when deprecated), with slots 7 and 8 of `StrForm`: every run of the loop, for any gas bound and
message runner over `StateGasMeter`, that ends with no error ends in a state described by
`EffectDF` for the calls of that runner (`FwdAtS`). No assumption on the runner. -/
theorem effect_allS (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (h7 : StrForm (storageAt state message.currentTarget 7))
    (h8 : StrForm (storageAt state message.currentTarget 8))
    {m s : Evm fork StateGasMeter}
    (start : At CODE message 0 [] .empty gas state substate (toNat m))
    (hres : byte20 (storageAt state message.currentTarget 10) ≠ 0 → m.gas.reservoir = 0)
    {within : GasMeter.gasHeld m.gas ≤ bound}
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runS m within = .ok s)
    (hok : s.error = none) :
    EffectDF (FwdAtS runS message state (upAddr state message)) message state s.state := by
  by_cases hdep : byte20 (storageAt state message.currentTarget 10) = 0
  · exact .loc (effect_local_any hfork hsize' (.inl hdep) h7 h8 start hrun hok)
  by_cases hf : FlagFn (selector message.data)
  case neg => exact .loc (effect_local_any hfork hsize' (.inr hf) h7 h8 start hrun hok)
  have hr := hres hdep
  have ne : ∀ {a b : Nat}, selector message.data = a → a ≠ b → selector message.data ≠ b :=
    fun h hab e => hab (h.symm.trans e)
  rcases hf with (h | h | h | h | h | h) | h
  · obtain ⟨c, r, hcode, hroute, -, -, -, -, caller, msg, lt, child, hch, he, hcr, hmr, hfwd, -, hcs, -, -,
      -, hst, -⟩ := dep_approve_completeS hfork hsize' h hdep rfl rfl start hr hrun hok
    obtain ⟨X, hX, hF⟩ := fwdS_of hcode hroute hfwd (by
      rw [hcs]; exact sameView_recordAccountRead (sameView_route (sameView_recordAccountRead
        ⟨fun a n => by simp only [callState, storageAt_readSlot], fun a => rfl⟩ _) r) _) hcr hmr hch he hst
    exact .fwd hdep (.inl h) (fun e => absurd e (ne h (by decide)))
      (fun e => absurd e (ne h (by decide))) X hX hF
  · obtain ⟨c, r, hcode, hroute, -, -, -, caller, msg, lt, child, hch, he, hcr, hmr, hfwd, -, hcs, -, -,
      -, hst, -⟩ := dep_totalSupply_completeS hfork hsize' h hdep start hr hrun hok
    obtain ⟨X, hX, hF⟩ := fwdS_of hcode hroute hfwd (by
      rw [hcs]; exact sameView_recordAccountRead (sameView_route (sameView_recordAccountRead
        ⟨fun a n => by simp only [callState, storageAt_readSlot], fun a => rfl⟩ _) r) _) hcr hmr hch he hst
    exact .fwd hdep (.inr (.inl h)) (fun e => absurd e (ne h (by decide)))
      (fun e => absurd e (ne h (by decide))) X hX hF
  · obtain ⟨c, r, hcode, hroute, hpause, hblack, -, -, -, caller, msg, lt, child, hch, he, hcr, hmr, hfwd, -,
      hcs, -, -, -, hst, -⟩ :=
      dep_transferFrom_completeS hfork hsize' h hdep rfl rfl rfl rfl start hr hrun hok
    obtain ⟨X, hX, hF⟩ := fwdS_of hcode hroute hfwd (by
      rw [hcs]; exact sameView_recordAccountRead (sameView_route (sameView_recordAccountRead
        ⟨fun a n => by simp only [DeprecatedTransferFrom.callStateF,
        TransferFrom.checkState, storageAt_readSlot], fun a => rfl⟩ _) r) _) hcr hmr hch he hst
    exact .fwd hdep (.inr (.inr (.inl h))) (fun e => absurd e (ne h (by decide)))
      (fun _ => ⟨hpause, hblack⟩) X hX hF
  · obtain ⟨c, r, hcode, hroute, -, -, -, caller, msg, lt, child, hch, he, hcr, hmr, hfwd, -, hcs, -, -,
      -, hst, -⟩ := dep_balanceOf_completeS hfork hsize' h hdep start hr hrun hok
    obtain ⟨X, hX, hF⟩ := fwdS_of hcode hroute hfwd (by
      rw [hcs]; exact sameView_recordAccountRead (sameView_route (sameView_recordAccountRead
        ⟨fun a n => by simp only [callState, storageAt_readSlot], fun a => rfl⟩ _) r) _) hcr hmr hch he hst
    exact .fwd hdep (.inr (.inr (.inr (.inl h)))) (fun e => absurd e (ne h (by decide)))
      (fun e => absurd e (ne h (by decide))) X hX hF
  · obtain ⟨c, r, hcode, hroute, hpause, hblack, -, -, -, caller, msg, lt, child, hch, he, hcr, hmr, hfwd, -,
      hcs, -, -, -, hst, -⟩ :=
      dep_transfer_completeS hfork hsize' h hdep rfl rfl rfl rfl start hr hrun hok
    obtain ⟨X, hX, hF⟩ := fwdS_of hcode hroute hfwd (by
      rw [hcs]; exact sameView_recordAccountRead (sameView_route (sameView_recordAccountRead
        ⟨fun a n => by simp only [DeprecatedTransfer.callStateT,
        Transfer.shortState, storageAt_readSlot], fun a => rfl⟩ _) r) _) hcr hmr hch he hst
    exact .fwd hdep (.inr (.inr (.inr (.inr (.inl h))))) (fun _ => ⟨hpause, hblack⟩)
      (fun e => absurd e (ne h (by decide))) X hX hF
  · obtain ⟨c, r, hcode, hroute, -, -, -, caller, msg, lt, child, hch, he, hcr, hmr, hfwd, -, hcs, -, -,
      -, hst, -⟩ := dep_allowance_completeS hfork hsize' h hdep rfl rfl start hr hrun hok
    obtain ⟨X, hX, hF⟩ := fwdS_of hcode hroute hfwd (by
      rw [hcs]; exact sameView_recordAccountRead (sameView_route (sameView_recordAccountRead
        ⟨fun a n => by simp only [callState, storageAt_readSlot], fun a => rfl⟩ _) r) _) hcr hmr hch he hst
    exact .fwd hdep (.inr (.inr (.inr (.inr (.inr h))))) (fun e => absurd e (ne h (by decide)))
      (fun e => absurd e (ne h (by decide))) X hX hF
  · obtain ⟨c, r, hcode, hroute, howner, hlisted, -, -, -, caller, msg, lt, child, hch, he, hcr, hmr, -,
      hacc', hfwd, -, hcs, -, -, -, hst, -⟩ :=
      dep_destroy_completeS hfork hsize' h hdep rfl rfl rfl rfl start hr hrun hok
    have hv : SameView caller.state state := by
      rw [hcs]
      exact sameView_recordAccountRead (sameView_route (sameView_recordAccountRead
        ⟨fun a n => by simp only [DeprecatedDestroy.callStateD, DestroySpec.preState,
        storageAt_readSlot], fun a => rfl⟩ _) r) _
    refine .dfwd hdep h howner hlisted caller.state child.1.state
      (resWord (DeprecatedBalance.outMemOf (DeprecatedDestroy.memD message) child.1.output))
      (fun n => hv.1 _ n)
      ⟨caller, msg, lt, child, ⟨c, r, hcode, hroute, sendsVia_data hfwd, hv⟩, hcr, hmr, hch, he,
        rfl, rfl⟩
      hacc' ?_
    rw [hst, state_incorporateChildS]

/-! ## The properties -/

variable {F : State.TransactionState → State.TransactionState → Prop}

theorem EffectDF.paused {S S' : State.TransactionState} (K : SepOn (callKeys message S))
    (h : EffectDF F message S S')
    (hp : byte20 (storageAt S message.currentTarget 0) ≠ 0)
    (hk : byte20 (storageAt S message.currentTarget 10) ≠ 0 →
      ∀ X Y, F X Y → BalKept message.currentTarget X Y) :
    BalKept message.currentTarget S S' ∨
      (callerWord message = ownerOf S message.currentTarget ∧
        (selector message.data = 0xcc872b66 ∨ selector message.data = 0xdb006a75 ∨
          selector message.data = 0xf3bdc228)) := by
  cases h with
  | loc h => exact h.paused K hp
  | fwd hdep _ hT hF X hX hf =>
    by_cases e1 : selector message.data = 0xa9059cbb
    · exact absurd (hT e1).1 hp
    by_cases e2 : selector message.data = 0x23b872dd
    · exact absurd (hF e2).1 hp
    exact .inl fun x hx => (hk hdep X S' hf x hx).trans (hX _)
  | dfwd _ hsel howner => exact .inr ⟨howner, .inr (.inr hsel)⟩

theorem EffectDF.protKept {S S' : State.TransactionState} (K : SecSep (callKeys message S))
    (h : EffectDF F message S S')
    (hno : callerWord message ≠ ownerOf S message.currentTarget)
    (hk : byte20 (storageAt S message.currentTarget 10) ≠ 0 →
      ∀ X Y, F X Y → ProtKept message.currentTarget X Y) :
    ProtKept message.currentTarget S S' := by
  cases h with
  | loc h => exact fun n hn => h.nonOwnerK K.toSepOn hno n (protected_not_kba K hn)
  | fwd hdep _ _ _ X hX hf => exact fun n hn => (hk hdep X S' hf n hn).trans (hX n)
  | dfwd _ _ howner => exact absurd howner hno

theorem EffectDF.listed {S S' : State.TransactionState} (K : SepOn (callKeys message S))
    (h : EffectDF F message S S')
    {a : U256} (ha : a.toNat < 2 ^ 160) (hl : Listed message.currentTarget S a)
    (hsel : (selector message.data ≠ 0xdb006a75 ∧ selector message.data ≠ 0xf3bdc228) ∨
      callerWord message ≠ ownerOf S message.currentTarget)
    (hk : byte20 (storageAt S message.currentTarget 10) ≠ 0 →
      ∀ X Y, F X Y → ListedNoDec message.currentTarget X Y) :
    NoDec message.currentTarget (mapSlot a 2) S S' := by
  cases h with
  | loc h => exact h.listed K ha hl hsel
  | fwd hdep _ _ _ X hX hf =>
    exact NoDec.congr_left hX (hk hdep X S' hf a ha (by unfold Listed; rw [hX]; exact hl))
  | dfwd _ hs howner =>
    rcases hsel with ⟨-, hd⟩ | hno
    · exact absurd hs hd
    · exact absurd howner hno

theorem EffectDF.allowKept {y z : U256} {S S' : State.TransactionState}
    (K : SecSep (y :: z :: callKeys message S)) (h : EffectDF F message S S')
    (hsel : selector message.data ≠ 0x095ea7b3 ∧ selector message.data ≠ 0x23b872dd)
    (hk : byte20 (storageAt S message.currentTarget 10) ≠ 0 →
      ∀ X Y, F X Y → AllowKept message.currentTarget X Y) :
    AllowKeptAt y z message.currentTarget S S' := by
  cases h with
  | loc h => exact h.allowKept K hsel
  | fwd hdep _ _ _ X hX hf => exact (hk hdep X S' hf y z).trans (hX _)
  | dfwd hdep _ _ _ X Y d hX hf hacc hst =>
    have hbo : ¬ BalOrOne (mapSlot y (mapSlot z 5)) := not_balOrOne K.allowYZ.1 K.allowYZ.2.1
    unfold AllowKeptAt
    rw [hst, writes_tail hacc (bal_arg _ _) d _ hbo, hk hdep X Y hf y z, hX]

theorem EffectDF.supply {S S' : State.TransactionState} (K : SepOn (callKeys message S))
    (h : EffectDF F message S S')
    (hk : byte20 (storageAt S message.currentTarget 10) ≠ 0 →
      ∀ X Y, F X Y → SupplyKept message.currentTarget X Y) :
    SupplyStepD message S S' := by
  cases h with
  | loc h => exact .inl (h.supply K)
  | fwd hdep _ _ _ X hX hf => exact .inl (.inl ((hk hdep X S' hf).trans (hX 1)))
  | dfwd hdep hsel howner _ X Y d hX hf hacc hst =>
    refine .inr ⟨hsel, howner, d, ?_⟩
    rw [hst]
    simp only [DeprecatedDestroy.tailState]
    rw [storageAt_writeSlot_self (hasAccount_writeSlot hacc),
      storageAt_writeSlot_of_ne hacc (Ne.symm (bal_ne_one K.fixed (addrArg_lt _ _))),
      hk hdep X Y hf, hX]

/-! ## Single calls over `StateGasMeter`, deprecated or not -/

section Calls

variable {m s : Evm fork StateGasMeter} {within : GasMeter.gasHeld m.gas ≤ bound}

/-- **Pause, one call over the EIP-8037 meter, deprecated or not.** `paused_call_all` for a run
over `StateGasMeter` (reservoir 0 when deprecated), with `KeepsBal` stated for the runner over
`StateGasMeter` (`KeepsAtS … BalKept`). -/
theorem paused_call_allS (K : SepOn (callKeys message state)) (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (hpaused : byte20 (storageAt state message.currentTarget 0) ≠ 0)
    (h7 : StrForm (storageAt state message.currentTarget 7))
    (h8 : StrForm (storageAt state message.currentTarget 8))
    (hkeeps : byte20 (storageAt state message.currentTarget 10) ≠ 0 →
      KeepsAtS runS message state (upAddr state message) (BalKept message.currentTarget))
    (start : At CODE message 0 [] .empty gas state substate (toNat m))
    (hres : byte20 (storageAt state message.currentTarget 10) ≠ 0 → m.gas.reservoir = 0)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runS m within = .ok s)
    (hok : s.error = none) :
    BalKept message.currentTarget state s.state ∨
      (callerWord message = ownerOf state message.currentTarget ∧
        (selector message.data = 0xcc872b66 ∨ selector message.data = 0xdb006a75 ∨
          selector message.data = 0xf3bdc228)) :=
  (effect_allS hfork hsize' h7 h8 start hres hrun hok).paused K hpaused
    fun hd _ _ hf => (hkeeps hd).fwd hf

/-- **Non-owner, one call over the EIP-8037 meter, deprecated or not.** `nonOwner_call_all` for a
run over `StateGasMeter` (reservoir 0 when deprecated), with `KeepsSlots` stated for the runner
over `StateGasMeter`. -/
theorem nonOwner_call_allS (K : SecSep (callKeys message state)) (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (h7 : StrForm (storageAt state message.currentTarget 7))
    (h8 : StrForm (storageAt state message.currentTarget 8))
    (hno : callerWord message ≠ ownerOf state message.currentTarget)
    (hkeeps : byte20 (storageAt state message.currentTarget 10) ≠ 0 →
      KeepsAtS runS message state (upAddr state message) (ProtKept message.currentTarget))
    (start : At CODE message 0 [] .empty gas state substate (toNat m))
    (hres : byte20 (storageAt state message.currentTarget 10) ≠ 0 → m.gas.reservoir = 0)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runS m within = .ok s)
    (hok : s.error = none) : ProtKept message.currentTarget state s.state :=
  (effect_allS hfork hsize' h7 h8 start hres hrun hok).protKept K hno
    fun hd _ _ hf => (hkeeps hd).fwd hf

/-- **Blacklist, one call over the EIP-8037 meter, deprecated or not.** `listed_call_all` for a
run over `StateGasMeter` (reservoir 0 when deprecated), with `KeepsListed` stated for the runner
over `StateGasMeter`. -/
theorem listed_call_allS (K : SepOn (callKeys message state)) (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (h7 : StrForm (storageAt state message.currentTarget 7))
    (h8 : StrForm (storageAt state message.currentTarget 8))
    {a : U256} (ha : a.toNat < 2 ^ 160) (hl : Listed message.currentTarget state a)
    (hsel : (selector message.data ≠ 0xdb006a75 ∧ selector message.data ≠ 0xf3bdc228) ∨
      callerWord message ≠ ownerOf state message.currentTarget)
    (hkeeps : byte20 (storageAt state message.currentTarget 10) ≠ 0 →
      KeepsAtS runS message state (upAddr state message) (ListedNoDec message.currentTarget))
    (start : At CODE message 0 [] .empty gas state substate (toNat m))
    (hres : byte20 (storageAt state message.currentTarget 10) ≠ 0 → m.gas.reservoir = 0)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runS m within = .ok s)
    (hok : s.error = none) : NoDec message.currentTarget (mapSlot a 2) state s.state :=
  (effect_allS hfork hsize' h7 h8 start hres hrun hok).listed K ha hl hsel
    fun hd _ _ hf => (hkeeps hd).fwd hf

/-- **Allowances, one call over the EIP-8037 meter, deprecated or not.** `allowKept_call_all`
for a run over `StateGasMeter` (reservoir 0 when deprecated), with `KeepsAllow` stated for the
runner over `StateGasMeter`. -/
theorem allowKept_call_allS {y z : U256} (K : SecSep (y :: z :: callKeys message state))
    (hfork : .berlin ≤ fork) (hsize' : message.data.size < 2 ^ 256)
    (h7 : StrForm (storageAt state message.currentTarget 7))
    (h8 : StrForm (storageAt state message.currentTarget 8))
    (hsel : selector message.data ≠ 0x095ea7b3 ∧ selector message.data ≠ 0x23b872dd)
    (hkeeps : byte20 (storageAt state message.currentTarget 10) ≠ 0 →
      KeepsAtS runS message state (upAddr state message) (AllowKept message.currentTarget))
    (start : At CODE message 0 [] .empty gas state substate (toNat m))
    (hres : byte20 (storageAt state message.currentTarget 10) ≠ 0 → m.gas.reservoir = 0)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runS m within = .ok s)
    (hok : s.error = none) : AllowKeptAt y z message.currentTarget state s.state :=
  (effect_allS hfork hsize' h7 h8 start hres hrun hok).allowKept K hsel
    fun hd _ _ hf => (hkeeps hd).fwd hf

/-- **Supply, one call over the EIP-8037 meter, deprecated or not.** `supply_call_all` for a run
over `StateGasMeter` (reservoir 0 when deprecated), with `KeepsSupply` stated for the runner over
`StateGasMeter`. -/
theorem supply_call_allS (K : SepOn (callKeys message state)) (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (h7 : StrForm (storageAt state message.currentTarget 7))
    (h8 : StrForm (storageAt state message.currentTarget 8))
    (hkeeps : byte20 (storageAt state message.currentTarget 10) ≠ 0 →
      KeepsAtS runS message state (upAddr state message) (SupplyKept message.currentTarget))
    (start : At CODE message 0 [] .empty gas state substate (toNat m))
    (hres : byte20 (storageAt state message.currentTarget 10) ≠ 0 → m.gas.reservoir = 0)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runS m within = .ok s)
    (hok : s.error = none) : SupplyStepD message state s.state :=
  (effect_allS hfork hsize' h7 h8 start hres hrun hok).supply K
    fun hd _ _ hf => (hkeeps hd).fwd hf

/-- **Owner functions over the EIP-8037 meter, deprecated or not** (round 41). `owner_only` for a
run of the loop over `StateGasMeter`, any gas bound and message runner, no assumption on the
runner, from a frame `m` whose `toNat` is the fresh frame of `CODE`, with reservoir 0 when the
call is deprecated destroyBlackFunds (any reservoir otherwise, `owner_only_any`): every run of one
of the ten owner functions that ends with no error is a call by the owner. -/
theorem owner_only_allS (hfork : .berlin ≤ fork) (hsize' : message.data.size < 2 ^ 256)
    (hsel : OwnerFn (selector message.data))
    (start : At CODE message 0 [] .empty gas state substate (toNat m))
    (hres : byte20 (storageAt state message.currentTarget 10) ≠ 0 →
      selector message.data = 0xf3bdc228 → m.gas.reservoir = 0)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runS m within = .ok s)
    (hok : s.error = none) : callerWord message = ownerOf state message.currentTarget := by
  by_cases hd : byte20 (storageAt state message.currentTarget 10) = 0 ∨
      selector message.data ≠ 0xf3bdc228
  · exact owner_only_any hfork hsize' hsel hd start hrun hok
  · obtain ⟨hdep, h⟩ := not_or.mp hd
    have hs : selector message.data = 0xf3bdc228 := Classical.byContradiction h
    obtain ⟨_, _, -, -, howner, -⟩ :=
      dep_destroy_completeS hfork hsize' hs hdep rfl rfl rfl rfl start (hres hdep hs) hrun hok
    exact howner

end Calls

end UsdtVerify.Security
