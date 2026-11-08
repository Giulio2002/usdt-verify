import UsdtVerify.Usdt.Invariant.All
import UsdtVerify.Usdt.Invariant.SeqMeter
import UsdtVerify.Usdt.Complete.Deprecated.Meter

/-!
# The invariant on the deprecated paths over EthLib's EIP-8037 meter (round 39)

`Usdt/Invariant/All.lean` (`inv_call_ns`) for the deprecated paths, first over `RunC` with any
relation `Run` of the child, then for a run over `StateGasMeter` from reservoir 0.

- `KeepsInvAtC Run`, `HonestBalanceAtC Run`: `KeepsInvAt` and `HonestBalanceAt` for the relation
  `Run`. `LocalForwardC`: `LocalForward` for `Run`.
- `dep_X_localC` (the six forwarding functions), `dep_destroy_localC`, `inv_dep_destroy_iffC`,
  `inv_dep_destroyC`: the lemmas of All.lean over `RunC`.
- `KeepsInvAtS`, `HonestBalanceAtS`: the two runner assumptions for a message runner over
  `StateGasMeter`, about the calls the code makes (`SentVia`, of the `toNat` caller).
  `keepsInvAtC_of_S`, `honestBalanceAtC_of_S`: they give the assumptions over `RunC` for `RunS`.
- `inv_call_depS`: every deprecated call over `StateGasMeter` from reservoir 0 that ends with no
  error keeps `Inv`, under `KeepsInvAtS` and, for destroyBlackFunds, `HonestBalanceAtS`.
- `inv_call_anyD`: `inv_call_any` (any reservoir when not deprecated) together with the deprecated
  case (reservoir 0).
-/

namespace UsdtVerify.Complete

open EthLib.Base (Fork U256 Address)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open UsdtVerify.Gas
open UsdtVerify.Meter (toNat)
open Invariant Deprecated DeprecatedBalance DeprecatedDestroy DestroySpec

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate} {evm s : Evm fork Nat} {gas : Nat}
  {Run : Evm fork Nat → Message fork → Evm fork Nat → Prop}

/-- `KeepsInvAt` for a relation `Run` of the child. -/
def KeepsInvAtC (Run : Evm fork Nat → Message fork → Evm fork Nat → Prop) (message : Message fork)
    (state : State.TransactionState) : Prop :=
  ∀ caller msg child, SentVia message state (upAddr state message) caller msg →
    Run caller msg child → child.error = none →
    Inv message.currentTarget caller.state → Inv message.currentTarget child.state

/-- `HonestBalanceAt` for a relation `Run` of the child. -/
def HonestBalanceAtC (Run : Evm fork Nat → Message fork → Evm fork Nat → Prop)
    (message : Message fork) (state : State.TransactionState) : Prop :=
  ∀ caller msg child, SentVia message state (upAddr state message) caller msg →
    Run caller msg child → msg.data = dataB message → child.error = none →
      resWord (outMemOf (memD message) child.output) =
        storageAt child.state message.currentTarget (balSlot message)

/-- `LocalForward` for a relation `Run` of the child. -/
def LocalForwardC (Run : Evm fork Nat → Message fork → Evm fork Nat → Prop)
    (message : Message fork) (state : State.TransactionState) (s : Evm fork Nat) : Prop :=
  ∃ caller msg child, SentVia message state (upAddr state message) caller msg ∧
    Run caller msg child ∧ child.error = none ∧
    (hasAccount caller.state message.currentTarget ↔ hasAccount state message.currentTarget) ∧
    s.state = child.state

/-- `LocalForwardC` keeps `Inv` under `KeepsInvAtC`. -/
theorem inv_of_localC (hkeeps : KeepsInvAtC Run message state)
    (hI : Inv message.currentTarget state)
    (h : LocalForwardC Run message state s) : Inv message.currentTarget s.state := by
  obtain ⟨caller, msg, child, hsv, hch, he, -, hst⟩ := h
  have hv := hsv.choose_spec.choose_spec.2.2.2
  rw [hst]
  exact hkeeps caller msg child hsv hch he
    ((DepInv.inv_congr (fun n => hv.1 message.currentTarget n)).2 hI)

theorem dep_totalSupply_localC (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x18160ddd)
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (hrun : RunC fork Run evm s) (hE : EndsOk fork evm) (hok : s.error = none) :
    LocalForwardC Run message state s := by
  obtain ⟨c, r, hcode, hroute, -, -, -, caller, msg, child, hch, he, hfwd, -, hcs, -, -, -, -, -, hst, -⟩ :=
    dep_totalSupply_completeC hfork hsize' hsel hdep start hrun hE hok
  refine ⟨caller, msg, child, ⟨c, r, hcode, hroute, sendsVia_data hfwd, ?_⟩, hch, he, ?_, ?_⟩
  · rw [hcs]
    exact sameView_recordAccountRead (sameView_route (sameView_recordAccountRead
      ⟨fun a n => by simp only [callState, storageAt_readSlot], fun a => rfl⟩ _) r) _
  · rw [hcs]
    exact hasAccount_caller_iff _ Iff.rfl
  · rw [hst, state_incorporateChild]


theorem dep_balanceOf_localC (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x70a08231)
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (hrun : RunC fork Run evm s) (hE : EndsOk fork evm) (hok : s.error = none) :
    LocalForwardC Run message state s := by
  obtain ⟨c, r, hcode, hroute, -, -, -, caller, msg, child, hch, he, hfwd, -, hcs, -, -, -, -, -, hst, -⟩ :=
    dep_balanceOf_completeC hfork hsize' hsel hdep start hrun hE hok
  refine ⟨caller, msg, child, ⟨c, r, hcode, hroute, sendsVia_data hfwd, ?_⟩, hch, he, ?_, ?_⟩
  · rw [hcs]
    exact sameView_recordAccountRead (sameView_route (sameView_recordAccountRead
      ⟨fun a n => by simp only [callState, storageAt_readSlot], fun a => rfl⟩ _) r) _
  · rw [hcs]
    exact hasAccount_caller_iff _ Iff.rfl
  · rw [hst, state_incorporateChild]


theorem dep_allowance_localC (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xdd62ed3e)
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (hrun : RunC fork Run evm s) (hE : EndsOk fork evm) (hok : s.error = none) :
    LocalForwardC Run message state s := by
  obtain ⟨c, r, hcode, hroute, -, -, -, caller, msg, child, hch, he, hfwd, -, hcs, -, -, -, -, -, hst, -⟩ :=
    dep_allowance_completeC hfork hsize' hsel hdep rfl rfl start hrun hE hok
  refine ⟨caller, msg, child, ⟨c, r, hcode, hroute, sendsVia_data hfwd, ?_⟩, hch, he, ?_, ?_⟩
  · rw [hcs]
    exact sameView_recordAccountRead (sameView_route (sameView_recordAccountRead
      ⟨fun a n => by simp only [callState, storageAt_readSlot], fun a => rfl⟩ _) r) _
  · rw [hcs]
    exact hasAccount_caller_iff _ Iff.rfl
  · rw [hst, state_incorporateChild]


theorem dep_approve_localC (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x095ea7b3)
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (hrun : RunC fork Run evm s) (hE : EndsOk fork evm) (hok : s.error = none) :
    LocalForwardC Run message state s := by
  obtain ⟨c, r, hcode, hroute, -, -, -, -, caller, msg, child, hch, he, hfwd, -, hcs, -, -, -, -, -, hst, -⟩ :=
    dep_approve_completeC hfork hsize' hsel hdep rfl rfl start hrun hE hok
  refine ⟨caller, msg, child, ⟨c, r, hcode, hroute, sendsVia_data hfwd, ?_⟩, hch, he, ?_, ?_⟩
  · rw [hcs]
    exact sameView_recordAccountRead (sameView_route (sameView_recordAccountRead
      ⟨fun a n => by simp only [callState, storageAt_readSlot], fun a => rfl⟩ _) r) _
  · rw [hcs]
    exact hasAccount_caller_iff _ Iff.rfl
  · rw [hst, state_incorporateChild]


theorem dep_transfer_localC (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xa9059cbb)
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (hrun : RunC fork Run evm s) (hE : EndsOk fork evm) (hok : s.error = none) :
    LocalForwardC Run message state s := by
  obtain ⟨c, r, hcode, hroute, -, -, -, -, -, caller, msg, child, hch, he, hfwd, -, hcs, -, -, -, -, -, hst, -⟩ :=
    dep_transfer_completeC hfork hsize' hsel hdep rfl rfl rfl rfl start hrun hE hok
  refine ⟨caller, msg, child, ⟨c, r, hcode, hroute, sendsVia_data hfwd, ?_⟩, hch, he, ?_, ?_⟩
  · rw [hcs]
    exact sameView_recordAccountRead (sameView_route (sameView_recordAccountRead
      ⟨fun a n => by simp only [DeprecatedTransfer.callStateT, Transfer.shortState,
        storageAt_readSlot], fun a => rfl⟩ _) r) _
  · rw [hcs]
    exact hasAccount_caller_iff _ Iff.rfl
  · rw [hst, state_incorporateChild]


theorem dep_transferFrom_localC (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x23b872dd)
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (hrun : RunC fork Run evm s) (hE : EndsOk fork evm) (hok : s.error = none) :
    LocalForwardC Run message state s := by
  obtain ⟨c, r, hcode, hroute, -, -, -, -, -, caller, msg, child, hch, he, hfwd, -, hcs, -, -, -, -, -, hst, -⟩ :=
    dep_transferFrom_completeC hfork hsize' hsel hdep rfl rfl rfl rfl start hrun hE hok
  refine ⟨caller, msg, child, ⟨c, r, hcode, hroute, sendsVia_data hfwd, ?_⟩, hch, he, ?_, ?_⟩
  · rw [hcs]
    exact sameView_recordAccountRead (sameView_route (sameView_recordAccountRead
      ⟨fun a n => by simp only [DeprecatedTransferFrom.callStateF, TransferFrom.checkState,
        storageAt_readSlot], fun a => rfl⟩ _) r) _
  · rw [hcs]
    exact hasAccount_caller_iff _ Iff.rfl
  · rw [hst, state_incorporateChild]


theorem dep_destroy_localC (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xf3bdc228)
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0)
    (hkeeps : KeepsInvAtC Run message state)
    (hI : Inv message.currentTarget state)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (hrun : RunC fork Run evm s) (hE : EndsOk fork evm) (hok : s.error = none) :
    ∃ caller msg child, Run caller msg child ∧ child.error = none ∧
      SentVia message state (upAddr state message) caller msg ∧
      msg.data = dataB message ∧
      hasAccount child.state message.currentTarget ∧ Inv message.currentTarget child.state ∧
      s.state = tailState child.state message.currentTarget (addrArg message.data 0)
        (resWord (outMemOf (memD message) child.output)) := by
  obtain ⟨c, r, hcode, hroute, -, -, -, -, -, caller, msg, child, hch, he, -, hacc', hfwd, -,
      hcs, -, -, -, -, -, hst, -⟩ :=
    dep_destroy_completeC hfork hsize' hsel hdep rfl rfl rfl rfl start hrun hE hok
  have hv : SameView caller.state state := by
    rw [hcs]
    exact sameView_recordAccountRead (sameView_route (sameView_recordAccountRead
      ⟨fun a n => by simp only [callStateD, preState, storageAt_readSlot], fun a => rfl⟩ _) r) _
  have hsv : SentVia message state (upAddr state message) caller msg :=
    ⟨c, r, hcode, hroute, sendsVia_data hfwd, hv⟩
  have hIc : Inv message.currentTarget caller.state :=
    (DepInv.inv_congr (fun n => hv.1 message.currentTarget n)).2 hI
  refine ⟨caller, msg, child, hch, he, hsv, hfwd.2.2.2.2.2.2.1, hacc',
    hkeeps caller msg child hsv hch he hIc, ?_⟩
  rw [hst, state_incorporateChild]


theorem inv_dep_destroy_iffC (K : SepOn (callKeys message state)) (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xf3bdc228)
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0)
    (hkeeps : KeepsInvAtC Run message state)
    (hI : Inv message.currentTarget state)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (hrun : RunC fork Run evm s) (hE : EndsOk fork evm) (hok : s.error = none) :
    ∃ caller msg child, Run caller msg child ∧ child.error = none ∧
      SentVia message state (upAddr state message) caller msg ∧
      msg.data = dataB message ∧
      (Inv message.currentTarget s.state ↔ resWord (outMemOf (memD message) child.output) =
        storageAt child.state message.currentTarget (balSlot message)) := by
  obtain ⟨caller, msg, child, hch, he, hsv, hmd, hacc', hI', hst⟩ :=
    dep_destroy_localC hfork hsize' hsel hdep hkeeps hI start hrun hE hok
  refine ⟨caller, msg, child, hch, he, hsv, hmd, ?_⟩
  rw [hst]
  exact DepInv.inv_tail_iff K.fixed hacc' (addrArg_lt _ _) K.uniqArg0 hI' _


theorem inv_dep_destroyC (K : SepOn (callKeys message state)) (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xf3bdc228)
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0)
    (hkeeps : KeepsInvAtC Run message state)
    (hhonest : HonestBalanceAtC Run message state)
    (hI : Inv message.currentTarget state)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (hrun : RunC fork Run evm s) (hE : EndsOk fork evm) (hok : s.error = none) : Inv message.currentTarget s.state := by
  obtain ⟨caller, msg, child, hch, he, hsv, hmd, hiff⟩ :=
    inv_dep_destroy_iffC K hfork hsize' hsel hdep hkeeps hI start hrun hE hok
  exact hiff.2 (hhonest caller msg child hsv hch hmd he)


/-! ## Over `StateGasMeter` -/

section Meter

variable {bound : Nat} {runChild : MessageRunner fork StateGasMeter bound}

/-- `KeepsInvAt` for a message runner over `StateGasMeter`: every call that the code of `C` makes
from `state` (`SentVia`, of the `toNat` caller) and that the runner ends with no error keeps
`Inv C` from the caller state to the child's end state. -/
def KeepsInvAtS (runChild : MessageRunner fork StateGasMeter bound) (message : Message fork)
    (state : State.TransactionState) : Prop :=
  ∀ caller msg lt child, SentVia message state (upAddr state message) (toNat caller) msg →
    runChild caller msg lt = .ok child → child.1.error = none →
    Inv message.currentTarget caller.state → Inv message.currentTarget child.1.state

/-- `HonestBalanceAt` for a message runner over `StateGasMeter`. -/
def HonestBalanceAtS (runChild : MessageRunner fork StateGasMeter bound) (message : Message fork)
    (state : State.TransactionState) : Prop :=
  ∀ caller msg lt child, SentVia message state (upAddr state message) (toNat caller) msg →
    runChild caller msg lt = .ok child → msg.data = dataB message → child.1.error = none →
      resWord (outMemOf (memD message) child.1.output) =
        storageAt child.1.state message.currentTarget (balSlot message)

theorem keepsInvAtC_of_S (h : KeepsInvAtS runChild message state) :
    KeepsInvAtC (RunS runChild) message state := by
  rintro caller msg child hsv ⟨cS, lt, chS, hch, rfl, hchN⟩ he hI
  have cs : child.state = chS.1.state := by rw [hchN]; rfl
  have ce : child.error = chS.1.error := by rw [hchN]; rfl
  rw [cs]
  exact h cS msg lt chS hsv hch (ce ▸ he) hI

theorem honestBalanceAtC_of_S (h : HonestBalanceAtS runChild message state) :
    HonestBalanceAtC (RunS runChild) message state := by
  rintro caller msg child hsv ⟨cS, lt, chS, hch, rfl, hchN⟩ hmd he
  have cs : child.state = chS.1.state := by rw [hchN]; rfl
  have ce : child.error = chS.1.error := by rw [hchN]; rfl
  have co : child.output = chS.1.output := by rw [hchN]; rfl
  rw [cs, co]
  exact h cS msg lt chS hsv hch hmd (ce ▸ he)

/-- **Every successful deprecated call over the EIP-8037 meter keeps the invariant.** From
Berlin, from a frame `m` of `StateGasMeter` with reservoir 0 whose `toNat` is the fresh frame of
`CODE`, deprecated (byte 20 of slot 10 not 0), with the hypotheses of `inv_call_ns` stated for a
runner over `StateGasMeter` (`KeepsInvAtS`, and `HonestBalanceAtS` for destroyBlackFunds): if
`Inv C state` holds and the loop of the interpreter, for any gas bound and that runner, ends with
no error, then `Inv C s.state` holds. -/
theorem inv_call_depS {m s : Evm fork StateGasMeter}
    (K : SepOn (callKeys message state)) (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (h7 : StrForm (storageAt state message.currentTarget 7))
    (h8 : StrForm (storageAt state message.currentTarget 8))
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0)
    (hkeeps : KeepsInvAtS runChild message state)
    (hhonest : selector message.data = 0xf3bdc228 → HonestBalanceAtS runChild message state)
    (hI : Inv message.currentTarget state)
    (start : At CODE message 0 [] .empty gas state substate (toNat m))
    (hres : m.gas.reservoir = 0) {within : GasMeter.gasHeld m.gas ≤ bound}
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild m within = .ok s)
    (hok : s.error = none) : Inv message.currentTarget s.state := by
  obtain ⟨G, hC⟩ := runC_of_sgm hfork hrun hok (.inl hres)
  have hE := endsOk_of_sgm hfork hrun hok
  obtain ⟨G', hEnds⟩ := Shadow.shadow_ends hfork hrun hok
  have start' := at_sh start (Shadow.budget m)
  have hk := keepsInvAtC_of_S hkeeps
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
  | ⟨31, _⟩, hi => exact hsG G ▸ inv_dep_destroyC K hfork hsize' (hi.trans rfl) hdep hk (honestBalanceAtC_of_S (hhonest (hi.trans rfl))) hI start hC hE (hokG G)
  | ⟨n + 32, h⟩, _ => exact absurd h (by omega)

/-- **Every successful call over the EIP-8037 meter keeps the invariant, deprecated or not.**
`inv_call_any` (any reservoir) when not deprecated, `inv_call_depS` (reservoir 0) when
deprecated. -/
theorem inv_call_anyD {m s : Evm fork StateGasMeter}
    (K : SepOn (callKeys message state)) (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (h7 : StrForm (storageAt state message.currentTarget 7))
    (h8 : StrForm (storageAt state message.currentTarget 8))
    (hkeeps : byte20 (storageAt state message.currentTarget 10) ≠ 0 →
      KeepsInvAtS runChild message state)
    (hhonest : byte20 (storageAt state message.currentTarget 10) ≠ 0 →
      selector message.data = 0xf3bdc228 → HonestBalanceAtS runChild message state)
    (hI : Inv message.currentTarget state)
    (start : At CODE message 0 [] .empty gas state substate (toNat m))
    (hres : byte20 (storageAt state message.currentTarget 10) ≠ 0 → m.gas.reservoir = 0)
    {within : GasMeter.gasHeld m.gas ≤ bound}
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild m within = .ok s)
    (hok : s.error = none) : Inv message.currentTarget s.state := by
  by_cases hdep : byte20 (storageAt state message.currentTarget 10) = 0
  · exact inv_call_any K hfork hsize' hdep h7 h8 hI start hrun hok
  · exact inv_call_depS K hfork hsize' h7 h8 hdep (hkeeps hdep) (hhonest hdep) hI start
      (hres hdep) hrun hok

/-! ## Sequences and `processMessage` -/

/-- One successful run of `CODE` over `StateGasMeter` for a message to `C`, from `S` to `S'`,
deprecated, from reservoir 0, under the hypotheses of `inv_call_depS`. -/
def GoodCallDS (C : Address) (S S' : State.TransactionState) : Prop :=
  ∃ (fork : Fork) (message : Message fork) (substate : Substate) (gas bound : Nat)
    (runChild : MessageRunner fork StateGasMeter bound) (m s : Evm fork StateGasMeter)
    (within : GasMeter.gasHeld m.gas ≤ bound),
    message.currentTarget = C ∧ .berlin ≤ fork ∧ message.data.size < 2 ^ 256 ∧
    SepOn (callKeys message S) ∧ StrForm (storageAt S C 7) ∧ StrForm (storageAt S C 8) ∧
    byte20 (storageAt S C 10) ≠ 0 ∧ KeepsInvAtS runChild message S ∧
    (selector message.data = 0xf3bdc228 → HonestBalanceAtS runChild message S) ∧
    At CODE message 0 [] .empty gas S substate (toNat m) ∧ m.gas.reservoir = 0 ∧
    Evm.runFrame (step fork) (step_decreases fork) bound runChild m within = .ok s ∧
    s.error = none ∧ S' = s.state

/-- One successful deprecated call over `StateGasMeter` keeps `Inv C`. -/
theorem inv_goodCallDS {C : Address} {S S' : State.TransactionState}
    (h : GoodCallDS C S S') (hI : Inv C S) : Inv C S' := by
  obtain ⟨fork, message, substate, gas, bound, runChild, m, s, within, hC, hfork, hsize, K, h7,
    h8, hdep, hk, hh, start, hres, hrun, hok, rfl⟩ := h
  subst hC
  exact inv_call_depS K hfork hsize h7 h8 hdep hk hh hI start hres hrun hok

/-- `CallsS` steps and deprecated calls over `StateGasMeter` (`GoodCallDS`). -/
inductive CallsDS (C : Address) : State.TransactionState → State.TransactionState → Prop
  | nil (S : State.TransactionState) : CallsDS C S S
  | calls {S S' S'' : State.TransactionState} : CallsS C S S' → CallsDS C S' S'' →
      CallsDS C S S''
  | callDS {S S' S'' : State.TransactionState} : GoodCallDS C S S' → CallsDS C S' S'' →
      CallsDS C S S''

/-- `Inv C` along every finite sequence of `CallsDS C`. -/
theorem inv_callsDS {C : Address} {S S' : State.TransactionState}
    (h : CallsDS C S S') (hI : Inv C S) : Inv C S' := by
  induction h with
  | nil => exact hI
  | calls hc _ ih => exact ih (inv_callsS hc hI)
  | callDS hg _ ih => exact ih (inv_goodCallDS hg hI)

/-- **Deprecated top-level messages over the EIP-8037 meter.** From Paris, a top-level message to
`C` (code `CODE`, no precompile, call data below 2^256 bytes, deprecated), run by EthLib's
`processMessage` over `StateGasMeter` to the end from a starting meter with reservoir 0, under `KeepsInvAtS` and, for
destroyBlackFunds, `HonestBalanceAtS` of `processRunnerM`, is a `GoodCallDS` when it ends with no
error and an `Untouched` step when it ends with an error. -/
theorem process_stepDS {fork : Fork} (hparis : .paris ≤ fork)
    {message : Message fork} {state : State.TransactionState} {substate : Substate}
    (hmc : message.code = CODE)
    (noPrecompile : precompileAddress fork message = none)
    (hsize : message.data.size < 2 ^ 256) (K : SepOn (callKeys message state))
    (h7 : StrForm (storageAt state message.currentTarget 7))
    (h8 : StrForm (storageAt state message.currentTarget 8))
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0)
    (hkeeps : KeepsInvAtS (ProcessMeter.processRunnerM fork message.gas) message state)
    (hhonest : selector message.data = 0xf3bdc228 →
      HonestBalanceAtS (ProcessMeter.processRunnerM fork message.gas) message state)
    {meter : StateGasMeter} {held : GasMeter.gasHeld meter ≤ message.gas}
    (hres : meter.reservoir = 0)
    {ended : { evm : Evm fork StateGasMeter // GasMeter.gasHeld evm.gas ≤ message.gas }}
    (hproc : processMessage fork message state substate meter held = .ok ended) :
    GoodCallDS message.currentTarget state ended.val.state ∨
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
      (ProcessMeter.processRunnerM fork message.gas)
      (startFrame message (startState fork message state) substate meter) held = result
    have hmap := ProcessMeter.processMessage_map_valM ht noPrecompile hres'
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
      have start := ProcessMeter.at_startFrameS hmc (startState fork message state) substate meter
      rw [hst] at start hres'
      exact ⟨fork, message, substate, _, message.gas, ProcessMeter.processRunnerM fork message.gas,
        _, s, _, rfl, hberlin, hsize, K, h7, h8, hdep, hkeeps, hhonest, start, hres, hres', hse,
        by rw [hend]⟩
  · exact .inr (fun _ => Local.processMessage_failed_getStorage hproc herr _ _)

/-- **Every top-level message over the EIP-8037 meter, deprecated or not.** From Paris, a
top-level message to `C` (code `CODE`, no precompile, call data below 2^256 bytes) run by
`processMessage` over `StateGasMeter` from any starting meter is a `GoodCallS` (not deprecated,
any reservoir), a `GoodCallDS` (deprecated, under its hypotheses, a starting meter with reservoir
0) or an `Untouched` step. -/
theorem process_stepSD {fork : Fork} (hparis : .paris ≤ fork)
    {message : Message fork} {state : State.TransactionState} {substate : Substate}
    (hmc : message.code = CODE)
    (noPrecompile : precompileAddress fork message = none)
    (hsize : message.data.size < 2 ^ 256) (K : SepOn (callKeys message state))
    (h7 : StrForm (storageAt state message.currentTarget 7))
    (h8 : StrForm (storageAt state message.currentTarget 8))
    (hkeeps : byte20 (storageAt state message.currentTarget 10) ≠ 0 →
      KeepsInvAtS (ProcessMeter.processRunnerM fork message.gas) message state)
    (hhonest : byte20 (storageAt state message.currentTarget 10) ≠ 0 →
      selector message.data = 0xf3bdc228 →
      HonestBalanceAtS (ProcessMeter.processRunnerM fork message.gas) message state)
    {meter : StateGasMeter} {held : GasMeter.gasHeld meter ≤ message.gas}
    (hres : byte20 (storageAt state message.currentTarget 10) ≠ 0 → meter.reservoir = 0)
    {ended : { evm : Evm fork StateGasMeter // GasMeter.gasHeld evm.gas ≤ message.gas }}
    (hproc : processMessage fork message state substate meter held = .ok ended) :
    GoodCallS message.currentTarget state ended.val.state ∨
      GoodCallDS message.currentTarget state ended.val.state ∨
      Untouched message.currentTarget state ended.val.state := by
  by_cases hdep : byte20 (storageAt state message.currentTarget 10) = 0
  · rcases process_stepS hparis hmc noPrecompile hsize K h7 h8 hdep hproc with h | h
    · exact .inl h
    · exact .inr (.inr h)
  · exact .inr (process_stepDS hparis hmc noPrecompile hsize K h7 h8 hdep (hkeeps hdep)
      (hhonest hdep) (hres hdep) hproc)

/-- `process_stepDS` for the fresh meter of the message, whose reservoir is that of the
message. -/
theorem process_stepDS_start {fork : Fork} (hparis : .paris ≤ fork)
    {message : Message fork} {state : State.TransactionState} {substate : Substate}
    (hmc : message.code = CODE)
    (noPrecompile : precompileAddress fork message = none)
    (hsize : message.data.size < 2 ^ 256) (K : SepOn (callKeys message state))
    (h7 : StrForm (storageAt state message.currentTarget 7))
    (h8 : StrForm (storageAt state message.currentTarget 8))
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0)
    (hres : message.reservoir = 0)
    (hkeeps : KeepsInvAtS (ProcessMeter.processRunnerM fork message.gas) message state)
    (hhonest : selector message.data = 0xf3bdc228 →
      HonestBalanceAtS (ProcessMeter.processRunnerM fork message.gas) message state)
    {ended : { evm : Evm fork StateGasMeter // GasMeter.gasHeld evm.gas ≤ message.gas }}
    (hproc : processMessage fork message state substate = .ok ended) :
    GoodCallDS message.currentTarget state ended.val.state ∨
      Untouched message.currentTarget state ended.val.state :=
  process_stepDS hparis hmc noPrecompile hsize K h7 h8 hdep hkeeps hhonest hres hproc

/-- `process_stepSD` for the fresh meter of the message, whose reservoir is that of the
message. -/
theorem process_stepSD_start {fork : Fork} (hparis : .paris ≤ fork)
    {message : Message fork} {state : State.TransactionState} {substate : Substate}
    (hmc : message.code = CODE)
    (noPrecompile : precompileAddress fork message = none)
    (hsize : message.data.size < 2 ^ 256) (K : SepOn (callKeys message state))
    (h7 : StrForm (storageAt state message.currentTarget 7))
    (h8 : StrForm (storageAt state message.currentTarget 8))
    (hres : byte20 (storageAt state message.currentTarget 10) ≠ 0 → message.reservoir = 0)
    (hkeeps : byte20 (storageAt state message.currentTarget 10) ≠ 0 →
      KeepsInvAtS (ProcessMeter.processRunnerM fork message.gas) message state)
    (hhonest : byte20 (storageAt state message.currentTarget 10) ≠ 0 →
      selector message.data = 0xf3bdc228 →
      HonestBalanceAtS (ProcessMeter.processRunnerM fork message.gas) message state)
    {ended : { evm : Evm fork StateGasMeter // GasMeter.gasHeld evm.gas ≤ message.gas }}
    (hproc : processMessage fork message state substate = .ok ended) :
    GoodCallS message.currentTarget state ended.val.state ∨
      GoodCallDS message.currentTarget state ended.val.state ∨
      Untouched message.currentTarget state ended.val.state :=
  process_stepSD hparis hmc noPrecompile hsize K h7 h8 hkeeps hhonest hres hproc

end Meter

end UsdtVerify.Complete
