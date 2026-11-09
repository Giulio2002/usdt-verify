import UsdtVerify.Usdt.Invariant.Calls
import UsdtVerify.Evm.Frame
import UsdtVerify.Evm.Route
import UsdtVerify.Usdt.Invariant.DeprecatedDestroy
import UsdtVerify.Usdt.Complete.Deprecated.Destroy

/-!
# The invariant over every successful call, deprecated or not

When deprecated, seven functions call the upgraded contract `ua` (the low 160 bits of slot 10).
What they do to the local storage (the storage of the contract `C`), from the completeness
theorems `dep_*_complete`:

- totalSupply, balanceOf, allowance, transfer, approve, transferFrom (`dep_*_local`, stated with
  `LocalForward`): up to the CALL the code only reads; at the CALL the storage of `C` is the start
  storage (`storageAt` agrees at every slot), and `C` has an account in the caller state iff it
  has one in the start state; after the CALL the code writes nothing: the end state is the state
  the runner's child frame ended in (`child.state`).
  So `Inv C` at the end is `Inv C` of the child's state.
- destroyBlackFunds (`dep_destroy_local`): the same up to and through the CALL, then the two
  writes over the child's state `S`: the end state is `tailState S C a d`, `d` the word that the
  call wrote at 0x60. By `DepInv.inv_tail_iff` (under `FixedSep` and `UniqBal a`, `Inv C S`, an account of `C`
  in `S`), `Inv` holds at the end iff `d = balances[a]` in `S` (`inv_dep_destroy_iff`).
  `dep_destroy_complete` proves the account of `C` in `S` for every run that ends with no error.

The callee may call back into `C` (reentrancy), so what the child's state holds is an assumption
on the runner. Named assumptions:

- `KeepsInv runChild C ua`: whenever the runner ends a message from `C` to `ua` with no error,
  from a caller state where `Inv C` holds, `Inv C` holds in the child's end state.
  It asks nothing about the account of `C`.
  It says nothing about what the callee does in between (it covers any reentrant calls into `C`).
- `HonestBalance runChild message state`: whenever the runner ends a message from `C` to `ua` with
  the data `balanceOf(a)` (`dataB message`) with no error, the word the call writes at 0x60 is
  `balances[a]` in the child's end state.

Through round 19 the callee assumption was `KeepsInvAcc` (now so named): only from a caller state
where `C` has an account, and it also kept the account; `inv_call_ns` then took an account of `C`
when deprecated (`hacc`).
Since round 20 it takes `KeepsInv` and no account.
`keepsInv_of_acc`: `KeepsInvAcc` and the case with no account (`KeepsInvNoAcc`) give `KeepsInv`.
A missing account of `C` does not make a step of the forwarding paths fail: the completeness
theorems `dep_*_complete` and the forward specifications of the six forwarding functions take no
account; those of destroyBlackFunds take none in the start state (their `hkeep` is an account at
the end of each forwarded call).
It reaches the runner: `localForward_noAcc` (with no account at the start, the CALL is sent from
a caller state with no account of `C`).
So that case cannot be ruled out from the code; `KeepsInv` assumes it for the runner.

`inv_call_ns`: `Complete.inv_call` without `hdep`: under `SepOn` of the call's keys, `StrForm` of slots 7 and 8,
`Inv` at the start, and, when deprecated, `KeepsInv` and (for destroyBlackFunds) `HonestBalance`,
every successful call ends with `Inv`.
No account of `C` is assumed, deprecated or not.
No hypothesis on the code of the upgraded address: when it is an EIP-7702 delegation, the message
still has `ua` as its current target (it runs the delegate's code), so both assumptions apply to
it as stated.
-/

namespace UsdtVerify.Complete

open EthLib.Base (Fork U256 Address)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open UsdtVerify.Gas
open Invariant Deprecated DeprecatedBalance DeprecatedDestroy DestroySpec

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate} {bound : Nat} {runChild : MessageRunner fork Nat bound}
  {evm s : Evm fork Nat} {gas : Nat}

/-- The named callee assumption: whenever the runner ends a message from `C` to `ua` with no
error, from a caller state where `Inv C` holds, `Inv C` holds in the child's end state.
It asks nothing about the account of `C`, in the caller state or in the child's end state.
Any reentrant call into `C` is inside the child's run, so this covers it. -/
def KeepsInv (runChild : MessageRunner fork Nat bound) (C ua : Address) : Prop :=
  ∀ caller msg lt child, runChild caller msg lt = .ok child → msg.caller = C →
    msg.currentTarget = ua → child.1.error = none → Inv C caller.state → Inv C child.1.state

/-- The callee assumption of rounds 15 to 19: as `KeepsInv`, but only from a caller state where
`C` has an account, and the child's end state also keeps that account. -/
def KeepsInvAcc (runChild : MessageRunner fork Nat bound) (C ua : Address) : Prop :=
  ∀ caller msg lt child, runChild caller msg lt = .ok child → msg.caller = C →
    msg.currentTarget = ua → child.1.error = none → hasAccount caller.state C →
      Inv C caller.state → hasAccount child.1.state C ∧ Inv C child.1.state

/-- The case of `KeepsInv` that `KeepsInvAcc` leaves out: a caller state where `C` has no
account. -/
def KeepsInvNoAcc (runChild : MessageRunner fork Nat bound) (C ua : Address) : Prop :=
  ∀ caller msg lt child, runChild caller msg lt = .ok child → msg.caller = C →
    msg.currentTarget = ua → child.1.error = none → ¬hasAccount caller.state C →
      Inv C caller.state → Inv C child.1.state

/-- `KeepsInvAcc` and `KeepsInvNoAcc` together give `KeepsInv`. -/
theorem keepsInv_of_acc {C ua : Address} (hacc : KeepsInvAcc runChild C ua)
    (hno : KeepsInvNoAcc runChild C ua) : KeepsInv runChild C ua := by
  intro caller msg lt child hch hmc hmt he hI
  by_cases ha : hasAccount caller.state C
  · exact (hacc caller msg lt child hch hmc hmt he ha hI).2
  · exact hno caller msg lt child hch hmc hmt he ha hI

/-- The named answer assumption for destroyBlackFunds: whenever the runner ends the forwarded
`balanceOf(a)` with no error, the word that the CALL writes at 0x60 is the local `balances[a]`
in the child's end state. -/
def HonestBalance (runChild : MessageRunner fork Nat bound) (message : Message fork)
    (state : State.TransactionState) : Prop :=
  ∀ caller msg lt child, runChild caller msg lt = .ok child →
    msg.caller = message.currentTarget → msg.currentTarget = upAddr state message →
    msg.data = dataB message → child.1.error = none →
      resWord (outMemOf (memD message) child.1.output) =
        storageAt child.1.state message.currentTarget (balSlot message)

/-- Round 29 (docs/AUDIT.md, finding 2): `KeepsInv` restricted to the calls the code of `C`
actually makes from `state` (`SentVia`: the caller state reads as `state` since round 49, the
message runs the code that the upgraded address holds in `state`, no value). `KeepsInv` implies it
(`keepsInv_at`); unlike `KeepsInv`, EthLib's `processRunner` can meet it (Sanity/Process.lean). -/
def KeepsInvAt (runChild : MessageRunner fork Nat bound) (message : Message fork)
    (state : State.TransactionState) : Prop :=
  KeepsOn runChild (SentVia message state (upAddr state message))
    (fun X Y => Inv message.currentTarget X → Inv message.currentTarget Y)

/-- Round 29: `HonestBalance` restricted in the same way (`SentVia`). -/
def HonestBalanceAt (runChild : MessageRunner fork Nat bound) (message : Message fork)
    (state : State.TransactionState) : Prop :=
  ∀ caller msg lt child, SentVia message state (upAddr state message) caller msg →
    runChild caller msg lt = .ok child → msg.data = dataB message → child.1.error = none →
      resWord (outMemOf (memD message) child.1.output) =
        storageAt child.1.state message.currentTarget (balSlot message)

theorem keepsInv_at (h : KeepsInv runChild message.currentTarget (upAddr state message)) :
    KeepsInvAt runChild message state := by
  intro caller msg lt child hch ⟨_, _, _, _, _, hmc, hmt, _⟩ he hI
  exact h caller msg lt child hch hmc hmt he hI

/-- Round 33 (docs/AUDIT.md, third audit, T4): `KeepsInvAcc` gives `KeepsInvAt` together with
`KeepsInvNoAcc`, the case of a caller state where `C` has no account. Through round 48 `SentVia`
fixed only the storage and code of the caller state, so that case was not excluded. Since round 49
(EthLib's `SentVia`) the caller state reads as `state`, with its accounts. -/
theorem keepsInvAt_of_acc
    (hacc : KeepsInvAcc runChild message.currentTarget (upAddr state message))
    (hno : KeepsInvNoAcc runChild message.currentTarget (upAddr state message)) :
    KeepsInvAt runChild message state :=
  keepsInv_at (keepsInv_of_acc hacc hno)

/-- Round 49: when `state` has an account of `C`, `KeepsInvAcc` alone gives `KeepsInvAt`. EthLib's
`SentVia` asks the caller state to read as `state` (`ReadsAs`), so it has the account of `C`
that `state` has, and the case `KeepsInvNoAcc` covers does not arise. -/
theorem keepsInvAt_of_acc_hasAccount
    (hacc : KeepsInvAcc runChild message.currentTarget (upAddr state message))
    (hS : hasAccount state message.currentTarget) :
    KeepsInvAt runChild message state := by
  intro caller msg lt child hch hs he hI
  obtain ⟨-, -, -, -, hv, hmc, hmt, -⟩ := hs
  have hc : hasAccount caller.state message.currentTarget := by
    unfold hasAccount; rw [(hv.1 message.currentTarget List.not_mem_nil).1]; exact hS
  exact (hacc caller msg lt child hch hmc hmt he hc hI).2

theorem honest_at (h : HonestBalance runChild message state) :
    HonestBalanceAt runChild message state := by
  intro caller msg lt child ⟨_, _, _, _, _, hmc, hmt, _⟩ hch hmd he
  exact h caller msg lt child hch hmc hmt hmd he

/-- What a deprecated forwarding function does to the local storage: one call that the code
makes (`SentVia`: from a caller state that reads as the start state, to the upgraded address,
running its code), and the end state is the child's end state. `C` has an account in the caller
state iff it has one in the start state. -/
def LocalForward (runChild : MessageRunner fork Nat bound) (message : Message fork)
    (state : State.TransactionState) (s : Evm fork Nat) : Prop :=
  ∃ caller msg lt child, SentVia message state (upAddr state message) caller msg ∧
    runChild caller msg lt = .ok child ∧ child.1.error = none ∧
    (hasAccount caller.state message.currentTarget ↔ hasAccount state message.currentTarget) ∧
    s.state = child.1.state

theorem storageAt_rec (S : State.TransactionState) (u c : Address) (n : U256) :
    storageAt (S.recordAccountRead u) c n = storageAt S c n := by
  simp only [storageAt, State.TransactionState.getStorage_recordAccountRead]

theorem storageAt_route (S : State.TransactionState) (r : Route) (c : Address) (n : U256) :
    storageAt (routeState S r) c n = storageAt S c n := by
  rcases r with _ | ⟨d, _⟩
  · rfl
  · exact storageAt_rec S d c n

/-- The caller state of a forwarding CALL (records of account reads and the route over `X`) has
an account of `c` iff `S` has one, when `X` has one iff `S` has one. -/
theorem hasAccount_caller_iff {S X : State.TransactionState} {c u v : Address} (r : Route)
    (h : hasAccount X c ↔ hasAccount S c) :
    hasAccount ((routeState (X.recordAccountRead u) r).recordAccountRead v) c ↔
      hasAccount S c := by
  rcases r with _ | ⟨d, _⟩ <;> exact h

/-- `LocalForward` keeps `Inv` under `KeepsInvAt`. -/
theorem inv_of_local (hkeeps : KeepsInvAt runChild message state)
    (hI : Inv message.currentTarget state)
    (h : LocalForward runChild message state s) : Inv message.currentTarget s.state := by
  obtain ⟨caller, msg, lt, child, hsv, hch, he, -, hst⟩ := h
  have hv := hsv.choose_spec.choose_spec.2.2.1
  rw [hst]
  exact hkeeps caller msg lt child hch hsv he
    ((DepInv.inv_congr (fun n => storageAt_of_readsAs hv message.currentTarget n)).2 hI)

/-- With no account of `C` in the start state, a `LocalForward` call is sent from a caller state
with no account of `C` either: that is the case `KeepsInvNoAcc` covers. -/
theorem localForward_noAcc (hno : ¬hasAccount state message.currentTarget)
    (h : LocalForward runChild message state s) :
    ∃ caller msg lt child, runChild caller msg lt = .ok child ∧ child.1.error = none ∧
      msg.caller = message.currentTarget ∧ msg.currentTarget = upAddr state message ∧
      ¬hasAccount caller.state message.currentTarget ∧ s.state = child.1.state := by
  obtain ⟨caller, msg, lt, child, ⟨_, _, _, _, _, hmc, hmt, _⟩, hch, he, hac, hst⟩ := h
  exact ⟨caller, msg, lt, child, hch, he, hmc, hmt, fun h => hno (hac.1 h), hst⟩

/-! ## The six forwarding functions -/

theorem dep_totalSupply_local (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x18160ddd)
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) : LocalForward runChild message state s := by
  obtain ⟨c, r, hcode, hroute, -, -, -, caller, msg, lt, child, hch, he, hfwd, -, hcs, -, -, -, -, -, hst, -⟩ :=
    dep_totalSupply_complete hfork hsize' hsel hdep start within hrun hok
  refine ⟨caller, msg, lt, child, sentVia_of_sendsVia hcode hroute hfwd ?_, hch, he, ?_, ?_⟩
  · rw [hcs]
    reads_as
  · rw [hcs]
    exact hasAccount_caller_iff _ Iff.rfl
  · rw [hst, state_incorporateChild]

theorem dep_balanceOf_local (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x70a08231)
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) : LocalForward runChild message state s := by
  obtain ⟨c, r, hcode, hroute, -, -, -, caller, msg, lt, child, hch, he, hfwd, -, hcs, -, -, -, -, -, hst, -⟩ :=
    dep_balanceOf_complete hfork hsize' hsel hdep start within hrun hok
  refine ⟨caller, msg, lt, child, sentVia_of_sendsVia hcode hroute hfwd ?_, hch, he, ?_, ?_⟩
  · rw [hcs]
    reads_as
  · rw [hcs]
    exact hasAccount_caller_iff _ Iff.rfl
  · rw [hst, state_incorporateChild]

theorem dep_allowance_local (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xdd62ed3e)
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) : LocalForward runChild message state s := by
  obtain ⟨c, r, hcode, hroute, -, -, -, caller, msg, lt, child, hch, he, hfwd, -, hcs, -, -, -, -, -, hst, -⟩ :=
    dep_allowance_complete hfork hsize' hsel hdep rfl rfl start within hrun hok
  refine ⟨caller, msg, lt, child, sentVia_of_sendsVia hcode hroute hfwd ?_, hch, he, ?_, ?_⟩
  · rw [hcs]
    reads_as
  · rw [hcs]
    exact hasAccount_caller_iff _ Iff.rfl
  · rw [hst, state_incorporateChild]

theorem dep_approve_local (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x095ea7b3)
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) : LocalForward runChild message state s := by
  obtain ⟨c, r, hcode, hroute, -, -, -, -, caller, msg, lt, child, hch, he, hfwd, -, hcs, -, -, -, -, -, hst, -⟩ :=
    dep_approve_complete hfork hsize' hsel hdep rfl rfl start within hrun hok
  refine ⟨caller, msg, lt, child, sentVia_of_sendsVia hcode hroute hfwd ?_, hch, he, ?_, ?_⟩
  · rw [hcs]
    reads_as
  · rw [hcs]
    exact hasAccount_caller_iff _ Iff.rfl
  · rw [hst, state_incorporateChild]

theorem dep_transfer_local (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xa9059cbb)
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) : LocalForward runChild message state s := by
  obtain ⟨c, r, hcode, hroute, -, -, -, -, -, caller, msg, lt, child, hch, he, hfwd, -, hcs, -, -, -, -, -, hst, -⟩ :=
    dep_transfer_complete hfork hsize' hsel hdep rfl rfl rfl rfl start within
      hrun hok
  refine ⟨caller, msg, lt, child, sentVia_of_sendsVia hcode hroute hfwd ?_, hch, he, ?_, ?_⟩
  · rw [hcs]
    reads_as
  · rw [hcs]
    exact hasAccount_caller_iff _ Iff.rfl
  · rw [hst, state_incorporateChild]

theorem dep_transferFrom_local (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x23b872dd)
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) : LocalForward runChild message state s := by
  obtain ⟨c, r, hcode, hroute, -, -, -, -, -, caller, msg, lt, child, hch, he, hfwd, -, hcs, -, -, -, -, -, hst, -⟩ :=
    dep_transferFrom_complete hfork hsize' hsel hdep rfl rfl rfl rfl start within
      hrun hok
  refine ⟨caller, msg, lt, child, sentVia_of_sendsVia hcode hroute hfwd ?_, hch, he, ?_, ?_⟩
  · rw [hcs]
    reads_as
  · rw [hcs]
    exact hasAccount_caller_iff _ Iff.rfl
  · rw [hst, state_incorporateChild]

/-! ## destroyBlackFunds -/

/-- Deprecated destroyBlackFunds under `KeepsInv`: one call from `C` to `ua` with data `dataB`
that ends with no error, whose end state `S` has an account of `C` (from `dep_destroy_complete`)
and `Inv C` (from `KeepsInv`); the end state is `tailState S C a d`, with `d` the word at 0x60. -/
theorem dep_destroy_local (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xf3bdc228)
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0)
    (hkeeps : KeepsInvAt runChild message state)
    (hI : Inv message.currentTarget state)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) :
    ∃ caller msg lt child, runChild caller msg lt = .ok child ∧ child.1.error = none ∧
      SentVia message state (upAddr state message) caller msg ∧
      msg.data = dataB message ∧
      hasAccount child.1.state message.currentTarget ∧ Inv message.currentTarget child.1.state ∧
      s.state = tailState child.1.state message.currentTarget (addrArg message.data 0)
        (resWord (outMemOf (memD message) child.1.output)) := by
  obtain ⟨c, r, hcode, hroute, -, -, -, -, -, caller, msg, lt, child, hch, he, -, hacc', hfwd, -,
      hcs, -, -, -, -, -, hst, -⟩ :=
    dep_destroy_complete hfork hsize' hsel hdep rfl rfl rfl rfl start within hrun hok
  have hv : ReadsAs caller.state state := by
    rw [hcs]
    reads_as
  have hsv : SentVia message state (upAddr state message) caller msg :=
    sentVia_of_sendsVia hcode hroute hfwd hv
  have hIc : Inv message.currentTarget caller.state :=
    (DepInv.inv_congr (fun n => storageAt_of_readsAs hv message.currentTarget n)).2 hI
  refine ⟨caller, msg, lt, child, hch, he, hsv, hfwd.2.2.2.2.2.2.1, hacc',
    hkeeps caller msg lt child hch hsv he hIc, ?_⟩
  rw [hst, state_incorporateChild]

/-- Deprecated destroyBlackFunds under `KeepsInv`: `Inv` holds at the end iff the answer `d` is
the local `balances[a]` in the state the call left. -/
theorem inv_dep_destroy_iff (K : SepOn (callKeys message state)) (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xf3bdc228)
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0)
    (hkeeps : KeepsInvAt runChild message state)
    (hI : Inv message.currentTarget state)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) :
    ∃ caller msg lt child, runChild caller msg lt = .ok child ∧ child.1.error = none ∧
      SentVia message state (upAddr state message) caller msg ∧
      msg.data = dataB message ∧
      (Inv message.currentTarget s.state ↔ resWord (outMemOf (memD message) child.1.output) =
        storageAt child.1.state message.currentTarget (balSlot message)) := by
  obtain ⟨caller, msg, lt, child, hch, he, hsv, hmd, hacc', hI', hst⟩ :=
    dep_destroy_local hfork hsize' hsel hdep hkeeps hI start within
      hrun hok
  refine ⟨caller, msg, lt, child, hch, he, hsv, hmd, ?_⟩
  rw [hst]
  exact DepInv.inv_tail_iff K.fixed hacc' (addrArg_lt _ _) K.uniqArg0 hI' _

/-- Deprecated destroyBlackFunds under `KeepsInv` and `HonestBalance` keeps `Inv`. -/
theorem inv_dep_destroy (K : SepOn (callKeys message state)) (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xf3bdc228)
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0)
    (hkeeps : KeepsInvAt runChild message state)
    (hhonest : HonestBalanceAt runChild message state)
    (hI : Inv message.currentTarget state)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) : Inv message.currentTarget s.state := by
  obtain ⟨caller, msg, lt, child, hch, he, hsv, hmd, hiff⟩ :=
    inv_dep_destroy_iff K hfork hsize' hsel hdep hkeeps hI start
      within hrun hok
  exact hiff.2 (hhonest caller msg lt child hsv hch hmd he)

/-! ## Every call -/

/-- **Every successful call keeps the invariant, deprecated or not.**

`inv_call` with `hdep` replaced by what the deprecated paths need. From Berlin (Glamsterdam
included), a fresh frame of `CODE` at pc 0, static or not (since round 19), with any call data
below 2^256 bytes, any value, any gas, any gas bound and any message runner. Under `SepOn` of the
call's keys, with
string slots 7 and 8 of `StrForm`, and, when deprecated (byte 20 of slot 10 not 0): the runner
meets `KeepsInv` (`hkeeps`), and for destroyBlackFunds it meets `HonestBalance` (`hhonest`).
No account of the contract is assumed (since round 20).
If `Inv C state` holds and the interpreter loop ends with no error, then `Inv C s.state` holds. -/
theorem inv_call_ns (K : SepOn (callKeys message state)) (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (h7 : StrForm (storageAt state message.currentTarget 7))
    (h8 : StrForm (storageAt state message.currentTarget 8))
    (hkeeps : byte20 (storageAt state message.currentTarget 10) ≠ 0 →
      KeepsInvAt runChild message state)
    (hhonest : byte20 (storageAt state message.currentTarget 10) ≠ 0 →
      selector message.data = 0xf3bdc228 → HonestBalanceAt runChild message state)
    (hI : Inv message.currentTarget state)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) : Inv message.currentTarget s.state := by
  by_cases hdep : byte20 (storageAt state message.currentTarget 10) = 0
  · exact inv_call K hfork hsize' hdep h7 h8 hI start (Ends.run hrun) hok
  have hk := hkeeps hdep
  obtain ⟨_, -, i, hi⟩ := runFrame_ok_dispatch hfork hsize' start within hrun hok
  match i, hi with
  | ⟨0, _⟩, hi => exact inv_name hfork hsize' (hi.trans rfl) h7 hI start (Ends.run hrun) hok
  | ⟨1, _⟩, hi => exact inv_deprecate K hfork hsize' (hi.trans rfl) hI start (Ends.run hrun) hok
  | ⟨2, _⟩, hi => exact inv_of_local hk hI (dep_approve_local hfork hsize' (hi.trans rfl) hdep start within hrun hok)
  | ⟨3, _⟩, hi => exact inv_deprecated hfork hsize' (hi.trans rfl) hI start (Ends.run hrun) hok
  | ⟨4, _⟩, hi => exact inv_addBlackList K hfork hsize' (hi.trans rfl) hI start (Ends.run hrun) hok
  | ⟨5, _⟩, hi => exact inv_of_local hk hI (dep_totalSupply_local hfork hsize' (hi.trans rfl) hdep start within hrun hok)
  | ⟨6, _⟩, hi => exact inv_of_local hk hI (dep_transferFrom_local hfork hsize' (hi.trans rfl) hdep start within hrun hok)
  | ⟨7, _⟩, hi => exact inv_upgradedAddress hfork hsize' (hi.trans rfl) hI start (Ends.run hrun) hok
  | ⟨8, _⟩, hi => exact inv_balances hfork hsize' (hi.trans rfl) hI start (Ends.run hrun) hok
  | ⟨9, _⟩, hi => exact inv_decimals hfork hsize' (hi.trans rfl) hI start (Ends.run hrun) hok
  | ⟨10, _⟩, hi => exact inv_maximumFee hfork hsize' (hi.trans rfl) hI start (Ends.run hrun) hok
  | ⟨11, _⟩, hi => exact inv_totalSupplyVar hfork hsize' (hi.trans rfl) hI start (Ends.run hrun) hok
  | ⟨12, _⟩, hi => exact inv_unpause K hfork hsize' (hi.trans rfl) hI start (Ends.run hrun) hok
  | ⟨13, _⟩, hi => exact inv_getBlackListStatus hfork hsize' (hi.trans rfl) hI start (Ends.run hrun) hok
  | ⟨14, _⟩, hi => exact inv_allowed hfork hsize' (hi.trans rfl) hI start (Ends.run hrun) hok
  | ⟨15, _⟩, hi => exact inv_paused hfork hsize' (hi.trans rfl) hI start (Ends.run hrun) hok
  | ⟨16, _⟩, hi => exact inv_of_local hk hI (dep_balanceOf_local hfork hsize' (hi.trans rfl) hdep start within hrun hok)
  | ⟨17, _⟩, hi => exact inv_pause K hfork hsize' (hi.trans rfl) hI start (Ends.run hrun) hok
  | ⟨18, _⟩, hi => exact inv_getOwner hfork hsize' (hi.trans rfl) hI start (Ends.run hrun) hok
  | ⟨19, _⟩, hi => exact inv_owner hfork hsize' (hi.trans rfl) hI start (Ends.run hrun) hok
  | ⟨20, _⟩, hi => exact inv_symbol hfork hsize' (hi.trans rfl) h8 hI start (Ends.run hrun) hok
  | ⟨21, _⟩, hi => exact inv_of_local hk hI (dep_transfer_local hfork hsize' (hi.trans rfl) hdep start within hrun hok)
  | ⟨22, _⟩, hi => exact inv_setParams K hfork hsize' (hi.trans rfl) hI start (Ends.run hrun) hok
  | ⟨23, _⟩, hi => exact inv_issue K hfork hsize' (hi.trans rfl) hI start (Ends.run hrun) hok
  | ⟨24, _⟩, hi => exact inv_redeem K hfork hsize' (hi.trans rfl) hI start (Ends.run hrun) hok
  | ⟨25, _⟩, hi => exact inv_of_local hk hI (dep_allowance_local hfork hsize' (hi.trans rfl) hdep start within hrun hok)
  | ⟨26, _⟩, hi => exact inv_basisPointsRate hfork hsize' (hi.trans rfl) hI start (Ends.run hrun) hok
  | ⟨27, _⟩, hi => exact inv_isBlackListed hfork hsize' (hi.trans rfl) hI start (Ends.run hrun) hok
  | ⟨28, _⟩, hi => exact inv_removeBlackList K hfork hsize' (hi.trans rfl) hI start (Ends.run hrun) hok
  | ⟨29, _⟩, hi => exact inv_maxUint hfork hsize' (hi.trans rfl) hI start (Ends.run hrun) hok
  | ⟨30, _⟩, hi => exact inv_transferOwnership K hfork hsize' (hi.trans rfl) hI start (Ends.run hrun) hok
  | ⟨31, _⟩, hi => exact inv_dep_destroy K hfork hsize' (hi.trans rfl) hdep hk (hhonest hdep (hi.trans rfl)) hI start within hrun hok
  | ⟨n + 32, h⟩, _ => exact absurd h (by omega)

end UsdtVerify.Complete
