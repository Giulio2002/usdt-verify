import UsdtVerify.Complete.Inv
import UsdtVerify.Complete.DepInv
import UsdtVerify.Complete.DepDestroy

/-!
# The invariant over every successful call, deprecated or not

When deprecated, seven functions call the upgraded contract `ua` (the low 160 bits of slot 10).
What they do to the local storage (the storage of the contract `C`), from the completeness
theorems `dep_*_complete`:

- totalSupply, balanceOf, allowance, transfer, approve, transferFrom (`dep_*_local`, stated with
  `LocalForward`): up to the CALL the code only reads; at the CALL the storage of `C` is the start
  storage (`storageAt` agrees at every slot) and `C` keeps its account; after the CALL the code
  writes nothing: the end state is the state the runner's child frame ended in (`child.state`).
  So `Inv C` at the end is `Inv C` of the child's state.
- destroyBlackFunds (`dep_destroy_local`): the same up to and through the CALL, then the two
  writes over the child's state `S`: the end state is `tailState S C a d`, `d` the word that the
  call wrote at 0x60. By `DepInv.inv_tail_iff` (under `KeccakSep`, `Inv C S`, an account of `C`
  in `S`), `Inv` holds at the end iff `d = balances[a]` in `S` (`inv_dep_destroy_iff`).

The callee may call back into `C` (reentrancy), so what the child's state holds is an assumption
on the runner. Named assumptions:

- `KeepsInv runChild C ua`: whenever the runner ends a message from `C` to `ua` with no error,
  from a caller state where `C` has an account and `Inv C` holds, then in the child's end state
  `C` still has an account and `Inv C` holds. It says nothing about what the callee does in
  between (it covers any reentrant calls into `C`).
- `HonestBalance runChild message state`: whenever the runner ends a message from `C` to `ua` with
  the data `balanceOf(a)` (`dataB message`) with no error, the word the call writes at 0x60 is
  `balances[a]` in the child's end state.

`inv_call_ns`: `Complete.inv_call` without `hdep`: under `KeccakSep`, `StrForm` of
slots 7 and 8, `Inv` at the start, and, when deprecated, an account of the contract (`hacc`),
`KeepsInv` and (for destroyBlackFunds) `HonestBalance`, every successful call ends with `Inv`.
When not deprecated no account is assumed (`inv_call`: each writing path that succeeds had one).
When deprecated the account is used only by the forwarding functions and destroyBlackFunds: the
premise of `KeepsInv` asks for an account of `C` in the caller state of the CALL (`LocalForward`
carries it there from the start state), and destroyBlackFunds needs the account in the child's
end state for `DepInv.inv_tail_iff` (round 19: `dep_destroy_complete` proves it for a successful run; `KeepsInv` gives `Inv` there). Nothing here shows that a successful
deprecated forward implies an account (the code writes nothing locally before or after the CALL),
so it stays a hypothesis, only when deprecated.
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
error, from a caller state where `C` has an account and `Inv C` holds, the child's end state keeps
both. Any reentrant call into `C` is inside the child's run, so this covers it. -/
def KeepsInv (runChild : MessageRunner fork Nat bound) (C ua : Address) : Prop :=
  ∀ caller msg lt child, runChild caller msg lt = .ok child → msg.caller = C →
    msg.currentTarget = ua → child.1.error = none → hasAccount caller.state C →
      Inv C caller.state → hasAccount child.1.state C ∧ Inv C child.1.state

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

/-- What a deprecated forwarding function does to the local storage: one call, from a caller
state whose storage at `C` is the start storage (and `C` keeps its account), and the end state is
the child's end state. -/
def LocalForward (runChild : MessageRunner fork Nat bound) (message : Message fork)
    (state : State.TransactionState) (s : Evm fork Nat) : Prop :=
  ∃ caller msg lt child, runChild caller msg lt = .ok child ∧ child.1.error = none ∧
    msg.caller = message.currentTarget ∧ msg.currentTarget = upAddr state message ∧
    (∀ n, storageAt caller.state message.currentTarget n =
      storageAt state message.currentTarget n) ∧
    (hasAccount state message.currentTarget → hasAccount caller.state message.currentTarget) ∧
    s.state = child.1.state

theorem storageAt_rec (S : State.TransactionState) (u c : Address) (n : U256) :
    storageAt (S.recordAccountRead u) c n = storageAt S c n := by
  simp only [storageAt, State.TransactionState.getStorage_recordAccountRead]

theorem hasAccount_rec {S : State.TransactionState} {c : Address} (u : Address)
    (h : hasAccount S c) : hasAccount (S.recordAccountRead u) c := h

theorem storageAt_route (S : State.TransactionState) (r : Route) (c : Address) (n : U256) :
    storageAt (routeState S r) c n = storageAt S c n := by
  rcases r with _ | ⟨d, _⟩
  · rfl
  · exact storageAt_rec S d c n

theorem hasAccount_route {S : State.TransactionState} {c : Address} (r : Route)
    (h : hasAccount S c) : hasAccount (routeState S r) c := by
  rcases r with _ | ⟨d, _⟩
  · exact h
  · exact hasAccount_rec d h

/-- `LocalForward` keeps `Inv` under `KeepsInv`. -/
theorem inv_of_local (hkeeps : KeepsInv runChild message.currentTarget (upAddr state message))
    (hacc : hasAccount state message.currentTarget) (hI : Inv message.currentTarget state)
    (h : LocalForward runChild message state s) : Inv message.currentTarget s.state := by
  obtain ⟨caller, msg, lt, child, hch, he, hmc, hmt, hsto, hac, hst⟩ := h
  rw [hst]
  exact (hkeeps caller msg lt child hch hmc hmt he (hac hacc)
    ((DepInv.inv_congr hsto).2 hI)).2

/-! ## The six forwarding functions -/

theorem dep_totalSupply_local (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x18160ddd)
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) : LocalForward runChild message state s := by
  obtain ⟨_, _, -, -, -, -, -, caller, msg, lt, child, hch, he, hfwd, -, hcs, -, -, -, -, -, hst, -⟩ :=
    dep_totalSupply_complete hfork hsize' hsel hdep start within hrun hok
  refine ⟨caller, msg, lt, child, hch, he, hfwd.1, hfwd.2.1, fun n => ?_, fun h => ?_, ?_⟩
  · rw [hcs]; simp only [callState, storageAt_rec, storageAt_route, storageAt_readSlot]
  · rw [hcs]
    exact hasAccount_rec _ (hasAccount_route _ (hasAccount_rec _ (hasAccount_rec _
      (hasAccount_readSlot h))))
  · rw [hst, state_incorporateChild]

theorem dep_balanceOf_local (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x70a08231)
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) : LocalForward runChild message state s := by
  obtain ⟨_, _, -, -, -, -, -, caller, msg, lt, child, hch, he, hfwd, -, hcs, -, -, -, -, -, hst, -⟩ :=
    dep_balanceOf_complete hfork hsize' hsel hdep start within hrun hok
  refine ⟨caller, msg, lt, child, hch, he, hfwd.1, hfwd.2.1, fun n => ?_, fun h => ?_, ?_⟩
  · rw [hcs]; simp only [callState, storageAt_rec, storageAt_route, storageAt_readSlot]
  · rw [hcs]
    exact hasAccount_rec _ (hasAccount_route _ (hasAccount_rec _ (hasAccount_rec _
      (hasAccount_readSlot h))))
  · rw [hst, state_incorporateChild]

theorem dep_allowance_local (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xdd62ed3e)
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) : LocalForward runChild message state s := by
  obtain ⟨_, _, -, -, -, -, -, caller, msg, lt, child, hch, he, hfwd, -, hcs, -, -, -, -, -, hst, -⟩ :=
    dep_allowance_complete hfork hsize' hsel hdep rfl rfl start within hrun hok
  refine ⟨caller, msg, lt, child, hch, he, hfwd.1, hfwd.2.1, fun n => ?_, fun h => ?_, ?_⟩
  · rw [hcs]; simp only [callState, storageAt_rec, storageAt_route, storageAt_readSlot]
  · rw [hcs]
    exact hasAccount_rec _ (hasAccount_route _ (hasAccount_rec _ (hasAccount_rec _
      (hasAccount_readSlot h))))
  · rw [hst, state_incorporateChild]

theorem dep_approve_local (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x095ea7b3)
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) : LocalForward runChild message state s := by
  obtain ⟨_, _, -, -, -, -, -, -, caller, msg, lt, child, hch, he, hfwd, -, hcs, -, -, -, -, -, hst, -⟩ :=
    dep_approve_complete hfork hsize' hsel hdep rfl rfl start within hrun hok
  refine ⟨caller, msg, lt, child, hch, he, hfwd.1, hfwd.2.1, fun n => ?_, fun h => ?_, ?_⟩
  · rw [hcs]; simp only [callState, storageAt_rec, storageAt_route, storageAt_readSlot]
  · rw [hcs]
    exact hasAccount_rec _ (hasAccount_route _ (hasAccount_rec _ (hasAccount_rec _
      (hasAccount_readSlot h))))
  · rw [hst, state_incorporateChild]

theorem dep_transfer_local (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xa9059cbb)
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) : LocalForward runChild message state s := by
  obtain ⟨_, _, -, -, -, -, -, -, -, caller, msg, lt, child, hch, he, hfwd, -, hcs, -, -, -, -, -, hst, -⟩ :=
    dep_transfer_complete hfork hsize' hsel hdep rfl rfl rfl rfl start within
      hrun hok
  refine ⟨caller, msg, lt, child, hch, he, hfwd.1, hfwd.2.1, fun n => ?_, fun h => ?_, ?_⟩
  · rw [hcs]
    simp only [DeprecatedTransfer.callStateT, Transfer.shortState, storageAt_rec,
      storageAt_route, storageAt_readSlot]
  · rw [hcs]
    exact hasAccount_rec _ (hasAccount_route _ (hasAccount_rec _ (hasAccount_rec _
      (hasAccount_readSlot (hasAccount_readSlot (hasAccount_readSlot h))))))
  · rw [hst, state_incorporateChild]

theorem dep_transferFrom_local (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x23b872dd)
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) : LocalForward runChild message state s := by
  obtain ⟨_, _, -, -, -, -, -, -, -, caller, msg, lt, child, hch, he, hfwd, -, hcs, -, -, -, -, -, hst, -⟩ :=
    dep_transferFrom_complete hfork hsize' hsel hdep rfl rfl rfl rfl start within
      hrun hok
  refine ⟨caller, msg, lt, child, hch, he, hfwd.1, hfwd.2.1, fun n => ?_, fun h => ?_, ?_⟩
  · rw [hcs]
    simp only [DeprecatedTransferFrom.callStateF, TransferFrom.checkState, storageAt_rec,
      storageAt_route, storageAt_readSlot]
  · rw [hcs]
    exact hasAccount_rec _ (hasAccount_route _ (hasAccount_rec _ (hasAccount_rec _
      (hasAccount_readSlot (hasAccount_readSlot (hasAccount_readSlot h))))))
  · rw [hst, state_incorporateChild]

/-! ## destroyBlackFunds -/

/-- Deprecated destroyBlackFunds: one call as in `LocalForward`, then the end state is
`tailState S C a d` over the child's end state `S`, with `d` the word at 0x60. -/
theorem dep_destroy_local (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xf3bdc228)
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0)
    (hkeeps : KeepsInv runChild message.currentTarget (upAddr state message))
    (hacc : hasAccount state message.currentTarget) (hI : Inv message.currentTarget state)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) :
    ∃ caller msg lt child, runChild caller msg lt = .ok child ∧ child.1.error = none ∧
      msg.caller = message.currentTarget ∧ msg.currentTarget = upAddr state message ∧
      msg.data = dataB message ∧
      hasAccount child.1.state message.currentTarget ∧ Inv message.currentTarget child.1.state ∧
      s.state = tailState child.1.state message.currentTarget (addrArg message.data 0)
        (resWord (outMemOf (memD message) child.1.output)) := by
  have hpre : ∀ (caller : Evm fork Nat) (r : Route), caller.state = (routeState
      ((callStateD state message).recordAccountRead (upAddr state message)) r).recordAccountRead
      message.currentTarget →
      hasAccount caller.state message.currentTarget ∧ Inv message.currentTarget caller.state := by
    intro caller r hcs
    refine ⟨?_, (DepInv.inv_congr (fun n => ?_)).2 hI⟩
    · rw [hcs]
      exact hasAccount_rec _ (hasAccount_route _ (hasAccount_rec _ (hasAccount_rec _
        (hasAccount_readSlot (hasAccount_readSlot (hasAccount_readSlot hacc))))))
    · rw [hcs]
      simp only [callStateD, preState, storageAt_rec, storageAt_route, storageAt_readSlot]
  obtain ⟨_, _, -, -, -, -, -, -, -, caller, msg, lt, child, hch, he, -, -, hfwd, -, hcs, -, -, -,
      -, -, hst, -⟩ :=
    dep_destroy_complete hfork hsize' hsel hdep rfl rfl rfl rfl start within hrun hok
  obtain ⟨hacc', hI'⟩ := hkeeps caller msg lt child hch hfwd.1 hfwd.2.1 he (hpre caller _ hcs).1
    (hpre caller _ hcs).2
  refine ⟨caller, msg, lt, child, hch, he, hfwd.1, hfwd.2.1, hfwd.2.2.2.2.2.2.1, hacc', hI', ?_⟩
  rw [hst, state_incorporateChild]

/-- Deprecated destroyBlackFunds under `KeepsInv`: `Inv` holds at the end iff the answer `d` is
the local `balances[a]` in the state the call left. -/
theorem inv_dep_destroy_iff (K : KeccakSep) (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xf3bdc228)
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0)
    (hkeeps : KeepsInv runChild message.currentTarget (upAddr state message))
    (hacc : hasAccount state message.currentTarget) (hI : Inv message.currentTarget state)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) :
    ∃ caller msg lt child, runChild caller msg lt = .ok child ∧ child.1.error = none ∧
      msg.caller = message.currentTarget ∧ msg.currentTarget = upAddr state message ∧
      msg.data = dataB message ∧
      (Inv message.currentTarget s.state ↔ resWord (outMemOf (memD message) child.1.output) =
        storageAt child.1.state message.currentTarget (balSlot message)) := by
  obtain ⟨caller, msg, lt, child, hch, he, hmc, hmt, hmd, hacc', hI', hst⟩ :=
    dep_destroy_local hfork hsize' hsel hdep hkeeps hacc hI start within
      hrun hok
  refine ⟨caller, msg, lt, child, hch, he, hmc, hmt, hmd, ?_⟩
  rw [hst]
  exact DepInv.inv_tail_iff K hacc' (addrArg_lt _ _) hI' _

/-- Deprecated destroyBlackFunds under `KeepsInv` and `HonestBalance` keeps `Inv`. -/
theorem inv_dep_destroy (K : KeccakSep) (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xf3bdc228)
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0)
    (hkeeps : KeepsInv runChild message.currentTarget (upAddr state message))
    (hhonest : HonestBalance runChild message state)
    (hacc : hasAccount state message.currentTarget) (hI : Inv message.currentTarget state)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) : Inv message.currentTarget s.state := by
  obtain ⟨caller, msg, lt, child, hch, he, hmc, hmt, hmd, hiff⟩ :=
    inv_dep_destroy_iff K hfork hsize' hsel hdep hkeeps hacc hI start
      within hrun hok
  exact hiff.2 (hhonest caller msg lt child hch hmc hmt hmd he)

/-! ## Every call -/

/-- **Every successful call keeps the invariant, deprecated or not.**

`inv_call` with `hdep` replaced by what the deprecated paths need. From Berlin (Glamsterdam
included), a fresh frame of `CODE` at pc 0 with any call data below 2^256 bytes, any value, any
gas, any gas bound and any message runner (static or not since round 19). Under `KeccakSep`, with
string slots 7 and 8 of `StrForm`, and, when deprecated (byte 20 of slot 10 not 0): the contract
has an account (`hacc`), the runner meets `KeepsInv` (`hkeeps`), and for destroyBlackFunds it
meets `HonestBalance` (`hhonest`). If `Inv C state` holds and the interpreter loop ends with no error,
then `Inv C s.state` holds. -/
theorem inv_call_ns (K : KeccakSep) (hfork : .berlin ≤ fork)
    (hacc : byte20 (storageAt state message.currentTarget 10) ≠ 0 →
      hasAccount state message.currentTarget)
    (hsize' : message.data.size < 2 ^ 256)
    (h7 : StrForm (storageAt state message.currentTarget 7))
    (h8 : StrForm (storageAt state message.currentTarget 8))
    (hkeeps : byte20 (storageAt state message.currentTarget 10) ≠ 0 →
      KeepsInv runChild message.currentTarget (upAddr state message))
    (hhonest : byte20 (storageAt state message.currentTarget 10) ≠ 0 →
      selector message.data = 0xf3bdc228 → HonestBalance runChild message state)
    (hI : Inv message.currentTarget state)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) : Inv message.currentTarget s.state := by
  by_cases hdep : byte20 (storageAt state message.currentTarget 10) = 0
  · exact inv_call K hfork hsize' hdep h7 h8 hI start within hrun hok
  have hk := hkeeps hdep
  have hacc := hacc hdep
  obtain ⟨_, -, i, hi⟩ := runFrame_ok_dispatch hfork hsize' start within hrun hok
  match i, hi with
  | ⟨0, _⟩, hi => exact inv_name hfork hsize' (hi.trans rfl) h7 hI start within hrun hok
  | ⟨1, _⟩, hi => exact inv_deprecate K hfork hsize' (hi.trans rfl) hI start within hrun hok
  | ⟨2, _⟩, hi => exact inv_of_local hk hacc hI (dep_approve_local hfork hsize' (hi.trans rfl) hdep start within hrun hok)
  | ⟨3, _⟩, hi => exact inv_deprecated hfork hsize' (hi.trans rfl) hI start within hrun hok
  | ⟨4, _⟩, hi => exact inv_addBlackList K hfork hsize' (hi.trans rfl) hI start within hrun hok
  | ⟨5, _⟩, hi => exact inv_of_local hk hacc hI (dep_totalSupply_local hfork hsize' (hi.trans rfl) hdep start within hrun hok)
  | ⟨6, _⟩, hi => exact inv_of_local hk hacc hI (dep_transferFrom_local hfork hsize' (hi.trans rfl) hdep start within hrun hok)
  | ⟨7, _⟩, hi => exact inv_upgradedAddress hfork hsize' (hi.trans rfl) hI start within hrun hok
  | ⟨8, _⟩, hi => exact inv_balances hfork hsize' (hi.trans rfl) hI start within hrun hok
  | ⟨9, _⟩, hi => exact inv_decimals hfork hsize' (hi.trans rfl) hI start within hrun hok
  | ⟨10, _⟩, hi => exact inv_maximumFee hfork hsize' (hi.trans rfl) hI start within hrun hok
  | ⟨11, _⟩, hi => exact inv_totalSupplyVar hfork hsize' (hi.trans rfl) hI start within hrun hok
  | ⟨12, _⟩, hi => exact inv_unpause K hfork hsize' (hi.trans rfl) hI start within hrun hok
  | ⟨13, _⟩, hi => exact inv_getBlackListStatus hfork hsize' (hi.trans rfl) hI start within hrun hok
  | ⟨14, _⟩, hi => exact inv_allowed hfork hsize' (hi.trans rfl) hI start within hrun hok
  | ⟨15, _⟩, hi => exact inv_paused hfork hsize' (hi.trans rfl) hI start within hrun hok
  | ⟨16, _⟩, hi => exact inv_of_local hk hacc hI (dep_balanceOf_local hfork hsize' (hi.trans rfl) hdep start within hrun hok)
  | ⟨17, _⟩, hi => exact inv_pause K hfork hsize' (hi.trans rfl) hI start within hrun hok
  | ⟨18, _⟩, hi => exact inv_getOwner hfork hsize' (hi.trans rfl) hI start within hrun hok
  | ⟨19, _⟩, hi => exact inv_owner hfork hsize' (hi.trans rfl) hI start within hrun hok
  | ⟨20, _⟩, hi => exact inv_symbol hfork hsize' (hi.trans rfl) h8 hI start within hrun hok
  | ⟨21, _⟩, hi => exact inv_of_local hk hacc hI (dep_transfer_local hfork hsize' (hi.trans rfl) hdep start within hrun hok)
  | ⟨22, _⟩, hi => exact inv_setParams K hfork hsize' (hi.trans rfl) hI start within hrun hok
  | ⟨23, _⟩, hi => exact inv_issue K hfork hsize' (hi.trans rfl) hI start within hrun hok
  | ⟨24, _⟩, hi => exact inv_redeem K hfork hsize' (hi.trans rfl) hI start within hrun hok
  | ⟨25, _⟩, hi => exact inv_of_local hk hacc hI (dep_allowance_local hfork hsize' (hi.trans rfl) hdep start within hrun hok)
  | ⟨26, _⟩, hi => exact inv_basisPointsRate hfork hsize' (hi.trans rfl) hI start within hrun hok
  | ⟨27, _⟩, hi => exact inv_isBlackListed hfork hsize' (hi.trans rfl) hI start within hrun hok
  | ⟨28, _⟩, hi => exact inv_removeBlackList K hfork hsize' (hi.trans rfl) hI start within hrun hok
  | ⟨29, _⟩, hi => exact inv_maxUint hfork hsize' (hi.trans rfl) hI start within hrun hok
  | ⟨30, _⟩, hi => exact inv_transferOwnership K hfork hsize' (hi.trans rfl) hI start within hrun hok
  | ⟨31, _⟩, hi => exact inv_dep_destroy K hfork hsize' (hi.trans rfl) hdep hk (hhonest hdep (hi.trans rfl)) hacc hI start within hrun hok
  | ⟨n + 32, h⟩, _ => exact absurd h (by omega)

end UsdtVerify.Complete
