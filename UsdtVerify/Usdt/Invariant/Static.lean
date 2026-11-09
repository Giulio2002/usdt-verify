import UsdtVerify.Usdt.Invariant.All
import EthLib.Execution.Proofs.Evm.Call.StaticMessage

/-!
# A static frame keeps the state, and the invariant over every successful call

EthLib proves that a step of a static frame keeps the state up to the records of its reads
(`staticTouchResult_step`; SSTORE, TSTORE, LOG and SELFDESTRUCT do not continue in such a frame).
`static_runFrame` (round 52, the induction of EthLib's `staticTouchStep_runFrame` with no touch)
shows that a whole run of a static frame does too, when the runner ends every static child message
with a state that differs from its caller's only by reads.

- `StaticKeeps runChild`: that runner assumption, named (it was the premise of EthLib's
  `staticStep_runFrame`, which EthLib #1619 removed).
- `staticKeeps_process`: from Paris, the interpreter's own runner (`processRunner`) meets it
  (EthLib's `processMessage_static`).
- `static_run`: a run of a fresh static frame of `CODE` (for a message whose code is `CODE`, at an
  account that holds code: EthLib's `StaticCode`) under a runner that meets `StaticKeeps` ends,
  when it ends with `.ok`, in a state that reads as the start state at every address
  (`SameOutside []`: account, storage, transient storage). Any fork, any gas, any call data, any
  error at the end.
- `inv_static`: so `Inv C` holds at the end of such a run when it holds at the start.
- `inv_call_all`: the invariant over every successful call, static or not. In a static frame it
  is `inv_static`, with the hypotheses `message.code = CODE`, `StaticCode` and `StaticKeeps`; in
  a frame that is not static it is `inv_call_ns` (Usdt/Invariant/All.lean), with the
  deprecated-path assumptions `KeepsInvAt` and `HonestBalanceAt` (round 29), and (since round 20) no account of
  the contract. The hypothesis "not static" of `inv_call_all` is gone; since round 19
  `inv_call_ns` takes it neither.
-/

namespace UsdtVerify.Complete

open EthLib.Base (Fork U256 Address)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open Invariant Deprecated

variable {fork : Fork} {bound : Nat} {runChild : MessageRunner fork Nat bound}
  {message : Message fork} {state : State.TransactionState} {substate : Substate}
  {gas : Nat} {evm s : Evm fork Nat}

/-- The named runner assumption for static frames: whenever the runner ends a static message
(EthLib's `StaticMessage`) sent from a static frame, the child's end state differs from the
caller's only by the records of reads, and keeps its block. This was the premise `runs` of EthLib's
`staticStep_runFrame` (removed from EthLib by #1619; `static_runFrame` below takes its place). -/
def StaticKeeps (runChild : MessageRunner fork Nat bound) : Prop :=
  ∀ {caller : Evm fork Nat} {msg : Message fork} {lt : msg.gas < bound} {c : Evm fork Nat}
    {used : GasMeter.gasHeld c.gas ≤ msg.gas},
    StaticFrame caller → StaticMessage caller.state msg → runChild caller msg lt = .ok ⟨c, used⟩ →
      StateKept caller c ∧ c.state.parent = caller.state.parent

/-- From Paris, the interpreter's own runner meets `StaticKeeps` (EthLib's
`processMessage_static`). -/
theorem staticKeeps_process (hfork : .paris ≤ fork) :
    StaticKeeps (processRunner fork bound) := by
  intro caller msg lt c used _ hm hrun
  simp only [processRunner] at hrun
  split at hrun
  · exact processMessage_static hfork msg.gas msg caller.state _ _ _ rfl hm ⟨c, used⟩ hrun
  · have := hm.2.1
    simp_all

/-- A whole run of a static frame, under a runner that meets `StaticKeeps`, is a static touch step
with no touch (round 52). EthLib #1619 replaced `staticStep_runFrame` by
`staticTouchStep_runFrame`, whose conclusion names some list of touched addresses. This is the
same induction with the runner's list fixed to `[]`, so the end state keeps every address. -/
theorem static_runFrame (hkeep : StaticKeeps runChild) {evm after : Evm fork Nat}
    {within : GasMeter.gasHeld evm.gas ≤ bound} (hf : StaticFrame evm)
    (h : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok after) :
    StaticTouchStep [] evm after := by
  fun_induction Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within
  case case1 => cases h
  case case2 => cases h; exact .of_staticStep (staticStep_exceptionalHalt _ _)
  case case3 =>
    rename_i result _ ih
    have n : StaticStep _ _ := staticTouchResult_step hf.1 hf.2.1 hf.2.2 result
    exact n.trans_touchStep (ih (StaticFrame.of_staticStep n hf) h)
  case case4 => cases h
  case case5 => cases h
  case case6 => cases h; exact .of_staticStep (staticStep_exceptionalHalt _ _)
  case case7 =>
    obtain ⟨c0, hmsg, hres⟩ :=
      staticTouchResult_step hf.1 hf.2.1 hf.2.2 ‹step _ _ = .ok (.child _ _ _)›
    obtain ⟨kept, parent⟩ :=
      hkeep (StaticFrame.of_staticStep c0 hf) hmsg ‹runChild _ _ _ = .ok _›
    have n := hres [] _ _ (by assumption)
      ⟨kept, fun a k => (kept a (by simp)).2.1 k, fun a k => (kept a (by simp)).2.2 k,
        by simp⟩ parent (by simp)
    have htr := ‹StaticFrame _ → Evm.runFrame _ _ _ _ _ _ = .ok after → StaticTouchStep [] _ after›
      (StaticFrame.of_touchStep n hf) h
    simpa using n.trans htr
  case case8 => cases h; exact .refl _

/-- A run of a fresh static frame of `CODE`, for a message whose code is `CODE` at an account that
holds code (`StaticCode`), under a runner that meets `StaticKeeps`: the end state reads as the
start state at every address (account, storage, transient storage). Any fork, any gas. -/
theorem static_run (hst : message.isStatic = true) (hmc : message.code = CODE)
    (hhold : StaticCode state message) (hkeep : StaticKeeps runChild)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s) :
    State.TransactionState.SameOutside [] state s.state := by
  obtain ⟨hc, -, hm, -, -, -, -, -, -, -, hs, -⟩ := start
  have hf : StaticFrame evm :=
    ⟨by rw [hm]; exact hst, by rw [hc, hm, hmc], by rw [hs, hm]; exact hhold⟩
  have hk := (static_runFrame hkeep hf hrun).state.1
  rw [hs] at hk
  exact hk

/-- In a static frame, as in `static_run`, `Inv C` at the start gives `Inv C` at the end of every
run that ends with `.ok`, for any fork. -/
theorem inv_static (hst : message.isStatic = true) (hmc : message.code = CODE)
    (hhold : StaticCode state message) (hkeep : StaticKeeps runChild)
    (hI : Inv message.currentTarget state)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s) :
    Inv message.currentTarget s.state := by
  have so := static_run hst hmc hhold hkeep start within hrun
  refine (DepInv.inv_congr (fun n => ?_)).mpr hI
  exact (so message.currentTarget (by simp)).2.1 _

/-- The invariant over every successful call, static or not.

From Berlin (Glamsterdam included, deprecated or not), a fresh frame of `CODE` at pc 0 with any call data below
2^256 bytes, any value, any gas, any gas bound and any message runner, under `SepOn` of the
call's keys (`callKeys`), with
string slots 7 and 8 of `StrForm`, and:
- when the frame is static (`hstat`): the code of the message is `CODE`, it runs at an account
  that holds code (`StaticCode`), and the runner meets `StaticKeeps`;
- when deprecated (byte 20 of slot 10 not 0): the runner meets `KeepsInvAt` (`hkeeps`), and for
  destroyBlackFunds `HonestBalanceAt` (`hhonest`).
No `hacc` (since round 20): when the frame is not static, no account of the contract is assumed;
when it is static, `StaticCode` for the nonempty code `CODE` implies one.
If `Inv C state` holds and the interpreter loop ends with no error, then `Inv C s.state` holds. -/
theorem inv_call_all (K : SepOn (callKeys message state)) (hfork : .berlin ≤ fork)
    (hstat : message.isStatic = true →
      message.code = CODE ∧ StaticCode state message ∧ StaticKeeps runChild)
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
  cases hs : message.isStatic
  · exact inv_call_ns K hfork hsize' h7 h8 hkeeps hhonest hI start within hrun hok
  · obtain ⟨hmc, hhold, hkeep⟩ := hstat hs
    exact inv_static hs hmc hhold hkeep hI start within hrun

end UsdtVerify.Complete
