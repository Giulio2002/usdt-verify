import UsdtVerify.Complete.DepInvAll
import EthLib.Execution.Proofs.Evm.Call.StaticMessage

/-!
# A static frame keeps the state, and the invariant over every successful call

EthLib proves that a step of a static frame keeps the state up to the records of its reads
(`staticResult_step`; SSTORE, TSTORE, LOG and SELFDESTRUCT do not continue in such a frame), and
that a whole run of a static frame does (`staticStep_runFrame`), when the runner ends every
static child message with a state that differs from its caller's only by reads.

- `StaticKeeps runChild`: that runner assumption, named (EthLib's premise of
  `staticStep_runFrame`).
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
  a frame that is not static it is `inv_call_ns` (Complete/DepInvAll.lean), with `hacc` (the
  contract has an account) and the deprecated-path assumptions. The hypothesis "not static" of
  `inv_call_ns` is gone.
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
caller's only by the records of reads, and keeps its block. This is the premise `runs` of EthLib's
`staticStep_runFrame`. -/
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
  have h := staticStep_runFrame (step := step fork) (decreases := step_decreases fork)
    (fun hf' hstep => staticResult_step hf'.1 hf'.2.1 hf'.2.2 hstep)
    (fun hf' hstep => staticResult_step hf'.1 hf'.2.1 hf'.2.2 hstep)
    (fun hf' hm' hr => hkeep hf' hm' hr) hf hrun
  have hk := h.state
  unfold StateKept at hk
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

From Berlin (Glamsterdam included when not deprecated; before Glamsterdam when deprecated, the
CALL rules being pre-Glamsterdam), a fresh frame of `CODE` at pc 0 with any call data below
2^256 bytes, any value, any gas, any gas bound and any message runner, under `KeccakSep`, with
string slots 7 and 8 of `StrForm`, and:
- when the frame is static (`hstat`): the code of the message is `CODE`, it runs at an account
  that holds code (`StaticCode`), and the runner meets `StaticKeeps`;
- when it is not static (`hacc`): the contract has an account;
- when deprecated (byte 20 of slot 10 not 0): the runner meets `KeepsInv` (`hkeeps`), and for
  destroyBlackFunds `HonestBalance` (`hhonest`).
If `Inv C state` holds and the interpreter loop ends with no error, then `Inv C s.state` holds. -/
theorem inv_call_all (K : KeccakSep) (hfork : .berlin ≤ fork)
    (hglam : byte20 (storageAt state message.currentTarget 10) ≠ 0 → fork < .glamsterdam)
    (hstat : message.isStatic = true →
      message.code = CODE ∧ StaticCode state message ∧ StaticKeeps runChild)
    (hacc : message.isStatic = false → hasAccount state message.currentTarget)
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
  cases hs : message.isStatic
  · exact inv_call_ns K hfork hglam hs (hacc hs) hsize' h7 h8 hkeeps hhonest hI start within hrun
      hok
  · obtain ⟨hmc, hhold, hkeep⟩ := hstat hs
    exact inv_static hs hmc hhold hkeep hI start within hrun

end UsdtVerify.Complete
