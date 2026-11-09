import UsdtVerify.Evm.Call
import UsdtVerify.Evm.Stuck
import UsdtVerify.Evm.StepSim
import UsdtVerify.Evm.Shadow
import UsdtVerify.Evm.NoState

/-!
# Runs of the meter `Nat` with an abstract child (round 39)

The deprecated paths of USDT make a CALL. A run over EthLib's EIP-8037 meter `StateGasMeter`
from reservoir 0 follows the run over `Nat` step by step up to that CALL (`Meter.step_simX`,
`Meter.step_callX`), but not after it: the child may give back a reservoir. This file states the
part of a run over `Nat` that both meters give, as a predicate on the frames of the meter `Nat`.

- `Fwd x`: the frame `x` is one that the step-by-step simulation covers: the opcode is `SimAtX`
  (an opcode of `simulated`, EXTCODESIZE or GAS) and an SSTORE there refills nothing, or it is a
  CALL with value 0 to an address whose code is found (`CallX`).
- `RunC fork Run Tail l s`: `s` has an error; or `l` is stopped and `s = l`; or `l` is running and not
  `Fwd` (the run leaves the simulation); or a `Step` from `l` and `RunC` from the next frame; or
  the step from `l` sends a message `msg` from a frame `c`, the relation `Run c msg ch` holds for
  some child frame `ch`, the resume from `ch` gives `b`, and `Ends fork b s`.
- `RunN runChild`: the relation of a message runner over `Nat`. `RunC.of_runFrame`: every end
  of the loop over `Nat` gives `RunC` with it. `EndsOk.of_runFrame`: and `EndsOk`.
- `EndsOk fork l`: a loop with some more gas than `l` ends with no error (`Ends`). The failing
  specifications from a fresh frame (the dispatcher, the guards) use it.
- Lemmas over `RunC` for a run that ends with no error: `RunC.stopped`, `RunC.next_of`,
  `RunC.not_bad`, `low_to_runningC`, `HoareJ.lowC`, `ok_splitC` (over `StepJ`, the steps from
  frames where an SSTORE neither refills nor charges state gas, since round 42), `no_okC` (a
  specification to a revert with gas left, through `HoareG.toJE`), `RunC.extcodesize`, `RunC.gasOp` (one step each), `call_okC` and
  `CallEndC` (the CALL under the relation `Run`).
-/

namespace UsdtVerify.Complete

open EthLib.Base (Fork U256 toAddressMasked Address)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic hiding HoareG SpecG StepG
open UsdtVerify.Gas
open UsdtVerify.Meter (SimAtX CallX)
open UsdtVerify.Refill (NoRefillAtN NoStateAtN StepI HoareI StepJ HoareJ)
open GasCosts
open Deprecated

variable {fork : Fork}

/-! ## The predicate -/

/-- A frame that the step-by-step simulation between the two meters covers: a `SimAtX` opcode
where an SSTORE neither refills nor charges state gas (since round 42), or a CALL with value 0 to
an address whose code is found. -/
def Fwd (x : Evm fork Nat) : Prop :=
  (SimAtX x ∧ NoRefillAtN x ∧ NoStateAtN x) ∨ CallX x

/-- A run of the meter `Nat` from `l` to `s`, with the runs of messages given by the relation
`Run`, and an exit at the frames that are not `Fwd`. After a message the run is an `Ends`. -/
inductive RunC (fork : Fork) (Run : Evm fork Nat → Message fork → Evm fork Nat → Prop)
    (Tail : Evm fork Nat → Prop) : Evm fork Nat → Evm fork Nat → Prop
  | stop {l : Evm fork Nat} : l.running = false → RunC fork Run Tail l l
  | bad {l s : Evm fork Nat} : s.error ≠ none → RunC fork Run Tail l s
  | out {l s : Evm fork Nat} : l.running = true → ¬ Fwd l → RunC fork Run Tail l s
  | step {l b s : Evm fork Nat} : Step fork l b → RunC fork Run Tail b s → RunC fork Run Tail l s
  | call {l c ch b s : Evm fork Nat} {msg : Message fork}
      {res : Evm fork Nat → Except EvmError (Evm fork Nat)} :
      l.running = true → step fork l = .ok (.child c msg res) → Run c msg ch →
      res ch = .ok b → Tail b → Ends fork b s → RunC fork Run Tail l s

/-- The runs of a message runner over `Nat`: the runner gives the child frame `ch`. -/
def RunN {bound : Nat} (runChild : MessageRunner fork Nat bound) (c : Evm fork Nat)
    (msg : Message fork) (ch : Evm fork Nat) : Prop :=
  ∃ lt h, runChild c msg lt = .ok ⟨ch, h⟩

/-- A loop with some more gas than `l` ends with no error. -/
def EndsOk (fork : Fork) (l : Evm fork Nat) : Prop :=
  ∃ k s, Ends fork (addGas k l) s ∧ s.error = none

section Nat

variable {bound : Nat} {runChild : MessageRunner fork Nat bound}

/-- A resume that fails with an error that aborts makes the run fail. -/
theorem runFrame_of_child_abort {Meter : Type} [GasMeter Meter] [LawfulGasMeter Meter] {bound : Nat}
    {runChild : MessageRunner fork Meter bound} {evm caller : Evm fork Meter}
    {message : Message fork} {resume : Evm fork Meter → Except EvmError (Evm fork Meter)}
    {child : { child : Evm fork Meter // GasMeter.gasHeld child.gas ≤ message.gas }}
    {within : GasMeter.gasHeld evm.gas ≤ bound} {e : EvmError} (running : evm.running = true)
    (sent : step fork evm = .ok (.child caller message resume)) (lt : message.gas < bound)
    (ran : runChild caller message lt = .ok child) (failed : resume child.1 = .error e)
    (aborts : e.aborts = true) :
    Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .error e := by
  rw [Evm.runFrame]
  simp only [running, dite_true]
  split <;> rename_i heq <;> rw [sent] at heq <;> cases heq
  split <;> rename_i hchild
  · rw [ran] at hchild
    cases hchild
  · rw [ran] at hchild
    cases hchild
    split <;> rename_i hresume <;> rw [failed] at hresume <;> cases hresume
    simp [aborts]

/-- **Every end of the loop over `Nat` is a `RunC`**, with the relation of its runner. -/
theorem RunC.of_runFrame {l s : Evm fork Nat} {within : GasMeter.gasHeld l.gas ≤ bound}
    (h : Evm.runFrame (Evm.step fork) (step_decreases fork) bound runChild l within = .ok s) :
    RunC fork (RunN runChild) (fun _ => True) l s := by
  by_cases hr : l.running = true
  · rcases hstep : Evm.step fork l with e | (b | ⟨c, msg, res⟩)
    · by_cases ab : e.aborts = true
      · rw [runFrame_of_step_eq_abort hr hstep ab] at h
        cases h
      · rw [runFrame_of_step_eq_error hr hstep (by simpa using ab)] at h
        cases h
        exact .step (.halt hr hstep (by simpa using ab)) (.stop rfl)
    · rw [runFrame_of_step_eq_next hr hstep] at h
      have hlt : measure b < measure l := step_decreases fork hr hstep
      exact .step (.next hr hstep) (RunC.of_runFrame h)
    · have lt : msg.gas < bound := Nat.lt_of_lt_of_le (step_decreases fork hr hstep).1 within
      rcases hch : runChild c msg lt with e | ⟨ch, hle⟩
      · rw [runFrame_of_runChild_eq_error hr hstep lt hch] at h
        cases h
      · rcases hres : res ch with e | b
        · by_cases ab : e.aborts = true
          · rw [runFrame_of_child_abort hr hstep lt hch hres ab] at h
            cases h
          · rw [runFrame_of_step_eq_child_error hr hstep lt hch hres (by simpa using ab)] at h
            cases h
            exact .bad (by simp [exceptionalHalt])
        · rw [runFrame_of_step_eq_child hr hstep lt hch hres] at h
          exact .call hr hstep ⟨lt, hle, hch⟩ hres trivial (Ends.run h)
  · have hl : l.running = false := by simpa using hr
    rw [runFrame_of_running_eq_false hl] at h
    cases h
    exact .stop hl
termination_by measure l

/-- Every end with no error of the loop over `Nat` gives `EndsOk`. -/
theorem EndsOk.of_runFrame {l s : Evm fork Nat} {within : GasMeter.gasHeld l.gas ≤ bound}
    (h : Evm.runFrame (step fork) (step_decreases fork) bound runChild l within = .ok s)
    (hok : s.error = none) : EndsOk fork l :=
  ⟨0, s, by rw [Shadow.sh_zero]; exact Ends.run h, hok⟩

end Nat

/-! ## A run that ends with no error -/

variable {Run : Evm fork Nat → Message fork → Evm fork Nat → Prop} {Tail : Evm fork Nat → Prop}

/-- From a stopped frame, a `RunC` that ends with no error ends there. -/
theorem RunC.stopped {l s : Evm fork Nat} (h : RunC fork Run Tail l s) (hl : l.running = false)
    (hok : s.error = none) : s = l := by
  cases h with
  | stop _ => rfl
  | bad he => exact absurd hok he
  | out hr _ => rw [hl] at hr; cases hr
  | step hs _ => rw [hs.running] at hl; cases hl
  | call hr _ _ _ _ _ => rw [hl] at hr; cases hr

/-- From a running `Fwd` frame whose step gives the next frame `b`, a `RunC` that ends with no
error goes on from `b`. -/
theorem RunC.next_of {l b s : Evm fork Nat} (h : RunC fork Run Tail l s) (hr : l.running = true)
    (hf : Fwd l) (hs : Evm.step fork l = .ok (.next b)) (hok : s.error = none) : RunC fork Run Tail b s := by
  cases h with
  | stop hl => rw [hl] at hr; cases hr
  | bad he => exact absurd hok he
  | out _ hn => exact absurd hf hn
  | step h1 h2 =>
    rw [Step.deterministic h1 (.next hr hs)] at h2
    exact h2
  | call _ hc _ _ _ _ => rw [hs] at hc; cases hc

/-- From a running `Fwd` frame whose step fails or halts with an error, no `RunC` ends with no
error. -/
theorem RunC.not_bad {l s : Evm fork Nat} (h : RunC fork Run Tail l s) (hr : l.running = true)
    (hf : Fwd l) (hs : StepBad (Evm.step fork l)) (hok : s.error = none) : False := by
  rcases hs with ⟨e, he⟩ | ⟨b, hb, hbr, hbe⟩
  · cases h with
    | stop hl => rw [hl] at hr; cases hr
    | bad he' => exact he' hok
    | out _ hn => exact hn hf
    | step h1 h2 =>
      cases h1 with
      | next _ hn => rw [he] at hn; cases hn
      | halt _ hn _ =>
        rw [he] at hn
        cases hn
        have := h2.stopped rfl hok
        rw [this] at hok
        simp [exceptionalHalt] at hok
    | call _ hc _ _ _ _ => rw [he] at hc; cases hc
  · have h' := h.next_of hr hf hb hok
    rw [h'.stopped hbr hok] at hok
    exact hbe hok

/-- A frame of a `StepJ` chain is `Fwd`, with any less gas. -/
theorem fwd_of_stepJ {k : Nat} {l y : Evm fork Nat} (hs : StepJ fork (addGas k l) y) : Fwd l :=
  .inl ⟨.inl hs.1.2.1, Refill.noRefillAtN_sh k hs.2.1, Refill.noStateAtN_sh k hs.2.2⟩

/-- A frame at EXTCODESIZE or GAS is `Fwd`. -/
theorem fwd_of_op {x : Evm fork Nat} {op : Op} (hlt : x.pc < x.code.size)
    (hop : Op.ofByte fork x.code[x.pc] = some op) (h : op = .extcodesize ∨ op = .gas) : Fwd x := by
  refine .inl ⟨.inr ⟨hlt, by rcases h with rfl | rfl; exact .inl hop; exact .inr hop⟩, ?_, ?_⟩
  · intro _ hs
    have e := hop.symm.trans hs
    rcases h with rfl | rfl <;> cases e
  · intro _ hs
    have e := hop.symm.trans hs
    rcases h with rfl | rfl <;> cases e

/-- **A successful `RunC` follows a `StepJ` chain.** Along a chain of `StepJ` from `addGas k l` to
`z`, a `RunC` from `l` that ends with no error goes through a frame `z'` with `z = addGas k z'`. -/
theorem low_to_runningC {hi z : Evm fork Nat} (hr : Reaches (StepJ fork) hi z) :
    ∀ (k : Nat) (l : Evm fork Nat), hi = addGas k l → ∀ {s : Evm fork Nat}, RunC fork Run Tail l s →
      s.error = none → ∃ z', z = addGas k z' ∧ RunC fork Run Tail z' s := by
  induction hr with
  | refl =>
    rintro k l rfl s hs _
    exact ⟨l, rfl, hs⟩
  | step hs _ ih =>
    rintro k l rfl s hrun hok
    have hf : Fwd l := fwd_of_stepJ hs
    obtain ⟨⟨hstep, -, hmono⟩, -⟩ := hs
    have hr : l.running = true := hstep.running
    rcases hmono k l rfl with (⟨e, he⟩ | ⟨b, hb, hbr, hbe⟩) | ⟨b, hb, hh⟩
    · exact (hrun.not_bad hr hf (.inl ⟨e, he⟩) hok).elim
    · exact (hrun.not_bad hr hf (.inr ⟨b, hb, hbr, hbe⟩) hok).elim
    · have hb' := hrun.next_of hr hf hb hok
      cases hstep with
      | next _ hn =>
        rw [hh] at hn
        cases hn
        exact ih k b rfl hb' hok
      | halt _ hn _ =>
        rw [hh] at hn
        cases hn

/-- `low_to_runningC` for a `HoareJ`. -/
theorem HoareJ.lowC {P Q : Evm fork Nat → Prop} (h : HoareJ fork P Q) {k : Nat}
    {l s : Evm fork Nat} (hp : P (addGas k l)) (hs : RunC fork Run Tail l s) (hok : s.error = none) :
    ∃ z', Q (addGas k z') ∧ RunC fork Run Tail z' s := by
  obtain ⟨z, hr, hq⟩ := h _ hp
  obtain ⟨z', rfl, hz⟩ := low_to_runningC hr k l rfl hs hok
  exact ⟨z', hq, hz⟩

/-- `ok_split` over `RunC`, for a `HoareJ`. -/
theorem ok_splitC {code : ByteArray} {message : Message fork} {pc pc' : Nat}
    {stack stack' : List U256} {memory memory' : ByteArray} {state state' : State.TransactionState}
    {substate substate' : Substate} {B c : Nat} (hB : c ≤ B)
    (h : ∀ g, B ≤ g → HoareJ fork (At code message pc stack memory g state substate)
      (At code message pc' stack' memory' (g - c) state' substate'))
    {gas : Nat} {evm s : Evm fork Nat}
    (start : At code message pc stack memory gas state substate evm)
    (hrun : RunC fork Run Tail evm s) (hok : s.error = none) :
    c ≤ gas ∧ ∃ z', At code message pc' stack' memory' (gas - c) state' substate' z' ∧
      RunC fork Run Tail z' s := by
  obtain ⟨z', hq, hz⟩ := HoareJ.lowC (h (gas + B) (by omega)) (at_addGas start B) hrun hok
  obtain ⟨hk, hat⟩ := at_unsh hq
  refine ⟨by omega, z', ?_, hz⟩
  have : gas + B - c - B = gas - c := by omega
  rw [this] at hat
  exact hat

/-- `ok_splitC` for a triple over `StepG` between `At` frames whose storage reads the same and
with less than 97,920 gas paid (`HoareG.toJA`). -/
theorem ok_splitCA {code : ByteArray} {message : Message fork} {pc pc' : Nat}
    {stack stack' : List U256} {memory memory' : ByteArray} {state state' : State.TransactionState}
    {substate substate' : Substate} {B c : Nat} (hB : c ≤ B)
    (h : ∀ g, B ≤ g → HoareG fork (At code message pc stack memory g state substate)
      (At code message pc' stack' memory' (g - c) state' substate'))
    (hc : c < 97920) (hst : ∀ a k, state'.getStorage a k = state.getStorage a k)
    {gas : Nat} {evm s : Evm fork Nat}
    (start : At code message pc stack memory gas state substate evm)
    (hrun : RunC fork Run Tail evm s) (hok : s.error = none) :
    c ≤ gas ∧ ∃ z', At code message pc' stack' memory' (gas - c) state' substate' z' ∧
      RunC fork Run Tail z' s :=
  ok_splitC hB (fun g hg => Refill.HoareG.toJA (h g hg) (by omega) hst) start hrun hok

/-- **No successful `RunC` before a revert.** A specification over `StepG` to a revert that pays
`c < 97,920` and keeps the storage, proved for every gas from `B ≥ c` on: no `RunC` from the
start frame, with any gas, ends with no error. -/
theorem no_okC {code : ByteArray} {message : Message fork} {pc : Nat} {stack : List U256}
    {memory : ByteArray} {state state' : State.TransactionState} {substate substate' : Substate}
    {out : ByteArray} {B c : Nat} (hB : c ≤ B)
    (h : ∀ g, B ≤ g → SpecG fork (At code message pc stack memory g state substate)
      (Halted true out (g - c) state' substate'))
    (hc : c < 97920) (hst : ∀ a k, state'.getStorage a k = state.getStorage a k)
    {gas : Nat} {evm s : Evm fork Nat}
    (start : At code message pc stack memory gas state substate evm)
    (hrun : RunC fork Run Tail evm s) (hok : s.error = none) : False := by
  have hI : HoareJ fork (At code message pc stack memory (gas + (B + 1)) state substate)
      (fun e => e.running = false ∧ Halted true out (gas + (B + 1) - c) state' substate' e) :=
    Refill.HoareG.toJE (h _ (by omega)) fun c' e hc' he => by
      rw [hc'.2.2.2.2.2.2.1, he.2.2.2.2.1, he.2.2.2.2.2.1, hc'.2.2.2.2.2.2.2.2.2.2.1]
      have : STORAGE_SET_STATE_GAS = 97920 := rfl
      exact ⟨by omega, .inr (by omega), hst⟩
  obtain ⟨z', ⟨hz, hh⟩, hrz⟩ := HoareJ.lowC hI (at_addGas start (B + 1)) hrun hok
  rw [hrz.stopped hz hok] at hok
  rw [show z'.error = (addGas (B + 1) z').error from rfl, hh.2.1] at hok
  simp at hok

/-- **No refill along a cheap tail** (round 42). If, from every gas `g` from `B` on, a
specification over `StepG` takes an `At` frame to a normal halt with `g - c` gas left, `c` below
97,920, and the storage as at the start, then no running frame that the run from an `At` frame
with any gas reaches along `Step` refills at an SSTORE. -/
theorem noRefill_of_specA {code : ByteArray} {message : Message fork} {pc : Nat}
    {stack : List U256} {memory out : ByteArray} {state state' : State.TransactionState}
    {substate substate' : Substate} {B c : Nat} (hB : c ≤ B) (hc : c < 97920)
    (h : ∀ g, B ≤ g → SpecG fork (At code message pc stack memory g state substate)
      (Halted false out (g - c) state' substate'))
    (hst : ∀ a k, state'.getStorage a k = state.getStorage a k)
    {gas : Nat} {evm : Evm fork Nat}
    (start : At code message pc stack memory gas state substate evm) :
    ∀ y, Reaches (Step fork) evm y → y.running = true → NoRefillAtN y := by
  obtain ⟨z, hr, hz, -⟩ := Refill.SpecG.toIA (h (gas + B) (by omega)) (by omega) hst _
    (at_addGas start B)
  exact Refill.noRefill_low hr hz

/-! ## EXTCODESIZE and GAS -/

/-- The step of an `At` frame at an instruction rule: the next frame. -/
theorem At.next_of {code : ByteArray} {message : Message fork} {pc : Nat} {stack : List U256}
    {memory : ByteArray} {gas : Nat} {state : State.TransactionState} {substate : Substate}
    {byte : UInt8} {op : Op} {run : Evm fork Nat → Except EvmError (Evm fork Nat)}
    {post : Evm fork Nat → Prop}
    (hlt : pc < code.size) (hbyte : code[pc] = byte) (decoded : Op.ofByte fork byte = some op)
    (hrun : instruction fork op = some run)
    (h : ∀ evm, At code message pc stack memory gas state substate evm →
      ∃ after, run evm = .ok after ∧ post after)
    {evm : Evm fork Nat} (hat : At code message pc stack memory gas state substate evm) :
    ∃ h : evm.pc < evm.code.size, Op.ofByte fork evm.code[evm.pc] = some op ∧
      ∃ after, step fork evm = .ok (.next after) ∧ post after := by
  obtain ⟨after, ok, hpost⟩ := h evm hat
  obtain ⟨hc, -, -, hpc, -⟩ := hat
  subst hc hpc
  have hop : Op.ofByte fork evm.code[evm.pc] = some op := by rw [hbyte]; exact decoded
  refine ⟨hlt, hop, after, ?_, hpost⟩
  rw [step_of_instruction hlt hop hrun, ok]
  rfl

section Rules

variable {code : ByteArray} {message : Message fork} {pc : Nat} {memory : ByteArray} {gas : Nat}
  {state : State.TransactionState} {substate : Substate}

/-- **EXTCODESIZE over `RunC`** (`At.extcodesize`), from Berlin: a `RunC` that ends with no
error goes on from the frame after it. -/
theorem RunC.extcodesize (hfork : .berlin ≤ fork) {word : U256} {rest : List U256}
    {c : ByteArray} (hlt : pc < code.size) (hbyte : code[pc] = 0x3b)
    (hcode : state.getCode (state.getAccount (toAddressMasked word)).codeHash = .ok c)
    (hgas : externalBaseCost fork (decide (toAddressMasked word ∉ substate.accessedAddresses)) ≤
      gas)
    {evm s : Evm fork Nat} (start : At code message pc (word :: rest) memory gas state substate evm)
    (hrun : RunC fork Run Tail evm s) (hok : s.error = none) :
    ∃ z, At code message (pc + 1) (BitVec.ofNat 256 c.size :: rest) memory
        (gas - externalBaseCost fork (decide (toAddressMasked word ∉ substate.accessedAddresses)))
        (state.recordAccountRead (toAddressMasked word))
        { substate with
          accessedAddresses := substate.accessedAddresses.insert (toAddressMasked word) } z ∧
      RunC fork Run Tail z s := by
  obtain ⟨hlt', hop, z, hz, hpost⟩ := At.next_of (post := At code message (pc + 1)
      (BitVec.ofNat 256 c.size :: rest) memory
      (gas - externalBaseCost fork (decide (toAddressMasked word ∉ substate.accessedAddresses)))
      (state.recordAccountRead (toAddressMasked word))
      { substate with
        accessedAddresses := substate.accessedAddresses.insert (toAddressMasked word) }) hlt hbyte
    (ofByte_of_decode (op := .extcodesize) rfl (Fork.frontier_le _)) rfl (fun evm hat => by
      obtain ⟨hc, hj, hm, hpc, hst, hmem, hg, hrn, herr, hout, hs, hss⟩ := hat
      have found : accountCode evm (toAddressMasked word) = .ok c := by
        simp [accountCode, hs, hcode, Except.mapError]
      rw [extcodesizeStep_of_accountCode hst found]
      simp only [accessAddress, hfork, ↓reduceIte, hss, hg, charge_nat hgas]
      exact ⟨_, rfl, hc, hj, hm, by simp [hpc], rfl, hmem, rfl, hrn, herr, hout, by simp [hs],
        by simp⟩) start
  exact ⟨z, hpost, hrun.next_of start.2.2.2.2.2.2.2.1 (fwd_of_op hlt' hop (.inl rfl)) hz hok⟩

/-- **GAS over `RunC`**: a `RunC` that ends with no error goes on from the frame after it. -/
theorem RunC.gasOp {stack : List U256} (hlt : pc < code.size) (hbyte : code[pc] = 0x5a)
    (hgas : 2 ≤ gas) (hstack : stack.length < STACK_LIMIT)
    {evm s : Evm fork Nat} (start : At code message pc stack memory gas state substate evm)
    (hrun : RunC fork Run Tail evm s) (hok : s.error = none) :
    ∃ z, At code message (pc + 1) (BitVec.ofNat 256 (gas - 2) :: stack) memory (gas - 2) state
        substate z ∧ RunC fork Run Tail z s := by
  obtain ⟨hlt', hop, z, hz, hpost⟩ := At.next_of (post := At code message (pc + 1)
      (BitVec.ofNat 256 (gas - 2) :: stack) memory (gas - 2) state substate) hlt hbyte
    (ofByte_of_decode (op := .gas) rfl (Fork.frontier_le _)) rfl (fun evm hat => by
      obtain ⟨hcode, hj, hm, hpc, hst, hmem, hg, hrn, herr, hout, hs, hss⟩ := hat
      rw [readFrame_of_length_lt (by rw [hst]; exact hstack),
        charge_nat (by rw [hg, show OPCODE_GAS = 2 from rfl]; exact hgas)]
      refine ⟨_, rfl, hcode, hj, hm, by simp [hpc], ?_, hmem, by simp [hg, OPCODE_GAS, BASE],
        hrn, herr, hout, hs, hss⟩
      simp [hst, hg, OPCODE_GAS, BASE, GasMeter.gasLeft]) start
  exact ⟨z, hpost, hrun.next_of start.2.2.2.2.2.2.2.1 (fwd_of_op hlt' hop (.inr rfl)) hz hok⟩

/-! ## CALL under the relation `Run` -/

/-- `CallEnd` with the relation `Run` in place of a message runner: `Run caller msg child` holds,
and the frame that resumes from `child` (the flag `1` for no error, the output written, the gas
back, the state and substate of `child`) `Ends` in `s`. -/
def CallEndC (Run : Evm fork Nat → Message fork → Evm fork Nat → Prop)
    (Tail : Evm fork Nat → Prop) (code : ByteArray)
    (message : Message fork)
    (pc : Nat) (asked to i isz o osz : U256) (rest : List U256) (memory : ByteArray) (gas : Nat)
    (state : State.TransactionState) (substate : Substate) (cold : Bool) (calleeCode : ByteArray)
    (r : Route) (s : Evm fork Nat) : Prop :=
  ∃ caller msg child, Run caller msg child ∧
    caller.state = (routeState (state.recordAccountRead (toAddressMasked to)) r).recordAccountRead
      message.currentTarget ∧
    caller.substate = routeSub { substate with
      accessedAddresses := substate.accessedAddresses.insert (toAddressMasked to) } r ∧
    msg.gas = (messageCallGas fork 0 asked.toNat gas
      (extendMemory memory.size [(i, isz), (o, osz)]).cost
      (accCost fork cold +
        routeCost fork (substate.accessedAddresses.insert (toAddressMasked to)) r)).subCall ∧
    msg.caller = message.currentTarget ∧ msg.currentTarget = toAddressMasked to ∧
    msg.target = some (toAddressMasked to) ∧
    msg.codeAddress = some (routeAddr (toAddressMasked to) r) ∧
    msg.code = routeCode calleeCode r ∧ msg.disablePrecompiles = r.isSome ∧
    msg.data = memoryReadBytes (memoryExtend memory
      (extendMemory memory.size [(i, isz), (o, osz)]).expandBy) i.toNat isz.toNat ∧
    msg.value = 0 ∧ msg.depth = message.depth + 1 ∧
    (msg.isStatic = message.isStatic ∧ msg.blockEnv = message.blockEnv ∧
      msg.txEnv = message.txEnv ∧ msg.shouldTransferValue = true) ∧
    ∃ after, At code message (pc + 1) ((if child.error.isNone then 1 else 0) :: rest)
      (memoryWrite (memoryExtend memory
        (extendMemory memory.size [(i, isz), (o, osz)]).expandBy)
        o.toNat (child.output.extract 0 (min osz.toNat child.output.size)))
      (gas - ((messageCallGas fork 0 asked.toNat gas
        (extendMemory memory.size [(i, isz), (o, osz)]).cost
        (accCost fork cold +
          routeCost fork (substate.accessedAddresses.insert (toAddressMasked to)) r)).cost +
        (extendMemory memory.size [(i, isz), (o, osz)]).cost) + child.gas)
      (incorporateChild fork caller child).state (incorporateChild fork caller child).substate
      after ∧
    Tail after ∧ Ends fork after s

/-- **`call_ok` over `RunC`.** A `RunC` that ends with no error through a CALL (no value) with
the gas of the accesses and the memory, below the greatest depth, along the route `r`, goes
through `CallEndC`. -/
theorem call_okC (hfork : .berlin ≤ fork)
    {asked to i isz o osz : U256} {rest : List U256} {cold : Bool} {calleeCode : ByteArray}
    {r : Route} (hlt : pc < code.size) (hbyte : code[pc] = 0xf1)
    (hcode : state.getCode (state.getAccount (toAddressMasked to)).codeHash = .ok calleeCode)
    (hroute : Routes fork state calleeCode r)
    (hdepth : message.depth + 1 ≤ STACK_DEPTH_LIMIT)
    (hcold : decide (toAddressMasked to ∉ substate.accessedAddresses) = cold)
    (hgas : accCost fork cold +
      routeCost fork (substate.accessedAddresses.insert (toAddressMasked to)) r +
      (extendMemory memory.size [(i, isz), (o, osz)]).cost ≤ gas)
    {evm s : Evm fork Nat}
    (start : At code message pc (asked :: to :: 0 :: i :: isz :: o :: osz :: rest) memory gas
      state substate evm)
    (hrun : RunC fork Run Tail evm s) (hok : s.error = none) :
    CallEndC Run Tail code message pc asked to i isz o osz rest memory gas state substate cold
      calleeCode r s := by
  have hcost := callBaseCost_eq hfork cold
  obtain ⟨hc, hj, hm, hpc, hst, hmem, hg, hr, herr, hout, hs, hss⟩ := start
  subst hm hg hs hss hcold hmem
  obtain ⟨caller, msg, hstep, c1, c2, c3, c4, c5, c6, c7, c8, c9, co, c10, c11, m1, m2, m3, mt,
      mca, m4, mdp, md, m5, m6, m7, m8, m9, m10⟩ :=
    callStep_child_r hfork hst hcode hroute hdepth
      (by rw [hcost]; omega)
  have hlt' : evm.pc < evm.code.size := by rw [hc, hpc]; exact hlt
  have hop : Op.ofByte fork evm.code[evm.pc] = some .call := by
    simp only [hc, hpc, hbyte]; exact ofByte_of_decode (op := .call) rfl (Fork.frontier_le _)
  have hsent : step fork evm = .ok (.child caller msg (resumeCall fork caller 0 o osz)) := by
    rw [step_call hlt' (by simp only [hc, hpc, hbyte])]
    exact hstep
  have hf : Fwd evm := .inr ⟨hlt', hop, _, _, _, _, _, _, _, _, hst, hcode⟩
  have hlen : caller.stack.val.length < STACK_LIMIT := by
    have := evm.stack.property
    rw [hst] at this
    rw [c5]
    simp at this
    omega
  cases hrun with
  | stop hl => rw [hl] at hr; cases hr
  | bad he => exact absurd hok he
  | out _ hn => exact absurd hf hn
  | step h1 _ =>
    cases h1 with
    | next _ hn => rw [hsent] at hn; cases hn
    | halt _ hn _ => rw [hsent] at hn; cases hn
  | @call _ c' ch b _ msg' res _ hc' hch hres hT hE =>
    rw [hsent] at hc'
    cases hc'
    obtain ⟨after, hres', a1, a2, a3, a4, a5, a6, a7, a8, a9, ao, a10, a11, -⟩ :=
      resumeCall_eq (child := ch) (o := o) (osz := osz) hlen
    rw [hres'] at hres
    have hab : after = b := Except.ok.inj hres
    subst hab
    refine ⟨caller, msg, ch, hch, c10, c11, by rw [m1, hcost], m2, m3, mt, mca, m4, mdp,
      md, m5, m6, ⟨m7, m8, m9, m10⟩, after, ?_, hT, hE⟩
    refine ⟨by rw [a1, c1, hc], by rw [a2, c2, hj], by rw [a3, c3], by rw [a4, c4, hpc],
      by rw [a5, c5], by rw [a6, c6], ?_, by rw [a8, c8, hr], by rw [a9, c9, herr],
      by rw [ao, co, hout], a10, a11⟩
    rw [a7, c7, hcost]

end Rules

/-- The price of a read of a slot is at most 2100. -/
theorem slotCost_le (c : Bool) : slotCost c ≤ 2100 := by cases c <;> decide

/-! ## Failing specifications from a fresh frame -/

/-- `no_okE` from a frame where `EndsOk` holds. -/
theorem EndsOk.no_ok {code : ByteArray} {message : Message fork} {pc : Nat} {stack : List U256}
    {memory : ByteArray} {state : State.TransactionState} {substate : Substate} {evm : Evm fork Nat}
    (hE : EndsOk fork evm) {B : Nat} {Q : Nat → Evm fork Nat → Prop}
    (h : ∀ g, B ≤ g → SpecG fork (At code message pc stack memory g state substate) (Q g))
    (herr : ∀ g e, Q g e → e.error ≠ none)
    {gas : Nat} (start : At code message pc stack memory gas state substate evm) : False :=
  let ⟨k, _, hs, hok⟩ := hE
  no_okE h herr (at_addGas start k) hs hok

end UsdtVerify.Complete
