import EthLib.Execution.Proofs.Evm.Logic.Rules
import EthLib.Execution.Proofs.Evm.Logic.Fault

/-!
# Runs with less gas

A run with less gas follows the run with more gas, or it fails.

- `sh k e`: the frame `e` with `k` more gas.
- `Fails r`: the result `r` of an instruction is an error, or a stopped frame with an error.
- `RunMono run`: for every frame `a`, the instruction on `a` fails, or it gives a frame `b` and the
  instruction on `sh k a` gives `sh k b`.
- `GasMono x`: the same, for the step of the interpreter from every frame with `k` less gas
  than `x`.
- `StepG`: a step of EthLib's relation `Step` from a frame that is `GasMono`. `HoareG` and
  `SpecG` are triples over `StepG`; they imply EthLib's `Hoare` and `Spec`.
- `At.ruleG`: the rule of one opcode, as EthLib's `At.rule`, for an instruction that is `RunMono`.
- `low_of_reaches`, `SpecG.low`: if a `SpecG` holds from `sh k l`, and the loop of the
  interpreter run from `l` ends with no error, then that end frame `s` has `sh k s` in the
  postcondition. So a successful run with less gas ends as the run with more gas, with exactly
  `k` less gas left.

GAS (0x5a) is not `RunMono`: it pushes the gas left. The calls are not instructions of the table
`instruction`. No rule for them is given here.
-/

namespace UsdtVerify.Gas

open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic

variable {fork : Fork}

/-- The frame `e` with `k` more gas. -/
def sh (k : Nat) (e : Evm fork Nat) : Evm fork Nat := { e with gas := e.gas + k }

/-- A result of an instruction that is no success: an error, or a stopped frame with an error. -/
def Fails (r : Except EvmError (Evm fork Nat)) : Prop :=
  (∃ e, r = .error e) ∨ ∃ b, r = .ok b ∧ b.running = false ∧ b.error ≠ none

/-- The result `lo` fails, or it is a frame whose shift by `k` is the result `hi`. -/
def Rel (k : Nat) (lo hi : Except EvmError (Evm fork Nat)) : Prop :=
  Fails lo ∨ ∃ b, lo = .ok b ∧ hi = .ok (sh k b)

/-- An instruction that, with `k` more gas, gives the same frame with `k` more gas, or that fails
with less. -/
def RunMono (run : Evm fork Nat → Except EvmError (Evm fork Nat)) : Prop :=
  ∀ a k, Rel k (run a) (run (sh k a))

/-- `Rel` for the results of a step. -/
def RelS (k : Nat) (lo hi : Except EvmError (StepResult fork Nat)) : Prop :=
  (∃ e, lo = .error e) ∨ (∃ b, lo = .ok (.next b) ∧ b.running = false ∧ b.error ≠ none) ∨
    ∃ b, lo = .ok (.next b) ∧ hi = .ok (.next (sh k b))

/-- From every frame with `k` less gas than `x`, the step fails, or it follows the step from `x`. -/
def GasMono (x : Evm fork Nat) : Prop :=
  ∀ k l, x = sh k l → RelS k (step fork l) (step fork x)

/-- A step from a frame that is `GasMono`. -/
def StepG (fork : Fork) (x y : Evm fork Nat) : Prop := Step fork x y ∧ GasMono x

/-- A triple over the steps from frames that are `GasMono`. -/
abbrev HoareG (fork : Fork) (P Q : Evm fork Nat → Prop) : Prop := Triple (StepG fork) P Q

/-- A specification over the steps from frames that are `GasMono`. -/
def SpecG (fork : Fork) (P Q : Evm fork Nat → Prop) : Prop :=
  HoareG fork P fun evm => evm.running = false ∧ Q evm

@[simp] theorem gas_sh (k : Nat) (e : Evm fork Nat) : (sh k e).gas = e.gas + k := rfl
@[simp] theorem running_sh (k : Nat) (e : Evm fork Nat) : (sh k e).running = e.running := rfl
@[simp] theorem error_sh (k : Nat) (e : Evm fork Nat) : (sh k e).error = e.error := rfl
@[simp] theorem state_sh (k : Nat) (e : Evm fork Nat) : (sh k e).state = e.state := rfl
@[simp] theorem substate_sh (k : Nat) (e : Evm fork Nat) : (sh k e).substate = e.substate := rfl
@[simp] theorem output_sh (k : Nat) (e : Evm fork Nat) : (sh k e).output = e.output := rfl

/-! ## From instructions to steps -/

theorem relS_of_rel {k : Nat} {lo hi : Except EvmError (Evm fork Nat)} (h : Rel k lo hi) :
    RelS k (StepResult.next <$> lo) (StepResult.next <$> hi) := by
  rcases h with (⟨e, rfl⟩ | ⟨b, rfl, hr, he⟩) | ⟨b, rfl, rfl⟩
  · exact .inl ⟨e, rfl⟩
  · exact .inr (.inl ⟨b, rfl, hr, he⟩)
  · exact .inr (.inr ⟨b, rfl, rfl⟩)

/-- A frame at an opcode whose instruction is `RunMono` is `GasMono`. -/
theorem gasMono_of_run {x : Evm fork Nat} {op : Op}
    {run : Evm fork Nat → Except EvmError (Evm fork Nat)} (hlt : x.pc < x.code.size)
    (decoded : Op.ofByte fork x.code[x.pc] = some op) (hrun : instruction fork op = some run)
    (hm : RunMono run) : GasMono x := by
  rintro k l rfl
  rw [step_of_instruction (evm := l) hlt decoded hrun,
    step_of_instruction (evm := sh k l) hlt decoded hrun]
  exact relS_of_rel (hm l k)

/-- A frame at a byte that is no opcode at the fork is `GasMono`: both steps fail. -/
theorem gasMono_of_none {x : Evm fork Nat} (hlt : x.pc < x.code.size)
    (none : Op.ofByte fork x.code[x.pc] = none) : GasMono x := by
  rintro k l rfl
  exact .inl ⟨_, step_of_ofByte_eq_none (evm := l) hlt none⟩

/-! ## Triples over `StepG` -/

theorem reaches_toStep {a b : Evm fork Nat} (h : Reaches (StepG fork) a b) :
    Reaches (Step fork) a b :=
  h.mono fun hs => hs.1

theorem HoareG.toHoare {P Q : Evm fork Nat → Prop} (h : HoareG fork P Q) : Hoare fork P Q :=
  fun evm hp =>
    let ⟨after, hr, hq⟩ := h evm hp
    ⟨after, reaches_toStep hr, hq⟩

theorem SpecG.toSpec {P Q : Evm fork Nat → Prop} (h : SpecG fork P Q) : Spec fork P Q :=
  HoareG.toHoare h

theorem SpecG.seq {P Q R : Evm fork Nat → Prop} (first : HoareG fork P Q)
    (second : SpecG fork Q R) : SpecG fork P R := Triple.seq first second

theorem SpecG.consequence {P P' Q Q' : Evm fork Nat → Prop} (h : SpecG fork P Q)
    (pre : ∀ evm, P' evm → P evm) (post : ∀ evm, Q evm → Q' evm) : SpecG fork P' Q' :=
  Triple.consequence h pre fun evm ⟨hs, hq⟩ => ⟨hs, post evm hq⟩

/-- `SpecG` for the loop of the interpreter, through EthLib's `Spec.runFrame`. -/
theorem SpecG.runFrame {P Q : Evm fork Nat → Prop} (h : SpecG fork P Q)
    {bound : Nat} {runChild : MessageRunner fork Nat bound} {evm : Evm fork Nat}
    (hp : P evm) (within : GasMeter.gasHeld evm.gas ≤ bound) :
    ∃ stopped, Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within =
      .ok stopped ∧ Q stopped :=
  Spec.runFrame (SpecG.toSpec h) hp within

/-- The rule of one opcode over `StepG`: EthLib's `At.rule`, for an instruction that is
`RunMono`. -/
theorem At.ruleG {code : ByteArray} {message : Message fork} {pc : Nat} {stack : List U256}
    {memory : ByteArray} {gas : Nat} {state : State.TransactionState} {substate : Substate}
    {byte : UInt8} {op : Op}
    {run : Evm fork Nat → Except EvmError (Evm fork Nat)} {post : Evm fork Nat → Prop}
    (hlt : pc < code.size) (hbyte : code[pc] = byte) (decoded : Op.ofByte fork byte = some op)
    (hrun : instruction fork op = some run) (hm : RunMono run)
    (h : ∀ evm, At code message pc stack memory gas state substate evm →
      ∃ after, run evm = .ok after ∧ post after) :
    HoareG fork (At code message pc stack memory gas state substate) post := by
  apply Triple.of_step
  intro evm hp
  obtain ⟨after, ok, hpost⟩ := h evm hp
  refine ⟨after, ⟨Step.of_code hp.2.2.2.2.2.2.2.1 hp.1 hp.2.2.2.1 hlt hbyte decoded hrun ok, ?_⟩,
    hpost⟩
  obtain ⟨hcode, -, -, hpc, -⟩ := hp
  subst hcode hpc
  exact gasMono_of_run hlt (by rw [hbyte]; exact decoded) hrun hm

/-- A frame at the byte `0xfe` halts with an invalid opcode, over `StepG`. -/
theorem invalid_feG {code : ByteArray} {message : Message fork} {pc : Nat} {stack : List U256}
    {memory : ByteArray} {gas : Nat} {state : State.TransactionState} {substate : Substate}
    (hlt : pc < code.size) (hbyte : code[pc] = 0xfe) :
    SpecG fork (At code message pc stack memory gas state substate)
      (Faulted (.invalidOpcode 0xfe) state substate) := by
  apply Triple.of_step
  intro evm hat
  obtain ⟨hcode, -, -, hpc, -, -, -, hrun, -, -, hs, hss⟩ := id hat
  have hlt' : evm.pc < evm.code.size := by rw [hcode, hpc]; exact hlt
  have hnone : Op.ofByte fork evm.code[evm.pc] = none := by
    subst hcode hpc; rw [hbyte]; rfl
  have hstep : step fork evm = .error (.invalidOpcode 0xfe) := by
    rw [step_of_ofByte_eq_none hlt' hnone]
    subst hcode hpc; rw [hbyte]
  exact ⟨_, ⟨Step.halt hrun hstep rfl, gasMono_of_none hlt' hnone⟩,
    rfl, rfl, rfl, rfl, rfl, hs, hss⟩

/-! ## Lifting triples over `StepG` to triples over `Step` -/

/-- Every step of `R` is a step of `R'`. -/
class StepLift (R R' : Evm fork Nat → Evm fork Nat → Prop) : Prop where
  lift : ∀ {x y}, R x y → R' x y

instance StepLift.refl (R : Evm fork Nat → Evm fork Nat → Prop) : StepLift R R := ⟨id⟩

instance StepLift.stepG : StepLift (StepG fork) (Step fork) := ⟨And.left⟩

theorem Triple.lift {R R' : Evm fork Nat → Evm fork Nat → Prop} [StepLift R R']
    {P Q : Evm fork Nat → Prop} (h : Triple R P Q) : Triple R' P Q :=
  fun evm hp =>
    let ⟨after, hr, hq⟩ := h evm hp
    ⟨after, hr.mono StepLift.lift, hq⟩

/-- Sequence of a triple over `R` and one over `R'`, when every `R` step is an `R'` step. -/
theorem Triple.seqL {R R' : Evm fork Nat → Evm fork Nat → Prop} [StepLift R R']
    {P Q S : Evm fork Nat → Prop} (first : Triple R P Q) (second : Triple R' Q S) :
    Triple R' P S :=
  Triple.seq (Triple.lift first) second

instance {P Q : Evm fork Nat → Prop} : Coe (HoareG fork P Q) (Hoare fork P Q) :=
  ⟨HoareG.toHoare⟩

instance {P Q : Evm fork Nat → Prop} : Coe (SpecG fork P Q) (Spec fork P Q) :=
  ⟨SpecG.toSpec⟩

/-! ## A run with less gas -/

section Loop

variable {bound : Nat} {runChild : MessageRunner fork Nat bound}

theorem runFrame_stopped {evm : Evm fork Nat} (h : evm.running = false)
    {within : GasMeter.gasHeld evm.gas ≤ bound} :
    Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok evm := by
  rw [Evm.runFrame]
  simp [h]

/-- Along a chain of `StepG` from `sh k l` to a stopped frame `z`: if the loop of the interpreter
run from `l` ends with no error in `s`, then `z = sh k s`. -/
theorem low_of_reaches {hi z : Evm fork Nat} (hr : Reaches (StepG fork) hi z)
    (hz : z.running = false) :
    ∀ (k : Nat) (l : Evm fork Nat), hi = sh k l →
      ∀ (within : GasMeter.gasHeld l.gas ≤ bound) {s : Evm fork Nat},
        Evm.runFrame (step fork) (step_decreases fork) bound runChild l within = .ok s →
        s.error = none → z = sh k s := by
  induction hr with
  | refl =>
    rintro k l rfl within s hs _
    rw [runFrame_stopped (by simpa using hz)] at hs
    cases hs
    rfl
  | step hs _ ih =>
    rintro k l rfl within s hrun hok
    obtain ⟨hstep, hmono⟩ := hs
    have hr : l.running = true := hstep.running
    rcases hmono k l rfl with ⟨e, he⟩ | ⟨b, hb, hbr, hbe⟩ | ⟨b, hb, hh⟩
    · by_cases ab : e.aborts = true
      · rw [runFrame_of_step_eq_abort hr he ab] at hrun
        cases hrun
      · rw [runFrame_of_step_eq_error hr he (by simpa using ab)] at hrun
        cases hrun
        simp [exceptionalHalt] at hok
    · rw [runFrame_of_step_eq_next hr hb, runFrame_stopped hbr] at hrun
      cases hrun
      exact absurd hok hbe
    · rw [runFrame_of_step_eq_next hr hb] at hrun
      cases hstep with
      | next _ hn =>
        rw [hh] at hn
        cases hn
        exact ih hz k b rfl _ hrun hok
      | halt _ hn _ =>
        rw [hh] at hn
        cases hn

/-- A specification over `StepG` from `sh k l`, and a run from `l` that ends with no error in
`s`: the postcondition holds of `sh k s`. -/
theorem SpecG.low {P Q : Evm fork Nat → Prop} (h : SpecG fork P Q) {k : Nat} {l : Evm fork Nat}
    (hp : P (sh k l)) (within : GasMeter.gasHeld l.gas ≤ bound) {s : Evm fork Nat}
    (hs : Evm.runFrame (step fork) (step_decreases fork) bound runChild l within = .ok s)
    (hok : s.error = none) : Q (sh k s) := by
  obtain ⟨z, hr, hz, hq⟩ := h _ hp
  rw [← low_of_reaches hr hz k l rfl within hs hok]
  exact hq

end Loop

/-- A frame `At` some gas is, with `k` more gas, `At` that gas plus `k`. -/
theorem at_sh {code : ByteArray} {message : Message fork} {pc : Nat} {stack : List U256}
    {memory : ByteArray} {gas : Nat} {state : State.TransactionState} {substate : Substate}
    {l : Evm fork Nat} (h : At code message pc stack memory gas state substate l) (k : Nat) :
    At code message pc stack memory (gas + k) state substate (sh k l) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, by simp [h7], h8, h9, h10, h11, h12⟩

/-- A run that ends with no error in `s`, from a frame where a `SpecG` to a normal halt holds
with `k` more gas: `s` is that halt, with `k` less gas. -/
theorem SpecG.halted {code : ByteArray} {message : Message fork} {pc : Nat} {stack : List U256}
    {memory : ByteArray} {gas : Nat} {state : State.TransactionState} {substate : Substate}
    {out : ByteArray} {g' : Nat} {st' : State.TransactionState} {ss' : Substate} {k : Nat}
    (h : SpecG fork (At code message pc stack memory (gas + k) state substate)
      (Halted false out g' st' ss'))
    {bound : Nat} {runChild : MessageRunner fork Nat bound} {l : Evm fork Nat}
    (hl : At code message pc stack memory gas state substate l)
    (within : GasMeter.gasHeld l.gas ≤ bound) {s : Evm fork Nat}
    (hs : Evm.runFrame (step fork) (step_decreases fork) bound runChild l within = .ok s)
    (hok : s.error = none) :
    s.running = false ∧ s.output = out ∧ s.gas + k = g' ∧ s.state = st' ∧ s.substate = ss' := by
  obtain ⟨hr, -, ho, hg, hst, hss⟩ := SpecG.low h (at_sh hl k) within hs hok
  exact ⟨hr, ho, hg, hst, hss⟩

/-- A run with no error is impossible from a frame where a `SpecG` to a frame with an error
holds with `k` more gas. -/
theorem SpecG.not_ok {P Q : Evm fork Nat → Prop} (h : SpecG fork P Q)
    (herr : ∀ e, Q e → e.error ≠ none) {k : Nat} {l : Evm fork Nat} (hp : P (sh k l))
    {bound : Nat} {runChild : MessageRunner fork Nat bound}
    (within : GasMeter.gasHeld l.gas ≤ bound) {s : Evm fork Nat}
    (hs : Evm.runFrame (step fork) (step_decreases fork) bound runChild l within = .ok s) :
    s.error ≠ none := by
  intro hok
  exact herr _ (SpecG.low h hp within hs hok) (by simpa using hok)

end UsdtVerify.Gas
