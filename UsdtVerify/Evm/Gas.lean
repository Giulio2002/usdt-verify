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

/-- The opcodes whose step `Evm/Meter.lean` relates between the meter `Nat` and the meter
`StateGasMeter`: those of the rules here. -/
def simulated : Op → Bool
  | .stop | .add | .mul | .sub | .div | .exp | .lt | .gt | .eq | .iszero | .and | .or | .not
  | .keccak256 | .caller | .callvalue | .calldataload | .calldatasize | .pop | .mload | .mstore
  | .sload | .sstore | .jump | .jumpi | .jumpdest | .push _ | .dup _ | .swap _ | .log _
  | .«return» | .revert => true
  | _ => false

/-- The opcode at the program counter of `x`, if any, is `simulated` and has an instruction. -/
def SimAt (x : Evm fork Nat) : Prop :=
  ∀ (h : x.pc < x.code.size) (op : Op), Op.ofByte fork x.code[x.pc] = some op →
    simulated op = true ∧ (instruction (Meter := Nat) fork op).isSome = true

/-- From every frame with `k` less gas than `x`, the step fails, or it follows the step from `x`.
The opcode at `x` is `SimAt`. -/
def GasMono (x : Evm fork Nat) : Prop :=
  SimAt x ∧ ∀ k l, x = sh k l → RelS k (step fork l) (step fork x)

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

/-- A frame at a `simulated` opcode with an instruction is `SimAt`. -/
theorem simAt_of {x : Evm fork Nat} {op : Op}
    {run : Evm fork Nat → Except EvmError (Evm fork Nat)} (hlt : x.pc < x.code.size)
    (decoded : Op.ofByte fork x.code[x.pc] = some op) (hrun : instruction fork op = some run)
    (hsim : simulated op = true) : SimAt x := by
  intro h op' hop
  have e : some op = some op' := decoded.symm.trans hop
  cases e
  exact ⟨hsim, by rw [hrun]; rfl⟩

/-- A frame at an opcode whose instruction is `RunMono` is `GasMono`. -/
theorem gasMono_of_run {x : Evm fork Nat} {op : Op}
    {run : Evm fork Nat → Except EvmError (Evm fork Nat)} (hlt : x.pc < x.code.size)
    (decoded : Op.ofByte fork x.code[x.pc] = some op) (hrun : instruction fork op = some run)
    (hm : RunMono run) (hsim : simulated op = true := by first | decide | rfl) : GasMono x := by
  refine ⟨simAt_of hlt decoded hrun hsim, ?_⟩
  rintro k l rfl
  rw [step_of_instruction (evm := l) hlt decoded hrun,
    step_of_instruction (evm := sh k l) hlt decoded hrun]
  exact relS_of_rel (hm l k)

/-- A frame at a byte that is no opcode at the fork is `GasMono`: both steps fail. -/
theorem gasMono_of_none {x : Evm fork Nat} (hlt : x.pc < x.code.size)
    (none : Op.ofByte fork x.code[x.pc] = none) : GasMono x := by
  refine ⟨fun h op hop => ?_, ?_⟩
  · have e : (Option.none : Option Op) = some op := none.symm.trans hop
    cases e
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
      ∃ after, run evm = .ok after ∧ post after) (hsim : simulated op = true := by first | decide | rfl) :
    HoareG fork (At code message pc stack memory gas state substate) post := by
  apply Triple.of_step
  intro evm hp
  obtain ⟨after, ok, hpost⟩ := h evm hp
  refine ⟨after, ⟨Step.of_code hp.2.2.2.2.2.2.2.1 hp.1 hp.2.2.2.1 hlt hbyte decoded hrun ok, ?_⟩,
    hpost⟩
  obtain ⟨hcode, -, -, hpc, -⟩ := hp
  subst hcode hpc
  exact gasMono_of_run hlt (by rw [hbyte]; exact decoded) hrun hm hsim

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

/-! ## Where a loop of steps ends

`Ends fork l s`: `s` is a stopped frame that `l` reaches along `Step`, or the steps from `l`
reach a running frame that is not `SimAt` (there `s` is any frame). `Ends.run`: the loop of the
interpreter `runFrame`, for any gas bound and message runner, meets it when it ends in `s`.
Evm/Meter.lean shows that a loop over the meter `StateGasMeter` meets it too. -/

/-- A frame that a stopped frame reaches along `Step` is that frame. -/
theorem reaches_stopped {a b : Evm fork Nat} (h : Reaches (Step fork) a b)
    (ha : a.running = false) : b = a := by
  cases h with
  | refl => rfl
  | step hs _ => rw [hs.running] at ha; cases ha

/-- `s` is a stopped frame that `l` reaches along `Step`, or `l` reaches along `Step` a running
frame that is not `SimAt`. -/
def Ends (fork : Fork) (l s : Evm fork Nat) : Prop :=
  (Reaches (Step fork) l s ∧ s.running = false) ∨
    ∃ x, Reaches (Step fork) l x ∧ x.running = true ∧ ¬ SimAt x

/-- The step from a `SimAt` frame sends no message. -/
theorem SimAt.not_child {x : Evm fork Nat} (hp : SimAt x) {c : Evm fork Nat} {m : Message fork}
    {r : Evm fork Nat → Except EvmError (Evm fork Nat)} :
    step fork x ≠ .ok (.child c m r) := by
  intro h
  by_cases hlt : x.pc < x.code.size
  · rcases hop : Op.ofByte fork x.code[x.pc] with _ | op
    · rw [step_of_ofByte_eq_none hlt hop] at h
      cases h
    · obtain ⟨-, hs⟩ := hp hlt op hop
      obtain ⟨run, hrun⟩ := Option.isSome_iff_exists.mp hs
      rw [step_of_instruction hlt hop hrun] at h
      rcases hr : run x with e | b <;> simp [hr, Functor.map, Except.map] at h
  · rw [step_of_size_le (by omega)] at h
    cases h

theorem Ends.stopped {l s : Evm fork Nat} (h : Ends fork l s) (hl : l.running = false) :
    s = l := by
  rcases h with ⟨hr, -⟩ | ⟨x, hr, hx, -⟩
  · exact reaches_stopped hr hl
  · rw [reaches_stopped hr hl, hl] at hx
    cases hx

/-- From a running `SimAt` frame, `Ends` goes on from the frame of its step. -/
theorem Ends.step_exists {l s : Evm fork Nat} (h : Ends fork l s) (hr : l.running = true)
    (hp : SimAt l) : ∃ b, Step fork l b ∧ Ends fork b s := by
  rcases h with ⟨hrc, hs'⟩ | ⟨x, hrc, hx, hnp⟩
  · cases hrc with
    | refl => rw [hr] at hs'; cases hs'
    | step h1 h2 => exact ⟨_, h1, .inl ⟨h2, hs'⟩⟩
  · cases hrc with
    | refl => exact absurd hp hnp
    | step h1 h2 => exact ⟨_, h1, .inr ⟨x, h2, hx, hnp⟩⟩

theorem Ends.next {l b s : Evm fork Nat} (h : Ends fork l s) (hr : l.running = true)
    (hp : SimAt l) (hs : step fork l = .ok (.next b)) : Ends fork b s := by
  obtain ⟨b', hb, hend⟩ := h.step_exists hr hp
  rw [Step.deterministic hb (.next hr hs)] at hend
  exact hend

theorem Ends.error {l s : Evm fork Nat} {e : EvmError} (h : Ends fork l s)
    (hr : l.running = true) (hp : SimAt l) (hs : step fork l = .error e) :
    e.aborts = false ∧ s = exceptionalHalt l e := by
  obtain ⟨b, hb, hend⟩ := h.step_exists hr hp
  cases hb with
  | next _ hn => rw [hs] at hn; cases hn
  | halt _ hn hab =>
    rw [hs] at hn
    cases hn
    exact ⟨hab, hend.stopped rfl⟩

/-- `Ends` holds of the frame where the loop of the interpreter ends, for any gas bound and
message runner. -/
theorem Ends.run {l s : Evm fork Nat} {within : GasMeter.gasHeld l.gas ≤ bound}
    (h : Evm.runFrame (step fork) (step_decreases fork) bound runChild l within = .ok s) :
    Ends fork l s := by
  by_cases hr : l.running = true
  · rcases hstep : step fork l with e | (b | ⟨c, m, r⟩)
    · by_cases ab : e.aborts = true
      · rw [runFrame_of_step_eq_abort hr hstep ab] at h
        cases h
      · rw [runFrame_of_step_eq_error hr hstep (by simpa using ab)] at h
        cases h
        exact .inl ⟨.single (.halt hr hstep (by simpa using ab)), rfl⟩
    · rw [runFrame_of_step_eq_next hr hstep] at h
      have hlt : measure b < measure l := step_decreases fork hr hstep
      rcases Ends.run h with ⟨hrc, hs⟩ | ⟨x, hrc, hx, hnp⟩
      · exact .inl ⟨.step (.next hr hstep) hrc, hs⟩
      · exact .inr ⟨x, .step (.next hr hstep) hrc, hx, hnp⟩
    · by_cases hp : SimAt l
      · exact absurd hstep hp.not_child
      · exact .inr ⟨l, .refl _, hr, hp⟩
  · have hl : l.running = false := by simpa using hr
    rw [runFrame_of_running_eq_false hl] at h
    cases h
    exact .inl ⟨.refl _, hl⟩
termination_by measure l

/-- Along a chain of `StepG` from `sh k l` to a stopped frame `z`: if the loop from `l` ends in
`s` with no error (`Ends`), then `z = sh k s`. -/
theorem low_of_reachesE {hi z : Evm fork Nat} (hr : Reaches (StepG fork) hi z)
    (hz : z.running = false) :
    ∀ (k : Nat) (l : Evm fork Nat), hi = sh k l → ∀ {s : Evm fork Nat}, Ends fork l s →
      s.error = none → z = sh k s := by
  induction hr with
  | refl =>
    rintro k l rfl s hs _
    rw [hs.stopped (by simpa using hz)]
  | step hs _ ih =>
    rintro k l rfl s hend hok
    obtain ⟨hstep, hsim, hmono⟩ := hs
    have hr : l.running = true := hstep.running
    rcases hmono k l rfl with ⟨e, he⟩ | ⟨b, hb, hbr, hbe⟩ | ⟨b, hb, hh⟩
    · rw [(hend.error hr hsim he).2] at hok
      simp [exceptionalHalt] at hok
    · rw [(hend.next hr hsim hb).stopped hbr] at hok
      exact absurd hok hbe
    · cases hstep with
      | next _ hn =>
        rw [hh] at hn
        cases hn
        exact ih hz k b rfl (hend.next hr hsim hb) hok
      | halt _ hn _ =>
        rw [hh] at hn
        cases hn

/-- Along a chain of `StepG` from `sh k l` to a stopped frame `z`: if the loop of the interpreter
run from `l` ends with no error in `s`, then `z = sh k s`. -/
theorem low_of_reaches {hi z : Evm fork Nat} (hr : Reaches (StepG fork) hi z)
    (hz : z.running = false) :
    ∀ (k : Nat) (l : Evm fork Nat), hi = sh k l →
      ∀ (within : GasMeter.gasHeld l.gas ≤ bound) {s : Evm fork Nat},
        Evm.runFrame (step fork) (step_decreases fork) bound runChild l within = .ok s →
        s.error = none → z = sh k s :=
  fun k l h _ _ hrun hok => low_of_reachesE hr hz k l h (Ends.run hrun) hok

/-- A specification over `StepG` from `sh k l`, and a loop from `l` that ends in `s` with no
error (`Ends`): the postcondition holds of `sh k s`. -/
theorem SpecG.lowE {P Q : Evm fork Nat → Prop} (h : SpecG fork P Q) {k : Nat} {l : Evm fork Nat}
    (hp : P (sh k l)) {s : Evm fork Nat} (hs : Ends fork l s) (hok : s.error = none) :
    Q (sh k s) := by
  obtain ⟨z, hr, hz, hq⟩ := h _ hp
  rw [← low_of_reachesE hr hz k l rfl hs hok]
  exact hq

/-- A specification over `StepG` from `sh k l`, and a run from `l` that ends with no error in
`s`: the postcondition holds of `sh k s`. -/
theorem SpecG.low {P Q : Evm fork Nat → Prop} (h : SpecG fork P Q) {k : Nat} {l : Evm fork Nat}
    (hp : P (sh k l)) (within : GasMeter.gasHeld l.gas ≤ bound) {s : Evm fork Nat}
    (hs : Evm.runFrame (step fork) (step_decreases fork) bound runChild l within = .ok s)
    (hok : s.error = none) : Q (sh k s) :=
  SpecG.lowE h hp (Ends.run hs) hok

end Loop

/-- A frame `At` some gas is, with `k` more gas, `At` that gas plus `k`. -/
theorem at_sh {code : ByteArray} {message : Message fork} {pc : Nat} {stack : List U256}
    {memory : ByteArray} {gas : Nat} {state : State.TransactionState} {substate : Substate}
    {l : Evm fork Nat} (h : At code message pc stack memory gas state substate l) (k : Nat) :
    At code message pc stack memory (gas + k) state substate (sh k l) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, by simp [h7], h8, h9, h10, h11, h12⟩

/-- A loop that ends in `s` with no error (`Ends`), from a frame where a `SpecG` to a normal
halt holds with `k` more gas: `s` is that halt, with `k` less gas. -/
theorem SpecG.haltedE {code : ByteArray} {message : Message fork} {pc : Nat} {stack : List U256}
    {memory : ByteArray} {gas : Nat} {state : State.TransactionState} {substate : Substate}
    {out : ByteArray} {g' : Nat} {st' : State.TransactionState} {ss' : Substate} {k : Nat}
    (h : SpecG fork (At code message pc stack memory (gas + k) state substate)
      (Halted false out g' st' ss'))
    {l : Evm fork Nat} (hl : At code message pc stack memory gas state substate l)
    {s : Evm fork Nat} (hs : Ends fork l s) (hok : s.error = none) :
    s.running = false ∧ s.output = out ∧ s.gas + k = g' ∧ s.state = st' ∧ s.substate = ss' := by
  obtain ⟨hr, -, ho, hg, hst, hss⟩ := SpecG.lowE h (at_sh hl k) hs hok
  exact ⟨hr, ho, hg, hst, hss⟩

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
    s.running = false ∧ s.output = out ∧ s.gas + k = g' ∧ s.state = st' ∧ s.substate = ss' :=
  SpecG.haltedE h hl (Ends.run hs) hok

/-- A loop that ends with no error (`Ends`) is impossible from a frame where a `SpecG` to a frame
with an error holds with `k` more gas. -/
theorem SpecG.not_okE {P Q : Evm fork Nat → Prop} (h : SpecG fork P Q)
    (herr : ∀ e, Q e → e.error ≠ none) {k : Nat} {l : Evm fork Nat} (hp : P (sh k l))
    {s : Evm fork Nat} (hs : Ends fork l s) : s.error ≠ none := by
  intro hok
  exact herr _ (SpecG.lowE h hp hs hok) (by simpa using hok)

/-- A run with no error is impossible from a frame where a `SpecG` to a frame with an error
holds with `k` more gas. -/
theorem SpecG.not_ok {P Q : Evm fork Nat → Prop} (h : SpecG fork P Q)
    (herr : ∀ e, Q e → e.error ≠ none) {k : Nat} {l : Evm fork Nat} (hp : P (sh k l))
    {bound : Nat} {runChild : MessageRunner fork Nat bound}
    (within : GasMeter.gasHeld l.gas ≤ bound) {s : Evm fork Nat}
    (hs : Evm.runFrame (step fork) (step_decreases fork) bound runChild l within = .ok s) :
    s.error ≠ none :=
  SpecG.not_okE h herr hp (Ends.run hs)

end UsdtVerify.Gas
