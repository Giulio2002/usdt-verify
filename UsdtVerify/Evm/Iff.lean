import UsdtVerify.Evm.Exact
import UsdtVerify.Evm.Route

/-!
# Exact success conditions

- `RunsOk`: the loop of the interpreter, run from a frame, ends in a frame with no error.
- `runsOk_of_spec`: a specification to a frame with no error gives `RunsOk`.
- `runsOk_iff`: a condition `G` under which a specification to a frame with no error holds, and
  that every run ending with no error meets, is equivalent to `RunsOk`.
- `not_runsOk_low`: with a condition `G` that every run ending with no error meets, and under
  which a specification to a normal halt that pays `cost` holds for every gas from a bound
  `B ≥ cost` on, no run with less gas than `cost` ends with no error.
-/

namespace UsdtVerify.Exact

open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open UsdtVerify.Gas

variable {fork : Fork} {code : ByteArray} {message : Message fork} {pc : Nat}
  {stack : List U256} {memory : ByteArray} {state : State.TransactionState}
  {substate : Substate} {bound : Nat} {runChild : MessageRunner fork Nat bound}
  {evm : Evm fork Nat}

/-- The loop of the interpreter, run from `evm` with gas bound `bound` and message runner
`runChild`, ends in a frame with no error. -/
def RunsOk (fork : Fork) (bound : Nat) (runChild : MessageRunner fork Nat bound)
    (evm : Evm fork Nat) (within : GasMeter.gasHeld evm.gas ≤ bound) : Prop :=
  ∃ s, Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s ∧
    s.error = none

/-- A normal halt has no error. -/
theorem halted_false_ok {out : ByteArray} {g : Nat} {st : State.TransactionState}
    {ss : Substate} (e : Evm fork Nat) (h : Halted false out g st ss e) : e.error = none := by
  rw [h.2.1]; simp

/-- A specification to frames with no error, from a frame where its precondition holds. -/
theorem runsOk_of_spec {P Q : Evm fork Nat → Prop} (h : SpecG fork P Q)
    (hQ : ∀ e, Q e → e.error = none) (hp : P evm) (within : GasMeter.gasHeld evm.gas ≤ bound) :
    RunsOk fork bound runChild evm within := by
  obtain ⟨s, hs, hq⟩ := SpecG.runFrame h hp within (runChild := runChild)
  exact ⟨s, hs, hQ s hq⟩

/-- `RunsOk` holds exactly when `G` holds, if `G` gives a specification to frames with no error
and every run that ends with no error meets `G`. -/
theorem runsOk_iff {G : Prop} {P Q : Evm fork Nat → Prop} (hspec : G → SpecG fork P Q)
    (hQ : ∀ e, Q e → e.error = none) (hp : P evm) (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hcomp : ∀ s, Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within =
      .ok s → s.error = none → G) :
    RunsOk fork bound runChild evm within ↔ G :=
  ⟨fun ⟨s, hs, hok⟩ => hcomp s hs hok, fun hg => runsOk_of_spec (hspec hg) hQ hp within⟩

/-- With less gas than `cost`, no run ends with no error, if every run that ends with no error
meets `G`, and under `G` a specification to a normal halt that pays `cost` holds from `B` gas
on. -/
theorem not_runsOk_low {G : Prop} {B cost gas : Nat} (hB : cost ≤ B) (hlt : gas < cost)
    {out : ByteArray} {st' : State.TransactionState} {ss' : Substate}
    (hspec : G → ∀ g, B ≤ g → SpecG fork (At code message pc stack memory g state substate)
      (Halted false out (g - cost) st' ss'))
    (start : At code message pc stack memory gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hcomp : ∀ s, Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within =
      .ok s → s.error = none → G) :
    ¬ RunsOk fork bound runChild evm within := by
  rintro ⟨s, hs, hok⟩
  have := (Complete.ok_exact hB (hspec (hcomp s hs hok)) start within hs hok).1
  omega

/-- `not_runsOk_low` for a specification with two gas bounds, the second one the cost. -/
theorem not_runsOk_low2 {G : Prop} {B1 cost gas : Nat} (hlt : gas < cost)
    {out : ByteArray} {st' : State.TransactionState} {ss' : Substate}
    (hspec : G → ∀ g, B1 ≤ g → cost ≤ g →
      SpecG fork (At code message pc stack memory g state substate)
        (Halted false out (g - cost) st' ss'))
    (start : At code message pc stack memory gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hcomp : ∀ s, Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within =
      .ok s → s.error = none → G) :
    ¬ RunsOk fork bound runChild evm within :=
  not_runsOk_low (B := B1 + cost) (Nat.le_add_left _ _) hlt
    (fun hG g hg => hspec hG g (Complete.le_l hg) (Complete.le_r hg)) start within hcomp

/-- `not_runsOk_low` for a specification with three gas bounds, the third one the cost. -/
theorem not_runsOk_low3 {G : Prop} {B1 B2 cost gas : Nat} (hlt : gas < cost)
    {out : ByteArray} {st' : State.TransactionState} {ss' : Substate}
    (hspec : G → ∀ g, B1 ≤ g → B2 ≤ g → cost ≤ g →
      SpecG fork (At code message pc stack memory g state substate)
        (Halted false out (g - cost) st' ss'))
    (start : At code message pc stack memory gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hcomp : ∀ s, Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within =
      .ok s → s.error = none → G) :
    ¬ RunsOk fork bound runChild evm within :=
  not_runsOk_low2 (B1 := B1 + B2) hlt
    (fun hG g h1 h2 => hspec hG g (Complete.le_l h1) (Complete.le_r h1) h2) start within hcomp

/-! ## Paths that forward a message -/

open UsdtVerify.Complete (Route Routes SendsVia)

/-- The runner returns a frame for every message. -/
def NoFail (runChild : MessageRunner fork Nat bound) : Prop :=
  ∀ caller msg lt e, runChild caller msg lt ≠ .error e

/-- The callee assumption: a message forwarded from `M` to `ua` along the route `r` with data `d`
ends with no error exactly when `A` holds. -/
def AnsIff (M : Message fork) (ua : EthLib.Base.Address) (c : ByteArray) (r : Route)
    (d : ByteArray) (A : Prop) : Evm fork Nat → Message fork → Evm fork Nat → Prop :=
  fun _ msg child => SendsVia M ua c r d msg → (child.error = none ↔ A)

/-- A specification under a callee assumption, a runner that meets it and never fails: the loop
ends with no error when every end frame of the specification has none. -/
theorem runsOk_of_specUnder {callee : Evm fork Nat → Message fork → Evm fork Nat → Prop}
    {P Q : Evm fork Nat → Prop} (h : SpecUnder fork callee P Q) (meets : Meets callee runChild)
    (hnf : NoFail runChild) (hQ : ∀ e, Q e → e.error = none) (hp : P evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    RunsOk fork bound runChild evm within := by
  obtain ⟨after, hreach, ⟨halted, hq⟩ | aborted⟩ := h bound runChild meets evm hp within
  · refine ⟨after, ?_, hQ _ hq⟩
    rw [runFrame_eq_of_reaches StepBy.gasHeld_le StepBy.runFrame_eq hreach within,
      runFrame_of_running_eq_false halted]
  · obtain ⟨-, caller, msg, -, -, lt, e, failed⟩ := aborted
    exact absurd failed (hnf caller msg lt e)

/-- A path that forwards one message: `RunsOk` holds exactly when `G` and `A` hold. -/
theorem fwd_ok_iff {G A : Prop} {P : Evm fork Nat → Prop} {M : Message fork}
    {ua : EthLib.Base.Address} {c : ByteArray} {r : Route} {d : ByteArray}
    (hspec : G → SpecUnder fork (AnsIff M ua c r d A) P (fun e => A → e.error = none))
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hcomp : ∀ s, Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within =
      .ok s → s.error = none → G ∧ ∃ caller msg lt child, runChild caller msg lt = .ok child ∧
        child.1.error = none ∧ SendsVia M ua c r d msg)
    (hans : ∀ caller msg lt child, runChild caller msg lt = .ok child → SendsVia M ua c r d msg →
      (child.1.error = none ↔ A))
    (hnf : NoFail runChild) (hp : P evm) :
    RunsOk fork bound runChild evm within ↔ G ∧ A := by
  constructor
  · rintro ⟨s, hs, hok⟩
    obtain ⟨hG, caller, msg, lt, child, hch, he, hfwd⟩ := hcomp s hs hok
    exact ⟨hG, (hans caller msg lt child hch hfwd).1 he⟩
  · rintro ⟨hG, hA⟩
    exact runsOk_of_specUnder (hspec hG)
      ⟨fun caller msg lt child hch hfwd => hans caller msg lt child hch hfwd,
        fun caller msg lt e h => absurd h (hnf caller msg lt e)⟩
      hnf (fun e h => h hA) hp within

/-- A code has at most one route in a state. -/
theorem routes_unique {st : State.TransactionState} {c : ByteArray} {r r' : Route}
    (h : Routes fork st c r) (h' : Routes fork st c r') : r = r' := by
  rcases r with _ | ⟨d, c1⟩ <;> rcases r' with _ | ⟨d', c2⟩
  · rfl
  · obtain ⟨hp, hd, -⟩ := h'
    rw [h hp] at hd; cases hd
  · obtain ⟨hp, hd, -⟩ := h
    rw [h' hp] at hd; cases hd
  · obtain ⟨-, hd, hc⟩ := h
    obtain ⟨-, hd', hc'⟩ := h'
    rw [hd] at hd'; cases hd'
    rw [hc] at hc'; cases hc'
    rfl

end UsdtVerify.Exact
