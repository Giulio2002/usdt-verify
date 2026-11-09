import UsdtVerify.Evm.Exact
import UsdtVerify.Evm.Route
import UsdtVerify.Evm.Stuck
import EthLib.Execution.Proofs.Evm.Logic.RunsOk

/-!
# Exact success conditions

Proves the generic forms of an exact success condition: a condition is equivalent to the run
ending with no error (`RunsOk`), for a path that halts and for a path that forwards one message.

- `RunsOk` (round 52: EthLib's `RunsOk`, #1633, with the meter `Nat`; the local definition, the
  same proposition with the fork explicit, is removed): the loop of the interpreter, run from a
  frame, ends in a frame with no error. `runsOk_of_spec` (now EthLib's `Spec.runsOk`) and
  `runsOk_of_specUnder` (no use; EthLib's `SpecOn.runsOk` is the form for a runner that may fail
  on named messages) are removed.
- `halted_false_ok`: a normal halt has no error.
- `runsOk_iff`: from a frame where the precondition holds, a condition `G` under which a
  specification to a frame with no error holds, and that every run ending with no error meets,
  is equivalent to `RunsOk`.
- `not_runsOk_low`: with a condition `G` that every run ending with no error meets, and under
  which a specification to a normal halt that pays `cost` holds for every gas from a bound
  `B ≥ cost` on, no run with less gas than `cost` ends with no error.
  `not_runsOk_low2` and `not_runsOk_low3` take a specification with one or two more gas bounds.
  Round 52: proved from EthLib's `not_runsOk_of_lt` (#1633), which takes no condition `G`. The
  wrappers with `G` stay, as do `runsOk_iff`, `not_runsOk_stuck` and `iff_max`: EthLib #1633
  left out these forms as thin wrappers.
- `not_runsOk_stuck` (round 26): with a condition `G` that every run ending with no error meets,
  and under which the frame, with its own gas, reaches a `Stuck` frame (for example an SSTORE
  with at most 2300 gas left, `Gas.NoWrite`), no run ends with no error.
- `of_runsOk` (round 26): a run that ends with no error meets such a condition `G`.
- `iff_max` (round 26): the form of an exact gas threshold `max cost stip`, from `RunsOk ↔ G`
  above both bounds, failure below `cost`, failure from `cost` to below `stip`, and `RunsOk → G`.
- `NoFail`: the message runner returns a frame for every message (it never fails).
- `AnsIff M ua c r d A`: the callee assumption that a message forwarded along the route `r`
  (`SendsVia M ua c r d`) ends with no error exactly when `A` holds.
- `runsOk_of_specUnder`: a specification under a callee assumption to frames with no error,
  from a frame where its precondition holds, under a runner that meets the assumption and never
  fails, gives `RunsOk`.
- `fwd_ok_iff_fails` (round 26): for a path that forwards one message, under a runner that may
  fail with any error, from a specification that ends only at a failure of the runner on a
  forwarded message (`SpecOn`): `RunsOk` holds exactly when `G` and `A` hold, if the runner
  ends each forwarded message in a frame meeting `Q` (a condition on the caller's frame and the
  ended frame) exactly when `A` holds, and a failure of the runner on a forwarded message excludes
  `A`. Under `NoFail` the last condition holds, which gives the form for a runner that never fails.
  Round 30: the runner assumption is asked only of the messages of `S` that meet a condition
  `Cl` on the caller frame and the message (the exact theorems take `CallFrom`: the gas the CALL
  gives, and the state and substate of the caller frame at the CALL).
- `fwd_ok_or_fails` (round 31, replacing the round-26 form under `AnsIff`): the hypotheses of
  `fwd_ok_iff_fails` without `hfail`, for a runner that may fail with any error: success gives `G`
  and `A`; `G` and `A` give success or a failure of the runner on a message of `S`.
  `fwd_ok_iff_fails` is derived from it.
- `routes_unique`: a code has at most one route in a state.
-/

namespace UsdtVerify.Exact

open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic hiding HoareG SpecG SpecG.runFrame Stuck no_ok_stuck_at
open UsdtVerify.Gas

variable {fork : Fork} {code : ByteArray} {message : Message fork} {pc : Nat}
  {stack : List U256} {memory : ByteArray} {state : State.TransactionState}
  {substate : Substate} {bound : Nat} {runChild : MessageRunner fork Nat bound}
  {evm : Evm fork Nat}

/-- A normal halt has no error. -/
theorem halted_false_ok {out : ByteArray} {g : Nat} {st : State.TransactionState}
    {ss : Substate} (e : Evm fork Nat) (h : Halted false out g st ss e) : e.error = none := by
  rw [h.2.1]; simp

/-- `RunsOk` holds exactly when `G` holds, if `G` gives a specification to frames with no error
and every run that ends with no error meets `G`. -/
theorem runsOk_iff {G : Prop} {P Q : Evm fork Nat → Prop} (hspec : G → SpecG fork P Q)
    (hQ : ∀ e, Q e → e.error = none) (hp : P evm) (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hcomp : ∀ s, Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within =
      .ok s → s.error = none → G) :
    RunsOk bound runChild evm within ↔ G :=
  ⟨fun ⟨s, hs, hok⟩ => hcomp s hs hok, fun hg => Spec.runsOk (SpecG.toSpec (hspec hg)) hQ hp within⟩

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
    ¬ RunsOk bound runChild evm within := by
  rintro ⟨s, hs, hok⟩
  exact not_runsOk_of_lt (B := B) hlt
    (fun g hg _ => lowerPre (SpecG.toLogic (hspec (hcomp s hs hok) g hg))) start.toLogic within
    ⟨s, hs, hok⟩

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
    ¬ RunsOk bound runChild evm within :=
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
    ¬ RunsOk bound runChild evm within :=
  not_runsOk_low2 (B1 := B1 + B2) hlt
    (fun hG g h1 h2 => hspec hG g (Complete.le_l h1) (Complete.le_r h1) h2) start within hcomp

/-- No run ends with no error, if every run that ends with no error meets `G`, and under `G`
the frame, with its own gas, reaches a `Stuck` frame. -/
theorem not_runsOk_stuck {G : Prop} {gas : Nat}
    (hstuck : G → HoareG fork (At code message pc stack memory gas state substate) Stuck)
    (start : At code message pc stack memory gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hcomp : ∀ s, Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within =
      .ok s → s.error = none → G) :
    ¬ RunsOk bound runChild evm within := by
  rintro ⟨s, hs, hok⟩
  exact no_ok_stuck_at (hstuck (hcomp s hs hok)) start within hs hok

/-- The condition `G` of a run that ends with no error. -/
theorem of_runsOk {G : Prop} (h : RunsOk bound runChild evm within)
    (hcomp : ∀ s, Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within =
      .ok s → s.error = none → G) : G :=
  let ⟨s, hs, hok⟩ := h
  hcomp s hs hok

/-- The form of an exact gas threshold: if `R` is equivalent to `G` from `max cost stip` gas on,
fails below `cost`, fails from `cost` to below `stip`, and implies `G`, then `R` holds exactly
when `G` holds and the gas is at least `max cost stip`. -/
theorem iff_max {R G : Prop} {cost stip gas : Nat}
    (hok : cost ≤ gas → stip ≤ gas → (R ↔ G)) (hlow : gas < cost → ¬ R)
    (hmid : cost ≤ gas → gas < stip → ¬ R) (hcomp : R → G) :
    R ↔ G ∧ max cost stip ≤ gas := by
  constructor
  · intro h
    have h1 : cost ≤ gas := Nat.le_of_not_lt fun hl => hlow hl h
    have h2 : stip ≤ gas := Nat.le_of_not_lt fun hl => hmid h1 hl h
    exact ⟨hcomp h, Nat.max_le.mpr ⟨h1, h2⟩⟩
  · rintro ⟨hG, hm⟩
    exact (hok (Nat.max_le.mp hm).1 (Nat.max_le.mp hm).2).2 hG

/-! ## Paths that forward a message -/

open UsdtVerify.Complete (SendsVia)

/-- The runner returns a frame for every message. -/
def NoFail (runChild : MessageRunner fork Nat bound) : Prop :=
  ∀ caller msg lt e, runChild caller msg lt ≠ .error e

/-- The runner returns a frame for every caller frame and message that satisfy `S` (round 29,
docs/AUDIT.md finding 3: `NoFail` asks it of every message, which EthLib's `processRunner` does
not meet; the exact theorems ask it only of the messages their path sends; round 31, second audit
M1: `S` also reads the caller frame, so they ask it only from the caller frame at the CALL). -/
def NoFailOn (runChild : MessageRunner fork Nat bound) (S : Evm fork Nat → Message fork → Prop) :
    Prop :=
  ∀ caller msg lt e, S caller msg → runChild caller msg lt ≠ .error e

theorem NoFail.on {S : Evm fork Nat → Message fork → Prop} (h : NoFail runChild) :
    NoFailOn runChild S :=
  fun caller msg lt e _ => h caller msg lt e

/-- The callee assumption: a message forwarded from `M` to `ua` along the route `r` with data `d`
ends with no error exactly when `A` holds. -/
def AnsIff (M : Message fork) (ua : EthLib.Base.Address) (c : ByteArray) (r : Route)
    (d : ByteArray) (A : Prop) : Evm fork Nat → Message fork → Evm fork Nat → Prop :=
  fun _ msg child => SendsVia M ua c r d msg → (child.error = none ↔ A)

/-- A path that forwards one message, under a runner that may fail with any error (round 31): with
the hypotheses of `fwd_ok_iff_fails` but no `hfail`, a run that ends with no error meets `G` and
`A`, and when `G` and `A` hold, the run ends with no error or the runner fails on a message of
`S` sent from a caller frame meeting `Cl`. -/
theorem fwd_ok_or_fails {G A : Prop} {Q : Evm fork Nat → Evm fork Nat → Prop}
    {S : Message fork → Prop} {Cl : Evm fork Nat → Message fork → Prop}
    {P : Evm fork Nat → Prop}
    (hspec : G → SpecOn fork (fun caller msg child => S msg → Cl caller msg → Q caller child)
      (fun caller msg => S msg ∧ Cl caller msg) P (fun e => e.error = none))
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hcomp : ∀ s, Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within =
      .ok s → s.error = none → G ∧ ∃ caller msg lt child, runChild caller msg lt = .ok child ∧
        Q caller child.1 ∧ S msg ∧ Cl caller msg)
    (hans : ∀ caller msg lt child, runChild caller msg lt = .ok child → S msg → Cl caller msg →
      (Q caller child.1 ↔ A))
    (hp : P evm) :
    (RunsOk bound runChild evm within → G ∧ A) ∧
      (G ∧ A → RunsOk bound runChild evm within ∨
        ∃ caller msg lt e, runChild caller msg lt = .error e ∧ S msg ∧ Cl caller msg) := by
  constructor
  · rintro ⟨s, hs, hok⟩
    obtain ⟨hG, caller, msg, lt, child, hch, hq, hS, hC⟩ := hcomp s hs hok
    exact ⟨hG, (hans caller msg lt child hch hS hC).1 hq⟩
  · rintro ⟨hG, hA⟩
    obtain ⟨after, hreach, ⟨halted, hq⟩ | ⟨-, caller, msg, -, -, ⟨hS, hC⟩, lt, e, failed⟩⟩ :=
      hspec hG bound runChild
        (fun caller msg lt child hch hS hC => (hans caller msg lt child hch hS hC).2 hA)
        evm hp within
    · refine .inl ⟨after, ?_, hq⟩
      rw [runFrame_eq_of_reaches StepBy.gasHeld_le StepBy.runFrame_eq hreach within,
        runFrame_of_running_eq_false halted]
    · exact .inr ⟨caller, msg, lt, e, failed, hS, hC⟩

/-- A path that forwards one message, under a runner that may fail with any error: `RunsOk` holds
exactly when `G` and `A` hold, if `G` gives a specification to frames with no error that holds
under every runner whose frames for messages of `S` sent from a caller frame meeting `Cl` meet `Q`
(`Q` of the caller's frame and the ended frame) and that ends otherwise only at a failure of the
runner on a message of `S` sent from a caller frame meeting `Cl` (`SpecOn`); every run that ends with no error meets `G` and had a
message of `S`, sent from a caller frame meeting `Cl`, end in a frame meeting `Q`; the runner ends
each message of `S` sent from a caller frame meeting `Cl` in a frame meeting `Q` exactly when `A`
holds (`hans`); and a failure of the runner on a message of `S` from a caller frame meeting `Cl`
excludes `A` (`hfail`). -/
theorem fwd_ok_iff_fails {G A : Prop} {Q : Evm fork Nat → Evm fork Nat → Prop}
    {S : Message fork → Prop} {Cl : Evm fork Nat → Message fork → Prop}
    {P : Evm fork Nat → Prop}
    (hspec : G → SpecOn fork (fun caller msg child => S msg → Cl caller msg → Q caller child)
      (fun caller msg => S msg ∧ Cl caller msg) P (fun e => e.error = none))
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hcomp : ∀ s, Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within =
      .ok s → s.error = none → G ∧ ∃ caller msg lt child, runChild caller msg lt = .ok child ∧
        Q caller child.1 ∧ S msg ∧ Cl caller msg)
    (hans : ∀ caller msg lt child, runChild caller msg lt = .ok child → S msg → Cl caller msg →
      (Q caller child.1 ↔ A))
    (hfail : ∀ caller msg lt e, runChild caller msg lt = .error e → S msg → Cl caller msg → ¬ A)
    (hp : P evm) :
    RunsOk bound runChild evm within ↔ G ∧ A := by
  have h := fwd_ok_or_fails hspec within hcomp hans hp
  exact ⟨h.1, fun hGA => (h.2 hGA).resolve_right
    fun ⟨caller, msg, lt, e, failed, hS, hC⟩ => hfail caller msg lt e failed hS hC hGA.2⟩

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
