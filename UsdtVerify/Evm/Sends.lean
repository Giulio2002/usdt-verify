import EthLib.Execution.Proofs.Evm.Logic.Message

/-!
# Triples whose runner may fail, with the failure on a named message

EthLib's `HoareUnder` asks the runner to fail only with errors that abort the run (`Meets`), and
its triples allow the run to end at a frame whose runner fails on ANY message it sends
(`AbortsBy`). The forms here (round 26) take no assumption on the errors of the runner, and say on
which messages it may fail:

- `AbortsOn S`: the frame sends a message of `S`, and the runner fails on it (with any error).
  Round 31: `S` is a condition on the caller frame of the step and the message (docs/AUDIT.md,
  second audit, M1), so a failure is known to come from that caller frame.
- `MeetsOk callee runChild`: each frame that the runner gives meets `callee` (the `ok` part of
  `Meets`).
- `HoareOn fork callee S P Q`: under every runner that meets `callee` in that sense, every frame of
  `P` reaches a frame of `Q`, or a frame whose runner fails on a message of `S`.
  `SpecOn`: the same to a stopped frame.
- `HoareOn.of_hoare` (no message), `HoareOn.of_child` (a step that sends a message of `S`, as
  EthLib's `HoareUnder.of_child`), `seq`, `consequence`, `mono_S`.
- `HoareOn.toUnder`, `SpecOn.toUnder`: such a triple is a triple of EthLib under the same callee
  assumption.
-/

namespace UsdtVerify.Sends

open EthLib.Base (Fork)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic

variable {fork : Fork}

/-- The frame sends a message of `S` (a condition on the caller frame and the message), and the
runner fails on it (with any error). -/
def AbortsOn (S : Evm fork Nat → Message fork → Prop) (bound : Nat) (runChild : MessageRunner fork Nat bound)
    (evm : Evm fork Nat) : Prop :=
  evm.running = true ∧ ∃ caller message resume,
    step fork evm = .ok (.child caller message resume) ∧ S caller message ∧
      ∃ lt e, runChild caller message lt = .error e

/-- Each frame that the runner gives meets the assumption (the runner may fail, with any
error). -/
def MeetsOk {bound : Nat} (callee : Evm fork Nat → Message fork → Evm fork Nat → Prop)
    (runChild : MessageRunner fork Nat bound) : Prop :=
  ∀ caller message lt child, runChild caller message lt = .ok child →
    callee caller message child.1

/-- Under every runner whose frames meet `callee`, every frame of `P` reaches a frame of `Q`, or
a frame whose runner fails on a message of `S`, for every bound on the gas of messages at least
the gas of the frame. -/
def HoareOn (fork : Fork) (callee : Evm fork Nat → Message fork → Evm fork Nat → Prop)
    (S : Evm fork Nat → Message fork → Prop) (P Q : Evm fork Nat → Prop) : Prop :=
  ∀ bound (runChild : MessageRunner fork Nat bound), MeetsOk callee runChild →
    ∀ evm, P evm → GasMeter.gasHeld evm.gas ≤ bound →
      ∃ after, Reaches (StepBy fork bound runChild) evm after ∧
        (Q after ∨ AbortsOn S bound runChild after)

/-- `HoareOn` to a stopped frame. -/
def SpecOn (fork : Fork) (callee : Evm fork Nat → Message fork → Evm fork Nat → Prop)
    (S : Evm fork Nat → Message fork → Prop) (P Q : Evm fork Nat → Prop) : Prop :=
  HoareOn fork callee S P fun evm => evm.running = false ∧ Q evm

variable {callee : Evm fork Nat → Message fork → Evm fork Nat → Prop}
  {S : Evm fork Nat → Message fork → Prop}

namespace HoareOn

/-- A triple with no message. -/
theorem of_hoare {P Q : Evm fork Nat → Prop} (h : Hoare fork P Q) : HoareOn fork callee S P Q :=
  fun _ _ _ evm hp _ =>
    let ⟨after, hreach, hq⟩ := h evm hp
    ⟨after, hreach.mono fun hs => .step hs, .inl hq⟩

/-- A step that sends a message of `S`, to a frame of `Q` from every frame that ends it (as
EthLib's `HoareUnder.of_child`). -/
theorem of_child {P Q : Evm fork Nat → Prop}
    (h : ∀ evm, P evm → evm.running = true ∧ ∃ caller message resume,
      step fork evm = .ok (.child caller message resume) ∧ S caller message ∧
      ∀ child, GasMeter.gasHeld child.gas ≤ message.gas → callee caller message child →
        (∃ after, resume child = .ok after ∧ Q after) ∨
          ∃ e, resume child = .error e ∧ e.aborts = false ∧ Q (exceptionalHalt evm e)) :
    HoareOn fork callee S P Q := by
  intro bound runChild meets evm hp within
  obtain ⟨running, caller, message, resume, sent, hS, hresume⟩ := h evm hp
  have lt : message.gas < bound := by
    have := (step_decreases fork running sent).1
    omega
  cases ran : runChild caller message lt with
  | error e => exact ⟨evm, .refl evm, .inr ⟨running, caller, message, resume, sent, hS, lt, e, ran⟩⟩
  | ok child =>
    rcases hresume child.1 child.2 (meets caller message lt child ran) with
      ⟨after, resumed, hq⟩ | ⟨e, failed, halts, hq⟩
    · exact ⟨after, .single (.child running sent lt ran resumed), .inl hq⟩
    · exact ⟨_, .single (.childHalt running sent lt ran failed halts), .inl hq⟩

/-- Sequence. -/
theorem seq {P Q R : Evm fork Nat → Prop} (first : HoareOn fork callee S P Q)
    (second : HoareOn fork callee S Q R) : HoareOn fork callee S P R := by
  intro bound runChild meets evm hp within
  obtain ⟨mid, h1, hq | ha⟩ := first bound runChild meets evm hp within
  · obtain ⟨after, h2, hr⟩ := second bound runChild meets mid hq
      (Nat.le_trans (h1.gasHeld_le StepBy.gasHeld_le) within)
    exact ⟨after, h1.trans h2, hr⟩
  · exact ⟨mid, h1, .inr ha⟩

/-- Consequence. -/
theorem consequence {P P' Q Q' : Evm fork Nat → Prop} (h : HoareOn fork callee S P Q)
    (pre : ∀ evm, P' evm → P evm) (post : ∀ evm, Q evm → Q' evm) :
    HoareOn fork callee S P' Q' := fun bound runChild meets evm hp within =>
  let ⟨after, hr, hq⟩ := h bound runChild meets evm (pre evm hp) within
  ⟨after, hr, hq.imp_left (post after)⟩

/-- A larger set of messages. -/
theorem mono_S {S' : Evm fork Nat → Message fork → Prop} {P Q : Evm fork Nat → Prop}
    (h : HoareOn fork callee S P Q) (hS : ∀ c m, S c m → S' c m) : HoareOn fork callee S' P Q :=
  fun bound runChild meets evm hp within =>
    let ⟨after, hr, hq⟩ := h bound runChild meets evm hp within
    ⟨after, hr, hq.imp_right fun ⟨r, c, m, res, s, hm, rest⟩ => ⟨r, c, m, res, s, hS c m hm, rest⟩⟩

/-- A triple of EthLib under the same callee assumption. -/
theorem toUnder {P Q : Evm fork Nat → Prop} (h : HoareOn fork callee S P Q) :
    HoareUnder fork callee P Q := fun bound runChild meets evm hp within =>
  let ⟨after, hr, hq⟩ := h bound runChild meets.ok evm hp within
  ⟨after, hr, hq.imp_right fun ⟨r, c, m, res, s, _, lt, e, f⟩ => ⟨r, c, m, res, s, lt, e, f⟩⟩

end HoareOn

namespace SpecOn

/-- A triple to a frame from which the specification holds. -/
theorem seq {P Q R : Evm fork Nat → Prop} (first : HoareOn fork callee S P Q)
    (second : SpecOn fork callee S Q R) : SpecOn fork callee S P R := HoareOn.seq first second

/-- Consequence for a specification. -/
theorem consequence {P P' Q Q' : Evm fork Nat → Prop} (h : SpecOn fork callee S P Q)
    (pre : ∀ evm, P' evm → P evm) (post : ∀ evm, Q evm → Q' evm) : SpecOn fork callee S P' Q' :=
  HoareOn.consequence h pre fun evm ⟨hs, hq⟩ => ⟨hs, post evm hq⟩

/-- A specification of EthLib under the same callee assumption. -/
theorem toUnder {P Q : Evm fork Nat → Prop} (h : SpecOn fork callee S P Q) :
    SpecUnder fork callee P Q := HoareOn.toUnder h

end SpecOn

end UsdtVerify.Sends
