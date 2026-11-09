import UsdtVerify.Evm.GasRules
import EthLib.Base.Proofs.MapM

/-!
# Writes that cannot complete: static frames, no account, at most 2300 gas left

A frame is `Stuck` when it is running and its step, from it or from the same frame with any less
gas, fails: an error, or a halt with an error. A run that reaches such a frame along `StepG` (from
a start with more gas, as in `no_ok`) does not end with no error (`no_ok_stuck`): every frame
with less gas fails earlier or at that frame.

`sstore_stuck`: SSTORE in a static frame, or when the current target has no account in the
state, is `Stuck` (any fork, any gas): from Glamsterdam a static frame fails first; otherwise
the step either fails before the write (stack, the stipend, gas), halts after its reads
(`keepReads`), or reaches the write, which a static frame refuses and which `setStorage` refuses
without an account (an error of the state, which aborts the run).

This is how the completeness theorems of the writing functions (not deprecated) do without the hypotheses
`hstatic` (not static) and `hacc` (an account): on each writing path the run reaches its first
SSTORE, and with a static frame or no account it cannot end with no error.

Round 26:
- `sstore_low_stuck`: from Istanbul, SSTORE with at most 2300 gas left fails (EIP-2200), so it
  is `Stuck`.
- `NoWrite message state g`: a static frame, no account for the current target, or (from
  Istanbul) at most `g ≤ 2300` gas; `sstoreNoWrite`: an SSTORE where `NoWrite` holds is `Stuck`.
- `no_ok_stuck_at`: a run that reaches a `Stuck` frame along `StepG` from a start with its own gas
  does not end with no error (used for a gas below a stipend bound, where `no_ok_stuck`, which
  starts with more gas, does not apply).

Round 48: EthLib's Logic/LessGas.lean (#1615) has `Stuck`, `not_ok_of_reaches`, `no_ok_stuck`,
`At.stuck`, `sstore_stuck` and `sstore_low_stuck` over `Logic.StepG` and `Logic.At`. The local
`Stuck` is EthLib's `Stuck` with `SimAt` (Evm/Gas.lean), and the local forms take `Ends` (the
meter link uses them for a loop over `StateGasMeter`), so they stay. The SSTORE facts under them
are now EthLib's (`sstoreStep_halts`, `sstoreStep_of_isStatic`, `sstoreStep_of_gasLeft_le`), and
the local `sstoreStep_bad` and `sstoreStep_low` are removed. `At.stuck`: EthLib's `At.stuck` for
the local `At` and `Stuck`.
-/

namespace UsdtVerify.Gas

open EthLib
open EthLib.Base (Fork U256 Address)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic

variable {fork : Fork}

/-- A running frame at a `simulated` opcode from which the step fails, also with any less gas. -/
def Stuck (z : Evm fork Nat) : Prop :=
  z.running = true ∧ SimAt z ∧ ∀ k l, z = addGas k l → StepFails (step fork l)

section Loop

variable {bound : Nat} {runChild : MessageRunner fork Nat bound}

/-- Along a chain of `StepG` from `addGas k l` to a `Stuck` frame, no loop from `l` ends with no error
(`Ends`). -/
theorem not_ok_of_reachesE {hi z : Evm fork Nat} (hr : Reaches (StepG fork) hi z)
    (hz : Stuck z) :
    ∀ (k : Nat) (l : Evm fork Nat), hi = addGas k l → ∀ {s : Evm fork Nat}, Ends fork l s →
      s.error ≠ none := by
  induction hr with
  | refl =>
    rintro k l rfl s hend
    have hr : l.running = true := by simpa using hz.1
    have hsim : SimAt l := hz.2.1
    rcases hz.2.2 k l rfl with ⟨e, he⟩ | ⟨b, hb, hbr, hbe⟩
    · rw [(hend.error hr hsim he).2]
      simp [exceptionalHalt]
    · rw [(hend.next hr hsim hb).stopped hbr]
      exact hbe
  | step hs _ ih =>
    rintro k l rfl s hend
    obtain ⟨hstep, hsim, hmono⟩ := hs
    have hr : l.running = true := hstep.running
    rcases hmono k l rfl with (⟨e, he⟩ | ⟨b, hb, hbr, hbe⟩) | ⟨b, hb, hh⟩
    · rw [(hend.error hr hsim he).2]
      simp [exceptionalHalt]
    · rw [(hend.next hr hsim hb).stopped hbr]
      exact hbe
    · cases hstep with
      | next _ hn =>
        rw [hh] at hn
        cases hn
        exact ih hz k b rfl (hend.next hr hsim hb)
      | halt _ hn _ =>
        rw [hh] at hn
        cases hn

/-- Along a chain of `StepG` from `addGas k l` to a `Stuck` frame, the loop run from `l` does not end
with no error. -/
theorem not_ok_of_reaches {hi z : Evm fork Nat} (hr : Reaches (StepG fork) hi z)
    (hz : Stuck z) :
    ∀ (k : Nat) (l : Evm fork Nat), hi = addGas k l →
      ∀ (within : GasMeter.gasHeld l.gas ≤ bound) {s : Evm fork Nat},
        Evm.runFrame (step fork) (step_decreases fork) bound runChild l within = .ok s →
        s.error ≠ none :=
  fun k l h _ _ hrun => not_ok_of_reachesE hr hz k l h (Ends.run hrun)

variable {code : ByteArray} {message : Message fork} {pc : Nat} {stack : List U256}
  {memory : ByteArray} {state : State.TransactionState} {substate : Substate}
  {evm s : Evm fork Nat}

/-- No loop that ends with no error (`Ends`) from a frame where, with any gas from `B` on, the
frames reach a `Stuck` frame along `StepG`. -/
theorem no_ok_stuckE {B : Nat}
    (h : ∀ g, B ≤ g → HoareG fork (At code message pc stack memory g state substate) Stuck)
    {gas : Nat} (start : At code message pc stack memory gas state substate evm)
    (hrun : Ends fork evm s) (hok : s.error = none) : False := by
  obtain ⟨z, hr, hz⟩ := h (gas + B) (by omega) _ (at_addGas start B)
  exact not_ok_of_reachesE hr hz B evm rfl hrun hok

/-- No loop that ends with no error (`Ends`) from a frame that, with its own gas, reaches a
`Stuck` frame along `StepG`. -/
theorem no_ok_stuck_atE {gas : Nat}
    (h : HoareG fork (At code message pc stack memory gas state substate) Stuck)
    (start : At code message pc stack memory gas state substate evm)
    (hrun : Ends fork evm s) (hok : s.error = none) : False := by
  obtain ⟨z, hr, hz⟩ := h evm start
  exact not_ok_of_reachesE hr hz 0 evm (by simp [addGas]) hrun hok

/-- No successful run from a frame where, with any gas from `B` on, the frames reach a `Stuck`
frame along `StepG`. -/
theorem no_ok_stuck {B : Nat}
    (h : ∀ g, B ≤ g → HoareG fork (At code message pc stack memory g state substate) Stuck)
    {gas : Nat} (start : At code message pc stack memory gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) : False :=
  no_ok_stuckE h start (Ends.run hrun) hok

/-- No successful run from a frame that, with its own gas, reaches a `Stuck` frame along
`StepG`. -/
theorem no_ok_stuck_at {gas : Nat}
    (h : HoareG fork (At code message pc stack memory gas state substate) Stuck)
    (start : At code message pc stack memory gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) : False :=
  no_ok_stuck_atE h start (Ends.run hrun) hok

end Loop
/-- A frame of a code is `Stuck` at a `simulated` opcode whose instruction fails on every frame
with the message, the stack and the state of the rule and at most its gas: EthLib's `At.stuck`,
for `At` and this `Stuck` (with `SimAt`). -/
theorem At.stuck {byte : UInt8} {op : Op} {run : Evm fork Nat → Except EvmError (Evm fork Nat)}
    {gas : Nat} (hlt : pc < code.size) (hbyte : code[pc] = byte)
    (decoded : Op.ofByte fork byte = some op) (hrun : instruction fork op = some run)
    (fails : ∀ low : Evm fork Nat, low.message = message → low.stack.val = stack →
      low.state = state → low.gas ≤ gas → Fails (run low))
    (hsim : simulated op = true := by first | decide | rfl) :
    HoareG fork (At code message pc stack memory gas state substate) Stuck := by
  intro evm hat
  refine ⟨evm, .refl _, hat.2.2.2.2.2.2.2.1, ?_, ?_⟩
  · obtain ⟨hcode, -, -, hpc, -⟩ := hat
    subst hcode hpc
    exact simAt_of hlt (by rw [hbyte]; exact decoded) hrun hsim
  · obtain ⟨hcode, -, hm, hpc, hst, -, hg, -, -, -, hs, -⟩ := hat
    rintro k low rfl
    have hc : low.code = code := hcode
    have hp : low.pc = pc := hpc
    subst hc hp
    have hdec : Op.ofByte fork low.code[low.pc] = some op := by rw [hbyte]; exact decoded
    rw [step_of_instruction hlt hdec hrun]
    rcases fails low hm hst hs (by rw [← hg]; exact Nat.le_add_right _ _) with
      ⟨e, he⟩ | ⟨b, hb, hbr, hbe⟩
    · exact .inl ⟨e, by rw [he]; rfl⟩
    · exact .inr ⟨b, by rw [hb]; rfl, hbr, hbe⟩

/-- SSTORE in a static frame, or at an address with no account, is `Stuck`, at any fork and any
gas (EthLib's `sstore_stuck`, for `At` and this `Stuck`). -/
theorem sstore_stuck {key new : U256} {rest : List U256} {gas : Nat}
    (hlt : pc < code.size) (hbyte : code[pc] = 0x55)
    (hbad : message.isStatic = true ∨
      ¬(state.getAccountOptional message.currentTarget).isSome = true) :
    HoareG fork (At code message pc (key :: new :: rest) memory gas state substate) Stuck := by
  refine At.stuck hlt hbyte (ofByte_of_decode (op := .sstore) rfl (Fork.frontier_le _))
    instruction_sstore fun low hm _ hs _ => ?_
  rcases h : sstoreStep low with e | b
  · exact .inl ⟨e, rfl⟩
  · obtain ⟨hbr, hbe⟩ := sstoreStep_halts
      (by rw [hm, hs]; exact hbad.imp id Option.not_isSome_iff_eq_none.mp) h
    exact .inr ⟨b, rfl, hbr, by simpa [Option.isSome_iff_ne_none] using hbe⟩

/-- `sstore_stuck` with the account stated as `hasAccount`. -/
theorem sstoreStuckW {key new : U256} {rest : List U256} {gas : Nat}
    (hlt : pc < code.size) (hbyte : code[pc] = 0x55)
    (hbad : message.isStatic = true ∨ ¬hasAccount state message.currentTarget) :
    HoareG fork (At code message pc (key :: new :: rest) memory gas state substate) Stuck :=
  sstore_stuck hlt hbyte hbad
/-- SSTORE with at most 2300 gas left is `Stuck` from Istanbul on (EIP-2200): every frame with that
gas or less fails at it (EthLib's `sstore_low_stuck`, for `At` and this `Stuck`). -/
theorem sstore_low_stuck (hist : Fork.istanbul ≤ fork) {key new : U256} {rest : List U256}
    {gas : Nat} (hlt : pc < code.size) (hbyte : code[pc] = 0x55) (hlow : gas ≤ 2300) :
    HoareG fork (At code message pc (key :: new :: rest) memory gas state substate) Stuck := by
  have hstip : GasCosts.CALL_STIPEND = 2300 := rfl
  refine At.stuck hlt hbyte (ofByte_of_decode (op := .sstore) rfl (Fork.frontier_le _))
    instruction_sstore fun l _ hst _ hg => .inl ?_
  by_cases first : fork ≥ .glamsterdam ∧ l.message.isStatic = true
  · exact ⟨_, sstoreStep_of_isStatic first.1 first.2⟩
  · refine ⟨_, sstoreStep_of_gasLeft_le hist hst (by simp only [GasMeter.gasLeft]; omega) ?_⟩
    by_cases hg : fork ≥ .glamsterdam
    · exact .inr (by simpa [hg] using first)
    · exact .inl (Nat.lt_of_not_le hg)

/-- The SSTORE of a frame of `message` in `state` with `g` gas cannot complete: the frame is
static, the current target has no account, or (from Istanbul) at most 2300 gas is left. -/
def NoWrite (message : Message fork) (state : State.TransactionState) (g : Nat) : Prop :=
  message.isStatic = true ∨ ¬hasAccount state message.currentTarget ∨
    (Fork.istanbul ≤ fork ∧ g ≤ 2300)

theorem NoWrite.of_bad {message : Message fork} {state : State.TransactionState} {g : Nat}
    (h : message.isStatic = true ∨ ¬hasAccount state message.currentTarget) :
    NoWrite message state g :=
  h.elim .inl fun h => .inr (.inl h)

theorem NoWrite.of_low (hfork : .berlin ≤ fork) {message : Message fork}
    {state : State.TransactionState} {g : Nat} (h : g ≤ 2300) : NoWrite message state g :=
  .inr (.inr ⟨Nat.le_trans (by decide) hfork, h⟩)

theorem NoWrite.le {message : Message fork} {state : State.TransactionState} {g g' : Nat}
    (h : NoWrite message state g) (hle : g' ≤ g) : NoWrite message state g' :=
  h.elim .inl fun h => h.elim (fun h => .inr (.inl h)) fun h => .inr (.inr ⟨h.1, by omega⟩)

/-- An SSTORE that cannot complete (`NoWrite`) is `Stuck`. -/
theorem sstoreNoWrite {key new : U256} {rest : List U256} {gas : Nat}
    (hlt : pc < code.size) (hbyte : code[pc] = 0x55) (h : NoWrite message state gas) :
    HoareG fork (At code message pc (key :: new :: rest) memory gas state substate) Stuck := by
  rcases h with h | h | ⟨hist, h⟩
  · exact sstore_stuck hlt hbyte (.inl h)
  · exact sstore_stuck hlt hbyte (.inr h)
  · exact sstore_low_stuck hist hlt hbyte h

/-- Not (not static and `P`): static, or not `P`. -/
theorem bad_of_not {b : Bool} {P : Prop} (h : ¬(b = false ∧ P)) : b = true ∨ ¬P := by
  cases b <;> simp_all

end UsdtVerify.Gas
