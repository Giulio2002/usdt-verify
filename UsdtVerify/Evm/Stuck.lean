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
- `sstoreStep_low`, `sstore_low_stuck`: from Istanbul, SSTORE with at most 2300 gas left fails
  (EIP-2200), so it is `Stuck`.
- `NoWrite message state g`: a static frame, no account for the current target, or (from
  Istanbul) at most `g ≤ 2300` gas; `sstoreNoWrite`: an SSTORE where `NoWrite` holds is `Stuck`.
- `no_ok_stuck_at`: a run that reaches a `Stuck` frame along `StepG` from a start with its own gas
  does not end with no error (used for a gas below a stipend bound, where `no_ok_stuck`, which
  starts with more gas, does not apply).
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
  z.running = true ∧ SimAt z ∧ ∀ k l, z = sh k l →
    (∃ e, step fork l = .error e) ∨
      ∃ b, step fork l = .ok (.next b) ∧ b.running = false ∧ b.error ≠ none

section Loop

variable {bound : Nat} {runChild : MessageRunner fork Nat bound}

/-- Along a chain of `StepG` from `sh k l` to a `Stuck` frame, no loop from `l` ends with no error
(`Ends`). -/
theorem not_ok_of_reachesE {hi z : Evm fork Nat} (hr : Reaches (StepG fork) hi z)
    (hz : Stuck z) :
    ∀ (k : Nat) (l : Evm fork Nat), hi = sh k l → ∀ {s : Evm fork Nat}, Ends fork l s →
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
    rcases hmono k l rfl with ⟨e, he⟩ | ⟨b, hb, hbr, hbe⟩ | ⟨b, hb, hh⟩
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

/-- Along a chain of `StepG` from `sh k l` to a `Stuck` frame, the loop run from `l` does not end
with no error. -/
theorem not_ok_of_reaches {hi z : Evm fork Nat} (hr : Reaches (StepG fork) hi z)
    (hz : Stuck z) :
    ∀ (k : Nat) (l : Evm fork Nat), hi = sh k l →
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
  obtain ⟨z, hr, hz⟩ := h (gas + B) (by omega) _ (at_sh start B)
  exact not_ok_of_reachesE hr hz B evm rfl hrun hok

/-- No loop that ends with no error (`Ends`) from a frame that, with its own gas, reaches a
`Stuck` frame along `StepG`. -/
theorem no_ok_stuck_atE {gas : Nat}
    (h : HoareG fork (At code message pc stack memory gas state substate) Stuck)
    (start : At code message pc stack memory gas state substate evm)
    (hrun : Ends fork evm s) (hok : s.error = none) : False := by
  obtain ⟨z, hr, hz⟩ := h evm start
  exact not_ok_of_reachesE hr hz 0 evm (by simp [sh]) hrun hok

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

/-- SSTORE in a static frame, or at an address with no account, never completes: its step fails
or halts with an error. -/
theorem sstoreStep_bad {l b : Evm fork Nat}
    (hbad : l.message.isStatic = true ∨
      ¬(l.state.getAccountOptional l.message.currentTarget).isSome = true)
    (h : sstoreStep l = .ok b) : b.running = false ∧ b.error ≠ none := by
  unfold sstoreStep at h
  split at h
  · simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  obtain ⟨⟨k, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨n, e2⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  have c2 := (popWord_sameContext h1).trans (popWord_sameContext h2)
  simp only [] at h
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h
  · rcases hpair : accessStorageKey e2 e2.message.currentTarget (U256.toBeBytes k) with
      ⟨cold, e3⟩
    obtain ⟨keys, hacc⟩ := accessStorageKey_snd e2 e2.message.currentTarget (U256.toBeBytes k)
    rw [hpair] at hacc
    simp only [hpair] at h
    rcases keepReads_eq_ok h with h | ⟨e, rfl⟩
    · obtain ⟨e4, h4, h⟩ := Base.bind_ok_iff.mp h
      obtain ⟨e5, h5, h⟩ := Base.bind_ok_iff.mp h
      have c5 := (chargeGas_sameContext h4).trans (chargeStateGas_sameContext h5)
      have m5 : e5.message = l.message := by
        rw [c5.message]
        simp only [refillStateGas, recordStorageRead]
        cases hacc
        exact c2.message
      have s5 : e5.state = (l.state.recordStorageRead l.message.currentTarget
          (U256.toBeBytes k)) := by
        rw [c5.state]
        simp only [refillStateGas, recordStorageRead]
        cases hacc
        rw [c2.state, c2.message]
      split at h
      · simp [throw, throwThe, MonadExceptOf.throw] at h
      · rename_i hns
        obtain ⟨st, hst, h⟩ := Base.bind_ok_iff.mp h
        have hst := Base.mapError_ok_iff.mp hst
        rw [m5] at hns
        rw [s5, c2.message] at hst
        rcases hbad with hb | hb
        · rw [hb] at hns
          exact absurd rfl hns
        · unfold State.TransactionState.setStorage at hst
          split at hst
          · cases hst
          · rename_i hsome
            have : (l.state.getAccountOptional l.message.currentTarget).isSome = true := by
              simpa [State.TransactionState.recordStorageRead,
                State.TransactionState.getAccountOptional, Option.isSome_iff_ne_none] using hsome
            exact absurd this hb
    · exact ⟨rfl, by simp [exceptionalHalt]⟩

/-- SSTORE in a static frame, or at an address with no account, is `Stuck`, at any fork and any
gas. -/
theorem sstore_stuck {key new : U256} {rest : List U256} {gas : Nat}
    (hlt : pc < code.size) (hbyte : code[pc] = 0x55)
    (hbad : message.isStatic = true ∨
      ¬(state.getAccountOptional message.currentTarget).isSome = true) :
    HoareG fork (At code message pc (key :: new :: rest) memory gas state substate) Stuck := by
  intro evm hat
  obtain ⟨hcode, -, hm, hpc, -, -, -, hrun, -, -, hs, -⟩ := hat
  refine ⟨evm, .refl _, hrun, ?_, ?_⟩
  · have hlt' : evm.pc < evm.code.size := by rw [hpc, hcode]; exact hlt
    refine simAt_of hlt' ?_ instruction_sstore rfl
    have : evm.code[evm.pc] = (0x55 : UInt8) := by simp only [hcode, hpc, hbyte]
    rw [this]
    exact ofByte_of_decode (op := .sstore) rfl (Fork.frontier_le _)
  rintro k l rfl
  have hcode' : l.code = code := hcode
  have hpc' : l.pc = pc := hpc
  have hlt' : l.pc < l.code.size := by rw [hpc', hcode']; exact hlt
  have hdec : Op.ofByte fork l.code[l.pc] = some .sstore := by
    have : l.code[l.pc] = (0x55 : UInt8) := by simp only [hcode', hpc', hbyte]
    rw [this]
    exact ofByte_of_decode (op := .sstore) rfl (Fork.frontier_le _)
  rw [step_of_instruction hlt' hdec instruction_sstore]
  cases hst : sstoreStep l with
  | error e => exact .inl ⟨e, by simp [Functor.map, Except.map]⟩
  | ok b =>
    refine .inr ⟨b, by simp [Functor.map, Except.map], sstoreStep_bad ?_ hst⟩
    have hm' : l.message = message := hm
    have hs' : l.state = state := hs
    rw [hm', hs']
    exact hbad

/-- `sstore_stuck` with the account stated as `hasAccount`. -/
theorem sstoreStuckW {key new : U256} {rest : List U256} {gas : Nat}
    (hlt : pc < code.size) (hbyte : code[pc] = 0x55)
    (hbad : message.isStatic = true ∨ ¬hasAccount state message.currentTarget) :
    HoareG fork (At code message pc (key :: new :: rest) memory gas state substate) Stuck :=
  sstore_stuck hlt hbyte hbad

/-- SSTORE with at most 2300 gas left fails from Istanbul on (EIP-2200): its step is an error. -/
theorem sstoreStep_low (hist : Fork.istanbul ≤ fork) {l : Evm fork Nat} (hlow : l.gas ≤ 2300) :
    ∃ e, sstoreStep l = .error e := by
  cases h : sstoreStep l with
  | error e => exact ⟨e, rfl⟩
  | ok b =>
    exfalso
    unfold sstoreStep at h
    split at h
    · simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
    obtain ⟨⟨k, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨⟨n, e2⟩, h2, h⟩ := Base.bind_ok_iff.mp h
    have g1 : e1.gas = l.gas := by
      unfold popWord at h1
      obtain ⟨⟨_, _⟩, -, h1⟩ := Base.bind_ok_iff.mp h1
      cases h1; rfl
    have g2 : e2.gas = e1.gas := by
      unfold popWord at h2
      obtain ⟨⟨_, _⟩, -, h2⟩ := Base.bind_ok_iff.mp h2
      cases h2; rfl
    simp only [] at h
    split at h
    · simp [throw, throwThe, MonadExceptOf.throw] at h
    · rename_i hn
      exact hn ⟨hist, by rw [g2, g1]; exact hlow⟩

/-- SSTORE with at most 2300 gas left is `Stuck` from Istanbul on (EIP-2200): every frame with that
gas or less fails at it. -/
theorem sstore_low_stuck (hist : Fork.istanbul ≤ fork) {key new : U256} {rest : List U256}
    {gas : Nat} (hlt : pc < code.size) (hbyte : code[pc] = 0x55) (hlow : gas ≤ 2300) :
    HoareG fork (At code message pc (key :: new :: rest) memory gas state substate) Stuck := by
  intro evm hat
  obtain ⟨hcode, -, -, hpc, -, -, hg, hrun, -, -, -, -⟩ := hat
  refine ⟨evm, .refl _, hrun, ?_, ?_⟩
  · have hlt' : evm.pc < evm.code.size := by rw [hpc, hcode]; exact hlt
    refine simAt_of hlt' ?_ instruction_sstore rfl
    have : evm.code[evm.pc] = (0x55 : UInt8) := by simp only [hcode, hpc, hbyte]
    rw [this]
    exact ofByte_of_decode (op := .sstore) rfl (Fork.frontier_le _)
  rintro k l rfl
  have hcode' : l.code = code := hcode
  have hpc' : l.pc = pc := hpc
  have hlt' : l.pc < l.code.size := by rw [hpc', hcode']; exact hlt
  have hdec : Op.ofByte fork l.code[l.pc] = some .sstore := by
    have : l.code[l.pc] = (0x55 : UInt8) := by simp only [hcode', hpc', hbyte]
    rw [this]
    exact ofByte_of_decode (op := .sstore) rfl (Fork.frontier_le _)
  rw [step_of_instruction hlt' hdec instruction_sstore]
  have hl : l.gas ≤ 2300 := by
    have : l.gas + k = gas := hg
    omega
  obtain ⟨e, he⟩ := sstoreStep_low hist hl
  exact .inl ⟨e, by simp [he, Functor.map, Except.map]⟩

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
