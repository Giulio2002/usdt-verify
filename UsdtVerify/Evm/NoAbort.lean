import UsdtVerify.Evm.GasRules

/-!
# GENERIC: runs that never abort, at any gas

The loop of the interpreter (`runFrame`) returns an error only for an error that aborts the whole
run (`EvmError.aborts`: an error of the state, an opcode with no instruction, ...), or when the
runner of messages returns one. A run that halts with out of gas is a frame with an error, not
an error of the loop. The triples over `StepG` (Evm/Gas.lean) say how a run with more gas ends,
and with less gas the step may fail with any error. Here the failures with less gas are shown
to halt the frame.

- `NoAbort r`: the result `r` is no error that aborts.
- `noAbort_pushN`, `noAbort_mstore`, `noAbort_calldataload`, `noAbort_keccak256`,
  `noAbort_sload`, `noAbort_return`: these instructions fail, on any frame, only with errors that
  halt the frame (stack, gas).
- `StepGA`: a step of `StepG` from a frame `x` such that the step from every frame with less gas
  than `x` is no error that aborts. `HoareGA`, `SpecGA`: triples over it; they imply the triples
  over `StepG` (`SpecGA.toG`).
- `At.ruleGA`: the rule of one opcode over `StepGA`, for an instruction that is `RunMono` and
  fails only with errors that halt. `pushGA`, `calldataloadGA`, `mstoreGA`, `keccak256GA`,
  `sloadGA`, `returnGA`: the rules of Evm/GasRules.lean over `StepGA`.
- `no_error_ga`: if, with every gas from a bound `B` on, a `SpecGA` holds from a frame, then the
  loop run from that frame with ANY gas (also below `B`) returns a frame, never an error.
-/

namespace UsdtVerify.Gas

open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts

variable {fork : Fork}

/-! ## Results that do not abort -/

/-- The result `r` is no error that aborts the run. -/
def NoAbort {α : Type} (r : Except EvmError α) : Prop := ∀ e, r = .error e → e.aborts = false

theorem NoAbort.ok {α : Type} (a : α) : NoAbort (.ok a : Except EvmError α) :=
  fun _ h => by cases h

theorem NoAbort.bind {α β : Type} {x : Except EvmError α} {f : α → Except EvmError β}
    (hx : NoAbort x) (hf : ∀ a, NoAbort (f a)) : NoAbort (x >>= f) := by
  intro e h
  cases hx' : x with
  | error e' =>
    have hb : (x >>= f) = .error e' := by rw [hx']; rfl
    rw [hb] at h
    cases h
    exact hx _ hx'
  | ok a =>
    have hb : (x >>= f) = f a := by rw [hx']; rfl
    rw [hb] at h
    exact hf a e h

theorem NoAbort.map {α β : Type} {x : Except EvmError α} (f : α → β) (hx : NoAbort x) :
    NoAbort (f <$> x) := by
  intro e h
  cases hx' : x with
  | error e' =>
    rw [hx'] at h
    simp only [Functor.map, Except.map, Except.error.injEq] at h
    subst h
    exact hx _ hx'
  | ok a =>
    rw [hx'] at h
    simp [Functor.map, Except.map] at h

theorem noAbort_popWord (evm : Evm fork Nat) : NoAbort (popWord evm) := by
  rintro e h
  rcases hs : evm.stack with ⟨_ | ⟨x, rest⟩, hp⟩ <;>
    simp [popWord, Stack.pop, hs, bind, Except.bind, pure, Except.pure] at h
  subst h; rfl

theorem noAbort_pushWord (evm : Evm fork Nat) (x : U256) : NoAbort (pushWord evm x) := by
  rintro e h
  simp only [pushWord, Stack.push, bind, Except.bind] at h
  split at h
  · rename_i heq
    cases h
    split at heq
    · cases heq; rfl
    · cases heq
  · cases h

theorem noAbort_chargeGas (evm : Evm fork Nat) (c : Nat) : NoAbort (chargeGas evm c) := by
  rintro e h
  simp only [chargeGas, GasMeter.charge, bind, Except.bind] at h
  split at h
  · rename_i heq
    cases h
    split at heq
    · cases heq; rfl
    · cases heq
  · cases h

theorem noAbort_chargeGasAndMemory (evm : Evm fork Nat) (c : Nat) (ranges : List (U256 × U256)) :
    NoAbort (chargeGasAndMemory evm c ranges) :=
  NoAbort.bind (noAbort_chargeGas _ _) fun _ => NoAbort.ok _

theorem noAbort_pushN (n : Fin 33) (evm : Evm fork Nat) : NoAbort (pushN n evm) :=
  NoAbort.bind (noAbort_chargeGas _ _) fun _ =>
    NoAbort.bind (noAbort_pushWord _ _) fun _ => NoAbort.ok _

theorem noAbort_mstore (evm : Evm fork Nat) : NoAbort (mstoreStep evm) :=
  NoAbort.bind (noAbort_popWord _) fun _ =>
    NoAbort.bind (noAbort_popWord _) fun _ =>
      NoAbort.bind (noAbort_chargeGasAndMemory _ _ _) fun _ => NoAbort.ok _

theorem noAbort_calldataload (evm : Evm fork Nat) : NoAbort (calldataloadStep evm) :=
  NoAbort.bind (noAbort_popWord _) fun _ =>
    NoAbort.bind (noAbort_chargeGas _ _) fun _ =>
      NoAbort.bind (noAbort_pushWord _ _) fun _ => NoAbort.ok _

theorem noAbort_keccak256 (evm : Evm fork Nat) : NoAbort (keccak256Step evm) :=
  NoAbort.bind (noAbort_popWord _) fun _ =>
    NoAbort.bind (noAbort_popWord _) fun _ =>
      NoAbort.bind (noAbort_chargeGasAndMemory _ _ _) fun _ =>
        NoAbort.bind (noAbort_pushWord _ _) fun _ => NoAbort.ok _

theorem noAbort_sload (evm : Evm fork Nat) : NoAbort (sloadStep evm) :=
  NoAbort.bind (noAbort_popWord _) fun _ =>
    NoAbort.bind (noAbort_chargeGas _ _) fun _ =>
      NoAbort.bind (noAbort_pushWord _ _) fun _ => NoAbort.ok _

theorem noAbort_return (evm : Evm fork Nat) : NoAbort (returnStep evm) :=
  NoAbort.bind (noAbort_popWord _) fun _ =>
    NoAbort.bind (noAbort_popWord _) fun _ =>
      NoAbort.bind (noAbort_chargeGasAndMemory _ _ _) fun _ => NoAbort.ok _

/-! ## Steps that do not abort with less gas -/

/-- From every frame with less gas than `x`, the step is no error that aborts. -/
def NoAbortLow (x : Evm fork Nat) : Prop := ∀ k l, x = sh k l → NoAbort (step fork l)

/-- A step of `StepG` from a frame `x` such that the step from every frame with less gas than `x`
is no error that aborts. -/
def StepGA (fork : Fork) (x y : Evm fork Nat) : Prop := StepG fork x y ∧ NoAbortLow x

/-- A triple over `StepGA`. -/
abbrev HoareGA (fork : Fork) (P Q : Evm fork Nat → Prop) : Prop := Triple (StepGA fork) P Q

/-- A specification over `StepGA`. -/
def SpecGA (fork : Fork) (P Q : Evm fork Nat → Prop) : Prop :=
  HoareGA fork P fun evm => evm.running = false ∧ Q evm

instance StepLift.stepGA : StepLift (StepGA fork) (StepG fork) := ⟨And.left⟩

/-- A specification over `StepGA` is one over `StepG`. -/
theorem SpecGA.toG {P Q : Evm fork Nat → Prop} (h : SpecGA fork P Q) : SpecG fork P Q :=
  Triple.lift h

theorem SpecGA.consequence {P P' Q Q' : Evm fork Nat → Prop} (h : SpecGA fork P Q)
    (pre : ∀ evm, P' evm → P evm) (post : ∀ evm, Q evm → Q' evm) : SpecGA fork P' Q' :=
  Triple.consequence h pre fun evm ⟨hs, hq⟩ => ⟨hs, post evm hq⟩

/-- The rule of one opcode over `StepGA`: `At.ruleG`, for an instruction that also fails, on any
frame, only with errors that halt the frame. -/
theorem At.ruleGA {code : ByteArray} {message : Message fork} {pc : Nat} {stack : List U256}
    {memory : ByteArray} {gas : Nat} {state : State.TransactionState} {substate : Substate}
    {byte : UInt8} {op : Op}
    {run : Evm fork Nat → Except EvmError (Evm fork Nat)} {post : Evm fork Nat → Prop}
    (hlt : pc < code.size) (hbyte : code[pc] = byte) (decoded : Op.ofByte fork byte = some op)
    (hrun : instruction fork op = some run) (hm : RunMono run) (hna : ∀ a, NoAbort (run a))
    (h : ∀ evm, At code message pc stack memory gas state substate evm →
      ∃ after, run evm = .ok after ∧ post after) (hsim : simulated op = true := by first | decide | rfl) :
    HoareGA fork (At code message pc stack memory gas state substate) post := by
  apply Triple.of_step
  intro evm hp
  obtain ⟨after, ok, hpost⟩ := h evm hp
  refine ⟨after, ⟨⟨Step.of_code hp.2.2.2.2.2.2.2.1 hp.1 hp.2.2.2.1 hlt hbyte decoded hrun ok, ?_⟩,
    ?_⟩, hpost⟩
  · obtain ⟨hcode, -, -, hpc, -⟩ := hp
    subst hcode hpc
    exact gasMono_of_run hlt (by rw [hbyte]; exact decoded) hrun hm hsim
  · obtain ⟨hcode, -, -, hpc, -⟩ := hp
    rintro k l rfl
    change l.code = code at hcode
    change l.pc = pc at hpc
    subst hcode hpc
    rw [step_of_instruction hlt (by rw [hbyte]; exact decoded) hrun]
    exact NoAbort.map _ (hna l)

/-! ## The loop never returns an error -/

section Loop

variable {bound : Nat} {runChild : MessageRunner fork Nat bound}

/-- Along a chain of `StepGA` from `sh k l` to a stopped frame, the loop run from `l` returns a
frame, never an error: with less gas, each step halts the frame, or follows the chain. -/
theorem no_error_of_reaches {hi z : Evm fork Nat} (hr : Reaches (StepGA fork) hi z)
    (hz : z.running = false) :
    ∀ (k : Nat) (l : Evm fork Nat), hi = sh k l →
      ∀ (within : GasMeter.gasHeld l.gas ≤ bound) (e : EvmError),
        Evm.runFrame (step fork) (step_decreases fork) bound runChild l within ≠ .error e := by
  induction hr with
  | refl =>
    rintro k l rfl within e h
    rw [runFrame_stopped (by simpa using hz)] at h
    cases h
  | step hs _ ih =>
    rintro k l rfl within e h
    obtain ⟨⟨hstep, -, hmono⟩, hna⟩ := hs
    have hr : l.running = true := hstep.running
    rcases hmono k l rfl with ⟨e', he⟩ | ⟨b, hb, hbr, -⟩ | ⟨b, hb, hh⟩
    · rw [runFrame_of_step_eq_error hr he (hna k l rfl e' he)] at h
      cases h
    · rw [runFrame_of_step_eq_next hr hb, runFrame_stopped hbr] at h
      cases h
    · rw [runFrame_of_step_eq_next hr hb] at h
      cases hstep with
      | next _ hn =>
        rw [hh] at hn
        cases hn
        exact ih hz k b rfl _ e h
      | halt _ hn _ =>
        rw [hh] at hn
        cases hn

/-- If, with every gas from `B` on, a `SpecGA` holds from a frame, then the loop run from that
frame with any gas returns a frame, never an error. -/
theorem no_error_ga {code : ByteArray} {message : Message fork} {pc : Nat} {stack : List U256}
    {memory : ByteArray} {state : State.TransactionState} {substate : Substate} {B : Nat}
    {Q : Nat → Evm fork Nat → Prop}
    (h : ∀ g, B ≤ g → SpecGA fork (At code message pc stack memory g state substate) (Q g))
    {gas : Nat} {evm : Evm fork Nat} (start : At code message pc stack memory gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) (e : EvmError) :
    Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within ≠ .error e := by
  obtain ⟨z, hr, hz, -⟩ := h (gas + B) (by omega) _ (at_sh start B)
  exact no_error_of_reaches hr hz B evm rfl within e

end Loop

/-! ## Rules over `StepGA` -/

variable {code : ByteArray} {message : Message fork} {pc : Nat} {stack : List U256}
  {memory : ByteArray} {gas : Nat} {state : State.TransactionState} {substate : Substate}

/-- `pushG` over `StepGA`. -/
theorem pushGA {n : Fin 33} {word : U256} (hn : n.val ≠ 0) (hlt : pc < code.size)
    (hbyte : code[pc] = 0x5f + UInt8.ofNat n.val)
    (decoded : Op.decode (0x5f + UInt8.ofNat n.val) = some (.push n))
    (hword : pushData code pc n = word) (hgas : 3 ≤ gas) (hstack : stack.length < STACK_LIMIT) :
    HoareGA fork (At code message pc stack memory gas state substate)
      (At code message (pc + (1 + n)) (word :: stack) memory (gas - 3) state substate) := by
  have hn' : n ≠ 0 := fun h => hn (by simp [h])
  apply At.ruleGA hlt hbyte
    (ofByte_of_decode decoded (by simp [Op.since, hn', Fork.frontier_le])) (instruction_push n)
    (runMono_pushN n) (noAbort_pushN n)
  rintro evm ⟨hcode, hj, hm, hpc, hst, hmem, hg, hrun, herr, hout, hs, hss⟩
  have hlen : evm.stack.val.length < STACK_LIMIT := by rw [hst]; exact hstack
  rw [pushN_nat hn (by rw [hg]; exact hgas) hlen]
  refine ⟨_, rfl, hcode, hj, hm, by simp [hpc], by simp [hst, hcode, hpc, hword], hmem,
    by simp [hg, OPCODE_PUSH, VERY_LOW], hrun, herr, hout, hs, hss⟩

/-- `calldataloadG` over `StepGA`. -/
theorem calldataloadGA {start : U256} {rest : List U256} (hlt : pc < code.size)
    (hbyte : code[pc] = 0x35) (hgas : 3 ≤ gas) :
    HoareGA fork (At code message pc (start :: rest) memory gas state substate)
      (At code message (pc + 1) (loadWord message.data start.toNat 32 :: rest) memory
        (gas - 3) state substate) := by
  apply At.ruleGA hlt hbyte (ofByte_of_decode (op := .calldataload) rfl (Fork.frontier_le _))
    instruction_calldataload runMono_calldataload noAbort_calldataload
  rintro evm ⟨hcode, hj, hm, hpc, hst, hmem, hg, hrun, herr, hout, hs, hss⟩
  rw [calldataloadStep_cons hst, charge_nat (by rw [hg]; exact hgas)]
  exact ⟨_, rfl, hcode, hj, hm, by simp [hpc], by simp [hm], hmem,
    by simp [hg, OPCODE_CALLDATALOAD, VERY_LOW], hrun, herr, hout, hs, hss⟩

/-- `mstoreG` over `StepGA`. -/
theorem mstoreGA {start value : U256} {rest : List U256} (hlt : pc < code.size)
    (hbyte : code[pc] = 0x52)
    (hgas : 3 + (extendMemory memory.size [(start, 32)]).cost ≤ gas) :
    HoareGA fork (At code message pc (start :: value :: rest) memory gas state substate)
      (At code message (pc + 1) rest
        (memoryWrite (memoryExtend memory (extendMemory memory.size [(start, 32)]).expandBy)
          start.toNat (wordBytes value))
        (gas - (3 + (extendMemory memory.size [(start, 32)]).cost)) state substate) := by
  apply At.ruleGA hlt hbyte (ofByte_of_decode (op := .mstore) rfl (Fork.frontier_le _))
    instruction_mstore runMono_mstore noAbort_mstore
  rintro evm ⟨hcode, hj, hm, hpc, hst, hmem, hg, hrun, herr, hout, hs, hss⟩
  subst hmem hg
  have hcost : OPCODE_MSTORE_BASE = 3 := rfl
  rw [mstoreStep_cons hst]
  dsimp only
  rw [hcost, charge_nat hgas]
  refine ⟨_, rfl, hcode, hj, hm, by simp [hpc], ?_, ?_, ?_, hrun, herr, hout, hs, hss⟩
  · show rest = rest
    rfl
  · simp
  · simp

/-- `keccak256G` over `StepGA`. -/
theorem keccak256GA {start size : U256} {rest : List U256} (hlt : pc < code.size)
    (hbyte : code[pc] = 0x20)
    (hgas :
      keccak256Cost size + (extendMemory memory.size [(start, size)]).cost ≤ gas) :
    HoareGA fork (At code message pc (start :: size :: rest) memory gas state substate)
      (At code message (pc + 1)
        (keccak (memoryReadBytes
          (memoryExtend memory (extendMemory memory.size [(start, size)]).expandBy)
          start.toNat size.toNat) :: rest)
        (memoryExtend memory (extendMemory memory.size [(start, size)]).expandBy)
        (gas - (keccak256Cost size + (extendMemory memory.size [(start, size)]).cost))
        state substate) := by
  apply At.ruleGA hlt hbyte (ofByte_of_decode (op := .keccak256) rfl (Fork.frontier_le _))
    instruction_keccak256 runMono_keccak256 noAbort_keccak256
  rintro evm ⟨hcode, hj, hm, hpc, hst, hmem, hg, hrun, herr, hout, hs, hss⟩
  subst hmem hg
  rw [keccak256Step_cons hst]
  dsimp only
  rw [charge_nat hgas]
  exact ⟨_, rfl, hcode, hj, hm, by simp [hpc], rfl, rfl, rfl, hrun, herr, hout, hs, hss⟩

/-- `sloadG` over `StepGA`. -/
theorem sloadGA (hfork : .berlin ≤ fork) {key : U256} {rest : List U256} {cold : Bool}
    (hlt : pc < code.size) (hbyte : code[pc] = 0x54)
    (hcold : decide (U256.toBeBytes key ∉
      substate.accessedStorageKeys.getD message.currentTarget ∅) = cold)
    (hgas : (if cold then 2100 else 100) ≤ gas) :
    HoareGA fork (At code message pc (key :: rest) memory gas state substate)
      (At code message (pc + 1)
        (state.getStorage message.currentTarget (U256.toBeBytes key) :: rest) memory
        (gas - if cold then 2100 else 100)
        (state.recordStorageRead message.currentTarget (U256.toBeBytes key))
        { substate with
          accessedStorageKeys := (substate.accessedStorageKeys.insert message.currentTarget
            ((substate.accessedStorageKeys.getD message.currentTarget ∅).insert
              (U256.toBeBytes key))) }) := by
  apply At.ruleGA hlt hbyte (ofByte_of_decode (op := .sload) rfl (Fork.frontier_le _))
    instruction_sload runMono_sload noAbort_sload
  rintro evm ⟨hcode, hj, hm, hpc, hst, hmem, hg, hrun, herr, hout, hs, hss⟩
  subst hm hg hs hss
  rw [sloadStep_cons hst]
  simp only [accessStorageKey, hfork, ↓reduceIte, hcold, sloadCost_of_berlin hfork]
  rw [charge_nat hgas]
  refine ⟨_, rfl, hcode, hj, rfl, by simp [hpc], ?_, hmem, ?_, hrun, herr, hout, rfl, rfl⟩
  · show _ :: rest = _ :: rest
    rfl
  · simp

/-- `returnG` over `StepGA`. -/
theorem returnGA {start size : U256} {rest : List U256} (hlt : pc < code.size)
    (hbyte : code[pc] = 0xf3) (hgas : (extendMemory memory.size [(start, size)]).cost ≤ gas) :
    SpecGA fork (At code message pc (start :: size :: rest) memory gas state substate)
      (Halted false
        (memoryReadBytes (memoryExtend memory (extendMemory memory.size [(start, size)]).expandBy)
          start.toNat size.toNat)
        (gas - (extendMemory memory.size [(start, size)]).cost) state substate) := by
  apply At.ruleGA hlt hbyte (ofByte_of_decode (op := .«return») rfl (Fork.frontier_le _))
    instruction_return runMono_return noAbort_return
  rintro evm ⟨hcode, hj, hm, hpc, hst, hmem, hg, hrun, herr, hout, hs, hss⟩
  subst hmem hg
  rw [returnStep_cons hst]
  dsimp only
  rw [charge_nat hgas]
  exact ⟨_, rfl, rfl, rfl, herr, rfl, by simp, hs, hss⟩

end UsdtVerify.Gas
