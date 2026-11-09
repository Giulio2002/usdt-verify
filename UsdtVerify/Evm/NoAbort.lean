import UsdtVerify.Evm.GasRules
import EthLib.Execution.Proofs.Evm.Logic.NoAbort

/-!
# GENERIC: runs that never abort, at any gas

The loop of the interpreter (`runFrame`) returns an error only for an error that aborts the whole
run (`EvmError.aborts`: an error of the state, an opcode with no instruction, ...), or when the
runner of messages returns one. A run that halts with out of gas is a frame with an error, not
an error of the loop. The triples over `StepG` (Evm/Gas.lean) say how a run with more gas ends,
and with less gas the step may fail with any error. Here the failures with less gas are shown
to halt the frame.

EthLib's Logic/NoAbort.lean (#1616) gives `NoAbort r` (the result `r` is no error that aborts),
the facts `noAbort_pushN`, `noAbort_mstore`, ... (these instructions fail, on any frame, only
with errors that halt the frame) and `NoAbortLow x` (from every frame with less gas than `x`, the
step is no error that aborts). Round 48: the local copies of these are removed.

- `StepGA`: a step of `StepG` (Evm/Gas.lean: EthLib's `Logic.StepG` with `SimAt`) from a frame
  that is `NoAbortLow`. This is EthLib's `Logic.StepGA` with `SimAt`. `HoareGA`, `SpecGA`:
  triples over it; they imply the triples over `StepG` (`SpecGA.toG`) and EthLib's `SpecGA`
  (`SpecGA.toLogic`).
- `At.ruleGA`: the rule of one opcode over `StepGA`, for an instruction that is `RunMono` and
  fails only with errors that halt. `pushGA`, `calldataloadGA`, `mstoreGA`, `keccak256GA`,
  `sloadGA`, `returnGA`: the rules of Evm/GasRules.lean over `StepGA`.
- `no_error_of_reaches`: EthLib's `no_error_of_reaches`, for `StepGA`.
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
/-! ## Steps that do not abort with less gas -/
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

/-- A specification over `StepGA` is one over EthLib's `Logic.StepGA`. -/
theorem SpecGA.toLogic {P Q : Evm fork Nat → Prop} (h : SpecGA fork P Q) :
    Logic.SpecGA fork P Q :=
  fun evm hp =>
    let ⟨after, hr, hq⟩ := h evm hp
    ⟨after, hr.mono fun hs => ⟨⟨hs.1.1, hs.1.2.2⟩, hs.2⟩, hq⟩

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
    have hdec : Op.ofByte fork evm.code[evm.pc] = some op := by rw [hbyte]; exact decoded
    exact ⟨simAt_of hlt hdec hrun hsim, Logic.gasMono_of_run hlt hdec hrun hm⟩
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

/-- Along a chain of `StepGA` from `addGas k l` to a stopped frame, the loop run from `l`
returns a frame, never an error: EthLib's `no_error_of_reaches`, for `StepGA`. -/
theorem no_error_of_reaches {hi z : Evm fork Nat} (hr : Reaches (StepGA fork) hi z)
    (hz : z.running = false) :
    ∀ (k : Nat) (l : Evm fork Nat), hi = addGas k l →
      ∀ (within : GasMeter.gasHeld l.gas ≤ bound) (e : EvmError),
        Evm.runFrame (step fork) (step_decreases fork) bound runChild l within ≠ .error e :=
  Logic.no_error_of_reaches (hr.mono fun hs => ⟨⟨hs.1.1, hs.1.2.2⟩, hs.2⟩) hz

/-- If, with every gas from `B` on, a `SpecGA` holds from a frame, then the loop run from that
frame with any gas returns a frame, never an error. -/
theorem no_error_ga {code : ByteArray} {message : Message fork} {pc : Nat} {stack : List U256}
    {memory : ByteArray} {state : State.TransactionState} {substate : Substate} {B : Nat}
    {Q : Nat → Evm fork Nat → Prop}
    (h : ∀ g, B ≤ g → SpecGA fork (At code message pc stack memory g state substate) (Q g))
    {gas : Nat} {evm : Evm fork Nat} (start : At code message pc stack memory gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) (e : EvmError) :
    Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within ≠ .error e := by
  obtain ⟨z, hr, hz, -⟩ := h (gas + B) (by omega) _ (at_addGas start B)
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
