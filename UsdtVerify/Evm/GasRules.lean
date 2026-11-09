import UsdtVerify.Evm.Gas
import EthLib.Execution.Proofs.Evm.Logic.Branch
import EthLib.Execution.Proofs.Evm.Logic.Stack
import UsdtVerify.Evm.Write
import EthLib.Execution.Proofs.Evm.Logic.Log
import EthLib.Execution.Proofs.Evm.Logic.NoAbort

/-!
# Rules of opcodes over `StepG`

Each instruction used here is `RunMono`: with less gas it fails, or it gives the same frame with
the same less gas. Round 48: these facts (`runMono_pushN`, `runMono_sstore`, ...) are EthLib's
(Logic/RunMono.lean, #1615), and the local copies are removed. The rules are EthLib's rules
(`Logic.push`, `binary`, `jumpi_taken`, ...) restated over the local `StepG` (with `SimAt`) and
the local `At` (no condition on the return data) through `At.ruleG`, with the same hypotheses and
conclusions. EthLib's own G rules (`Logic.pushG`, ...) are over `Logic.StepG` and `Logic.At`, and
do not give `SimAt` along their steps, so they cannot replace these.

Round 50: the steps that never abort with less gas (`StepGA`, `HoareGA`, `SpecGA`, `At.ruleGA`,
EthLib's `Logic.StepGA` with `SimAt`) moved here from Evm/NoAbort.lean. As in EthLib, PUSH,
CALLDATALOAD, MSTORE, KECCAK256, SLOAD and RETURN are proved once over `StepGA` (`pushGA`, ...),
and their rules over `StepG` (`pushG`, ...) follow by `Triple.lift` and `SpecGA.toG`, with the
same hypotheses and conclusions as before.
-/

namespace UsdtVerify.Gas

open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts

variable {fork : Fork}

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

/-! ## The rules -/

section Rules

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

/-- EthLib's `push` over `StepG`. -/
theorem pushG {n : Fin 33} {word : U256} (hn : n.val ≠ 0) (hlt : pc < code.size)
    (hbyte : code[pc] = 0x5f + UInt8.ofNat n.val)
    (decoded : Op.decode (0x5f + UInt8.ofNat n.val) = some (.push n))
    (hword : pushData code pc n = word) (hgas : 3 ≤ gas) (hstack : stack.length < STACK_LIMIT) :
    HoareG fork (At code message pc stack memory gas state substate)
      (At code message (pc + (1 + n)) (word :: stack) memory (gas - 3) state substate) :=
  Triple.lift (pushGA hn hlt hbyte decoded hword hgas hstack)

/-- EthLib's `push1` over `StepG`. -/
theorem push1G {byte : UInt8} (hlt : pc + 1 < code.size) (hop : code[pc]'(by omega) = 0x60)
    (hbyte : code[pc + 1] = byte) (hgas : 3 ≤ gas) (hstack : stack.length < STACK_LIMIT) :
    HoareG fork (At code message pc stack memory gas state substate)
      (At code message (pc + 2) (BitVec.ofNat 256 byte.toNat :: stack) memory (gas - 3) state
        substate) :=
  pushG (n := 1) (by decide) (by omega) (by rw [hop]; decide) rfl
    (by simp [pushData, bufferRead, EthLib.Base.byteAt, hlt, hbyte, EthLib.Base.bytesToNat]) hgas hstack

/-- EthLib's `push_of_readFrame` over `StepG`, for a word that does not depend on the gas. -/
theorem push_of_readFrameG {byte : UInt8} {op : Op} {cost : Nat} {f : Evm fork Nat → U256}
    {word : U256} (hlt : pc < code.size) (hbyte : code[pc] = byte)
    (decoded : Op.ofByte fork byte = some op)
    (hrun : instruction (Meter := Nat) fork op = some (readFrame cost f))
    (hf : ∀ (a : Evm fork Nat) g, f { a with gas := g } = f a)
    (hword : ∀ evm : Evm fork Nat, evm.code = code → evm.message = message → evm.pc = pc →
      evm.memory = memory → f evm = word)
    (hgas : cost ≤ gas) (hstack : stack.length < STACK_LIMIT)
    (hsim : simulated op = true := by first | decide | rfl) :
    HoareG fork (At code message pc stack memory gas state substate)
      (At code message (pc + 1) (word :: stack) memory (gas - cost) state substate) := by
  apply At.ruleG hlt hbyte decoded hrun (runMono_readFrame cost f hf) (hsim := hsim)
  rintro evm ⟨hcode, hj, hm, hpc, hst, hmem, hg, hrun, herr, hout, hs, hss⟩
  rw [readFrame_of_length_lt (by rw [hst]; exact hstack), charge_nat (by rw [hg]; exact hgas)]
  exact ⟨_, rfl, hcode, hj, hm, by simp [hpc], by
      dsimp only
      rw [hword { evm with gas := evm.gas - cost } hcode hm hpc hmem, hst], hmem,
    by simp [hg], hrun, herr, hout, hs, hss⟩

/-- EthLib's `caller` over `StepG`. -/
theorem callerG (hlt : pc < code.size) (hbyte : code[pc] = 0x33) (hgas : 2 ≤ gas)
    (hstack : stack.length < STACK_LIMIT) :
    HoareG fork (At code message pc stack memory gas state substate)
      (At code message (pc + 1) (message.caller.toU256 :: stack) memory (gas - 2) state
        substate) :=
  push_of_readFrameG hlt hbyte (ofByte_of_decode (op := .caller) rfl (Fork.frontier_le _))
    instruction_caller (fun _ _ => rfl) (fun _ _ hm _ _ => by rw [hm]) hgas hstack

/-- EthLib's `callvalue` over `StepG`. -/
theorem callvalueG (hlt : pc < code.size) (hbyte : code[pc] = 0x34) (hgas : 2 ≤ gas)
    (hstack : stack.length < STACK_LIMIT) :
    HoareG fork (At code message pc stack memory gas state substate)
      (At code message (pc + 1) (message.value :: stack) memory (gas - 2) state substate) :=
  push_of_readFrameG hlt hbyte (ofByte_of_decode (op := .callvalue) rfl (Fork.frontier_le _))
    rfl (fun _ _ => rfl) (fun _ _ hm _ _ => by rw [hm]) hgas hstack

/-- EthLib's `calldatasize` over `StepG`. -/
theorem calldatasizeG (hlt : pc < code.size) (hbyte : code[pc] = 0x36) (hgas : 2 ≤ gas)
    (hstack : stack.length < STACK_LIMIT) :
    HoareG fork (At code message pc stack memory gas state substate)
      (At code message (pc + 1) (BitVec.ofNat 256 message.data.size :: stack) memory (gas - 2)
        state substate) :=
  push_of_readFrameG hlt hbyte (ofByte_of_decode (op := .calldatasize) rfl (Fork.frontier_le _))
    rfl (fun _ _ => rfl) (fun _ _ hm _ _ => by rw [hm]) hgas hstack

/-- EthLib's `binary` over `StepG`. -/
theorem binaryG {byte : UInt8} {op : Op} {cost : Nat} {f : U256 → U256 → U256} {x y : U256}
    {rest : List U256} (hlt : pc < code.size) (hbyte : code[pc] = byte)
    (decoded : Op.ofByte fork byte = some op)
    (hrun : instruction (Meter := Nat) fork op = some (binaryOp cost f)) (hgas : cost ≤ gas)
    (hsim : simulated op = true := by first | decide | rfl) :
    HoareG fork (At code message pc (x :: y :: rest) memory gas state substate)
      (At code message (pc + 1) (f x y :: rest) memory (gas - cost) state substate) := by
  apply At.ruleG hlt hbyte decoded hrun (runMono_binaryOp cost f) (hsim := hsim)
  rintro evm ⟨hcode, hj, hm, hpc, hst, hmem, hg, hrun, herr, hout, hs, hss⟩
  rw [binaryOp_cons hst, charge_nat (by rw [hg]; exact hgas)]
  exact ⟨_, rfl, hcode, hj, hm, by simp [hpc], rfl, hmem, by simp [hg], hrun, herr, hout, hs, hss⟩

/-- EthLib's `unary` over `StepG`. -/
theorem unaryG {byte : UInt8} {op : Op} {cost : Nat} {f : U256 → U256} {x : U256}
    {rest : List U256} (hlt : pc < code.size) (hbyte : code[pc] = byte)
    (decoded : Op.ofByte fork byte = some op)
    (hrun : instruction (Meter := Nat) fork op = some (unaryOp cost f)) (hgas : cost ≤ gas)
    (hsim : simulated op = true := by first | decide | rfl) :
    HoareG fork (At code message pc (x :: rest) memory gas state substate)
      (At code message (pc + 1) (f x :: rest) memory (gas - cost) state substate) := by
  apply At.ruleG hlt hbyte decoded hrun (runMono_unaryOp cost f) (hsim := hsim)
  rintro evm ⟨hcode, hj, hm, hpc, hst, hmem, hg, hrun, herr, hout, hs, hss⟩
  rw [unaryOp_cons hst, charge_nat (by rw [hg]; exact hgas)]
  exact ⟨_, rfl, hcode, hj, hm, by simp [hpc], rfl, hmem, by simp [hg], hrun, herr, hout, hs, hss⟩

/-- EthLib's `dup_of_decode` over `StepG`. -/
theorem dup_of_decodeG {byte : UInt8} {n : Fin 16} {x : U256} (hlt : pc < code.size)
    (hbyte : code[pc] = byte) (decoded : Op.decode byte = some (.dup n))
    (hx : stack[n.val]? = some x) (hgas : 3 ≤ gas) (hstack : stack.length < STACK_LIMIT) :
    HoareG fork (At code message pc stack memory gas state substate)
      (At code message (pc + 1) (x :: stack) memory (gas - 3) state substate) := by
  apply At.ruleG hlt hbyte (ofByte_of_decode decoded (Fork.frontier_le _)) (instruction_dup n)
    (runMono_dupN n)
  rintro evm ⟨hcode, hj, hm, hpc, hst, hmem, hg, hrun, herr, hout, hs, hss⟩
  have hlen : evm.stack.val.length < STACK_LIMIT := by rw [hst]; exact hstack
  rw [dupN_of_getElem? (x := x) (by rw [hst]; exact hx) hlen,
    charge_nat (by rw [hg]; exact hgas)]
  exact ⟨_, rfl, hcode, hj, hm, by simp [hpc], by simp [hst], hmem,
    by simp [hg, OPCODE_DUP, VERY_LOW], hrun, herr, hout, hs, hss⟩

/-- EthLib's `dup` over `StepG`. -/
theorem dupG (n : Fin 16) {x : U256} (hlt : pc < code.size)
    (hbyte : code[pc] = (0x80 + n.val).toUInt8) (hx : stack[n.val]? = some x) (hgas : 3 ≤ gas)
    (hstack : stack.length < STACK_LIMIT) :
    HoareG fork (At code message pc stack memory gas state substate)
      (At code message (pc + 1) (x :: stack) memory (gas - 3) state substate) :=
  dup_of_decodeG hlt hbyte (decode_dup n) hx hgas hstack

/-- EthLib's `dup1` over `StepG`. -/
theorem dup1G {x : U256} {rest : List U256} (hlt : pc < code.size) (hbyte : code[pc] = 0x80)
    (hgas : 3 ≤ gas) (hstack : (x :: rest).length < STACK_LIMIT) :
    HoareG fork (At code message pc (x :: rest) memory gas state substate)
      (At code message (pc + 1) (x :: x :: rest) memory (gas - 3) state substate) :=
  dupG 0 hlt (by rw [hbyte]; rfl) rfl hgas hstack

/-- EthLib's `swap_of_decode` over `StepG`. -/
theorem swap_of_decodeG {byte : UInt8} {n : Fin 16} {top x : U256} {rest : List U256}
    (hlt : pc < code.size) (hbyte : code[pc] = byte) (decoded : Op.decode byte = some (.swap n))
    (hx : rest[n.val]? = some x) (hgas : 3 ≤ gas) :
    HoareG fork (At code message pc (top :: rest) memory gas state substate)
      (At code message (pc + 1) (x :: rest.set n.val top) memory (gas - 3) state substate) := by
  apply At.ruleG hlt hbyte (ofByte_of_decode decoded (Fork.frontier_le _))
    (instruction_of_stackOnlyStep rfl) (runMono_swapN n)
  rintro evm ⟨hcode, hj, hm, hpc, hst, hmem, hg, hrun, herr, hout, hs, hss⟩
  rw [swapN_of_getElem? hst hx, charge_nat (by rw [hg]; exact hgas)]
  exact ⟨_, rfl, hcode, hj, hm, by simp [hpc], rfl, hmem, by simp [hg, OPCODE_SWAP, VERY_LOW],
    hrun, herr, hout, hs, hss⟩

/-- EthLib's `swap` over `StepG`. -/
theorem swapG (n : Fin 16) {top x : U256} {rest : List U256} (hlt : pc < code.size)
    (hbyte : code[pc] = (0x90 + n.val).toUInt8) (hx : rest[n.val]? = some x) (hgas : 3 ≤ gas) :
    HoareG fork (At code message pc (top :: rest) memory gas state substate)
      (At code message (pc + 1) (x :: rest.set n.val top) memory (gas - 3) state substate) :=
  swap_of_decodeG hlt hbyte (decode_swap n) hx hgas

/-- EthLib's `jumpdest` over `StepG`. -/
theorem jumpdestG (hlt : pc < code.size) (hbyte : code[pc] = 0x5b) (hgas : 1 ≤ gas) :
    HoareG fork (At code message pc stack memory gas state substate)
      (At code message (pc + 1) stack memory (gas - 1) state substate) := by
  apply At.ruleG hlt hbyte (ofByte_of_decode (op := .jumpdest) rfl (Fork.frontier_le _))
    instruction_jumpdest runMono_jumpdest
  rintro evm ⟨hcode, hj, hm, hpc, hst, hmem, hg, hrun, herr, hout, hs, hss⟩
  rw [jumpdestStep_eq, charge_nat (by rw [hg]; exact hgas)]
  exact ⟨_, rfl, hcode, hj, hm, by simp [hpc], hst, hmem, by simp [hg, OPCODE_JUMPDEST], hrun,
    herr, hout, hs, hss⟩

/-- EthLib's `jumpi_zero` over `StepG`. -/
theorem jumpi_zeroG {destination : U256} {rest : List U256} (hlt : pc < code.size)
    (hbyte : code[pc] = 0x57) (hgas : 10 ≤ gas) :
    HoareG fork (At code message pc (destination :: 0 :: rest) memory gas state substate)
      (At code message (pc + 1) rest memory (gas - 10) state substate) := by
  apply At.ruleG hlt hbyte (ofByte_of_decode (op := .jumpi) rfl (Fork.frontier_le _))
    instruction_jumpi runMono_jumpi
  rintro evm ⟨hcode, hj, hm, hpc, hst, hmem, hg, hrun, herr, hout, hs, hss⟩
  rw [jumpiStep_zero hst, charge_nat (by rw [hg]; exact hgas)]
  exact ⟨_, rfl, hcode, hj, hm, by simp [hpc], rfl, hmem, by simp [hg, OPCODE_JUMPI, HIGH],
    hrun, herr, hout, hs, hss⟩

/-- EthLib's `jumpi_of_eq_zero` over `StepG`. -/
theorem jumpi_of_eq_zeroG {destination condition : U256} {rest : List U256}
    (hlt : pc < code.size) (hbyte : code[pc] = 0x57) (hgas : 10 ≤ gas) (zero : condition = 0) :
    HoareG fork
      (At code message pc (destination :: condition :: rest) memory gas state substate)
      (At code message (pc + 1) rest memory (gas - 10) state substate) := by
  subst zero
  exact jumpi_zeroG hlt hbyte hgas

/-- EthLib's `jumpi_taken` over `StepG`. -/
theorem jumpi_takenG {destination condition : U256} {rest : List U256} (hlt : pc < code.size)
    (hbyte : code[pc] = 0x57) (hgas : 10 ≤ gas) (nonzero : condition ≠ 0)
    (valid : isValidJumpDest (validJumpDestinations code) destination.toNat = true) :
    HoareG fork
      (At code message pc (destination :: condition :: rest) memory gas state substate)
      (At code message destination.toNat rest memory (gas - 10) state substate) := by
  apply At.ruleG hlt hbyte (ofByte_of_decode (op := .jumpi) rfl (Fork.frontier_le _))
    instruction_jumpi runMono_jumpi
  rintro evm ⟨hcode, hj, hm, hpc, hst, hmem, hg, hrun, herr, hout, hs, hss⟩
  rw [jumpiStep_of_isValidJumpDest hst nonzero (charge_nat (by rw [hg]; exact hgas))
    (by rw [hj]; exact valid)]
  exact ⟨_, rfl, hcode, hj, hm, rfl, rfl, hmem, by simp [hg, OPCODE_JUMPI, HIGH], hrun, herr,
    hout, hs, hss⟩

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

/-- EthLib's `calldataload` over `StepG`. -/
theorem calldataloadG {start : U256} {rest : List U256} (hlt : pc < code.size)
    (hbyte : code[pc] = 0x35) (hgas : 3 ≤ gas) :
    HoareG fork (At code message pc (start :: rest) memory gas state substate)
      (At code message (pc + 1) (loadWord message.data start.toNat 32 :: rest) memory
        (gas - 3) state substate) :=
  Triple.lift (calldataloadGA hlt hbyte hgas)

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

/-- EthLib's `mstore` over `StepG`. -/
theorem mstoreG {start value : U256} {rest : List U256} (hlt : pc < code.size)
    (hbyte : code[pc] = 0x52)
    (hgas : 3 + (extendMemory memory.size [(start, 32)]).cost ≤ gas) :
    HoareG fork (At code message pc (start :: value :: rest) memory gas state substate)
      (At code message (pc + 1) rest
        (memoryWrite (memoryExtend memory (extendMemory memory.size [(start, 32)]).expandBy)
          start.toNat (wordBytes value))
        (gas - (3 + (extendMemory memory.size [(start, 32)]).cost)) state substate) :=
  Triple.lift (mstoreGA hlt hbyte hgas)

/-- EthLib's `revert` over `StepG`. -/
theorem revertG (hfork : .byzantium ≤ fork) {start size : U256} {rest : List U256}
    (hlt : pc < code.size) (hbyte : code[pc] = 0xfd)
    (hgas : (extendMemory memory.size [(start, size)]).cost ≤ gas) :
    SpecG fork (At code message pc (start :: size :: rest) memory gas state substate)
      (Halted true
        (memoryReadBytes (memoryExtend memory (extendMemory memory.size [(start, size)]).expandBy)
          start.toNat size.toNat)
        (gas - (extendMemory memory.size [(start, size)]).cost) state substate) := by
  apply At.ruleG hlt hbyte (ofByte_of_decode (op := .revert) rfl hfork)
    (instruction_revert hfork) runMono_revert
  rintro evm ⟨hcode, hj, hm, hpc, hst, hmem, hg, hrun, herr, hout, hs, hss⟩
  subst hmem hg
  rw [revertStep_eq, returnStep_cons hst]
  dsimp only
  rw [charge_nat hgas]
  exact ⟨_, rfl, rfl, rfl, rfl, rfl, by simp, hs, hss⟩

/-- EthLib's `reshape` over `StepG`. -/
theorem reshapeG {pc : Nat} {s s' : List U256} {m m' : ByteArray} {g g' : Nat}
    {st : State.TransactionState} {ss : Substate} (hs : s = s') (hm : m = m') (hg : g = g') :
    HoareG fork (At code message pc s m g st ss) (At code message pc s' m' g' st ss) := by
  subst hs hm hg
  exact Triple.of_imp fun _ h => h

/-- `Hoare.gas_eq` over `StepG`. -/
theorem HoareG.gas_eq {P : Evm fork Nat → Prop} {pc : Nat} {s : List U256} {m : ByteArray}
    {g g' : Nat} {st : State.TransactionState} {ss : Substate}
    (h : HoareG fork P (At code message pc s m g st ss)) (hg : g = g') :
    HoareG fork P (At code message pc s m g' st ss) := hg ▸ h

end Rules

end UsdtVerify.Gas

section

/-!
## More rules of opcodes over `StepG`

POP, JUMP, MLOAD, KECCAK256, EXP, RETURN, STOP, SLOAD, SSTORE and LOG0..LOG4 are `RunMono`;
their rules are EthLib's, restated over `StepG`; SSTORE at every fork
from Berlin (`sstoreG_any`, `sstoreWG`, price `writeCost`).
-/

namespace UsdtVerify.Gas

open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts

variable {fork : Fork}
/-! ## The rules -/

section Rules

variable {code : ByteArray} {message : Message fork} {pc : Nat} {stack : List U256}
  {memory : ByteArray} {gas : Nat} {state : State.TransactionState} {substate : Substate}

/-- EthLib's `pop` over `StepG`. -/
theorem popG {x : U256} {rest : List U256} (hlt : pc < code.size) (hbyte : code[pc] = 0x50)
    (hgas : 2 ≤ gas) :
    HoareG fork (At code message pc (x :: rest) memory gas state substate)
      (At code message (pc + 1) rest memory (gas - 2) state substate) := by
  apply At.ruleG hlt hbyte (ofByte_of_decode (op := .pop) rfl (Fork.frontier_le _))
    (instruction_of_stackOnlyStep rfl) runMono_pop
  rintro evm ⟨hcode, hj, hm, hpc, hst, hmem, hg, hrun, herr, hout, hs, hss⟩
  rw [popStep_cons hst, charge_nat (by rw [hg]; exact hgas)]
  exact ⟨_, rfl, hcode, hj, hm, by simp [hpc], rfl, hmem, by simp [hg, OPCODE_POP, BASE], hrun,
    herr, hout, hs, hss⟩

/-- EthLib's `exp` over `StepG`. -/
theorem expG {base exponent : U256} {rest : List U256} (hlt : pc < code.size)
    (hbyte : code[pc] = 0x0a)
    (hgas : OPCODE_EXP_BASE + (gasSchedule fork).OPCODE_EXP_PER_BYTE * exponentBytes exponent ≤
      gas) :
    HoareG fork (At code message pc (base :: exponent :: rest) memory gas state substate)
      (At code message (pc + 1) (Evm.exp base exponent :: rest) memory
        (gas - (OPCODE_EXP_BASE + (gasSchedule fork).OPCODE_EXP_PER_BYTE *
          exponentBytes exponent)) state substate) := by
  apply At.ruleG hlt hbyte (ofByte_of_decode (op := .exp) rfl (Fork.frontier_le _))
    (instruction_of_stackOnlyStep rfl) runMono_exp
  rintro evm ⟨hcode, hj, hm, hpc, hst, hmem, hg, hrun, herr, hout, hs, hss⟩
  rw [expStep_of_cons hst, charge_nat (by rw [hg]; exact hgas)]
  exact ⟨_, rfl, hcode, hj, hm, by simp [hpc], rfl, hmem, by simp [hg], hrun, herr, hout, hs, hss⟩

/-- `expG` with the price from Spurious Dragon worked out (EIP-160: 10, and 50 per byte of the
exponent). -/
theorem expLG (hfork : .spuriousDragon ≤ fork) {base exponent : U256} {rest : List U256}
    (hlt : pc < code.size) (hbyte : code[pc] = 0x0a)
    (hgas : 10 + 50 * exponentBytes exponent ≤ gas) :
    HoareG fork (At code message pc (base :: exponent :: rest) memory gas state substate)
      (At code message (pc + 1) (Evm.exp base exponent :: rest) memory
        (gas - (10 + 50 * exponentBytes exponent)) state substate) := by
  have price : OPCODE_EXP_BASE + (gasSchedule fork).OPCODE_EXP_PER_BYTE *
      exponentBytes exponent = 10 + 50 * exponentBytes exponent := by
    simp [OPCODE_EXP_BASE, gasSchedule, hfork]
  have h := expG (fork := fork) (code := code) (message := message) (memory := memory)
    (state := state) (substate := substate) (base := base) (exponent := exponent) (rest := rest)
    hlt hbyte (by rw [price]; exact hgas)
  rw [price] at h
  exact h

/-- EthLib's `jump` over `StepG`. -/
theorem jumpG {destination : U256} {rest : List U256} (hlt : pc < code.size)
    (hbyte : code[pc] = 0x56) (hgas : 8 ≤ gas)
    (valid : isValidJumpDest (validJumpDestinations code) destination.toNat = true) :
    HoareG fork (At code message pc (destination :: rest) memory gas state substate)
      (At code message destination.toNat rest memory (gas - 8) state substate) := by
  apply At.ruleG hlt hbyte (ofByte_of_decode (op := .jump) rfl (Fork.frontier_le _))
    instruction_jump runMono_jump
  rintro evm ⟨hcode, hj, hm, hpc, hst, hmem, hg, hrun, herr, hout, hs, hss⟩
  rw [jumpStep_of_isValidJumpDest hst (charge_nat (by rw [hg]; exact hgas))
    (by rw [hj]; exact valid)]
  exact ⟨_, rfl, hcode, hj, hm, rfl, rfl, hmem, by simp [hg, OPCODE_JUMP, MID], hrun, herr, hout,
    hs, hss⟩

/-- EthLib's `mload` over `StepG`. -/
theorem mloadG {start : U256} {rest : List U256} (hlt : pc < code.size)
    (hbyte : code[pc] = 0x51)
    (hgas : 3 + (extendMemory memory.size [(start, 32)]).cost ≤ gas) :
    HoareG fork (At code message pc (start :: rest) memory gas state substate)
      (At code message (pc + 1)
        (loadWord (memoryReadBytes
          (memoryExtend memory (extendMemory memory.size [(start, 32)]).expandBy)
          start.toNat 32) 0 32 :: rest)
        (memoryExtend memory (extendMemory memory.size [(start, 32)]).expandBy)
        (gas - (3 + (extendMemory memory.size [(start, 32)]).cost)) state substate) := by
  apply At.ruleG hlt hbyte (ofByte_of_decode (op := .mload) rfl (Fork.frontier_le _))
    instruction_mload runMono_mload
  rintro evm ⟨hcode, hj, hm, hpc, hst, hmem, hg, hrun, herr, hout, hs, hss⟩
  subst hmem hg
  have hcost : OPCODE_MLOAD_BASE = 3 := rfl
  rw [mloadStep_cons hst]
  dsimp only
  rw [hcost, charge_nat hgas]
  refine ⟨_, rfl, hcode, hj, hm, by simp [hpc], ?_, ?_, ?_, hrun, herr, hout, hs, hss⟩
  · show _ :: rest = _ :: rest
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

/-- EthLib's `keccak256` over `StepG`. -/
theorem keccak256G {start size : U256} {rest : List U256} (hlt : pc < code.size)
    (hbyte : code[pc] = 0x20)
    (hgas :
      keccak256Cost size + (extendMemory memory.size [(start, size)]).cost ≤ gas) :
    HoareG fork (At code message pc (start :: size :: rest) memory gas state substate)
      (At code message (pc + 1)
        (keccak (memoryReadBytes
          (memoryExtend memory (extendMemory memory.size [(start, size)]).expandBy)
          start.toNat size.toNat) :: rest)
        (memoryExtend memory (extendMemory memory.size [(start, size)]).expandBy)
        (gas - (keccak256Cost size + (extendMemory memory.size [(start, size)]).cost))
        state substate) :=
  Triple.lift (keccak256GA hlt hbyte hgas)

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

/-- EthLib's `sload` over `StepG`. -/
theorem sloadG (hfork : .berlin ≤ fork) {key : U256} {rest : List U256} {cold : Bool}
    (hlt : pc < code.size) (hbyte : code[pc] = 0x54)
    (hcold : decide (U256.toBeBytes key ∉
      substate.accessedStorageKeys.getD message.currentTarget ∅) = cold)
    (hgas : (if cold then 2100 else 100) ≤ gas) :
    HoareG fork (At code message pc (key :: rest) memory gas state substate)
      (At code message (pc + 1)
        (state.getStorage message.currentTarget (U256.toBeBytes key) :: rest) memory
        (gas - if cold then 2100 else 100)
        (state.recordStorageRead message.currentTarget (U256.toBeBytes key))
        { substate with
          accessedStorageKeys := (substate.accessedStorageKeys.insert message.currentTarget
            ((substate.accessedStorageKeys.getD message.currentTarget ∅).insert
              (U256.toBeBytes key))) }) :=
  Triple.lift (sloadGA hfork hlt hbyte hcold hgas)

/-- EthLib's `stop` over `StepG`. -/
theorem stopG (hlt : pc < code.size) (hbyte : code[pc] = 0x00) :
    SpecG fork (At code message pc stack memory gas state substate)
      (Halted false .empty gas state substate) := by
  apply At.ruleG hlt hbyte (ofByte_of_decode (op := .stop) rfl (Fork.frontier_le _)) rfl
    runMono_stop
  rintro evm ⟨-, -, -, -, -, -, hg, -, herr, hout, hs, hss⟩
  exact ⟨_, stopStep_eq evm, rfl, rfl, herr, hout, hg, hs, hss⟩

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

/-- EthLib's `return` over `StepG`. -/
theorem returnG {start size : U256} {rest : List U256} (hlt : pc < code.size)
    (hbyte : code[pc] = 0xf3) (hgas : (extendMemory memory.size [(start, size)]).cost ≤ gas) :
    SpecG fork (At code message pc (start :: size :: rest) memory gas state substate)
      (Halted false
        (memoryReadBytes (memoryExtend memory (extendMemory memory.size [(start, size)]).expandBy)
          start.toNat size.toNat)
        (gas - (extendMemory memory.size [(start, size)]).cost) state substate) :=
  SpecGA.toG (returnGA hlt hbyte hgas)

/-- The price of an SSTORE for the one-counter meter, at every fork from Berlin: the price of the
write (`sstoreCost`) plus the state gas of a new slot (`sstoreStateGas`, 0 before Glamsterdam).
The meter `Nat` has no reservoir: its refill of state gas is no change. -/
abbrev writeCost (fork : Fork) (orig cur new : U256) (cold : Bool) : Nat :=
  sstoreCost fork orig cur new cold + sstoreStateGas fork orig cur new

theorem writeCost_of_lt (hglam : fork < .glamsterdam) (orig cur new : U256) (cold : Bool) :
    writeCost fork orig cur new cold = sstoreCost fork orig cur new cold := by
  have hng : ¬fork ≥ .glamsterdam := Nat.not_le_of_lt hglam
  simp [writeCost, sstoreStateGas, hng]

/-- An upper bound of `writeCost` at `fork`: 22100 (a cold write from zero, 2100 + 20000) before
Glamsterdam; from Glamsterdam 110020 (a cold access 2100, a write 10000 and the state gas of a new
slot 97920). -/
abbrev writeMax (fork : Fork) : Nat := if fork ≥ .glamsterdam then 110020 else 22100

/-- From Berlin, an SSTORE costs at most `writeMax fork`. -/
theorem writeCost_le (hfork : .berlin ≤ fork) (orig cur new : U256) (cold : Bool) :
    writeCost fork orig cur new cold ≤ writeMax fork := by
  by_cases hg : fork ≥ .glamsterdam
  · simp only [writeMax, hg, ↓reduceIte, writeCost, sstoreCost, sstoreStateGas, true_and]
    have h1 : STORAGE_SET_STATE_GAS = 97920 := rfl
    cases cold <;> simp only [COLD_STORAGE_ACCESS, WARM_ACCESS, STORAGE_WRITE, h1, ite_true,
      Bool.false_eq_true, ite_false] <;> (repeat' split) <;> omega
  · rw [writeCost_of_lt (Nat.lt_of_not_le hg)]
    simp only [writeMax, hg, ↓reduceIte]
    have := sstoreCost_le hfork (Nat.lt_of_not_le hg) orig cur new cold
    simp only [COLD_STORAGE_ACCESS, STORAGE_SET] at this
    exact this

/-- The step of SSTORE at every fork from Berlin (Glamsterdam included), in a frame that may
change the state: EthLib's `sstoreStep_eq`, with the state gas of a new slot in the price. -/
theorem sstoreStep_eq_any (hfork : .berlin ≤ fork)
    {evm : Evm fork Nat} {key new : U256} {rest : List U256} {state' : State.TransactionState}
    (hst : evm.stack.val = key :: new :: rest) (hstatic : evm.message.isStatic = false)
    (hstipend : CALL_STIPEND < evm.gas)
    (hgas : writeCost fork
      (evm.state.getStorageOriginal evm.message.currentTarget (U256.toBeBytes key))
      (evm.state.getStorage evm.message.currentTarget (U256.toBeBytes key)) new
      (decide (U256.toBeBytes key ∉
        evm.substate.accessedStorageKeys.getD evm.message.currentTarget ∅)) ≤ evm.gas)
    (hset : (evm.state.recordStorageRead evm.message.currentTarget (U256.toBeBytes key)).setStorage
      evm.message.currentTarget (U256.toBeBytes key) new = .ok state') :
    ∃ after, sstoreStep evm = .ok after ∧
      after.code = evm.code ∧ after.validJumpDestinations = evm.validJumpDestinations ∧
      after.message = evm.message ∧ after.pc = evm.pc + 1 ∧ after.stack.val = rest ∧
      after.memory = evm.memory ∧
      after.gas = evm.gas - writeCost fork
        (evm.state.getStorageOriginal evm.message.currentTarget (U256.toBeBytes key))
        (evm.state.getStorage evm.message.currentTarget (U256.toBeBytes key)) new
        (decide (U256.toBeBytes key ∉
          evm.substate.accessedStorageKeys.getD evm.message.currentTarget ∅)) ∧
      after.running = evm.running ∧ after.error = evm.error ∧ after.output = evm.output ∧
      after.state = state' ∧ after.substate = { evm.substate with
        accessedStorageKeys := evm.substate.accessedStorageKeys.insert evm.message.currentTarget
          ((evm.substate.accessedStorageKeys.getD evm.message.currentTarget ∅).insert
            (U256.toBeBytes key))
        refundCounter := evm.substate.refundCounter + sstoreRefund fork
          (evm.state.getStorageOriginal evm.message.currentTarget (U256.toBeBytes key))
          (evm.state.getStorage evm.message.currentTarget (U256.toBeBytes key)) new } := by
  have hist : Fork.istanbul ≤ fork := Nat.le_trans (by decide) hfork
  rcases evm with ⟨pc, ⟨l, hl⟩, memory, code, valid, gas, running, message, output, returnData,
    state, substate, error⟩
  simp only at hst hstatic hstipend hgas hset ⊢
  subst hst
  generalize hC : sstoreCost fork
      (state.getStorageOriginal message.currentTarget (U256.toBeBytes key))
      (state.getStorage message.currentTarget (U256.toBeBytes key)) new
      (!decide (U256.toBeBytes key ∈ substate.accessedStorageKeys.getD message.currentTarget ∅))
      = C
  have hC' : sstoreCost fork
      (state.getStorageOriginal message.currentTarget (U256.toBeBytes key))
      (state.getStorage message.currentTarget (U256.toBeBytes key)) new
      (decide (U256.toBeBytes key ∉ substate.accessedStorageKeys.getD message.currentTarget ∅))
      = C := by simpa using hC
  generalize hS : sstoreStateGas fork
      (state.getStorageOriginal message.currentTarget (U256.toBeBytes key))
      (state.getStorage message.currentTarget (U256.toBeBytes key)) new = S at hgas ⊢
  rw [writeCost, hC', hS] at hgas
  simp only [writeCost, hC', hS]
  have hrefill : ∀ g : Nat, GasMeter.refill g (sstoreStateRefill fork
      (state.getStorageOriginal message.currentTarget (U256.toBeBytes key))
      (state.getStorage message.currentTarget (U256.toBeBytes key)) new) = g := fun _ => rfl
  have h1 : ¬ gas < C := by omega
  have h2 : ¬ gas - C < S := by omega
  have hsub : gas - C - S = gas - (C + S) := by omega
  simp [sstoreStep, popWord, Stack.pop, bind, Except.bind, pure, Except.pure, hist,
    GasMeter.gasLeft, Nat.not_le.mpr hstipend, accessStorageKey, hfork, recordStorageRead,
    keepReads, refillStateGas, hrefill, chargeGas, GasMeter.charge, h1, hC,
    chargeStateGas, GasMeter.chargeState, hS, h2, hstatic, hset, Except.mapError, advance, hsub]

/-- SSTORE over `StepG` at every fork from Berlin, Glamsterdam included, with the price
`writeCost`. -/
theorem sstoreG_any (hfork : .berlin ≤ fork) {key new : U256}
    {rest : List U256} {cold : Bool} {state' : State.TransactionState}
    (hlt : pc < code.size) (hbyte : code[pc] = 0x55) (hstatic : message.isStatic = false)
    (hcold : decide (U256.toBeBytes key ∉
      substate.accessedStorageKeys.getD message.currentTarget ∅) = cold)
    (hstipend : CALL_STIPEND < gas)
    (hgas : writeCost fork (state.getStorageOriginal message.currentTarget (U256.toBeBytes key))
      (state.getStorage message.currentTarget (U256.toBeBytes key)) new cold ≤ gas)
    (hset : (state.recordStorageRead message.currentTarget (U256.toBeBytes key)).setStorage
      message.currentTarget (U256.toBeBytes key) new = .ok state') :
    HoareG fork (At code message pc (key :: new :: rest) memory gas state substate)
      (At code message (pc + 1) rest memory
        (gas - writeCost fork
          (state.getStorageOriginal message.currentTarget (U256.toBeBytes key))
          (state.getStorage message.currentTarget (U256.toBeBytes key)) new cold)
        state'
        { substate with
          accessedStorageKeys := substate.accessedStorageKeys.insert message.currentTarget
            ((substate.accessedStorageKeys.getD message.currentTarget ∅).insert
              (U256.toBeBytes key))
          refundCounter := substate.refundCounter + sstoreRefund fork
            (state.getStorageOriginal message.currentTarget (U256.toBeBytes key))
            (state.getStorage message.currentTarget (U256.toBeBytes key)) new }) := by
  apply At.ruleG hlt hbyte (ofByte_of_decode (op := .sstore) rfl (Fork.frontier_le _))
    instruction_sstore runMono_sstore
  rintro evm ⟨hcode, hj, hm, hpc, hst, hmem, hg, hrun, herr, hout, hs, hss⟩
  subst hm hg hs hss hcold
  obtain ⟨after, h, a1, a2, a3, a4, a5, a6, a7, a8, a9, ao, a10, a11⟩ :=
    sstoreStep_eq_any hfork hst hstatic hstipend hgas hset
  exact ⟨after, h, by rw [a1, hcode], by rw [a2, hj], a3, by rw [a4, hpc], a5, by rw [a6, hmem],
    a7, by rw [a8, hrun], by rw [a9, herr], by rw [ao, hout], a10, a11⟩

/-- SSTORE over slots (`writeSlot`, `storeSub`) over `StepG` at every fork from Berlin
(Glamsterdam included), with the price `writeCost` (the pre-Glamsterdam `sstoreW` was deleted in
round 19). -/
theorem sstoreWG (hfork : .berlin ≤ fork) {key new : U256}
    {rest : List U256} {cold : Bool} (hlt : pc < code.size) (hbyte : code[pc] = 0x55)
    (hstatic : message.isStatic = false) (hacc : hasAccount state message.currentTarget)
    (hcold : coldIn substate message.currentTarget key = cold) (hstipend : 2300 < gas)
    (hgas : writeCost fork (originalAt state message.currentTarget key)
      (storageAt state message.currentTarget key) new cold ≤ gas) :
    HoareG fork (At code message pc (key :: new :: rest) memory gas state substate)
      (At code message (pc + 1) rest memory
        (gas - writeCost fork (originalAt state message.currentTarget key)
          (storageAt state message.currentTarget key) new cold)
        (writeSlot state message.currentTarget key new)
        (storeSub fork substate message.currentTarget key
          (originalAt state message.currentTarget key)
          (storageAt state message.currentTarget key) new)) :=
  sstoreG_any hfork hlt hbyte hstatic hcold hstipend hgas (setStorage_writeSlot hacc)

/-- EthLib's `log` over `StepG`. -/
theorem logG {n : Fin 5} {byte : UInt8} {start size : U256} {words rest : List U256}
    (hlen : words.length = n.val) (hlt : pc < code.size) (hbyte : code[pc] = byte)
    (decoded : Op.decode byte = some (.log n)) (hstatic : message.isStatic = false)
    (hgas : logCost n.val size + (extendMemory memory.size [(start, size)]).cost ≤ gas) :
    HoareG fork (At code message pc (start :: size :: (words ++ rest)) memory gas state substate)
      (At code message (pc + 1) rest
        (memoryExtend memory (extendMemory memory.size [(start, size)]).expandBy)
        (gas - (logCost n.val size + (extendMemory memory.size [(start, size)]).cost)) state
        { substate with
          logs := substate.logs.push
            { address := message.currentTarget
              topics := words.map U256.toBeBytes
              data := memoryReadBytes
                (memoryExtend memory (extendMemory memory.size [(start, size)]).expandBy)
                start.toNat size.toNat } }) := by
  apply At.ruleG hlt hbyte (ofByte_of_decode decoded (Fork.frontier_le _)) (instruction_log n)
    (runMono_log n.val)
  rintro evm ⟨hcode, hj, hm, hpc, hst, hmem, hg, hrun, herr, hout, hs, hss⟩
  subst hm hg hs hss hmem
  have hl := evm.stack.property
  rw [hst] at hl
  have hlr : (words ++ rest).length ≤ STACK_LIMIT := by simp at hl ⊢; omega
  have hs : evm.stack = ⟨start :: size :: (words ++ rest), hst ▸ evm.stack.property⟩ :=
    Subtype.ext hst
  have htop := popTopics_append (evm := { evm with stack := ⟨words ++ rest, hlr⟩ })
    (words := words) (rest := rest) rfl
  rw [hlen] at htop
  simp only [logStep, popWord, Stack.pop, hs, bind, Except.bind, pure, Except.pure]
  rw [htop]
  simp only [chargeGasAndMemory, chargeGas, GasMeter.charge, logCost] at hgas ⊢
  simp only [Nat.not_lt.mpr hgas, ite_false, bind, Except.bind, pure, Except.pure, hstatic,
    Bool.false_eq_true]
  exact ⟨_, rfl, hcode, hj, rfl, by simp [advance, hpc], rfl, rfl, rfl, hrun, herr, hout, rfl,
    rfl⟩

/-- EthLib's `Spec.reshape` over `StepG`. -/
theorem SpecG.reshape {pc : Nat} {s s' : List U256} {m m' : ByteArray} {g g' : Nat}
    {st : State.TransactionState} {ss : Substate} {Q : Evm fork Nat → Prop} (hs : s = s')
    (hm : m = m') (hg : g = g') (h : SpecG fork (At code message pc s' m' g' st ss) Q) :
    SpecG fork (At code message pc s m g st ss) Q :=
  SpecG.seq (reshapeG hs hm hg) h

end Rules

section Table

variable {message : Message fork} {state : State.TransactionState} {substate : Substate}

/-- EthLib's `branchTable` over `StepG`. -/
theorem branchTableG {code : ByteArray} {memory : ByteArray} {n m : Fin 33} (hn : n.val ≠ 0)
    (hm : m.val ≠ 0) {x : U256} {rest : List U256} (hstack : rest.length + 2 < STACK_LIMIT) :
    ∀ {pc gas : Nat} {entries : List (U256 × U256)}, Table code n m pc entries →
      22 * tested x entries ≤ gas →
      HoareG fork (At code message pc (x :: rest) memory gas state substate)
        (At code message (branch x pc (entrySize n m) entries) (x :: rest) memory
          (gas - 22 * tested x entries) state substate)
  | pc, gas, [], _, _ => Triple.of_imp fun _ h => h
  | pc, gas, (key, dest) :: entries, ⟨⟨l0, b0⟩, ⟨l1, b1⟩, hkey, ⟨l2, b2⟩, ⟨l3, b3⟩, hdest,
      ⟨l4, b4⟩, valid, table⟩, hgas => by
    have h22 : 22 ≤ gas := by
      simp only [tested] at hgas
      split at hgas <;> omega
    have h1 := dup1G (fork := fork) (code := code) (message := message) (memory := memory)
      (state := state) (substate := substate) (pc := pc) (x := x) (rest := rest) (gas := gas)
      l0 b0 (by omega) (by simp only [List.length_cons]; omega)
    have h2 := pushG (fork := fork) (code := code) (message := message) (memory := memory)
      (state := state) (substate := substate) (pc := pc + 1) (stack := x :: x :: rest)
      (gas := gas - 3) (n := n) (word := key) hn l1 b1 (decode_push n hn) hkey (by omega)
      (by simp only [List.length_cons]; omega)
    have h3 := binaryG (fork := fork) (code := code) (message := message) (memory := memory)
      (state := state) (substate := substate) (pc := pc + 1 + (1 + n)) (x := key) (y := x)
      (rest := x :: rest) (gas := gas - 3 - 3) l2 b2
      (ofByte_of_decode (op := .eq) rfl (Fork.frontier_le _)) instruction_eq
      (by simp only [OPCODE_EQ, VERY_LOW]; omega)
    have h4 := pushG (fork := fork) (code := code) (message := message) (memory := memory)
      (state := state) (substate := substate) (pc := pc + 1 + (1 + n) + 1)
      (stack := equal key x :: x :: rest) (gas := gas - 3 - 3 - OPCODE_EQ) (n := m) (word := dest)
      hm l3 b3 (decode_push m hm) hdest (by simp only [OPCODE_EQ, VERY_LOW]; omega)
      (by simp only [List.length_cons]; omega)
    have h14 := ((h1.seq h2).seq h3).seq h4
    by_cases hk : key = x
    · have h5 := jumpi_takenG (fork := fork) (code := code) (message := message)
        (memory := memory) (state := state) (substate := substate)
        (pc := pc + 1 + (1 + n) + 1 + (1 + m))
        (destination := dest) (condition := equal key x) (rest := x :: rest)
        (gas := gas - 3 - 3 - OPCODE_EQ - 3) l4 b4 (by simp only [OPCODE_EQ, VERY_LOW]; omega)
        (by simp [equal, hk]) valid
      have h := h14.seq h5
      simp only [branch, tested, hk, ite_true]
      exact HoareG.gas_eq h (by simp only [OPCODE_EQ, VERY_LOW]; omega)
    · have heq : equal key x = 0 := by simp [equal, hk]
      rw [heq] at h14
      have h5 := jumpi_zeroG (fork := fork) (code := code) (message := message)
        (memory := memory) (state := state) (substate := substate)
        (pc := pc + 1 + (1 + n) + 1 + (1 + m))
        (destination := dest) (rest := x :: rest) (gas := gas - 3 - 3 - OPCODE_EQ - 3) l4 b4
        (by simp only [OPCODE_EQ, VERY_LOW]; omega)
      have hpc : pc + 1 + (1 + n) + 1 + (1 + m) + 1 = pc + entrySize n m := by
        simp only [entrySize]
        omega
      rw [hpc] at h5
      simp only [tested, hk, ite_false] at hgas
      have h15 := HoareG.gas_eq (h14.seq h5) (g' := gas - 22)
        (by simp only [OPCODE_EQ, VERY_LOW]; omega)
      have ih := branchTableG (memory := memory) (x := x) (pc := pc + entrySize n m) (gas := gas - 22) hn hm hstack
        table (by omega)
      simp only [branch, tested, hk, ite_false]
      exact HoareG.gas_eq (h15.seq ih) (by omega)

end Table

end UsdtVerify.Gas

end
