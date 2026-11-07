import UsdtVerify.Gas
import UsdtVerify.Local.Rules

/-!
# Rules of opcodes over `StepG`

Each instruction used here is `RunMono`: with less gas it fails, or it gives the same frame with
the same less gas. The rules are EthLib's rules (`Logic.push`, `binary`, `jumpi_taken`, ...)
restated over `StepG` through `At.ruleG`, with the same hypotheses and conclusions.
-/

namespace UsdtVerify.Gas

open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts

variable {fork : Fork}

/-! ## Instructions that charge once -/

/-- A result that pays `c` from the gas `g`, then gives `F` of the gas left. -/
theorem rel_map_charge {k g c : Nat} {F : Nat → Evm fork Nat}
    (hF : ∀ g', F (g' + k) = sh k (F g')) :
    Rel k ((GasMeter.charge g c).map F) ((GasMeter.charge (g + k) c).map F) := by
  simp only [GasMeter.charge]
  by_cases h : g < c
  · exact .inl (.inl ⟨.outOfGas, by simp [h, Except.map]⟩)
  · have h' : ¬ g + k < c := by omega
    refine .inr ⟨F (g - c), by simp [h, Except.map], ?_⟩
    simp only [h', ↓reduceIte, Except.map]
    rw [show g + k - c = (g - c) + k by omega, hF]

theorem fails_error {e : EvmError} : Fails (fork := fork) (.error e) := .inl ⟨e, rfl⟩

theorem rel_error {k : Nat} {e : EvmError} {hi : Except EvmError (Evm fork Nat)} :
    Rel k (.error e) hi := .inl fails_error

/-- A result that is an error for every outcome of the charge. -/
theorem error_of_charge {r : Except EvmError (Evm fork Nat)} {g c : Nat}
    (h : ∀ g', GasMeter.charge g c = .ok g' → ∃ e, r = .error e)
    (h' : ∀ e, GasMeter.charge g c = .error e → ∃ e', r = .error e') : ∃ e, r = .error e := by
  rcases hc : GasMeter.charge g c with e | g'
  · exact h' e hc
  · exact h g' hc

theorem runMono_binaryOp (cost : Nat) (f : U256 → U256 → U256) :
    RunMono (fork := fork) (binaryOp cost f) := by
  intro a k
  rcases hs : a.stack with ⟨_ | ⟨x, _ | ⟨y, rest⟩⟩, hp⟩
  · refine .inl (.inl ⟨.stackUnderflow, ?_⟩)
    simp [binaryOp, popWord, Stack.pop, hs, bind, Except.bind, pure, Except.pure]
  · refine .inl (.inl ⟨.stackUnderflow, ?_⟩)
    simp [binaryOp, popWord, Stack.pop, hs, bind, Except.bind, pure, Except.pure]
  · have h : a.stack.val = x :: y :: rest := by rw [hs]
    rw [binaryOp_cons h, binaryOp_cons (evm := sh k a) h]
    exact rel_map_charge (fun _ => rfl)

theorem runMono_unaryOp (cost : Nat) (f : U256 → U256) :
    RunMono (fork := fork) (unaryOp cost f) := by
  intro a k
  rcases hs : a.stack with ⟨_ | ⟨x, rest⟩, hp⟩
  · refine .inl (.inl ⟨.stackUnderflow, ?_⟩)
    simp [unaryOp, popWord, Stack.pop, hs, bind, Except.bind, pure, Except.pure]
  · have h : a.stack.val = x :: rest := by rw [hs]
    rw [unaryOp_cons h, unaryOp_cons (evm := sh k a) h]
    exact rel_map_charge (fun _ => rfl)

theorem runMono_calldataload : RunMono (fork := fork) calldataloadStep := by
  intro a k
  rcases hs : a.stack with ⟨_ | ⟨x, rest⟩, hp⟩
  · refine .inl (.inl ⟨.stackUnderflow, ?_⟩)
    simp [calldataloadStep, popWord, Stack.pop, hs, bind, Except.bind, pure, Except.pure]
  · have h : a.stack.val = x :: rest := by rw [hs]
    rw [calldataloadStep_cons h, calldataloadStep_cons (evm := sh k a) h]
    exact rel_map_charge (fun _ => rfl)

theorem runMono_mstore : RunMono (fork := fork) mstoreStep := by
  intro a k
  rcases hs : a.stack with ⟨_ | ⟨x, _ | ⟨y, rest⟩⟩, hp⟩
  · refine .inl (.inl ⟨.stackUnderflow, ?_⟩)
    simp [mstoreStep, popWord, Stack.pop, hs, bind, Except.bind, pure, Except.pure]
  · refine .inl (.inl ⟨.stackUnderflow, ?_⟩)
    simp [mstoreStep, popWord, Stack.pop, hs, bind, Except.bind, pure, Except.pure]
  · have h : a.stack.val = x :: y :: rest := by rw [hs]
    rw [mstoreStep_cons h, mstoreStep_cons (evm := sh k a) h]
    exact rel_map_charge (fun _ => rfl)

theorem runMono_jumpdest : RunMono (fork := fork) jumpdestStep := by
  intro a k
  rw [jumpdestStep_eq, jumpdestStep_eq]
  exact rel_map_charge (fun _ => rfl)

theorem stack_of_chargeGas {e b : Evm fork Nat} {c : Nat} (h : chargeGas e c = .ok b) :
    b.stack = e.stack := by
  simp only [chargeGas, bind, Except.bind] at h
  split at h
  · cases h
  · simp only [pure, Except.pure, Except.ok.injEq] at h
    rw [← h]

theorem pushWord_full {e : Evm fork Nat} (h : e.stack.val.length = STACK_LIMIT) (x : U256) :
    pushWord e x = .error .stackOverflow := by
  simp [pushWord, Stack.push, h, bind, Except.bind]

theorem full_of_not_lt {e : Evm fork Nat} (h : ¬ e.stack.val.length < STACK_LIMIT) :
    e.stack.val.length = STACK_LIMIT := by
  have := e.stack.property; omega

/-- An instruction that reads a word of the frame that does not depend on the gas. -/
theorem runMono_readFrame (cost : Nat) (f : Evm fork Nat → U256)
    (hf : ∀ (a : Evm fork Nat) g, f { a with gas := g } = f a) :
    RunMono (readFrame cost f) := by
  intro a k
  by_cases room : a.stack.val.length < STACK_LIMIT
  · rw [readFrame_of_length_lt room, readFrame_of_length_lt (evm := sh k a) room]
    refine rel_map_charge (fun g' => ?_)
    simp only [sh, hf]
  · refine .inl (.inl ?_)
    simp only [readFrame, bind, Except.bind]
    split
    · exact ⟨_, rfl⟩
    · rename_i b hb
      rw [pushWord_full (by rw [stack_of_chargeGas hb]; exact full_of_not_lt room)]
      exact ⟨_, rfl⟩

theorem runMono_pushN (n : Fin 33) : RunMono (fork := fork) (pushN n) := by
  intro a k
  by_cases room : a.stack.val.length < STACK_LIMIT
  · rw [pushN_of_length_lt room, pushN_of_length_lt (evm := sh k a) room]
    exact rel_map_charge (fun _ => rfl)
  · refine .inl (.inl ?_)
    simp only [pushN, bind, Except.bind]
    split
    · exact ⟨_, rfl⟩
    · rename_i b hb
      rw [pushWord_full (by rw [stack_of_chargeGas hb]; exact full_of_not_lt room)]
      exact ⟨_, rfl⟩

theorem runMono_dupN (n : Fin 16) : RunMono (fork := fork) (dupN n) := by
  intro a k
  by_cases hroom : a.stack.val.length < STACK_LIMIT ∧ ∃ x, a.stack.val[n.val]? = some x
  · obtain ⟨room, x, hx⟩ := hroom
    rw [dupN_of_getElem? hx room, dupN_of_getElem? (evm := sh k a) hx room]
    exact rel_map_charge (fun _ => rfl)
  · refine .inl (.inl ?_)
    simp only [dupN, bind, Except.bind]
    split
    · exact ⟨_, rfl⟩
    · rename_i b hb
      have hs := stack_of_chargeGas hb
      split
      · exact ⟨_, rfl⟩
      · rename_i x hx
        rw [hs] at hx
        have room : ¬ a.stack.val.length < STACK_LIMIT := fun r => hroom ⟨r, x, hx⟩
        rw [pushWord_full (by rw [hs]; exact full_of_not_lt room)]
        exact ⟨_, rfl⟩

theorem runMono_swapN (n : Fin 16) : RunMono (fork := fork) (swapN n) := by
  intro a k
  rcases hs : a.stack with ⟨_ | ⟨top, rest⟩, hp⟩
  · refine .inl (.inl (error_of_charge (g := a.gas) (c := OPCODE_SWAP) ?_ ?_))
    · intro g' hc
      exact ⟨_, swapN_of_length_le hc (by rw [hs]; simp)⟩
    · intro e hc
      exact ⟨e, by simp [swapN, chargeGas, hc, bind, Except.bind]⟩
  · have h : a.stack.val = top :: rest := by rw [hs]
    rcases hx : rest[n.val]? with _ | x
    · refine .inl (.inl (error_of_charge (g := a.gas) (c := OPCODE_SWAP) ?_ ?_))
      · intro g' hc
        exact ⟨_, swapN_of_length_le hc (by
          rw [h, List.length_cons]; have := List.getElem?_eq_none_iff.mp hx; omega)⟩
      · intro e hc
        exact ⟨e, by simp [swapN, chargeGas, hc, bind, Except.bind]⟩
    · rw [swapN_of_getElem? h hx, swapN_of_getElem? (evm := sh k a) h hx]
      exact rel_map_charge (fun _ => rfl)

theorem runMono_jumpi : RunMono (fork := fork) jumpiStep := by
  intro a k
  rcases hs : a.stack with ⟨_ | ⟨d, _ | ⟨c, rest⟩⟩, hp⟩
  · refine .inl (.inl ⟨.stackUnderflow, ?_⟩)
    simp [jumpiStep, popWord, Stack.pop, hs, bind, Except.bind, pure, Except.pure]
  · refine .inl (.inl ⟨.stackUnderflow, ?_⟩)
    simp [jumpiStep, popWord, Stack.pop, hs, bind, Except.bind, pure, Except.pure]
  · simp only [jumpiStep, popWord, Stack.pop, hs, chargeGas, bind, Except.bind, pure,
      Except.pure, sh, GasMeter.charge]
    by_cases hg : a.gas < OPCODE_JUMPI
    · exact .inl (.inl ⟨.outOfGas, by simp [hg]⟩)
    · have hg' : ¬ a.gas + k < OPCODE_JUMPI := by omega
      have he : a.gas + k - OPCODE_JUMPI = a.gas - OPCODE_JUMPI + k := by omega
      simp only [hg, hg', ↓reduceIte, he]
      by_cases hc : c = 0
      · simp only [hc, ↓reduceIte]
        exact .inr ⟨_, rfl, rfl⟩
      · simp only [hc, ↓reduceIte]
        split
        · exact .inr ⟨_, rfl, rfl⟩
        · exact .inl (.inl ⟨_, rfl⟩)

theorem runMono_revert : RunMono (fork := fork) revertStep := by
  intro a k
  rw [revertStep_eq]
  rcases hr : returnStep a with e | c
  · exact .inl (.inl ⟨e, rfl⟩)
  · refine .inl (.inr ⟨_, rfl, ?_, by simp⟩)
    exact (haltWithOutput_stops hr).2


/-! ## The rules -/

section Rules

variable {code : ByteArray} {message : Message fork} {pc : Nat} {stack : List U256}
  {memory : ByteArray} {gas : Nat} {state : State.TransactionState} {substate : Substate}

/-- EthLib's `push_of_decode` over `StepG`. -/
theorem push_of_decodeG {byte : UInt8} {n : Fin 33} {word : U256} (hlt : pc < code.size)
    (hbyte : code[pc] = byte) (decoded : Op.decode byte = some (.push n)) (hn : n.val ≠ 0)
    (hword : pushData code pc n = word) (hgas : 3 ≤ gas) (hstack : stack.length < STACK_LIMIT) :
    HoareG fork (At code message pc stack memory gas state substate)
      (At code message (pc + (1 + n)) (word :: stack) memory (gas - 3) state substate) := by
  have hn' : n ≠ 0 := fun h => hn (by simp [h])
  apply At.ruleG hlt hbyte
    (ofByte_of_decode decoded (by simp [Op.since, hn', Fork.frontier_le])) (instruction_push n)
    (runMono_pushN n)
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
  push_of_decodeG hlt hbyte decoded hn hword hgas hstack

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
    (hgas : cost ≤ gas) (hstack : stack.length < STACK_LIMIT) :
    HoareG fork (At code message pc stack memory gas state substate)
      (At code message (pc + 1) (word :: stack) memory (gas - cost) state substate) := by
  apply At.ruleG hlt hbyte decoded hrun (runMono_readFrame cost f hf)
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
    (hrun : instruction (Meter := Nat) fork op = some (binaryOp cost f)) (hgas : cost ≤ gas) :
    HoareG fork (At code message pc (x :: y :: rest) memory gas state substate)
      (At code message (pc + 1) (f x y :: rest) memory (gas - cost) state substate) := by
  apply At.ruleG hlt hbyte decoded hrun (runMono_binaryOp cost f)
  rintro evm ⟨hcode, hj, hm, hpc, hst, hmem, hg, hrun, herr, hout, hs, hss⟩
  rw [binaryOp_cons hst, charge_nat (by rw [hg]; exact hgas)]
  exact ⟨_, rfl, hcode, hj, hm, by simp [hpc], rfl, hmem, by simp [hg], hrun, herr, hout, hs, hss⟩

/-- EthLib's `unary` over `StepG`. -/
theorem unaryG {byte : UInt8} {op : Op} {cost : Nat} {f : U256 → U256} {x : U256}
    {rest : List U256} (hlt : pc < code.size) (hbyte : code[pc] = byte)
    (decoded : Op.ofByte fork byte = some op)
    (hrun : instruction (Meter := Nat) fork op = some (unaryOp cost f)) (hgas : cost ≤ gas) :
    HoareG fork (At code message pc (x :: rest) memory gas state substate)
      (At code message (pc + 1) (f x :: rest) memory (gas - cost) state substate) := by
  apply At.ruleG hlt hbyte decoded hrun (runMono_unaryOp cost f)
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

/-- EthLib's `calldataload` over `StepG`. -/
theorem calldataloadG {start : U256} {rest : List U256} (hlt : pc < code.size)
    (hbyte : code[pc] = 0x35) (hgas : 3 ≤ gas) :
    HoareG fork (At code message pc (start :: rest) memory gas state substate)
      (At code message (pc + 1) (loadWord message.data start.toNat 32 :: rest) memory
        (gas - 3) state substate) := by
  apply At.ruleG hlt hbyte (ofByte_of_decode (op := .calldataload) rfl (Fork.frontier_le _))
    instruction_calldataload runMono_calldataload
  rintro evm ⟨hcode, hj, hm, hpc, hst, hmem, hg, hrun, herr, hout, hs, hss⟩
  rw [calldataloadStep_cons hst, charge_nat (by rw [hg]; exact hgas)]
  exact ⟨_, rfl, hcode, hj, hm, by simp [hpc], by simp [hm], hmem,
    by simp [hg, OPCODE_CALLDATALOAD, VERY_LOW], hrun, herr, hout, hs, hss⟩

/-- EthLib's `mstore` over `StepG`. -/
theorem mstoreG {start value : U256} {rest : List U256} (hlt : pc < code.size)
    (hbyte : code[pc] = 0x52)
    (hgas : 3 + (extendMemory memory.size [(start, 32)]).cost ≤ gas) :
    HoareG fork (At code message pc (start :: value :: rest) memory gas state substate)
      (At code message (pc + 1) rest
        (memoryWrite (memoryExtend memory (extendMemory memory.size [(start, 32)]).expandBy)
          start.toNat (wordBytes value))
        (gas - (3 + (extendMemory memory.size [(start, 32)]).cost)) state substate) := by
  apply At.ruleG hlt hbyte (ofByte_of_decode (op := .mstore) rfl (Fork.frontier_le _))
    instruction_mstore runMono_mstore
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

/-- `repc` over `StepG`. -/
theorem repcG {pc pc' : Nat} {s : List U256} {m : ByteArray} {g : Nat}
    {st : State.TransactionState} {ss : Substate} (h : pc = pc') :
    HoareG fork (At code message pc s m g st ss) (At code message pc' s m g st ss) := by
  subst h
  exact Triple.of_imp fun _ h => h

/-- `Hoare.gas_eq` over `StepG`. -/
theorem HoareG.gas_eq {P : Evm fork Nat → Prop} {pc : Nat} {s : List U256} {m : ByteArray}
    {g g' : Nat} {st : State.TransactionState} {ss : Substate}
    (h : HoareG fork P (At code message pc s m g st ss)) (hg : g = g') :
    HoareG fork P (At code message pc s m g' st ss) := hg ▸ h

end Rules

end UsdtVerify.Gas
