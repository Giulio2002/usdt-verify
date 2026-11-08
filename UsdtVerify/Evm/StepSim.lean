import UsdtVerify.Evm.CallSim

/-!
# One step over the two meters, at EXTCODESIZE, GAS and CALL too (round 38)

`Meter.step_sim` relates one step over `StateGasMeter` (reservoir 0, no refill at an SSTORE) to
one step over `Nat` at the opcodes of `simulated`. The deprecated paths also run EXTCODESIZE, GAS
and CALL. Here:

- `SimAtX x`: the opcode at `x` is `SimAt`, or EXTCODESIZE, or GAS.
- `step_simX`: `step_sim` for a frame whose `toNat` is `SimAtX`. EXTCODESIZE and GAS charge only
  execution gas, and GAS pushes the execution gas left, which is the gas of the `toNat` frame.
- `CallX x`: the opcode at `x` is CALL, with 0 as the value on the stack and the code of the
  called address found in the state.
- `step_callX`: from a frame with reservoir 0 whose `toNat` is `CallX`, from Berlin: the step over
  `StateGasMeter` fails or halts the frame with an error (`StepBadS`), or both steps give the same
  error or corresponding next frames (`CorrS`, at the greatest depth), or both send the same
  message (`CallCorr`): the caller over `Nat` is the `toNat` of the caller over `StateGasMeter`,
  whose reservoir is 0, and both resume through EthLib's `resumeCall`. The message carries the
  reservoir of the frame, 0 (stated in `CallCorr` since round 41).
-/

namespace UsdtVerify.Meter

open EthLib.Base (Fork U256 toAddressMasked Address)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open UsdtVerify.Gas
open UsdtVerify.Complete
open GasCosts

variable {fork : Fork}

/-- The opcode at the program counter of `x` is `SimAt`, or EXTCODESIZE, or GAS. -/
def SimAtX (x : Evm fork Nat) : Prop :=
  SimAt x ∨ ∃ h : x.pc < x.code.size, Op.ofByte fork x.code[x.pc] = some .extcodesize ∨
    Op.ofByte fork x.code[x.pc] = some .gas

theorem instruction_extcodesizeS :
    instruction (Meter := StateGasMeter) fork .extcodesize = some extcodesizeStep := rfl

theorem instruction_extcodesizeN :
    instruction (Meter := Nat) fork .extcodesize = some extcodesizeStep := rfl

theorem instruction_gasN : instruction (Meter := Nat) fork .gas =
    some (readFrame OPCODE_GAS fun evm => BitVec.ofNat 256 (GasMeter.gasLeft evm.gas)) := rfl

theorem instruction_gasS : instruction (Meter := StateGasMeter) fork .gas =
    some (readFrame OPCODE_GAS fun evm => BitVec.ofNat 256 (GasMeter.gasLeft evm.gas)) := rfl

/-- **One step, EXTCODESIZE and GAS included.** `step_sim` for a frame whose `toNat` is
`SimAtX`. -/
theorem step_simX {m : Evm fork StateGasMeter} (hr : m.gas.reservoir = 0)
    (hp : SimAtX (toNat m)) (hnr : NoRefillAt m) :
    CorrS (step fork m) (step fork (toNat m)) := by
  rcases hp with hp | ⟨hlt, hop | hop⟩
  · exact step_sim hr hp hnr
  · rw [step_of_instruction (evm := m) hlt hop instruction_extcodesizeS,
      step_of_instruction hlt hop instruction_extcodesizeN]
    exact corrS_map (lifts_extcodesizeStep.corr hr)
  · rw [step_of_instruction (evm := m) hlt hop instruction_gasS,
      step_of_instruction hlt hop instruction_gasN]
    exact corrS_map (lifts_gasStep.corr hr)

/-- The opcode at the program counter of `x` is CALL, the value on the stack is 0, and the state
holds the code of the called address. -/
def CallX (x : Evm fork Nat) : Prop :=
  ∃ h : x.pc < x.code.size, Op.ofByte fork x.code[x.pc] = some .call ∧
    ∃ g a i isz o osz rest c, x.stack.val = g :: a :: 0 :: i :: isz :: o :: osz :: rest ∧
      x.state.getCode (x.state.getAccount (toAddressMasked a)).codeHash = .ok c

/-- Two steps that send the same message: the caller over `Nat` is the `toNat` of the caller over
`StateGasMeter`, whose reservoir is 0, the message has reservoir 0, and both resume through
`resumeCall`. -/
def CallCorr (rS : Except EvmError (StepResult fork StateGasMeter))
    (rN : Except EvmError (StepResult fork Nat)) : Prop :=
  ∃ caller msg o osz, rS = .ok (.child caller msg (resumeCall fork caller 0 o osz)) ∧
    rN = .ok (.child (toNat caller) msg (resumeCall fork (toNat caller) 0 o osz)) ∧
    caller.gas.reservoir = 0 ∧ msg.reservoir = 0

/-- Every call has a route, or, from Pectra, delegates to an address whose code is not found. -/
theorem routes_or_missing (st : State.TransactionState) (c : ByteArray) :
    (∃ r, Routes fork st c r) ∨ ∃ d e, .pectra ≤ fork ∧ delegatedAddress c = some d ∧
      st.getCode (st.getAccount d).codeHash = .error e := by
  by_cases hpec : Fork.pectra ≤ fork
  · rcases hd : delegatedAddress c with _ | d
    · exact .inl ⟨none, fun _ => hd⟩
    · rcases hdc : st.getCode (st.getAccount d).codeHash with e | c'
      · exact .inr ⟨d, e, hpec, rfl, hdc⟩
      · exact .inl ⟨some (d, c'), hpec, hd, hdc⟩
  · exact .inl ⟨none, fun h => absurd h hpec⟩

/-- **The step of a CALL.** From Berlin, from a frame of `StateGasMeter` with reservoir 0 whose
`toNat` is `CallX`: the step fails or halts the frame with an error, or the two steps give the same
error or corresponding next frames, or they send the same message (`CallCorr`). -/
theorem step_callX (hfork : .berlin ≤ fork) {m : Evm fork StateGasMeter}
    (hr : m.gas.reservoir = 0) (hc : CallX (toNat m)) :
    StepBadS (step fork m) ∨ CorrS (step fork m) (step fork (toNat m)) ∨
      CallCorr (step fork m) (step fork (toNat m)) := by
  obtain ⟨hlt, hop, g, a, i, isz, o, osz, rest, c, hst, hcode⟩ := hc
  have hS : step fork m = callStep .call m :=
    step_of_messageInstruction (Meter := StateGasMeter) hlt hop rfl rfl
  have hN : step fork (toNat m) = callStep .call (toNat m) :=
    step_of_messageInstruction hlt hop instruction_call messageInstruction_call
  rw [hS, hN]
  change m.stack.val = _ at hst
  change m.state.getCode (m.state.getAccount (toAddressMasked a)).codeHash = .ok c at hcode
  rcases routes_or_missing (fork := fork) m.state c with ⟨r, hroute⟩ | ⟨d, e, hpec, hd, hmiss⟩
  · by_cases hlow : m.gas.gasLeft <
        callBaseCost fork (decide (toAddressMasked a ∉ m.substate.accessedAddresses)) +
        routeCost fork (m.substate.accessedAddresses.insert (toAddressMasked a)) r +
        (extendMemory m.memory.size [(i, isz), (o, osz)]).cost
    · exact .inl (callStep_low_rS hfork hst hcode hroute hlow)
    have hgas := Nat.le_of_not_lt hlow
    by_cases hdeep : STACK_DEPTH_LIMIT < m.message.depth + 1
    · obtain ⟨after, h1, h2, h3⟩ := callStep_deep_sim hfork hr hst hcode hroute hdeep hgas
      exact .inr (.inl (.inr ⟨after, h1, h2, .inl h3⟩))
    · obtain ⟨caller, msg, h1, h2, h3⟩ :=
        callStep_child_sim hfork hr hst hcode hroute (by omega) hgas
      obtain ⟨c', msg', h1', -, hmr⟩ :=
        callStep_child_res0 hfork hr hst hcode hroute (by omega) hgas
      cases h1.symm.trans h1'
      exact .inr (.inr ⟨caller, msg, o, osz, h1, h2, h3, hmr⟩)
  · exact .inl (callStep_missingS hfork hst hcode hpec hd hmiss)

end UsdtVerify.Meter
