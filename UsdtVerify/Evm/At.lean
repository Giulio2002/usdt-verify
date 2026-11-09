import EthLib.Execution.Proofs.Evm.Logic.Rules
import EthLib.Execution.Proofs.Evm.Logic.Steps
import EthLib.Execution.Proofs.Evm.Logic.Fault
import EthLib.Execution.Proofs.Evm.Logic.Callee

/-!
# A running frame that does not name its return data

EthLib's `Logic.At` (from EthLib #1351) names every field of a frame, the return data included.
The rules of this repository were written when `At` named every field but the return data, and
no theorem of this repository constrains the return data of a frame. `UsdtVerify.At` keeps that
form: the same twelve conditions, with no condition on the return data. Inside the namespace
`UsdtVerify`, the name `At` is this predicate.

- `At.toLogic`, `At.ofLogic`, `At.iff_logic`: `At` holds of a frame when EthLib's `At` holds with
  the return data of that frame.
- `liftAt`, `liftPre`: an EthLib triple from `Logic.At … rd` (to `Logic.At … rd`), for every
  return data `rd`, is a triple from `At` (to `At`), over any step relation. `lowerPre`: a triple
  from `At` is a triple from `Logic.At … rd`, for every `rd`.
- `At.startFrame`: EthLib's `at_startFrame` (the frame that a message starts), for `At`.
- `meets_of_specAt`: EthLib's `meets_of_spec` (the runner of the interpreter meets the
  specification of a callee), for a specification from `At`.
- `At.rule`: EthLib's `At.rule` for `At`.
- `At.extcodesize`, `At.gas_rule`, `At.caller`, `At.reshape`: EthLib's `extcodesize_of_berlin_le`
  (EXTCODESIZE at every fork from Berlin), `gas_rule` (GAS), `caller` (CALLER) and `reshape`
  (equal stack, memory and gas), for `At`. `At.stop`, `At.revert`, `At.invalid_fe`: EthLib's
  `stop`, `revert` and `invalid_fe`, from `At`.

The other opcode rules of this repository are proved from `At.rule` and `Gas.At.ruleG`
(Evm/Gas.lean, Evm/GasRules.lean), so they need no lift.
-/

namespace UsdtVerify

open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm

variable {fork : Fork}

/-- A running frame of a code, at a program counter, with a stack, a memory and some gas, its
flags of jump destinations, its message, its state and substate, no error and an empty output.
Its return data is any. -/
def At (code : ByteArray) (message : Message fork) (pc : Nat) (stack : List U256)
    (memory : ByteArray) (gas : Nat) (state : State.TransactionState) (substate : Substate)
    (evm : Evm fork Nat) : Prop :=
  evm.code = code ∧ evm.validJumpDestinations = validJumpDestinations code ∧
    evm.message = message ∧ evm.pc = pc ∧ evm.stack.val = stack ∧ evm.memory = memory ∧
    evm.gas = gas ∧ evm.running = true ∧ evm.error = none ∧ evm.output = .empty ∧
    evm.state = state ∧ evm.substate = substate

variable {code : ByteArray} {message : Message fork} {pc : Nat} {stack : List U256}
  {memory : ByteArray} {gas : Nat} {state : State.TransactionState} {substate : Substate}
  {evm : Evm fork Nat}

/-- `At` gives EthLib's `At` with the return data of the frame. -/
theorem At.toLogic (h : At code message pc stack memory gas state substate evm) :
    Logic.At code message pc stack memory gas state substate evm.returnData evm :=
  let ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := h
  ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, rfl⟩

/-- EthLib's `At`, with any return data, gives `At`. -/
theorem At.ofLogic {rd : ByteArray}
    (h : Logic.At code message pc stack memory gas state substate rd evm) :
    At code message pc stack memory gas state substate evm :=
  let ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, _⟩ := h
  ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩

/-- `At` holds exactly when EthLib's `At` holds with the return data of the frame. -/
theorem At.iff_logic :
    At code message pc stack memory gas state substate evm ↔
      Logic.At code message pc stack memory gas state substate evm.returnData evm :=
  ⟨At.toLogic, At.ofLogic⟩

/-- A triple from EthLib's `At` with every return data is a triple from `At`. -/
theorem liftPre {R : Evm fork Nat → Evm fork Nat → Prop} {Q : Evm fork Nat → Prop}
    (h : ∀ rd, Logic.Triple R (Logic.At code message pc stack memory gas state substate rd) Q) :
    Logic.Triple R (At code message pc stack memory gas state substate) Q :=
  fun evm hp => h evm.returnData evm hp.toLogic

/-- A triple between EthLib's `At` frames with the same return data, for every return data, is a
triple between `At` frames. -/
theorem liftAt {R : Evm fork Nat → Evm fork Nat → Prop} {code' : ByteArray}
    {message' : Message fork} {pc' : Nat} {stack' : List U256} {memory' : ByteArray} {gas' : Nat}
    {state' : State.TransactionState} {substate' : Substate}
    (h : ∀ rd, Logic.Triple R (Logic.At code message pc stack memory gas state substate rd)
      (Logic.At code' message' pc' stack' memory' gas' state' substate' rd)) :
    Logic.Triple R (At code message pc stack memory gas state substate)
      (At code' message' pc' stack' memory' gas' state' substate') :=
  fun evm hp =>
    let ⟨after, hr, hq⟩ := h evm.returnData evm hp.toLogic
    ⟨after, hr, At.ofLogic hq⟩

/-- A triple from `At` is a triple from EthLib's `At` with any return data. -/
theorem lowerPre {R : Evm fork Nat → Evm fork Nat → Prop} {Q : Evm fork Nat → Prop}
    {rd : ByteArray}
    (h : Logic.Triple R (At code message pc stack memory gas state substate) Q) :
    Logic.Triple R (Logic.At code message pc stack memory gas state substate rd) Q :=
  fun evm hp => h evm (At.ofLogic hp)

/-- The frame that a message starts is a running frame of its code, at 0, with nothing on it
(EthLib's `at_startFrame`, for `At`). -/
theorem At.startFrame (hcode : message.code = code) (state : State.TransactionState)
    (substate : Substate) :
    At code message 0 [] .empty message.gas state substate
      (startFrame message state substate (GasMeter.start message.gas message.reservoir)) :=
  At.ofLogic (Logic.at_startFrame hcode state substate)

/-- The runner of the interpreter meets the specification of the code of a callee (EthLib's
`meets_of_spec`, for a specification from `At`). -/
theorem meets_of_specAt
    {G : Message fork → State.TransactionState → Substate → Prop}
    {Q : Message fork → State.TransactionState → Substate → Evm fork Nat → Prop}
    (hspec : ∀ message state substate, message.code = code → G message state substate →
      Logic.Spec fork
        (At code message 0 [] .empty message.gas (startState fork message state) substate)
        (Q message state substate))
    (bound : Nat) :
    Logic.Meets (Logic.RunsAs code G Q) (Logic.processRunner fork bound) :=
  Logic.meets_of_spec (fun message state substate hcode hg =>
    lowerPre (hspec message state substate hcode hg)) bound

/-- The rule of an opcode, from the instruction that its byte runs on a frame of the code
(EthLib's `At.rule`, for `At`). -/
theorem At.rule {byte : UInt8} {op : Op}
    {run : Evm fork Nat → Except EvmError (Evm fork Nat)} {post : Evm fork Nat → Prop}
    (hlt : pc < code.size) (hbyte : code[pc] = byte) (decoded : Op.ofByte fork byte = some op)
    (hrun : instruction fork op = some run)
    (h : ∀ evm, At code message pc stack memory gas state substate evm →
      ∃ after, run evm = .ok after ∧ post after) :
    Logic.Hoare fork (At code message pc stack memory gas state substate) post :=
  liftPre fun _ => Logic.At.rule hlt hbyte decoded hrun fun evm hp => h evm (At.ofLogic hp)

/-- From Berlin (Glamsterdam included), EXTCODESIZE pushes the size of the code of an account:
EthLib's `extcodesize_of_berlin_le`, for `At`. -/
theorem At.extcodesize (hfork : .berlin ≤ fork) {word : U256} {rest : List U256} {cold : Bool}
    {c : ByteArray} (hlt : pc < code.size) (hbyte : code[pc] = 0x3b)
    (hcode : state.getCode (state.getAccount (EthLib.Base.toAddressMasked word)).codeHash = .ok c)
    (hcold : decide (EthLib.Base.toAddressMasked word ∉ substate.accessedAddresses) = cold)
    (hgas : externalBaseCost fork cold ≤ gas) :
    Logic.Hoare fork (At code message pc (word :: rest) memory gas state substate)
      (At code message (pc + 1) (BitVec.ofNat 256 c.size :: rest) memory
        (gas - externalBaseCost fork cold)
        (state.recordAccountRead (EthLib.Base.toAddressMasked word))
        { substate with
          accessedAddresses :=
            substate.accessedAddresses.insert (EthLib.Base.toAddressMasked word) }) :=
  liftAt fun _ => Logic.extcodesize_of_berlin_le hfork hlt hbyte hcode hcold hgas

/-- GAS pushes the gas left after its price of 2: EthLib's `gas_rule`, for `At`. -/
theorem At.gas_rule (hlt : pc < code.size) (hbyte : code[pc] = 0x5a) (hgas : 2 ≤ gas)
    (hstack : stack.length < STACK_LIMIT) :
    Logic.Hoare fork (At code message pc stack memory gas state substate)
      (At code message (pc + 1) (BitVec.ofNat 256 (gas - 2) :: stack) memory (gas - 2) state
        substate) :=
  liftAt fun _ => Logic.gas_rule hlt hbyte hgas hstack

/-- CALLER pushes the address of the caller for 2 gas: EthLib's `caller`, for `At`. -/
theorem At.caller (hlt : pc < code.size) (hbyte : code[pc] = 0x33) (hgas : 2 ≤ gas)
    (hstack : stack.length < STACK_LIMIT) :
    Logic.Hoare fork (At code message pc stack memory gas state substate)
      (At code message (pc + 1) (message.caller.toU256 :: stack) memory (gas - 2) state
        substate) :=
  liftAt fun _ => Logic.caller hlt hbyte hgas hstack

/-- A frame is also a frame with an equal stack, memory and gas: EthLib's `reshape`, for `At`. -/
theorem At.reshape {s s' : List U256} {m m' : ByteArray} {g g' : Nat}
    (hs : s = s') (hm : m = m') (hg : g = g') :
    Logic.Hoare fork (At code message pc s m g state substate)
      (At code message pc s' m' g' state substate) :=
  liftAt fun _ => Logic.reshape hs hm hg

/-- STOP halts with no output: EthLib's `stop`, from `At`. -/
theorem At.stop (hlt : pc < code.size) (hbyte : code[pc] = 0x00) :
    Logic.Spec fork (At code message pc stack memory gas state substate)
      (Logic.Halted false .empty gas state substate) :=
  liftPre fun _ => Logic.stop hlt hbyte

/-- REVERT halts with the bytes of memory it names: EthLib's `revert`, from `At`. -/
theorem At.revert (hfork : .byzantium ≤ fork) {start size : U256} {rest : List U256}
    (hlt : pc < code.size) (hbyte : code[pc] = 0xfd)
    (hgas : (extendMemory memory.size [(start, size)]).cost ≤ gas) :
    Logic.Spec fork (At code message pc (start :: size :: rest) memory gas state substate)
      (Logic.Halted true
        (memoryReadBytes (memoryExtend memory (extendMemory memory.size [(start, size)]).expandBy)
          start.toNat size.toNat)
        (gas - (extendMemory memory.size [(start, size)]).cost) state substate) :=
  liftPre fun _ => Logic.revert hfork hlt hbyte hgas

/-- The byte `0xfe` halts the frame as an invalid opcode: EthLib's `invalid_fe`, from `At`. -/
theorem At.invalid_fe (hlt : pc < code.size) (hbyte : code[pc] = 0xfe) :
    Logic.Spec fork (At code message pc stack memory gas state substate)
      (Logic.Faulted (.invalidOpcode 0xfe) state substate) :=
  liftPre fun _ => Logic.invalid_fe hlt hbyte

end UsdtVerify
