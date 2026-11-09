import UsdtVerify.Evm.Keeps
import EthLib.Execution.Proofs.Evm.Logic.Callee
import EthLib.Execution.Proofs.Evm.Instructions.MemoryData

/-!
# Concrete message runners

For any code. `stopRunner` and `answerRunner` keep the storage of every account; they show that a runner assumption of the form `Keeps runChild C ua R` can hold
when `R` holds between two states with the same storage at `C` (`SameStore C`).

- `stopRunner fork bound ua`: on a message to `ua` whose code is the one byte STOP
  (`STOP_CODE`), that has a target, moves no value and calls no precompile (`StopMsg`), it is
  EthLib's `processRunner`; it also is on every message to another address; any other message
  to `ua` it fails with `outOfGas`.
  `stopRunner_ok`: a message to `ua` that it ends returns no error, in the state that
  `startState` gives (the caller's state, with the target touched before Paris).
  `stopRunner_keeps`: every message to `ua` it ends keeps the storage of every account.
- `answerRunner f`: ends every message at once with no error, gas 0, the output `f caller msg`,
  and the caller's state (`answerRunner_ok`). `answerRunner_keeps`.
- `answerRunnerAt S f` (round 26): the same, but every message ends in the given state `S`
  (`answerRunnerAt_ok`); it does not keep storage in general.
- `failRunner e` (round 26): fails on every message with the error `e`.

`Keeps` asks its relation of every message to `ua` that the runner ends with no error, whatever
the code of the message; `stopRunner` meets it by failing the messages to `ua` that do not run
STOP. Nothing here is claimed of `processRunner` on those messages.

`loadWord_append_wordBytes`: the word at `A.size` of `A ++ wordBytes w` is `w`.
-/

namespace UsdtVerify

open EthLib.Base (Fork U256 Address byteAt natToBytes)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic

variable {fork : Fork} {bound : Nat}

/-- `S'` has the storage of `S` at `C`: every slot of `C` holds the same word. -/
def SameStore (C : Address) (S S' : State.TransactionState) : Prop :=
  ∀ n, storageAt S' C n = storageAt S C n

/-- The code of one byte, STOP. -/
def STOP_CODE : ByteArray := ⟨#[0x00]⟩

/-- A message to `ua` that `stopRunner` passes to `processRunner`: its code is STOP, it has a
target, it moves no value and calls no precompile. A message to another address is not
restricted. -/
def StopMsg (fork : Fork) (ua : Address) (msg : Message fork) : Prop :=
  msg.currentTarget = ua → msg.code = STOP_CODE ∧ msg.target.isSome = true ∧
    ¬(msg.shouldTransferValue = true ∧ msg.value ≠ 0) ∧ precompileAddress fork msg = none

open Classical in
/-- EthLib's `processRunner` on the messages of `StopMsg`; any other message (to `ua`) fails with
`outOfGas`. -/
noncomputable def stopRunner (fork : Fork) (bound : Nat) (ua : Address) :
    MessageRunner fork Nat bound :=
  fun caller msg lt =>
    if StopMsg fork ua msg then processRunner fork bound caller msg lt else .error .outOfGas

/-- `startState` keeps the storage of every account. -/
theorem storageAt_startState (msg : Message fork) (S : State.TransactionState) (C : Address)
    (n : U256) : storageAt (startState fork msg S) C n = storageAt S C n := by
  unfold startState
  split
  · unfold State.TransactionState.touchAccount
    split <;> rfl
  · rfl

/-- A message to `ua` that `stopRunner` ends: no error, and the state of `startState`. -/
theorem stopRunner_ok {ua : Address} {caller : Evm fork Nat} {msg : Message fork}
    {lt : msg.gas < bound} {child : { c : Evm fork Nat // GasMeter.gasHeld c.gas ≤ msg.gas }}
    (h : stopRunner fork bound ua caller msg lt = .ok child) (ht : msg.currentTarget = ua) :
    child.1.error = none ∧ child.1.state = startState fork msg caller.state := by
  unfold stopRunner at h
  split at h
  · rename_i hs
    obtain ⟨hcode, htarget, hnv, hnp⟩ := hs ht
    obtain ⟨target, htg⟩ := Option.isSome_iff_exists.mp htarget
    simp only [processRunner, htg] at h
    obtain ⟨stopped, hq, hmap⟩ := processMessage_of_spec (state := caller.state)
      (substate := caller.substate.child)
      (At.stop (code := STOP_CODE) (pc := 0) (by decide) rfl) hnv hnp
      (At.startFrame hcode _ _)
    rw [h] at hmap
    have hc : child.1 = rollbackOnError caller.state stopped := by
      simpa [Except.map] using hmap
    obtain ⟨-, herr, -, -, hst, -⟩ := hq
    have herr' : stopped.error = none := by simpa using herr
    rw [hc, rollbackOnError_of_error_eq_none herr']
    exact ⟨herr', hst⟩
  · cases h

/-- Every message to `ua` that `stopRunner` ends with no error keeps the storage of every
account `C`. -/
theorem stopRunner_keeps (ua C : Address) :
    Keeps (stopRunner fork bound ua) C ua (SameStore C) := by
  intro caller msg lt child h _ ht _ n
  rw [(stopRunner_ok h ht).2, storageAt_startState]

/-- The runner that ends every message at once with no error, gas 0, the output
`f caller msg` and the caller's state. -/
def answerRunner (f : Evm fork Nat → Message fork → ByteArray) : MessageRunner fork Nat bound :=
  fun caller msg _ =>
    .ok ⟨{ caller with
      gas := (0 : Nat)
      output := f caller msg
      error := none
      running := false }, Nat.zero_le _⟩

theorem answerRunner_ok {f : Evm fork Nat → Message fork → ByteArray} {caller : Evm fork Nat}
    {msg : Message fork} {lt : msg.gas < bound}
    {child : { c : Evm fork Nat // GasMeter.gasHeld c.gas ≤ msg.gas }}
    (h : answerRunner f caller msg lt = .ok child) :
    child.1.error = none ∧ child.1.state = caller.state ∧ child.1.output = f caller msg := by
  simp only [answerRunner, Except.ok.injEq] at h
  subst h
  exact ⟨rfl, rfl, rfl⟩

/-- Every message that `answerRunner f` ends keeps the storage of every account `C`. -/
theorem answerRunner_keeps (f : Evm fork Nat → Message fork → ByteArray) (ua C : Address) :
    Keeps (answerRunner (bound := bound) f) C ua (SameStore C) := by
  intro caller msg lt child h _ _ _ n
  rw [(answerRunner_ok h).2.1]

/-- The runner that fails on every message with the error `e` (round 26). -/
def failRunner (e : EvmError) : MessageRunner fork Nat bound := fun _ _ _ => .error e

/-- The runner that ends every message at once with no error, gas 0, the output `f caller msg`
and the state `S` (round 26: a runner whose ended frames all have the state `S`). -/
def answerRunnerAt (S : State.TransactionState) (f : Evm fork Nat → Message fork → ByteArray) :
    MessageRunner fork Nat bound :=
  fun caller msg _ =>
    .ok ⟨{ caller with
      gas := (0 : Nat)
      output := f caller msg
      error := none
      running := false
      state := S }, Nat.zero_le _⟩

theorem answerRunnerAt_ok {S : State.TransactionState}
    {f : Evm fork Nat → Message fork → ByteArray} {caller : Evm fork Nat}
    {msg : Message fork} {lt : msg.gas < bound}
    {child : { c : Evm fork Nat // GasMeter.gasHeld c.gas ≤ msg.gas }}
    (h : answerRunnerAt S f caller msg lt = .ok child) :
    child.1.error = none ∧ child.1.state = S ∧ child.1.output = f caller msg ∧ child.1.gas = 0 := by
  simp only [answerRunnerAt, Except.ok.injEq] at h
  subst h
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- The word at `A.size` of `A ++ wordBytes w` is `w`. -/
theorem loadWord_append_wordBytes (A : ByteArray) (w : U256) :
    loadWord (A ++ wordBytes w) A.size 32 = w := by
  have hw := size_wordBytes w
  have hl : (List.range 32).map (fun i => byteAt (A ++ wordBytes w) (A.size + i)) =
      (wordBytes w).data.toList := by
    apply List.ext_getElem
    · simp only [List.length_map, List.length_range, Array.length_toList]
      rw [ByteArray.size_data, hw]
    · intro i h1 h2
      simp only [List.getElem_map, List.getElem_range, Array.getElem_toList]
      have hi : i < 32 := by simpa using h1
      have hlt : A.size + i < (A ++ wordBytes w).size := by
        rw [ByteArray.size_append, hw]; omega
      simp only [byteAt, hlt, ↓reduceDIte]
      rw [ByteArray.getElem_append_right (by omega)]
      simp only [Nat.add_sub_cancel_left]
      rfl
  have bytes : (wordBytes w).data.toList = natToBytes 32 w.toNat :=
    EthLib.Base.U256.toList_toBeBytes w
  have small : w.toNat < 256 ^ 32 := by
    have := w.isLt
    rwa [show (2 : Nat) ^ 256 = 256 ^ 32 by decide] at this
  rw [loadWord, bufferRead, hl, bytes, EthLib.Base.bytesToNat_natToBytes_of_lt small]
  apply BitVec.eq_of_toNat_eq
  simp

end UsdtVerify
