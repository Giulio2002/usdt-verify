import UsdtVerify.Evm.Frame
import UsdtVerify.Evm.Route
import EthLib.Execution.Proofs.Evm.Logic.Callee
import EthLib.Execution.Proofs.Evm.Instructions.MemoryData

/-!
# Concrete message runners

For any code. `answerRunner` keeps the storage of every account. It shows that a runner
assumption of the form `KeepsOn runChild (FromTo C ua) R` (EthLib's `KeepsOn` over every message
from `C` to `ua`) can hold when `R` holds between two states with the same storage at `C`
(`SameStore C`).

- `answerRunner f`: ends every message at once with no error, gas 0, the output `f caller msg`,
  and the caller's state (`answerRunner_ok`). `answerRunner_keeps`.

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

/-- Every message from `C` to `ua` (round 49: the set over which the removed local `Keeps` asked
its relation, now given to EthLib's `KeepsOn`). -/
def FromTo (C ua : Address) (_ : Evm fork Nat) (msg : Message fork) : Prop :=
  msg.caller = C ∧ msg.currentTarget = ua

/-- A call of EthLib's `SentVia` from `message` to `ua` is a message from its current target to
`ua`: so `KeepsOn … (FromTo message.currentTarget ua)` gives `KeepsOn … (SentVia message S ua)`
(`KeepsOn.mono`). -/
theorem fromTo_of_sentVia {message : Message fork} {S : State.TransactionState} {ua : Address}
    {caller : Evm fork Nat} {msg : Message fork} (h : SentVia message S ua caller msg) :
    FromTo message.currentTarget ua caller msg := by
  obtain ⟨-, -, -, -, -, hmc, hmt, -⟩ := h
  exact ⟨hmc, hmt⟩

open Classical in

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
    KeepsOn (answerRunner (bound := bound) f) (FromTo C ua) (SameStore C) := by
  intro caller msg lt child h _ _ n
  rw [(answerRunner_ok h).2.1]

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
