import UsdtVerify.Evm.Runners
import UsdtVerify.Usdt.Security.Supply

/-!
# Sanity: runners that meet the runner assumptions

The theorems deprecated or not take named assumptions on the message runner when deprecated:
`KeepsInv` (`inv_call_ns`, `inv_call_all`), `HonestBalance` (deprecated destroyBlackFunds),
`StaticKeeps` (static frames, `inv_call_all`), and `KeepsSlots`, `KeepsBal`, `KeepsListed`,
`KeepsAllow`, `KeepsSupply` (the security theorems `*_call_all`, `*_seq_all`).
This file shows that each of them holds for some runner, so none of them is false for every runner.

- `keeps*_of_same`: a runner whose messages from `C` to `ua` keep the storage of `C`
  (`Keeps … (SameStore C)`) meets `KeepsSlots`, `KeepsBal`, `KeepsListed`, `KeepsAllow`,
  `KeepsSupply` and `KeepsInv`.
- `stop_keeps_all`: `stopRunner fork bound ua` (Evm/Runners.lean: EthLib's `processRunner` on the
  messages to `ua` whose code is the one byte STOP, with a target, no value and no precompile; any
  other message to `ua` fails) meets all six, for every `C`, at every fork.
  `stop_staticKeeps`: from Paris it meets `StaticKeeps` (EthLib's `processMessage_static`).
- `balRunner`: the `answerRunner` that answers every message with the 32 bytes of the word at
  slot `keccak(x ++ 2)` of the message's caller in the caller's state, `x` the word at byte 4 of
  the message's data (`balances[x]` when the caller is `C`), and keeps the state.
  `bal_keeps_all`: it meets the six assumptions above; `bal_staticKeeps`: `StaticKeeps` at every
  fork; `bal_honest`: `HonestBalance (balRunner) message state` for every message and state.
- `honestBalance_of_answers`: `HonestBalance` holds whenever every forwarded `balanceOf(a)` that
  the runner ends with no error answers at least 32 bytes whose first word is `balances[a]` of the
  contract in the child's end state.

No real upgraded contract is shown to meet these assumptions: `stopRunner` is the run of STOP at
`ua` (its messages to `ua` with other code fail), and `balRunner` is not the run of any code.
-/

namespace UsdtVerify.Sanity

open EthLib.Base (Fork U256 Address)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open Complete Security Invariant Deprecated DeprecatedBalance DeprecatedDestroy DestroySpec

variable {fork : Fork} {bound : Nat} {runChild : MessageRunner fork Nat bound} {C ua : Address}

/-! ## Keeping the storage of `C` gives every runner assumption -/

theorem keepsSlots_of_same (h : Keeps runChild C ua (SameStore C)) : KeepsSlots runChild C ua :=
  h.mono fun _ _ hs n _ => hs n

theorem keepsBal_of_same (h : Keeps runChild C ua (SameStore C)) : KeepsBal runChild C ua :=
  h.mono fun _ _ hs _ _ => hs _

theorem keepsListed_of_same (h : Keeps runChild C ua (SameStore C)) :
    KeepsListed runChild C ua :=
  h.mono fun _ _ hs a _ _ => by unfold NoDec; rw [hs]; exact Nat.le_refl _

theorem keepsAllow_of_same (h : Keeps runChild C ua (SameStore C)) : KeepsAllow runChild C ua :=
  h.mono fun _ _ hs _ _ => hs _

theorem keepsSupply_of_same (h : Keeps runChild C ua (SameStore C)) :
    KeepsSupply runChild C ua :=
  h.mono fun _ _ hs => hs 1

theorem keepsInv_of_same (h : Keeps runChild C ua (SameStore C)) : KeepsInv runChild C ua :=
  fun caller msg lt child hch hmc hmt he hI =>
    (DepInv.inv_congr (h caller msg lt child hch hmc hmt he)).2 hI

/-- The six runner assumptions of the theorems deprecated or not, together. -/
def KeepsAll (runChild : MessageRunner fork Nat bound) (C ua : Address) : Prop :=
  KeepsSlots runChild C ua ∧ KeepsBal runChild C ua ∧ KeepsListed runChild C ua ∧
    KeepsAllow runChild C ua ∧ KeepsSupply runChild C ua ∧ KeepsInv runChild C ua

theorem keepsAll_of_same (h : Keeps runChild C ua (SameStore C)) : KeepsAll runChild C ua :=
  ⟨keepsSlots_of_same h, keepsBal_of_same h, keepsListed_of_same h, keepsAllow_of_same h,
    keepsSupply_of_same h, keepsInv_of_same h⟩

/-! ## The STOP runner -/

/-- `stopRunner` meets `KeepsSlots`, `KeepsBal`, `KeepsListed`, `KeepsAllow`, `KeepsSupply` and
`KeepsInv`, for every contract `C`, at every fork and bound. -/
theorem stop_keeps_all (C ua : Address) : KeepsAll (stopRunner fork bound ua) C ua :=
  keepsAll_of_same (stopRunner_keeps ua C)

/-- From Paris, `stopRunner` meets `StaticKeeps`. -/
theorem stop_staticKeeps (hfork : .paris ≤ fork) (ua : Address) :
    StaticKeeps (stopRunner fork bound ua) := by
  intro caller msg lt c used hs hm hrun
  unfold stopRunner at hrun
  split at hrun
  · exact staticKeeps_process (bound := bound) hfork hs hm hrun
  · cases hrun

/-! ## The balance runner -/

/-- The answer of `balRunner`: the 32 bytes of the word at slot `keccak(x ++ 2)` of the
message's caller, in the caller's state, `x` the word at byte 4 of the message's data. -/
def balAnswer (caller : Evm fork Nat) (msg : Message fork) : ByteArray :=
  wordBytes (storageAt caller.state msg.caller (mapSlot (loadWord msg.data 4 32) 2))

/-- The runner that answers every message with `balAnswer` and keeps the state. -/
def balRunner (fork : Fork) (bound : Nat) : MessageRunner fork Nat bound :=
  answerRunner balAnswer

theorem bal_keeps_all (C ua : Address) : KeepsAll (balRunner fork bound) C ua :=
  keepsAll_of_same (answerRunner_keeps _ ua C)

/-- `balRunner` meets `StaticKeeps` at every fork: it keeps the state. -/
theorem bal_staticKeeps : StaticKeeps (balRunner fork bound) := by
  intro caller msg lt c used _ _ hrun
  have h := (answerRunner_ok hrun).2.1
  simp only at h
  refine ⟨?_, by rw [h]⟩
  unfold StateKept
  rw [h]
  exact State.TransactionState.SameOutside.refl _ _

/-- `HonestBalance` holds whenever every forwarded `balanceOf(a)` that the runner ends with no
error answers at least 32 bytes whose first word is `balances[a]` of the contract in the child's
end state. -/
theorem honestBalance_of_answers {message : Message fork} {state : State.TransactionState}
    (h : ∀ caller msg lt child, runChild caller msg lt = .ok child →
      msg.caller = message.currentTarget → msg.currentTarget = upAddr state message →
      msg.data = dataB message → child.1.error = none →
        32 ≤ child.1.output.size ∧ loadWord child.1.output 0 32 =
          storageAt child.1.state message.currentTarget (balSlot message)) :
    HonestBalance runChild message state := by
  intro caller msg lt child hch hmc hmt hmd he
  obtain ⟨hsz, hw⟩ := h caller msg lt child hch hmc hmt hmd he
  rw [resWord_outMemOf (size_memD _) hsz, hw]

theorem size_SEL_B : SEL_B.size = 4 := by decide

/-- `balRunner` meets `HonestBalance` for every message and state. -/
theorem bal_honest (message : Message fork) (state : State.TransactionState) :
    HonestBalance (balRunner fork bound) message state := by
  refine honestBalance_of_answers fun caller msg lt child hch hmc _ hmd _ => ?_
  obtain ⟨-, hst, hout⟩ := answerRunner_ok hch
  have hx : loadWord msg.data 4 32 = addrArg message.data 0 := by
    rw [hmd, dataB, ← size_SEL_B, loadWord_append_wordBytes]
  have h0 : loadWord (wordBytes (storageAt caller.state message.currentTarget
      (balSlot message))) 0 32 = storageAt caller.state message.currentTarget (balSlot message) := by
    have := loadWord_append_wordBytes .empty
      (storageAt caller.state message.currentTarget (balSlot message))
    simpa using this
  rw [hout, hst]
  simp only [balAnswer, hx, hmc]
  exact ⟨by rw [size_wordBytes]; exact Nat.le_refl _, h0⟩

/-- One runner meets every runner assumption of the theorems deprecated or not at once:
`KeepsSlots`, `KeepsBal`, `KeepsListed`, `KeepsAllow`, `KeepsSupply`, `KeepsInv` (for every `C`
and `ua`), `StaticKeeps`, and `HonestBalance` (for every message and state). -/
theorem runner_assumptions_hold :
    ∃ runChild : MessageRunner fork Nat bound, (∀ C ua, KeepsAll runChild C ua) ∧
      StaticKeeps runChild ∧ ∀ message state, HonestBalance runChild message state :=
  ⟨balRunner fork bound, bal_keeps_all, bal_staticKeeps, bal_honest⟩

end UsdtVerify.Sanity
