import UsdtVerify.Evm.Runners
import UsdtVerify.Usdt.Security.Supply

/-!
# Sanity: runners that meet the runner assumptions

The theorems deprecated or not take named assumptions on the message runner when deprecated:
`KeepsInvAt` (`inv_call_ns`, `inv_call_all`), `HonestBalanceAt` (deprecated destroyBlackFunds),
`StaticKeeps` (static frames, `inv_call_all`), and `KeepsSlots`, `KeepsBal`, `KeepsListed`,
`KeepsAllow`, `KeepsSupply` (the security theorems `*_call_all`, `*_seq_all`).
This file shows that one runner meets all of them at once (`runner_assumptions_hold`).

- `keeps*_of_same`: a runner whose messages from `C` to the upgraded address keep the storage of
  `C` (`SameFor`, `KeepsOn … (FromTo C ua) (SameStore C)`, over every message) meets `KeepsSlots`,
  `KeepsBal`, `KeepsListed`, `KeepsAllow`, `KeepsSupply` and `KeepsInvAt` (`KeepsOn.mono` with
  `fromTo_of_sentVia`).
- `balRunner`: the `answerRunner` that answers every message with the 32 bytes of the word at
  slot `keccak(x ++ 2)` of the message's caller in the caller's state, `x` the word at byte 4 of
  the message's data (`balances[x]` when the caller is `C`), and keeps the state.
  `bal_keeps_all`: it meets the six assumptions above; `bal_staticKeeps`: `StaticKeeps` at every
  fork; `bal_honest`: `HonestBalanceAt (balRunner) message state` for every message and state.

`balRunner` is not the run of any code. EthLib's own `processRunner`, with a real upgraded code,
meets the assumptions too: Sanity/Process.lean (STOP, the six `Keeps` forms), Sanity/Mirror.lean
(`MIRROR`, `HonestBalanceAt`) and `staticKeeps_process` (`StaticKeeps`, from Paris).
-/

namespace UsdtVerify.Sanity

open EthLib.Base (Fork U256 Address)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open Complete Security Invariant Deprecated DeprecatedBalance DeprecatedDestroy DestroySpec

variable {fork : Fork} {bound : Nat} {runChild : MessageRunner fork Nat bound} {C ua : Address}

/-! ## Keeping the storage of `C` gives every runner assumption -/

section Same

variable {message : Message fork} {S : State.TransactionState}

/-- A runner whose messages from `C` to the upgraded address keep the storage of `C`. -/
abbrev SameFor (runChild : MessageRunner fork Nat bound) (message : Message fork)
    (S : State.TransactionState) : Prop :=
  KeepsOn runChild (FromTo message.currentTarget (upAddr S message))
    (SameStore message.currentTarget)

theorem keepsSlots_of_same (h : SameFor runChild message S) : KeepsSlots runChild message S :=
  h.mono (fun _ _ => fromTo_of_sentVia) fun _ _ hs n _ => hs n

theorem keepsBal_of_same (h : SameFor runChild message S) : KeepsBal runChild message S :=
  h.mono (fun _ _ => fromTo_of_sentVia) fun _ _ hs _ _ => hs _

theorem keepsListed_of_same (h : SameFor runChild message S) : KeepsListed runChild message S :=
  h.mono (fun _ _ => fromTo_of_sentVia) fun _ _ hs a _ _ => by
    unfold NoDec; rw [hs]; exact Nat.le_refl _

theorem keepsAllow_of_same (h : SameFor runChild message S) : KeepsAllow runChild message S :=
  h.mono (fun _ _ => fromTo_of_sentVia) fun _ _ hs _ _ => hs _

theorem keepsSupply_of_same (h : SameFor runChild message S) : KeepsSupply runChild message S :=
  h.mono (fun _ _ => fromTo_of_sentVia) fun _ _ hs => hs 1

theorem keepsInv_of_same (h : SameFor runChild message S) : KeepsInvAt runChild message S :=
  h.mono (fun _ _ => fromTo_of_sentVia) fun _ _ hs hI => (DepInv.inv_congr hs).2 hI

end Same

/-- The six runner assumptions of the theorems deprecated or not, together (round 29: in their
`At` forms, about the calls the code makes from `S`). -/
def KeepsAll (runChild : MessageRunner fork Nat bound) (message : Message fork)
    (S : State.TransactionState) : Prop :=
  KeepsSlots runChild message S ∧ KeepsBal runChild message S ∧ KeepsListed runChild message S ∧
    KeepsAllow runChild message S ∧ KeepsSupply runChild message S ∧ KeepsInvAt runChild message S

theorem keepsAll_of_same {message : Message fork} {S : State.TransactionState}
    (h : SameFor runChild message S) : KeepsAll runChild message S :=
  ⟨keepsSlots_of_same h, keepsBal_of_same h, keepsListed_of_same h, keepsAllow_of_same h,
    keepsSupply_of_same h, keepsInv_of_same h⟩

/-! ## The STOP runner -/

/-! ## The balance runner -/

/-- The answer of `balRunner`: the 32 bytes of the word at slot `keccak(x ++ 2)` of the
message's caller, in the caller's state, `x` the word at byte 4 of the message's data. -/
def balAnswer (caller : Evm fork Nat) (msg : Message fork) : ByteArray :=
  wordBytes (storageAt caller.state msg.caller (mapSlot (loadWord msg.data 4 32) 2))

/-- The runner that answers every message with `balAnswer` and keeps the state. -/
def balRunner (fork : Fork) (bound : Nat) : MessageRunner fork Nat bound :=
  answerRunner balAnswer

theorem bal_keeps_all (message : Message fork) (S : State.TransactionState) :
    KeepsAll (balRunner fork bound) message S :=
  keepsAll_of_same (answerRunner_keeps _ _ _)

/-- `balRunner` meets `StaticKeeps` at every fork: it keeps the state. -/
theorem bal_staticKeeps : StaticKeeps (balRunner fork bound) := by
  intro caller msg lt c used _ _ hrun
  have h := (answerRunner_ok hrun).2.1
  simp only at h
  refine ⟨?_, by rw [h]⟩
  unfold StateKept
  rw [h]
  exact State.TransactionState.SameOutside.refl _ _

theorem size_SEL_B : SEL_B.size = 4 := by decide

/-- `balRunner` meets `HonestBalanceAt` for every message and state. -/
theorem bal_honest (message : Message fork) (state : State.TransactionState) :
    HonestBalanceAt (balRunner fork bound) message state := by
  intro caller msg lt child ⟨_, _, _, _, _, hmc, _, _⟩ hch hmd _
  obtain ⟨-, hst, hout⟩ := answerRunner_ok hch
  have hx : loadWord msg.data 4 32 = addrArg message.data 0 := by
    rw [hmd, dataB, ← size_SEL_B, loadWord_append_wordBytes]
  have h0 : loadWord (wordBytes (storageAt caller.state message.currentTarget
      (balSlot message))) 0 32 = storageAt caller.state message.currentTarget (balSlot message) := by
    have := loadWord_append_wordBytes .empty
      (storageAt caller.state message.currentTarget (balSlot message))
    simpa using this
  rw [resWord_outMemOf (o := child.1.output) (size_memD _)
    (by rw [hout, balAnswer, size_wordBytes]; exact Nat.le_refl _), hout, hst]
  simp only [balAnswer, hx, hmc]
  exact h0

/-- One runner meets every runner assumption of the theorems deprecated or not at once:
`KeepsSlots`, `KeepsBal`, `KeepsListed`, `KeepsAllow`, `KeepsSupply`, `KeepsInvAt` (for every
message and state), `StaticKeeps`, and `HonestBalanceAt` (for every message and state). -/
theorem runner_assumptions_hold :
    ∃ runChild : MessageRunner fork Nat bound, (∀ message S, KeepsAll runChild message S) ∧
      StaticKeeps runChild ∧ ∀ message state, HonestBalanceAt runChild message state :=
  ⟨balRunner fork bound, bal_keeps_all, bal_staticKeeps, bal_honest⟩

end UsdtVerify.Sanity
