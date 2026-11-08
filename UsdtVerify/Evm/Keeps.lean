import UsdtVerify.Evm.Frame

/-!
# A relation that a message runner keeps over the calls from one account to another

For any code and any message runner `runChild`:

- `Forwarded runChild C ua X Y`: the runner ends, with no error, a message whose caller is `C`
  and whose current target is `ua`, sent from a caller frame in the state `X`; the child frame
  ends in the state `Y`.
- `Keeps runChild C ua R`: every such message that the runner ends with no error goes from a
  state `X` to a state `Y` with `R X Y`. It is an assumption on the runner (on what the code at
  `ua`, and whatever it calls, does), in the style of `KeepsInv`.

`NoDec.congr_left`: the relation depends on the storage of `C` only.
-/

namespace UsdtVerify

open EthLib.Base (Fork U256 Address)
open EthLib.Execution
open EthLib.Execution.Evm

variable {fork : Fork} {bound : Nat} {runChild : MessageRunner fork Nat bound} {C ua : Address}

/-- The runner ends with no error a message from `C` to `ua`, sent from a caller frame in the
state `X`, and the child frame ends in the state `Y`. -/
def Forwarded (runChild : MessageRunner fork Nat bound) (C ua : Address)
    (X Y : State.TransactionState) : Prop :=
  ∃ caller msg lt child, runChild caller msg lt = .ok child ∧ child.1.error = none ∧
    msg.caller = C ∧ msg.currentTarget = ua ∧ caller.state = X ∧ child.1.state = Y

/-- The named form of a runner assumption: every message from `C` to `ua` that the runner ends
with no error goes from its caller state `X` to its child's end state `Y` with `R X Y`. -/
def Keeps (runChild : MessageRunner fork Nat bound) (C ua : Address)
    (R : State.TransactionState → State.TransactionState → Prop) : Prop :=
  ∀ caller msg lt child, runChild caller msg lt = .ok child → msg.caller = C →
    msg.currentTarget = ua → child.1.error = none → R caller.state child.1.state

theorem Keeps.fwd {R : State.TransactionState → State.TransactionState → Prop}
    {X Y : State.TransactionState} (hk : Keeps runChild C ua R)
    (h : Forwarded runChild C ua X Y) : R X Y := by
  obtain ⟨caller, msg, lt, child, hch, he, hmc, hmt, rfl, rfl⟩ := h
  exact hk caller msg lt child hch hmc hmt he

theorem Keeps.mono {R R' : State.TransactionState → State.TransactionState → Prop}
    (hk : Keeps runChild C ua R) (hR : ∀ X Y, R X Y → R' X Y) : Keeps runChild C ua R' :=
  fun caller msg lt child hch hmc hmt he => hR _ _ (hk caller msg lt child hch hmc hmt he)

variable {W : U256 → Prop} {S X Y : State.TransactionState}

theorem NoDec.congr_left {k : U256} (hX : ∀ n, storageAt X C n = storageAt S C n)
    (h : NoDec C k X Y) : NoDec C k S Y := by
  unfold NoDec at *; rw [← hX k]; exact h

end UsdtVerify
