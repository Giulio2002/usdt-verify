import UsdtVerify.Evm.Frame
import UsdtVerify.Evm.Route

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

Round 29 (docs/AUDIT.md, finding 2): `Keeps` quantifies over every caller frame and every message
from `C` to `ua`, including its code, so EthLib's own runner `processRunner` (which runs the
message's code) meets it for no `ua`. The forms used by the theorems now quantify only over the
calls that the code of `C` actually makes:

- `SameView X S`: `X` has the storage and the code of `S` at every address (the states the code
  of `C` calls from differ from its start state only by recorded reads).
- `SentVia message S ua caller msg`: the caller frame's state has the view of `S`, and `msg` is
  the message of a CALL from `C = message.currentTarget` to `ua` that runs the code `c` that
  `ua` holds in `S`, along its route `r` (EIP-7702), with no value and the depth and static flag
  of `message` (`Complete.SendsVia`; any data, any gas).
- `KeepsAt runChild message S ua R`: every such message that the runner ends with no error goes
  from the caller state to the child's end state with `R`. `Keeps.at`: `Keeps` implies it.
- `FwdAt`: one such message, ended with no error, from `X` to `Y`.
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

/-! ## The calls the code actually makes (round 29) -/

open Complete (Routes SendsVia)

/-- `X` has the storage and the code of `S` at every address. -/
def SameView (X S : State.TransactionState) : Prop :=
  (∀ a n, storageAt X a n = storageAt S a n) ∧
    ∀ a, X.getCode (X.getAccount a).codeHash = S.getCode (S.getAccount a).codeHash

theorem SameView.refl (S : State.TransactionState) : SameView S S := ⟨fun _ _ => rfl, fun _ => rfl⟩

theorem sameView_recordAccountRead {X S : State.TransactionState} (h : SameView X S) (u : Address) :
    SameView (X.recordAccountRead u) S :=
  ⟨fun a n => by
    simp only [storageAt, State.TransactionState.getStorage_recordAccountRead]
    exact h.1 a n, fun a => h.2 a⟩

theorem sameView_readSlot {X S : State.TransactionState} (h : SameView X S) (c : Address)
    (n : U256) : SameView (readSlot X c n) S :=
  ⟨fun a m => by rw [storageAt_readSlot]; exact h.1 a m, fun a => h.2 a⟩

theorem sameView_route {X S : State.TransactionState} (h : SameView X S) (r : Complete.Route) :
    SameView (Complete.routeState X r) S := by
  rcases r with _ | ⟨d, _⟩
  · exact h
  · exact sameView_recordAccountRead h d

/-- The caller frame and message of a CALL that the code of `message.currentTarget`, run from the
state `S`, makes to `ua`: the caller state has the view of `S`, and the message runs the code
that `ua` holds in `S` along its route, with no value (any data, any gas). -/
def SentVia (message : Message fork) (S : State.TransactionState) (ua : Address)
    (caller : Evm fork Nat) (msg : Message fork) : Prop :=
  ∃ c r, S.getCode (S.getAccount ua).codeHash = .ok c ∧ Routes fork S c r ∧
    SendsVia message ua c r msg.data msg ∧ SameView caller.state S

theorem sendsVia_data {message msg : Message fork} {c : ByteArray} {r : Complete.Route}
    {d : ByteArray} (h : SendsVia message ua c r d msg) : SendsVia message ua c r msg.data msg := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, rfl, h8⟩

/-- `Keeps` over the calls the code of `C` actually makes from `S` (`SentVia`). -/
def KeepsAt (runChild : MessageRunner fork Nat bound) (message : Message fork)
    (S : State.TransactionState) (ua : Address)
    (R : State.TransactionState → State.TransactionState → Prop) : Prop :=
  ∀ caller msg lt child, SentVia message S ua caller msg → runChild caller msg lt = .ok child →
    child.1.error = none → R caller.state child.1.state

/-- One call that the code of `C` makes from `S` to `ua`, ended with no error, from `X` to `Y`. -/
def FwdAt (runChild : MessageRunner fork Nat bound) (message : Message fork)
    (S : State.TransactionState) (ua : Address) (X Y : State.TransactionState) : Prop :=
  ∃ caller msg lt child, SentVia message S ua caller msg ∧ runChild caller msg lt = .ok child ∧
    child.1.error = none ∧ caller.state = X ∧ child.1.state = Y

theorem KeepsAt.fwd {message : Message fork} {S : State.TransactionState}
    {R : State.TransactionState → State.TransactionState → Prop} {X Y : State.TransactionState}
    (hk : KeepsAt runChild message S ua R) (h : FwdAt runChild message S ua X Y) : R X Y := by
  obtain ⟨caller, msg, lt, child, hs, hch, he, rfl, rfl⟩ := h
  exact hk caller msg lt child hs hch he

theorem KeepsAt.mono {message : Message fork} {S : State.TransactionState}
    {R R' : State.TransactionState → State.TransactionState → Prop}
    (hk : KeepsAt runChild message S ua R) (hR : ∀ X Y, R X Y → R' X Y) :
    KeepsAt runChild message S ua R' :=
  fun caller msg lt child hs hch he => hR _ _ (hk caller msg lt child hs hch he)

/-- The old form implies the new one. -/
theorem Keeps.at {message : Message fork} {S : State.TransactionState}
    {R : State.TransactionState → State.TransactionState → Prop}
    (hk : Keeps runChild message.currentTarget ua R) : KeepsAt runChild message S ua R := by
  intro caller msg lt child ⟨_, _, _, _, hv, _⟩ hch he
  exact hk caller msg lt child hch hv.1 hv.2.1 he

end UsdtVerify
