import UsdtVerify.Evm.ProcessMeter
import EthLib.Execution.Transactions.Process

/-!
# The first frame of a call with no authorization (round 45)

EthLib's `processMessageCall` runs `prepareFirstFrame` before the message: it applies the
authorizations of the transaction (EIP-7702), commits the state gas they paid, charges the state
gas of a new account for a call that moves ether to an account not alive (from Glamsterdam),
reads the recipient and its code, and follows a delegation indicator (from Pectra).

`prepareFirstFrame_call`: for a call (`target = some C`) with no value and no authorization, whose
recipient has code `c` that is no delegation indicator (or before Pectra), over any meter:
the first frame is the message with the code `c` and the gas the meter holds, the state with the
read of `C` recorded, the substate as given, no refund, and the meter
`GasMeter.commit (GasMeter.start gas reservoir)` of the message.

Evm/Auth.lean (round 46) states the first frame of such a call with authorizations
(`Auth.prepareFirstFrame_auths`).
-/

namespace UsdtVerify.FirstFrame

open EthLib.Base (Fork U256 Address)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Transactions
open EthLib.Execution.State (TransactionState)

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-- **The first frame of a call with no value and no authorization.** See the module doc. -/
theorem prepareFirstFrame_call (chainId : Nat) (message : Message fork) (state : TransactionState)
    (substate : Substate) (paidWrites : Std.ExtTreeSet Address) {C : Address}
    (ht : message.target = some C) (hv : message.value = 0) {c : ByteArray}
    (hc : state.getCode (state.getAccount C).codeHash = .ok c)
    (hd : fork ≥ .pectra → delegatedAddress c = none) :
    prepareFirstFrame (Meter := Meter) chainId message state substate [] paidWrites =
      .ok (FirstFrame.ofMeter { message with code := c } (state.recordAccountRead C) substate 0
        (GasMeter.commit (GasMeter.start message.gas message.reservoir : Meter))) := by
  have hc' : (state.recordAccountRead C).getCode
      ((state.recordAccountRead C).getAccount C).codeHash = .ok c := hc
  have hdel : (if fork ≥ .pectra then delegatedAddress c else none) = none := by
    split
    · exact hd ‹_›
    · rfl
  simp only [prepareFirstFrame, ht, applyAuthorizations, List.foldlM, hv, bind, Except.bind, pure,
    Except.pure, Except.mapError]
  simp only [ne_eq, not_true_eq_false, false_and, and_false, ↓reduceIte]
  simp only [hc', hdel]

end UsdtVerify.FirstFrame
