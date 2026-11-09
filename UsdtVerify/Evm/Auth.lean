import UsdtVerify.Evm.Meter
import EthLib.Execution.Transactions.Process
import EthLib.Execution.Proofs.State.Frame
import EthLib.Execution.Proofs.State.Tracker
import EthLib.Execution.Proofs.Transactions.Authorization
import EthLib.Execution.Proofs.Transactions.Process

/-!
# The authorizations of a call (rounds 46, 51, 52)

EthLib's `applyAuthorization` (EIP-7702) recovers the authority of each authorization by ECDSA
public key recovery over a Keccak-256 hash (`recoverAuthority`), which is out of reach for given
signatures here. The statements about it take what `recoverAuthority` returns as a hypothesis, or
hold for any recovery.

Round 52: EthLib #1632 ported the round 46 and round 51 theorems of this file into EthLib
(`EthLib/Execution/Proofs/Transactions/Authorization.lean` and `Process.lean`, namespace
`EthLib.Execution.Transactions`). The local copies are deleted and their users call EthLib's:
- `delegate_ok`, `delegateRefund`: `delegate_isOk` (states the refund, 12500 before Glamsterdam for
  an authority with an account), `delegate_eq_ok`, `sameOutside_delegate`, `getCode_delegate_of_ne`,
  `getCode_delegate_self`. `delegate_parent` is `(sameOutside_delegate h).2`, `delegate_res` is
  `hasCodes_delegate` and `hasPreCodes_delegate`.
- `pay_pre`, `pay_glam`, `pay_keeps`: `payAuthorization_of_lt_glamsterdam`,
  `payAuthorization_eq_ok_iff`, `state_payAuthorization`.
- `apply_out`, `apply_none`, `apply_refused`, `apply_accepted`, `apply_cases`:
  `applyAuthorization_of_not_inScope`, `applyAuthorization_of_recoverAuthority_none`,
  `applyAuthorization_of_refused`, `applyAuthorization_of_accepts_of_pay`,
  `applyAuthorization_cases`.
- `accepts_code`, `apply_code`, `apply_keeps`, `fold_keeps`: `authorityAccepts_of_code`,
  `applyAuthorization_of_code`, `applyAuthorization_keeps`, `foldlM_applyAuthorization_keeps` (which
  also keep the transient storage).
- `apply_meter_pre`, `fold_meter_pre`: `meter_applyAuthorization_of_lt_glamsterdam`,
  `meter_foldlM_applyAuthorization_of_lt_glamsterdam`.
- `prepareFirstFrame_auths`, `prepareFirstFrame_auths_error`:
  `prepareFirstFrame_of_applyAuthorizations`, `prepareFirstFrame_of_applyAuthorizations_error`.
- `chargeState_ok`, `charge_ok`, `charge_bound`: `chargesWithin_stateGasMeter` and
  `chargeAuthorization_isOk`.
- `apply_exists_of`, `apply_exists`, `fold_exists`: `applyAuthorization_isOk_of_pay`,
  `applyAuthorization_isOk`, `foldlM_applyAuthorization_isOk` with `chargesWithin_stateGasMeter`
  (they need the pre-state codes only from Glamsterdam; `hasPreCodes_applyAuthorization` keeps
  them). `apply_exists_pre`, `fold_exists_pre`: `applyAuthorization_isOk_of_lt_glamsterdam`,
  `foldlM_applyAuthorization_isOk_of_lt_glamsterdam` (which need no pre-state codes).
- `getCode_modifyState`, `getCode_setCode_of_ne`, `getCode_setCode_self`, `parent_modifyState`:
  EthLib's lemmas of the same names in `EthLib.Execution.State.TransactionState`.

What stays, and why:
- `hashOf`, `seen`, `authMax`, `Resolves`, `PreResolves`: names in the statements of
  Usdt/Sanity/MirrorAuth.lean and MirrorAuthN.lean, which are kept as they are. `hashOf` is
  `keccak256`, `seen` is the delegations that EthLib's refused case gives, `authMax` is the sum of
  EthLib's bound `NEW_ACCOUNT_STATE_GAS + ACCOUNT_WRITE + AUTH_BASE_STATE_GAS`, and `Resolves`,
  `PreResolves` are EthLib's `HasCodes`, `HasPreCodes`; all are reducible, so EthLib's theorems
  apply to them as they are.
- `authMax_eq`: EthLib states the value 227790 only in its docs.
- `getCode_empty`: the code under the empty code hash; EthLib has no lemma for it.
- `getCode_insert`, `ok_bind`, `chargeAuthorization_eq`, `chargeState_ok`, `charge_ok` (helpers of
  the old proofs) are removed with them.
-/

namespace UsdtVerify.Auth

open EthLib.Base (Fork U256 Address Hash32)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Transactions
open EthLib.Execution.State (TransactionState)

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-! ## The state -/

/-- The Keccak-256 hash of a code, under which `setCode` keeps it. -/
abbrev hashOf (code : ByteArray) : Hash32 := EthLib.Cryptography.Hash.Keccak.keccak256 code

/-- The empty code hash always has a code. -/
theorem getCode_empty (s : TransactionState) : s.getCode State.EMPTY_CODE_HASH = .ok .empty := by
  unfold TransactionState.getCode
  simp

/-! ## One authorization -/

/-- The delegations with the read and the access of the authority `a`: what EthLib's
`applyAuthorization_of_refused` gives. -/
abbrev seen (done : Delegations Meter) (a : Address) : Delegations Meter :=
  { done with state := done.state.recordAccountRead a, accessed := done.accessed.insert a }

/-! ## The meter of EIP-8037 and the existence of the result -/

/-- The most execution gas that one authorization takes from Glamsterdam: a new account, the
first write and a new delegation indicator (183600 + 9000 + 35190). It is the bound of EthLib's
`chargeAuthorization_isOk` and `foldlM_applyAuthorization_isOk`. -/
abbrev authMax : Nat :=
  GasCosts.NEW_ACCOUNT_STATE_GAS + GasCosts.ACCOUNT_WRITE + GasCosts.AUTH_BASE_STATE_GAS

theorem authMax_eq : authMax = 227790 := rfl

/-- Every account's code hash has a code in the state: EthLib's `HasCodes`. -/
abbrev Resolves (s : TransactionState) : Prop := HasCodes s

/-- Every account's code hash before the transaction has a code in the state: EthLib's
`HasPreCodes`. -/
abbrev PreResolves (s : TransactionState) : Prop := HasPreCodes s

end UsdtVerify.Auth
