import Batteries.Tactic.Alias
import UsdtVerify.Functions.TotalSupply
import UsdtVerify.Functions.BalanceOf
import UsdtVerify.Functions.Transfer
import UsdtVerify.Functions.TransferSuccess
import UsdtVerify.Functions.ApproveSpec
import UsdtVerify.Functions.ApproveRevert
import UsdtVerify.Functions.TransferFromSpec
import UsdtVerify.Functions.TransferFeeSpec
import UsdtVerify.Functions.TransferFault
import UsdtVerify.Functions.TransferFaults
import UsdtVerify.Functions.TransferFromFault
import UsdtVerify.Functions.TransferFromFeeSpec
import UsdtVerify.Functions.TransferFromFault2
import UsdtVerify.Functions.DeprecatedBalance
import UsdtVerify.Functions.DeprecatedTransferFrom

/-!
# Summary: what is proved about the deployed USDT bytecode

All theorems are about the 11075-byte runtime code `CODE` (data/usdt.runtime.hex), run by
EthLib's EVM semantics from pc 0 in a fresh frame (`At CODE message 0 [] .empty gas state
substate`), for every fork from Berlin on (the paths that write storage: Berlin ≤ fork <
Glamsterdam, EthLib's SSTORE rule). Each is a `Spec`: every run from such a frame reaches an end
frame satisfying the postcondition; `runFrame_*` theorems state the same about the interpreter
loop `runFrame` for every gas bound and message runner. Common hypotheses of every path below:
the call data has the function's selector in its first 4 bytes and fewer than 2^256 bytes, the
call has no value, and there is enough gas (an exact cost, given in each theorem; a path that
writes storage also needs more than 2300 gas left at an SSTORE where stated). "Not paused",
"not deprecated" mean byte 20 of slot 0, of slot 10 is 0; "x blacklisted" means the low byte of
`isBlackListed[x]` (slot `keccak(x ++ 6)`) is not 0. `S` is the state after the reads of the
checks. `C` is the contract. `fee = min(v * basisPointsRate / 10000, maximumFee)` (slots 3, 4) as
the bytecode computes it (`feeOf`). Balances are the words of `balances[x]` = slot
`keccak(x ++ 2)`; allowances of `allowed[x][y]` = slot `keccak(y ++ keccak(x ++ 5))`.

The end conditions: `Stopped` (STOP: no error; the state and substate given, gas left exact;
the output is not tracked, see STATUS), `Halted true .empty` (REVERT, no output; the caller rolls
the state back), `Faulted (.invalidOpcode 0xfe)` (a failed SafeMath assert: no output, no gas
left; the caller discards the state). The writes of the success paths are stated as the sequence
of writes the code makes, each read in the state where the code reads it; the `*_effects`
theorems below turn those end states into plain facts about the slots and logs.

## totalSupply() — `totalSupply_spec`
Not deprecated ⇒ returns the 32 bytes of slot 1; state: only reads.

## balanceOf(address) — `balanceOf_spec`
Not deprecated ⇒ returns the 32 bytes of `balances[a]`, `a` = argument word 0 masked to 160
bits; only reads.

## transfer(address to, uint256 v) — selector 0xa9059cbb
- `transfer_paused`: paused ⇒ REVERT.
- `transfer_blacklisted`: not paused, caller blacklisted ⇒ REVERT. (The recipient's status is
  not read.)
- `transfer_short`: not paused, caller not blacklisted, not deprecated, call data < 68 bytes ⇒
  REVERT.
From here on: call data ≥ 68 bytes, not paused, caller not blacklisted, not deprecated.
- `transfer_mulOv`: `v * rate ≥ 2^256` ⇒ INVALID.
- `transfer_feeGt`: no overflow, `fee > v` ⇒ INVALID.
- `transfer_low`: no overflow, `fee ≤ v`, `balances[caller] < v` ⇒ INVALID.
- `transfer_toOv`: `fee ≤ v`, `v ≤ balances[caller]`, `balances[to] + (v - fee) ≥ 2^256`
  (read after the sender's write) ⇒ INVALID.
- `transfer_ownerOv`: `0 < fee ≤ v`, the transfer to `to` fits, `balances[owner] + fee ≥ 2^256`
  (owner = low 160 bits of slot 0) ⇒ INVALID.
- `transfer_ok` (fee = 0): STOP; `balances[caller] := balances[caller] - v`, then
  `balances[to] := balances[to] + v`; log `Transfer(caller, to, v)`. See `transfer_ok_effects`.
- `transfer_fee` (fee > 0): STOP; sender `-= v`, `to += v - fee`, owner `+= fee`; logs
  `Transfer(caller, owner, fee)`, `Transfer(caller, to, v - fee)`. See `transfer_fee_effects`.
  Transfer returns no word (USDT's non-standard ABI).

## approve(address s, uint256 v) — selector 0x095ea7b3
Call data ≥ 68 bytes, not deprecated (paused and blacklists are not read):
- `approve_zero` (v = 0): `allowed[caller][s] := 0`, log `Approval(caller, s, 0)`, STOP.
- `approve_set` (v ≠ 0, `allowed[caller][s] = 0`): `allowed[caller][s] := v`, log
  `Approval(caller, s, v)`, STOP.
- `approve_revert` (v ≠ 0, `allowed[caller][s] ≠ 0`): REVERT.

## transferFrom(address f, address t, uint256 v) — selector 0x23b872dd
- `transferFrom_paused`: paused ⇒ REVERT.
- `transferFrom_blacklisted`: not paused, `f` blacklisted ⇒ REVERT. (Neither the caller nor `t`
  is read.)
- `transferFrom_short`: not paused, `f` not blacklisted, not deprecated, call data < 100 bytes ⇒
  REVERT.
From here on: call data ≥ 100 bytes, not paused, `f` not blacklisted, not deprecated;
`A = allowed[f][caller]`.
- `transferFrom_mulOv`: `v * rate ≥ 2^256` ⇒ INVALID.
- `transferFrom_allowLow`: no overflow, `A < v` ⇒ INVALID (the fee is computed first; nothing
  is written).
- `transferFrom_balLow`: no overflow, `fee ≤ v`, `A = MAX_UINT ∨ v ≤ A`, `balances[f] < v` (read
  after the allowance step) ⇒ INVALID (after the allowance write).
- `transferFrom_feeGt`: no overflow, `A = MAX_UINT ∨ v ≤ A`, `fee > v` ⇒ INVALID (after the
  allowance write).
- `transferFrom_toOv`: `fee ≤ v`, the allowance step and the debit of `f` pass,
  `balances[t] + (v - fee) ≥ 2^256` (read after the write of `f`) ⇒ INVALID.
- `transferFrom_ownerOv`: `0 < fee ≤ v`, the transfer to `t` fits, `balances[owner] + fee ≥ 2^256`
  ⇒ INVALID.
- `transferFrom_ok` (fee = 0, `A = MAX_UINT ∨ v ≤ A`, `v ≤ balances[f]`, no overflow at `t`):
  STOP; `allowed[f][caller] := A - v` unless `A = MAX_UINT`; `balances[f] -= v`;
  `balances[t] += v`; log `Transfer(f, t, v)`. See `transferFrom_ok_effects`.
- `transferFrom_fee` (fee > 0, `fee ≤ v`, the same, no overflow at `t` and at the owner): STOP;
  the allowance step; `balances[f] -= v`; `balances[t] += v - fee`; `balances[owner] += fee`; logs
  `Transfer(f, owner, fee)`, `Transfer(f, t, v - fee)`. See `transferFrom_fee_effects`.

## Conservation (local)
`transfer_ok_conserves`, `transfer_fee_conserves`, `transferFrom_ok_conserves`,
`transferFrom_fee_conserves`: on the end state of each success path, the integer changes of the
balance slots the path writes are `-v` (payer), `+(v - fee)` (payee), `+fee` (owner, fee paths)
and sum to zero. Hypotheses: the slots are pairwise distinct (and distinct from slot 0 and the
allowance slot where needed); this is assumed, not derived from keccak. Only these slots are
stated; "sum of all balances = `_totalSupply`" needs a sum over a mapping and is not proved.

Every from-pc-0 theorem has a `runFrame_*` form (the interpreter loop, any gas bound, any runner).

## Deprecated: totalSupply() and balanceOf(who) forward to `upgradedAddress`
With byte 20 of slot 10 set, `ua` = low 160 bits of slot 10 (as an address) holding a code `c`
(`0 < |c|`, no delegation), the theorems are `SpecUnder` triples: they hold under every runner of
messages that meets a callee assumption `callee`, and say nothing when the runner aborts.
- `totalSupply_dep` / `balanceOf_dep` (any `callee`): the frame sends `ua` one message with no
  value and data `0x18160ddd` / `0x70a08231 ++ who` (`Forwarded` / `Sends`); if that call ends with
  no error, the frame returns the word at 0x60 after the first `min 32 |output|` output bytes were
  copied there; if it ends with an error, the frame reverts with no output.
- `totalSupply_dep_answers` / `balanceOf_dep_answers`: a callee that answers `o` (`|o| ≥ 32`) ⇒ the
  frame returns `wordBytes (loadWord o 0 32)`. `*_dep_fails`: a failing callee ⇒ REVERT, no output.
- `totalSupply_dep_process` / `balanceOf_dep_process`: the same with the interpreter's own runner
  `processRunner`, for any code at `ua` with a `Spec` (EthLib's `meets_of_spec`, `RunsAs`).
- `totalSupply_depNoCode` / `balanceOf_depNoCode`: empty code at `ua` ⇒ REVERT before any call.

## Deprecated: transfer, approve, transferFrom forward to `upgradedAddress` (no output range)
With byte 20 of slot 10 set and `ua` holding a code `c` as above. The hypotheses are bundled in
`HypT` / `HypA` / `HypF` (fork range, selector, no value, deprecated, the code at `ua`, depth,
coldness flags; transfer: not paused and caller not blacklisted; transferFrom: not paused and `f`
not blacklisted; approve: call data ≥ 68 bytes, its own payload check comes first). transfer and
transferFrom need only call data ≥ 4 bytes on this path (the payload checks are in BasicToken /
StandardToken, which are not reached).
- `transfer_dep` / `approve_dep` / `transferFrom_dep` (any `callee`): the frame sends `ua` one
  message (`Sends`) with no value, the gas of EIP-150, and the data
  `0x6e18980a ++ caller ++ to ++ v` (`transferByLegacy`, `dataT`),
  `0xaee92d33 ++ caller ++ s ++ v` (`approveByLegacy`, `dataA`),
  `0x8b477adb ++ caller ++ f ++ t ++ v` (`transferFromByLegacy`, `dataF`), each address argument
  as a word masked to 160 bits; the CALL has an output range of size 0. If that call ends with no
  error, the frame STOPs with no error (`Local.Stopped`); if it ends with an error, it reverts
  with no output. Gas left, state and substate: exact (after the call, `incorporateChild`).
- `*_dep_succeeds`: a callee that ends every such message with no error ⇒ STOP, no error, state and
  substate from `incorporateChild` of the callee's frame. `*_dep_fails`: REVERT, no output.
- `*_dep_process`: the interpreter's own runner `processRunner`, for any code at `ua` with a `Spec`
  whose stopped frames have no error (`meets_of_spec`, `RunsAs`) ⇒ STOP with no error, or abort.
- `*_depNoCode`: empty code at `ua` ⇒ REVERT before any call.
What the upgraded contract does with the forwarded call (the balances it changes) is the callee's
business: nothing is assumed or proved about it beyond the callee assumption.

## Not proved
A nonzero call value; the other functions; the fallback. The returned bytes of a STOP (`At` does
not track the output buffer).
-/

namespace UsdtVerify.Summary

open EthLib.Base (Fork U256 Address)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open Transfer SafeMath TransferOk TransferFee TransferFrom

alias totalSupply_spec := TotalSupply.spec
alias balanceOf_spec := BalanceOf.spec
alias transfer_paused := Transfer.spec_paused
alias transfer_blacklisted := Transfer.spec_blacklisted
alias transfer_short := Transfer.spec_short
alias transfer_mulOv := TransferOk.spec_mulOv
alias transfer_feeGt := TransferOk.spec_feeGt
alias transfer_low := TransferOk.spec_low
alias transfer_toOv := TransferOk.spec_toOv
alias transfer_ownerOv := TransferOk.spec_ownerOv
alias transfer_ok := TransferOk.spec_ok
alias transfer_fee := TransferFee.spec_fee
alias approve_zero := Approve.spec_zero
alias approve_set := Approve.spec_set
alias approve_revert := Approve.spec_revert
alias transferFrom_paused := TransferFrom.spec_paused
alias transferFrom_blacklisted := TransferFrom.spec_blacklisted
alias transferFrom_short := TransferFrom.spec_short
alias transferFrom_mulOv := TransferFrom.spec_mulOv
alias transferFrom_allowLow := TransferFrom.spec_allowLow
alias transferFrom_balLow := TransferFrom.spec_balLow
alias transferFrom_feeGt := TransferFrom.spec_feeGtF
alias transferFrom_toOv := TransferFrom.spec_toOvF
alias transferFrom_ownerOv := TransferFrom.spec_ownerOvF
alias transferFrom_ok := TransferFrom.spec_ok
alias transferFrom_fee := TransferFrom.spec_feeF
alias totalSupply_dep := Deprecated.spec_dep
alias totalSupply_dep_answers := Deprecated.spec_dep_answers
alias totalSupply_dep_fails := Deprecated.spec_dep_fails
alias totalSupply_dep_process := Deprecated.runFrame_dep_process
alias totalSupply_depNoCode := Deprecated.spec_depNoCode
alias balanceOf_dep := DeprecatedBalance.spec_depB
alias balanceOf_dep_answers := DeprecatedBalance.spec_depB_answers
alias balanceOf_dep_fails := DeprecatedBalance.spec_depB_fails
alias balanceOf_dep_process := DeprecatedBalance.runFrame_depB_process
alias balanceOf_depNoCode := DeprecatedBalance.spec_depBNoCode
alias transfer_dep := DeprecatedTransfer.spec_depT
alias transfer_dep_succeeds := DeprecatedTransfer.spec_depT_succeeds
alias transfer_dep_fails := DeprecatedTransfer.spec_depT_fails
alias transfer_dep_process := DeprecatedTransfer.runFrame_depT_process
alias transfer_depNoCode := DeprecatedTransfer.spec_depTNoCode
alias approve_dep := DeprecatedTransfer.spec_depA
alias approve_dep_succeeds := DeprecatedTransfer.spec_depA_succeeds
alias approve_dep_fails := DeprecatedTransfer.spec_depA_fails
alias approve_dep_process := DeprecatedTransfer.runFrame_depA_process
alias approve_depNoCode := DeprecatedTransfer.spec_depANoCode
alias transferFrom_dep := DeprecatedTransferFrom.spec_depF
alias transferFrom_dep_succeeds := DeprecatedTransferFrom.spec_depF_succeeds
alias transferFrom_dep_fails := DeprecatedTransferFrom.spec_depF_fails
alias transferFrom_dep_process := DeprecatedTransferFrom.runFrame_depF_process
alias transferFrom_depNoCode := DeprecatedTransferFrom.spec_depFNoCode

variable {fork : Fork} {message : Message fork}

/-- The end of `transfer_ok` in plain terms, for any state `S` in which the contract has an
account: the frame stopped without error; `balances[to]` is its word after the sender's write
plus `v`; when the two slots differ, `balances[caller]` is its word in `S` minus `v` and the
recipient's word read was its word in `S`; one log was appended, `Transfer(caller, to, v)`. -/
theorem transfer_ok_effects {S : State.TransactionState} (hacc : hasAccount S message.currentTarget)
    {ss : Substate} {g : Nat} {v a : U256} {evm : Evm fork Nat}
    (h : Local.Stopped g (credited S message v a) (loggedSub fork ss S message v a) evm) :
    evm.running = false ∧ evm.error = none ∧
    storageAt evm.state message.currentTarget (recipientSlot a) =
      add (balT S message v a) v ∧
    (recipientSlot a ≠ senderSlot message →
      storageAt evm.state message.currentTarget (senderSlot message) = sub (balS S message) v ∧
      balT S message v a = storageAt S message.currentTarget (recipientSlot a)) ∧
    evm.substate.logs = ss.logs.push (transferLog message.currentTarget
      (bitwiseAnd ADDR_MASK message.caller.toU256) (bitwiseAnd ADDR_MASK a) v) := by
  obtain ⟨hr, he, -, hs, hss⟩ := h
  have hacc3 : hasAccount (reads3 S message) message.currentTarget :=
    hasAccount_readSlot (hasAccount_readSlot (hasAccount_readSlot hacc))
  have hacc4 : hasAccount (readSlot (debited S message v) message.currentTarget
      (recipientSlot a)) message.currentTarget :=
    hasAccount_readSlot (hasAccount_writeSlot hacc3)
  refine ⟨hr, he, ?_, ?_, ?_⟩
  · rw [hs]; exact storageAt_writeSlot_self hacc4
  · intro hne
    rw [hs]
    refine ⟨?_, ?_⟩
    · rw [credited, storageAt_writeSlot_of_ne hacc4 (Ne.symm hne), storageAt_readSlot]
      exact storageAt_writeSlot_self hacc3
    · rw [balT, debited, storageAt_writeSlot_of_ne hacc3 hne]
      simp only [reads3, storageAt_readSlot]
  · rw [hss]

/-- The logs of the allowance step: unchanged. -/
theorem logs_allowSub {fork : Fork} {ss : Substate} {t : Address} {n o A v : U256} :
    (allowSub fork ss t n o A v).logs = ss.logs := by
  unfold allowSub; split <;> rfl

/-- The end of `transferFrom_ok` in plain terms, for any state `S` in which the contract has an
account, with `A` the allowance in `S`: the frame stopped without error; `balances[t]` is its word
after the write of `f` plus `v`; when the slots of `t` and `f` differ, `balances[f]` is its word
after the allowance step minus `v`; when the allowance slot differs from both balance slots, it
holds `A` if `A = MAX_UINT`, else `A - v`; one log was appended, `Transfer(f, t, v)`. -/
theorem transferFrom_ok_effects {S : State.TransactionState}
    (hacc : hasAccount S message.currentTarget) {ss : Substate} {g : Nat} {v t f : U256}
    {evm : Evm fork Nat}
    (h : Local.Stopped g (creditedF S message v t f) (loggedSubF fork ss S message v t f) evm) :
    evm.running = false ∧ evm.error = none ∧
    storageAt evm.state message.currentTarget (recipientSlot t) =
      add (balTo S message v t f) v ∧
    (recipientSlot t ≠ recipientSlot f →
      storageAt evm.state message.currentTarget (recipientSlot f) =
        sub (balFrom S message v f) v) ∧
    (allowFrom message f ≠ recipientSlot f → allowFrom message f ≠ recipientSlot t →
      storageAt evm.state message.currentTarget (allowFrom message f) =
        if allowOf S message f = MAX_UINT then allowOf S message f
        else sub (allowOf S message f) v) ∧
    evm.substate.logs = ss.logs.push (transferLog message.currentTarget
      (bitwiseAnd ADDR_MASK f) (bitwiseAnd ADDR_MASK t) v) := by
  obtain ⟨hr, he, -, hs, hss⟩ := h
  have hacc3 : hasAccount (readsF S message f) message.currentTarget :=
    hasAccount_readSlot (hasAccount_readSlot (hasAccount_readSlot hacc))
  have hacc4 : hasAccount (readSlot (allowedF S message v f) message.currentTarget
      (recipientSlot f)) message.currentTarget :=
    hasAccount_readSlot (hasAccount_allowState hacc3)
  have hacc5 : hasAccount (readSlot (debitedF S message v f) message.currentTarget
      (recipientSlot t)) message.currentTarget :=
    hasAccount_readSlot (hasAccount_writeSlot hacc4)
  refine ⟨hr, he, ?_, ?_, ?_, ?_⟩
  · rw [hs]; exact storageAt_writeSlot_self hacc5
  · intro hne
    rw [hs, creditedF, storageAt_writeSlot_of_ne hacc5 (Ne.symm hne), storageAt_readSlot]
    exact storageAt_writeSlot_self hacc4
  · intro hf ht
    rw [hs, creditedF, storageAt_writeSlot_of_ne hacc5 ht, storageAt_readSlot, debitedF,
      storageAt_writeSlot_of_ne hacc4 hf, storageAt_readSlot, allowedF]
    unfold allowState
    split
    · simp only [readsF, allowOf, storageAt_readSlot]
    · exact storageAt_writeSlot_self hacc3
  · rw [hss]
    show ((creditedSubF fork ss S message v t f).logs).push _ = _
    simp only [allowedSubF]
    rw [logs_allowSub]

/-- The end of `transfer_fee` in plain terms, for any state `S` in which the contract has an
account, with `os` the owner's balance slot (owner read from slot 0 after the recipient's
write): the frame stopped without error; `balances[owner]` is its word read after the recipient's
write plus the fee; when the slots differ, `balances[to]` is its word after the sender's write
plus `v - fee`, and `balances[caller]` is its word in `S` minus `v`; two logs were appended,
`Transfer(caller, owner', fee)` (owner' read from slot 0 after the owner's write) then
`Transfer(caller, to, v - fee)`. -/
theorem transfer_fee_effects {S : State.TransactionState}
    (hacc : hasAccount S message.currentTarget) {ss : Substate} {g : Nat} {v a : U256}
    {evm : Evm fork Nat}
    (h : Local.Stopped g (feeState S message v a) (feeSub fork ss S message v a) evm) :
    evm.running = false ∧ evm.error = none ∧
    storageAt evm.state message.currentTarget (ownerSlot (ownerWord S message v a)) =
      add (balO S message v a) (feeOf S message v) ∧
    (recipientSlot a ≠ ownerSlot (ownerWord S message v a) →
      storageAt evm.state message.currentTarget (recipientSlot a) =
        add (balT S message v a) (sendOf S message v)) ∧
    (senderSlot message ≠ ownerSlot (ownerWord S message v a) →
      senderSlot message ≠ recipientSlot a →
      storageAt evm.state message.currentTarget (senderSlot message) =
        sub (balS S message) v) ∧
    evm.substate.logs = (ss.logs.push (transferLog message.currentTarget
      (bitwiseAnd ADDR_MASK message.caller.toU256)
      (bitwiseAnd ADDR_MASK (ownerKey (storageAt (ownedB (creditedFee S message v a)
        message.currentTarget (feeOf S message v)) message.currentTarget 0)))
      (feeOf S message v))).push (transferLog message.currentTarget
        (bitwiseAnd ADDR_MASK message.caller.toU256) (bitwiseAnd ADDR_MASK a)
        (sendOf S message v)) := by
  obtain ⟨hr, he, -, hs, hss⟩ := h
  have hacc3 : hasAccount (reads3 S message) message.currentTarget :=
    hasAccount_readSlot (hasAccount_readSlot (hasAccount_readSlot hacc))
  have hacc4 : hasAccount (readSlot (debited S message v) message.currentTarget
      (recipientSlot a)) message.currentTarget :=
    hasAccount_readSlot (hasAccount_writeSlot hacc3)
  have hacc5 : hasAccount (readSlot (readSlot (readSlot (creditedFee S message v a)
      message.currentTarget 0) message.currentTarget
      (ownerSlotOf (creditedFee S message v a) message.currentTarget)) message.currentTarget 0)
      message.currentTarget :=
    hasAccount_readSlot (hasAccount_readSlot (hasAccount_readSlot (hasAccount_writeSlot hacc4)))
  refine ⟨hr, he, ?_, ?_, ?_, ?_⟩
  · rw [hs, feeState, storageAt_readSlot]
    exact storageAt_writeSlot_self hacc5
  · intro hne
    rw [hs, feeState, storageAt_readSlot, ownedB, storageAt_writeSlot_of_ne hacc5 hne]
    simp only [storageAt_readSlot]
    exact storageAt_writeSlot_self hacc4
  · intro ho hr'
    rw [hs, feeState, storageAt_readSlot, ownedB, storageAt_writeSlot_of_ne hacc5 ho]
    simp only [storageAt_readSlot]
    rw [creditedFee, storageAt_writeSlot_of_ne hacc4 hr', storageAt_readSlot]
    exact storageAt_writeSlot_self hacc3
  · rw [hss]

/-- The end of `transferFrom_fee` in plain terms, for any state `S` in which the contract has an
account: the frame stopped without error; `balances[owner]` (owner read from slot 0 after the
write of `t`) is its word read then plus the fee; when the slots differ, `balances[t]` is its
word after the write of `f` plus `v - fee`; two logs were appended, `Transfer(f, owner', fee)`
then `Transfer(f, t, v - fee)`. -/
theorem transferFrom_fee_effects {S : State.TransactionState}
    (hacc : hasAccount S message.currentTarget) {ss : Substate} {g : Nat} {v t f : U256}
    {evm : Evm fork Nat}
    (h : Local.Stopped g (feeStateF S message v t f) (feeSubF fork ss S message v t f) evm) :
    evm.running = false ∧ evm.error = none ∧
    storageAt evm.state message.currentTarget (ownerSlot (ownerWordF S message v t f)) =
      add (balOF S message v t f) (feeOf S message v) ∧
    (recipientSlot t ≠ ownerSlot (ownerWordF S message v t f) →
      storageAt evm.state message.currentTarget (recipientSlot t) =
        add (balTo S message v t f) (sendOf S message v)) ∧
    evm.substate.logs = (ss.logs.push (transferLog message.currentTarget
      (bitwiseAnd ADDR_MASK f)
      (bitwiseAnd ADDR_MASK (ownerKey (storageAt (ownedB (creditedFeeF S message v t f)
        message.currentTarget (feeOf S message v)) message.currentTarget 0)))
      (feeOf S message v))).push (transferLog message.currentTarget
        (bitwiseAnd ADDR_MASK f) (bitwiseAnd ADDR_MASK t) (sendOf S message v)) := by
  obtain ⟨hr, he, -, hs, hss⟩ := h
  have hacc3 : hasAccount (readsF S message f) message.currentTarget :=
    hasAccount_readSlot (hasAccount_readSlot (hasAccount_readSlot hacc))
  have hacc4 : hasAccount (readSlot (allowedF S message v f) message.currentTarget
      (recipientSlot f)) message.currentTarget :=
    hasAccount_readSlot (hasAccount_allowState hacc3)
  have hacc5 : hasAccount (readSlot (debitedF S message v f) message.currentTarget
      (recipientSlot t)) message.currentTarget :=
    hasAccount_readSlot (hasAccount_writeSlot hacc4)
  have hacc6 : hasAccount (readSlot (readSlot (readSlot (creditedFeeF S message v t f)
      message.currentTarget 0) message.currentTarget
      (ownerSlotOf (creditedFeeF S message v t f) message.currentTarget)) message.currentTarget 0)
      message.currentTarget :=
    hasAccount_readSlot (hasAccount_readSlot (hasAccount_readSlot (hasAccount_writeSlot hacc5)))
  refine ⟨hr, he, ?_, ?_, ?_⟩
  · rw [hs, feeStateF, storageAt_readSlot]
    exact storageAt_writeSlot_self hacc6
  · intro hne
    rw [hs, feeStateF, storageAt_readSlot, ownedB, storageAt_writeSlot_of_ne hacc6 hne]
    simp only [storageAt_readSlot]
    exact storageAt_writeSlot_self hacc5
  · rw [hss]
    show ((ownerLoggedBF fork (creditedSubFeeF fork ss S message v t f)
      (creditedFeeF S message v t f) message _ (feeOf S message v) f).logs).push _ = _
    simp only [allowedSubF]
    rw [logs_allowSub]


/-! ## Local conservation of balances

For each success path, the changes of the balance slots the path writes sum to zero: the sender
loses `v`, the recipient gains `v - fee` and the owner gains `fee` (fee 0 on the `_ok` paths).
This is stated over those slots only, as integer changes between the state `S` after the checks
and the end state. The balance slots are keccak outputs; that they are pairwise distinct (and
distinct from slot 0 and the allowance slot where the owner or the allowance is read in between)
is a hypothesis, never derived. The global statement "the sum of all balances equals
`_totalSupply`" needs a sum over a mapping and is not stated or proved here. -/

/-- The change of slot `k` of `c` from `st` to `st'`, as an integer. -/
def delta (st st' : State.TransactionState) (c : Address) (k : U256) : Int :=
  ((storageAt st' c k).toNat : Int) - ((storageAt st c k).toNat : Int)

theorem toNat_sub_of_le' {a b : U256} (h : b.toNat ≤ a.toNat) :
    (sub a b).toNat = a.toNat - b.toNat :=
  BitVec.toNat_sub_of_le (BitVec.le_def.mpr h)

theorem toNat_add_of_lt' {a b : U256} (h : a.toNat + b.toNat < 2 ^ 256) :
    (add a b).toNat = a.toNat + b.toNat := by
  simp only [add, BitVec.toNat_add, Nat.mod_eq_of_lt h]

theorem storageAt_allowState_of_ne {st : State.TransactionState} {c : Address} {n A v k : U256}
    (h : hasAccount st c) (hne : k ≠ n) :
    storageAt (allowState st c n A v) c k = storageAt st c k := by
  unfold allowState; split
  · rfl
  · exact storageAt_writeSlot_of_ne h hne

/-- Conservation on `transfer_ok` (fee 0): with the sender's and the recipient's slots distinct,
no underflow and no overflow (as the spec's hypotheses, read in `S`), the sender's slot changes by
`-v`, the recipient's by `+v`, and the two changes sum to zero. -/
theorem transfer_ok_conserves {S : State.TransactionState}
    (hacc : hasAccount S message.currentTarget) {ss : Substate} {g : Nat} {v a : U256}
    {evm : Evm fork Nat}
    (h : Local.Stopped g (credited S message v a) (loggedSub fork ss S message v a) evm)
    (hne : recipientSlot a ≠ senderSlot message)
    (hbal : v.toNat ≤ (storageAt S message.currentTarget (senderSlot message)).toNat)
    (hto : (storageAt S message.currentTarget (recipientSlot a)).toNat + v.toNat < 2 ^ 256) :
    delta S evm.state message.currentTarget (senderSlot message) = -(v.toNat : Int) ∧
    delta S evm.state message.currentTarget (recipientSlot a) = (v.toNat : Int) ∧
    delta S evm.state message.currentTarget (senderSlot message) +
      delta S evm.state message.currentTarget (recipientSlot a) = 0 := by
  obtain ⟨-, -, hR, hS, -⟩ := transfer_ok_effects hacc h
  obtain ⟨hS, hT⟩ := hS hne
  rw [hT] at hR
  have h1 : (storageAt evm.state message.currentTarget (senderSlot message)).toNat =
      (storageAt S message.currentTarget (senderSlot message)).toNat - v.toNat := by
    rw [hS]; exact toNat_sub_of_le' hbal
  have h2 : (storageAt evm.state message.currentTarget (recipientSlot a)).toNat =
      (storageAt S message.currentTarget (recipientSlot a)).toNat + v.toNat := by
    rw [hR]; exact toNat_add_of_lt' hto
  simp only [delta]
  omega


/-- The owner word read by `transfer` (slot 0 after the recipient's write) is slot 0 of `S` when
neither balance slot is slot 0. -/
theorem ownerWord_eq {S : State.TransactionState} (hacc : hasAccount S message.currentTarget)
    {v a : U256} (hs0 : senderSlot message ≠ 0) (hr0 : recipientSlot a ≠ 0) :
    ownerWord S message v a = storageAt S message.currentTarget 0 := by
  have hacc3 : hasAccount (reads3 S message) message.currentTarget :=
    hasAccount_readSlot (hasAccount_readSlot (hasAccount_readSlot hacc))
  have hacc4 : hasAccount (readSlot (debited S message v) message.currentTarget
      (recipientSlot a)) message.currentTarget :=
    hasAccount_readSlot (hasAccount_writeSlot hacc3)
  rw [ownerWord, creditedFee, storageAt_writeSlot_of_ne hacc4 (Ne.symm hr0), storageAt_readSlot,
    debited, storageAt_writeSlot_of_ne hacc3 (Ne.symm hs0)]
  simp only [reads3, storageAt_readSlot]

/-- Conservation on `transfer_fee`: write `o` for the owner's balance slot, the owner being the
low 160 bits of slot 0 in `S`. With the sender's, the recipient's and the owner's slots pairwise
distinct, the sender's and the recipient's slots not slot 0, `fee ≤ v`, no underflow of the
sender and no overflow of the recipient and the owner (read in `S`), the sender's slot changes
by `-v`, the recipient's by `+(v - fee)`, the owner's by `+fee`, and the three changes sum to
zero. -/
theorem transfer_fee_conserves {S : State.TransactionState}
    (hacc : hasAccount S message.currentTarget) {ss : Substate} {g : Nat} {v a : U256}
    {evm : Evm fork Nat}
    (h : Local.Stopped g (feeState S message v a) (feeSub fork ss S message v a) evm)
    (hsr : senderSlot message ≠ recipientSlot a)
    (hso : senderSlot message ≠ ownerSlot (storageAt S message.currentTarget 0))
    (hro : recipientSlot a ≠ ownerSlot (storageAt S message.currentTarget 0))
    (hs0 : senderSlot message ≠ 0) (hr0 : recipientSlot a ≠ 0)
    (hfv : (feeOf S message v).toNat ≤ v.toNat)
    (hbal : v.toNat ≤ (storageAt S message.currentTarget (senderSlot message)).toNat)
    (hto : (storageAt S message.currentTarget (recipientSlot a)).toNat +
      (v.toNat - (feeOf S message v).toNat) < 2 ^ 256)
    (hown : (storageAt S message.currentTarget
      (ownerSlot (storageAt S message.currentTarget 0))).toNat + (feeOf S message v).toNat <
        2 ^ 256) :
    delta S evm.state message.currentTarget (senderSlot message) = -(v.toNat : Int) ∧
    delta S evm.state message.currentTarget (recipientSlot a) =
      (v.toNat : Int) - ((feeOf S message v).toNat : Int) ∧
    delta S evm.state message.currentTarget (ownerSlot (storageAt S message.currentTarget 0)) =
      ((feeOf S message v).toNat : Int) ∧
    delta S evm.state message.currentTarget (senderSlot message) +
      delta S evm.state message.currentTarget (recipientSlot a) +
      delta S evm.state message.currentTarget
        (ownerSlot (storageAt S message.currentTarget 0)) = 0 := by
  have hw := ownerWord_eq (v := v) hacc hs0 hr0
  obtain ⟨-, -, hO, hR, hS, -⟩ := transfer_fee_effects hacc h
  rw [hw] at hO hR hS
  have hacc3 : hasAccount (reads3 S message) message.currentTarget :=
    hasAccount_readSlot (hasAccount_readSlot (hasAccount_readSlot hacc))
  have hacc4 : hasAccount (readSlot (debited S message v) message.currentTarget
      (recipientSlot a)) message.currentTarget :=
    hasAccount_readSlot (hasAccount_writeSlot hacc3)
  have hT : balT S message v a = storageAt S message.currentTarget (recipientSlot a) := by
    rw [balT, debited, storageAt_writeSlot_of_ne hacc3 (Ne.symm hsr)]
    simp only [reads3, storageAt_readSlot]
  have hOv : balO S message v a =
      storageAt S message.currentTarget (ownerSlot (storageAt S message.currentTarget 0)) := by
    rw [balO, balOf, ownerSlotOf, ← ownerWord, hw, creditedFee,
      storageAt_writeSlot_of_ne hacc4 (Ne.symm hro), storageAt_readSlot, debited,
      storageAt_writeSlot_of_ne hacc3 (Ne.symm hso)]
    simp only [reads3, storageAt_readSlot]
  have hsend : (sendOf S message v).toNat = v.toNat - (feeOf S message v).toNat :=
    toNat_sub_of_le' hfv
  have h1 : (storageAt evm.state message.currentTarget (senderSlot message)).toNat =
      (storageAt S message.currentTarget (senderSlot message)).toNat - v.toNat := by
    rw [hS hso hsr]; exact toNat_sub_of_le' hbal
  have h2 : (storageAt evm.state message.currentTarget (recipientSlot a)).toNat =
      (storageAt S message.currentTarget (recipientSlot a)).toNat +
        (v.toNat - (feeOf S message v).toNat) := by
    rw [hR hro, hT, toNat_add_of_lt' (by rw [hsend]; exact hto), hsend]
  have h3 : (storageAt evm.state message.currentTarget
      (ownerSlot (storageAt S message.currentTarget 0))).toNat =
      (storageAt S message.currentTarget
        (ownerSlot (storageAt S message.currentTarget 0))).toNat + (feeOf S message v).toNat := by
    rw [hO, hOv]; exact toNat_add_of_lt' hown
  simp only [delta]
  omega

/-- Conservation on `transferFrom_ok` (fee 0): with the slots of `f` and `t` distinct and the
allowance slot distinct from both, no underflow of `f` and no overflow of `t` (read in `S`), the
slot of `f` changes by `-v`, the slot of `t` by `+v`, and the two changes sum to zero. -/
theorem transferFrom_ok_conserves {S : State.TransactionState}
    (hacc : hasAccount S message.currentTarget) {ss : Substate} {g : Nat} {v t f : U256}
    {evm : Evm fork Nat}
    (h : Local.Stopped g (creditedF S message v t f) (loggedSubF fork ss S message v t f) evm)
    (hft : recipientSlot f ≠ recipientSlot t)
    (haf : allowFrom message f ≠ recipientSlot f) (hat : allowFrom message f ≠ recipientSlot t)
    (hbal : v.toNat ≤ (storageAt S message.currentTarget (recipientSlot f)).toNat)
    (hto : (storageAt S message.currentTarget (recipientSlot t)).toNat + v.toNat < 2 ^ 256) :
    delta S evm.state message.currentTarget (recipientSlot f) = -(v.toNat : Int) ∧
    delta S evm.state message.currentTarget (recipientSlot t) = (v.toNat : Int) ∧
    delta S evm.state message.currentTarget (recipientSlot f) +
      delta S evm.state message.currentTarget (recipientSlot t) = 0 := by
  obtain ⟨-, -, hT, hF, -, -⟩ := transferFrom_ok_effects hacc h
  have hacc3 : hasAccount (readsF S message f) message.currentTarget :=
    hasAccount_readSlot (hasAccount_readSlot (hasAccount_readSlot hacc))
  have hacc4 : hasAccount (readSlot (allowedF S message v f) message.currentTarget
      (recipientSlot f)) message.currentTarget :=
    hasAccount_readSlot (hasAccount_allowState hacc3)
  have hFv : balFrom S message v f = storageAt S message.currentTarget (recipientSlot f) := by
    rw [balFrom, allowedF, storageAt_allowState_of_ne hacc3 (Ne.symm haf)]
    simp only [readsF, storageAt_readSlot]
  have hTv : balTo S message v t f = storageAt S message.currentTarget (recipientSlot t) := by
    rw [balTo, debitedF, storageAt_writeSlot_of_ne hacc4 (Ne.symm hft), storageAt_readSlot,
      allowedF, storageAt_allowState_of_ne hacc3 (Ne.symm hat)]
    simp only [readsF, storageAt_readSlot]
  have h1 : (storageAt evm.state message.currentTarget (recipientSlot f)).toNat =
      (storageAt S message.currentTarget (recipientSlot f)).toNat - v.toNat := by
    rw [hF (Ne.symm hft), hFv]; exact toNat_sub_of_le' hbal
  have h2 : (storageAt evm.state message.currentTarget (recipientSlot t)).toNat =
      (storageAt S message.currentTarget (recipientSlot t)).toNat + v.toNat := by
    rw [hT, hTv]; exact toNat_add_of_lt' hto
  simp only [delta]
  omega


/-- The owner word read by `transferFrom` (slot 0 after the write of `t`) is slot 0 of `S` when
neither balance slot nor the allowance slot is slot 0. -/
theorem ownerWordF_eq {S : State.TransactionState} (hacc : hasAccount S message.currentTarget)
    {v t f : U256} (hf0 : recipientSlot f ≠ 0) (ht0 : recipientSlot t ≠ 0)
    (ha0 : allowFrom message f ≠ 0) :
    ownerWordF S message v t f = storageAt S message.currentTarget 0 := by
  have hacc3 : hasAccount (readsF S message f) message.currentTarget :=
    hasAccount_readSlot (hasAccount_readSlot (hasAccount_readSlot hacc))
  have hacc4 : hasAccount (readSlot (allowedF S message v f) message.currentTarget
      (recipientSlot f)) message.currentTarget :=
    hasAccount_readSlot (hasAccount_allowState hacc3)
  have hacc5 : hasAccount (readSlot (debitedF S message v f) message.currentTarget
      (recipientSlot t)) message.currentTarget :=
    hasAccount_readSlot (hasAccount_writeSlot hacc4)
  rw [ownerWordF, creditedFeeF, storageAt_writeSlot_of_ne hacc5 (Ne.symm ht0), storageAt_readSlot,
    debitedF, storageAt_writeSlot_of_ne hacc4 (Ne.symm hf0), storageAt_readSlot, allowedF,
    storageAt_allowState_of_ne hacc3 (Ne.symm ha0)]
  simp only [readsF, storageAt_readSlot]

/-- Conservation on `transferFrom_fee`: write `o` for the owner's balance slot, the owner being
the low 160 bits of slot 0 in `S`. With the slots of `f`, `t` and `o` pairwise distinct, the
allowance slot distinct from all three, none of `f`, `t` and the allowance slot equal to slot 0,
`fee ≤ v`, no underflow of `f` and no overflow of `t` and `o` (read in `S`), the slot of `f`
changes by `-v`, the slot of `t` by `+(v - fee)`, `o` by `+fee`, and the three changes sum to
zero. -/
theorem transferFrom_fee_conserves {S : State.TransactionState}
    (hacc : hasAccount S message.currentTarget) {ss : Substate} {g : Nat} {v t f : U256}
    {evm : Evm fork Nat}
    (h : Local.Stopped g (feeStateF S message v t f) (feeSubF fork ss S message v t f) evm)
    (hft : recipientSlot f ≠ recipientSlot t)
    (hfo : recipientSlot f ≠ ownerSlot (storageAt S message.currentTarget 0))
    (hto' : recipientSlot t ≠ ownerSlot (storageAt S message.currentTarget 0))
    (haf : allowFrom message f ≠ recipientSlot f) (hat : allowFrom message f ≠ recipientSlot t)
    (hao : allowFrom message f ≠ ownerSlot (storageAt S message.currentTarget 0))
    (hf0 : recipientSlot f ≠ 0) (ht0 : recipientSlot t ≠ 0) (ha0 : allowFrom message f ≠ 0)
    (hfv : (feeOf S message v).toNat ≤ v.toNat)
    (hbal : v.toNat ≤ (storageAt S message.currentTarget (recipientSlot f)).toNat)
    (hto : (storageAt S message.currentTarget (recipientSlot t)).toNat +
      (v.toNat - (feeOf S message v).toNat) < 2 ^ 256)
    (hown : (storageAt S message.currentTarget
      (ownerSlot (storageAt S message.currentTarget 0))).toNat + (feeOf S message v).toNat <
        2 ^ 256) :
    delta S evm.state message.currentTarget (recipientSlot f) = -(v.toNat : Int) ∧
    delta S evm.state message.currentTarget (recipientSlot t) =
      (v.toNat : Int) - ((feeOf S message v).toNat : Int) ∧
    delta S evm.state message.currentTarget (ownerSlot (storageAt S message.currentTarget 0)) =
      ((feeOf S message v).toNat : Int) ∧
    delta S evm.state message.currentTarget (recipientSlot f) +
      delta S evm.state message.currentTarget (recipientSlot t) +
      delta S evm.state message.currentTarget
        (ownerSlot (storageAt S message.currentTarget 0)) = 0 := by
  have hw := ownerWordF_eq (v := v) (t := t) hacc hf0 ht0 ha0
  obtain ⟨-, -, hO, hR, -⟩ := transferFrom_fee_effects hacc h
  obtain ⟨-, -, -, hst, -⟩ := h
  rw [hw] at hO hR
  have hacc3 : hasAccount (readsF S message f) message.currentTarget :=
    hasAccount_readSlot (hasAccount_readSlot (hasAccount_readSlot hacc))
  have hacc4 : hasAccount (readSlot (allowedF S message v f) message.currentTarget
      (recipientSlot f)) message.currentTarget :=
    hasAccount_readSlot (hasAccount_allowState hacc3)
  have hacc5 : hasAccount (readSlot (debitedF S message v f) message.currentTarget
      (recipientSlot t)) message.currentTarget :=
    hasAccount_readSlot (hasAccount_writeSlot hacc4)
  have hacc6 : hasAccount (readSlot (readSlot (readSlot (creditedFeeF S message v t f)
      message.currentTarget 0) message.currentTarget
      (ownerSlotOf (creditedFeeF S message v t f) message.currentTarget)) message.currentTarget 0)
      message.currentTarget :=
    hasAccount_readSlot (hasAccount_readSlot (hasAccount_readSlot (hasAccount_writeSlot hacc5)))
  have hFv : balFrom S message v f = storageAt S message.currentTarget (recipientSlot f) := by
    rw [balFrom, allowedF, storageAt_allowState_of_ne hacc3 (Ne.symm haf)]
    simp only [readsF, storageAt_readSlot]
  have hTv : balTo S message v t f = storageAt S message.currentTarget (recipientSlot t) := by
    rw [balTo, debitedF, storageAt_writeSlot_of_ne hacc4 (Ne.symm hft), storageAt_readSlot,
      allowedF, storageAt_allowState_of_ne hacc3 (Ne.symm hat)]
    simp only [readsF, storageAt_readSlot]
  have hOv : balOF S message v t f =
      storageAt S message.currentTarget (ownerSlot (storageAt S message.currentTarget 0)) := by
    rw [balOF, balOf, ownerSlotOf, ← ownerWordF, hw, creditedFeeF,
      storageAt_writeSlot_of_ne hacc5 (Ne.symm hto'), storageAt_readSlot, debitedF,
      storageAt_writeSlot_of_ne hacc4 (Ne.symm hfo), storageAt_readSlot, allowedF,
      storageAt_allowState_of_ne hacc3 hao.symm]
    simp only [readsF, storageAt_readSlot]
  have hF : storageAt evm.state message.currentTarget (recipientSlot f) =
      sub (balFrom S message v f) v := by
    have hfo' : recipientSlot f ≠ ownerSlotOf (creditedFeeF S message v t f)
        message.currentTarget := by
      rw [ownerSlotOf, ← ownerWordF, hw]; exact hfo
    rw [hst, feeStateF, storageAt_readSlot, ownedB, storageAt_writeSlot_of_ne hacc6 hfo']
    simp only [storageAt_readSlot]
    rw [creditedFeeF, storageAt_writeSlot_of_ne hacc5 hft, storageAt_readSlot]
    exact storageAt_writeSlot_self hacc4
  have hsend : (sendOf S message v).toNat = v.toNat - (feeOf S message v).toNat :=
    toNat_sub_of_le' hfv
  have h1 : (storageAt evm.state message.currentTarget (recipientSlot f)).toNat =
      (storageAt S message.currentTarget (recipientSlot f)).toNat - v.toNat := by
    rw [hF, hFv]; exact toNat_sub_of_le' hbal
  have h2 : (storageAt evm.state message.currentTarget (recipientSlot t)).toNat =
      (storageAt S message.currentTarget (recipientSlot t)).toNat +
        (v.toNat - (feeOf S message v).toNat) := by
    rw [hR hto', hTv, toNat_add_of_lt' (by rw [hsend]; exact hto), hsend]
  have h3 : (storageAt evm.state message.currentTarget
      (ownerSlot (storageAt S message.currentTarget 0))).toNat =
      (storageAt S message.currentTarget
        (ownerSlot (storageAt S message.currentTarget 0))).toNat + (feeOf S message v).toNat := by
    rw [hO, hOv]; exact toNat_add_of_lt' hown
  simp only [delta]
  omega

end UsdtVerify.Summary
