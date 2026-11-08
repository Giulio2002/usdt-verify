import Batteries.Tactic.Alias
import UsdtVerify.Usdt.Complete.Dispatch
import UsdtVerify.Usdt.Complete.Read
import UsdtVerify.Usdt.Complete.Transfer
import UsdtVerify.Usdt.Complete.Approve
import UsdtVerify.Usdt.Complete.TransferFrom
import UsdtVerify.Usdt.Complete.Owner
import UsdtVerify.Usdt.Complete.Getters
import UsdtVerify.Usdt.Complete.Deprecated.Transfer
import UsdtVerify.Usdt.Complete.Deprecated.Allowance
import UsdtVerify.Usdt.Complete.Deprecated.Destroy
import UsdtVerify.Usdt.Spec.TotalSupply
import UsdtVerify.Usdt.Spec.BalanceOf
import UsdtVerify.Usdt.Proofs.Transfer
import UsdtVerify.Usdt.Spec.Transfer
import UsdtVerify.Usdt.Spec.Approve
import UsdtVerify.Usdt.Spec.TransferFrom
import UsdtVerify.Usdt.Spec.Deprecated.BalanceOf
import UsdtVerify.Usdt.Spec.Deprecated.TransferFrom
import UsdtVerify.Usdt.Spec.Dispatch
import UsdtVerify.Usdt.Spec.Pause
import UsdtVerify.Usdt.Spec.BlackList
import UsdtVerify.Usdt.Spec.Issue
import UsdtVerify.Usdt.Spec.SetParams
import UsdtVerify.Usdt.Spec.AddrWrite
import UsdtVerify.Usdt.Spec.Destroy
import UsdtVerify.Usdt.Spec.Getters
import UsdtVerify.Usdt.Spec.RunFrames
import UsdtVerify.Usdt.Spec.Strings
import UsdtVerify.Usdt.Spec.Deprecated.Allowance
import UsdtVerify.Usdt.Spec.Deprecated.Destroy

/-!
# Summary: what is proved about the deployed USDT bytecode

All theorems are about the 11075-byte runtime code `CODE` (data/usdt.runtime.hex), run by
EthLib's EVM semantics from pc 0 in a fresh frame (`At CODE message 0 [] .empty gas state
substate`), for every fork from Berlin on. The paths that write storage hold from Berlin on,
Glamsterdam included, since round 17: each SSTORE costs `Gas.writeCost` (`sstoreCost` plus the
state gas of a new slot, `sstoreStateGas`, 0 before Glamsterdam), by the local rule
`Gas.sstoreWG`. The deprecated paths hold at the same forks since round 19: EXTCODESIZE costs
`extCost fork` (EthLib's `externalBaseCost`: 2600 cold / 100 warm before Glamsterdam, the access
plus 100 from Glamsterdam, EIP-8038; local rule `Local.extcodesize`), every account access
`accCost fork` (3000 cold from Glamsterdam), and the CALL rules (`callStep_child_r`, `callWithR`
and the step lemmas of Evm/Call.lean) cover the order of the charges at Glamsterdam. Each non-deprecated path is a `SpecG` (round 12: a `Spec` over
the steps from frames where the same step with less gas fails or gives the same frame with that
much less gas; it implies the `Spec`), each deprecated path a `Spec`: every run from such a
frame reaches an end
frame satisfying the postcondition; `runFrame_*` theorems state the same about the interpreter
loop `runFrame` for every gas bound and message runner. Common hypotheses of every path below:
the call data has the function's selector in its first 4 bytes and fewer than 2^256 bytes, the
call has no value, and there is enough gas (an exact cost, given in each theorem; a path that
writes storage also needs more than 2300 gas left at an SSTORE where stated).
Static frame and account, by name:
`hstatic` is `message.isStatic = false`; `hacc` is an account of `C` in the start state.
These specs take both `hstatic` and `hacc`: `transfer_toOv`, `transfer_ownerOv`, `transfer_ok`,
`transfer_fee`, `approve_zero`, `approve_set`, `transferFrom_toOv`, `transferFrom_ownerOv`,
`transferFrom_ok`, `transferFrom_fee`, `pause`, `unpause`, `addBlackList`, `removeBlackList`,
`issue`, `redeem`, `setParams`, `setParams_mulOv`, `deprecate`, `transferOwnership`,
`destroyBlackFunds`, and their `runFrame_*` forms.
`transferFrom_balLow` and `transferFrom_feeGt` take both only when the allowance is not
`MAX_UINT` (`hgood`); their forms `TransferFrom.runFrame_balLow` and
`TransferFrom.runFrame_feeGtF` take both unconditionally.
`destroyBlackFunds_dep`, `destroyBlackFunds_dep_answers` and `destroyBlackFunds_dep_fails` take
`hstatic` and `hkeep` (an account of `C` in the end state of each forwarded call that ends with
no error).
`runFrame_destroyBlackFunds_dep_process` takes `hstatic`, and its `hQ` asks for that account.
The `*_effects` and `*_conserves` theorems, `listState_flag`, `listState_other`, `ownerWord_eq`,
`ownerWordF_eq` and `storageAt_allowState_of_ne` take an account of `C` in the state they are
about.
No other spec or `runFrame_*` theorem below takes `hstatic` or `hacc`.
The completeness theorems (`*_complete`, `*_dep_complete`) take neither. "Not paused",
"not deprecated" mean byte 20 of slot 0, of slot 10 is 0; "x blacklisted" means the low byte of
`isBlackListed[x]` (slot `keccak(x ++ 6)`) is not 0. `S` is the state after the reads of the
checks. `C` is the contract. `fee = min(v * basisPointsRate / 10000, maximumFee)` (slots 3, 4) as
the bytecode computes it (`feeOf`). Balances are the words of `balances[x]` = slot
`keccak(x ++ 2)`; allowances of `allowed[x][y]` = slot `keccak(y ++ keccak(x ++ 5))`.

The end conditions: `Halted false .empty` after STOP (no error, empty output: transfer and the
other STOP paths return no bytes; the state and substate given, gas left exact), `Halted false
out` after RETURN, `Halted true .empty` (REVERT, no output; the caller rolls the state back),
`Faulted (.invalidOpcode 0xfe)` (a failed SafeMath assert: no output, no gas left; the caller
discards the state). The writes of the success paths are stated as the sequence
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
(`0 < |c|`), and the CALL along a route `r` (`Routes`: no delegation, or from Pectra an EIP-7702
delegate `d` whose code `c'` is found; the CALL then pays the access to `d` too, and the message
runs `c'` at `d` with `ua` as its current target), the theorems are `SpecUnder` triples: they
hold under every runner of messages that meets a callee assumption `callee`, and say nothing
when the runner aborts.
- `totalSupply_dep` / `balanceOf_dep` (any `callee`): the frame sends `ua` one message with no
  value and data `0x18160ddd` / `0x70a08231 ++ who` along the route (`SendsVia`); if that call ends with
  no error, the frame returns the word at 0x60 after the first `min 32 |output|` output bytes were
  copied there; if it ends with an error, the frame reverts with no output.
- `totalSupply_dep_answers` / `balanceOf_dep_answers`: a callee that answers `o` (`|o| ≥ 32`) ⇒ the
  frame returns `wordBytes (loadWord o 0 32)`. `*_dep_fails`: a failing callee ⇒ REVERT, no output.
- `totalSupply_dep_process` / `balanceOf_dep_process`: the same with the interpreter's own runner
  `processRunner`, for any code of the route with a `Spec` (EthLib's `meets_of_spec`, `RunsAs`).
- `totalSupply_depNoCode` / `balanceOf_depNoCode`: empty code at `ua` ⇒ REVERT before any call.

## Deprecated: transfer, approve, transferFrom forward to `upgradedAddress` (no output range)
With byte 20 of slot 10 set and `ua` holding a code `c` as above. The hypotheses are bundled in
`HypT` / `HypA` / `HypF` (fork range, selector, no value, deprecated, the code at `ua`, its route, depth,
coldness flags; transfer: not paused and caller not blacklisted; transferFrom: not paused and `f`
not blacklisted; approve: call data ≥ 68 bytes, its own payload check comes first). transfer and
transferFrom need only call data ≥ 4 bytes on this path (the payload checks are in BasicToken /
StandardToken, which are not reached).
- `transfer_dep` / `approve_dep` / `transferFrom_dep` (any `callee`): the frame sends `ua` one
  message along the route (`SendsVia`) with no value, the gas of EIP-150, and the data
  `0x6e18980a ++ caller ++ to ++ v` (`transferByLegacy`, `dataT`),
  `0xaee92d33 ++ caller ++ s ++ v` (`approveByLegacy`, `dataA`),
  `0x8b477adb ++ caller ++ f ++ t ++ v` (`transferFromByLegacy`, `dataF`), each address argument
  as a word masked to 160 bits; the CALL has an output range of size 0. If that call ends with no
  error, the frame STOPs with no error (`Halted false .empty`); if it ends with an error, it reverts
  with no output. Gas left, state and substate: exact (after the call, `incorporateChild`).
- `*_dep_succeeds`: a callee that ends every such message with no error ⇒ STOP, no error, state and
  substate from `incorporateChild` of the callee's frame. `*_dep_fails`: REVERT, no output.
- `*_dep_process`: the interpreter's own runner `processRunner`, for any code of the route with a `Spec`
  whose stopped frames have no error (`meets_of_spec`, `RunsAs`) ⇒ STOP with no error, or abort.
- `*_depNoCode`: empty code at `ua` ⇒ REVERT before any call.
What the upgraded contract does with the forwarded call (the balances it changes) is the callee's
business: nothing is assumed or proved about it beyond the callee assumption.

## Nonzero call value — `nonpayable`, `runFrame_nonpayable`
Every one of the 32 functions is nonpayable, and each entry of the selector table starts with
its own copy of `JUMPDEST CALLVALUE ISZERO PUSH2 JUMPI PUSH1 0 DUP1 REVERT`. For `i : Fin 32`,
call data of 4 to 2^256 - 1 bytes whose selector is the key of entry `i` of `ENTRIES` (the table
in bytecode order, docs/MAP.md) and a nonzero value ⇒ REVERT with no output, before any storage
read: state and substate unchanged, gas left `gas - (87 + 22 * (i + 1))`.

## Owner functions: the `onlyOwner` check (Usdt/Proofs/Owner.lean)
`owner` = the low 160 bits of slot 0 (`ownerOf`); the caller is compared as
`caller & (2^160 - 1)` (`callerWord`). The check is inlined in each owner function; `ownerOk` /
`ownerRevert` cover all ten copies (`CHECKS`). A caller other than the owner gets REVERT with no
output after reading slot 0.
Every `spec_*` of rounds 7 and 8 from pc 0 has a `runFrame_*` wrapper in the same namespace
(Usdt/Spec/RunFrames.lean, generated from the statements; each proof applies EthLib's `Spec.runFrame`).

## pause() 0x8456cb59 / unpause() 0x3f4ba83a (Usdt/Spec/Pause.lean)
`paused` is byte 20 of slot 0.
- `pause_notOwner` / `unpause_notOwner`: caller ≠ owner ⇒ REVERT, no output.
- `pause_paused`: owner, byte 20 ≠ 0 ⇒ REVERT (`whenNotPaused`).
  `unpause_notPaused`: owner, byte 20 = 0 ⇒ REVERT (`whenPaused`).
- `pause` (owner, byte 20 = 0) / `unpause` (owner, byte 20 ≠ 0): STOP; slot 0 :=
  `withPaused w0 1` / `withPaused w0 0`; one log with the topic of `Pause()` / `Unpause()` and no
  data. `withPaused w b` has byte 20 = b (`byte20_withPaused`), the same owner
  (`owner_withPaused`), and every bit outside 160..167 of `w` (`bit_withPaused`).

## addBlackList(a) 0x0ecb93c0 / removeBlackList(a) 0xe4997dc5 (Usdt/Spec/BlackList.lean)
`a` = argument word 0 masked to 160 bits; `L = keccak(a ++ 6)` (`listSlot a`).
- `addBlackList_notOwner` / `removeBlackList_notOwner`: caller ≠ owner ⇒ REVERT, no output.
- `addBlackList` / `removeBlackList` (owner): STOP; slot 0 read; `L := setLow w 1` / `setLow w 0`
  (`w` the word of `L`); one log `AddedBlackList(a)` / `RemovedBlackList(a)` with data the word
  `a`. The old flag is not read. `listState_flag`: the low byte of `L` is then 1 / 0;
  `listState_other`: every other slot is unchanged.

## issue(a) 0xcc872b66 / redeem(a) 0xdb006a75 (Usdt/Spec/Issue.lean)
`a` = argument word 0; `T` = slot 1 (`_totalSupply`); `O = keccak(owner ++ 2)` (`ownerBal`),
`B` its word.
- `issue_notOwner` / `redeem_notOwner`: caller ≠ owner ⇒ REVERT.
- `issue_req1`: owner, `¬(0 < a ∧ T + a < 2^256)` ⇒ REVERT (so `issue(0)` reverts).
  `issue_req2`: the first passes, `¬(0 < a ∧ B + a < 2^256)` ⇒ REVERT.
- `redeem_req1`: owner, `T < a` ⇒ REVERT. `redeem_req2`: `a ≤ T`, `B < a` ⇒ REVERT.
- `issue` (owner, `0 < a`, `T + a < 2^256`, `B + a < 2^256`): STOP; `O := B + a`, then
  slot 1 `:= T' + a` (read after the first write); log `Issue(a)` (data the word `a`).
- `redeem` (owner, `a ≤ T`, `a ≤ B`): STOP; slot 1 `:= T - a`, then `O := B' - a`; log
  `Redeem(a)`.
- `issue_effects` / `redeem_effects`: with `O ≠ 1` (assumed; `O` is a keccak output), the end
  words are `B ± a` and `T ± a` as numbers, and every other slot is unchanged.

## setParams(b, m) 0xc0324c77 (Usdt/Spec/SetParams.lean)
`b`, `m` = argument words 0, 1; `d` = slot 9 (`decimals`); `f = m * 10^d` (EVM words).
- `setParams_notOwner`: caller ≠ owner ⇒ REVERT. `setParams_bpHigh`: owner, `b ≥ 20` ⇒ REVERT.
  `setParams_feeHigh`: owner, `b < 20`, `m ≥ 50` ⇒ REVERT.
- `setParams` (owner, `b < 20`, `m < 50`, `m * 10^d < 2^256`): STOP; slot 3 := `b`, slot 4 :=
  `f` (SafeMath `mul`); log `Params(b, f)` (data the two words, read back from slots 3 and 4).
  `params_effects`: slot 3 = `b`, slot 4 = `f`, every other slot unchanged.
  The `mul` overflow (INVALID; needs `d ≥ 75`) is not covered.

## deprecate(a) 0x0753c30c / transferOwnership(a) 0xf2fde38b (Usdt/Spec/AddrWrite.lean)
`a` = argument word 0 masked to 160 bits. `withAddr w a` = `w` with its low 160 bits from `a`.
- `deprecate_notOwner` / `transferOwnership_notOwner`: caller ≠ owner ⇒ REVERT.
- `deprecate` (owner): STOP; slot 10 := `withPaused w10 1`, then slot 10 :=
  `withAddr (withPaused w10 1) a`; log `Deprecate(a)`. `deprecate_effects`: `deprecated`
  (byte 20 of slot 10) = 1, `upgradedAddress` (low 160 bits) = `a`, other slots unchanged.
- `transferOwnership_zero` (owner, `a = 0`): STOP, only slot 0 read, nothing written, no log.
  `transferOwnership` (owner, `a ≠ 0`): STOP; slot 0 := `withAddr w0 a`; no log.
  `transferOwnership_effects`: the owner is `a`, `paused` is kept, other slots unchanged.

## destroyBlackFunds(a) 0xf3bdc228 (Usdt/Spec/Destroy.lean)
`a` = argument word 0 masked to 160 bits; `B = keccak(a ++ 2)` (`balSlot`), `d` its word
(`dirty`); `T` = slot 1.
- `destroyBlackFunds_notOwner`: caller ≠ owner ⇒ REVERT. `destroyBlackFunds_notListed`: owner,
  `a` not blacklisted ⇒ REVERT.
- `destroyBlackFunds` (owner, `a` blacklisted, not deprecated): STOP; reads slot 0,
  `isBlackListed[a]`, slot 10 and `B` (TetherToken's own `balanceOf` getter, reached by an
  internal call); `B := 0`, then slot 1 `:= T' - d` (unchecked; `T'` read after the first
  write); log `DestroyedBlackFunds(a, d)` (topic 0x61e6e66b…, data the words `a` and `d`).
  Gas `2865 +` the five read prices `+` the two write prices. `runFrame_destroyBlackFunds`.
  `destroyBlackFunds_effects`: with `B ≠ 1`, `B` is 0, slot 1 is `T - d` as a word (as numbers
  when `d ≤ T`), every other slot unchanged.
- Deprecated (`destroyBlackFunds_dep`, Usdt/Spec/Deprecated/Destroy.lean): owner, `a` blacklisted, byte 20
  of slot 10 set, `ua` holding a code `c`, any route. The internal `balanceOf(a)` sends `ua` one
  message along the route with data `0x70a08231 ++ a` (`dataB`) and no value; it never reads `B`. If the call fails: REVERT, no
  output. If it ends with no error, with `S`, `ss` the state and substate it left and `d` the word
  at 0x60 after the copy of its output: STOP in `tailState S C a d` (`B := 0` in THIS contract,
  then slot 1 `:= T' - d`, unchecked), substate `tailSub` (log `DestroyedBlackFunds(a, d)`), gas
  exact (`tailCost`; `B` may be cold). Hypotheses beyond the usual: at least `TAIL_MAX fork` (47881
  before Glamsterdam, 223721 from Glamsterdam) gas after the CALL's price, a frame that is not
  static, and `hkeep` (the callee leaves the contract's account in place). (The completeness
  theorem `destroyBlackFunds_dep_complete` below needs neither of the last two.)
  So `_totalSupply` drops by the balance that the UPGRADED contract reports, while the local
  `balances[a]` (whatever it held) becomes 0. `destroyBlackFunds_dep_answers` (a callee answering
  `o`, ≥ 32 bytes: STOP, state `tailState S C a (first word of o)` for some `S`),
  `destroyBlackFunds_dep_fails`, `runFrame_destroyBlackFunds_dep_process` (EthLib's runner,
  upgraded code with a `Spec`), `destroyBlackFunds_depNoCode` (empty code: REVERT before any
  call, gas `1497 +` slots 0, `isBlackListed[a]`, 10 `+` address).

## Getters (Usdt/Spec/Getters.lean)
Each returns 32 bytes and only reads; `a`, `a0`, `a1` are argument words masked to 160 bits.
- `decimals`, `maximumFee`, `totalSupplyVar` (`_totalSupply()`), `basisPointsRate`: the word of
  slot 9, 4, 1, 3 (`getter_slot` covers the four).
- `maxUint` (`MAX_UINT()`): the word 2^256 - 1, no read.
- `deprecatedFlag` (`deprecated()`), `pausedFlag` (`paused()`): the word 1 if byte 20 of slot 10
  / slot 0 is nonzero, else 0.
- `upgradedAddress`: the low 160 bits of slot 10. `owner`, `getOwner`: the low 160 bits of slot
  0 (`ownerOf`).
- `balances(a)`: `balances[a]` (no deprecation check). `isBlackListed(a)`,
  `getBlackListStatus(a)`: 1 if the low byte of `isBlackListed[a]` is nonzero, else 0.
- `allowed(a0, a1)`: `allowed[a0][a1]`, slot `keccak(a1 ++ keccak(a0 ++ 5))`; `allowance(a0, a1)`,
  not deprecated: the same word, after reading slot 10. (Deprecated allowance is not covered.)

## name(), symbol() — `name`, `symbol`, `name_tether`, `symbol_usdt`
name() reads slot 7, symbol() slot 8 (`string`). For a slot word `w` in Solidity's short form
with `n` bytes, 1 ≤ n ≤ 31 (`w mod 256 = 2n`): the run returns 96 bytes, the word 0x20 (offset),
the word n (length), and `topBytes w n` (the first n bytes of `w`, then zeros); the slot is read
three times (first at the cold/warm price, then warm); gas `1010 + slot` / `1450 + slot`.
For the words of "Tether USD" and "USDT" (`NAME_WORD`, `SYMBOL_WORD`) the data word is the UTF-8
bytes of the string padded with zeros.
Empty string (`name_empty`, `symbol_empty`; Usdt/Spec/Strings.lean): low byte of the slot 0 ⇒ returns
the word 0x20 and the word 0; slot read twice; gas `643 + slot` / `1083 + slot`.
Long form (`name_long`, `symbol_long`): slot word odd, `N = w / 2`, 32 ≤ N < 2^180 ⇒ returns the
word 0x20, the word N, and `strData` of the words of slots `keccak(k) + i`, i < ceil(N/32): the
N/32 whole words, then (when 32 ∤ N) the first N mod 32 bytes of the next word followed by zeros.
Slot `k` read twice, the data slots once each in order (`rdSt`, `rdSs`); gas exact (`rdGas` for
the data reads, EthLib's `memoryGasCost` for the memory). With `spec_name`/`spec_symbol` this
covers every slot word that Solidity writes for a string (short form `2n`, n ≤ 31; long form
`2n + 1`, n ≥ 32, below the 2^180 bound). Not covered: odd words with `w / 2 < 32` (Solidity
never writes them).

## allowance(owner, spender) when deprecated — `allowance_dep`, `allowance_dep_answers`, ...
With byte 20 of slot 10 set and `ua` holding a code `c`, any route: the frame sends `ua` one
message along the route (`SendsVia`) with no value, the gas of EIP-150, and the data `0xdd62ed3e ++ owner ++ spender`
(`dataAl`, each argument word masked to 160 bits, 68 bytes); the CALL's output range is 32 bytes
at 0x60. If that call ends with no error the frame returns the word at 0x60 after the copy of the
callee's output; otherwise it reverts with no output. `*_answers`: a callee that answers `o`
(≥ 32 bytes) ⇒ the run returns the first word of `o`. `*_fails` ⇒ REVERT, no output.
`runFrame_allowance_dep_process`: the interpreter's own runner, for upgraded code with a `Spec`.
`allowance_depNoCode`: empty code at `ua` ⇒ REVERT before any call (gas `1184 + slot 10 +
address`).

## A call that names no function — `fallback_unknown`, `fallback_short`
TetherToken has no fallback function; both paths end at 406 (`JUMPDEST PUSH1 0 DUP1 REVERT`) and
neither checks the call value. Call data of 4 bytes or more whose selector is no key of the
32-entry table ⇒ REVERT, no output, state and substate unchanged, gas 773. Fewer than 4 bytes ⇒
REVERT, no output, unchanged, gas 46.

## The global invariant (Usdt/Invariant/Supply.lean, imports this file)
`Inv C S`: the sum over the 2^160 addresses of `balances[a]` equals `_totalSupply` (slot 1).
Under the keccak hypothesis `KeccakSep` (stated, not proved), the end state of every proved
success path that writes is reached by `Steps` (`reach_*`), and `steps_inv` keeps `Inv` along any
finite sequence of steps; read-only paths only record reads (`inv_readSlot`, `inv_rdSt`).
destroyBlackFunds keeps `Inv`: under `Inv`, `d ≤ _totalSupply`, so its unchecked subtraction does
not wrap (`destroy_inv`).
Every successful call, not deprecated, static or not, with or without an account:
`Complete.inv_call`. Deprecated or not: `Complete.inv_call_ns` (Usdt/Invariant/All.lean, from
Berlin, Glamsterdam included; when deprecated, under the named assumptions `KeepsInv` on the
runner and `HonestBalance` for destroyBlackFunds, and since round 20 with no account of the
contract assumed; the upgraded code may be an EIP-7702 delegation). Static or not:
`Complete.inv_call_all` (Usdt/Invariant/Static.lean; "not static" replaced by `hstat`: when static,
`message.code = CODE`, `StaticCode` and `StaticKeeps`; a static frame keeps the state, EthLib's `staticStep_runFrame`, under the named runner
assumption `StaticKeeps`, proved for the interpreter's runner from Paris by
`staticKeeps_process`). Along a finite sequence of such calls and of steps that keep the storage
of `C`: `Complete.inv_calls` (Usdt/Invariant/Seq.lean); a successful top-level `processMessage` of
`CODE` with no value and no precompile, from Paris (Glamsterdam included), under
the named assumptions, is such a call (`Complete.goodCall_process`); a top-level
`processMessage` (any code, any fork) that ends with an error keeps every storage word
(`Complete.untouched_process_failed`), one of `CODE` with no precompile, call data below 2^256
bytes and a nonzero value always ends with an error from Berlin
(`Complete.process_value_fails`), and from Paris (Glamsterdam included) every
top-level `processMessage` of `CODE` with no precompile, under the hypotheses of
`goodCall_process` except "no value", is one of the two kinds of steps (`Complete.process_step`).
None
has an alias here, since Invariant imports this file.

## Security properties (Usdt/Security/, round 22; they import this file)
Over every successful run of a fresh frame of `CODE`, from Berlin (Glamsterdam included), static
or not, any call data below 2^256 bytes, any value, any gas, bound and runner, not deprecated
(`hdep`), slots 7 and 8 of `StrForm` (`h7`, `h8`; not taken by `transferFrom_bound`):
`Security.effect_call` classifies the end state (`Effect`). Under `KeccakSep`, and `AllowSep`
where named (a slot of `allowed` is none of the slots 0..10 and no slot of `isBlackListed`;
not proved):
`Security.nonOwner_call` (a caller other than the owner, the low 160 bits of slot 0, changes only
slots of `balances` and `allowed`; slots 0, 1, 3, 4, 10 and the blacklist slots keep their words;
`AllowSep`), `Security.paused_call` (when paused, every balance keeps its word, or it is the
owner's issue, redeem or destroyBlackFunds), `Security.listed_call` (a blacklisted address word's
balance does not decrease, except by the owner's redeem or destroyBlackFunds),
`Security.transferFrom_bound` (`v ≤ A` unless `A = MAX_UINT`; `balances[_from]` falls by at most
`v`; the allowance becomes `A - v`, or stays `MAX_UINT`), `Security.allowKept_call` (only approve
and transferFrom change a slot of `allowed`; `AllowSep`), `Security.supply_call` (slot 1 changes
only by the owner's issue `+ v`, redeem `- v`, destroyBlackFunds `- balances[a]`, unchecked).
Over sequences (`Security.Seq`, with `Untouched` steps): `nonOwner_seq`, `paused_seq`,
`listed_seq` (calls by callers other than the owner; the start state not deprecated, with
`StrForm`), `allowKept_seq`, `supply_seq` (calls of the other functions, each not deprecated with
`StrForm` at its start). See docs/RESULTS.md for the exact statements.

## Security properties deprecated or not (round 23)
`Security.effect_all` (no `hdep`, no runner assumption; `StrForm` of slots 7 and 8): `EffectD`, an `Effect`, or one of the six
forwards (end state = the child's end state of one call to the upgraded address from a state with
the start storage of the contract), or the owner's deprecated destroyBlackFunds (that call, then
`balances[a] := 0`, slot 1 `:=` (slot 1 of the child's end state) `- d`, for some word `d`). `Security.effect_local`: the 25 functions outside
`FlagFn` have their `Effect` deprecated or not. With a runner assumption `Keeps…` taken only when
deprecated (`hkeeps`): `Security.nonOwner_call_all` (`KeepsSlots`; the `Protected` slots keep
their words), `Security.paused_call_all` (`KeepsBal`), `Security.listed_call_all`
(`KeepsListed`), `Security.allowKept_call_all` (`KeepsAllow`), `Security.supply_call_all`
(`KeepsSupply`; `SupplyStepD`), and the `_seq_all` forms over `SeqR`. With no runner assumption:
`Security.owner_only` (the ten `onlyOwner` functions succeed only for the owner),
`Security.nonOwner_local` (non-owner calls of functions outside the six forwards),
`Security.transfer_checks_all`, `Security.transferFrom_checks_all` (not paused, sender or
`_from` not blacklisted). See docs/RESULTS.md, "Security properties, deprecated or not".

## Non-vacuity (round 24; Usdt/Sanity/, which imports this file)
Concrete runners meet the runner assumptions. `stopRunner` is EthLib's `processRunner` on the
messages to `ua` that run the one byte STOP, and it fails every other message to `ua`. It meets
`KeepsSlots`, `KeepsBal`, `KeepsListed`, `KeepsAllow`, `KeepsSupply` and `KeepsInv`, and from Paris
`StaticKeeps`. `balRunner` keeps the state and answers the word of `balances[x]`. It meets all six,
`StaticKeeps` and `HonestBalance` (`Sanity.runner_assumptions_hold`).
For every fork from Berlin, block, transaction, contract address and substate, each of these
gives a call, a start state and a gas where every hypothesis of a spec theorem holds, with a run
under `processRunner` that ends with no error: `Sanity.transfer_ok_sat`,
`Sanity.transferFrom_ok_sat`, `Sanity.approve_set_sat`, `Sanity.issue_sat`, `Sanity.redeem_sat`
and `Sanity.destroy_sat`. No keccak fact is used.
Under `KeccakSep`, and `AllowSep` where needed, the `Sanity.*_applies` theorems apply the
security theorems, `inv_call_ns` and `inv_call_all` to such runs. They discharge every other
hypothesis. No witness run is deprecated.
`Sanity.strForm_name` and `Sanity.strForm_symbol`: the words of "Tether USD" and "USDT" are of
`StrForm`. `Sanity.strings_applies`: under `KeccakSep`, `inv_call_all` and `supply_call` apply with
those words in slots 7 and 8.

## Completeness of the dispatcher, for every gas — `dispatch_complete` (UsdtVerify/Complete/)
From Berlin, a fresh frame of `CODE` at pc 0, call data of size below 2^256, ANY gas, any gas
bound and any message runner: if the loop of the interpreter ends with no error, then the call
data has at least 4 bytes, its selector is the key of one of the 32 entries of the table, and the
call value is 0. Out of gas is covered by `Gas.SpecG.low`: a run with less gas that ends with no
error ends as the run with more gas, with exactly that much less gas left (the steps it follows
are steps of `Gas.StepG`, from frames whose instruction is `Gas.RunMono`).

## Not proved
See docs/STATUS.md ("Open").

## Completeness per function — `totalSupply_complete`, `balanceOf_complete`, `transfer_complete`
Not deprecated, Berlin on: every run of the loop that ends with no error, for any gas, is the success path of the
specification, with the exact output, gas, state and substate. For transfer, the conclusion
also lists every check the run passed, and the end is the fee-0 path or the fee path.

Round 13, same method: `approve_complete` (not deprecated; `v = 0`, or `v ≠ 0` over an allowance
of 0; the new revert `Approve.spec_payload` excludes call data below 68 bytes),
`transferFrom_complete` (not deprecated; every check, then fee 0 or fee > 0), and the owner
functions `pause_complete`, `unpause_complete`, `addBlackList_complete`,
`removeBlackList_complete`, `issue_complete`, `redeem_complete`, `setParams_complete` (the new
INVALID spec `SetParamsSpec.spec_mulOv` excludes the overflow of `m * 10^d`),
`deprecate_complete`, `transferOwnership_complete`, `destroyBlackFunds_complete` (not
deprecated). Each conclusion states that the caller is the owner and the `require`s passed.
Hypotheses of each: Berlin ≤ fork (Glamsterdam included), size < 2^256, the selector, the
coldness flags as named in the specs, and `hdep` (not deprecated) for approve, transferFrom and
destroyBlackFunds. A static frame or a contract with no account needs no hypothesis: each writing
path reaches an SSTORE that is then `Gas.Stuck` (Evm/Stuck.lean, the `bad_*` lemmas), so no such run
ends with no error (`Gas.no_ok_stuck`), and each of these conclusions (for transferOwnership, its
`a ≠ 0` case) states `message.isStatic = false` and an account of the contract.

Getters (round 13): `decimals_complete`, `maximumFee_complete`, `totalSupplyVar_complete`,
`basisPointsRate_complete`, `deprecated_complete`, `paused_complete`, `upgradedAddress_complete`,
`owner_complete`, `getOwner_complete`, `maxUint_complete`, `balances_complete`,
`isBlackListed_complete`, `getBlackListStatus_complete`, `allowed_complete`,
`allowance_complete` (not deprecated): exact output, gas, state (reads only), substate.
`name_complete`, `symbol_complete`: under the named hypothesis `Complete.StrForm w` on the slot
word (empty, short 1..31 bytes, or long with 32 ≤ w / 2 < 2^180), the empty, short or long path.

Deprecated (rounds 14, 15), for any gas, any gas bound and ANY message runner:
`totalSupply_dep_complete`, `balanceOf_dep_complete`, `transfer_dep_complete`,
`approve_dep_complete`, `transferFrom_dep_complete`, `allowance_dep_complete`. Every run that ends with no error passed the
checks before the forward (transfer, transferFrom: not paused and the blacklist; approve: 68
bytes), the upgraded address has code of nonzero size, the runner was called with the forwarded
message and returned a frame with no error, and the end is exact: output (the word at 0x60 for
the three getters, empty for the three writes), gas, and the state and substate of
`incorporateChild`; and the upgraded account's code `c` is found in the state, and the CALL
follows a route `r`: no delegation, or (from Pectra) `c` is an EIP-7702 indicator to an address
whose code is found, the message runs that code with the precompiles disabled, and the CALL pays
the access to the delegate (`routeCost`). From Berlin on, Glamsterdam included (round 19:
EXTCODESIZE at `extCost fork`, the accesses at `accCost fork`, Evm/Local/Extcodesize.lean and
Evm/Route.lean). Named hypotheses
beyond the fork range, size, selector and flag: the coldness flags only.
`destroyBlackFunds_dep_complete`: the owner's call, `a` blacklisted, the forward of
`balanceOf(a)` answered with no error, then over the state `S` the call left and the word `d` at
0x60: STOP with empty output in `tailState S C a d` (`balances[a] := 0`, `_totalSupply := T' - d`
unchecked), `tailSub`, gas exact; the frame is not static and the contract has an account in
the child's end state (round 19: proved, the first SSTORE of the tail is `Stuck` otherwise;
through round 18 these were the named hypotheses `hstatic` and `hkeep`). Named hypotheses: the
coldness flags only.
-/

namespace UsdtVerify.Summary

open EthLib.Base (Fork U256 Address)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open Transfer SafeMath TransferOk TransferFee TransferFrom

alias dispatch_complete := Complete.runFrame_ok_dispatch
alias totalSupply_complete := Complete.ok_totalSupply
alias balanceOf_complete := Complete.ok_balanceOf
alias transfer_complete := Complete.ok_transfer
alias approve_complete := Complete.ok_approve
alias transferFrom_complete := Complete.ok_transferFrom
alias pause_complete := Complete.ok_pause
alias unpause_complete := Complete.ok_unpause
alias addBlackList_complete := Complete.ok_addBlackList
alias removeBlackList_complete := Complete.ok_removeBlackList
alias issue_complete := Complete.ok_issue
alias redeem_complete := Complete.ok_redeem
alias setParams_complete := Complete.ok_setParams
alias deprecate_complete := Complete.ok_deprecate
alias transferOwnership_complete := Complete.ok_transferOwnership
alias destroyBlackFunds_complete := Complete.ok_destroyBlackFunds
alias approve_short := Approve.spec_payload
alias setParams_mulOv := SetParamsSpec.spec_mulOv
alias decimals_complete := Complete.ok_decimals
alias maximumFee_complete := Complete.ok_maximumFee
alias totalSupplyVar_complete := Complete.ok_totalSupplyVar
alias basisPointsRate_complete := Complete.ok_basisPointsRate
alias deprecated_complete := Complete.ok_deprecated
alias paused_complete := Complete.ok_paused
alias upgradedAddress_complete := Complete.ok_upgradedAddress
alias owner_complete := Complete.ok_owner
alias getOwner_complete := Complete.ok_getOwner
alias maxUint_complete := Complete.ok_maxUint
alias balances_complete := Complete.ok_balances
alias isBlackListed_complete := Complete.ok_isBlackListed
alias getBlackListStatus_complete := Complete.ok_getBlackListStatus
alias allowed_complete := Complete.ok_allowed
alias allowance_complete := Complete.ok_allowance
alias name_complete := Complete.ok_name
alias symbol_complete := Complete.ok_symbol
alias totalSupply_dep_complete := Complete.dep_totalSupply_complete
alias balanceOf_dep_complete := Complete.dep_balanceOf_complete
alias transfer_dep_complete := Complete.dep_transfer_complete
alias approve_dep_complete := Complete.dep_approve_complete
alias transferFrom_dep_complete := Complete.dep_transferFrom_complete
alias allowance_dep_complete := Complete.dep_allowance_complete
alias destroyBlackFunds_dep_complete := Complete.dep_destroy_complete
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
alias nonpayable := Nonpayable.spec
alias runFrame_nonpayable := Nonpayable.runFrame_spec
alias pause := PauseSpec.spec_pause
alias unpause := PauseSpec.spec_unpause
alias pause_notOwner := PauseSpec.spec_pause_notOwner
alias unpause_notOwner := PauseSpec.spec_unpause_notOwner
alias pause_paused := PauseSpec.spec_pause_paused
alias unpause_notPaused := PauseSpec.spec_unpause_notPaused
alias addBlackList := BlackListSpec.spec_add
alias removeBlackList := BlackListSpec.spec_remove
alias addBlackList_notOwner := BlackListSpec.spec_add_notOwner
alias removeBlackList_notOwner := BlackListSpec.spec_remove_notOwner
alias issue := IssueSpec.spec_issue
alias redeem := IssueSpec.spec_redeem
alias issue_notOwner := IssueSpec.spec_issue_notOwner
alias redeem_notOwner := IssueSpec.spec_redeem_notOwner
alias issue_req1 := IssueSpec.spec_issue_req1
alias issue_req2 := IssueSpec.spec_issue_req2
alias redeem_req1 := IssueSpec.spec_redeem_req1
alias redeem_req2 := IssueSpec.spec_redeem_req2
alias issue_effects := IssueSpec.issue_effects
alias redeem_effects := IssueSpec.redeem_effects
alias setParams := SetParamsSpec.spec_setParams
alias setParams_notOwner := SetParamsSpec.spec_notOwner
alias setParams_bpHigh := SetParamsSpec.spec_bpHigh
alias setParams_feeHigh := SetParamsSpec.spec_feeHigh
alias setParams_effects := SetParamsSpec.params_effects
alias deprecate := AddrWriteSpec.spec_deprecate
alias deprecate_notOwner := AddrWriteSpec.spec_deprecate_notOwner
alias deprecate_effects := AddrWriteSpec.deprecate_effects
alias transferOwnership := AddrWriteSpec.spec_transferOwnership
alias transferOwnership_zero := AddrWriteSpec.spec_transferOwnership_zero
alias transferOwnership_notOwner := AddrWriteSpec.spec_transferOwnership_notOwner
alias transferOwnership_effects := AddrWriteSpec.transferOwnership_effects
alias destroyBlackFunds_notOwner := Destroy.spec_notOwner
alias destroyBlackFunds_notListed := Destroy.spec_notListed
alias destroyBlackFunds := DestroySpec.spec
alias runFrame_destroyBlackFunds := DestroySpec.runFrame_spec
alias destroyBlackFunds_effects := DestroySpec.destroy_effects
alias getter_slot := Getters.spec_slot
alias decimals := Getters.spec_decimals
alias maximumFee := Getters.spec_maximumFee
alias totalSupplyVar := Getters.spec_totalSupplyVar
alias basisPointsRate := Getters.spec_basisPointsRate
alias maxUint := Getters.spec_maxUint
alias deprecatedFlag := Getters.spec_deprecated
alias pausedFlag := Getters.spec_paused
alias upgradedAddress := Getters.spec_upgradedAddress
alias owner := Getters.spec_owner
alias getOwner := Getters.spec_getOwner
alias balances := GettersMap.spec_balances
alias isBlackListed := GettersMap.spec_isBlackListed
alias getBlackListStatus := GettersMap.spec_getBlackListStatus
alias allowed := GettersMap.spec_allowed
alias allowance := GettersMap.spec_allowance
alias name := Strings.spec_name
alias symbol := Strings.spec_symbol
alias name_tether := Strings.spec_name_tether
alias symbol_usdt := Strings.spec_symbol_usdt
alias runFrame_name := Strings.runFrame_name
alias runFrame_symbol := Strings.runFrame_symbol
alias allowance_dep := DeprecatedAllowance.spec_depAl
alias allowance_dep_answers := DeprecatedAllowance.spec_depAl_answers
alias allowance_dep_fails := DeprecatedAllowance.spec_depAl_fails
alias runFrame_allowance_dep_process := DeprecatedAllowance.runFrame_depAl_process
alias allowance_depNoCode := DeprecatedAllowance.spec_depAlNoCode
alias runFrame_allowance_depNoCode := DeprecatedAllowance.runFrame_depAlNoCode
alias fallback_unknown := Fallback.spec_unknown
alias fallback_short := Fallback.spec_short
alias runFrame_fallback_unknown := Fallback.runFrame_unknown
alias runFrame_fallback_short := Fallback.runFrame_short
alias destroyBlackFunds_dep := DeprecatedDestroy.spec_depD
alias destroyBlackFunds_dep_answers := DeprecatedDestroy.spec_depD_answers
alias destroyBlackFunds_dep_fails := DeprecatedDestroy.spec_depD_fails
alias runFrame_destroyBlackFunds_dep_process := DeprecatedDestroy.runFrame_depD_process
alias destroyBlackFunds_depNoCode := DeprecatedDestroy.spec_depDNoCode
alias runFrame_destroyBlackFunds_depNoCode := DeprecatedDestroy.runFrame_depDNoCode
alias name_empty := StringsGen.spec_nameEmpty
alias symbol_empty := StringsGen.spec_symbolEmpty
alias name_long := StringsGen.spec_nameLong
alias symbol_long := StringsGen.spec_symbolLong
alias runFrame_name_empty := StringsGen.runFrame_nameEmpty
alias runFrame_symbol_empty := StringsGen.runFrame_symbolEmpty
alias runFrame_name_long := StringsGen.runFrame_nameLong
alias runFrame_symbol_long := StringsGen.runFrame_symbolLong

variable {fork : Fork} {message : Message fork}

/-- The end of `transfer_ok` in plain terms, for any state `S` in which the contract has an
account: the frame stopped without error; `balances[to]` is its word after the sender's write
plus `v`; when the two slots differ, `balances[caller]` is its word in `S` minus `v` and the
recipient's word read was its word in `S`; one log was appended, `Transfer(caller, to, v)`. -/
theorem transfer_ok_effects {S : State.TransactionState} (hacc : hasAccount S message.currentTarget)
    {ss : Substate} {g : Nat} {v a : U256} {evm : Evm fork Nat}
    (h : Halted false .empty g (credited S message v a) (loggedSub fork ss S message v a) evm) :
    evm.running = false ∧ evm.error = none ∧
    storageAt evm.state message.currentTarget (recipientSlot a) =
      add (balT S message v a) v ∧
    (recipientSlot a ≠ senderSlot message →
      storageAt evm.state message.currentTarget (senderSlot message) = sub (balS S message) v ∧
      balT S message v a = storageAt S message.currentTarget (recipientSlot a)) ∧
    evm.substate.logs = ss.logs.push (transferLog message.currentTarget
      (bitwiseAnd ADDR_MASK message.caller.toU256) (bitwiseAnd ADDR_MASK a) v) := by
  obtain ⟨hr, he, -, -, hs, hss⟩ := h
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
    (h : Halted false .empty g (creditedF S message v t f) (loggedSubF fork ss S message v t f) evm) :
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
  obtain ⟨hr, he, -, -, hs, hss⟩ := h
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
    (h : Halted false .empty g (feeState S message v a) (feeSub fork ss S message v a) evm) :
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
  obtain ⟨hr, he, -, -, hs, hss⟩ := h
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
    (h : Halted false .empty g (feeStateF S message v t f) (feeSubF fork ss S message v t f) evm) :
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
  obtain ⟨hr, he, -, -, hs, hss⟩ := h
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
    (h : Halted false .empty g (credited S message v a) (loggedSub fork ss S message v a) evm)
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
    (h : Halted false .empty g (feeState S message v a) (feeSub fork ss S message v a) evm)
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
    (h : Halted false .empty g (creditedF S message v t f) (loggedSubF fork ss S message v t f) evm)
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
    (h : Halted false .empty g (feeStateF S message v t f) (feeSubF fork ss S message v t f) evm)
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
  obtain ⟨-, -, -, -, hst, -⟩ := h
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
