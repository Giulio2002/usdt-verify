# Status of the USDT verification

Pinned EthLib: d4d422780 (merge of #1266: memory reads after disjoint/adjacent writes; also on it
#1258, the frame-read rules CALLVALUE/CALLDATASIZE/...).
Re-pinned in round 6: EthLib's `callvalue`, `calldatasize`, `jumpi_of_eq_zero`,
`memoryReadBytes_memoryWrite_of_disjoint` (no read bound) and `memoryReadBytes_memoryWrite_memoryWrite`
replace the local `Local.read/callvalue/calldatasize/jumpi_zero'` and `Generic/Memory.lean` (deleted).
Previous pin: c1fe45a71 (#1250, kept).
Previous pin: 997edf8e4 (merge of #1238: NatCode, reshape, evm_step, kept).
The local NatCode copy and `reshape`/`Spec.reshape` were removed in favour of EthLib's.
Earlier pin: 5f5ae55b5 (#1223, kept).
Previously 189b419dd; re-pinned and rebuilt green (exit 0) with EthLib's stack rules replacing the local copies.
Bytecode: data/usdt.runtime.hex, 11075 bytes, keccak256 b44fb4e9...ea55, block 26362952 (see data/SOURCE.md).
No `sorry`, `admit`, axiom, `native_decide`, `bv_decide` or `decide +native` anywhere.
`decide +kernel` (kernel-checked) is used for jump-destination walks and one `exp` value.
`#print axioms` on every main theorem: [propext, Classical.choice, Quot.sound] (UsdtVerify/Test/Axioms.lean, printed at build).

## Proved

All specs: fork with `Fork.berlin ≤ fork`, the one-counter (`Nat`) gas meter of EthLib's logic,
start frame `At CODE message 0 [] .empty gas state substate` (fresh call frame), and the real
interpreter loop `runFrame` for every gas bound and every message runner (`Spec.runFrame`).

### `UsdtVerify.TotalSupply.spec` / `runFrame_spec` (UsdtVerify/Functions/TotalSupply.lean)
If the call data has `4 ≤ size < 2^256`, its first four bytes (big-endian) are 0x18160ddd,
the call value is 0, and byte 20 of storage slot 10 (the `deprecated` flag; bits 160..167) is 0,
then the run halts normally (no revert) with output = the 32 big-endian bytes of storage slot 1,
gas left = gas - (411 + price(slot 10) + price(slot 1)) (2100 cold / 100 warm, EIP-2929),
state = state with slots 10 and 1 recorded as read, substate = slots 10 and 1 marked accessed.

### `UsdtVerify.BalanceOf.spec` / `runFrame_spec` (UsdtVerify/Functions/BalanceOf.lean)
Same hypotheses with selector 0x70a08231. Then the run halts normally with output = the 32 bytes
of the slot `keccak256(wordBytes k ++ wordBytes 2)`, where `k` = (call data word at offset 4)
AND (2^160 - 1); gas left = gas - (831 + price(slot 10) + price(balance slot)), where the balance
slot's coldness is taken after slot 10 was accessed (stated so to avoid assuming hash != 10);
reads and accesses recorded as above.

The base slot 2 of `balances`, slot 1 of `_totalSupply`, slot 10 / byte 20 of `deprecated`
were read off the bytecode (PUSH1 02 / PUSH1 01 / PUSH1 0a PUSH1 14 ... EXP DIV), see docs/MAP.md.

### `UsdtVerify.Transfer.spec_paused` / `runFrame_paused` (UsdtVerify/Functions/Transfer.lean)
Selector 0xa9059cbb, `4 ≤ size < 2^256`, value 0, byte 20 of slot 0 (`paused`) ≠ 0 ⇒ the run
halts with the revert error (`Halted true`), empty output, gas left = gas - (762 + price(slot 0)),
slot 0 recorded read/accessed. (Frame-level result: the rollback of state happens in the
message layer, outside `runFrame`.)

### `UsdtVerify.Transfer.spec_blacklisted` / `runFrame_blacklisted`
Same, with byte 20 of slot 0 = 0 (not paused) and the low byte of slot
`keccak256(wordBytes c ++ wordBytes 6)` ≠ 0, where `c` is the caller address as a word
(`isBlackListed[msg.sender]`, base slot 6, read off PUSH1 06) ⇒ revert, empty output,
gas left = gas - (913 + price(slot 0) + price(blacklist slot)) (blacklist slot coldness taken
after slot 0 was accessed).

### `UsdtVerify.Transfer.spec_short` / `runFrame_short`
Selector 0xa9059cbb, `4 ≤ size < 68`, value 0, not paused (byte 20 of slot 0 = 0), caller not
blacklisted (low byte of `isBlackListed[caller]` = 0), not deprecated (byte 20 of slot 10 = 0) ⇒
BasicToken's payload check (`onlyPayloadSize(2 * 32)`: CALLDATASIZE < 0x44) reverts with empty
output; gas left = gas - (1094 + price(slot 0) + price(blacklist slot) + price(slot 10)), each
slot's coldness taken in the substate where the code reads it.

Reusable transfer blocks (all proved): `entry` (1866→5364), `notPaused` (5364→5392),
`blackLookup` (5392→5476 JUMPI) + `blackTest_ne`, `depInline` (5481→5775), `toBasic`
(5775→9883 with stack [amount, to, 0x1699, amount, to, 0x078a, sel]), `shortRevert` (9883).
The success path continues from 9883 with `68 ≤ size`.

Note (from the bytecode): `transfer` does NOT check the recipient's blacklist status, only the
sender's; the paused check comes first, then the sender blacklist, then deprecation.

### `UsdtVerify.TransferOk.spec_ok` / `runFrame_ok` (UsdtVerify/Functions/TransferSuccess.lean)
The success path of `transfer(to, v)` with a fee of 0. Fork range Berlin ≤ fork < Glamsterdam
(EthLib's SSTORE rule). Write C = the contract, v = argument word 1, a = argument word 0 masked
to 160 bits, S = the state after the reads of the checks (slots 0, blacklist, 10).
Hypotheses: frame not static; C has an account; 68 ≤ calldata size < 2^256; selector
0xa9059cbb; value 0; not paused; caller not blacklisted; not deprecated; `v * basisPointsRate`
(slot 3) < 2^256 (SafeMath `mul` assert); `feeOf = 0`, where the fee is exactly the bytecode's:
`raw = mul(v, rate) / 10000`, `fee = raw > maximumFee (slot 4) ? maximumFee : raw`; v ≤
`balances[caller]` (slot keccak(caller ++ 2)); `balT + v < 2^256` where balT is the recipient's
balance READ IN THE STATE AFTER THE SENDER'S WRITE (so a self-transfer is covered as the bytecode
does it); gas ≥ okCost, and more than 2300 gas left at each of the two SSTOREs (EIP-2200 stipend,
stated as two explicit bounds).
Conclusion: the frame stops normally (STOP) with
- state `credited S`: `balances[caller] := balS - v` (writeSlot), then the recipient slot read and
  `:= balT + v` (writeSlot), in this order;
- substate: slots 3, 4, sender, recipient accessed (plus 0, blacklist, 10), the two SSTORE
  refunds (`sstoreRefund` of original/current/new), and one log appended: address C, topics
  [0xddf252ad…b3ef, caller masked, a], data = the 32 bytes of v (`Transfer(caller, to, v)`);
- gas left exactly `gas - okCost`, okCost = 3863 + seven slot prices (EIP-2929 cold/warm, each in
  the substate where the code reads it) + `mulCost v` (72 if v = 0, 138 otherwise) + `capCost`
  (108 if the cap applies, the second, warm read of slot 4) + the two `sstoreCost`s (both warm).
- Returned bytes: transfer returns NO word (USDT's known non-standard ABI); STOP leaves the output
  buffer as it was. `At` does not track the output, so `Stopped` does not state it (generic gap).
Fee > 0: `TransferFee.spec_fee`; insufficient balance: `spec_low` (both below). Overflows and fee > v:
the INVALID specs below. Not covered: deprecated (CALL).

### `UsdtVerify.Approve.spec_zero` and `spec_set` (UsdtVerify/Functions/ApproveSpec.lean)
`approve(s, v)`, selector 0x095ea7b3, Berlin ≤ fork < Glamsterdam, not static, account exists,
68 ≤ size < 2^256, value 0, not deprecated (TetherToken checks slot 10 then calls StandardToken).
The allowance slot is `keccak(s ++ keccak(caller ++ 5))` (nested mapping, base slot 5).
- `spec_zero` (v = 0): the allowance is not read; it is written 0; log Approval(caller, s, 0)
  (topic 0x8c5be1e5…b925, data 32 bytes of 0); STOP; gas `2560 + price(slot 10) + sstoreCost`.
- `spec_set` (v ≠ 0 and allowance = 0, the `require`): allowance read then written v; log
  Approval(caller, s, v); STOP; gas `2753 + price(slot 10) + price(allowance) + sstoreCost(orig, 0, v, warm)`.
Each with an explicit stipend bound at the SSTORE. The revert with v ≠ 0 and a nonzero allowance: `spec_revert` below. Not covered: deprecated (CALL).

### `UsdtVerify.Approve.spec_revert` / `runFrame_revert` (UsdtVerify/Functions/ApproveRevert.lean)
`approve(s, v)` with 68 ≤ size < 2^256, selector 0x095ea7b3, value 0, not deprecated, v ≠ 0 and
`allowed[caller][s]` ≠ 0 ⇒ REVERT at 8380 (the `require`), empty output, gas left
`gas - (703 + price(slot 10) + price(allowance))`, slots 10 and the allowance recorded read/accessed.

### `UsdtVerify.TransferFrom.spec_ok` / `runFrame_ok` (UsdtVerify/Functions/TransferFrom*.lean)
`transferFrom(f, t, v)`, selector 0x23b872dd, fee 0. f, t = argument words 0, 1 masked; v = word 2;
S = state after the reads of the checks (slot 0, `isBlackListed[f]`, slot 10). Read off the bytecode:
TetherToken checks paused, then the blacklist of `_from` ONLY (not the caller, not `_to`), then
deprecation; StandardToken checks CALLDATASIZE ≥ 0x64 (three words); the allowance is
`allowed[_from][msg.sender]` = slot `keccak(caller ++ keccak(f ++ 5))`; the bytecode skips the
allowance write when it equals MAX_UINT = 2^256-1 (`if (_allowance < MAX_UINT)`).
Hypotheses: Berlin ≤ fork < Glamsterdam, not static, account exists, 100 ≤ size < 2^256, value 0,
not paused, f not blacklisted, not deprecated, `v*rate` no overflow, `feeOf S v = 0`,
`A = MAX_UINT ∨ v ≤ A` (A = the allowance in S), `v ≤ balances[f]` read after the allowance step,
`balances[t] + v < 2^256` read after the write of f, coldness flags for the 8 reads (each in the
substate where the code reads it), `stipCostF ≤ gas` (more than 2300 left at the SSTORE of
`balances[t]`; the two earlier SSTOREs' stipends follow from the total), `okCostF ≤ gas`.
Conclusion: STOP; state `creditedF S`: `allowState` (A ≠ MAX: allowance := A - v; A = MAX:
untouched), then `balances[f] := balF - v`, then `balances[t] := balT + v`; substate with the
accesses, the refunds, and the log Transfer(f, t, v) (topics [0xddf252ad…, f, t], data 32 bytes of
v); gas left exactly `gas - okCostF`, okCostF = 795 + 2971 + eight slot prices + mulCost v +
capCost + allowCost (26 at MAX; else 320 + the warm SSTORE price) + the two balance SSTORE prices.

### `UsdtVerify.TransferFee.spec_fee` / `runFrame_fee` (UsdtVerify/Functions/TransferFee*.lean)
`transfer(a, v)` with fee = `feeOf S v` ≠ 0. Extra hypotheses vs `spec_ok`: fee ≤ v (SafeMath sub of
sendAmount), `balT + (v - fee) < 2^256`, `balO + fee < 2^256` (balO = `balances[owner]` read after
the recipient's write; owner = low 160 bits of slot 0, read there). No stipend hypothesis: the
logs after each SSTORE cost more than 2300, so `feeCost ≤ gas` implies them.
Conclusion: STOP; sender := balS - v; recipient := balT + (v - fee); owner := balO + fee; slot 0
recorded read three more times (owner read, owner write, owner log topic; the topic is slot 0 read
after the owner's write — no assumption that slot 0 differs from the balance slots); logs
Transfer(caller, owner', fee) then Transfer(caller, a, v - fee); memory grows to 128 bytes; gas
left `gas - feeCost`, feeCost = 1034 + 5373 + nine slot prices + mulCost + capCost + three SSTORE
prices (all warm).

### `UsdtVerify.TransferOk.spec_low` (UsdtVerify/Functions/TransferFault.lean)
`transfer(a, v)` passing the checks, `v*rate` no overflow, fee ≤ v, `balances[caller] < v`, and
`lowCost ≤ gas` ⇒ the frame halts exceptionally (EthLib `Faulted (.invalidOpcode 0xfe)`, #1250):
no output, gas 0, state = S with slots 3, 4 and the sender's balance recorded read, nothing
written. SafeMath fault blocks: `subFault` (sub, a < b), `addFault` (add, a + b ≥ 2^256).

### Transfer INVALID paths (UsdtVerify/Functions/TransferFaults.lean, TransferFault.lean)
All from pc 0, with the checks passing (call data ≥ 68 bytes, selector 0xa9059cbb, no value, not
paused, caller not blacklisted, not deprecated). End: `Faulted (.invalidOpcode 0xfe) st ss`: no
output, gas 0, the state/substate the frame had (the caller discards them). Each takes an exact
gas bound to reach the INVALID (with less, the frame runs out of gas instead).
- `TransferOk.spec_mulOv`: `v * rate ≥ 2^256` ⇒ INVALID at 10802 (new block `SafeMath.mulFault`,
  with `div_mul_ne`); state S + slot 3 read. Gas `preCost + 204 + price(slot 3)`.
- `TransferOk.spec_feeGt`: no overflow, `v < fee` ⇒ INVALID at `sub(v, fee)`; S + slots 3, 4 read.
- `TransferOk.spec_low` / `runFrame_low`: `fee ≤ v`, `balances[caller] < v` (unchanged statement;
  `runFrame_low` is new).
- `TransferOk.spec_toOv`: any `fee ≤ v`, `v ≤ balances[caller]`, `balT + (v - fee) ≥ 2^256`
  (balT read after the sender's write) ⇒ INVALID at the `add`, in the state after the sender's
  write and the recipient's read. Needs `hstip` (> 2300 gas left at the sender's SSTORE).
- `TransferOk.spec_ownerOv`: `0 < fee ≤ v`, the recipient's credit fits,
  `balO + fee ≥ 2^256` ⇒ INVALID at the owner's `add`, after the recipient's write and the reads
  of slot 0 and the owner's slot. `hstip` (> 2300 at the recipient's SSTORE) and `hg`.
- `TransferOk.pre`: the common prefix pc 0 → 9883 as one Hoare triple (reusable).

### transferFrom reverts and INVALID paths (TransferFromFault.lean, TransferFromFault2.lean)
Selector 0x23b872dd, no value. Reverts (`Halted true .empty`, exact gas):
- `spec_paused` (REVERT at 3797): gas `462 + price(slot 0)`.
- `spec_blacklisted` (not paused, `isBlackListed[f]` low byte ≠ 0; REVERT at 3886):
  `614 + price(0) + price(black)`.
- `spec_short` (not paused, f not blacklisted, not deprecated, size < 100; REVERT at 8644):
  `801 + three prices`, state `checkState`.
INVALID (call data ≥ 100, checks pass; `A = allowed[f][caller]` in S):
- `spec_mulOv`: `v * rate ≥ 2^256`; S + allowance and slot 3 read.
- `spec_allowLow`: `A < v` (then `A ≠ MAX_UINT` follows from `v < 2^256`); INVALID at the
  allowance's `sub`; S + allowance, slots 3, 4 read; nothing written.
- `spec_balLow`: `fee ≤ v` (any fee), `A = MAX_UINT ∨ v ≤ A`, `balances[f] < v` (read after the
  allowance step) ⇒ INVALID at the debit's `sub`, after the allowance write. `hstip` at the
  allowance SSTORE.
- `spec_feeGtF`: `A = MAX_UINT ∨ v ≤ A`, `v < fee` ⇒ INVALID at `sub(v, fee)`, after the
  allowance write (the bytecode does the allowance step before `sendAmount`).
- `spec_toOvF`: `fee ≤ v`, allowance and debit pass, `balTo + (v - fee) ≥ 2^256` ⇒ INVALID at
  the `add`, after the write of `balances[f]`.
- `spec_ownerOvF`: `0 < fee ≤ v`, the credit of `t` fits, `balO + fee ≥ 2^256` ⇒ INVALID at the
  owner's `add`, after the write of `balances[t]`.
- `preF0` (pc 0 → 8619) and `preF` (→ 8648): reusable prefixes.

### `UsdtVerify.TransferFrom.spec_feeF` / `runFrame_feeF` (TransferFromFee.lean, TransferFromFeeSpec.lean)
`transferFrom(f, t, v)` with fee ≠ 0. Hypotheses as `spec_ok` with `fee ≠ 0`, `fee ≤ v`,
`balTo + (v - fee) < 2^256`, `balOF + fee < 2^256` (owner = low 160 bits of slot 0, read after the
write of `t`); `feeCostF ≤ gas` (the four SSTORE stipends follow: a LOG of > 2300 gas comes after
each). Conclusion: STOP; state `feeStateF S`: allowance step, `balances[f] := balF - v`,
`balances[t] := balT + (v - fee)`, `balances[owner] := balO + fee`, slot 0 read; logs
`Transfer(f, owner', fee)` then `Transfer(f, t, v - fee)`; gas left `gas - feeCostF`,
feeCostF = 795 + 5516 + ten slot prices + mulCost + capCost + allowCost + three balance SSTORE
prices. New blocks at 9274 (`creditStoreFeeF`), 9351 (`ownerCallF`), 9465 (`ownerStoreF`), 9566
(`ownerLogF`), 9700 (`logBlock128F`); lookup tails at 9393 and 9504 (`hashTailF`; the handoff's
guess 9415/9526 was off: those are the second AND of each tail).

### Round 5: interpreter-loop wrappers
Every from-pc-0 fault and revert theorem now has its `runFrame_*` form (one line each,
`(spec ...).runFrame start within`): `TransferOk.runFrame_mulOv/_feeGt/_toOv/_ownerOv`,
`TransferFrom.runFrame_paused/_blacklisted/_short/_allowLow/_balLow/_mulOv/_feeGtF/_toOvF/_ownerOvF`,
and also `Approve.runFrame_zero/_set`.

### Round 5: local conservation of balances (UsdtVerify/Summary.lean)
`transfer_ok_conserves`, `transfer_fee_conserves`, `transferFrom_ok_conserves`,
`transferFrom_fee_conserves`. Each takes the end frame of a success path (`Local.Stopped ...`, as
the `*_effects` lemmas), with `S` the state after the checks, and states, with
`delta S S' C k = (S'[k] : Int) - S[k]`:
- transfer, fee 0: sender `-v`, recipient `+v`, sum 0. Hypotheses: the two slots differ,
  `v ≤ S[sender]`, `S[recipient] + v < 2^256`.
- transfer, fee > 0: sender `-v`, recipient `+(v - fee)`, owner `+fee`, sum 0, the owner slot being
  `keccak(low160(S[0]) ++ 2)`. Hypotheses: the three slots pairwise distinct, sender and recipient
  slots ≠ slot 0, `fee ≤ v`, `v ≤ S[sender]`, `S[recipient] + (v - fee) < 2^256`,
  `S[owner] + fee < 2^256`.
- transferFrom, fee 0: `f` `-v`, `t` `+v`, sum 0. Hypotheses: slots of `f`, `t` distinct, the
  allowance slot distinct from both, no underflow / overflow (in `S`).
- transferFrom, fee > 0: `f` `-v`, `t` `+(v - fee)`, owner `+fee`, sum 0. Hypotheses: `f`, `t`,
  owner slots pairwise distinct, the allowance slot distinct from all three, `f`, `t` and allowance
  slots ≠ slot 0, `fee ≤ v`, no underflow / overflow (in `S`).
Distinctness of keccak-derived slots is always a hypothesis. Only the touched slots are stated:
the global "sum of all balances = `_totalSupply`" needs a sum over a mapping and is NOT proved.
(The `*_ok`/`*_fee` overflow hypotheses of the specs are stated on reads after earlier writes;
with the distinctness hypotheses they are the same words as in `S`.)

### Round 5: deprecated paths (CALL to `upgradedAddress`), UsdtVerify/Functions/Deprecated*.lean
Through EthLib's callee abstraction (`callWith`, `HoareUnder`/`SpecUnder`, `Meets`, `RunsAs`,
`meets_of_spec`); no USDT-specific support in EthLib.
- `Deprecated.spec_dep` (totalSupply) / `DeprecatedBalance.spec_depB` (balanceOf): for EVERY callee
  assumption `callee`, a `SpecUnder`: the run ends (or a runner abort) in a stopped frame with a
  caller frame, a message `msg` and an ended frame `child`, `callee caller msg child`, where `msg`
  goes from the contract to `ua` = low 160 bits of slot 10 (as an address), with `ua`'s code, no
  value, depth + 1, the frame's static flag, data = the 4 bytes 0x18160ddd (totalSupply) or
  `0x70a08231 ++ wordBytes who` (balanceOf, `who` = argument word 0 masked), and gas
  `(messageCallGas fork 0 (gasleft - 710) …).subCall` (EIP-150, EIP-2929); the caller state and
  substate exact (slot 10 read and accessed, `ua` read and accessed); then:
  `child.error = none` ⇒ RETURN of the 32 bytes of the word at 0x60 after CALL wrote the first
  `min 32 |output|` bytes of the child's output there (Solidity 0.4.17 does not check
  RETURNDATASIZE: with a shorter output the rest of the word is the old memory, the selector
  bytes); `child.error ≠ none` ⇒ REVERT with no output (the callee's revert data is NOT forwarded).
  Gas left, state, substate (`incorporateChild`) exact.
  Hypotheses: Berlin ≤ fork < Glamsterdam; selector; no value; deprecated byte ≠ 0; `ua` holds a code
  `c` with `0 < |c| < 2^256`, no delegation from Pectra; depth + 1 ≤ 1024; the gas to the CALL plus
  100 (`hg`); at least 121 (126 for balanceOf) gas left after the CALL's price (`htail`).
- `spec_dep_answers` / `spec_depB_answers`: if every forwarded message (`Forwarded` / `Sends`) ends
  with no error and output `o`, `|o| ≥ 32`: the run returns `wordBytes (loadWord o 0 32)` (the first
  32 bytes of `o`), no error. `spec_dep_fails` / `spec_depB_fails`: if every forwarded message ends
  with an error, the run reverts with empty output.
- `runFrame_dep_answers`: the interpreter loop under any runner meeting the assumption.
- `runFrame_dep_process` / `runFrame_depB_process`: the interpreter's OWN runner `processRunner`:
  for any code `c` at `ua` with a `Spec` (as `meets_of_spec` takes it) whose stopped frames end
  with no error and output `o` (`|o| ≥ 32`), `ua` no precompile: the run of USDT returns the first
  word of `o`, or the runner aborts (`answers_runsAs`, `answersD_runsAs` link `RunsAs` to the
  answer assumption).
- `spec_depNoCode` / `spec_depBNoCode`: `ua` has empty code ⇒ REVERT, empty output, before any call
  (gas `599`/`921 + price(slot 10) + price(ua)`).
Shared blocks (generic over both getters): `depSet` (3565/4665, flag set), `toCall`
(3719/4874: EXTCODESIZE, GAS, SUB), `noCode`, `failTail` (3737/4892), `retBig` (797/1511 on a
160-byte memory), `okTail`, `okTailB`, `fwdArgs`, `fwdArgsB`.
A callee that returns fewer than 32 bytes is covered only by `spec_dep`
(the general form), not by an `_answers` corollary.

### Summary (UsdtVerify/Summary.lean)
One place: a doc listing every proved path per function (precondition, effect on balances,
allowances, logs), `alias`es of all the from-pc-0 theorems under `UsdtVerify.Summary`, and four
plain-terms lemmas on the end states of the success paths, for any state where the contract has an
account: `transfer_ok_effects` (recipient slot = balT + v; if the slots differ, sender slot =
balS - v and balT = the recipient's word in S; logs = old logs + Transfer(caller, to, v)),
`transferFrom_ok_effects` (to slot = balTo + v; if slots differ, from slot = balFrom - v; if the
allowance slot differs from both, it is A when A = MAX_UINT else A - v; logs + Transfer(f, t, v)),
`transfer_fee_effects` and `transferFrom_fee_effects` (owner slot = balO + fee; the recipient slot
= balT + (v - fee) when it differs from the owner slot; the sender's for transfer when distinct;
logs + the two Transfer logs). Slot distinctness is a hypothesis (the slots are keccak outputs;
no hash assumption is made).

### Supporting results
- `UsdtVerify.table`: the 32-entry selector table at pc 54 (keys, destinations, all destinations
  valid JUMPDESTs) — `Table CODE 4 2 54 ENTRIES`.
- `UsdtVerify.dispatch`: prelude + table, from pc 0 to the destination of the selector.
- `UsdtVerify.selector_word`: the dispatcher's DIV/AND word equals the 4-byte selector.
- Shared blocks (UsdtVerify/Functions/Common.lean): `ret` (return-one-word block, proved at 797
  and 1511), `depCheck` (deprecation check, proved at 3565 and 4665).

### Round 6: deprecated transfer, approve, transferFrom (DeprecatedTransfer.lean, DeprecatedTransferFrom.lean)
Same design as round 5 (callWith, SpecUnder, Meets, RunsAs, meets_of_spec), CALL with an output
range of size 0. Hypotheses bundled in structures `HypT`, `HypA`, `HypF` (fields: Berlin ≤ fork <
Glamsterdam, size bounds, selector, value 0, deprecated byte ≠ 0, code `c` at `ua` with
0 < |c| < 2^256, no delegation from Pectra, depth + 1 ≤ 1024, coldness flags; transfer: not paused,
`isBlackListed[caller]` low byte 0; transferFrom: not paused, `isBlackListed[f]` low byte 0;
approve: 68 ≤ size, no paused/blacklist read). Size: transfer and transferFrom only `4 ≤ size`.
- `spec_depT` / `spec_depA` / `spec_depF` (any callee): `Sends message ua c d msg` with
  d = `dataT` = SEL 0x6e18980a ++ callerKey ++ addrArg 0 ++ wordArg 1 (100 bytes),
  `dataA` = 0xaee92d33 ++ callerKey ++ addrArg 0 ++ wordArg 1 (100 bytes),
  `dataF` = 0x8b477adb ++ callerKey ++ addrArg 0 ++ addrArg 1 ++ wordArg 2 (132 bytes);
  msg.gas = (callGas…).subCall; caller state/substate exact; child.error = none ⇒
  `Local.Stopped (gas - preCost - callCost + child.gas - 51/53/53)` with the
  `incorporateChild` state and substate; child.error ≠ none ⇒ `Halted true .empty (… - 25)`.
  preCost: transfer 1357 + 3 slot prices + account price; approve 724 + slot 10 + account;
  transferFrom 1093 + 3 slot prices + account. `hg`: preCost + 100 ≤ gas; `htail`: 51/53/53 left
  after the CALL's price.
- `_succeeds` (callee assumption `SucceedsD`: every such message ends with no error) ⇒ STOP, no
  error, `∃ caller msg child` with `Sends`, `child.error = none`, `Local.Stopped …`.
  `_fails` (`FailsD`) ⇒ `evm.error = some .revert ∧ evm.output = .empty`.
- `runFrame_dep{T,A,F}_process`: `processRunner`, any code at `ua` with a `Spec` (as
  `meets_of_spec`) whose stopped frames have no error; `ua` no precompile (`succeedsD_runsAs`).
- `spec_dep{T,A,F}NoCode`: empty code ⇒ REVERT at the EXTCODESIZE check; gas 1354 / 721 / 1090 +
  prices.
Shared blocks: `depSetW` (5481/2955/3890), `upLoad` (5503/2977/3912), `encode3` (5568/3042),
`encode4` (3978), `okTailT` (5757), `okTailA` (3231), `okTailF` (4218); `toCall`, `noCode`,
`failTail` now take five pcs each (and no memory-size hypothesis). Memory facts: `W1`..`W5`,
`data_W4`, `data_W5`, `read40_W4/5`, generic `read_ext` (a read below the old size is kept by
growth) and `read_prefix` (the first k bytes of a written range).

### Round 7: the nonpayable revert (UsdtVerify/Functions/Nonpayable.lean)
Each of the 32 table entries begins with its own copy of `JUMPDEST CALLVALUE ISZERO PUSH2 (e+11)
JUMPI PUSH1 0 DUP1 REVERT` (checked byte by byte in the proof of `valueRevert`, one case per
entry; `DESTS` = the 32 destinations).
- `valueRevert`: at any `e ∈ DESTS`, stack `[x]`, memory `MEM0`, value ≠ 0 ⇒ `Halted true .empty
  (gas - 25)`, state and substate unchanged.
- `table_entry` (`decide +kernel`): for each `i : Fin 32`, the table tests `i + 1` entries for key
  `i` and branches to destination `i`.
- `spec` / `runFrame_spec`: Berlin ≤ fork, `4 ≤ size < 2^256`, `selector = ENTRIES[i].1`, value ≠ 0
  ⇒ `Halted true .empty (gas - (87 + 22 * (i + 1)))` with the start state and substate.

### Round 7: onlyOwner, pause(), unpause() (Owner.lean, Pause.lean, PauseSpec.lean)
- `Owner.ownerTest/ownerOk/ownerRevert`: the inlined `require(msg.sender == owner)` at the ten
  `CHECKS` (from the `SWAP1` before `SLOAD`, stack `0 :: 0 :: rest`, any memory): reads slot 0
  (price `slotCost c0`), compares `callerWord = caller & (2^160-1)` with
  `ownerOf = slot0 & (2^160-1)`; equal ⇒ pc `s + 87`, gas `69 + slotCost c0`; not equal ⇒
  `Halted true .empty`, gas `75 + slotCost c0`. `prefix9`: `JUMPDEST PUSH1 0 DUP1` at the nine
  `BODIES` (destroyBlackFunds pushes a local first). Generic (no sorry): `writeSlot_readSlot`,
  `storeSub_accessSlot`.
- `PauseSpec.spec_pause_notOwner` (574 + slot 0), `spec_unpause_notOwner` (464 + slot 0): REVERT.
- `spec_pause_paused` (786 + slot 0), `spec_unpause_notPaused` (673 + slot 0): REVERT.
- `spec_pause` / `spec_unpause`: Berlin ≤ fork < Glamsterdam, not static, account exists, owner
  caller, flag clear / set, `hstip` (3297 / 3184 + slot 0 ≤ gas: more than 2300 at the SSTORE) ⇒
  `Local.Stopped (gas - (1784 / 1671 + slotCost c0 + flagCost))`, state
  `writeSlot S C 0 (withPaused w0 1 / 0)`, substate `storeSub … ` with the log
  `log0 C PAUSE_TOPIC / UNPAUSE_TOPIC` (one topic, empty data) appended.
- `withPaused w b = (b * 2^160) | (~(0xff * 2^160) & w)`; `bit_withPaused`, `byte20_withPaused`,
  `owner_withPaused` (bit-level proofs, `decide +kernel` over `i < 256` for one Bool identity).

### Round 7: addBlackList, removeBlackList (Admin.lean, BlackList.lean, BlackListSpec.lean)
- Shared (Admin.lean): `hashTail7` (the lookup tail at the 13 copies not in `HASH_PCS`),
  `entry1` (entry of the five one-address functions, 74 gas), `setLow w b = b | (~0xff & w)`
  with `lowByte_setLow` and `bit_setLow` (bits ≥ 8 kept).
- `listWrite` (3375 / 7379, the two bodies are the same code 4004 bytes apart): `isBlackListed[a]`
  read and written to `setLow w 1 / 0`; `listLog`: `AddedBlackList(a)` / `RemovedBlackList(a)`
  (LOG1, data = the masked word `a`, memory grows to 128 bytes), jump back, STOP.
- `spec_add_notOwner` (328 + slot 0), `spec_remove_notOwner` (856 + slot 0): REVERT.
- `spec_add` / `spec_remove`: `Local.Stopped (gas - (1567 / 2095 + slot 0 + slot L + write))`,
  state `writeSlot (readSlot S C 0) C L (setLow w v)`, substate with both accesses, the write's
  refund and the log; `hstip`: 2779 / 3307 + slot 0 + slot L ≤ gas.
- `listState_flag`, `listState_other`: the end state in plain terms.

### Round 7: issue, redeem (Issue.lean, IssueSpec.lean)
- Blocks: `ownerLookup` (the `balances[owner]` lookup at its five copies, slot 0 warm, 229 gas),
  `issueTest1/2`, `redeemTest1/2` (the `require` tests), `reqPass` / `reqRevert` (their JUMPIs,
  13 / 19 gas), `issueOwner` / `issueTotal` / `redeemTotal` / `redeemOwner` (the writes, macro
  `op_write`), `amountLog` (LOG1 of the amount, 1075 gas to STOP), `entryW` (word-argument
  entry, 68 gas). Generic (no sorry): `readSlot_comm`, `accessSlot_comm`, `readSlot_0n0`,
  `accessSlot_0n0`.
- Reverts: `spec_issue_notOwner` (740), `spec_redeem_notOwner` (762), `spec_issue_req1`
  (875 + slots 0, 1), `spec_issue_req2` (1462 + slots 0, 1, O), `spec_redeem_req1` (794 + …),
  `spec_redeem_req2` (1052 + …).
- `spec_issue`: `Local.Stopped (gas - (3024 + slots 0, 1, O + issueCostO + issueCostT))`, state
  `issueState` (reads 0, 1, 0, O; `O := B + a`; read 0; `1 := T' + a`), substate `issueSub`;
  `hstip`: 4248 + slots + issueCostO ≤ gas. `spec_redeem`: 2614 + …, `redeemState`
  (`1 := T - a`, then `O := B' - a`), `redeemSub`; `hstip` 3838 + slots + redeemCostT.
- `issue_effects`, `redeem_effects`: with `O ≠ 1`, slot values as numbers, other slots kept.

### Round 7: setParams (SetParams.lean, SetParamsSpec.lean)
- Blocks: `entry2` (two word arguments, 92 gas), `test1/test2` + `pass/fail` (the two
  `require`s), `write3` (slot 3, cold or warm), `mulCall` (slot 9, `exp 10 d` with its EIP-160
  price `50 * exponentBytes d`, SafeMath `mulBlock` at 10755, back to 5942), `write4` (slot 4),
  `paramsLogBlock` (slots 3 and 4 read back, two MSTOREs growing memory to 160 bytes, LOG1 of 64
  bytes, 1556 gas to STOP). Generic: `read_after64`.
- `spec_notOwner` (742 + slot 0), `spec_bpHigh` (771 + slot 0), `spec_feeHigh` (800 + slot 0).
- `spec_setParams`: `Local.Stopped (gas - (2425 + paramsCost))`, `paramsState`, `paramsSub` (log
  `Params(b, f)` with data `wordBytes b ++ wordBytes f`); `hstip` 3168 + … ≤ gas;
  `params_effects`.

### Round 7: deprecate, transferOwnership (AddrWrite.lean, AddrWriteSpec.lean)
- Blocks: `depFlag` (2737: slot 10 := `withPaused w10 1`, 118 + slot 10 + write), `depPrefix`,
  `addrTail` (2770 / 7755: the warm slot `k` gets its low 160 bits from `a`, 158 + write),
  `ownTest` / `ownSkip` / `ownGo` / `ownEnd`; `listLog` (BlackList.lean) now also covers the
  `Deprecate(a)` log at 2830. `withAddr`, `bit_withAddr`, `addr_withAddr`, `byte20_withAddr`.
- `spec_deprecate_notOwner` (262), `spec_transferOwnership_notOwner` (900),
  `spec_transferOwnership_zero` (947 + slot 0: STOP, no write).
- `spec_deprecate`: `Local.Stopped (gas - (1628 + slots 0, 10 + depCost))`, `depState`, `depSub`;
  `hstip` 2840 + … . `spec_transferOwnership`: `gas - (1114 + slot 0 + ownCost)`, state
  `writeSlot S C 0 (withAddr w0 a)`, substate `storeSub …` (no log); `hstip` 3401 + slot 0.
- `deprecate_effects`, `transferOwnership_effects`.

### Round 7: destroyBlackFunds, the reverts (Destroy.lean)
- `toBody` (its body pushes the local first: `JUMPDEST PUSH1 0 DUP1 PUSH1 0`, check at 7824).
- `spec_notOwner` (925 + slot 0), `spec_notListed` (1074 + slot 0 + `isBlackListed[a]`;
  `lowTest_eq`).
- Not covered: the success path. It calls TetherToken's `balanceOf` getter at 4665 (with its own
  deprecation check) from a deeper stack; `BalanceOf.toLookup` / `lookup` are stated for the
  exact stack of balanceOf and need a `rest` generalization first.

## Open (not proved)
- destroyBlackFunds' success path, the getters other than totalSupply/balanceOf, the fallback, invariants across calls, the global
  "sum of balances = totalSupply" (needs a sum over a mapping).
- The returned bytes after STOP (generic gap 8).

## Generic gaps found (for the EthLib program-logic agent)
1. Missing opcode rules at the pin (kept as LOCAL lemmas, UsdtVerify/Local/Rules.lean):
   CALLVALUE, CALLDATASIZE (a generic "read a frame value" rule), instruction-table lemmas for
   LT/GT/DIV/AND/OR/SUB/MUL/NOT, JUMPI on a condition *proved* 0, and EXP with its EIP-160 price
   worked out (a corollary of EthLib's `exp`, whose price is `gasSchedule fork`).
   POP/DUPn/SWAPn/EXP now come from EthLib (#1223).
2. (UPSTREAMED in #1238, local copy removed) Long code: a `#[...]` literal does not scale. Solved locally, generically
   (UsdtVerify/Generic/NatCode.lean): store code as ONE big-endian Nat literal; byte i is
   `n >>> (8*(size-1-i))` (Meta and kernel shift big numerals with GMP; `/ 256^k` does NOT work,
   Meta refuses exponents > 256). `CODE` is irreducible; facts used: size, getElem, byteAt.
3. (UPSTREAMED in #1238) Jump validity on long code: solved locally, generically: a Bool walk along opcode boundaries
   (`walk`, `boundaryFrom_of_walk`, `valid_of_walk`) checked by `decide +kernel`, through
   EthLib's `isValidJumpDest_iff_boundaryFrom`.
4. Memory reads after writes: `memoryReadBytes_memoryWrite_of_disjoint`,
   `memoryReadBytes_two_writes` (UsdtVerify/Generic/Memory.lean).
5. Tactic pitfall: `first | ... | ...` does not catch maxRecDepth; a byte goal `CODE[pc] = b`
   also contains `CODE.size` in its bound proof, so `rw [size_CODE]; decide` on it unfolds `CODE`.
   Order alternatives so the byte lemma runs first.
6. (SOLVED upstream in #1250, used since pin c1fe45a71) INVALID / exceptional halts.
7. No rule for STOP (0x00) at the pin: LOCAL rule `Local.stop` (UsdtVerify/Local/Halt.lean),
   with postcondition `Stopped` (no error, gas, state, substate).
8. `At` does not name the output buffer, so a STOP-ended run cannot state its (empty) output.
9. Storage writes over slots (UsdtVerify/Spec/Write.lean, generic): `writeSlot` (the `.ok` branch
   of setStorage after the read is recorded, under `hasAccount`), `storeSub`, `sstoreW` (EthLib's
   `sstore` restated), read/access idempotence (`readSlot_readSlot`, `accessSlot_accessSlot`),
   `storageAt_writeSlot_self/_of_ne`, `originalAt_writeSlot`, `hasAccount_writeSlot/_readSlot`.
10. Tactic pitfall (Lean v4.35.0 `omega`): a goal `X + 2400 ≤ gas - (1034 + a0 + a1 + a2)` with
   ~6 atoms and a hypothesis of the same sum hits "maximum recursion depth"; the same fact without
   the subtraction is fine. Worked around with `Nat.le_sub_of_add_le` (no limit raised).
   Also: omega atoms are syntactic, so abbrevs (balS, senderSlot, readSlot-wrapped reads) must be
   unfolded/normalized (`storageAt_readSlot`, `originalAt_readSlot`) to one form first.

11. Local generic lemmas added (no sorry): `coldIn_accessSlot_false` (an accessed slot stays warm),
   `coldIn_accessSlot_of_warm` (accessing a warm slot changes no coldness), `coldIn_storeSub'`,
   `coldIn_storeSub_false`, `read64_append`, `slotCost_ge`.
12. Tactic pitfalls (new): (a) a `simp only [...] at h1 h2` location list cannot continue on the next
   line (parse error "unexpected identifier"); keep it on one line. (b) `simp only
   [storageAt_readSlot]` does not fire on `readSlot st C 0` when the 0 came from a PUSH; `rw` does.
   (c) `maxHeartbeats` is per declaration: a 60-step composition exceeded 200000; split it into
   two theorems (no limit raised). (d) a wrong memory term in a block argument (one `mapMem` too
   many) shows up as a whnf heartbeat timeout, not a type error.
   (e) The omega maxRecDepth trap of `X + 2400 ≤ gas - (1034 + a + b + c)` was not hit again
   (the `Nat.le_sub_of_add_le` style was kept), so no repro file was written.

13. Round 4: the local `memoryReadBytes_memoryWrite_self` was removed; EthLib's
   `memoryReadBytes_memoryWrite` (Machine/Memory.lean, present at the pin) is used instead.
   New local generic lemmas: `SafeMath.div_mul_ne` (overflow ⇒ `div (mul a b) a ≠ b`, used by
   `mulFault`), `TransferFrom.coldIn_allowSub_false`, `Summary.logs_allowSub`. No new gap in
   EthLib's rules was hit this round.

14. Round 5 (LOCAL, UsdtVerify/Local/Account.lean, no sorry): EthLib's program logic at the pin has
   no rule for EXTCODESIZE (0x3b) nor GAS (0x5a). Local generic rules: `Local.extcodesize` (Berlin ≤
   fork < Glamsterdam: pushes the code size, pays 2600 cold / 100 warm, `externalBaseCost_of_berlin`,
   inserts the address into the accessed addresses, records the account read) and `Local.gasOp`
   (pushes `gas - 2`), with `instruction_extcodesize` / `instruction_gas`.
   CALL itself needed nothing new: `callWith` covers the input range (call data from memory) and the
   output range (return data copied into memory), which is all Solidity 0.4.17 uses (no
   RETURNDATASIZE/RETURNDATACOPY). Local generic memory lemma: `memoryReadBytes_write_after` (a read
   across a write = the bytes before ++ the written bytes), in DeprecatedBalance.lean.
   Pitfall: in `refine (lemma (by tac) ...).seq ?_`, tactic arguments run before the goal fixes
   implicit arguments (gas, rest, state): give them explicitly (`(gas := ...)`).

15. Round 6 (re-pin to d4d422780): gaps 1 (CALLVALUE, CALLDATASIZE, JUMPI on a condition proved 0)
   and 4 (memory reads after writes) are CLOSED by EthLib (#1258, #1266); the local copies are
   removed. Still local at d4d422780 (checked by grep of Logic/): STOP (gap 7), EXTCODESIZE and GAS
   (gap 14), the instruction-table lemmas LT/GT/DIV/AND/OR/SUB/MUL/NOT and EXP with its price
   (gap 1 remainder). New local generic memory lemmas (no sorry, DeprecatedTransfer.lean):
   `read_ext` (growth keeps a read below the old size) and `read_prefix` (a read of the first k
   bytes of a written range); `memoryReadBytes_write_after` (round 5) is reused.
   Pitfall: `congr 1` on `asked X = asked Y` with `if` atoms hit maxRecDepth; `exact congrArg asked
   (by unfold accCost; omega)` works. A long chain of gas subtractions unified against an explicit
   `(gas := …)` of a block also hits maxRecDepth: insert `step reshape (g' := …)` first.

16. Round 7: no new opcode gap (LOG1, SSTORE, SLOAD, EXP, CALLER, MSTORE all from EthLib or the
   existing local rules). New local generic lemmas (no sorry): `writeSlot_readSlot` (under
   `hasAccount`), `storeSub_accessSlot`, `readSlot_comm`, `accessSlot_comm`, `readSlot_0n0`,
   `accessSlot_0n0`, `read_after64`, `byte20_of_bits`, `lowByte_of_bits`, `testBit_one'`.
   Pitfalls: (a) a coldness argument such as `coldIn_accessSlot_self _ _ _` given inline fixes the
   block's substate to `accessSlot …` and fails (or times out in whnf) against a `storeSub …`
   substate; give it as `?h` and close it with `case h => exact …` after the `refine`.
   (b) `simp`/`omega` side arguments of a block are elaborated before the block's implicit gas and
   stack are unified: pass `(gas := …)` or defer them the same way. (c) after SLOAD the word is
   `st.getStorage t (toBeBytes n)`; `rw [getStorage_eq]` turns it into `storageAt` so omega sees one
   atom. (d) `if_neg`/`if_false` are deprecated in this toolchain (`ite_false`, or `split`).

## Measurements (macOS arm64, LEAN_NUM_THREADS=2, safe.sh 9G)
Round 7 (pin d4d422780, unchanged): clean project build (`rm -rf .lake/build`) 98.19 s wall,
1345454080 bytes (1283 MiB) max RSS (/usr/bin/time -l), exit 0, 0 "error:" lines, 1337 jobs,
124 `#print axioms`, all [propext, Classical.choice, Quot.sound]. New files of round 7: 3960 lines.
Round 6 (pin d4d422780): re-pin alone, clean project build 79.70 s wall, 1303 MB max RSS, exit 0,
0 "error:" lines, 1321 jobs, 67 `#print axioms` all [propext, Classical.choice, Quot.sound].
With the deprecated write paths: clean build 88.06 s wall, 1348 MB max RSS, exit 0, 1323 jobs,
82 `#print axioms`, all [propext, Classical.choice, Quot.sound]. After the Summary update: 87.99 s, 1341 MB, exit 0, 1323 jobs, 82 axioms lines, same set.
Round 5 (pin c1fe45a71): clean project build (`rm -rf .lake/build`) 78.79 s wall, 1304 MB max RSS
(/usr/bin/time -l), exit 0, 0 "error:" lines, 1319 jobs; 67 `#print axioms`, all
[propext, Classical.choice, Quot.sound].
Round 4 (pin c1fe45a71): clean project build (`rm -rf .lake/build`) 66.37 s wall, 1054 MB max RSS
(/usr/bin/time -l), exit 0, 0 "error:" lines, 1306 jobs; 35 `#print axioms`, all
[propext, Classical.choice, Quot.sound]. Lines: Functions/ + Generic/ 7885, Summary 328.
Earlier:
At pin c1fe45a71, clean project build (`rm -rf .lake/build`, EthLib oleans prebuilt): 63.39 s wall,
1034 MB max RSS (/usr/bin/time -l), exit 0, 0 "error:" lines. First build of the c1fe45a71 pin from
a copied cache of 997edf8e4 (EthLib rebuilt): 153.81 s, 1024 MB.
Per module (lake): TransferFrom 10 s, TransferOk 7.3 s, SafeMath 5.6 s, Approve 5.4 s,
TransferFeeBody 4.2 s, TransferBody 4.1 s, TransferFee 3.9 s, TransferFromBody 3.4 s,
TransferFault 3.3 s, Transfer 3.0 s, BalanceOf 2.8 s, Common 2.5 s, ApproveRevert 1.9 s.
Lines: Functions/ + Generic/ total 5413 (wc -l).
No limits (maxRecDepth, heartbeats) raised anywhere.
