# Status of the USDT verification

File paths in this page are those of the round-21 layout (docs/LAYOUT.md, which also maps the old
paths to the new ones); the round entries keep the old file names only where a file no longer exists.

Pinned EthLib: bc16ee428 (master after #1616; includes #1611, #1612, #1613, #1615 and #1616;
commit bc16ee428baf03295ef3622c30c9c901bae1444a, round 48). Re-pinned in round 48: EthLib's
Logic/GasMono.lean, RunMono.lean, LessGas.lean, NoAbort.lean and Route.lean replace the local
copies of `addGas` (was `Gas.sh`), `Fails`, `Follows` (was `Gas.Rel`), `RunMono`, `StepFollows`
(was `Gas.RelS`), every `runMono_*` fact, `NoAbort` and its facts, `NoAbortLow`, the SSTORE stuck
facts, and `Route`, `Routes` and the route functions. The local `StepG`, `HoareG`, `SpecG`,
`Stuck`, `StepGA` and the rules over the local `At` stay (round 48 below says why).
Previous pin: 0c34dc001 (master after #1608; includes #1597, #1599 and #1605; commit
0c34dc0010f6ff1b3d5f1c7614af10faa85fb685, round 47). Re-pinned in round 47: EthLib's `At` names
the return data of a frame (#1351), so `At` in this repository is now the local predicate of Evm/At.lean, with the same twelve
conditions as EthLib's `At` at the previous pin and no condition on the return data. EthLib's
Call/Parent.lean (#1597), `extcodesize_of_berlin_le`, `processMessage_map_val` over any meter and
`prepareFirstFrame_of_value_eq_zero` (#1599), Logic/FailsOn.lean (#1605) and `instruction_sub`
replace Evm/Local/Parent.lean, Evm/Local/Extcodesize.lean, Evm/ProcessMeter.lean,
Evm/FirstFrame.lean, Evm/Sends.lean and `Local.instruction_sub` (all removed).
Previous pin: fd3457dbf (master after #1300; includes #1292, `At` names an empty output and STOP
gives `Halted false .empty`, and #1299, DELEGATECALL/CALLCODE; commit fd3457dbfbf2118fd5d05fab5b42ffaafa07f28d).
Re-pinned in round 9: EthLib's `stop` (#1272/#1292), `gas_rule` and `extcodesize` (#1280) replace the
local `Local.stop`/`Stopped` (Local/Halt.lean) and `Local.extcodesize`/`gasOp` (Local/Account.lean),
both files deleted; `memoryReadBytes_memoryWrite_eq_append` (#1266 follow-up on master) replaces the
local `memoryReadBytes_write_after`; `recordStorageRead_recordStorageRead`,
`insert_insert_getD_self`, `getAccountOptional_setStorage` (#1277) now prove the local
`readSlot_readSlot`, `accessSlot_accessSlot`, `hasAccount_writeSlot`. Every STOP-ending spec now
states the empty output (`Halted false .empty`).
Previous pin: d4d422780 (merge of #1266; commit d4d422780db5d668b06d3fc2782ae7bca21074e1).
Re-pinned in round 6: EthLib's `callvalue`, `calldatasize`, `jumpi_of_eq_zero`,
`memoryReadBytes_memoryWrite_of_disjoint` (no read bound) and `memoryReadBytes_memoryWrite_memoryWrite`
replace the local `Local.read/callvalue/calldatasize/jumpi_zero'` and `Generic/Memory.lean` (deleted).
Previous pin: c1fe45a71 (#1250; commit c1fe45a711f2cecee729a7ef4f982535c7f5cba7).
Previous pin: 997edf8e4 (merge of #1238: NatCode, reshape, evm_step; commit 997edf8e411be8e7b1c768eecaefa706fe10b7aa).
The local NatCode copy and `reshape`/`Spec.reshape` were removed in favour of EthLib's.
Earlier pin: 5f5ae55b5 (#1223; commit 5f5ae55b5a4b8435c36c92b2220162394dccd405).
Previously 189b419dd; re-pinned and rebuilt green (exit 0) with EthLib's stack rules replacing the local copies.
Bytecode: data/usdt.runtime.hex, 11075 bytes, keccak256 b44fb4e9...ea55, block 26362952 (see data/SOURCE.md).
No `sorry`, `admit`, axiom, `native_decide`, `bv_decide` or `decide +native` anywhere.
`decide +kernel` (kernel-checked) is used for jump-destination walks and one `exp` value.
`#print axioms` on every main theorem: [propext, Classical.choice, Quot.sound] (UsdtVerify/Test/Axioms.lean, printed at build).

## Proved

All specs: fork with `Fork.berlin ≤ fork`, the one-counter (`Nat`) gas meter of EthLib's logic
(EthLib runs transactions with that meter up to BPO5, and with the EIP-8037 `StateGasMeter` from
Glamsterdam, which no theorem here covers; see Open),
start frame `At CODE message 0 [] .empty gas state substate` (fresh call frame), and the real
interpreter loop `runFrame` for every gas bound and every message runner (`Spec.runFrame`).

### `UsdtVerify.TotalSupply.spec` / `runFrame_spec` (UsdtVerify/Usdt/Spec/TotalSupply.lean)
If the call data has `4 ≤ size < 2^256`, its first four bytes (big-endian) are 0x18160ddd,
the call value is 0, and byte 20 of storage slot 10 (the `deprecated` flag; bits 160..167) is 0,
then the run halts normally (no revert) with output = the 32 big-endian bytes of storage slot 1,
gas left = gas - (411 + price(slot 10) + price(slot 1)) (2100 cold / 100 warm, EIP-2929),
state = state with slots 10 and 1 recorded as read, substate = slots 10 and 1 marked accessed.

### `UsdtVerify.BalanceOf.spec` / `runFrame_spec` (UsdtVerify/Usdt/Spec/BalanceOf.lean)
Same hypotheses with selector 0x70a08231. Then the run halts normally with output = the 32 bytes
of the slot `keccak256(wordBytes k ++ wordBytes 2)`, where `k` = (call data word at offset 4)
AND (2^160 - 1); gas left = gas - (831 + price(slot 10) + price(balance slot)), where the balance
slot's coldness is taken after slot 10 was accessed (stated so to avoid assuming hash != 10);
reads and accesses recorded as above.

The base slot 2 of `balances`, slot 1 of `_totalSupply`, slot 10 / byte 20 of `deprecated`
were read off the bytecode (PUSH1 02 / PUSH1 01 / PUSH1 0a PUSH1 14 ... EXP DIV), see docs/MAP.md.

### `UsdtVerify.Transfer.spec_paused` / `runFrame_paused` (UsdtVerify/Usdt/Spec/Transfer.lean)
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

### `UsdtVerify.TransferOk.spec_ok` / `runFrame_ok` (UsdtVerify/Usdt/Spec/Transfer.lean)
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
- Returned bytes: transfer returns NO word (USDT's known non-standard ABI): the end frame is
  `Halted false .empty`, the output is empty (since the round-9 re-pin).
Fee > 0: `TransferFee.spec_fee`; insufficient balance: `spec_low` (both below). Overflows and fee > v:
the INVALID specs below. Not covered: deprecated (CALL).

### `UsdtVerify.Approve.spec_zero` and `spec_set` (UsdtVerify/Usdt/Spec/Approve.lean)
`approve(s, v)`, selector 0x095ea7b3, Berlin ≤ fork < Glamsterdam, not static, account exists,
68 ≤ size < 2^256, value 0, not deprecated (TetherToken checks slot 10 then calls StandardToken).
The allowance slot is `keccak(s ++ keccak(caller ++ 5))` (nested mapping, base slot 5).
- `spec_zero` (v = 0): the allowance is not read; it is written 0; log Approval(caller, s, 0)
  (topic 0x8c5be1e5…b925, data 32 bytes of 0); STOP; gas `2560 + price(slot 10) + sstoreCost`.
- `spec_set` (v ≠ 0 and allowance = 0, the `require`): allowance read then written v; log
  Approval(caller, s, v); STOP; gas `2753 + price(slot 10) + price(allowance) + sstoreCost(orig, 0, v, warm)`.
Each with an explicit stipend bound at the SSTORE. The revert with v ≠ 0 and a nonzero allowance: `spec_revert` below. Not covered: deprecated (CALL).

### `UsdtVerify.Approve.spec_revert` / `runFrame_revert` (UsdtVerify/Usdt/Spec/Approve.lean)
`approve(s, v)` with 68 ≤ size < 2^256, selector 0x095ea7b3, value 0, not deprecated, v ≠ 0 and
`allowed[caller][s]` ≠ 0 ⇒ REVERT at 8380 (the `require`), empty output, gas left
`gas - (703 + price(slot 10) + price(allowance))`, slots 10 and the allowance recorded read/accessed.

### `UsdtVerify.TransferFrom.spec_ok` / `runFrame_ok` (UsdtVerify/Usdt/Proofs/TransferFrom.lean, Usdt/Spec/TransferFrom.lean)
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

### `UsdtVerify.TransferFee.spec_fee` / `runFrame_fee` (UsdtVerify/Usdt/Proofs/Fee.lean, Usdt/Spec/Transfer.lean)
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

### `UsdtVerify.TransferOk.spec_low` (UsdtVerify/Usdt/Spec/Transfer.lean)
`transfer(a, v)` passing the checks, `v*rate` no overflow, fee ≤ v, `balances[caller] < v`, and
`lowCost ≤ gas` ⇒ the frame halts exceptionally (EthLib `Faulted (.invalidOpcode 0xfe)`, #1250):
no output, gas 0, state = S with slots 3, 4 and the sender's balance recorded read, nothing
written. SafeMath fault blocks: `subFault` (sub, a < b), `addFault` (add, a + b ≥ 2^256).

### Transfer INVALID paths (UsdtVerify/Usdt/Spec/Transfer.lean)
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

### transferFrom reverts and INVALID paths (Usdt/Spec/TransferFrom.lean)
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

### `UsdtVerify.TransferFrom.spec_feeF` / `runFrame_feeF` (Usdt/Proofs/Fee.lean, Usdt/Spec/TransferFrom.lean)
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
`transferFrom_fee_conserves`. Each takes the end frame of a success path (`Halted false .empty ...`, as
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

### Round 5: deprecated paths (CALL to `upgradedAddress`), UsdtVerify/Usdt/Spec/Deprecated/*.lean
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
- Shared blocks (UsdtVerify/Usdt/Proofs/Common.lean): `ret` (return-one-word block, proved at 797
  and 1511), `depCheck` (deprecation check, proved at 3565 and 4665).

### Round 6: deprecated transfer, approve, transferFrom (Usdt/Spec/Deprecated/Transfer.lean, Usdt/Spec/Deprecated/TransferFrom.lean)
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
  `Halted false .empty (gas - preCost - callCost + child.gas - 51/53/53)` with the
  `incorporateChild` state and substate; child.error ≠ none ⇒ `Halted true .empty (… - 25)`.
  preCost: transfer 1357 + 3 slot prices + account price; approve 724 + slot 10 + account;
  transferFrom 1093 + 3 slot prices + account. `hg`: preCost + 100 ≤ gas; `htail`: 51/53/53 left
  after the CALL's price.
- `_succeeds` (callee assumption `SucceedsD`: every such message ends with no error) ⇒ STOP, no
  error, `∃ caller msg child` with `Sends`, `child.error = none`, `Halted false .empty …`.
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

### Round 7: the nonpayable revert (UsdtVerify/Usdt/Spec/Dispatch.lean)
Each of the 32 table entries begins with its own copy of `JUMPDEST CALLVALUE ISZERO PUSH2 (e+11)
JUMPI PUSH1 0 DUP1 REVERT` (checked byte by byte in the proof of `valueRevert`, one case per
entry; `DESTS` = the 32 destinations).
- `valueRevert`: at any `e ∈ DESTS`, stack `[x]`, memory `MEM0`, value ≠ 0 ⇒ `Halted true .empty
  (gas - 25)`, state and substate unchanged.
- `table_entry` (`decide +kernel`): for each `i : Fin 32`, the table tests `i + 1` entries for key
  `i` and branches to destination `i`.
- `spec` / `runFrame_spec`: Berlin ≤ fork, `4 ≤ size < 2^256`, `selector = ENTRIES[i].1`, value ≠ 0
  ⇒ `Halted true .empty (gas - (87 + 22 * (i + 1)))` with the start state and substate.

### Round 7: onlyOwner, pause(), unpause() (Usdt/Proofs/Owner.lean, Usdt/Proofs/Pause.lean, Usdt/Spec/Pause.lean)
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
  `Halted false .empty (gas - (1784 / 1671 + slotCost c0 + flagCost))`, state
  `writeSlot S C 0 (withPaused w0 1 / 0)`, substate `storeSub … ` with the log
  `log0 C PAUSE_TOPIC / UNPAUSE_TOPIC` (one topic, empty data) appended.
- `withPaused w b = (b * 2^160) | (~(0xff * 2^160) & w)`; `bit_withPaused`, `byte20_withPaused`,
  `owner_withPaused` (bit-level proofs, `decide +kernel` over `i < 256` for one Bool identity).

### Round 7: addBlackList, removeBlackList (Usdt/Proofs/Admin.lean, Usdt/Proofs/BlackList.lean, Usdt/Spec/BlackList.lean)
- Shared (Usdt/Proofs/Admin.lean): `hashTail7` (the lookup tail at the 13 copies not in `HASH_PCS`),
  `entry1` (entry of the five one-address functions, 74 gas), `setLow w b = b | (~0xff & w)`
  with `lowByte_setLow` and `bit_setLow` (bits ≥ 8 kept).
- `listWrite` (3375 / 7379, the two bodies are the same code 4004 bytes apart): `isBlackListed[a]`
  read and written to `setLow w 1 / 0`; `listLog`: `AddedBlackList(a)` / `RemovedBlackList(a)`
  (LOG1, data = the masked word `a`, memory grows to 128 bytes), jump back, STOP.
- `spec_add_notOwner` (328 + slot 0), `spec_remove_notOwner` (856 + slot 0): REVERT.
- `spec_add` / `spec_remove`: `Halted false .empty (gas - (1567 / 2095 + slot 0 + slot L + write))`,
  state `writeSlot (readSlot S C 0) C L (setLow w v)`, substate with both accesses, the write's
  refund and the log; `hstip`: 2779 / 3307 + slot 0 + slot L ≤ gas.
- `listState_flag`, `listState_other`: the end state in plain terms.

### Round 7: issue, redeem (Usdt/Proofs/Issue.lean, Usdt/Spec/Issue.lean)
- Blocks: `ownerLookup` (the `balances[owner]` lookup at its five copies, slot 0 warm, 229 gas),
  `issueTest1/2`, `redeemTest1/2` (the `require` tests), `reqPass` / `reqRevert` (their JUMPIs,
  13 / 19 gas), `issueOwner` / `issueTotal` / `redeemTotal` / `redeemOwner` (the writes, macro
  `op_write`), `amountLog` (LOG1 of the amount, 1075 gas to STOP), `entryW` (word-argument
  entry, 68 gas). Generic (no sorry): `readSlot_comm`, `accessSlot_comm`, `readSlot_0n0`,
  `accessSlot_0n0`.
- Reverts: `spec_issue_notOwner` (740), `spec_redeem_notOwner` (762), `spec_issue_req1`
  (875 + slots 0, 1), `spec_issue_req2` (1462 + slots 0, 1, O), `spec_redeem_req1` (794 + …),
  `spec_redeem_req2` (1052 + …).
- `spec_issue`: `Halted false .empty (gas - (3024 + slots 0, 1, O + issueCostO + issueCostT))`, state
  `issueState` (reads 0, 1, 0, O; `O := B + a`; read 0; `1 := T' + a`), substate `issueSub`;
  `hstip`: 4248 + slots + issueCostO ≤ gas. `spec_redeem`: 2614 + …, `redeemState`
  (`1 := T - a`, then `O := B' - a`), `redeemSub`; `hstip` 3838 + slots + redeemCostT.
- `issue_effects`, `redeem_effects`: with `O ≠ 1`, slot values as numbers, other slots kept.

### Round 7: setParams (Usdt/Proofs/SetParams.lean, Usdt/Spec/SetParams.lean)
- Blocks: `entry2` (two word arguments, 92 gas), `test1/test2` + `pass/fail` (the two
  `require`s), `write3` (slot 3, cold or warm), `mulCall` (slot 9, `exp 10 d` with its EIP-160
  price `50 * exponentBytes d`, SafeMath `mulBlock` at 10755, back to 5942), `write4` (slot 4),
  `paramsLogBlock` (slots 3 and 4 read back, two MSTOREs growing memory to 160 bytes, LOG1 of 64
  bytes, 1556 gas to STOP). Generic: `read_after64`.
- `spec_notOwner` (742 + slot 0), `spec_bpHigh` (771 + slot 0), `spec_feeHigh` (800 + slot 0).
- `spec_setParams`: `Halted false .empty (gas - (2425 + paramsCost))`, `paramsState`, `paramsSub` (log
  `Params(b, f)` with data `wordBytes b ++ wordBytes f`); `hstip` 3168 + … ≤ gas;
  `params_effects`.

### Round 7: deprecate, transferOwnership (Usdt/Proofs/AddrWrite.lean, Usdt/Spec/AddrWrite.lean)
- Blocks: `depFlag` (2737: slot 10 := `withPaused w10 1`, 118 + slot 10 + write), `depPrefix`,
  `addrTail` (2770 / 7755: the warm slot `k` gets its low 160 bits from `a`, 158 + write),
  `ownTest` / `ownSkip` / `ownGo` / `ownEnd`; `listLog` (Usdt/Proofs/BlackList.lean) now also covers the
  `Deprecate(a)` log at 2830. `withAddr`, `bit_withAddr`, `addr_withAddr`, `byte20_withAddr`.
- `spec_deprecate_notOwner` (262), `spec_transferOwnership_notOwner` (900),
  `spec_transferOwnership_zero` (947 + slot 0: STOP, no write).
- `spec_deprecate`: `Halted false .empty (gas - (1628 + slots 0, 10 + depCost))`, `depState`, `depSub`;
  `hstip` 2840 + … . `spec_transferOwnership`: `gas - (1114 + slot 0 + ownCost)`, state
  `writeSlot S C 0 (withAddr w0 a)`, substate `storeSub …` (no log); `hstip` 3401 + slot 0.
- `deprecate_effects`, `transferOwnership_effects`.

### Round 7: destroyBlackFunds, the reverts (Usdt/Spec/Destroy.lean)
- `toBody` (its body pushes the local first: `JUMPDEST PUSH1 0 DUP1 PUSH1 0`, check at 7824).
- `spec_notOwner` (925 + slot 0), `spec_notListed` (1074 + slot 0 + `isBlackListed[a]`;
  `lowTest_eq`).
- The success path: see round 8.

### Round 8: destroyBlackFunds, the success path (Usdt/Spec/Destroy.lean; Usdt/Spec/BalanceOf.lean generalized)
- `BalanceOf.toLookup`, `lookup`, `back` now hold for any words below the getter's own (`rest`),
  `lookup` for any memory of 96 bytes (`lookMem M a`; `MEM1 a = lookMem MEM0 a` by `rfl`), and
  `back` for both return addresses 1511 (balanceOf) and 8008 (destroyBlackFunds).
  `BalanceOf.spec` is re-derived from them unchanged.
- Blocks: `toGetter` (pc 0 to 4665, the owner, `a` blacklisted: `lowTest_ne`; 1086 + slot 0 +
  `isBlackListed[a]`), then `depCheck` (4665), `toLookup`, `lookup`, `back` (to 8008),
  `zeroBal` (8008: `balances[a] := 0`, lookup tail 8018 from `HASH_PCS7`; 110 + write, `hstip`
  2409), `subTotal` (8080: SLOAD slot 1, unchecked SUB, SSTORE; 33 + slot 1 + write, `hstip`
  2332 + slot 1), `logBlock` (8096: `DestroyedBlackFunds(mkey a, d)`, 64 bytes of data, back to
  2486, STOP; 1368).
- `spec`: `Halted false .empty (gas - (2865 + slots 0, L, 10, B, 1 + costB + costT))`,
  `destroyState` (`B := 0`, then slot 1 `:= T' - d`, `T'` read after the first write),
  `destroySub` (both `storeSub`s and the log). Hypotheses: not deprecated, `a` blacklisted,
  `hstip1` 3763 + four reads, `hstip2` 3796 + four reads + costB + slot 1.
  `runFrame_spec` (via `Spec.runFrame`). `destroy_effects`: with `B ≠ 1`, `B` = 0, slot 1 =
  `sub T d` (and `T - d` as numbers when `d ≤ T`), every other slot unchanged.
- Not covered: destroyBlackFunds when deprecated (the getter calls the upgraded contract).

### Round 8: the getters (Usdt/Spec/Getters.lean, Evm/MemRev.lean; Usdt/Proofs/Common.lean generalized)
- Return blocks: `ret` now covers its ten copies (`RET_PCS`) with any `rest` below the word;
  `retB` (`BOOL_PCS`: 695, 1277, 1430, 2250; four ISZERO, 65 gas) and `retA` (`ADDR_PCS`: 935,
  1573, 1658; masked twice, 65 gas). `depCheck` also covers allowance's copy at 6925.
- Entries: `entry0` (ten getters without arguments, 34), `entry1m` (three one-address getters,
  74), `entry2` (two two-address getters, 104), `toEntry` (pc 0 to the entry, 62 + 22t).
- `spec_slot` (one theorem for decimals/maximumFee/_totalSupply/basisPointsRate, slots
  9/4/1/3, `164 + 22t + slot`), corollaries `spec_decimals` (384), `spec_maximumFee` (406),
  `spec_totalSupplyVar` (428), `spec_basisPointsRate` (758); `spec_maxUint` (824, no read);
  `spec_flag` / `spec_deprecated` (350) / `spec_paused` (614): word `if byte20 w = 0 then 0
  else 1` (`isZero4_flag`); `spec_upgradedAddress` (388), `spec_owner` (652), `spec_getOwner`
  (638): `w & (2^160 - 1)` (`addr_expr`). Gas numbers are `+ slot price`.
- `spec_balances` (478 + slot; `hashPub`), `spec_isBlackListed` (933 + slot),
  `spec_getBlackListStatus` (663 + slot; `hashTail7` at 4531): word `if w % 256 = 0 then 0
  else 1` (`isZero4_low`); `spec_allowed` (705 + slot; `hashPub2`, `hashPub`),
  `spec_allowance` (not deprecated; 1156 + slot 10 + slot; lookup at 10814 with `hashTail7` at
  10822 and 10883). Slot `allowSlot = keccak(a1 ++ keccak(a0 ++ 5))`.
- Generic (local, no sorry): `memoryReadBytes_write_rev` (a read across two adjacent writes made
  in reverse address order; EthLib has only the in-order one), used by the public mapping
  getters, which write the base word at 32 before the key at 0.
- allowance() when deprecated: round 9, Usdt/Spec/Deprecated/Allowance.lean (below).

### Round 8: runFrame wrappers (Usdt/Spec/RunFrames.lean)
- 50 `runFrame_*` theorems: the five deprecated no-code reverts (`runFrame_dep{,B,T,A,F}NoCode`)
  and every `spec_*` from pc 0 of PauseSpec, BlackListSpec,
  IssueSpec, SetParamsSpec, AddrWriteSpec, Destroy, Getters and GettersMap (DestroySpec has
  its own). Same hypotheses plus `start`/`within`; the conclusion is the spec's end frame for
  the `runFrame` result, for every gas bound and message runner. The file is generated from the
  statements by a script (scratch, not in the repo); each proof is `(spec_* …).runFrame start
  within`.

### Round 9: name() and symbol() (Usdt/Spec/Strings.lean)
- `spec_str` over `STR_GETTERS` (name: selector 0x06fdde03, entry 411, body 2488, return block
  430, slot 7; symbol: 0x95d89b41, 1724, 5206, 1743, slot 8), `spec_name` / `spec_symbol`,
  `runFrame_name` / `runFrame_symbol`. Hypotheses: selector, size, no value, the slot word `w`
  with `w.toNat % 256 = 2 * n` and 1 ≤ n ≤ 31 (short form), coldness `ck` of the slot, gas
  `1010 + slotCost ck` (name) / `1450 + slotCost ck` (symbol). Conclusion: `Halted false
  (wordBytes 0x20 ++ wordBytes n ++ wordBytes (topBytes w n))`, exact gas, state `readSlot`
  and substate `accessSlot` of the slot (three reads, folded by `readSlot_readSlot`).
  `topBytes w n = (w / 2^(8(32-n))) * 2^(8(32-n))` (the first n bytes, then zeros), proved equal
  to the code's `NOT(256^(32-n) - 1) AND ((w / 256) * 256)` bit by bit (`strWord_eq`).
- `spec_name_tether` / `spec_symbol_usdt`: with the slot equal to `NAME_WORD` ("Tether USD",
  low byte 0x14) / `SYMBOL_WORD` ("USDT", 0x08) the output is `wordBytes 0x20 ++ wordBytes 10 ++
  ("Tether USD".toUTF8 ++ 22 zero bytes)` / `... 4 ++ ("USDT".toUTF8 ++ 28 zero bytes)`
  (`name_bytes`, `symbol_bytes` by `decide +kernel`). That the mainnet slots hold these words is a
  hypothesis (not read from chain here).
- Blocks: `entryS`, `body1` (to the free-pointer write, 102 + slot), `body2` (length write,
  warm read, the two length tests, 217), `body3` (data word at 0x80, return jump, 173), `retA`
  (offset and length words, 99), `retL` (one round of the copy loop, 78), `retE1` (loop exit,
  padding test, 77), `retE2` (mask, write back, RETURN 0xa0..0x100, 146). Memory as appended
  words (`MEMB`..`MEME`), reads by the generic local `read_left`, `read_right`, `ld`,
  `write_end` (MSTORE at the end appends).
- Not covered: the empty string (`n = 0`, the JUMPI at 2567 taken) and the long form
  (n ≥ 32, the loop over `keccak(slot)` at 2595 and more rounds of the copy loop).
- Pitfall: one theorem for the whole body (60+ steps, two cases) hit the 200000-heartbeat limit;
  split into three blocks (no limit raised).

### Round 9: allowance(owner, spender) when deprecated (Usdt/Spec/Deprecated/Allowance.lean)
- Path read off the bytecode: entry 2046 (`entry2`), deprecation check 6925 (`depSetA`, flag set,
  on at 6949), `fwdArgsA` (6949 → 7186: warm read of slot 10, `upWord`, 0 at 0x80, the selector
  word at 0x60, owner at 0x64, spender at 0x84; memory grows to 192 bytes, `M3A`), EXTCODESIZE
  7186 (`toCallA`/`noCodeA`), CALL 7203 (gas `gasleft - 710`, value 0, input 0x60..0xa4 = 68
  bytes, output 32 bytes at 0x60), 7204 (`failTailA` / `okTailA`), return block 2132 on 192
  bytes (`retAl`).
- `spec_depAl` (any callee): `Sends message ua c (dataAl message) msg`, `dataAl` = SEL 0xdd62ed3e
  ++ addrArg 0 ++ addrArg 1; msg.gas = `(callGasAl …).subCall`; caller state/substate exact;
  child.error = none ⇒ `Halted false (wordBytes (resWord (outMemOf (memAl message) child.output)))
  (gas - preCostAl - callCost + child.gas - 128)` with the `incorporateChild` state and substate;
  else `Halted true .empty (… - 25)`. `preCostAl = 1187 + slot 10 + account`.
  `spec_depAl_answers` (`AnswersD`, output ≥ 32 bytes ⇒ returns its first word),
  `spec_depAl_fails`, `runFrame_depAl_process`, `spec_depAlNoCode` / `runFrame_depAlNoCode`
  (gas `1184 + slot 10 + account`).
- The shared blocks of Usdt/Spec/Deprecated/TotalSupply.lean take their pcs as a disjunction used positionally by the
  callers; rather than renumber them, `depSetA`, `toCallA`, `noCodeA`, `failTailA`, `retAl`
  repeat their proofs at the pcs of this path (192-byte memory for the return block).

### Round 9: the fallback (Usdt/Spec/Dispatch.lean)
- `revert406`: `JUMPDEST PUSH1 0 DUP1 REVERT` at 406, 7 gas, any stack and memory.
- `spec_unknown`: `4 ≤ size < 2^256` and `BitVec.ofNat 256 (selector data) ∉ ENTRIES.map
  Prod.fst` ⇒ `Halted true .empty (gas - 773) state substate` (EthLib's `branch_of_forall_ne`,
  `tested_of_forall_ne`: the table falls through to 54 + 32 * 11 = 406 after 32 tests). No value
  hypothesis.
- `spec_short`: `size < 4` ⇒ the prelude's JUMPI to 0x196 is taken; `Halted true .empty
  (gas - 46) state substate`. No value hypothesis.
- `runFrame_unknown`, `runFrame_short`.

### Round 10: destroyBlackFunds when deprecated (Usdt/Spec/Deprecated/Destroy.lean)
- Path: `DestroySpec.toGetter` (0 → 4665, memory `MEMB`), `depSet` (4665, flag set),
  `fwdArgsD` (4689 → 4874: `fwdArgsB` on any 96-byte memory with the free memory pointer 0x60;
  memories `D1`, `D2`, `D3`; `read40_D*`, `data_D3`), `toCall`/`noCode` (4874), CALL at 4891
  (`callWith`, input 0x60..0x84, output 32 bytes at 0x60), `failTail` (4892) or `okTailD` (4892 →
  8008 with `resWord`), `zeroBalD` (8008, 160-byte memory, the SSTORE coldness `cB` free: the
  getter did not read `balances[a]`; `hashTail160` at 8018), `DestroySpec.subTotal` (8080),
  `logBlockD` (8096, 1362 gas: no memory growth). `tailD` composes 4892 → STOP.
- `spec_depD` (any callee): `Sends message ua c (dataB message) msg`, msg.gas =
  `(callGasD …).subCall`, caller state/substate exact; child.error = none ⇒ `Halted false .empty`
  with state `tailState S C a d` (`balances[a] := 0`, then slot 1 := `T' - d` unchecked) and
  substate `tailSub` (both `storeSub`s and the log), `S`/`ss` the incorporated state/substate,
  `d = resWord (outMemOf (memD message) child.output)`, gas `… - tailCost` (1581 + both SSTORE
  prices + slot 1 read); else `Halted true .empty (… - 25)`. `preCostD = 1500 + slots 0, L, 10 +
  account`. Hypotheses beyond the getter's: `htail : TAIL_MAX (47881) ≤ gas after the CALL's
  price` (EthLib's `sstoreCost_le` bounds both writes by 22100), and `hkeep` on the callee
  assumption (a forwarded message that ends with no error leaves `C`'s account in its state;
  needed by `writeSlot`).
- `spec_depD_answers` (`AnswersD` + `hkeep`: STOP, empty output, state `tailState S C a
  (loadWord o 0 32)` for some `S`), `spec_depD_fails`, `runFrame_depD_process` (`keep_runsAs`:
  `RunsAs` gives `hkeep` when `Q`'s stopped frames have no error and `C`'s account),
  `spec_depDNoCode` / `runFrame_depDNoCode` (gas `1497 + slots 0, L, 10 + account`).
- Finding (stated by `spec_depD`): when deprecated, `_totalSupply` of this contract drops by the
  balance that the UPGRADED contract reports, and this contract's `balances[a]` becomes 0.

### Round 10: name() and symbol() for the empty string and the long form (Usdt/Spec/Strings.lean)
- Generic local rules (any code): `mloadIn`, `mstoreIn` (a word within a memory whose size is a
  multiple of 32: no growth), `mstoreApp` (a word at the end: appended, price
  `memoryGasCost (s + 32) - memoryGasCost s`), `returnIn`, `ext_in`, `ext_app`, `write_last`,
  `read_cat`; words `wd`, `add_wd`, `sub_wd`, `and31w`, `maskTop` (the padding mask keeps the
  first m bytes of any word).
- The return block for any string (`retG`): memory `Mb` of `P` bytes (P ≡ 0 mod 32) with the free
  pointer `P` at 0x40, `N` at 0x60 and the words `dw i` at `0x80 + 32 i`, i < W = ceil(N/32):
  `retAG` (offset and length appended), `retLG` / `loopG` (the copy loop at 467 / 1780 by
  induction on the rounds), `retXZ` / `retZG` (32 | N: on at 539 / 1852, RETURN) or `retXP` /
  `retPG` (padding: the last word masked in place, RETURN). Output `wordBytes 0x20 ++ wordBytes N
  ++ strData dw N`, gas `retCost P N` = 170 + 75 W + (30 or 146) + memory growth.
- The body for any length: `body1G` (length `lenOf w`, free pointer `128 + 32 W`), `body2E` (N = 0:
  JUMPI at 2567 / 5285 taken), `body2L` (N ≥ 32: JUMPI at 2575 / 5293 taken, `keccak(wordBytes k)`
  at 2607 / 5325), `roundC` / `roundX` / `loopL` (storage loop at 2609 / 5327, one SLOAD per word,
  `rdSt` / `rdSs` / `rdGas` record the reads and their prices; exit 46 gas).
- `spec_strEmpty`, `spec_strLong`, corollaries `spec_nameEmpty` (643 + slot), `spec_symbolEmpty`
  (1083 + slot), `spec_nameLong`, `spec_symbolLong`, and `runFrame_*` for all four. The long
  form needs `N < 2^180` (stated). Odd slot words with `w / 2 < 32` (never written by Solidity)
  are not covered.

### Round 10: the global invariant (UsdtVerify/Usdt/Invariant/Supply.lean)
- Token state read from the storage of `C`: `bal C S i` = `balances[i]` (slot `mapSlot (wd i) 2`)
  as an integer; `sumBal C S` = Σ_{i < 2^160} `bal C S i` (`sumTo`, a plain recursive sum);
  `tot C S` = slot 1; `Inv C S` : `sumBal C S = tot C S`.
- Hypothesis `KeccakSep` (a structure, an explicit argument of every theorem that needs it; NOT
  proved, it is about keccak): `inj` (distinct address words below 2^160 have distinct balance
  slots), `fixed` (a balance slot is none of the slots 0..10), `list` (never `mapSlot y 6`),
  `allow` (never `mapSlot y (mapSlot z 5)`), `one_list`, `one_allow` (slot 1 is neither).
- Generic: `sumBal_readSlot`, `tot_readSlot`, `inv_readSlot`, `inv_rdSt` (reads change nothing);
  `sumBal_write_bal` (a write of `balances[x]`: the sum changes by new − old), `sumBal_write_nb`,
  `tot_write_ne`, `tot_write_one`, `inv_write_nb`; `le_sumTo` (a balance is at most the sum).
- Per success path (end state as the spec states it, over its `S`): `transferOk_inv`,
  `transferFee_inv`, `transferFromOk_inv`, `transferFromFee_inv` (allowance step `allowState`
  with or without the write), `approveZero_inv`, `approveSet_inv`, `pause_inv` (pause and
  unpause), `transferOwnership_inv`, `list_inv` (add/removeBlackList), `params_inv`,
  `deprecate_inv`, `issue_inv`, `redeem_inv`, `destroy_inv`. Hypotheses: `KeccakSep`, the
  contract has an account, `Inv` before, and the no-wrap conditions that the spec of the path
  assumes (same statements).
- destroyBlackFunds: the subtraction from `_totalSupply` is unchecked, but under `Inv` the
  balance `d` is one term of the sum, so `d ≤ _totalSupply` (`le_sumTo`) and the result is
  `Σ − d`: `Inv` holds after (no extra hypothesis).
- Sequences: `Step C` (reads, writes of fixed / blacklist / allowance slots, and the eight
  balance-changing end states, each with its no-wrap hypotheses), `Steps C` (finite sequences),
  `step_inv`, `steps_inv`. `reach_*`: the end state of each writing success path, over the start
  state, is reached by `Steps` under the spec's own hypotheses (transfer ok/fee, transferFrom
  ok/fee, approve zero/set, pause/unpause, transferOwnership, add/removeBlackList, setParams,
  deprecate, issue, redeem, destroyBlackFunds). `transfer_ok_keeps` combines one of them with
  `steps_inv`. Read-only paths end in `readSlot` / `rdSt` of the start state (`Step.read`,
  `Step.rd`).
- What is NOT claimed: that the proved paths are all the success paths of a call (no
  completeness theorem over all inputs and gas); the deprecated paths (the callee's effects are
  arbitrary); `KeccakSep` itself.

### Round 11: gas shift and the completeness of the dispatcher (Evm/Gas.lean, Evm/GasRules.lean, Usdt/Complete/Dispatch.lean)
- `Gas.sh k e` (e with k more gas), `Fails`, `Rel`, `RunMono run` (∀ a k, `run a` fails or gives
  `b` with `run (sh k a) = sh k b`), `GasMono x` (the same for `step` from every frame with `k`
  less gas than `x`), `StepG` (= `Step` from a `GasMono` frame), `HoareG`, `SpecG`
  (`HoareG.toHoare`, `SpecG.toSpec`, `SpecG.runFrame`, `SpecG.seq`, `SpecG.consequence`).
- `low_of_reaches`, `SpecG.low`: a `SpecG` from `sh k l` and a run of the interpreter loop from
  `l` (any gas bound, any runner) ending with no error in `s` ⇒ the postcondition holds of
  `sh k s`. `SpecG.halted` (a normal halt: same output, state, substate, `k` less gas),
  `SpecG.not_ok` (a postcondition with an error: no run with less gas ends with no error).
- `At.ruleG` (EthLib's `At.rule` plus `RunMono`), `invalid_feG`; `RunMono` for binaryOp, unaryOp,
  calldataload, mstore, jumpdest, readFrame (word independent of the gas), pushN, dupN, swapN,
  jumpi, revert (generic over the frame, stack underflow and overflow included).
- G-rules (EthLib's rules restated over `StepG`, same hypotheses): `push_of_decodeG`, `pushG`,
  `push1G`, `push_of_readFrameG`, `callerG`, `callvalueG`, `calldatasizeG`, `binaryG`, `unaryG`,
  `dup_of_decodeG`, `dupG`, `dup1G`, `swap_of_decodeG`, `swapG`, `jumpdestG`, `jumpi_zeroG`,
  `jumpi_of_eq_zeroG`, `jumpi_takenG`, `calldataloadG`, `mstoreG`, `revertG`, `reshapeG`,
  `repcG`, `HoareG.gas_eq`.
- Over `StepG`: `preludeG`, `branchTableG` (EthLib's `branchTable`), `dispatchG`, `revert406G`,
  `spec_unknownG`, `spec_shortG`, `valueRevertG`, `nonpayableG`.
- `selector_cases`: size < 4, or a selector that is no key, or the key of entry `i : Fin 32`.
- `runFrame_ok_dispatch`: Berlin ≤ fork, size < 2^256, fresh frame at pc 0, any gas: a run of the
  loop that ends with no error ⇒ 4 ≤ size, value = 0, selector = key of some entry `i`.
- Why `StepG` and not EthLib's `Spec`: a `Spec` does not name the frames it passes, and GAS (and
  CALL) give another result with more gas, so the shift argument needs the chain to avoid them.
  A triple over `StepG` carries that for each step.

### Round 12: the function specs over `StepG`; completeness of totalSupply, balanceOf, transfer (Evm/GasRules.lean, Evm/Exact.lean, Usdt/Complete/Read.lean, Usdt/Complete/Transfer.lean)
- `RunMono` for POP, JUMP, MLOAD, KECCAK256, EXP, RETURN, STOP, SLOAD, SSTORE and LOG0..LOG4
  (`runMono_pop` ... `runMono_log`), for every frame. SSTORE: the stipend check, the charge,
  the state-gas charge, the static check and the write all fail (or halt with an error through
  `keepReads`) with less gas, or give the same frame with `k` less gas. G rules: `popG`, `jumpG`,
  `mloadG`, `keccak256G`, `expG`, `expLG` (the local `Local.exp`), `returnG`, `stopG`, `sloadG`,
  `sstoreG`, `sstoreWG` (the local `sstoreW`), `logG`, `SpecG.reshape`; `branchTableG` moved here.
- `StepLift R R'` (every `R` step is an `R'` step; instances `R R` and `StepG Step`),
  `Triple.lift`, `Triple.seqL`; `Coe` from `HoareG`/`SpecG` to `Hoare`/`Spec`. The `step` macro
  is `refine Gas.Triple.seqL r ?_`, so a rule over `StepG` also runs in a goal over `Step`. The
  macros of Usdt/Steps.lean (`pushR`, `binR`, `popR`, `jumpR`, ...) give the G rules; `repc`/`restate` (Evm/Steps.lean)
  are over `StepG` (`repcH`/`restateH` over `Step`).
- Every function file was restated by a script (code regions only): `Hoare fork` → `HoareG fork`,
  `Spec fork` → `SpecG fork`, each EthLib rule → its G rule. The theorem names did not change;
  every non-deprecated specification (and the Summary aliases) is now a `SpecG` (it implies the
  old `Spec` by `SpecG.toSpec`, also a coercion). The 34 deprecated theorems whose path goes
  through EXTCODESIZE, GAS, CALL or states a callee specification (`toCall`, `preCall*`,
  `spec_dep*`, `noCode*`, ...) stay over `Step`, closed under use; the blocks they use before and
  after the call are now over `StepG`.
- `ok_exact`: a `SpecG` to a normal halt paying `cost`, for every gas from `B ≥ cost`, and a run
  of the loop from the same frame with any gas that ends with no error ⇒ `cost ≤ gas`, output,
  `s.gas = gas - cost`, state and substate as stated. `no_ok`: a `SpecG` to an error for every gas
  from some bound ⇒ no run from that frame ends with no error.
- `ok_totalSupply`, `ok_balanceOf` (Berlin ≤ fork, size < 2^256, the selector, not deprecated):
  every successful run returns the slot word with the exact gas, state and substate.
- `ok_transfer` (also fork < Glamsterdam, not static, the contract has an account, not
  deprecated, the eight coldness flags named as in the specs): every successful run passed all
  the checks (68 ≤ size, not paused, caller not blacklisted, no overflow of `v * rate`,
  `fee ≤ v`, `v ≤ balances[caller]`, no overflow at the recipient) and is `spec_ok` (fee 0) or
  `spec_fee` (fee > 0 and no overflow at the owner), exact gas, state, substate, empty output.

### Round 13: completeness of approve, transferFrom and the owner functions (Usdt/Complete/Approve.lean, Usdt/Complete/TransferFrom.lean, Usdt/Complete/Owner.lean, Usdt/Spec/SetParams.lean)
- New specs: `Approve.payloadRevert` / `Approve.spec_payload` (approve with 4 ≤ size < 68:
  TetherToken's payload check at 2931 fails before the deprecation check; REVERT, no output,
  state and substate unchanged, gas 280). `SetParamsSpec.mulCallFault` / `spec_mulOv` (the owner's
  setParams with `b < 20`, `m < 50` and `m * 10^d ≥ 2^256`: INVALID at 10802 after the write of
  slot 3).
- `no_ok2`, `ok_exact2`, `ok_exact3`: `no_ok`/`ok_exact` for specs with two or three gas
  hypotheses; the bounds are found by unification (no explicit `B` sums).
- `ok_approve` (not deprecated): 68 ≤ size, and `spec_zero` (`v = 0`) or `spec_set` (`v ≠ 0`,
  allowance 0); excluded: `spec_payload`, `spec_revert`.
- `ok_transferFrom` (not deprecated): 100 ≤ size, not paused, `f` not blacklisted, no overflow of
  `v * rate`, allowance MAX_UINT or ≥ v, `fee ≤ v`, `v ≤ balances[f]`, no overflow at `t`; then
  `spec_ok` (fee 0) or `spec_feeF` (fee > 0, no overflow at the owner). Excluded: `spec_paused`,
  `spec_blacklisted`, `spec_short`, `spec_mulOv`, `spec_allowLow`, `spec_feeGtF`, `spec_balLow`,
  `spec_toOvF`, `spec_ownerOvF`.
- `ok_pause`, `ok_unpause`, `ok_addBlackList`, `ok_removeBlackList`, `ok_issue`, `ok_redeem`,
  `ok_setParams`, `ok_deprecate`, `ok_transferOwnership` (`a = 0`: nothing written; `a ≠ 0`),
  `ok_destroyBlackFunds` (not deprecated): the caller is the owner and every `require` passed,
  exact output, gas, state, substate. None of these functions checks the call data size.
- Hypotheses of all of them, by name: `hfork` (Berlin ≤ fork), `hglam` (fork < Glamsterdam),
  `hstatic` (not static), `hacc` (the contract has an account), `hsize'` (size < 2^256), `hsel`,
  the coldness flags `hc..` (equations naming each flag, any value), and `hdep` (byte 20 of slot
  10 is 0) for approve, transferFrom and destroyBlackFunds.
- Getters (Usdt/Complete/Getters.lean): `ok_decimals`, `ok_maximumFee`, `ok_totalSupplyVar`,
  `ok_basisPointsRate`, `ok_deprecated`, `ok_paused`, `ok_upgradedAddress`, `ok_owner`,
  `ok_getOwner`, `ok_maxUint`, `ok_balances`, `ok_isBlackListed`, `ok_getBlackListStatus`,
  `ok_allowed`, `ok_allowance` (`hdep`): no branch, so each is `ok_exact` of the spec; exact output,
  gas, state (reads), substate. `ok_name`, `ok_symbol`: under the named hypothesis `StrForm w`
  (slot 7 / 8 word: low byte 0, or low byte `2 n` with 1 ≤ n ≤ 31, or odd with
  32 ≤ w / 2 < 2^180), one of the three paths (`spec_nameEmpty`, `spec_name`, `spec_nameLong`).
  Words outside `StrForm` (even with low byte ≥ 64, odd with w / 2 < 32, or a long length
  ≥ 2^180) have no specification.
- The invariant over every successful call, not deprecated (Usdt/Invariant/Calls.lean): `inv_X` for each
  of the 32 functions (from `ok_X`, `Invariant.reach_*` and `steps_inv`; read-only ones by
  `inv_readSlot` / `inv_rdSt`), and `inv_call`: Berlin ≤ fork < Glamsterdam, a fresh frame of
  `CODE` at pc 0, any call data below 2^256 bytes, any value, any gas, any gas bound, any message
  runner; hypotheses `K : KeccakSep`, `hstatic`, `hacc`, `hdep` (not deprecated), `h7`/`h8`
  (`StrForm` of slots 7 and 8), `hI : Inv C state`; if the loop ends with no error, then
  `Inv C s.state`. The match over the 32 table entries uses `runFrame_ok_dispatch`.
- Deprecated paths, first step (Evm/Split.lean): `low_to_running` (the analogue of
  `low_of_reaches` that stops at a running frame: a successful run from `l` passes through the
  low copy `z'` of every frame `z = sh k z'` that `sh k l` reaches by `StepG`, and the loop from
  `z'` ends in the same `s`), `HoareG.low`, `at_unsh`, `ok_split` (a `HoareG` to a running frame
  paying `c`, for every gas from `B ≥ c`: a successful run with any gas has `c ≤ gas` and goes
  through that frame with `gas - c`). Applied to deprecated totalSupply()
  (now in Usdt/Complete/Deprecated/TotalSupply.lean): `prefixG_totalSupply` (pc 0 to 3719, over `StepG`) and `dep_totalSupply_split` (every
  successful deprecated `totalSupply()` run goes through the EXTCODESIZE frame at 3719 with gas
  `gas - (574 + price(slot 10))`, slot 10 read).

### Round 14: the invariant when deprecated, destroyBlackFunds (Usdt/Invariant/DeprecatedDestroy.lean)
- `inv_tail_iff` (KeccakSep, account, `a < 2^160`, `Inv C S`): `Inv C (tailState S C a d) ↔
  d = storageAt S C (mapSlot a 2)`. If `d ≤ T` the new total is `T - d`. Otherwise it wraps to
  `2^256 - d + T`, which is larger than `T - b`.
- `exists_breaks` (KeccakSep): a concrete state `zeroState C` (`ofBlock` of an empty block, an
  empty account written at `C`; every storage word is 0), with `a = 0` and `d = 1`: `Inv` holds
  before and fails after. Without KeccakSep this is not claimed: if `mapSlot i 2 = 1` for some
  `i`, the wrapped total could also be a balance.
- `depD_inv`, `depD_keeps`, `depD_breaks`: `SpecUnder` corollaries of `spec_depD`, with named
  callee hypotheses (`hcallee`: a successful forwarded call leaves the account and `Inv`;
  `hans`: the answer is the local balance, or `AnswersD` with `o`; `hsame`: the callee keeps every
  word of `C`'s storage; `hne`: the answer is not `balances[a]`). These statements need the gas
  bounds of `spec_depD` (`hg`, `htail`). The completeness of the deprecated paths, which would
  remove those bounds, is still open.
- No Summary alias: Invariant imports Summary (same as `inv_call`).

### Round 14: the deprecated paths from EXTCODESIZE on (Evm/Call.lean, Usdt/Complete/Deprecated/Call.lean, Usdt/Complete/Deprecated/TotalSupply.lean)
- Low-gas failures, computed from EthLib's step: `extcodesize_low` (gas below 2600/100, the code
  found), `step_gas_low` (below 2), `step_sub_low` (below 3), `callStep_low` (below the access
  plus memory: payCall's charge fails, `keepReads` halts the frame with outOfGas).
  `callStep_deep` covers CALL at the greatest depth: `genericCall` runs no message and
  `skipCall` pushes 0. Then `failTail` reverts.
- `call_ok`: CALL under ANY runner (no `Meets`). The step is `.child caller msg resume`
  (`callStep_child`). If the runner fails, the run fails (`runFrame_of_runChild_eq_error`).
  Otherwise the loop goes on from `resumeCall … child` (`resumeCall_eq`,
  `runFrame_of_step_eq_child`). The result is `CallEnd`, with the same message facts as `callWith`.
- `fromExt` (pcs 3719, 4874, 5739, 3213, 4200, so totalSupply, balanceOf (also inside
  destroyBlackFunds), transfer, approve and transferFrom): take a successful run from the
  EXTCODESIZE frame with any gas. The code size word is not 0, `accCost + 128 + memory ≤ G`, the
  depth is below the limit, and the run goes through `CallEnd`. The empty-code revert
  (`noCodeG`) and the JUMPI block (`midG`) are over StepG (`no_ok`, `ok_split`), and so is SUB
  (`subG`). Named hypotheses: `hcode` (the code `c` is found; `getCode` fails only for a code hash
  the state does not hold) and `hdel` (no Pectra delegation).
- `dep_totalSupply_complete`: every successful deprecated totalSupply() run, with any gas and any
  runner, is the forward. Its conclusion:
  - the runner returned a child with no error, for the `Forwarded` message with gas
    `callGas.subCall`;
  - the output is `resWord (outMem child.output)`;
  - the gas is exact: `gas - preCost - callGas.cost + child.gas - 121`, with at least 121 left
    after the CALL;
  - the state and substate are `incorporateChild`'s.
  Hypotheses: Berlin ≤ fork < Glamsterdam, data size < 2^256, the selector, deprecated, `hcode`,
  `hdel`.
- Pitfall: in `fromExt` the stack and gas terms must be in one form for omega. Generalize
  `accCost (decide …)` to `A` first. `rw [hext]` must come after `CallEnd` is unfolded, because
  the memory cost occurs only inside its body.

### Round 15: deprecated transfer, approve, transferFrom (Usdt/Complete/Deprecated/Transfer.lean)
- `prefixG_transfer` (0 → 5739), `prefixG_approve` (0 → 3213), `prefixG_transferFrom`
  (0 → 4200): the prefixes of `preCallT`, `preExtA`, `preExtF` restated over `StepG`
  (`Gas.callerG`, `Gas.reshapeG`, `repc`), up to the EXTCODESIZE frame. `okTailAG`: `okTailA`
  (3231) over `StepG` (`Gas.stopG`); `okTailT` and `okTailF` were already over `StepG`.
- `dep_transfer_complete`, `dep_approve_complete`, `dep_transferFrom_complete`: for any gas,
  any gas bound and ANY message runner, every run that ends with no error:
  - passed the checks before the forward: not paused and the blacklist (transfer: the caller,
    transferFrom: `_from`; excluded by `Transfer.spec_paused`/`spec_blacklisted` and
    `TransferFrom.spec_paused`/`spec_blacklisted`), or at least 68 bytes of call data (approve;
    `Approve.spec_payload`);
  - the code size at the upgraded address is not 0, `preCost + 100 ≤ gas`, the depth is below the
    limit;
  - the runner was called with the message of `Sends … (dataT/dataA/dataF message)` and gas
    `callGas*.subCall`, and returned a frame with no error;
  - the run stopped with empty output, gas `gas - preCost - callGas.cost + child.gas - 51/53/53`
    (at least that tail was left), and the state and substate of `incorporateChild`.
  Named hypotheses: `hcode`, `hdel`, and the coldness flags (`hc0`, `hcB`, `hc10`, `hcU`).
- Allowance (Usdt/Complete/Deprecated/Allowance.lean): `fromExt`, `midG`, `noCodeG`, `subG` now also take
  the pcs of allowance (EXTCODESIZE at 7186, GAS 7201, SUB 7202, CALL 7203; the same byte layout);
  the deep-CALL case at 7204 uses `DeprecatedAllowance.failTailA`. `prefixG_allowance` (0 → 7186)
  and `dep_allowance_complete`: the statement of `dep_balanceOf_complete` for the forward
  `Sends … (dataAl message)` (selector 0xdd62ed3e, owner, spender), output
  `wordBytes (resWord (outMemOf (memAl message) child.output))`, tail 128.
- destroyBlackFunds (Usdt/Complete/Deprecated/Destroy.lean): `fromExt` now takes up to 10 words below the
  CALL operands (`midG` up to 16), so it covers the call inside destroyBlackFunds (4874).
  `prefixG_destroy` (0 → 4874: `toGetter`, `depSet`, `fwdArgsD`) and `dep_destroy_complete`: for
  any gas, any gas bound and ANY runner, every successful run is the owner's (`spec_notOwner`
  excluded), with `a` blacklisted (`spec_notListed` excluded), the forward of `balanceOf(a)`
  answered with no error, then (via `ok_exact2` over `tailD`, bound `TAIL_MAX`) STOP with empty
  output in `tailState S C a d`, substate `tailSub`, gas `… - tailCost …` (the coldness of
  `balances[a]` and slot 1 taken in the substate after the call), with `S` the state of
  `incorporateChild` and `d = resWord (outMemOf (memD message) child.output)`. Named hypotheses:
  `hstatic`, `hcode`, `hdel`, the coldness flags, and `hkeep`: whenever the runner ends a
  forwarded message (`Sends … (dataB message)`), sent from the caller state at the CALL, with no
  error, the contract has an account in the
  child's state. The case without an account (where the SSTORE fails) is not covered.
- The invariant over every call (Usdt/Invariant/All.lean):
  - `LocalForward runChild message state s`: one runner call from `C` to `ua` that ended with no
    error, from a caller state whose storage at `C` equals the start storage at every slot (and
    `C` keeps its account), and `s.state = child.state`. `dep_{totalSupply,balanceOf,allowance,
    approve,transfer,transferFrom}_local` prove it for every successful deprecated run of the six
    forwarders (from `dep_*_complete` and `state_incorporateChild`): these functions write
    nothing locally after the CALL.
  - `dep_destroy_local`: under `KeepsInv`, the same call with `msg.data = dataB message`, then
    `s.state = tailState child.state C a d` with `d = resWord (outMemOf (memD message)
    child.output)`, and `C` has an account and `Inv C` in `child.state`.
    `inv_dep_destroy_iff` (`KeccakSep`): `Inv C s.state ↔ d = balances[a]` in `child.state`.
    `inv_dep_destroy`: with `HonestBalance`, `Inv C s.state`.
  - Named assumptions. `KeepsInv runChild C ua`: whenever the runner ends a message with
    `msg.caller = C`, `msg.currentTarget = ua` with no error, from a caller state where `C` has an
    account and `Inv C`, the child's end state keeps both. It covers any reentrant call into `C`
    (inside the child's run). `HonestBalance runChild message state`: whenever the runner ends such
    a message with `msg.data = dataB message` with no error, `resWord (outMemOf (memD message)
    child.output)` is `balances[a]` in the child's end state.
  - `inv_call_all`: `inv_call` with `hdep` removed. Hypotheses: `KeccakSep`, Berlin ≤ fork <
    Glamsterdam, not static, an account, size < 2^256, `StrForm` of slots 7 and 8, `Inv` at the
    start; and, each only when deprecated: `hdel`, `hkeeps : KeepsInv runChild C ua`,
    and, for the selector 0xf3bdc228, `hhonest : HonestBalance`. Conclusion: every run that ends
    with no error ends with `Inv C s.state`.
- `hcode` is no longer a hypothesis (round 15, step 5). `extcodesizeStep_notFound`: when the
  lookup of the code fails (`accountCode … = .error e`), EXTCODESIZE fails (before or after the
  charge). `fromExt_found`: at any of the six EXTCODESIZE pcs, a successful run found the code.
  Each `dep_*_complete` now concludes `∃ c, state.getCode (state.getAccount ua).codeHash = .ok c ∧
  …` and takes `hdel : ∀ c, state.getCode … = .ok c → .pectra ≤ fork → delegatedAddress c =
  none`; `hkeep` (destroyBlackFunds) quantifies the code in `Sends`. `inv_call_all` drops `hcode`.
  `hdel` stayed in round 15; round 16 removes it (below).
- Summary aliases: `totalSupply_dep_complete`, `balanceOf_dep_complete`, `allowance_dep_complete`,
  `destroyBlackFunds_dep_complete`,
  `transfer_dep_complete`, `approve_dep_complete`, `transferFrom_dep_complete`.

### Round 16: EIP-7702 delegation at the CALL, `hdel` removed (Evm/Call.lean, Usdt/Complete/Deprecated/)
- The route of a CALL (`Route := Option (Address × ByteArray)`, `Routes fork st c r`): `none` when
  the fork is before Pectra or `delegatedAddress c = none`; `some (d, c')` when, from Pectra,
  `delegatedAddress c = some d` and `st.getCode (st.getAccount d).codeHash = .ok c'`. Helpers
  `routeAddr`, `routeCode`, `routeCost` (the access to `d`, `accCost`, in the set of accessed
  addresses after the upgraded address), `routeState` (read of `d` recorded), `routeSub` (`d`
  accessed). `routes_congr`, `routes_rec`, `routeCost_insert_insert`,
  `accountAccessCost_of_berlin`.
- Step lemmas through EthLib's `accessDelegation` (no `hdel`): `callStep_child_r` (below the
  greatest depth with the gas of both accesses and memory: the step sends the message; caller
  state/substate with `routeState`/`routeSub`, extra price `callBaseCost + routeCost`, message
  with `codeAddress = routeAddr`, `code = routeCode`, `disablePrecompiles = r.isSome`, current
  target and target the called address); `callStep_low_r` (gas below that: the charge fails, the
  frame halts with an error); `callStep_deep_r` (greatest depth: 0 pushed); `callStep_missing`
  (from Pectra, a delegation whose delegate's code lookup fails: the step fails, a state error
  aborts). The `none` branches of the low/deep lemmas reuse `callStep_low`/`callStep_deep`.
- `CallEnd` and `call_ok` take the route `r` (hypothesis `hroute : Routes …` instead of `hdel`).
  `fromExt` has no `hdel`: it concludes `∃ r, Routes fork st c r ∧ …`, with the gas bound
  `accCost + 128 + routeCost + memory ≤ G`; a missing delegate code is excluded by
  `callStep_missing`.
- Each `dep_*_complete` (totalSupply, balanceOf, allowance, transfer, approve, transferFrom,
  destroyBlackFunds) drops `hdel` and concludes `∃ c r, getCode … = .ok c ∧ Routes fork state c r
  ∧ …`, with `preCost + 100 + routeCost (callSub…).accessedAddresses r ≤ gas`, the message
  `SendsVia message ua c r data msg` (as `Sends`, with the route's code address and code and
  `disablePrecompiles = r.isSome`), `msg.gas = (depCallGas fork asked left R).subCall`
  (`depCallGas` = `messageCallGas fork 0 asked left 0 (100 + R)`), and caller state/substate
  wrapped in `routeState`/`routeSub`. For `r = none` these are the round-15 statements (with
  `R = 0`). `hkeep` (destroyBlackFunds) now quantifies the route too.
- DepInvAll: `storageAt_route`, `hasAccount_route`; every `dep_*_local`, `dep_destroy_local`,
  `inv_dep_destroy_iff`, `inv_dep_destroy` and `inv_call_all` drop `hdel`. Under delegation the
  message's current target is still `ua`, so `KeepsInv` and `HonestBalance` are unchanged.
- Not changed in round 16: the forward specifications of round 5 to 10 (Usdt/Spec/Deprecated/*.lean,
  and the `SpecUnder` corollaries in Usdt/Invariant/DeprecatedDestroy.lean) still took `hdel`. Round 17 removes it
  (below).

### Round 17: the forward specifications along a route (Evm/Route.lean, Usdt/Spec/Deprecated/*.lean, Usdt/Invariant/DeprecatedDestroy.lean)
- Evm/Route.lean (new): `Route`, `Routes`, `routeAddr`, `routeCode`, `routeCost`,
  `routeState`, `routeSub`, `depCallGas`, `SendsVia`, `routes_congr`, `routes_rec`,
  `routeCost_insert_insert`, `accountAccessCost_of_berlin` and `callStep_child_r` moved there from
  Complete/DepCall.lean, now Usdt/Complete/Deprecated/Call.lean and Evm/Call.lean (same names, namespace `UsdtVerify.Complete`), with `Deprecated.accCost`
  from Usdt/Spec/Deprecated/TotalSupply.lean, so that the forward specifications can use them.
- `callWithR`: EthLib's `callWith` (a CALL with no value, as a `HoareUnder` triple under a callee
  assumption) along a route `r`, with `hroute : Routes fork state calleeCode r` in place of
  `callWith`'s hypothesis of no delegation. The price adds `routeCost` (the access to the
  delegate); the message has `codeAddress = some (routeAddr to r)`, `code = routeCode calleeCode r`,
  `disablePrecompiles = r.isSome`, current target `to`; the caller's state and substate are wrapped
  in `routeState`/`routeSub`.
- Every forward specification and its corollaries (`spec_dep*`, `spec_dep*_answers`,
  `spec_dep*_fails`, `spec_dep*_succeeds`, `runFrame_dep_answers` (totalSupply), `runFrame_dep*_process`, for
  totalSupply, balanceOf, allowance, transfer, approve, transferFrom, destroyBlackFunds) takes
  `{r : Route} (hroute : Routes fork state c r)` in place of `hdel` (`HypT`/`HypA`/`HypF`: the
  field `route` in place of `noDelegation`, and the structure takes `r`). The gas bound `hg` adds
  the price of the route (`callR`, `callRT`, `callRF`, `callRD`: `routeCost` of the set of
  accessed addresses at the CALL), and `callGas*` take it as their last argument (`100 + R`). The
  message is `SendsVia … r …` (the old `Forwarded` and `Sends` are removed), and the caller's state
  and substate are `routeState …`/`routeSub …`. The callee predicates `Answers`, `Fails`,
  `AnswersD`, `SucceedsD`, `FailsD` take the route; the `*_runsAs` lemmas give `RunsAs (routeCode c
  r) G Q`, with `hpre` on `routeAddr ua r`; the `*_process` theorems take the `Spec` of the code of
  the route. With `r = none` (`Routes … none` is the old `hdel`) each statement is the old one,
  with `R = 0`.
- Usdt/Invariant/DeprecatedDestroy.lean: `depD_inv`, `depD_keeps`, `depD_breaks` take the route the same way;
  `storageAt_callerD` takes the route.
- `callStep_low` and `callStep_deep` (Evm/Call.lean) state their hypothesis as `Routes fork
  evm.state calleeCode none`: they are the `none` case of `callStep_low_r`/`callStep_deep_r`.
- After this round no theorem of the repository takes a hypothesis that excludes an EIP-7702
  delegation at the upgraded address (checked by grep of `delegatedAddress`: it occurs only in
  `Routes`, in proofs, and in `callStep_missing`, whose hypothesis is that `c` IS a delegation).

### Round 17: static frames (Usdt/Invariant/Static.lean)
- `StaticKeeps runChild`: the premise `runs` of EthLib's `staticStep_runFrame` (the runner ends
  every static child message from a static frame in a state that differs from the caller's only
  by reads, with the same block), as a named runner assumption. `staticKeeps_process`: from
  Paris, `processRunner` meets it (EthLib's `processMessage_static`).
- `static_run` (any fork): a fresh frame `At CODE message 0 …` with `message.isStatic = true`,
  `message.code = CODE`, `StaticCode state message` (EthLib: a nonempty code runs at an account
  whose code hash is not the empty one), under a runner with `StaticKeeps`: every run that ends
  with `.ok` ends in a state with `SameOutside [] state s.state`. `inv_static`: `Inv C` is kept.
- `inv_call_all` is now in Usdt/Invariant/Static.lean: `hstatic` is replaced by `hstat : isStatic = true
  → message.code = CODE ∧ StaticCode state message ∧ StaticKeeps runChild`, and `hacc` is asked
  only when not static. The round-15 theorem is renamed `inv_call_ns` (Usdt/Invariant/All.lean).
- Not done: `hacc` for a frame that is not static. Without an account, the first SSTORE of each
  writing path fails (`setStorage` errors, an aborting state error), so no writing path succeeds;
  proving it needs, per writing path, the prefix up to its first SSTORE as a `HoareG` and a fault
  lemma for SSTORE without an account. The completeness theorems keep `hstatic` and `hacc` for the
  same reason (per-path fault proofs at the first write). (Done in round 18, below, except when deprecated.)

### Round 17: a finite sequence of calls (Usdt/Invariant/Seq.lean)
- `GoodCall C S S'`: an existential over fork, message, substate, gas, bound, runner, start
  frame and end frame: a successful run of `CODE` at pc 0 for a message to `C` from `S`, ending in
  `S'`, with every hypothesis of `inv_call_all` stated at `S`. `Untouched C S S'`: every storage
  word of `C` is the same. `Calls C`: the inductive finite sequences of both kinds of steps.
- `inv_goodCall`, `inv_calls` (`KeccakSep`): `Inv C` is kept along `Calls C`.
- `goodCall_process` (from Paris; before Glamsterdam when deprecated): a message with `message.code = CODE`, no value
  transfer and no precompile, with `processMessage … = .ok ended` and `ended.val.error = none`, is
  a `GoodCall` from the start state to `ended.val.state` (EthLib's `processMessage_map_val`,
  `at_startFrame`; `StaticKeeps` by `staticKeeps_process`).
- Not proved: that a failed top-level call keeps the storage of `C` after the rollback. EthLib's
  `getStorage_restoreTxState` needs the block (`parent`) of the end state to be the start's, and
  EthLib proves that only for static runs. So failed calls enter a sequence as `Untouched` steps,
  an assumption. Messages with value (all of which revert, `nonpayable`) are not covered by
  `goodCall_process` either. (Both done in round 18, below.)

### Round 17: the writing paths at Glamsterdam (Evm/GasRules.lean, every non-deprecated writing spec)
- `Gas.writeCost fork orig cur new cold := sstoreCost … + sstoreStateGas …` (the state gas of a
  new slot, 0 before Glamsterdam; `writeCost_of_lt`). EthLib's one-counter meter `Nat` has no
  reservoir: its `refill` is the identity and `chargeState` subtracts from the same counter.
- `sstoreStep_eq_any` (any fork from Berlin): the step of SSTORE in a frame that may write, with
  the price `writeCost` (from Glamsterdam the static check comes first and passes; the stipend
  check, the charge of `sstoreCost`, the charge of the state gas, the write). `sstoreG_any`, and
  `sstoreWG` now without `hglam` (the old pre-Glamsterdam `sstoreWG` is replaced).
- Every `sstoreCost fork` in the specifications is now `Gas.writeCost fork`; before Glamsterdam
  the two are equal. `hglam` was removed from every theorem (107 names) that needed it only through
  `sstoreWG` (found by a script over the call graph, checked by the build): every non-deprecated
  writing spec, its `runFrame_*` form, every completeness theorem of rounds 12 and 13, every
  `inv_X` and `inv_call`. They hold from Berlin on, Glamsterdam included.
- Still before Glamsterdam: the deprecated paths (EthLib's EXTCODESIZE and CALL rules, and the
  Route lemmas, are pre-Glamsterdam; `tailD` uses EthLib's pre-Glamsterdam bound
  `sstoreCost_le`), so the `dep_*` theorems, `inv_call_ns`, `inv_call_all` (which take
  `hglam` only when deprecated) and `GoodCall`/`goodCall_process` (the same). (Lifted in round
  19, below.)
- The Glamsterdam case rests on EthLib's model of Glamsterdam at the pin (fd3457dbf): its
  `sstoreCost` and `sstoreStateGas` for that fork, and its decoding of the opcodes used.

### Round 18: failed top-level calls and calls with value (Evm/Local/Parent.lean, Usdt/Invariant/Seq.lean)
- Evm/Local/Parent.lean (LOCAL, generic, proved from EthLib's semantics): every step of every frame,
  static or not, keeps the block of the state (`parent`): `parent_instruction` (the ten groups of
  instructions; SSTORE through EthLib's `TransactionState.parent_setStorage`, TSTORE by
  `parent_tstoreStep`, SELFDESTRUCT through `parent_selfdestructTransfer`, which rests on EthLib's
  `parent_modifyState` and `parent_moveEther`), `pResult_step` (calls and creations: the caller keeps it, and the
  frame that resumes keeps it when the child ended with the caller's block). `parent_runFrame`: a
  run keeps it under a runner that does. `parent_process`: by strong induction on the gas, every
  `processMessage` ends as `rollbackOnError state last` with `last` of the start block, and every
  `processCreateMessage` keeps the block (`parent_prepareCreation`, `parent_depositCode`). Any
  fork, any meter with `LawfulGasMeter`.
- `processMessage_failed_getStorage`: a message that ends with an error has, at every address and
  key, the storage word of the state it was sent from (EthLib's `getStorage_restoreTxState`, whose
  premise on the block is now proved for every message, not only static ones).
- `untouched_process_failed` (Usdt/Invariant/Seq.lean): so a failed top-level message, any code, is an
  `Untouched` step for every address. Round 17 had these steps as an assumption.
- `process_value_fails`: from Berlin, a top-level message of `CODE` with no precompile, call data
  below 2^256 bytes and a nonzero value ends with an error (both cases of EthLib's
  `processMessage`: value moved, `processMessage_map_val_value`; not moved,
  `processMessage_map_val`; a failed move gives no `.ok`), by `runFrame_ok_dispatch`.
- `process_step`: from Paris (before Glamsterdam when deprecated), every top-level message of
  `CODE` with no precompile that `processMessage` ends is a `GoodCall` (no error) or an
  `Untouched` step (an error). It takes the hypotheses of `goodCall_process` except "no value"
  (call data below 2^256 bytes and the named assumptions), for both cases; the error case uses
  none of them (`untouched_process_failed`).
- Still assumed in a `Calls` sequence: the `Untouched` steps that are not a top-level message of
  `CODE` (transactions to other accounts, fees).

### Round 18: no `hstatic`/`hacc` in the completeness theorems (UsdtVerify/Evm/Stuck.lean, the bad_* lemmas)
- UsdtVerify/Evm/Stuck.lean (generic): `Stuck z` (running, and the step from `z` or from `z` with any
  less gas fails or halts with an error); `not_ok_of_reaches`, `no_ok_stuck` (when, for every gas
  `g ≥ B`, the frame `At … g` reaches a `Stuck` frame along `StepG` (a `HoareG`), no run from
  `At … gas` ends with no error);
  `sstoreStep_bad`, `sstore_stuck`, `sstoreStuckW` (SSTORE in a static frame, or at an address
  with no account, is `Stuck`, any fork, any gas); `bad_of_not`, `hasAccount_readSlot_iff`.
- Per path, the prefix up to the first SSTORE as a `HoareG` to `Stuck` (the existing blocks are
  split into a `_pre` macro used by both): `PauseSpec.bad_pause`, `bad_unpause`,
  `BlackListSpec.bad_add`, `bad_remove`, `IssueSpec.bad_issue`, `bad_redeem`,
  `SetParamsSpec.bad_setParams`, `AddrWriteSpec.bad_transferOwnership`, `bad_deprecate`,
  `DestroySpec.bad`, `Approve.bad_zero`, `bad_set` (Usdt/Spec/Approve.lean), `TransferOk.bad_transfer`,
  `TransferFrom.bad_allowF`, `bad_transferFrom` (with the blocks `*Bad` below them).
- Every `ok_X` of a writing function (transfer, transferFrom, approve, the ten owner functions)
  no longer takes `hstatic` or `hacc`; each conclusion now begins with `message.isStatic = false
  ∧ hasAccount state C` (transferOwnership: in the `a ≠ 0` disjunct). `spec_feeGtF`,
  `spec_balLow`, `allowStep`, `bodyFeeGtF`, `bodyBalLow` take `hgood : A ≠ MAX_UINT → not
  static ∧ account` in place of `hstatic hacc` (with `A = MAX_UINT` nothing is written before
  those INVALIDs).
- `inv_X` (writing functions) and `inv_call` take neither; `inv_call_ns` takes `hacc` only when
  deprecated, and still takes `hstatic` (not static) for every call; `inv_call_all`, `GoodCall`, `goodCall_process`, `process_step` take
  `byte20 (slot 10) ≠ 0 → isStatic = false → hasAccount state C`.
- Still assumed, by name, in the invariant theorems: `KeccakSep`, `StrForm`, and when deprecated
  the runner assumptions `KeepsInv` and `HonestBalance` (`inv_call_all` also `hstat`). Since
  round 20 no account of the contract (`hacc`) is assumed by any of them.

### Round 19: the deprecated paths at Glamsterdam (Evm/Local/Extcodesize.lean, Evm/Route.lean, Evm/Call.lean, Usdt/Complete/Deprecated/)
- Prices over the fork (Evm/Route.lean): `accCost fork cold := accountAccessCost fork cold`
  (100 warm; 2600 cold, 3000 from Glamsterdam by EIP-8038) and `extCost fork cold :=
  externalBaseCost fork cold` (EXTCODESIZE: the access, plus 100 from Glamsterdam). Before
  Glamsterdam: `accCost_of_lt`, `extCost_of_lt` (= `if cold then 2600 else 100`); any fork:
  `accCost_false` (100), `callBaseCost_eq` (from Berlin), `extCost_ge` (≥ 100). `routeCost fork`
  prices the delegate with `accCost fork`. The removed `accountAccessCost_of_berlin` needed
  `hglam`.
- `Local.extcodesize` (LOCAL, generic): EXTCODESIZE from Berlin, Glamsterdam included, with the
  price `externalBaseCost fork cold` (EthLib's `Logic.extcodesize` stops before Glamsterdam).
- CALL at any fork from Berlin, computed from EthLib's `callStep`: `callStep_child_r` (no
  `hglam`; same conclusion: at Glamsterdam `payCall` charges the access and memory, the state gas
  0, then `messageCallGas … 0 0` on the gas left, and the numbers coincide with the old
  `messageCallGas fork 0 asked gas memory extra` once the access and memory are paid),
  `callWithR` (price `accCost fork cold`), `callStep_deep_r`. `callStep_low_r` and
  `callStep_missing` now conclude `StepBad` (the step fails, or halts the frame with an error):
  at Glamsterdam the check of the known price (`checkGas`) fails with a step error before the
  reads, or the check of the access to the delegate halts the frame; `ok_step_bad` turns either
  into "no run ends with no error". `callStep_low`, `callStep_deep` stay as the `none` case.
  `CallEnd`, `call_ok` use `accCost fork cold`; `extcodesize_low` uses `extCost`.
- The gas terms of the forward specifications and of the completeness theorems: `preCost*`,
  `askedOf*` take the fork (EXTCODESIZE at `extCost fork cU`); `callR*` through `routeCost fork`;
  `TAIL_MAX fork := 3681 + 2 * Gas.writeMax fork` with `Gas.writeMax fork` = 22100 before
  Glamsterdam, 110020 from Glamsterdam (`Gas.writeCost_le`: a cold access 2100, a write 10000 and
  the state gas of a new slot 97920), `TAIL_MAX_of_lt`: 47881 before Glamsterdam. `tailD` uses
  `writeCost_le` in place of EthLib's pre-Glamsterdam `sstoreCost_le`.
- `hglam` removed from: `toCall`, `preCall*`, `noCode`, every `spec_dep*` and its corollaries
  (`_answers`, `_fails`, `_succeeds`, `runFrame_*`, `_process`, `*NoCode`), the field `glam` of
  `HypT`/`HypA`/`HypF`, `fromExt`, `call_ok`, every `dep_*_complete`, `dep_*_local`,
  `dep_destroy_local`, `inv_dep_destroy_iff`, `inv_dep_destroy`, `depD_inv`/`depD_keeps`/
  `depD_breaks`, and the conditional `byte20 … ≠ 0 → fork < .glamsterdam` of `inv_call_ns`,
  `inv_call_all`, `GoodCall`, `goodCall_process`, `process_step`. The unused pre-Glamsterdam
  restatements `Gas.sstoreG` and `sstoreW` were deleted. After this round the only statements
  with `fork < .glamsterdam` are the reductions `accCost_of_lt`, `extCost_of_lt`,
  `Gas.writeCost_of_lt`, `TAIL_MAX_of_lt` (checked by grep).
- Done as one commit (09ae523), not one function at a time: `toCall`, `fromExt` and the CALL
  rules are shared by all seven deprecated functions.
- The Glamsterdam case rests on EthLib's model of Glamsterdam at the pin (fd3457dbf): its
  `externalBaseCost`, `accountAccessCost`, `callStep` (`checkGas`, `accessDelegation`, `payCall`),
  `sstoreCost` and `sstoreStateGas` for that fork.

### Round 19: deprecated destroyBlackFunds without `hstatic`/`hkeep` (Usdt/Spec/Deprecated/Destroy.lean, Usdt/Complete/Deprecated/Destroy.lean)
- `zeroBalBadD` (8008, memory of 160 bytes) and `tailBadD` (4892 after a successful call, then
  `okTailD`): in a static frame, or with no account for `C` in the state the call left, the run
  reaches the SSTORE of `balances[a]`, which is `Stuck` (`Gas.sstoreStuckW`).
- `dep_destroy_complete` takes neither `hstatic` nor `hkeep`. In the case of a successful child
  it splits on "not static and an account in the incorporated state"; otherwise `no_ok_stuck`
  with `tailBadD`. The conclusion adds `message.isStatic = false ∧ hasAccount child.1.state C`.
  Its named hypotheses are now the coldness flags only.
- `dep_destroy_local`, `inv_dep_destroy_iff`, `inv_dep_destroy` and `inv_call_ns` drop `hstatic`
  (`inv_call_ns` now holds for static frames too; `inv_call_all` still splits on the flag, since
  its `hacc` is asked only when not static).
- Still assumed: the account of the contract when deprecated, `hacc` (`byte20 (slot 10) ≠ 0 →
  isStatic = false → hasAccount state C` in `inv_call_all`, `GoodCall`, `goodCall_process`,
  `process_step`; `deprecated → hasAccount` in `inv_call_ns`). It is the premise of the named
  runner assumption `KeepsInv`. It cannot be derived from the deprecated flag: in EthLib's
  `TransactionState` the storage (`getStorage`, the write overlay over `preState`) is not tied to
  the existence of the account, so a nonzero slot 10 does not give an account. Removing it would
  mean restating `KeepsInv` (for example with `Inv` alone as premise and conclusion), a different
  assumption; not done.

### Round 20: the Summary's static/account hypotheses (UsdtVerify/Summary.lean, docs only)
- The "Common hypotheses" paragraph of Summary.lean now names every spec there that takes
  `hstatic` and `hacc` (the non-deprecated paths that reach an SSTORE, and their `runFrame_*`
  forms), the two transferFrom faults that take them only when the allowance is not `MAX_UINT`
  (`hgood`; their `runFrame_*` forms take both), the deprecated destroyBlackFunds specs (`hstatic`
  and `hkeep`), and the helper theorems that take an account. The list was made from the
  signatures of the alias targets (a script over the `alias` lines), not from memory.

### Round 20: the invariant without `hacc` (Usdt/Invariant/All.lean, Usdt/Invariant/Static.lean, Usdt/Invariant/Seq.lean)
- `KeepsInv` restated: premise `Inv C caller.state` only, conclusion `Inv C child.state` only.
  The round 15-19 form is kept as `KeepsInvAcc`; `KeepsInvNoAcc` is its missing case (no account
  of `C` in the caller state); `keepsInv_of_acc`: both give `KeepsInv`.
- Which one, at the CALL: a missing account is harmless to the frame (no step fails: no
  `dep_*_complete` takes an account, nor a forwarding spec of the six forwarding functions;
  destroyBlackFunds' forward specs take one only at the end of each forwarded call (`hkeep`); the CALL sends value 0, so EthLib's
  `finishCall` balance check `balance < value` is false). It reaches the runner: `LocalForward`
  now states `hasAccount caller.state C ↔ hasAccount state C` (proof: `hasAccount_caller_iff`,
  all the intermediate states are reads, definitionally the same accounts), and
  `localForward_noAcc` states the missing case. So `KeepsInv` covers it as an assumption; it is
  not derivable from the code.
- destroyBlackFunds: the account in the child's end state comes from `dep_destroy_complete`
  (round 19), `Inv` there from `KeepsInv`.
- `hacc` removed from `inv_of_local`, `dep_destroy_local`, `inv_dep_destroy_iff`,
  `inv_dep_destroy`, `inv_call_ns`, `inv_call_all`, `GoodCall`, `goodCall_process`,
  `process_step`. The unused `hasAccount_rec`, `hasAccount_route` were deleted.
- What changed in meaning: `KeepsInv` is now a different runner assumption. It asks more in one
  case (a caller state without an account of `C`, which the old form did not cover) and less in
  the other (it no longer asks the child to keep the account). Neither form implies the other (by the
  definitions; not stated as a theorem).
- `lake build UsdtVerify` (incremental): exit 0, 0 "error:" lines, 1384 jobs; `#print axioms`:
  398 [propext, Classical.choice, Quot.sound], 4 [propext, Quot.sound], 5 [propext], 1 none.
  No clean rebuild in this round (left to the reorganization).

### Round 21: the layout (docs/LAYOUT.md)
- Files moved, merged and split; no declaration, statement or proof changed. Generic EVM lemmas in
  `UsdtVerify/Evm/` (no import outside it); the bytecode, `Map.lean` (dispatcher, storage layout),
  `Spec/` (what each function does, from pc 0), `Proofs/` (the blocks; no import of `Spec/`),
  `Complete/` and `Invariant/` under `UsdtVerify/Usdt/`. docs/LAYOUT.md has the old to new map.
- Check of the code: the multiset of non-comment, non-import lines of every Lean file except
  Test/Axioms.lean, at c97bd42 and after the move, differs only in `section`/`end`, `namespace`,
  `open` and `variable` lines (33 sections around merged parts; the scaffolding repeated where a
  file was split). Test/Axioms.lean differs only in its imports.
- An independent read of the round 20 docs against the statements found three overclaims, now
  fixed: in a static frame `hstat` (`StaticCode` for the nonempty `CODE`) implies an account of
  `C`, so "no account assumed" holds for the frames that are not static (Static.lean, Seq.lean,
  RESULTS); the forward specifications of destroyBlackFunds take `hkeep` (an account at the end
  of each forwarded call), so "no forwarding spec takes an account" holds for the six other
  forwarding functions and for the start state (All.lean, RESULTS, round 20 above); "neither
  form implies the other" is by the definitions, not a theorem.

### Round 22: security properties (Usdt/Security/, Evm/Frame.lean; docs/RESULTS.md "Security properties")
- `Evm/Frame.lean` (generic): `Writes C W S S'` (every slot of `C` outside `W` keeps its word)
  and `NoDec C k S S'` (slot `k` does not decrease), with read/write/transitivity lemmas.
- `Security/Effect.lean`: `Effect` (one case per kind of successful call, from the `ok_X`
  completeness theorems) and `effect_call` (every successful run, not deprecated, slots 7 and 8 of
  `StrForm`, static or not, any call data below 2^256 bytes, value, gas, bound, runner); the slot
  classes `BalSlot`, `AllowSlot`, `ListSlot`, `OwnW`; the new keccak hypothesis `AllowSep` (a slot of
  `allowed` is none of the slots 0..10 and no slot of `isBlackListed`; not proved); `RunOk`,
  `Seq C Q` (successful runs meeting `Q`, and `Untouched` steps) and `seq_lift`.
- Access control (`Access.lean`): `Effect.nonOwner`, `nonOwner_call`, `nonOwner_seq`.
- Pause (`Pause.lean`): `Effect.paused`, `paused_call`, `paused_seq`.
- Blacklist (`Blacklist.lean`): `Effect.listed`, `listed_call`, `listed_seq`.
- Allowances (`Allowance.lean`): `transferFrom_bound`, `Effect.allowKept`, `allowKept_call`,
  `allowKept_seq`.
- Supply (`Supply.lean`): `Effect.supply`, `supply_call`, `supply_seq`.
- What each states: docs/RESULTS.md, section "Security properties (round 22)".
- Not done: the deprecated paths in these theorems (each single-call theorem takes `hdep`); the
  theorem that neither `KeepsInv` nor `KeepsInvAcc` implies the other.
- `lake build UsdtVerify` (incremental, after each of the five commits and after the docs):
  exit 0, 0 "error:" lines, 1374 jobs at the end; `#print axioms`: 18 new lines, each [propext,
  Classical.choice, Quot.sound]; in all 416 [propext, Classical.choice, Quot.sound], 4 [propext,
  Quot.sound], 5 [propext], 1 with none. grep of the new files for sorry, admit, axiom,
  native_decide, bv_decide, decide +native, maxHeartbeats: none. No clean rebuild in this round.

### Round 23: security properties deprecated or not (Usdt/Security/, Evm/Keeps.lean; docs/RESULTS.md "Security properties, deprecated or not")
- `Evm/Keeps.lean` (generic): `Forwarded runChild C ua X Y` (the runner ended with no error a
  message from `C` to `ua`, from caller state `X` to child end state `Y`) and `Keeps runChild C ua
  R` (every such message goes from `X` to `Y` with `R X Y`); `Keeps.fwd`, `Keeps.mono`,
  `Writes.congr_left`, `NoDec.congr_left`.
- `Security/Effect.lean`: `FwdFn` (the six forwarding selectors), `FlagFn` (and destroyBlackFunds);
  `effect_local` (`effect_call` with `hdep` weakened to "not deprecated or not `FlagFn`";
  `effect_call` is now its corollary, statement unchanged); `EffectD` (`loc`, `fwd`, `dfwd`) and
  `effect_all` (no `hdep`, no runner assumption; `h7`, `h8`); `RunOkR`, `SeqR`, `seqR_lift`, `Strs`.
- Runner assumptions, each `Keeps … R` for one relation: `KeepsSlots` (`ProtKept`), `KeepsBal`
  (`BalKept`), `KeepsListed` (`ListedNoDec`), `KeepsAllow` (`AllowKept`), `KeepsSupply`
  (`SupplyKept`). Each single-call theorem takes `byte20 (slot 10) ≠ 0 → Keeps…`.
- One call, no `hdep`: `nonOwner_call_all`, `paused_call_all`, `listed_call_all`,
  `allowKept_call_all`, `supply_call_all` (`SupplyStepD`: deprecated destroyBlackFunds sets slot
  1 to `T - d` for some word `d`, under `KeepsSupply`). Sequences: `nonOwner_seq_all`, `paused_seq_all`,
  `listed_seq_all`, `allowKept_seq_all`, `supply_seq_all` (`StrForm` of slots 7, 8 now in each
  call's predicate).
- With no runner assumption, deprecated or not: `owner_only` (the ten `onlyOwner` functions
  succeed only for the owner), `nonOwner_local` (non-owner, any function outside `FwdFn`: only
  `balances` and `allowed` slots change, `Protected` slots kept), `transfer_checks_all`,
  `transferFrom_checks_all` (not paused; sender / `_from` not blacklisted), and `effect_local`
  for the 25 functions outside `FlagFn`.
- Which functions run locally when deprecated: the 25 outside `FlagFn` (their `ok_X` take no
  flag hypothesis). Script cross-check of the bytecode (not a proof): six CALL opcodes, no
  CALLCODE/DELEGATECALL/STATICCALL; destroyBlackFunds uses balanceOf's CALL at 4891.
- An independent read-only check of the round-22 and round-23 docs against the statements found
  seven inaccuracies, now fixed: `d` in `dfwd` and `SupplyStepD` is some word (the statement does
  not tie it to the call's output); "do not read the flag" (deprecated(), upgradedAddress() and
  deprecate read slot 10) is now "do not branch on the flag"; `same` covers 17 getters, not 20;
  `Strs` was already per call in round-22 `allowKept_seq`, `supply_seq`; the `FwdFn`/`FlagFn`
  docstrings were swapped; `hkeeps` is a hypothesis of the single-call theorems only (the
  sequences carry it in `RunOkR`); `T` in Summary is slot 1 of the child's end state. Also added:
  the keccak hypotheses of the `_seq_all` theorems, `h7`/`h8` of `effect_all`, and that the
  round-22 `Effect.*` lemmas take neither `hdep` nor `StrForm`.
- Not done: a deprecated form of `transferFrom_bound` (deprecated transferFrom forwards); any
  proof of the runner assumptions for a concrete upgraded contract.
- `lake build UsdtVerify` (incremental, after each of the two code commits): exit 0, 0 "error:"
  lines, 1375 jobs; `#print axioms`: 25 new lines, each [propext, Classical.choice, Quot.sound];
  in all 441 [propext, Classical.choice, Quot.sound], 4 [propext, Quot.sound], 5 [propext], 1
  with none. grep of the changed files for sorry, admit, axiom, native_decide, bv_decide,
  decide +native, maxHeartbeats, maxRecDepth: none.

### Round 24: non-vacuity (Usdt/Sanity/, Evm/Runners.lean, Evm/Sample.lean; docs/RESULTS.md "Non-vacuity")
- `Evm/Runners.lean` (generic): `SameStore`, `stopRunner` (EthLib's `processRunner` on the
  messages to `ua` that run the one byte STOP with a target, no value and no precompile, and on
  every message to another address; it fails every other message to `ua`), `stopRunner_ok`,
  `stopRunner_keeps`, `answerRunner`, `answerRunner_keeps`, `loadWord_append_wordBytes`.
- `Evm/Sample.lean` (generic): `sState` (one account with given slots), `sMsg`, `sFrame`,
  `at_sFrame`, `data1`/`data2`/`data3` with their size, selector and word lemmas,
  `selector_append`, `loadWord_append_wordBytes_append`, `le_writeSlot`, `slotCost_le`.
- `Sanity/Runner.lean`: `keepsAll_of_same`; `stop_keeps_all` (`stopRunner` meets `KeepsSlots`,
  `KeepsBal`, `KeepsListed`, `KeepsAllow`, `KeepsSupply`, `KeepsInv`), `stop_staticKeeps` (from
  Paris); `balRunner` meets all six, `StaticKeeps` and `HonestBalance`
  (`runner_assumptions_hold`); `honestBalance_of_answers`.
- `Sanity/Transfer.lean`, `Calls.lean`, `TransferFrom.lean`: `transfer_ok_sat`,
  `transferFrom_ok_sat`, `approve_set_sat`, `issue_sat`, `redeem_sat`, `destroy_sat`. Each gives
  a call, a state and a gas where every hypothesis of the spec theorem holds, and the run under
  `processRunner` ends with no error. It holds at every fork from Berlin and for every block,
  transaction, contract address and substate. No keccak fact is used.
- `Sanity/Security.lean`: `OkRun`; `transfer_witness`, `paused_witness`, `listed_witness`,
  `inv_witness` (`inv_empty`); `nonOwner_applies`, `allowKept_supply_applies`, `paused_applies`,
  `listed_applies`, `inv_applies` apply the security theorems (single call and `_call_all`),
  `inv_call_ns` and `inv_call_all` under `KeccakSep` (and `AllowSep`), and discharge every other
  hypothesis. `transferFrom_bound_applies` (TransferFrom.lean) does the same for
  `transferFrom_bound`.
- `Sanity/Strings.lean`: `strForm_name`, `strForm_symbol`; `inv_mainnet` (under `KeccakSep`);
  `strings_applies` (`inv_call_all` and `supply_call` with "Tether USD" and "USDT" in slots 7
  and 8).
- Not done: a witness run that is deprecated (every witness has slot 10 not deprecated, so the
  runner hypotheses of the `_call_all` forms hold there only because these theorems take them
  only when deprecated); a real upgraded contract (code) shown to meet the runner assumptions;
  `KeccakSep`, `AllowSep` (statements about keccak).
- Unlike `processRunner`, `stopRunner` fails the messages to `ua` whose code is not STOP.
  `Keeps` asks its relation of every message to `ua` whatever its code, and nothing is claimed of
  `processRunner` there.
- `lake build UsdtVerify` (incremental, after each of the four code commits): exit 0, 0 "error:"
  lines. `#print axioms`: 42 new lines. 39 are [propext, Classical.choice, Quot.sound], 1
  (`selector_append`) is [propext, Quot.sound], and 2 (`strForm_name`, `strForm_symbol`) have no
  axioms. grep of the new files for sorry, admit, axiom declarations, native_decide, bv_decide,
  decide +native, maxHeartbeats, maxRecDepth: none.

### Round 25: exact success conditions (Usdt/Exact/, Usdt/Spec/Guards.lean, Evm/Iff.lean; docs/RESULTS.md "Exact success conditions")
- `Evm/Iff.lean` (generic): `RunsOk` (the interpreter loop returns a frame with no error),
  `halted_false_ok`, `runsOk_of_spec`, `runsOk_iff`, `not_runsOk_low`, `not_runsOk_low2`,
  `not_runsOk_low3`.
- `Usdt/Spec/Guards.lean`: `CallOk`, `CanWrite`, `IsOwner`, and the condition of each function
  (`PauseGuard`, `UnpauseGuard`, `OwnerWriteGuard`, `IssueGuard`, `RedeemGuard`,
  `SetParamsGuard`, `TransferOwnershipGuard`, `DestroyBlackFundsGuard`, `ApproveGuard`,
  `TransferGuard`, `TransferFromGuard`).
- `Usdt/Exact/Getters.lean`, `Owner.lean`, `Approve.lean`, `Transfer.lean`, `TransferFrom.lean`:
  `X_ok_iff` and `X_low` for the 32 functions, not deprecated where the function reads the flag
  (`hdep`). `X_ok_iff`: with the gas of the success path (the cost, and the stipend bounds the
  success spec takes), `RunsOk` holds iff the condition holds. `X_low`: below the cost, `RunsOk`
  does not hold. Each `ok_iff` comes from the completeness theorem (one direction) and the
  success spec run through `SpecG.runFrame` (the other); each `low` from the completeness theorem
  and `ok_exact`. Costs that depend on the path are `if`s: `strCost` (name, symbol),
  `ownershipCost`, `approveCost`/`approveStip`, `transferCost`/`transferStip1`/`transferStip2`,
  `transferFromCost` (with `stipCostF`).
- `Usdt/Exact/Deprecated.lean`: `X_dep_ok_iff`, `X_dep_low` for the seven forwarding paths
  (totalSupply, balanceOf, allowance, transfer, approve, transferFrom, destroyBlackFunds). Given
  the upgraded code `c` and route `r`, the gas `hg`, `htail` of the forward spec, a runner that
  never fails (`NoFail`) and ends each forwarded message with no error exactly when `A` holds
  (destroyBlackFunds: with no error and an account of the contract in its end state), `RunsOk`
  holds iff the checks before the forward (`ForwardOk`, `TransferDepGuard`, `ApproveDepGuard`,
  `TransferFromDepGuard`, `DestroyDepGuard`) and `A` hold. One direction from `dep_*_complete`
  with `routes_unique` and the uniqueness of the code found; the other from the forward spec
  under the callee assumption `AnsIff` (`fwd_ok_iff`); destroyBlackFunds under its own callee
  assumption (no error and an account of the contract), through `runsOk_of_specUnder`. `X_dep_low`: below
  the gas of `hg`, no successful run, for every runner (from `dep_*_complete`).
- `Usdt/Sanity/Exact.lean`: `answerRunner_noFail`, `answerRunner_ans`, `answerRunner_ans_acc`.
- Not covered: a gas at or above the cost but below a stipend bound (the run may fail there by
  EIP-2200; no theorem says either way); when deprecated, a gas between the bounds of `hg` and
  `htail`, and a runner that may fail.
- `lake build UsdtVerify` (incremental, after each code commit): exit 0, 0 "error:" lines.
- Independent accuracy check of the round-25 docs against the statements: nine items fixed (the
  gas hypotheses and `NoFail` named where a sentence left them out, `TransferOwnershipGuard`'s
  conditional `CanWrite`, the allowance step of transferFrom, the Sanity scope (`answerRunner`
  meets `hans` with `A = True` for the six forwards other than destroyBlackFunds), the proof route
  of deprecated destroyBlackFunds, `hszl` only in `*_dep_ok_iff`, the Iff.lean header).

### Round 26: exact gas thresholds (Evm/Stuck.lean, Evm/Iff.lean, Usdt/Exact/, Usdt/Sanity/Exact.lean; docs/RESULTS.md "Exact success conditions")
- `Evm/Stuck.lean` (generic): `sstoreStep_low`, `sstore_low_stuck` (from Istanbul, an SSTORE with
  at most 2300 gas left is `Stuck`), `NoWrite` (static, no account, or at most 2300 gas left from
  Istanbul) with `of_bad`, `of_low`, `le`, `sstoreNoWrite`; `no_ok_stuck_at` (a `Stuck` frame
  reached with the frame's own gas).
- `Evm/Iff.lean` (generic): `not_runsOk_stuck`, `of_runsOk`, `iff_max`, `fwd_ok_iffQ`,
  `fwd_ok_or_fails`.
- The `bad_*` lemmas of the writing functions other than transferFrom (and their blocks `*Bad`)
  now take `hbad : NoWrite` at the gas left at their first SSTORE and the exact gas to it (was:
  static or no account, and a looser gas bound); the completeness callers pass `.of_bad`. The
  `bad_*` lemmas of transferFrom are unchanged (its cost covers the stipends of the SSTOREs before
  the last one). New chains to a second SSTORE
  reached with at most 2300 gas left: `low_issue2`, `low_redeem2`, `low_setParams2`,
  `low_deprecate2`, `DestroySpec.low2`, `low_transfer2`, `low_transferFrom2` (blocks
  `issueTotalBad`, `redeemOwnerBad`, `write4Bad`, `subTotalBad`, `creditStoreBad`, `bodyLow2`,
  `creditStoreBadF`, `bodyLow2F`).
- `Usdt/Exact/`: `X_mid` and `X_iff_gas` for the 13 writing functions (not deprecated where they
  read the flag): `RunsOk ↔ guard ∧ max cost stip ≤ gas`, for every gas. New stipend names:
  `ownershipStip`, `transferStip`, `transferFromStip`.
- Deprecated, the six forwards other than destroyBlackFunds: `spec_dep*_g` (the bound `hcg` on the
  callee in place of `htail`; the old specs are derived), `X_dep_ok_iff_gas` (no `htail`; `hans`
  covers no error and enough gas after the CALL), `X_dep_ok_or_fails` (with `htail`; a runner that may
  fail with aborting errors; one-sided).
- `Evm/Runners.lean`: `answerRunnerAt`. `Usdt/Sanity/Exact.lean`: `answerRunnerAt_noFail`,
  `answerRunnerAt_ans_acc`, `answerRunnerAt_hans` (meets the `hans` of deprecated destroyBlackFunds
  with `A = True`), `answerRunnerAt_ans_gas`.
- Not covered: deprecated destroyBlackFunds between the bounds of `hg` and `htail` and under a
  runner that may fail; for the six forwards under a runner that may fail, only the one-sided form.
- `lake build UsdtVerify` (incremental, after each code commit): exit 0.
- Independent accuracy check of the round-26 docs against the statements: nine items fixed
  (`X_dep_ok_or_fails` keeps `htail`, so under a runner that may fail the gas between `hg` and
  `htail` stays open; `answerRunnerAt` does not keep storage; the `Stuck.lean`, `Iff.lean`,
  `Runners.lean` and Sanity headers; `answerRunnerAt_hans` needs the current target `C`;
  `answerRunnerAt_ans_gas` is stated per frame; the Summary heading; a parenthesis in LAYOUT).

### Round 26, second part: deprecated destroyBlackFunds at every gas, runners that may fail (Evm/Sends.lean, Evm/Route.lean, Evm/Iff.lean, Usdt/Spec/Deprecated/, Usdt/Exact/Deprecated.lean)
- `Usdt/Spec/Deprecated/Destroy.lean`: `tailStip` (the stipend bound of the code after the CALL:
  `2518 + (price of the write of balances[a]) + (price of the read of slot 1)`), `zeroBalNoWD`,
  `tailD_g` (the tail with `tailCost` and `tailStip` in place of `TAIL_MAX`), `tailMidD` (from
  `tailCost` to below `tailStip` an SSTORE with at most 2300 gas left is reached, `Stuck`),
  `spec_depD_g` (no `htail`, no `hkeep`; the callee assumption gives no error, the account and
  both bounds). `Complete.dep_destroy_complete` also gives `tailStip` (a new last conjunct).
- `Exact.destroyBlackFunds_dep_ok_iff_gas`: with `hg` only, `NoFail`, and `hans` (no error, an
  account of the contract, and `max tailCost tailStip` at most the gas the CALL keeps plus the
  gas left, both over the state and substate after the call), `RunsOk ↔ DestroyDepGuard ∧ A`.
- `Evm/Sends.lean` (generic): `AbortsOn`, `MeetsOk`, `HoareOn`, `SpecOn` (a runner that may fail
  with any error; the run ends in the postcondition or at a failure on a message of `S`),
  `of_hoare`, `of_child`, `seq`, `consequence`, `mono_S`, `toUnder`. `Evm/Route.lean`:
  `callWithRS` (`callWithR` derived). The seven `spec_dep*_g` are stated as `SpecOn` with
  `S = SendsVia …`. `Evm/Iff.lean`: `fwd_ok_iff_fails`. `Evm/Runners.lean`: `failRunner`.
- `Exact.X_dep_ok_iff_fails` (the seven paths): `hg` only, `hans` as in `X_dep_ok_iff_gas`, and
  `hfail` in place of `NoFail` (a failure of the runner, any error, on a forwarded message excludes
  `A`): `RunsOk ↔ checks ∧ A`. `X_dep_ok_iff_gas` derived from them. The one-sided
  `X_dep_ok_or_fails` are kept.
- `Usdt/Sanity/Exact.lean`: `answerRunnerAt_ans_gasD`, `failRunner_hans`, `failRunner_hfail`.
- `lake build UsdtVerify` (incremental, after each code commit): exit 0, 0 "error:" lines.
- Independent accuracy check of the docs of this part against the statements: five items fixed
  (`tailMidD` also needs `tailCost ≤ gas` and stops at the first SSTORE below 2485; the
  `callWithRS` wording, which said the runner may fail only on the message it sends: it may fail
  on any message, and the run ends at a failure on the forwarded one; the Summary gloss of
  `tailCost`; `answerRunnerAt_ans_gasD` needs an account of `C` in `S`).

### Round 27: code quality (no main statement weakened)
- Reachability check (a Lean script over the environment: the declarations of `Summary.lean`, the
  names of `Test/Axioms.lean` and the names in RESULTS.md as roots, closure over the constants of
  types and values): 13 unused lemmas removed (`NoDec.read_write_add`, `Gas.fails_error`,
  `Gas.rel_error`, `Gas.repcG`, `Writes.congr_left`, `Local.exp`, `wordArg_data2_0`, `restateH`,
  `Gas.hasAccount_readSlot_iff`, `TransferFee.ownerKey_eq`, `Security.same_reads`,
  `TransferOk.mkey_addrArg` of Spec/Transfer, `TransferOk.recipientSlot_addrArg`). Left unused on
  purpose: `Invariant.Steps.trans`, the `@[simp]` rfl lemmas `Gas.*_sh` and the two coercions of
  Evm/Gas.lean (a `dsimp` or coercion use leaves no constant in the proof term).
- Duplicates (a script grouping theorems by statement, up to reducible defeq): the copies over
  `StepG` in Complete/Dispatch.lean (`preludeG`, `dispatchG`, `revert406G`, `spec_unknownG`,
  `spec_shortG`, `valueRevertG`, `nonpayableG` and ten step macros) were the same statements as
  `prelude`, `dispatch` (Map.lean) and `Fallback.*`, `Nonpayable.*` (Spec/Dispatch.lean), already
  over `StepG`; `runFrame_ok_dispatch` now uses those. `mkey_addrArg` (three copies) is one lemma,
  `TransferOk.mkey_addrArg data i` in Proofs/Transfer.lean (`Admin.mkey_addrArg0` folded in);
  `Sanity.sumTo_zero` merged into `DepInv.sumTo_zero`. Left: the equal definitions `Untouched` /
  `SameStore`, `BlackList.listSlot` / `TransferFrom.blackFrom`, `TransferOk.mkey` / `BalanceOf.key`
  (main statements use them by name).
- Exact/Deprecated.lean: the six `X_dep_ok_iff` other than destroyBlackFunds are derived from
  `X_dep_ok_iff_fails` (same statements); `Exact.fwd_ok_iff` and `Exact.fwd_ok_iffQ` (Evm/Iff.lean),
  then unused, removed.
- Build warnings of our files: 56 unused simp arguments, 24 deprecated `if_pos`/`if_neg`, three
  unused binders (`valid_CODE` no longer takes `ht`, `fromExt_found` no longer takes `hfork`:
  both stronger). Only the module-system notes about EthLib imports remain.
- Names: the Summary aliases `*_depNoCode` are now `*_dep_noCode`; LAYOUT.md states the naming
  scheme. Headers: a lead sentence on what the file proves where it lacked one; stale lists fixed
  (Evm/Storage, Evm/Calldata, Proofs/Common); Evm/Call.lean titled as generic; Code/Bytes.lean has
  a header, written by `scripts/gen_code.py`. LAYOUT.md lists every file. `scripts/__pycache__`
  untracked.
- Test/Axioms.lean: one duplicate line dropped; added the six `spec_*` from pc 0 printed only
  through their `runFrame_*` form, the six helper lemmas of Summary.lean and the 40 `runFrame_*`
  of Spec/RunFrames.lean (708 entries).
- Build cost: no file is slow or large (slowest Spec/Strings 14 s, Proofs/TransferFrom 12 s, from
  lake's per-module times; whole build 1.79 GB max RSS), so no file was split.
- Lines: Lean files +362 / -633 (net -271; without Test/Axioms.lean +306 / -627, net -321).
- `lake build UsdtVerify` after each code commit: exit 0, 0 "error:" lines.
- Independent accuracy check of LAYOUT, RESULTS, STATUS and the changed headers: seven items fixed
  (the `G` suffix marks a `StepG` twin only where a `Step` form exists; Summary aliases only the
  per-function theorems; Admin's header named a `logAddr` that never existed; Common's header
  placed `MEM0`, which is in Map.lean; Sanity/Security has four witnesses, not three; Evm/Call's
  header placed `fromExt`, which is in Usdt/Complete/Deprecated/Call.lean; RESULTS placed
  `Gas.expLG` in Evm/Local/).

### Round 29: the audit findings (docs/AUDIT.md), hypotheses restated so they can hold

Finding 1 (critical): the keccak hypotheses are now local.
- Old: `KeccakSep` (and `AllowSep` for some security theorems), separation for all key words at
  once; almost certainly false (2^256 expected collisions for some fields), so every theorem that
  assumed it was, as far as anyone can tell, vacuous.
- New, in Usdt/Invariant/Supply.lean: `NotBal n` (no address word has `n` as balance slot),
  `UniqBal x` (no other address word has the balance slot of `x`), `NotFixed n`, `FixedSep`
  (slots 0..10 are no balance slot), and `SepOn A` for a list `A` of words: `FixedSep`, `UniqBal`
  of the address words of `A`, the `isBlackListed` slots keyed by `A` are no balance slot and not
  slot 1, the `allowed` slots keyed by two words of `A` are no balance slot and no fixed slot.
  `callKeys message S` = [caller, address argument 0, address argument 1, owner of `S`]. In
  Usdt/Security/Effect.lean: `NotList`, `SecSep A` (`SepOn A`, and the balance and allowance slots
  keyed by `A` are no `isBlackListed` slot of an address word). Each fact compares one given slot
  with 2^160 others (or with 11 fixed slots); under the random-function model each fails with
  probability about 2^-96.
- How each statement changed: every `K : KeccakSep` became `K : SepOn (callKeys message state)`,
  and every `K : KeccakSep` with `A : AllowSep` became `K : SecSep (callKeys message state)`, for
  the call's own message and start state. Sequences: `GoodCall` carries `SepOn (callKeys message S)`
  for its own call, so `inv_calls` and `inv_goodCall` take no keccak argument; `goodCall_process`
  and `process_step` take `K` for their message; the security sequence predicates (`NotOwnerK`,
  `NotOwnerS`, `NoAllowFn y z`, `NoAllowFnS y z`, `NoSupplyFn`, `NoSupplyFnS`) carry it per call.
  Step-level lemmas take the precise facts they use (`transferOk_inv F hus hur`, `Step`
  constructors carry `UniqBal` / `NotBal` of the slots they write; `step_inv` and `steps_inv` take
  `FixedSep`). `inv_tail_iff`, `not_inv_tail` take `FixedSep` and `UniqBal a`.
- Two conclusions were narrowed, because a global conclusion would need a global hypothesis:
  `ListSlot` (in `Protected`, so in `nonOwner_*`, `ProtKept`, `KeepsSlots`) now means a slot of
  `isBlackListed` of an address word (`y < 2^160`; it was any word); and the allowance theorems
  (`allowKept_call`, `_call_all`, `_seq`, `_seq_all`, `Effect.allowKept`, `EffectD.allowKept`)
  conclude `AllowKeptAt y z` for given words `y`, `z` under `SecSep (y :: z :: callKeys ..)`
  (they concluded `AllowKept`, every slot). `AllowKept` stays as the form of the runner
  assumption `KeepsAllow`. `OwnW` is now `OwnW message`: slots 0, 3, 4, 10 and the one
  `isBlackListed` slot of the first address argument (it was any `isBlackListed` slot).
- `exists_breaks` now takes `NotBal 1` only (was `KeccakSep`). It cannot be unconditional: if
  slot 1 were the balance slot of exactly one address word, every tail would keep `Inv` (argued).
- New lemmas: `SepOn.mono`, `SepOn.uniqCaller` / `uniqArg` / `uniqArg0` / `uniqOwner` /
  `uniqOwnerAt` / `listArg` / `allowArg` / `allowFromArg`, `storageAt_creditedFee0`,
  `storageAt_creditedFeeF0`, `storageAt_allowState_of_ne`, `nb1`, `bal_ne_zero`; Security:
  `SecSep.mono`, `sepOn_of_global` (`KeccakSep` and `AllowSep` give `SecSep A` for every `A`, so
  the old forms follow, except the narrowed `Protected`), `KeyBA` (balance and allowance slots
  keyed by a list) with `kba_*`, `writes_creditedK`, `writes_feeStateK`, `writes_creditedFK`,
  `writes_feeStateFK`, `Effect.nonOwnerK`, `fixed_not_kba`, `protected_not_kba`, `ownW_notBal`,
  `ownW_ne_one`, `not_ownW`, `SecSep.allowYZ`, `not_balOrOne`. Removed (they used the global
  hypotheses): `nb_list`, `nb_allow`, `bal_not_allow`, `bal_not_list`, `bal_not_fixed`,
  `bal_not_ownW`, `allow_not_ownW`, `allow_ne_one`, `fixed_not_ba`, `protected_not_ba`,
  `list_mk`, `KeccakSep` → `SepOn` corollary moved to `sepOn_of_global`.

Finding 2 (high): the runner assumptions are about the calls the code makes.
- Old: `KeepsInv runChild C ua`, `HonestBalance`, and `Keeps runChild C ua R` (the security
  `Keeps*`) quantified over every caller frame and message from `C` to `ua`, the code included;
  false for `processRunner` with any upgraded contract (audit, machine-checked for `ua = C`).
- New (Evm/Keeps.lean): `SameView X S` (same storage and code at every address), `SentVia message S
  ua caller msg` (the caller state has the view of `S`, and `msg` is a `SendsVia` message with the
  code `ua` holds in `S` along its route; any data, any gas), `KeepsAt`, `FwdAt`. All.lean:
  `KeepsInvAt runChild message state`, `HonestBalanceAt runChild message state`. The security
  `KeepsSlots`, `KeepsBal`, `KeepsListed`, `KeepsAllow`, `KeepsSupply` now take
  `(runChild) (message) (S)` and are `KeepsAt … (upAddr S message) R`. `EffectD.fwd`/`dfwd` carry
  `FwdAt`; `LocalForward` carries `SentVia`; `RunOkR` takes `KeepsAt`. `inv_call_ns`,
  `inv_call_all`, `GoodCall`, `goodCall_process`, `process_step`, `inv_dep_destroy(_iff)`,
  `dep_destroy_local` and every `*_call_all` / `*_seq_all` take the `At` forms. The old forms imply
  the new (`keepsInv_at`, `honest_at`, `Keeps.at`), so Sanity/Runner's runners still apply
  (`keeps*_of_same` now from `SameFor`, `KeepsAll runChild message S`).
- New, Sanity/Process.lean: `process_stop`, `processRunner_stop_keepsAt`,
  `processRunner_stop_keepsAll`, `keepsInvAt_process_stop`: from Paris, with `STOP_CODE` at the
  upgraded address (no precompile), `processRunner` meets all six `At` assumptions, in particular
  the `hkeeps` of `goodCall_process` / `process_step`. Not done: `HonestBalanceAt` for
  `processRunner` with a real code (a contract that answers the local balance would have to read
  it from `C`, e.g. through the getter `balances(address)`; not attempted).

Finding 3 (high), partly: the deprecated exact theorems.
- `Exact.NoFailOn runChild S` (Evm/Iff.lean): the runner returns a frame for every message of `S`;
  `NoFail.on`. The six `X_dep_ok_iff`, six `X_dep_ok_iff_gas` and `destroyBlackFunds_dep_ok_iff_gas`
  take `NoFailOn runChild (SendsVia message (upAddr state message) c r d)` in place of `NoFail`
  (weaker hypothesis). `destroyBlackFunds_dep_ok_iff` keeps `NoFail` (its proof goes through
  `runsOk_of_specUnder`).
- Sanity/Process.lean: `process_stop_sends`, `noFailOn_process_stop`, `hans_process_stop` (A =
  True), `totalSupply_dep_ok_iff_process_stop` (from Paris, upgraded code STOP, no precompile:
  `RunsOk` under `processRunner` iff `ForwardOk`).
- Open: `hans` of `X_dep_ok_iff_gas` / `X_dep_ok_iff_fails` asks one `A` for every gas of the
  forwarded message, and its condition reads the child's gas, so it is unsatisfiable for
  `processRunner`. It needs `callWithRS` and the seven `spec_dep*_g` to give the callee
  assumption `msg.gas`; not done.

### Round 30: audit findings 2 and 3 finished (Evm/Route.lean, Evm/Iff.lean, Evm/Mirror.lean, Usdt/Spec/Deprecated/, Usdt/Exact/Deprecated.lean, Usdt/Sanity/ProcessExact.lean, Usdt/Sanity/Mirror.lean)

Finding 3: `hans` is gas-aware.
- `Complete.CallFrom g st ss caller msg` (Evm/Route.lean): `msg.gas = g`, `caller.state = st`,
  `caller.substate = ss`; `atCallState`, `atCallSub`: the state and substate of the caller frame at
  a CALL along a route.
- The seven `spec_dep*_g` / `spec_depD_g`: `hcg` takes `CallFrom` of the CALL's gas (`callGas…`)
  and caller frame, besides `SendsVia` (`callWithRS` already gave these facts in its
  postcondition). `fwd_ok_iff_fails` takes a call condition `Cl` beside the message set `S`.
- `Exact.X_dep_ok_iff`, `X_dep_ok_iff_gas`, `X_dep_ok_iff_fails` (the seven paths): `hans` takes
  `CallFrom` too, so it is asked only of the message the CALL sends with the gas it gives, from the
  caller frame at the CALL. `A` may depend on that gas. `X_dep_ok_or_fails` keep the old `hans`.
- `destroyBlackFunds_dep_ok_iff` takes `NoFailOn` (was `NoFail`); it is now derived from
  `destroyBlackFunds_dep_ok_iff_fails` with `DeprecatedDestroy.tail_le_max` (the cost and the
  stipend bound of the tail are at most `TAIL_MAX`).
- Sanity/ProcessExact.lean (the round-29 exact part of Sanity/Process.lean moved here):
  `process_stop_child` (STOP under `processRunner`: no error, all its gas, the caller's state and
  accesses, no output), `hans_process_stop`, `hans_gas_process_stop`, `hans_destroy_process_stop`,
  `hans_destroy_gas_process_stop`, and the instances `X_dep_ok_iff_process_stop` and
  `X_dep_ok_iff_gas_process_stop` for totalSupply, balanceOf, allowance, transfer, approve,
  transferFrom and destroyBlackFunds (from Paris, upgraded code STOP, no precompile).

Finding 2: `HonestBalanceAt` for `processRunner` with a real code.
- Evm/Mirror.lean: `MIRROR` (25 bytes: store 2 at 32 and the call-data word at 4 at 0, KECCAK256
  of the 64 bytes, SLOAD, return the word). `mirror_spec`: the `SpecG` from pc 0 (cost
  `87 + slotCost`). `process_mirror`: from Paris, a message running `MIRROR` (no value, no
  precompile) under `processRunner` that ends with no error returns the word of slot
  `mapSlot k 2` of its current target in the caller's state, and ends in that state with the slot
  recorded read (any gas: `Complete.ok_exact`).
- Sanity/Mirror.lean: `honestBalanceAt_process_mirror`: from Paris, upgraded code `MIRROR`, no
  precompile, and `hmirror : storageAt S ua (balSlot message) = storageAt S C (balSlot message)`
  give `HonestBalanceAt (processRunner fork bound) message S`. `MIRROR` reads its own storage, so
  `hmirror` (for the one queried slot of the start state) is needed.
- Not done: an exact deprecated instance with `MIRROR` (gas-exact `hans` for a code whose success
  depends on its gas): it needs `NoFailOn` for `MIRROR` at every gas and its failure below its
  cost under `processRunner`; only successful runs are characterized (`ok_exact`).

### Round 31: a gas-exact deprecated instance with `MIRROR` (Evm/NoAbort.lean, Evm/Mirror.lean, Usdt/Sanity/MirrorExact.lean)

Finding 3: an instance with an upgraded code whose success depends on its gas.
- Evm/NoAbort.lean (generic): `NoAbort r` (no error that aborts the run), with `bind`/`map` and the
  facts for `popWord`, `pushWord`, `chargeGas`, `chargeGasAndMemory`, and the six instructions
  PUSH (`pushN`), MSTORE, CALLDATALOAD, KECCAK256, SLOAD, RETURN (they fail only with stack and
  gas errors). `StepGA x y`: `StepG` and, from every frame with less gas than `x`, the step is no
  aborting error. `HoareGA`, `SpecGA` (`SpecGA.toG`), `At.ruleGA`, `pushGA`, `calldataloadGA`,
  `mstoreGA`, `keccak256GA`, `sloadGA`, `returnGA`. `no_error_of_reaches`, `no_error_ga`: a `SpecGA`
  from every gas from `B` on gives, at ANY gas, a loop run that returns a frame, never an error
  (with less gas, a step either halts the frame with an error that does not abort, or follows the
  run with more gas).
- Evm/Mirror.lean: `mirror_specA` (the MIRROR spec over `StepGA`; `mirror_spec` now follows from
  it). `process_mirror_iff`: from Paris, a message running `MIRROR` (no value, no precompile,
  target `ua`) under `processRunner`, any gas, any caller frame: the runner returns a frame; it
  ends with no error iff `87 + slotCost c ≤ msg.gas` (`c`: coldness of the slot in the caller's
  substate); then its gas, output, state and substate are given. `process_mirror` is derived from
  it. `hasAccount_readSlot_iff`.
- Usdt/Sanity/MirrorExact.lean: `mirrorCost`, `route_mirror`, `process_mirror_sends` (the
  `balanceOf(a)` messages of a deprecated path), `noFailOn_process_mirror`,
  `hans_gas_process_mirror` (the `hans` of `balanceOf_dep_ok_iff_gas`, `A`: `mirrorCost ≤ g` and
  `T ≤ K + (g - mirrorCost)`), `incorporate_state`, `hans_destroy_gas_process_mirror` (the `hans` of
  `destroyBlackFunds_dep_ok_iff_gas`, `A` over the gas, state and substate at the CALL),
  `balanceOf_dep_ok_iff_gas_process_mirror` (hypothesis `hcM` names the coldness of the queried
  slot), `destroyBlackFunds_dep_ok_iff_gas_process_mirror` (hypothesis `hmirror`, as in
  `honestBalanceAt_process_mirror`; the subtracted word is USDT's `balances[a]` in the start state).
- Not done: `MIRROR` instances of the other five forwards (`MIRROR` answers `balanceOf` only), and
  one upgraded state where a useful code meets `KeepsInvAt` and `HonestBalanceAt` together.

Second audit, M1: the runner-failure hypotheses at the CALL's caller frame.
- Evm/Sends.lean: `AbortsOn`, `HoareOn`, `SpecOn`, `of_child`, `mono_S` take `S` over the caller
  frame and the message. Evm/Route.lean: `callWithRS`'s set adds the caller's state and substate
  and the message's gas. The seven deprecated `spec_dep*_g` / `spec_depD_g`: set
  `SendsVia … msg ∧ CallFrom …`.
- Evm/Iff.lean: `NoFailOn runChild S` with `S : Evm → Message → Prop`; `fwd_ok_or_fails` and
  `fwd_ok_iff_fails`: the failure comes with `Cl`, and `hfail` takes it.
- Exact/Deprecated.lean: `hnf : NoFailOn runChild (fun caller msg => SendsVia … msg ∧ CallFrom …)`,
  `hfail … → SendsVia … msg → CallFrom … → ¬ A`, and `X_dep_ok_or_fails`'s failure with
  `CallFrom`. Sanity: `noFailOn_process_stop`, `noFailOn_process_mirror` for any caller condition.

Second audit, L4 and I1: a deprecated state (Usdt/Sanity/MirrorState.lean).
- `keepsInvAt_process_mirror`, `W`, `UA`, `hnp_UA`, `exists_hash`, `S1`, `storageAt_S1`,
  `slot10_S1`, `up_S1`, `hcode_S1`, `balanceOf_mirror_sat` (Paris ≤ fork < Glamsterdam, the iff of
  `balanceOf_dep_ok_iff_gas_process_mirror` in `S1`), `process_step_dep_hyps` (flag set,
  `KeepsInvAt` and `HonestBalanceAt` together in `S1`, from Paris).

Finding 3: `X_dep_ok_or_fails` on the gas-aware `hans` (Evm/Iff.lean, Usdt/Exact/Deprecated.lean).
- `fwd_ok_or_fails` now has the hypotheses of `fwd_ok_iff_fails` without `hfail` (any errors of
  the runner; the failure in the conclusion is on a message of `S`); `fwd_ok_iff_fails` is derived
  from it. The round-26 form (under `AnsIff`, with `hab`) is removed.
- The seven `X_dep_ok_or_fails` (destroyBlackFunds is new): the hypotheses of `X_dep_ok_iff_fails`
  without `hfail` (`hg` only, `hans` with `CallFrom`); conclusion: success gives the checks and
  `A`, the checks and `A` give success or a failure of the runner on a `SendsVia` message. The
  `X_dep_ok_iff_fails` are derived from them. The old forms (with `htail`, the old `hans`, `hab`)
  follow from the new ones; they are not kept as theorems.

### Round 33: third audit T1–T5 (Evm/Route.lean, Evm/Call.lean, Usdt/Sanity/MirrorState.lean, Usdt/Invariant/All.lean, Usdt/Complete/)

T2 (third audit): the forwarded message carries the environments of the message of the path.
- Evm/Route.lean: `SendsVia` adds `msg.blockEnv = message.blockEnv`, `msg.txEnv = message.txEnv`
  and `msg.shouldTransferValue = true`, the fields EthLib's CALL (`finishCall`) gives the child.
  `callStep_child_r` concludes the three. `callWithRS` and `callWithR` give them, with
  `msg.isStatic`, in one conjunct of their postcondition. `SendsVia.env` reads the first two back.
- Evm/Call.lean: `CallEnd` carries the same conjunct.
- `SentVia` (the set of `KeepsAt`, `KeepsInvAt`, `HonestBalanceAt`) is `SendsVia` with the
  data free, so it fixes the environments too. `CallFrom` is not changed: every hypothesis that
  takes it takes `SendsVia` of the same message with it. The hypotheses `hans`, `NoFailOn`,
  `hfail`, and the failure disjunct of `X_dep_ok_or_fails` are now asked only of messages with
  the environments of `message`. No proof other than these two files changed. The STOP and
  `MIRROR` instances (Sanity/) build unchanged, since they assume `SendsVia` and use none of its
  new conjuncts.
- Still free in `SentVia`: the call data, the gas and the caller's substate (`KeepsAt` is over
  every call that the code of `C` makes from `S`, with any data and gas).

T3 (third audit): a deprecated state where destroyBlackFunds reaches the CALL
(Usdt/Sanity/MirrorState.lean).
- `SM`, `storageAt_SM`, `slotMap_cons`, `hasAccount_SM`, `hcode_SM`, `kD`, `KD`, `S2`, `mDO`
  (`destroyBlackFunds(a)` from `CALLER_A`), `addr_mDO`, `storageAt_S2`, `slot10_S2`, `up_S2`,
  `isOwner_S2`, `listed_S2`, `bal_S2`. In `S2 C H a`, `C` and `UA` have the same slots: 10
  (deprecated, upgraded address `UA`), 0 (owner `CALLER_A`), `isBlackListed[a]` 1 and
  `balances[a]` 1. The proofs split on every equality of the keccak slots with 0, 10 and each
  other, so no keccak value is computed. (Round 45: `S2` also has `_totalSupply` 1.)
- `process_step_dep_hyps2` (from Paris): the flag, `IsOwner`, `a` blacklisted, `balances[a] ≠ 0`
  at `C`, `UA` holds `MIRROR` with the same `balances[a]`, `KeepsInvAt` and `HonestBalanceAt`.
- `preCostD_le`, `destroy_gas_1M`, `destroy_mirror_runs` (Paris ≤ fork < Glamsterdam, 1000000
  gas, any substate): `RunsOk` for that call under `processRunner`, from the iff of
  `destroyBlackFunds_dep_ok_iff_gas_process_mirror`. So the run passes the checks and goes
  through the CALL.
- Not proved: `Inv` in `S2` (it needs keccak separation facts about the balance slots). Round 45:
  proved under `SepOn [kD a]` after `_totalSupply` 1 was added to `S2` (`inv_S2`).

T4 (third audit): `keepsInvAt_of_acc` (Usdt/Invariant/All.lean): `KeepsInvAcc` and
`KeepsInvNoAcc` give `KeepsInvAt` (through `keepsInv_of_acc` and `keepsInv_at`). `KeepsInvAcc`
alone does not give it: `SameView` fixes only storage and code, so `SentVia` allows a caller state
where `C` has no account, and `KeepsInvAcc` says nothing there (argued; no counterexample is
proved, since breaking `Inv` needs a keccak fact such as `NotBal 1`).

T5 (third audit): the gas of the completeness theorems not deprecated, with its bound.
- Usdt/Complete/Read.lean, Getters.lean, Owner.lean, Approve.lean, Transfer.lean,
  TransferFrom.lean: every `ok_X` concludes `(cost ≤ gas ∧ s.gas = gas - cost)` in place of
  `s.gas = gas - cost`, one conjunct at the same place, so no caller changed. The bound is the
  first component of `ok_exact` / `ok_exact2` / `ok_exact3`, which the proofs used to drop.
  The deprecated `dep_*_complete` already concluded their gas bound.

T1 (third audit): the EIP-8037 meter. Investigated, not done. Every statement stays about EthLib's
one-counter meter `Nat`.
- What EthLib runs. `processTransaction` (Transactions/Process.lean:435) runs
  `runTransaction StateGasMeter` from Glamsterdam and `runTransaction Nat` before. The
  `GasMeter Nat` instance (Evm/Machine/Frame.lean:129) takes state gas from the one counter,
  ignores refills (`refill gas _ := gas`), and has no reservoir. `StateGasMeter`
  (Evm/Gas/StateGas.lean) takes state gas from the reservoir first and the rest from execution
  gas, which it records as spill. A refill credits execution gas up to the spill and the rest to
  the reservoir. A revert or halt restores the spill and the baseline reservoir. A CALL passes on
  the whole reservoir.
- Why the statements do not carry over. (1) EthLib's symbolic logic is fixed to `Nat`. `At`
  (Proofs/Evm/Logic/Symbolic.lean:108) takes `evm : Evm fork Nat`, and its opcode rules (`stop`,
  `sstore`, `gas_rule`, `extcodesize`, the NatCode automation) are stated over it. Only the
  `Triple`/`Hoare`/`Spec` layer and the `instruction_*` lemmas are generic in the meter.
  (2) This repository is built on that logic. 68 files mention `Evm fork Nat`. That includes the
  gas framework of Evm/Gas.lean and Evm/GasRules.lean (`StepG`, `HoareG`, `SpecG`, on which
  `X_low`, `X_mid` and `X_iff_gas` rest) and the path specifications (about 20,000 lines in
  Usdt/Spec and Usdt/Proofs). (3) The statements change form. SSTORE's state gas for a new slot
  (`STORAGE_SET_STATE_GAS`, 64 × 1530) comes from the reservoir first. The 2300 check of
  EIP-2200 reads only the execution gas. A write that puts a new slot back to 0 refills, which
  the `Nat` meter ignores. So `X_iff_gas` for a writing function becomes a condition on two
  quantities (execution gas and reservoir), and the gas left differs when a refill happens.
  `Gas.writeMax` and the 2300 bound of `sstore_low_stuck` would be restated per pool.
- A route, not taken. `allocateGas` (Transactions/Settlement.lean:145) gives the top frame a
  reservoir of 0 when the transaction's gas limit is at most `TX_MAX_GAS_LIMIT` (2^24). In a frame
  with reservoir 0 that makes no CALL, `StateGasMeter` charges execution and state gas exactly as
  the `Nat` meter does on its execution gas. The two differ only on refills, and on reverts and
  halts, which are failures. A simulation lemma between `step` over `Evm fork StateGasMeter`
  (reservoir 0, no refill) and `step` over `Evm fork Nat` would carry `ok_X` and the
  non-deprecated part of `inv_call` over to such runs. EthLib has no parametricity theorem for
  its meter-generic `step`, so that lemma needs a case analysis of every opcode the code reaches.
  A linear disassembly of `CODE` shows 60 distinct bytes, counting each PUSH, DUP and SWAP width
  and the metadata at the end. The case analysis must also exclude the refill paths, where a slot set earlier
  in the transaction goes back to 0. The converse direction of `X_iff_gas` (enough gas gives
  success) and the deprecated paths (their CALL passes on the reservoir, and GAS pushes only the
  execution gas) need more. This is more than one round of work, so no part of it is in the
  repository.

### Round 34: the EIP-8037 meter through a simulation lemma (Evm/Gas.lean, Evm/Meter.lean, Usdt/Meter.lean, Usdt/Complete/)

T1 (third audit), the route of round 33, in part.
- `simulated : Op → Bool`: STOP, ADD, MUL, SUB, DIV, EXP, LT, GT, EQ, ISZERO, AND, OR, NOT,
  KECCAK256, CALLER, CALLVALUE, CALLDATALOAD, CALLDATASIZE, POP, MLOAD, MSTORE, SLOAD, SSTORE, JUMP,
  JUMPI, JUMPDEST, PUSHn, DUPn, SWAPn, LOGn, RETURN, REVERT: the opcodes that have a rule over
  `StepG`. The other bytes of `CODE` are CALL, EXTCODESIZE, GAS (deprecated paths only), INVALID
  (0xfe, no opcode) and 0x47 in the metadata. `SimAt x`: the opcode at `x`, if any, is
  `simulated` with an instruction. `GasMono` and `Stuck` include `SimAt`. `gasMono_of_run`,
  `At.ruleG`, `At.ruleGA`, `binaryG`, `unaryG`, `push_of_readFrameG` take `hsim` with a default
  (`decide` or `rfl`), so no rule call changed.
- `Ends fork l s` (Evm/Gas.lean) with `Ends.run`, `Ends.stopped`, `Ends.next`, `Ends.error`,
  `SimAt.not_child`. The `E` forms `low_of_reachesE`, `SpecG.lowE`, `SpecG.haltedE`,
  `SpecG.not_okE`, `not_ok_of_reachesE`, `no_ok_stuckE`, `no_ok_stuck_atE`, `ok_exactE`,
  `ok_exact2E`, `ok_exact3E`, `no_okE`, `no_ok2E`. The `runFrame` forms stay, proved from them.
- Usdt/Complete/Read, Getters, Owner, Approve, Transfer, TransferFrom and Usdt/Invariant/Calls:
  every `ok_X`, `inv_X` and `inv_call` takes `(hrun : Ends fork evm s)` in place of `within` and
  the `runFrame` equation. Conclusions unchanged. `ends_ok_dispatch` is the `Ends` form, and
  `runFrame_ok_dispatch` is proved from it. Callers (Exact/, Security/, Invariant/All, Seq,
  Sanity/Strings) pass `Ends.run hrun`.
- Evm/Meter.lean: `toNat`, `lift`; `Lifts` and `lifts_*` for the instructions of `simulated` other
  than SSTORE (they charge only execution gas, so the meter `g` passes through); `Corr`,
  `NoRefill`, `chargeStateGas_lift` (reservoir 0: the state gas comes from the execution gas and
  goes to the spill), `sim_sstoreStep`; `sim_of_simulated`; `NoRefillAt`, `CorrS`, `step_sim`;
  `ends_of_sgm`; `allocateGas_reservoir`.
- Usdt/Meter.lean: `inv_call_sgm`, `ok_transfer_sgm`, `ok_approve_sgm`, `ok_transferFrom_sgm`.
  Their gas conclusion is about `s.gas.gasLeft`, the execution gas left.
- Not done: a proof of `hnr` for any path (each needs the writes of the path: a slot whose
  original value is 0 and which is not 0 when the SSTORE writes 0); the deprecated paths; the
  converse direction of `X_iff_gas` under `StateGasMeter` (it needs the step of the meter `Nat`
  carried to `StateGasMeter`, which `step_sim` gives, and a runner-free run, not written);
  `process_step` and `goodCall_process` over `processMessage` at `StateGasMeter`.

### Round 35: refills located, the converse over the EIP-8037 meter (Evm/Refill.lean, Evm/Shadow.lean, Usdt/Refill/, Usdt/MeterIff.lean)

T1 (third audit), continued.
- Evm/Refill.lean: `NoRefillN`, `NoRefillAtN` (the Nat forms of `NoRefill`, `NoRefillAt`);
  `sstoreStep_cases`, `instr_same`, `step_store` (a step from a `SimAt` frame keeps the original
  words, does not raise the gas, and changes a word only as its SSTORE, paying its state gas);
  `create_gas`, `step_create`, `create2_gas` (turning one or two words that were 0 before the
  transaction into words that are not 0 pays 97,920 each); `noRefill_cheap`, `noRefill_one`;
  `StepI`, `HoareI`, `HoareG.toI`, `HoareG.toIA`, `SpecG.toIA`, `HoareG.toIW`, `HoareG.toI_lt`,
  `At.ruleI`, `sstoreWI`; `noRefill_low`, `noRefill_run`; `ends_of_sgmN`; `sgm_of_reaches`.
- Evm/Shadow.lean: `SstoreOk`, `sstoreAfter`, `sstoreOk_of_step`, `sstoreStep_of_ok` (for any
  meter, from Berlin); `runMono_of_simulated`, `lifts_of_simulated`; `budget`, `shadow_step`,
  `shadow_run`; `RunsOkS`, `shadow_ends`, `runFrame_of_specI`, `ends_of_specI`.
- Usdt/Refill/Approve.lean: `storeI`, `suffixAI`, `spec_zeroI` (with `hnr`), `spec_setI` (no
  hypothesis: a write of a word other than 0 never refills, `refill_of_ne`).
- Usdt/Refill/Transfer.lean: `bodyI`, `spec_okI` (fee 0, with `hnrD`); `refill_add` (the credit
  never refills); the tactics `cheap`, `same_store`, `stepC`.
- Usdt/MeterIff.lean: `ok_approve_any`, `ok_transfer_any`, `ok_transferFrom_any` (any reservoir);
  `approve_specI`, `approve_ok_sgm`, `approve_iff_gas_sgm`; `stip1_le_stip2`, `transfer_specI`,
  `transfer_ok_sgm`, `transfer_iff_gas_sgm` (reservoir 0, fee 0).
- Not done: the fee path of transfer (`bodyFee`, `feeHead`, `ownerPart`) and transferFrom over
  `StepI`, so their exact forms; `process_step` / `goodCall_process` over `StateGasMeter`; the gas
  of a run with a reservoir other than 0.

### Round 36: every writing function over the EIP-8037 meter, the gas at any reservoir, process_step (Evm/Refill.lean, Evm/Shadow.lean, Evm/ProcessMeter.lean, Usdt/Refill/, Usdt/MeterIff.lean, Usdt/MeterOwner.lean, Usdt/MeterGas.lean, Usdt/Invariant/SeqMeter.lean)

T1 (third audit), continued.
- Evm/Refill.lean: `HoareG.toIW'` (one write over a state that reads as the start; `toIW` is now
  its instance), `HoareG.toI1` (any stretch whose ends differ at one word, through
  `noRefill_one`), `SpecG.toIW'`, `SpecG.toIS` (a whole path to a halt), `getStorage_writeSlot_ne`,
  `writeCost_le_of_no_create`, `writeCost_le_max`, `exponentBytes_le`.
- Usdt/Refill/Fee.lean: transfer with a fee above 0 over `StepI` (`feeHeadI`, `ownerPartI`,
  `bodyFeeI`, `spec_feeI`). The credit and the owner's credit add without overflow
  (`refill_add`); the debit keeps `hnrD`. `transfer_specI`, `transfer_ok_sgm`,
  `transfer_iff_gas_sgm` no longer take `hfee`.
- Usdt/Refill/TransferFrom.lean: `allowStepI` (the allowance write only when `A ≠ MAX_UINT`,
  `hnrA`), `bodyFI`, `spec_okFI`, `headFI`, `ownerPartFI`, `bodyFeeFI`, `spec_feeFI`.
  Usdt/MeterIff.lean: `transferFrom_specI`, `transferFrom_ok_sgm`, `transferFrom_iff_gas_sgm`
  (`hnrA`, `hnrD`; `balances[_from]` is read after the allowance step, as in `TransferFromGuard`).
- Evm/Shadow.lean: `simAt_low`, `runFrame_of_reachesN`, `runsOk_of_specI`: a run over
  `StateGasMeter` with no error, together with a triple over `StepI` from a frame with more gas,
  gives a run of the meter `Nat` with no error from `toNat m`, for any runner. The converse of
  each `X_iff_gas_sgm` of round 36 uses it with the Nat `X_iff_gas`.
- Usdt/MeterOwner.lean: `X_specI`, `X_ok_sgm`, `X_iff_gas_sgm` for pause, unpause, addBlackList,
  removeBlackList, deprecate, transferOwnership (through `SpecG.toIW'` / `SpecG.toIS` on the
  whole path), issue, redeem, setParams, destroyBlackFunds (Usdt/Refill/Owner.lean: split at the
  point between the two writes). Refill hypotheses: none for pause, addBlackList, deprecate,
  transferOwnership (every word written is proved not 0: `withPaused_one_ne`, `setLow_one_ne`,
  `depWord_ne`, `withAddr_ne`); `hnr` for unpause and removeBlackList; `hnrT` for issue (the
  owner's credit adds without overflow; `_totalSupply` is read after it, and the two slots may
  be the same); `hnrT`, `hnrO` for redeem; `hnr3`, `hnr4` for setParams; `hnrB`, `hnrT` for
  destroyBlackFunds.
- Evm/Shadow.lean: `shadow_step` also states `n'.gas + Q m ≤ n.gas + Q m'` (`Q` = execution gas
  left + reservoir), with equality when the frame refills nothing; `shadow_runQ` carries it over a
  run; `gas_ge_any` (a lower bound from a triple over `StepG`, refills allowed) and `gas_eq_any`
  (the equality from a triple over `StepI`). Usdt/MeterGas.lean: `X_gas_any` for the 13 writing
  functions, any reservoir: `s.gas.gasLeft + s.gas.reservoir + cost = gas + m.gas.reservoir`.
- Evm/ProcessMeter.lean: EthLib's `processMessage_map_val` and `processMessage_map_val_value`
  restated for any lawful meter, with the same proofs; `at_startFrameS`.
  Usdt/Invariant/SeqMeter.lean: `inv_call_any` (any reservoir, refills allowed, through
  `shadow_ends`), `GoodCallS`, `CallsS`, `inv_callsS`, `goodCall_processS`,
  `process_value_failsS`, `process_stepS` (from Paris, not deprecated). The bound of 2^24 on the
  gas of the transaction (`allocateGas_reservoir`) is not needed for them.
- Not done: the deprecated paths over `StateGasMeter`; the split of the gas at the end between the
  execution gas left and the reservoir at a reservoir other than 0; the gas of a run with a
  refill (only `gas_ge_any`); the security properties over `StateGasMeter`.

### Round 37: the security properties over the EIP-8037 meter (Usdt/Security/)

T1 (third audit), continued.
- Usdt/Security/Effect.lean: `effect_localE` (`effect_local` for a loop that ends, `Gas.Ends`;
  `effect_local` is proved from it); `ends_any` (a run over `StateGasMeter` with no error, any
  reservoir, gives a fresh frame of `CODE` of the meter `Nat` whose loop `Ends` with no error in the
  same state, through `Shadow.shadow_ends`); `effect_local_any`, `effect_any`. `RunOkS` (a call
  over `StateGasMeter`), `RunEff`, `RunOk.eff`, `RunOkS.eff`, `SeqS` (steps `RunOk`, `RunOkS`,
  `Untouched`), `Seq.toS`, `seqS_lift`.
- Single calls over `StateGasMeter`, any gas bound, message runner and reservoir, refills allowed,
  not deprecated: `nonOwner_call_any`, `paused_call_any`, `listed_call_any`,
  `allowKept_call_any`, `supply_call_any`, `transferFrom_bound_any` (through
  `transferFrom_boundE`), `owner_only_any` (through `owner_onlyE`) and `nonOwner_local_any`
  (deprecated or not, except deprecated destroyBlackFunds, whose path makes a CALL).
- Sequences: `nonOwner_seqS`, `paused_seqS`, `listed_seqS`, `allowKept_seqS`, `supply_seqS` over
  `SeqS`, with the hypotheses of the `Seq` forms; `nonOwner_seq` and the other `Seq` forms are
  proved from them. Usdt/Security/Meter.lean: `runOkS_process`, `process_stepSec` (from Paris, a
  top-level message with code `CODE` that `processMessage` ends over `StateGasMeter` is a `RunOkS`
  step or an `Untouched` step).
- Evm/CallMeter.lean (CALL over `StateGasMeter`): `callStep_child_rS` (`callStep_child_r` for a
  frame over `StateGasMeter`: the same execution gas paid, the message carries the reservoir of
  the frame, the caller keeps a reservoir of 0 and the other fields of its meter); `resumeCall_sgm`
  (the caller resumed from a child over `StateGasMeter` has the fields of the resume over `Nat`
  from the `toNat` frames but the gas; over `Nat` the gas left is the caller's plus the child's,
  over `StateGasMeter` the execution gas left and the reservoir add up to those of the caller and
  the child); `lifts_gasStep`, `lifts_extcodesizeStep` (GAS and EXTCODESIZE are `Lifts` of their
  instruction over `Nat`).
- Not done: the deprecated paths over `StateGasMeter` (and so the `_all` security theorems over
  it). The route from here: the deprecated paths also run EXTCODESIZE and GAS, which are not
  `simulated` (their instructions are `Lifts`, but `step_sim` and `SimAt` do not include them). GAS pushes the execution gas left, so the shadow run of `shadow_ends` (more gas)
  does not carry them. At reservoir 0 with no refill (`step_sim`), EXTCODESIZE and GAS charge only
  execution gas, and the CALL sends the message of the meter `Nat` with reservoir 0
  (`callStep_child_rS`). The runner assumptions would then be stated of the runner over
  `StateGasMeter` (a `KeepsAt` form for it). The split of the gas at the end, and the gas of a run
  with a refill, are not done either.

### Round 38: one step at EXTCODESIZE, GAS and CALL over the EIP-8037 meter (Evm/CallSim.lean, Evm/StepSim.lean)

T1 (third audit), continued. Item 1 of the plan of round 37, at the level of one step.
- Evm/CallSim.lean, from a frame of `StateGasMeter` with reservoir 0, CALL with no value along a
  route: `callStep_child_sim` (below the greatest depth, with the gas: both meters send the same
  message, the caller over `Nat` is the `toNat` of the caller over `StateGasMeter`, whose
  reservoir is 0, both resume through `resumeCall`); `callStep_deep_sim` (at the greatest depth:
  corresponding next frames, reservoir 0). For any reservoir: `callStep_low_rS`,
  `callStep_missingS` (`StepBadS`).
- Evm/StepSim.lean: `SimAtX`, `step_simX` (`step_sim` at EXTCODESIZE and GAS too), `CallX`,
  `CallCorr`, `routes_or_missing`, `step_callX` (every CALL frame with value 0 and code found).
- Not done: items 2 to 4 (the deprecated cases of `inv_call_any` and `process_stepS`, the
  `dep_*_complete` theorems and the deprecated security properties over `StateGasMeter`). The
  route is in the round 38 handoff notes: a predicate on runs of the meter `Nat` with an abstract
  relation for the child and an exit at frames the simulation does not cover, the `dep_*` proofs
  restated over it, and a bridge from a run over `StateGasMeter` at reservoir 0.

### Round 39: the deprecated paths over the EIP-8037 meter (Evm/RunC.lean, Evm/RunCS.lean)

T1 (third audit), continued. Items 2 to 4 of the plan of round 38.
- Evm/RunC.lean: `Fwd` (a `SimAtX` frame where an SSTORE refills nothing, or a CALL with value 0
  and code found), `RunC fork Run l s` (a run of the meter `Nat` with an abstract relation `Run`
  for the child, an exit at frames that are not `Fwd`, an `Ends` after the CALL, and any end with
  an error), `RunN` (the relation of a runner over `Nat`), `EndsOk`. `RunC.of_runFrame` and
  `EndsOk.of_runFrame`: every end of the loop over `Nat` gives them. Lemmas over `RunC`:
  `RunC.stopped`, `RunC.next_of`, `RunC.not_bad`, `low_to_runningC`, `ok_splitC`, `ok_splitCA`,
  `no_okC`, `RunC.extcodesize`, `RunC.gasOp`, `call_okC` (`CallEndC`), `EndsOk.no_ok`.
- Evm/Refill.lean: `noRefill_cheapE`, `HoareG.toIE` (a stretch that ends in a revert with gas
  left refills nothing). `sstoreStep_cases` and `step_sstore` are strengthened: their halt branch
  also states that the gas is 0.
- Evm/RunCS.lean: `RunS` (the relation of a runner over `StateGasMeter`, with the child gas
  free), `resumeCall_withGas`, `runC_of_sgm` (from Berlin and reservoir 0, a run over
  `StateGasMeter` that ends with no error gives `RunC` with `RunS` from the `toNat` frame to the
  fields of the end with some gas: step by step up to the CALL, then `Shadow.shadow_run`),
  `endsOk_of_sgm`.
- Usdt/Complete/Deprecated/: `fromExt_foundC`, `fromExtC`, `EndsOk.dispatch`, and
  `dep_X_completeC` for the seven deprecated functions. The seven `dep_X_complete` keep their
  statements and are now proved from `dep_X_completeC`.
- Usdt/Complete/Deprecated/Meter.lean: `dep_X_completeS` for the seven, for a run over
  `StateGasMeter` from reservoir 0, any gas bound and runner. The conclusion is the one over
  `Nat` without the facts on the gas after the CALL (for destroyBlackFunds also without
  `tailCost` and `tailStip`). `incorporateChild_toNat`.
- Usdt/Invariant/DepMeter.lean: `KeepsInvAtC`, `HonestBalanceAtC`, `LocalForwardC`,
  `dep_X_localC`, `inv_dep_destroyC`; `KeepsInvAtS`, `HonestBalanceAtS` (the runner assumptions
  for a runner over `StateGasMeter`); `inv_call_depS` (deprecated, reservoir 0),
  `inv_call_anyD` (deprecated or not), `GoodCallDS`, `CallsDS`, `inv_callsDS`, `process_stepDS`
  (from Paris, deprecated, `message.reservoir = 0`), `process_stepSD` (every case).
- Usdt/Security/DepMeter.lean: `FwdAtS`, `KeepsAtS`, `EffectDF`, `effect_allS` (deprecated or not,
  reservoir 0 when deprecated), and `paused_call_allS`, `nonOwner_call_allS`, `listed_call_allS`,
  `allowKept_call_allS`, `supply_call_allS` with the runner assumptions stated by `KeepsAtS`.
- Not done: the deprecated paths over `StateGasMeter` from a reservoir other than 0; the gas left
  after the CALL over `StateGasMeter`; deprecated sequence forms (`_seq_all`) of the security
  properties over `StateGasMeter`; `owner_only` for deprecated destroyBlackFunds over
  `StateGasMeter`.

### Round 41: the fourth audit (USDT-40), findings U1 to U3

- U1. `goodCall_processS`, `process_value_failsS`, `process_stepS`, `process_stepDS`,
  `process_stepSD`, `runOkS_process` and `process_stepSec` take any starting meter of
  `processMessage` (`meter`, `held`), as `processMessageCall` passes the meter left by the
  authorizations. The deprecated forms take `meter.reservoir = 0`. The old statements are the
  `_start` corollaries. `processMessage_map_valM`, `processMessage_map_val_valueM` and
  `at_startFrameS` (Evm/ProcessMeter.lean) take the starting meter.
- U3. `callStep_child_res0` (Evm/CallMeter.lean): the CALL from reservoir 0 sends reservoir 0 and
  leaves the caller with reservoir 0. `CallCorr`, `RunS`, `FwdAtS` and the seven
  `dep_X_completeS` carry both facts, and `KeepsInvAtS`, `HonestBalanceAtS` and `KeepsAtS` ask
  their property only of calls from a caller and with a message of reservoir 0.
- U2. Usdt/Sanity/ProcessMeter.lean: `step_stopS`, `process_stopS`, `sentVia_process_stopS`,
  `keepsInvAtS_process_stop`, `keepsAtS_process_stop` (from Paris, `processRunnerM` over
  `StateGasMeter` meets `KeepsInvAtS` and `KeepsAtS … R` for every reflexive `R` when the upgraded
  address holds STOP), `process_mirrorS` and `honestBalanceAtS_process_mirror` (`HonestBalanceAtS`
  when it holds `MIRROR` mirroring USDT's `balances[a]`). Not shown: a concrete deprecated state
  over `StateGasMeter` with a run of USDT that ends with no error.
- Open items of round 39. Usdt/Security/SeqDepMeter.lean: `RunOkRS` (a call over `StateGasMeter`,
  reservoir 0 and `KeepsAtS … R` when deprecated), `SeqRS` (steps `RunOkR`, `RunOkRS`,
  `Untouched`), `SeqR.toRS`, `seqRS_lift`, `EffectD.toF`, and `nonOwner_seq_allS`,
  `paused_seq_allS`, `listed_seq_allS`, `allowKept_seq_allS`, `supply_seq_allS` with the
  predicates and runner relations of the `_seq_all` forms. `runOkRS_process`, `process_stepSecD`:
  from Paris, a top-level message over `StateGasMeter` from any starting meter (reservoir 0 when
  deprecated) is a `RunOkRS` or an `Untouched` step. Usdt/Security/DepMeter.lean:
  `owner_only_allS` (`owner_only` over `StateGasMeter`, reservoir 0 for deprecated
  destroyBlackFunds).

### Round 42: any reservoir when deprecated, the gas after the CALL, refills (Evm/NoState.lean, Evm/StepSimR.lean, Evm/RunCR.lean, Evm/Dom.lean, Usdt/Complete/Deprecated/MeterR.lean, Usdt/Exact/)

T1 (third audit), the two items left open in round 41, and the refill cases.
- Evm/NoState.lean: `NoStateN`, `NoStateAtN` (an SSTORE that charges no state gas),
  `noState_cheapE` (a cheap stretch charges no state gas: the charge alone is 97,920), `StepJ`,
  `HoareJ`, `HoareG.toJE`, `HoareG.toJA`, `SpecG.toJA`. `Fwd` now also asks `NoStateAtN`, and
  `low_to_runningC`, `HoareJ.lowC`, `ok_splitC`, `ok_splitCA`, `no_okC` go over `StepJ`. No
  statement text changed for this, and `RunC` now exits at more frames.
- Evm/CallSim.lean: `callStep_child_simR`, `callStep_deep_simR` (CALL over both meters at any
  reservoir: the message over `StateGasMeter` is the message over `Nat` with the reservoir of the
  frame). Evm/StepSimR.lean: `CorrR`, `sim_sstoreStepR`, `sim_of_simulatedR`, `step_simXR` (one
  step at any reservoir, for a frame whose SSTORE neither refills nor charges state gas),
  `CallCorrR`, `step_callXR`.
- `RunC` has a third parameter `Tail`, a predicate on the frame after the CALL, carried by
  `CallEndC`. The seven `dep_X_completeC` conclude `∃ after, Tail after`, and for the six paths
  other than destroyBlackFunds also that no running frame the run from `after` reaches refills
  (`noRefill_of_specA`). The Nat theorems `dep_X_complete` and the round 39 `dep_X_completeS`
  keep their statements.
- Evm/RunCR.lean: `RunSR`, `TailQ`, `runC_of_sgmR`: from Berlin, a run over `StateGasMeter` from
  any meter gives `RunC`, step for step while the frames are `Fwd` (the `dep_X_completeC` show
  that the path stays `Fwd` up to the CALL), and after the CALL the gas `G` of the end over `Nat` is
  at most the execution gas left plus the reservoir of the end plus a constant `E`, with equality
  when no frame of the tail refills.
- Usdt/Complete/Deprecated/MeterR.lean: `dep_X_completeR` for the seven deprecated functions, any
  reservoir, any gas bound and runner over `StateGasMeter`. The message the runner ran carries the
  reservoir of the first frame. For six paths, the execution gas left plus the reservoir at the
  end plus the gas of the tail is the execution gas left of the first frame less the path to the
  CALL and its price, plus the execution gas
  left and the reservoir of the child. For destroyBlackFunds that is a lower bound.
- Evm/Dom.lean: `sgm_charges_dom`, `dom_step`, `dom_run`, `runsOkS_of_specG` (a `StepG` run of the
  meter `Nat` is followed over `StateGasMeter` from a frame with the same fields and at least the
  gas, at any reservoir, refills allowed, with at least the gas at each step). Usdt/Exact/:
  `X_ok_dom` for the 13 writing functions: under the guard and the one-counter threshold of
  `X_ok_iff`, met by the execution gas left of the first frame alone (the reservoir not counted),
  the run over `StateGasMeter` at any reservoir ends with no error, with no refill hypothesis.
- Item 2 of round 41 (is a reservoir other than 0 impossible to state because of GAS before the
  CALL?): no. No step before the CALL charges state gas, so the execution gas left follows the gas
  of the meter `Nat` exactly at any reservoir, and GAS pushes the same word on both.
- The exact gas and success condition with refills, approve (Evm/SgmSplit.lean, Evm/SstoreS.lean,
  Evm/OneWrite.lean, Usdt/Refill/ApproveS.lean). Over `StateGasMeter` an SSTORE is the SSTORE of
  the meter `Nat` from the same frame with `sstoreBump g A S` more gas: the refill `A` credits the
  execution gas up to the spill and the reservoir with the rest, and the state gas `S` comes from
  the reservoir first (`sstoreS_of_cond`, `cond_of_sstoreS`). `one_write_sgm`: for a path with one
  write between two cheap stretches (`P` before, `T` after), from any meter, the run ends with no
  error if and only if `P + 2301 ≤ gas` and `P + writeCost + T ≤ gas + sstoreBump m.gas A S`, and
  every run that ends with no error has `gasLeft + P + writeCost + T = gas + bump` and the meter
  `sstoreMeter m.gas A c S` for the reservoir and the spill (`one_write_end`). `approve_zero_sgm`
  and `approve_set_sgm` apply it to approve, with no refill hypothesis and at any reservoir: `A` is
  97,920 when approve writes 0 over an allowance that was 0 at the start of the transaction and is
  not 0 now, and `S` is 97,920 when it writes a word other than 0 into such a slot.
- (Closed in round 43, see below.) Still not covered with refills: the exact condition and gas of transfer, transferFrom and the ten
  owner functions. For the six owner functions with one write the path has the shape of
  `one_write_sgm`, but the instances are not written. transfer, transferFrom, issue, redeem,
  setParams and destroyBlackFunds write two or three slots, and a refill of one write can pay the
  state gas of a later one, which needs `one_write_sgm` extended to a chain of writes.
- Not done (the first item closed in round 43): the exact threshold and gas with refills for the
  writing functions other than approve (`X_iff_gas_sgm`, `X_gas_any` keep `hnrD`, `hnrA` and the owner forms); the invariant and
  the security properties over `StateGasMeter` from a reservoir other than 0 when deprecated; equality
  of the gas for deprecated destroyBlackFunds over `StateGasMeter`; the split of the gas after the
  CALL; a concrete deprecated state over `StateGasMeter` with a run of USDT that ends with no error.

### Round 43: the exact gas and success condition with refills for every writing function (Evm/Chain.lean, Usdt/Refill/OwnerS.lean, ChainOwner.lean, ChainTransfer.lean, ChainFee.lean, TransferFromS.lean) (READY)

READY for the scope stated in this entry: clean rebuild of 95aa5ad from an empty build directory,
exit 0, 1440 jobs, 3:43 wall; independent read-only review (round 43): PASS WITH FIXES, fixes
applied in 7f29631 (the substate in the approve conclusions, docstrings, `#print axioms` of the path
pieces). The trust assumptions of "What is trusted" in docs/RESULTS.md are unchanged.

T1 (third audit), the item left open in round 42: the exact threshold and gas with refills for
the writing functions other than approve.
- Evm/Chain.lean: `ExactS`, `ExactS.run`, `exactS_halt`, `exactS_write`, `wOk`, `wMeter`, `wBump`,
  `wSgm`, `wMeter_gasLeft`, `getStorage_readSlot`. A path of cheap stretches (below 97,920 gas, no
  write) separated by SSTOREs is exact over `StateGasMeter` from any meter: the run ends with no
  error if and only if, at each write, `P + 2301 ≤ gasLeft` and `P + writeCost ≤ gasLeft + wBump`
  from the meter left by the previous write (`wMeter`), and the tail fits in the last meter. A
  refill of one write goes to the reservoir and the spill of the next meter, so it can pay the
  state gas of a later write.
- Usdt/Refill/OwnerS.lean (one write, through `one_write_sgm`): `pause_sgm`, `unpause_sgm`,
  `addBlackList_sgm`, `removeBlackList_sgm` (`list_sgm`), `transferOwnership_sgm`, with the paths
  split at the SSTORE (`pausePre`, `unpausePre`, `listPre`, `ownPre` and the stretches after).
- Usdt/Refill/ChainOwner.lean (two writes): `deprecate_sgm` (slot 10 twice), `issue_sgm`,
  `redeem_sgm`, `setParams_sgm`, `destroyBlackFunds_sgm`.
- Usdt/Refill/ChainTransfer.lean, ChainFee.lean: `transfer_sgm` (fee 0, two writes),
  `transferFee_sgm` (fee above 0, three writes).
- Usdt/Refill/TransferFromS.lean: `transferFrom_max_sgm` (fee 0, allowance MAX_UINT: `balances[f]`, `balances[t]`), `transferFrom_sgm` (fee 0, allowance not MAX_UINT with `v ≤ A`: the allowance, then the two balances), `transferFromFee_max_sgm` (fee above 0, MAX_UINT: three writes, the owner's balance last), `transferFromFee_sgm` (fee above 0, not MAX_UINT: four writes).
- Each theorem: from Berlin, from a frame with any meter whose `toNat` is the fresh frame of
  `CODE`, for any gas bound and message runner, under the hypotheses of the Nat success
  specification other than the gas, with no hypothesis on refills or on the reservoir: success if
  and only if the chain condition, and every successful run ends as the Nat specification says,
  with `gasLeft + cost = gas + the bumps` and the meter after the last write.
- Not covered here: the deprecated paths (round 42 `dep_X_completeR`: exact sum of execution gas
  and reservoir for six paths, a lower bound for destroyBlackFunds, the split not stated); the
  invariant and the security properties from a reservoir other than 0 when deprecated; a concrete
  deprecated state over `StateGasMeter` with a successful run; the preparation of the first frame
  (`prepareFirstFrame`).

### Round 44: the deprecated paths over the EIP-8037 meter from any reservoir: the invariant, the security properties, the exact gas of destroyBlackFunds, a successful concrete run (Usdt/Invariant/DepMeterR.lean, Usdt/Security/DepMeterR.lean, Usdt/Sanity/ProcessMeterR.lean, Evm/FwdS.lean, Usdt/Complete/Deprecated/CallS.lean, DestroyS.lean, Usdt/Refill/DestroyDepS.lean, Usdt/Sanity/MirrorStateS.lean) (READY)

READY for the scope stated in this entry: clean rebuild of cb60c64 from an empty build directory,
exit 0, 1448 jobs, 3:42 wall; independent read-only review (round 44): PASS WITH FIXES, fixes applied in 5d949a9 (docstrings). The trust
assumptions of "What is trusted" in docs/RESULTS.md are unchanged.

T1 (third audit), three of the items left open in round 43.
- The invariant when deprecated from any reservoir (Usdt/Invariant/DepMeterR.lean).
  `KeepsInvAtSR runChild message state r` and `HonestBalanceAtSR … r` are `KeepsInvAtS` and
  `HonestBalanceAtS` for the calls from a caller of reservoir 0 with a message of reservoir `r`,
  as the CALL from a frame of reservoir `r` sends them (`RunSR`). At `r = 0` they are the round 41
  assumptions (`keepsInvAtSR_zero`, `honestBalanceAtSR_zero`). `inv_call_depR`: from Berlin, from a
  frame with any reservoir, deprecated, under these assumptions at the reservoir of the first
  frame, every successful call keeps `Inv`. `inv_call_anyDR` (deprecated or not, no hypothesis on
  the reservoir), `GoodCallDR`, `CallsDR`, `inv_callsDR`, `GoodCallDS.toR`, `CallsDS.toR`,
  `process_stepDR`, `process_stepSDR` (from Paris, `processMessage` from any starting meter, the
  assumptions of `processRunnerM` at the reservoir of that meter).
- The security properties when deprecated from any reservoir (Usdt/Security/DepMeterR.lean).
  `FwdAtSR`, `KeepsAtSR` (`keepsAtSR_zero`), `effect_allSR` (no assumption on the runner),
  `paused_call_allSR`, `nonOwner_call_allSR`, `listed_call_allSR`, `allowKept_call_allSR`,
  `supply_call_allSR` (`KeepsAtSR` at the reservoir of the first frame), `owner_only_allSR` (no
  hypothesis on the reservoir), `RunOkRSR`, `SeqRSR`, `SeqRS.toRSR`, `seqRSR_lift`, the five
  `_seq_allSR`, `runOkRSR_process`, `process_stepSecDR`.
- The runner assumptions hold for EthLib's runner (Usdt/Sanity/ProcessMeterR.lean):
  `keepsInvAtSR_process_stop`, `keepsAtSR_process_stop` (STOP at the upgraded address, every `r`,
  every reflexive relation), `honestBalanceAtSR_process_mirror` (`MIRROR`, every `r`).
- Deprecated destroyBlackFunds, the exact gas after the CALL (Evm/FwdS.lean,
  Usdt/Complete/Deprecated/CallS.lean, Usdt/Refill/DestroyDepS.lean,
  Usdt/Complete/Deprecated/DestroyS.lean). Forward over `StateGasMeter`: `fwd_splitS` (a cheap
  `StepG` stretch), `fwd_stepS` (one step other than SSTORE), `step_callS`, `resumeCall_okS` (the
  meter after a CALL whose child succeeded is `GasMeter.absorb` of the two, `absorb_sum`),
  `runFrame_childS`, `runFrame_child_fwdS`, `fromExtS` (EXTCODESIZE at 4874 to the CALL at 4891).
  `tailD_sgm`: the tail after the CALL with its two writes, exact through `Complete.exactS_write`.
  `dep_destroy_exactR`: from Berlin, from a frame with any reservoir, every successful run went
  through a caller with the meter of the first frame, reservoir 0 and the gas before the CALL less
  its price, and a child with no error; the meter after the CALL is
  `GasMeter.absorb caller.gas child.gas true` (execution gas plus reservoir is the caller's plus
  the child's); from it both writes meet `wOk`, 1364 gas is left after the second, and the end is
  `tailState`, `tailSub` and the meter after the second write less 1364 execution gas.
- A concrete deprecated state over `StateGasMeter` with a successful run
  (Usdt/Sanity/MirrorStateS.lean). `process_mirrorS_ok`: `MIRROR` succeeds under `processRunnerM`
  with its gas, any reservoir. `destroy_mirror_runsS`: from Paris (Glamsterdam included), in
  `S2 C H a` with `MIRROR` at `UA`, `destroyBlackFunds(a)` from `CALLER_A`, from a frame with any
  meter whose execution gas left is at least 1000000 and below 2^255, any substate and gas bound:
  the run under `processRunnerM` ends with no error. Helpers `extCost_le`, `absorb_gasLeft_ge`,
  `callGas_bounds`.
- Docs: the pin lines of this page name full commit hashes in place of local worktree paths.
- Not covered here: the split of the gas after the CALL for the six deprecated paths other than
  destroyBlackFunds (`dep_X_completeR` states the sum); the preparation of the first frame
  (`prepareFirstFrame`); `Inv` in `S2`; a top-level `processMessage` form of
  `destroy_mirror_runsS`. (Round 45 covers these but for `prepareFirstFrame` with authorizations;
  see the round 45 entry.)

### Round 45: the six other deprecated paths exactly over the EIP-8037 meter, `Inv` in `S2`, the concrete run as a message, the first frame of a call (Usdt/Complete/Deprecated/CallS.lean, CallExactS.lean, PathsS.lean, Usdt/Sanity/MirrorState.lean, MirrorStateS.lean, MirrorCallS.lean, Evm/FirstFrame.lean) (READY)

READY for the scope stated in this entry: clean rebuild of fd2e8e7 from an empty build directory, exit 0, 1452 jobs, 3:04 wall; `#print axioms` on each new theorem gives [propext, Classical.choice, Quot.sound] or a subset (UsdtVerify/Test/Axioms.lean); independent read-only review (round 45) PASS WITH FIXES, fixes applied in 6f779e5 (docstrings) and in these docs (the authorizations assessment). The trust
assumptions of "What is trusted" in docs/RESULTS.md are unchanged.

T1 (third audit), the items left open in round 44.
- The split of the gas after the CALL for the six deprecated paths other than destroyBlackFunds.
  `fromExtSG` (CallS.lean): `fromExtS` at the six sites of `fromExtC` (EXTCODESIZE at 3719, 4874,
  5739, 3213, 4200, 7186; CALL at 3736, 4891, 5756, 3230, 4217, 7203), with any input and output of
  the CALL in a memory it does not extend; `fromExtS` is now its instance at 4874. `resumeG`
  (CallExactS.lean): the frame after the CALL at `q` as the frame at `q + 1`. `dep_call_exactS`:
  from EXTCODESIZE, with a tail at `q + 1` given as a `StepG` specification of `T` gas (below
  97,920) to a normal halt that keeps the state and substate, every run over `StateGasMeter` that
  ends with no error went through the CALL with a child with no error, `T ≤` the execution gas
  left of `GasMeter.absorb caller.gas child.gas true`, and ends with that meter less `T` execution
  gas. `dep_X_exactR` (PathsS.lean) for totalSupply (121), balanceOf (126), allowance (128),
  transfer (51), approve (53), transferFrom (53): from Berlin, from a frame with any reservoir, the
  caller's meter (`m.gas` with reservoir 0 and the gas before the CALL less its price), the message
  (`SendsVia`, the reservoir of `m`, the gas of `depCallGas`), the meter after the CALL and the
  exact end meter, as `dep_destroy_exactR` states them for destroyBlackFunds.
- `Inv` in `S2` (MirrorState.lean). `KD a` has a fifth pair `(1, 1)`: `_totalSupply` is 1 in `S2`
  (through round 44 slot 1 was not set there, so `Inv` failed unless a keccak slot of `a` is slot
  1). The earlier lemmas on `S2` keep their statements (the new pair comes last). `inv_S2`:
  `Inv C (S2 C H a)` under `SepOn [kD a]` (`sumTo_indicator`). `destroy_mirror_inv`: from Paris and
  before Glamsterdam, under `SepOn (callKeys …)` of the call, `Inv` in `S2`, the run of
  `destroy_mirror_runs`, and `Inv` at the end of every successful run of that call at any gas bound
  (`inv_dep_destroy`).
- A `processMessage` form of the concrete run (MirrorStateS.lean). `mDOG b t C a G R`: the message
  with gas field `G` and reservoir field `R`. `destroy_mirror_runsT`: the run from any state with
  slot 10 of `C` equal to `W`, the owner `CALLER_A`, `a` blacklisted, `MIRROR` at `UA` and an
  account at `C`; `destroy_mirror_runsG` from `S2`; `destroy_mirror_runsS` is now the case
  `G = R = 0`. `destroy_mirror_processS`: from Paris, `C` no precompile, `processMessage` over
  `StateGasMeter` in `S2` from any substate and any meter with execution gas left in
  [1000000, 2^255) and held gas at most `G` ends with a frame with no error.
- The preparation of the first frame (Evm/FirstFrame.lean, MirrorCallS.lean).
  `FirstFrame.prepareFirstFrame_call`: for a call with no value and no authorization whose
  recipient's code is no delegation indicator (or before Pectra), over any meter,
  `prepareFirstFrame` is `.ok` of the frame with that code, the state with the read of the
  recipient, the substate as given, refund 0 and the meter `commit (start gas reservoir)`. `S3 C H
  HC a`: `S2` with `CODE` at `C` under `HC` (in `S2` the code of `C` is empty, so
  `processMessageCall` would not run USDT there); same storage (`storageAt_S3`, by definition).
  `destroy_mirror_processT`, `destroy_mirror_callS`: from Paris, in `S3` with `C ≠ UA`, `C` no
  precompile, `H` and `HC` not the empty code hash, `HC ≠ H`, any chain, gas field in
  [1000000, 2^255), any reservoir field and substate, no authorization: `processMessageCall` over
  `StateGasMeter` gives an output with no error.
- Not done: `prepareFirstFrame` with authorizations. `applyAuthorization` (EthLib,
  Execution/Transactions/Authorization.lean) recovers each authority by secp256k1 ECDSA public key
  recovery (`Ecdsa.recover`) over a keccak hash of the RLP of the authorization. For given
  signatures that recovery is out of reach here (no `native_decide`; the kernel does not evaluate
  it). A form that takes the result of `recoverAuthority` for each authorization as a hypothesis
  (authorizations out of scope or not recovered leave the state as is; a recovered authority goes
  through `authorityAccepts`, `payAuthorization` and `delegate`) is possible but not done: it needs
  an induction over the list with the state, accesses and meter that `payAuthorization` and
  `delegate` leave, and that USDT's account and storage are kept (an account with code `CODE`
  accepts no delegation). The `processMessage` forms take any starting meter (round 41, U1), so
  they hold for whatever meter the authorizations leave; the link from a transaction with
  authorizations to that meter, message and state is not stated.
  (Round 46: done in the form with the recovered authorities as hypotheses, and end to end for the
  concrete call in `S3` with any list; see the round 46 entry.)

### Round 46: `prepareFirstFrame` with EIP-7702 authorizations, the recovered authorities as hypotheses; a type-4 deprecated call to USDT through `processMessageCall` (Evm/Auth.lean, Usdt/Sanity/MirrorAuth.lean) (READY)

READY for the scope stated in this entry: clean rebuild of fb104c2 from an empty build directory, exit 0, 1454 jobs, 188.85 s wall, 483 s user; `#print axioms` on each new theorem gives [propext, Classical.choice, Quot.sound] or a subset (UsdtVerify/Test/Axioms.lean); independent read-only review (round 46) PASS WITH FIXES, fixes applied in 5e376ee (docstrings, one proof step; incremental build exit 0, 1454 jobs) and in these docs (the scope, the `buyGas` caveat). The trust assumptions of "What is trusted" in docs/RESULTS.md are unchanged.

T1 (third audit), the item left open in round 45: `prepareFirstFrame` with authorizations.
`applyAuthorization` (EthLib, Execution/Transactions/Authorization.lean) recovers each authority by
secp256k1 ECDSA public key recovery over a keccak hash (`recoverAuthority`). For given signatures
that recovery is out of reach. The statements below either take what `recoverAuthority` returns
as a hypothesis or hold for every authority.
- One authorization (Evm/Auth.lean). `seen done a` is `done` with the read and the access of `a`.
  `apply_out`, `apply_none`: an authorization out of scope, or with no recovered authority, keeps
  the delegations. `apply_refused`: an authority `a` that `authorityAccepts` refuses gives
  `seen done a`. `apply_accepted`: an accepted authority gives the delegations of
  `payAuthorization` of `seen done a`, with the state and the added refund of `delegate`.
  `apply_cases`: every `.ok` result is one of these. `delegate_ok`: `delegate` never fails. It
  gives the authority its account with the hash of `delegationCode auth` and the nonce one more.
  Every other address reads as before (`SameOutside`), and the code under every other hash is
  kept. The refund is `delegateRefund`: 12500 before Glamsterdam for an authority with an account,
  else 0. `pay_pre`: before Glamsterdam `payAuthorization` keeps the delegations. `pay_glam`: from
  Glamsterdam it sets the meter of `chargeAuthorization` and records the paid write. It records the
  delegation when the address of the authorization is not the zero address. `pay_keeps`: it keeps the state, the accesses and the refund.
- An address whose code is not empty and no delegation indicator. `accepts_code`, `apply_code`:
  such an authority is refused. `apply_keeps`, `fold_keeps`: when no `delegationCode` of the list
  hashes to that address's code hash (a keccak hypothesis), the authorizations keep its account,
  its storage and its code. `fold_meter_pre`: before Glamsterdam the
  authorizations keep the meter.
- The first frame. `prepareFirstFrame_auths`: for a call with no value whose authorizations end
  with `.ok done`, and whose recipient `C` has in `done.state` a code `c` that is no delegation
  indicator (or before Pectra), over any meter, `prepareFirstFrame` is `.ok` of the frame with the
  code `c`, the state `done.state` with the read of `C`, the accessed addresses of `done`, the
  refund of `done` and the meter `GasMeter.commit done.meter`. `prepareFirstFrame_auths_error`:
  an error of the authorizations is the error of `prepareFirstFrame`.
- The meter of EIP-8037. `charge_bound`: from Glamsterdam, with at least `authMax` (227790 =
  183600 + 9000 + 35190) execution gas left and the pre-state code of the authority in the state,
  `chargeAuthorization` succeeds and takes at most `authMax` execution gas. `apply_exists`: over
  `StateGasMeter`, from a state where every account's code hash, now and before the transaction,
  has a code (`Resolves`, `PreResolves`), and from Glamsterdam with at least `authMax` execution
  gas left, one authorization ends with `.ok`, keeps both facts, and takes at most `authMax`
  execution gas. `fold_exists`: from such a state, and from Glamsterdam with at least `authMax`
  times the length of the list in execution gas, the authorizations of any list end with `.ok`
  and take at most that much execution gas. Neither takes a hypothesis on `recoverAuthority`.
- The concrete call (Usdt/Sanity/MirrorAuth.lean). `apply_usdt`: an authorization in scope whose
  recovered authority is `C`, in a state where the code of `C` is `CODE`, is refused: only the read and the
  access of `C` are added. `apply_fresh`: before Glamsterdam, an authorization in scope with nonce
  0 whose recovered authority has no account is accepted, with the state of `delegate`, refund 0
  added, and the meter kept. `apply_caller_S3` is its instance for the first authorization of a list from
  `S3`, with authority the caller `CALLER_A` (`CALLER_A ≠ C`, `CALLER_A ≠ UA`). There `CALLER_A`
  gets nonce 1, balance 0 and the hash of `delegationCode auth`. In a real transaction `buyGas`
  raises the sender's nonce before `processMessageCall`, so this instance only illustrates the
  lemmas. `prepareFirstFrame_S3`: in
  `S3`, for any list whose authorizations end with `.ok done` and no `delegationCode` of which hashes
  to `H` or `HC`, `prepareFirstFrame` is the frame of `prepareFirstFrame_auths` with the code
  `CODE`. `done.state` keeps the account, the storage and the code of `C` and `UA`.
  `destroy_mirror_call_auths`: from Paris, in `S3` with the hypotheses of `destroy_mirror_callS`,
  any list of authorizations no `delegationCode` of which hashes to `H` or `HC`, any paid writes,
  any reservoir field and substate, and a gas field `G` below 2^255 with at least 1000000 (and,
  from Glamsterdam, 227790 more per authorization): `processMessageCall` over `StateGasMeter` gives
  an output with no error. An authorization to USDT's address as the delegate (`auth.address = C`)
  and one whose authority is the caller are covered by this statement, which holds for every list.
- Not covered: the transaction around the message (`processTransaction`: the checks of a type-4
  transaction, the intrinsic gas, `buyGas` and the sender's nonce, the settlement, the
  deletions); anything about the output beyond "no error" (its refund, gas, state, logs and
  accesses); a call with value or to a recipient with a delegation indicator; forks before Paris
  for the concrete call; the error path of the authorizations in `S3` (the gas hypothesis rules
  out running out of gas); the recovery of any concrete signature. The keccak hypothesis on `H`
  and `HC` is assumed, not proved.

### Round 47: re-pin to EthLib 0c34dc001, the local copies of #1597, #1599 and #1605 removed (Evm/At.lean)

Built, checked and reviewed: clean rebuild of 4cac964 with `.lake/build` removed
first, exit 0, 1463 jobs, 156.20 s wall, 418.91 s user; `#print axioms` on the 1352 entries of
UsdtVerify/Test/Axioms.lean gives [propext, Classical.choice, Quot.sound] or a subset; no `sorry`,
`admit`, `axiom`, `native_decide` or `bv_decide` in UsdtVerify/ (grep exit 1). No new USDT
theorem. The trust assumptions of "What is trusted" in docs/RESULTS.md are unchanged.
Independent read-only review: PASS. It compared every statement and definition body of
`UsdtVerify` at 8923ce5 (EthLib pin5) and at this round (pin6) after unfolding the renamed and
shadowed names, and found no shared entry that differs. It checked that each EthLib replacement
has the same or weaker hypotheses and the same conclusion, and that all 11,813 `UsdtVerify`
theorems use only propext, Classical.choice and Quot.sound.

- The pin. EthLib master 0c34dc001 holds the generic lemmas upstreamed from this repository:
  #1597 (every message keeps the block of the state, a failed call keeps the state outside its
  effects), #1599 (EXTCODESIZE and EXTCODECOPY at every fork from Berlin, `processMessage` over any
  lawful meter, `prepareFirstFrame_of_value_eq_zero`) and #1605 (`FailsOn`, `MeetsOk`, `HoareOn`,
  `SpecOn`).
- `At` (Evm/At.lean). Since EthLib #1351 EthLib's `At` has a thirteenth argument, the return data
  of the frame, and a thirteenth condition. Every rule of this repository was written for the
  twelve conditions. `UsdtVerify.At` is that predicate, the body of EthLib's `At` at the previous
  pin, with no condition on the return data. Inside the namespace `UsdtVerify` the name `At` is
  this predicate, so the statements read as before and mean what they meant at the previous pin.
  `At.iff_logic`: `At` holds of a frame exactly when EthLib's `At` holds with the return data of
  that frame. `liftAt`, `liftPre`: an EthLib triple that holds from `Logic.At … rd` for every `rd`
  is a triple from `At`. `lowerPre`: the converse direction for a precondition. The EthLib rules
  this repository applies directly are restated for `At` by these lifts: `At.rule`,
  `At.extcodesize`, `At.gas_rule`, `At.caller`, `At.reshape`, `At.stop`, `At.revert`,
  `At.invalid_fe`, `At.startFrame`, `meets_of_specAt`. The other rules are proved here from
  `At.rule` and `Gas.At.ruleG`, so they need no lift. Two Sanity files (Process.lean,
  ProcessExact.lean) use EthLib's `At` with empty return data directly, for
  `processMessage_of_spec`. `resumeCall_eq` (EthLib) now also states the return data after a
  call, which the five uses discard.
- Removed, now in EthLib (docs/LAYOUT.md has the table):
  Evm/Local/Parent.lean (`Local.processMessage_failed_getStorage` is EthLib's
  `getStorage_processMessage_of_error`, which takes `error.isSome = true` where the local lemma
  took `error ≠ none`, bridged by `Option.isSome_iff_ne_none`);
  Evm/Local/Extcodesize.lean (`Local.extcodesize` is `At.extcodesize`, EthLib's
  `extcodesize_of_berlin_le` for `At`, same hypotheses);
  Evm/ProcessMeter.lean (`processRunnerM`, `processMessage_map_valM`,
  `processMessage_map_val_valueM` are EthLib's `processRunner`, `processMessage_map_val`,
  `processMessage_map_val_value`, now generic in the meter. `at_startFrameS` is not in EthLib, it
  is about this repository's `Meter.toNat`, and moves to Evm/Meter.lean as
  `Meter.at_startFrameS`);
  Evm/FirstFrame.lean (`FirstFrame.prepareFirstFrame_call` is EthLib's
  `prepareFirstFrame_of_value_eq_zero`, the same statement);
  Evm/Sends.lean (`Sends.AbortsOn`, `MeetsOk`, `HoareOn`, `SpecOn` are EthLib's `FailsOn`,
  `MeetsOk`, `HoareOn`, `SpecOn` with the same bodies, `mono_S` is `HoareOn.mono`);
  `Local.instruction_sub` is EthLib's `instruction_sub`.
- Statements. No headline theorem changed its meaning. The statements that named
  `ProcessMeter.processRunnerM` name `processRunner` (the same function: `processRunnerM` was
  EthLib's `processRunner` restated over any meter), and those that named `Sends.SpecOn` name
  EthLib's `SpecOn` (the same definition, `AbortsOn` renamed `FailsOn`). No EthLib lemma was weaker
  than a proof here needed, so no local copy of the four groups is kept.
- Kept local while their upstreaming is in flight: Evm/Route.lean, Evm/Keeps.lean, and the
  less-gas framework (Evm/Gas.lean, Evm/Stuck.lean, Evm/GasRules.lean, Evm/NoAbort.lean). Evm/Local/
  now holds only Rules.lean (the instruction-table lemmas of LT, GT, DIV, AND, OR, MUL, NOT).
- `processRunner` is generic in the meter since #1599, so two `runFrame` equations (Evm/Mirror.lean,
  Usdt/Invariant/Seq.lean) name the meter `Nat`.

### Round 48: re-pin to EthLib bc16ee428, the local copies of #1611, #1612, #1615 and #1616 removed

Built and checked: clean rebuild of 4930260 in a fresh clone (empty build directory), exit 0,
1468 jobs, 174.83 s wall, 468.17 s user; `#print axioms` on the 1329 entries of
UsdtVerify/Test/Axioms.lean gives [propext, Classical.choice, Quot.sound] or a subset (1276 the
three, 35 [propext, Quot.sound], 8 [propext], 10 none), with no `sorryAx`, `ofReduceBool` or
`trustCompiler`; no `sorry`, `admit`, `axiom`, `native_decide`, `bv_decide` or `decide +native` in
UsdtVerify/ (grep exit 1). No new USDT theorem, and no statement of a USDT theorem changed.
Independent read-only review: PASS, no finding to fix. It dumped every constant of `UsdtVerify`
at 67f8859 (pin6) and at 4930260 (pin7): 3352 before, 3284 after, 3276 shared, 2965 identical
(also by expression hash). The 311 others differ only by the renamed names (`Complete.Route` and
the route functions to EthLib's, `Gas.sh` to `addGas`), except the bodies of `Gas.StepG` (the
disjunction grouped differently, proved equal) and `Gas.Stuck` (equal by `rfl`). Each of the 76
removed entries was restated and proved in the new build from its EthLib replacement, or is an
unused proof helper. No EthLib definition changed between the two pins. The trust assumptions of "What is trusted" in docs/RESULTS.md are unchanged.
Lines of Lean in UsdtVerify/: 68,862 at the end of round 47, 68,074 after round 48 (788 fewer;
Evm/GasRules.lean 1162 to 752, Evm/NoAbort.lean 362 to 252, Evm/Route.lean 459 to 327,
Evm/Stuck.lean 321 to 240, Evm/Gas.lean 454 to 426).

- The pin. EthLib master bc16ee428 holds the less-gas framework and the route of a call,
  upstreamed from this repository: #1611 (`Route`, `Routes`, EIP-7702 delegation in the call
  rules of every kind, `callStep_child_of_routes`), #1612 (`addGas`, `Fails`, `Follows`,
  `RunMono`, `GasMono`, `StepG`, `HoareG`, `SpecG`, `SpecG.low`, `reaches_low`, `Stuck`), #1613
  (`ReadsAs`, `SentVia`, `KeepsOn`, `CallSends.sentVia`), #1615 (a G form of every opcode rule,
  every `runMono_*` fact, the SSTORE stuck rules) and #1616 (`NoAbort`, `NoAbortLow`, `StepGA`,
  the GA rules, `no_error_of_reaches`).
- Names. EthLib now declares many names that this repository declares too (`StepG`, `HoareG`,
  `SpecG`, `Stuck`, `pushG`, ...). Each file that opens both namespaces says
  `open EthLib.Execution.Evm.Logic hiding ...` for the names it uses, so each name means what it
  meant at the previous pin. Inside the namespace `UsdtVerify.Gas` the local names come first.
- Removed, now in EthLib (docs/LAYOUT.md has the table): `Gas.sh` (EthLib's `addGas`, the same
  body), `Gas.Fails`, `Gas.Rel` (`Follows`), `Gas.RunMono`, `Gas.RelS` (`StepFollows`, the same
  three cases with the two failures grouped first), every `Gas.runMono_*` fact and its helpers,
  `Gas.NoAbort`, its facts and `Gas.NoAbortLow`, `Gas.sstoreStep_bad` and `Gas.sstoreStep_low`
  (EthLib's `sstoreStep_halts`, `sstoreStep_of_isStatic`, `sstoreStep_of_gasLeft_le`), and
  `Complete.Route`, `Routes`, `routeAddr`, `routeCode`, `routeCost`, `routeState`, `routeSub`,
  `routes_congr`, `routes_rec`. `callStep_child_r` keeps its statement and is now proved from
  EthLib's `callStep_child_of_routes` for CALL. `Gas.at_sh` is renamed `Gas.at_addGas`.
- Kept local, and why.
  `StepG` (Evm/Gas.lean) is now `Step ∧ SimAt ∧ Logic.GasMono`: EthLib's `Logic.StepG` with
  `SimAt`. The meter link (Evm/Shadow.lean, Evm/Meter.lean) needs every frame of a run to be at a
  `simulated` opcode, and EthLib's `StepG` does not say so. `HoareG`, `SpecG`, `StepGA`,
  `HoareGA`, `SpecGA` and `Stuck` (EthLib's `Stuck` with `SimAt`) follow it, and they imply
  EthLib's (`HoareG.toLogic`, `SpecG.toLogic`, `SpecGA.toLogic`). For the same reason the opcode
  rules of Evm/GasRules.lean and Evm/NoAbort.lean stay: EthLib's `pushG`, `sstoreG`, ... are
  triples over `Logic.StepG` from EthLib's `At` with return data, and a triple does not show
  `SimAt` along its steps. `At.ruleG`, `At.ruleGA` and the new `At.stuck` are EthLib's rules of
  the same names for the local `At` and `StepG`.
  The `E` forms (`low_of_reachesE`, `SpecG.lowE`, `not_ok_of_reachesE`, `no_ok_stuckE`, ...)
  take `Ends` in place of a `runFrame` equation, so the meter link can use them for a loop over
  `StateGasMeter`. EthLib's `low_of_reaches`, `SpecG.low`, `no_ok_stuck` take only a `runFrame`
  equation, so the local forms stay. `no_error_of_reaches` is now EthLib's, for the local `StepGA`.
  Evm/Keeps.lean: EthLib's `SentVia` asks the caller state to read as `S` (`ReadsAs`: the same
  accounts, storage and transient storage), where the local `SentVia` asks only the same storage
  and code (`SameView`). The runner assumptions of the deprecated theorems (`KeepsAt`, `FwdAt`,
  `HonestBalanceAt`, `KeepsInvAt`, ...) are stated with the local `SentVia`, so they stay. With
  EthLib's `SentVia` they would quantify over fewer calls, and the theorems would be stronger. That
  change touches about twenty files and is left open.
  `accCost`, `extCost`, `SendsVia`, `CallFrom`, `atCallState`, `atCallSub`, `callWithRS` and
  `callWithR` (Evm/Route.lean) are about the deprecated paths of this contract and stay. The
  CALL steps over `StateGasMeter` (Evm/CallMeter.lean, Evm/CallSim.lean) stay, since EthLib's
  `callStep_child_of_routes` is for the meter `Nat` only.

## Open (not proved)
- The EIP-8037 meter (`StateGasMeter`) that EthLib's `processTransaction` uses from
  Glamsterdam (third audit, T1; rounds 33 to 36 above). Round 36 covers, not deprecated: the
  exact success condition from reservoir 0 for the 13 writing functions, the sum of the
  execution gas left and the reservoir at the end at any reservoir (`X_gas_any`), each under one
  hypothesis on the start state per write that can refill, and `process_step` /
  `goodCall_process` / `inv_calls` over `StateGasMeter` with no such hypothesis. Not covered: the
  deprecated paths, the split of the gas at the end between execution gas and reservoir, the gas
  of a run with a refill, and the security properties over `StateGasMeter` when deprecated.
  Round 37: the security properties over `StateGasMeter` not deprecated, single calls and `SeqS`
  sequences, with no hypothesis on the reservoir, on refills or on the gas limit.
  Round 39: the deprecated paths over `StateGasMeter` from reservoir 0 (completeness without the
  gas after the CALL, the invariant under `KeepsInvAtS` / `HonestBalanceAtS`, `process_stepDS`,
  the single-call security properties). Still open there: a reservoir other than 0 when
  deprecated, the gas left after the CALL, the deprecated sequence forms of the security
  properties.
  Round 41: the `processMessage` forms over `StateGasMeter` hold for any starting meter (fourth
  audit, U1), so they cover the meter that `processMessageCall` passes after the authorizations.
  The preparation of the first frame itself (`prepareFirstFrame`, the authorizations) is not
  verified here. The theorems start from its result. (Round 45: done for a call with no value and
  no authorization; round 46: with authorizations, see the round 46 entry.)
  Round 41: the deprecated sequence forms of the security properties over `StateGasMeter`
  (`_seq_allS` over `SeqRS`) and `owner_only` for deprecated destroyBlackFunds over it
  (`owner_only_allS`) are done, both from reservoir 0 when deprecated.
  Round 42: the completeness of the deprecated paths from any reservoir, with the execution gas
  left plus the reservoir at the end exact for six paths and bounded below for destroyBlackFunds
  (`dep_X_completeR`), and success of the 13 writing functions at any reservoir with refills
  allowed from the one-counter threshold (`X_ok_dom`), and the exact condition and gas of approve
  with refills at any reservoir (`approve_zero_sgm`, `approve_set_sgm`).
  Round 43 (READY): the exact success condition and gas with refills at any reservoir for every
  writing function on its success path not deprecated (Evm/Chain.lean and the `X_sgm` theorems of
  Usdt/Refill/), see the round 43 entry above.
  Round 44 (READY): the invariant and the security properties from any reservoir when deprecated
  (`inv_call_depR`, `process_stepDR`, `effect_allSR`, the `_call_allSR` and `_seq_allSR` forms,
  `owner_only_allSR`), the exact gas after the CALL of deprecated destroyBlackFunds with refills
  (`dep_destroy_exactR`), and a concrete deprecated run over `StateGasMeter` that ends with no
  error (`destroy_mirror_runsS`), see the round 44 entry above. Still open after round 44: the
  split of the gas after the CALL for the six deprecated paths other than destroyBlackFunds.
  Round 45 (READY): that split (`dep_X_exactR`), `Inv` in `S2` under `SepOn` of its key
  (`inv_S2`, `destroy_mirror_inv`), the concrete run through `processMessage` and
  `processMessageCall` (`destroy_mirror_processS`, `destroy_mirror_callS`, the latter in `S3`), and
  `prepareFirstFrame` for a call with no value and no authorization
  (`FirstFrame.prepareFirstFrame_call`), see the round 45 entry above. Still open:
  `prepareFirstFrame` with authorizations (for given signatures out of reach: ECDSA recovery over
  keccak; a form with the recovered authorities as hypotheses is possible and not done).
  Round 46 (READY): `prepareFirstFrame` with authorizations, with what `recoverAuthority` returns
  as hypotheses (Evm/Auth.lean: `apply_cases`, `delegate_ok`, `fold_keeps`,
  `prepareFirstFrame_auths`), their success over `StateGasMeter` with 227790 execution gas each
  from Glamsterdam and no hypothesis on the authorities (`fold_exists`), and the concrete
  deprecated call through `processMessageCall` in `S3` with any list of authorizations
  (`destroy_mirror_call_auths`), see the round 46 entry above. Still open: the type-4 transaction
  around the message (`processTransaction`), and the keccak hypothesis that no `delegationCode`
  hashes to the code hashes of `S3`.
- Security properties when deprecated without the runner assumptions of round 23 (`KeepsSlots`,
  `KeepsBal`, `KeepsListed`, `KeepsAllow`, `KeepsSupply`); none is proved for a concrete upgraded
  contract (round 24: concrete runners meet them, `Sanity/Runner.lean`). `transferFrom_bound` has
  no deprecated form.
- The keccak hypotheses `SepOn` / `SecSep` of a call's keys (round 29; finitely many facts, each
  one given slot against 2^160 others) are not proved, and not shown for any particular call.
- A theorem that neither `KeepsInv` nor `KeepsInvAcc` implies the other (by the definitions only).
- Completeness per function: done for the dispatcher (round 11), totalSupply, balanceOf,
  transfer (round 12), approve, transferFrom, the ten owner functions (round 13), not deprecated
  where the function reads the flag, and every getter and name/symbol (round 13, name/symbol
  under the named hypothesis `StrForm`), and the invariant over every successful call when not
  deprecated (`inv_call`).
- The deprecated paths: done (rounds 14, 15). Every deprecated function (totalSupply,
  balanceOf, transfer, approve, transferFrom, allowance, destroyBlackFunds) has its completeness
  theorem for any gas and any runner (`dep_*_complete`), with or without an EIP-7702 delegation
  at the upgraded address (round 16). destroyBlackFunds no longer takes `hstatic` or `hkeep`
  (round 19: both are in its conclusion); every `dep_*_complete` takes only the coldness flags
  beyond the fork, size, selector and flag.
- Hypotheses the completeness theorems of the writing paths keep, by name: size < 2^256
  (`hstatic` and `hacc` removed in round 18; for deprecated destroyBlackFunds `hstatic` and
  `hkeep` removed in round 19). Every fork from Berlin, Glamsterdam included (round 17 for the
  non-deprecated writing paths, round 19 for the deprecated paths).
- Failed top-level calls and calls with value: done (round 18, `untouched_process_failed`,
  `process_value_fails`, `process_step`).
- The deprecated paths in the invariant: done (round 15, now `inv_call_ns`; static frames too in `inv_call_all`, round 17, and in `inv_call_ns`, round 19) under the named runner
  assumptions `KeepsInv` and `HonestBalance` (through round 19 also an account of the contract
  when deprecated and not static, `hacc`; `inv_call_ns` took `hstatic` through round 18). Without `HonestBalance`, deprecated
  destroyBlackFunds keeps `Inv` exactly when the answer is the local balance
  (`inv_dep_destroy_iff`); `exists_breaks` gives a state where a different answer breaks it.
  Round 29: the assumptions are `KeepsInvAt` / `HonestBalanceAt` (the calls the code makes);
  `processRunner` meets `KeepsInvAt` when the upgraded code is STOP (`keepsInvAt_process_stop`).
  Round 30: `processRunner` meets `HonestBalanceAt` when the upgraded code is `MIRROR` and its
  queried slot holds USDT's `balances[a]` in the start state (`honestBalanceAt_process_mirror`);
  round 31: shown together with `KeepsInvAt` in one concrete deprecated state with `MIRROR`
  (`process_step_dep_hyps`; the keccak hypotheses of `process_step` there are not discharged).
- Non-vacuity (round 24): no witness run is deprecated (round 31: `balanceOf_mirror_sat` gives the
  hypotheses of a deprecated exact theorem in a concrete deprecated state, not a witness run of the
  spec theorems); the keccak hypotheses of the witness calls
  (`SepOn` / `SecSep` of their keys, since round 29) are not discharged.
- Exact success conditions (round 25): done for the 32 functions not deprecated and the seven
  deprecated forwarding paths (under `NoFail`, since round 29 `NoFailOn`, and a runner hypothesis
  giving the answer `A`).
  Round 26: every gas for the 13 writing functions not deprecated (`X_iff_gas`) and for the seven
  deprecated forwards (`X_dep_ok_iff_gas` with `X_dep_low`; destroyBlackFunds in the second part),
  and an iff for a runner that may fail with any error (`X_dep_ok_iff_fails`, under `hfail`).
  These take the runner hypotheses `hans` (and `NoFailOn` or `hfail`). Round 30: `hans` is asked
  only of the call the path makes, with its gas (`CallFrom`); discharged for `processRunner` with
  the upgraded code STOP for the seven forwards, `X_dep_ok_iff` and `X_dep_ok_iff_gas`
  (Sanity/ProcessExact.lean). Round 31: discharged for `processRunner` with the upgraded code
  `MIRROR`, whose success depends on its gas, for `balanceOf_dep_ok_iff_gas` and
  `destroyBlackFunds_dep_ok_iff_gas` (Sanity/MirrorExact.lean).
  Round 31: the `X_dep_ok_or_fails` take the gas-aware `hans` too (the seven paths).

## Generic gaps found (for the EthLib program-logic agent)
1. Missing opcode rules at the pin (kept as LOCAL lemmas, UsdtVerify/Evm/Local/Rules.lean):
   CALLVALUE, CALLDATASIZE (a generic "read a frame value" rule), instruction-table lemmas for
   LT/GT/DIV/AND/OR/SUB/MUL/NOT, JUMPI on a condition *proved* 0, and EXP with its EIP-160 price
   worked out (a corollary of EthLib's `exp`, whose price is `gasSchedule fork`).
   Round 47: SUB comes from EthLib (`instruction_sub`). The local entry is removed.
   POP/DUPn/SWAPn/EXP now come from EthLib (#1223). Round 27: the `Step` form `Local.exp` was
   unused and is removed; the EXP rule with its price worked out is `Gas.expLG` (over `StepG`,
   Evm/GasRules.lean).
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
7. (CLOSED in round 9 by EthLib #1272/#1292) No rule for STOP (0x00): the local `Local.stop` /
   `Stopped` were removed; EthLib's `stop` concludes `Halted false .empty`.
8. (CLOSED in round 9 by EthLib #1292) `At` did not name the output buffer; it now carries
   `evm.output = .empty`, so every STOP-ended spec states the empty output.
9. Storage writes over slots (UsdtVerify/Evm/Write.lean, generic): `writeSlot` (the `.ok` branch
   of setStorage after the read is recorded, under `hasAccount`), `storeSub`, `sstoreW` (EthLib's
   `sstore` restated; deleted in round 19, `Gas.sstoreWG` replaces it), read/access idempotence (`readSlot_readSlot`, `accessSlot_accessSlot`),
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

14. (CLOSED in round 9 by EthLib #1280: `extcodesize`, `gas_rule`, `externalBaseCost_of_berlin`;
   Local/Account.lean deleted.) Round 5 (LOCAL, UsdtVerify/Local/Account.lean, no sorry): EthLib's program logic at the pin has
   no rule for EXTCODESIZE (0x3b) nor GAS (0x5a). Local generic rules: `Local.extcodesize` (Berlin ≤
   fork < Glamsterdam: pushes the code size, pays 2600 cold / 100 warm, `externalBaseCost_of_berlin`,
   inserts the address into the accessed addresses, records the account read) and `Local.gasOp`
   (pushes `gas - 2`), with `instruction_extcodesize` / `instruction_gas`.
   CALL itself needed nothing new: `callWith` covers the input range (call data from memory) and the
   output range (return data copied into memory), which is all Solidity 0.4.17 uses (no
   RETURNDATASIZE/RETURNDATACOPY). Local generic memory lemma: `memoryReadBytes_write_after` (a read
   across a write = the bytes before ++ the written bytes), in Usdt/Spec/Deprecated/BalanceOf.lean.
   Pitfall: in `refine (lemma (by tac) ...).seq ?_`, tactic arguments run before the goal fixes
   implicit arguments (gas, rest, state): give them explicitly (`(gas := ...)`).

15. Round 6 (re-pin to d4d422780): gaps 1 (CALLVALUE, CALLDATASIZE, JUMPI on a condition proved 0)
   and 4 (memory reads after writes) are CLOSED by EthLib (#1258, #1266); the local copies are
   removed. Still local at d4d422780 (checked by grep of Logic/): STOP (gap 7), EXTCODESIZE and GAS
   (gap 14), the instruction-table lemmas LT/GT/DIV/AND/OR/SUB/MUL/NOT and EXP with its price
   (gap 1 remainder). New local generic memory lemmas (no sorry, Usdt/Spec/Deprecated/Transfer.lean):
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

17. Round 18 (LOCAL, UsdtVerify/Evm/Local/Parent.lean, no sorry): EthLib proves that a message keeps
   the block of the state (`parent`) only for static messages from Paris (`processMessage_static`), so its
   `getStorage_restoreTxState` could not be applied to the rollback of a failed message that is
   not static. `parent_process` proves it for every message and creation from any fork.
   Candidates for EthLib: the per-group lemmas, `pResult_step`, `parent_runFrame`,
   `parent_process`, `processMessage_failed_getStorage`.
   (CLOSED in round 47 by EthLib #1597, Call/Parent.lean: `parent_processMessage`,
   `processMessage_sameOutside_of_error`, `getStorage_processMessage_of_error`. The local file is
   removed.)
18. Round 19 (LOCAL, UsdtVerify/Evm/Local/Extcodesize.lean, no sorry): EthLib's `Logic.extcodesize`
   and `Logic.callWith` (and `callBaseCost_of_berlin`, `externalBaseCost_of_berlin`) take
   `fork < .glamsterdam`. `Local.extcodesize` is the EXTCODESIZE rule from Berlin with the price
   `externalBaseCost fork cold`; `callStep_child_r` (Evm/Route.lean) is a CALL step lemma
   from Berlin, Glamsterdam included, with the price of the fork. Candidates for EthLib: both, and
   a fork-generic `callWith`.
   (EXTCODESIZE CLOSED in round 47 by EthLib #1599, `extcodesize_of_berlin_le`, used through
   `At.extcodesize`. Local/Extcodesize.lean is removed. The CALL step and the route stay local in
   Evm/Route.lean while their upstreaming is in flight.)

## Measurements (macOS arm64, LEAN_NUM_THREADS=2, safe.sh 9G)
Round 48: clean project build of the tree of commit 4930260 (a fresh clone, empty build
directory, safe.sh 9G, LEAN_NUM_THREADS=2, `lake build UsdtVerify UsdtVerify.Test.Axioms`) 174.83 s
wall, 468.17 s user, 1832681472 bytes max RSS (`/usr/bin/time -l`), exit 0, 0 "error:" lines,
1468 jobs.
Round 47: clean project build of the tree of commit 4cac964 (`.lake/build` removed first, safe.sh
9G, LEAN_NUM_THREADS=2, `lake build UsdtVerify UsdtVerify.Test.Axioms`) 156.20 s wall, 418.91 s
user, exit 0, 1463 jobs.
Round 46: clean project build of the tree of commit fb104c2 (the build directory moved aside,
safe.sh 9G, LEAN_NUM_THREADS=2, `lake build UsdtVerify UsdtVerify.Test.Axioms`) 188.85 s wall,
483.10 s user, exit 0, 1454 jobs. The review fixes (5e376ee) built incrementally, exit 0, 1454 jobs.
Round 45: clean project build of the tree of commit fd2e8e7 (the build directory moved aside,
safe.sh 9G, LEAN_NUM_THREADS=2, `lake build UsdtVerify UsdtVerify.Test.Axioms`) 3:04 wall, 478 s
user, exit 0, 1452 jobs.
Round 41: clean project build of the tree of commit 8df74c4 (`rm -rf .lake/build`, safe.sh 9G,
LEAN_NUM_THREADS not set, `lake build UsdtVerify UsdtVerify.Test.Axioms`) 110.29 s wall, 436.43 s
user, 1787281408 bytes max RSS (/usr/bin/time -l), exit 0, 0 "error:" lines, 1425 jobs. Hash
check: 11075 bytes, keccak256 b44fb4e9...ea55. 1099 `#print axioms` lines: 1059 [propext,
Classical.choice, Quot.sound], 23 [propext, Quot.sound], 10 [propext], 7 none. No `sorryAx`,
`ofReduceBool` or `trustCompiler`. grep of UsdtVerify/ for sorry, admit, axiom declarations,
native_decide, bv_decide, decide +native: none.
Round 39: clean project build (`rm -rf .lake/build`, safe.sh 9G, LEAN_NUM_THREADS not set) 112.63 s
wall, 1790672896 bytes max RSS (/usr/bin/time -l), exit 0, 0 "error:" lines, 1423 jobs, 1071
`#print axioms` lines: 1031 [propext, Classical.choice, Quot.sound], 23 [propext, Quot.sound],
10 [propext], 7 none.
Round 37: clean project build (`rm -rf .lake/build`, safe.sh 9G, LEAN_NUM_THREADS not set) 110.27 s
wall, 1793163264 bytes max RSS (/usr/bin/time -l), exit 0, 0 "error:" lines, 1416 jobs, 995
`#print axioms` lines: 955 [propext, Classical.choice, Quot.sound], 23 [propext, Quot.sound],
10 [propext], 7 none.
Round 36: clean project build (`rm -rf .lake/build`, safe.sh 9G, LEAN_NUM_THREADS not set) 110.28 s
wall, 1812168704 bytes max RSS (/usr/bin/time -l), exit 0, 0 "error:" lines, 1414 jobs, 966
`#print axioms` lines: 926 [propext, Classical.choice, Quot.sound], 23 [propext, Quot.sound],
10 [propext], 7 none.
Round 35: clean project build (`rm -rf .lake/build`, LEAN_NUM_THREADS=2, safe.sh 9G) 142.97 s
wall, 1765408768 bytes max RSS (/usr/bin/time -l), exit 0, 0 "error:" lines, 1407 jobs, 871
`#print axioms` lines: 841 [propext, Classical.choice, Quot.sound], 20 [propext, Quot.sound],
10 [propext].
- Round 34 (tree of commit 5224fdd, rm -rf .lake/build, EthLib oleans prebuilt,
  `lake build UsdtVerify UsdtVerify.Test.Axioms` under `safe.sh -m 9G`): 109.30 s wall, 362.78 s
  user, 1773879296 bytes max RSS (`/usr/bin/time -l`), exit 0, 0 "error:" lines, 1402 jobs. Hash
  check: 11075 bytes, keccak256 b44fb4e9...ea55. `#print axioms`: 847 reports with axioms
  (817 [propext, Classical.choice, Quot.sound], 20 [propext, Quot.sound], 10 [propext]), 7 with
  none; no `sorryAx`, `ofReduceBool` or `trustCompiler`. grep of UsdtVerify/ for sorry, admit,
  axiom declarations, native_decide, bv_decide: none.
- Round 31, after M1 and MirrorState (tree of commit 161d97e, rm -rf .lake/build, EthLib oleans
  prebuilt, LEAN_NUM_THREADS=2, `lake build UsdtVerify UsdtVerify.Test.Axioms`): 137.82 s wall,
  341.04 s user, 1798881280 bytes max RSS, exit 0, 0 "error:" lines, 1400 jobs. Hash check: 11075
  bytes, keccak256 b44fb4e9...ea55. `#print axioms`: 827 with axioms, 6 with none; no sorryAx,
  ofReduceBool or trustCompiler.
- Round 33 (tree of commit 3f3250a, rm -rf .lake/build, EthLib oleans prebuilt,
  LEAN_NUM_THREADS=2, `lake build UsdtVerify UsdtVerify.Test.Axioms` under `safe.sh -m 9G`):
  135.78 s wall, 341.82 s user, 1763753984 bytes max RSS (`/usr/bin/time -l`), exit 0, 0 "error:"
  lines, 1400 jobs. Hash check: 11075 bytes, keccak256 b44fb4e9...ea55. `#print axioms`: 841
  reports, 7 with no axioms, none outside [propext, Classical.choice, Quot.sound], no `sorryAx`.
  grep of UsdtVerify/ for sorry, admit, axiom declarations, native_decide, bv_decide,
  decide +native: none.
- Round 31 (tree of commit 725dd5b, rm -rf .lake/build, EthLib oleans prebuilt,
  LEAN_NUM_THREADS=2, `lake build UsdtVerify UsdtVerify.Test.Axioms`): 135.77 s wall, 340.22 s
  user, 1796440064 bytes max RSS (`/usr/bin/time -l`), exit 0, 0 "error:" lines, 1399 jobs. Hash
  check: 11075 bytes, keccak256 b44fb4e9...ea55. `#print axioms`: 821 reports with axioms, 6 with
  none; none outside [propext, Classical.choice, Quot.sound]. grep of UsdtVerify/ for sorry,
  admit, axiom declarations, native_decide, bv_decide: none.
- Round 27 (tree of commit c7647b1, rm -rf .lake/build, EthLib oleans prebuilt,
  LEAN_NUM_THREADS=2): 136.79 s wall, 330.98 s user, 1788444672 bytes max RSS (`/usr/bin/time -l`),
  exit 0, 0 "error:" lines, 0 warnings other than the module-system notes, lake counter [1392/1393].
  Hash check: 11075 bytes, keccak256 b44fb4e9...ea55. `#print axioms`: 692 [propext,
  Classical.choice, Quot.sound], 6 [propext, Quot.sound], 7 [propext], 3 with no axioms (708).
  grep of UsdtVerify/ for sorry, admit, axiom declarations, native_decide, bv_decide,
  decide +native, maxHeartbeats, maxRecDepth: none.
- Round 26, second part (tree of commit 4413e35, rm -rf .lake/build, EthLib oleans prebuilt,
  LEAN_NUM_THREADS=2): 135.76 s wall, 334.81 s user, 1774419968 bytes max RSS (`/usr/bin/time -l`),
  exit 0, 0 "error:" lines, 1393 jobs. `#print axioms`: 648 [propext, Classical.choice,
  Quot.sound], 5 [propext, Quot.sound], 6 [propext], 3 with no axioms (662). grep of the changed
  files for sorry, admit, axiom declarations, native_decide, bv_decide, decide +native,
  maxHeartbeats, maxRecDepth: none.
- Round 26 (tree of commit 0efce8e, rm -rf .lake/build, EthLib oleans prebuilt, LEAN_NUM_THREADS=2): 138 s wall, exit 0, 0 "error:" lines.
- Round 25 (tree of commit 0f5fb8b, rm -rf .lake/build, EthLib oleans prebuilt): 102.14 s wall,
  336.50 s user, 1776189440 bytes max RSS (`/usr/bin/time -l`), exit 0, 0 "error:" lines, 1392
  jobs. `#print axioms`: 568 [propext, Classical.choice, Quot.sound], 5 [propext, Quot.sound],
  5 [propext], 3 with no axioms (581). grep of the new files for sorry, admit, axiom declarations,
  native_decide, bv_decide, decide +native, maxHeartbeats, maxRecDepth: none.
- Round 24 (tree of commit 2969de2 plus the round-24 docs, rm -rf .lake/build, EthLib oleans
  prebuilt): 124.57 s wall, 310.57 s user, 1785806848 bytes max RSS (`/usr/bin/time -l`), exit 0,
  0 "error:" lines, 1383 jobs. `#print axioms`: 480 [propext, Classical.choice, Quot.sound],
  5 [propext, Quot.sound], 5 [propext], 3 with no axioms (493).
- Round 23 (tree of commit c5d8090 plus the round-23 docs, rm -rf .lake/build, EthLib oleans
  prebuilt): 118.52 s wall, 303.37 s user, 1798701056 bytes max RSS (`/usr/bin/time -l`), exit 0,
  0 "error:" lines, 1375 jobs; `#print axioms`: 441 [propext, Classical.choice, Quot.sound],
  4 [propext, Quot.sound], 5 [propext], 1 with no axioms (451). Hash check: 11075 bytes,
  keccak256 b44fb4e9...ea55. grep of UsdtVerify/ for sorry, admit, native_decide, bv_decide,
  decide +native, axiom declarations: none.
- Round 21 (after commit c4094b2, rm -rf .lake/build, EthLib oleans prebuilt): 112.38 s wall,
  298.17 s user, 1755627520 bytes max RSS (`/usr/bin/time -l`), exit 0, 0 "error:" lines, 1367
  jobs (fewer modules after the merges); `#print axioms`: 398 [propext, Classical.choice,
  Quot.sound], 4 [propext, Quot.sound], 5 [propext], 1 with no axioms (408, as in round 20).
  The max RSS is above round 19's 1432436736 bytes: the merged files are larger.
  grep for sorry, admit, axiom declarations, native_decide, bv_decide, decide +native: none.
- Round 19 (after commit 776ae79, rm -rf .lake/build, EthLib oleans prebuilt): 126.69 s wall,
  1432436736 B max RSS, exit 0, 1384 jobs; `#print axioms`: 396 with [propext, Classical.choice,
  Quot.sound], 4 with [propext, Quot.sound], 5 with [propext], 1 with none.
- Round 18 (after commit 8f76073, rm -rf .lake/build, EthLib oleans prebuilt): 125.64 s wall,
  286.32 s user, 1408958464 bytes max RSS (`/usr/bin/time -l`), exit 0, 0 "error:" lines, 1383
  jobs; `#print axioms`: 392 [propext, Classical.choice, Quot.sound], 2 [propext, Quot.sound],
  2 [propext], 1 with no axioms.
- Round 17 (after commit e6d4b71, rm -rf .lake/build, EthLib oleans prebuilt): 123.62 s wall,
  277.07 s user, 1421475840 bytes max RSS (`/usr/bin/time -l`), exit 0, 0 "error:" lines, 1380
  jobs; `#print axioms`: 367 [propext, Classical.choice, Quot.sound], 2 [propext, Quot.sound],
  2 [propext], 1 with no axioms.
- Round 16 (after commit e70c18b, rm -rf .lake/build, EthLib oleans prebuilt): 131.21 s wall,
  294.41 s user, 1425702912 bytes max RSS (`/usr/bin/time -l`), exit 0, 0 "error:" lines, 1369
  jobs; `#print axioms`: 357 [propext, Classical.choice, Quot.sound], 2 [propext, Quot.sound],
  1 [propext], 1 with no axioms.
- Round 10 (after commit 7a82207, rm -rf .lake/build): 112.36 s wall, 1409957888 bytes max RSS
  (`/usr/bin/time -l`), exit 0, 1347 jobs, 221 `#print axioms`, all [propext, Classical.choice,
  Quot.sound].
Round 9, with the fallback (Usdt/Spec/Dispatch.lean, 120 lines): clean project build 119.67 s wall,
1345945600 bytes max RSS, exit 0, 0 "error:" lines, 1344 jobs, 170 `#print axioms`, all
[propext, Classical.choice, Quot.sound].
Round 9, with deprecated allowance (Usdt/Spec/Deprecated/Allowance.lean, 785 lines): clean project build
110.45 s wall, 1353220096 bytes max RSS, exit 0, 0 "error:" lines, 1343 jobs, 166
`#print axioms`, all [propext, Classical.choice, Quot.sound].
Round 9, with name()/symbol() (Usdt/Spec/Strings.lean, 958 lines): clean project build 100.12 s wall,
1343651840 bytes max RSS, exit 0, 0 "error:" lines, 1342 jobs, 160 `#print axioms`, all
[propext, Classical.choice, Quot.sound].
Round 9, re-pin to fd3457dbf alone: clean project build (`rm -rf .lake/build`) 103.21 s wall,
1342636032 bytes max RSS (/usr/bin/time -l), exit 0, 0 "error:" lines, 1340 jobs, 153
`#print axioms` (the two of the deleted local EXTCODESIZE/GAS rules removed), all
[propext, Classical.choice, Quot.sound].
Round 8 (pin d4d422780, unchanged): clean project build (`rm -rf .lake/build`) 103.12 s wall,
1342144512 bytes (1280 MiB) max RSS (/usr/bin/time -l), exit 0, 0 "error:" lines, 1342 jobs,
155 `#print axioms`, all [propext, Classical.choice, Quot.sound]. New files of round 8 (DestroySpec, Getters, GettersMap, MemRev, RunFrames): 2488 lines (wc -l).
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
