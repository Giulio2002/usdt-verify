# What is proved about the deployed USDT bytecode

This is a summary for a human reader. The Lean theorems are the reference; this page claims only
what they state. Theorem names in parentheses; the one-place index is `UsdtVerify/Summary.lean`.

## The object

- The runtime bytecode of TetherToken (USDT) on Ethereum mainnet: 11,075 bytes, read at block
  26362952 (`data/usdt.runtime.hex`, provenance in `data/SOURCE.md`).
- The Lean constant `CODE` holds those bytes. A build-time check (`UsdtVerify/Test/Hash.lean`)
  compares `CODE` with the hex file and its keccak256 with `b44fb4e9…ea55`. The interpreter runs
  this check; it is a test, not a kernel-checked theorem.
- The semantics is EthLib's EVM model (pinned commit fd3457dbf), with its program logic and the
  one-counter gas meter. Forks: Berlin onwards, and before Glamsterdam where storage is written or a
  call is made.

## What a theorem says

Each theorem starts from a fresh call frame running `CODE` at pc 0. Under the stated hypotheses on
the call data, the call value, the storage words read and the gas, every run reaches the stated
end frame. Every theorem from pc 0 is also given for the real interpreter loop `runFrame`, for every gas
bound and every message runner (`runFrame_*`).

The end frames are:
- a normal halt: RETURN with the given bytes, or STOP with an empty output;
- REVERT with empty output;
- an exceptional halt with INVALID (0xfe): a failed SafeMath `assert`. No gas is left and the
  caller discards the state.

Gas left, the storage writes (in order), the logs, and the accessed slots and addresses are exact
(EIP-2929 cold and warm prices, EIP-2200/3529 SSTORE prices and refunds).

## Functions covered

- **totalSupply(), balanceOf(who)**, when not deprecated: they return slot 1, or
  `balances[who]` (slot `keccak(who ++ 2)`).
- **transfer(to, v)**:
  - Reverts: when paused, when the caller is blacklisted, and when the call data is shorter than
    68 bytes.
  - INVALID: when `v * basisPointsRate` overflows, when fee > v, when the balance is too low, and
    when the recipient's or the owner's credit overflows.
  - Success with fee 0 and with fee > 0: the exact balance writes and `Transfer` logs.
  - `transfer` checks only the sender's blacklist status, not the recipient's.
- **approve(s, v)**: v = 0; v ≠ 0 over a zero allowance; the revert when v ≠ 0 and the
  allowance is nonzero; and the revert when the call data has fewer than 68 bytes.
- **transferFrom(f, t, v)**:
  - Reverts: when paused, when `f` is blacklisted, and when the call data is short.
  - Every INVALID case, as for transfer, plus an allowance below `v`.
  - Success with fee 0 and with fee > 0, including the `MAX_UINT` allowance that is never
    decreased.
- **Local conservation** (`*_conserves`): on each success path of transfer and transferFrom, the
  integer changes of the balance slots that the path writes sum to zero:
  - the payer changes by −v;
  - the payee changes by +(v − fee);
  - the owner changes by +fee.

  These theorems take as hypotheses that the slots are pairwise distinct, and distinct from slot 0
  and from the allowance slot where needed. The slots are keccak outputs, and their distinctness is
  assumed, not proved.
- **Deprecated totalSupply / balanceOf** (`Deprecated*.lean`). When the `deprecated` flag is set,
  USDT forwards the call to the address stored in slot 10. The theorems hold for every callee
  behaviour that meets a stated assumption, through EthLib's callee abstraction. USDT then:
  - sends exactly one message to the upgraded address, with no value and with the call data
    `0x18160ddd`, or `0x70a08231 ++ who` for balanceOf;
  - returns the first word of the callee's output if the callee succeeds;
  - reverts with empty output if the callee fails;
  - reverts before any call if the address has no code.

  `runFrame_dep_process` instantiates this with EthLib's own message runner: for any code at the
  upgraded address that has a proved specification, the run returns that code's answer, unless the
  runner aborts.
- **Deprecated transfer / approve / transferFrom** (`DeprecatedTransfer.lean`,
  `DeprecatedTransferFrom.lean`). The same callee abstraction. With the flag set (and, for transfer,
  not paused and the caller not blacklisted; for transferFrom, not paused and `f` not blacklisted;
  for approve, call data of at least 68 bytes), USDT:
  - sends exactly one message to the upgraded address, with no value, no output range, and the
    call data `0x6e18980a ++ caller ++ to ++ v` (`transferByLegacy`),
    `0xaee92d33 ++ caller ++ s ++ v` (`approveByLegacy`) or
    `0x8b477adb ++ caller ++ f ++ t ++ v` (`transferFromByLegacy`), each argument a 32-byte word,
    the addresses masked to 160 bits;
  - stops (STOP, no error) if the callee succeeds, with the state and substate that the callee's
    frame leaves (`incorporateChild`);
  - reverts with empty output if the callee fails;
  - reverts before any call if the address has no code.

  On this path transfer and transferFrom need only 4 bytes of call data: the payload-size checks
  live in BasicToken and StandardToken, which the deprecated path does not reach. Nothing is
  assumed or proved about what the upgraded contract does with the call (for example which
  balances it changes): that is the callee's behaviour, which the theorems leave open.
  `runFrame_dep{T,A,F}_process`: with EthLib's own runner, for any code at the upgraded address
  with a proved specification whose runs end with no error, the run stops with no error, unless the
  runner aborts.
- **Deprecated allowance(owner, spender)** (`DeprecatedAllowance.lean`). The same callee
  abstraction. With the flag set, USDT:
  - sends exactly one message to the upgraded address, with no value and the call data
    `0xdd62ed3e ++ owner ++ spender` (68 bytes, the addresses masked to 160 bits), with an output
    range of 32 bytes;
  - returns the first word of the callee's output if the callee succeeds with at least 32 bytes
    of output;
  - reverts with empty output if the callee fails;
  - reverts before any call if the address has no code.

  `runFrame_depAl_process` instantiates this with EthLib's own message runner, as for balanceOf.

- **A call that names no function** (`Fallback.lean`). TetherToken has no fallback function.
  - With at least 4 bytes of call data whose first four are not the selector of any of the 32
    functions, the run reverts with empty output, leaves the state and substate unchanged, and
    uses exactly 773 gas.
  - With fewer than 4 bytes of call data, the run reverts the same way after 46 gas.
  - Neither path checks the call value.

- **Nonzero call value** (`Nonpayable.lean`, `nonpayable`). All 32 functions are nonpayable. For
  every entry `i` of the selector table, a call whose selector is the key of entry `i` and whose
  value is not 0 reverts with empty output before reading storage: the state and substate are
  unchanged and the run uses exactly `87 + 22 * (i + 1)` gas.

- **The owner check** (`Owner.lean`). Every owner function starts with an inlined copy of
  `require(msg.sender == owner)`, where `owner` is the low 160 bits of slot 0. One pair of
  theorems covers all ten copies: if the caller is the owner the run goes on, and otherwise it
  reverts with empty output after reading slot 0.
- **pause() and unpause()** (`PauseSpec.lean`). `paused` is byte 20 of slot 0.
  - A caller that is not the owner gets a revert with empty output.
  - `pause()` reverts when already paused, and `unpause()` reverts when not paused.
  - On success the run stops after exactly one storage write, to slot 0. The new word has byte
    20 set to 1 (pause) or 0 (unpause), and every other bit unchanged, so the owner is unchanged
    too. One log is appended, with the topic of `Pause()` or `Unpause()` and no data. The gas is
    exact.
- **addBlackList(a) and removeBlackList(a)** (`BlackListSpec.lean`). `isBlackListed[a]` is the low
  byte of slot `keccak(a ++ 6)`.
  - A caller that is not the owner gets a revert with empty output.
  - The owner's call stops after exactly one storage write, to that slot. The low byte becomes 1
    (add) or 0 (remove), and the other bits are unchanged. Every other slot is unchanged. One log
    is appended: `AddedBlackList(a)` or `RemovedBlackList(a)`, with `a` as its data word. The old
    flag is not read, so adding twice or removing an absent address also succeeds. The gas is
    exact.
- **issue(a) and redeem(a)** (`IssueSpec.lean`). `_totalSupply` is slot 1 and `balances[owner]`
  is slot `O = keccak(owner ++ 2)`.
  - A caller that is not the owner gets a revert with empty output.
  - `issue` reverts unless `0 < a` and neither `_totalSupply + a` nor `balances[owner] + a`
    reaches 2^256. In particular `issue(0)` reverts. `redeem` reverts when `a` exceeds
    `_totalSupply` or `balances[owner]`.
  - On success, the run stops after exactly two storage writes and one log:
    - `issue` writes `balances[owner] + a`, then `_totalSupply + a`, and logs `Issue(a)`.
    - `redeem` writes `_totalSupply - a`, then `balances[owner] - a`, and logs `Redeem(a)`.
  - Assuming `O ≠ 1`, the new words are these sums and differences as plain numbers, and every
    other slot is unchanged. The gas is exact.
- **setParams(b, m)** (`SetParamsSpec.lean`). `basisPointsRate`, `maximumFee` and `decimals`
  are slots 3, 4 and 9.
  - A caller that is not the owner gets a revert with empty output. The owner's call reverts
    when `b ≥ 20`, or when `b < 20` and `m ≥ 50`.
  - Otherwise, if `m * 10^decimals < 2^256`, the run stops after writing `b` to slot 3 and
    `m * 10^decimals` to slot 4. Every other slot is unchanged. One log `Params(b, f)` is
    appended, with the two new words as data. The gas is exact.
  - When that product overflows (it needs `decimals ≥ 75`), SafeMath's assert ends the run in
    INVALID (`SetParamsSpec.spec_mulOv`, round 13).
- **deprecate(a) and transferOwnership(a)** (`AddrWriteSpec.lean`).
  - A caller that is not the owner gets a revert with empty output.
  - `deprecate` stops after two writes of slot 10. Afterwards `deprecated` (byte 20) is 1,
    `upgradedAddress` (the low 160 bits) is `a`, and every other slot is unchanged. One log
    `Deprecate(a)` is appended.
  - `transferOwnership(0)` stops without writing anything. For `a ≠ 0` it stops after one write
    of slot 0. Afterwards the owner is `a`, `paused` is unchanged, and so is every other slot.
    No log is emitted (Ownable has no event here).
  - The gas is exact.
- **destroyBlackFunds(a)** (`Destroy.lean`, `DestroySpec.lean`). `B` is the slot of
  `balances[a]` and `d` its word.
  - A caller that is not the owner gets a revert, and so does the owner when `a` is not
    blacklisted.
  - When the owner calls it, `a` is blacklisted and the contract is not deprecated, the code
    reads `d` through TetherToken's own `balanceOf` getter (an internal call). The run then stops
    after exactly two storage writes and one log:
    - it writes 0 to `B`, then `_totalSupply - d` to slot 1 (an unchecked subtraction, with
      `_totalSupply` read after the first write);
    - it logs `DestroyedBlackFunds(a, d)`, with the address word and `d` as data.
  - Assuming `B ≠ 1`, `B` is then 0, slot 1 is `_totalSupply - d` as a word (and as a number
    when `d ≤ _totalSupply`), and every other slot is unchanged. The gas is exact.
  - When the contract is deprecated (`DeprecatedDestroy.lean`), the getter does not read `B`.
    It sends the upgraded address `ua` one message with no value and the data
    `0x70a08231 ++ a` (`balanceOf(a)`). The theorem holds for every callee behaviour that meets
    a stated assumption: when the call ends with no error, the contract's account still exists
    in the state the call left. It also needs at least 47,881 gas left after the price of the
    CALL (`TAIL_MAX`, enough for both writes at their highest price).
    - If the call fails, the run reverts with no output.
    - If it succeeds, let `S` be the state the call left and `d` the first word of the reply
      (the word at 0x60 after the copy). The run stops after writing 0 to `B` and then
      `_totalSupply - d` (unchecked) to slot 1 of this contract, both over `S`, and logs
      `DestroyedBlackFunds(a, d)`. The gas is exact.
    - So `_totalSupply` drops by the balance that the upgraded contract reports, while the local
      `balances[a]` is set to 0 whatever it held.
    - If `ua` has no code, the run reverts before any call. The interpreter's own message runner
      is covered for an upgraded code with a proved specification.

- **The getters** (`Getters.lean`, `GettersMap.lean`). Each call with no value returns exactly
  32 bytes, writes nothing, and reads only the slots named; the gas is exact.
  - `decimals()`, `maximumFee()`, `_totalSupply()`, `basisPointsRate()` return the word of
    slot 9, 4, 1 and 3. `MAX_UINT()` returns 2^256 − 1 and reads nothing.
  - `deprecated()` and `paused()` return 1 if byte 20 of slot 10 (resp. slot 0) is nonzero,
    and 0 otherwise.
  - `upgradedAddress()` returns the low 160 bits of slot 10; `owner()` and `getOwner()` the low
    160 bits of slot 0.
  - `balances(a)` returns `balances[a]`, the same slot as `balanceOf`, with no deprecation
    check. `isBlackListed(a)` and `getBlackListStatus(a)` return 1 if the low byte of
    `isBlackListed[a]` is nonzero, and 0 otherwise.
  - `allowed(a0, a1)` returns `allowed[a0][a1]`; `allowance(a0, a1)`, when not deprecated,
    returns the same word after reading slot 10.
- **name() and symbol()** (`Strings.lean`). They read the string in slot 7 (name) or slot 8
  (symbol). The theorems cover a string of 1 to 31 bytes in Solidity's short form: the bytes
  from the top of the slot word, and the low byte equal to twice the length `n`.
  - The call returns 96 bytes, the ABI encoding of a string: the word 0x20, the word `n`, and a
    word holding the first `n` bytes of the slot word followed by zeros.
  - The run goes through the code's copy loop once and through its padding branch. It reads
    the slot three times, writes nothing, and the gas is exact.
  - For the slot words of "Tether USD" and "USDT", the third word is the UTF-8 bytes of the
    string followed by zero bytes (`spec_name_tether`, `spec_symbol_usdt`).
  - The empty string (`StringsGen.lean`; the low byte of the slot is 0): the call returns
    64 bytes, the word 0x20 and the word 0. It reads the slot twice, writes nothing, and the gas
    is exact.
  - The long form (`StringsGen.lean`): the slot word is odd and `N` = word / 2 is at least 32.
    Solidity stores such a string from slot `keccak(k)` on. The call returns the word 0x20, the
    word `N`, then the words of the slots `keccak(k) + i` for i < ceil(N / 32). The last word
    keeps only its first `N mod 32` bytes followed by zeros, when `N` is not a multiple of 32.
    The run goes through the code's two copy loops (storage to memory, then memory to memory)
    and reads each data slot once. The gas is exact, with the price of each data read cold or
    warm. A bound `N < 2^180` is a hypothesis.
  - Together these cover every slot word that Solidity writes for a string. Odd words with
    `word / 2 < 32` are not covered; Solidity never writes them.

- **The global invariant** (`Invariant.lean`). `Inv` says that the sum of `balances[a]` over all
  2^160 addresses equals `_totalSupply` (slot 1), both read from the contract's storage.
  - The theorems assume `KeccakSep`, a stated hypothesis about keccak that is not proved:
    - distinct addresses have distinct balance slots;
    - a balance slot is none of the fixed slots 0 to 10, and no slot of `isBlackListed` or
      `allowed`;
    - slot 1 is no slot of `isBlackListed` or `allowed`.
  - Under it, and when the contract is not deprecated, the end state of each proved success
    path keeps `Inv`, with the same no-wrap hypotheses that the path's specification already
    makes. The paths are transfer and transferFrom (with fee 0 and with a fee), approve, pause,
    unpause, transferOwnership, addBlackList, removeBlackList, setParams, deprecate, issue,
    redeem and destroyBlackFunds. The read-only functions only record reads.
  - destroyBlackFunds subtracts `d = balances[a]` from `_totalSupply` without a check. Under
    `Inv`, `d` is one term of the sum, so `d ≤ _totalSupply`, the subtraction does not wrap, and
    `Inv` still holds after it.
  - `steps_inv` lifts the invariant to any finite sequence of these steps.
  - That these paths are all the successful runs of a call, when not deprecated, is proved in
    round 13 (`ok_*`, and `inv_call` below). Nothing is proved here about the deprecated paths.

## Completeness of the dispatcher, for every gas

- `runFrame_ok_dispatch` (`UsdtVerify/Complete/Dispatch.lean`, alias `Summary.dispatch_complete`):
  from Berlin, a fresh frame of `CODE` at pc 0 with call data of size below 2^256, any gas, any
  gas bound and any message runner. If the interpreter loop ends with no error, then:
  - the call data has at least 4 bytes;
  - its selector is the key of one of the 32 entries of the table;
  - the call value is 0.
- Out of gas is included. `Gas.SpecG.low` says: if a run with `k` more gas follows the steps of
  a specification, then a run with less gas that ends with no error ends in the same frame, with
  exactly `k` less gas left. The specifications used for this are re-proved over `Gas.StepG`
  (steps from frames whose instruction gives the same result with more gas, or fails with less;
  GAS and the calls are not such instructions).
- Every specification of a non-deprecated path is now stated over `StepG` (round 12), so the
  same argument applies to each function. Proved so far: totalSupply(), balanceOf(address) and
  transfer(address,uint256), when the contract is not deprecated. For each, every run that
  ends with no error, with any gas, is one of the proved success paths, with the exact output,
  gas left, state and substate. For transfer, the run also passed every check (paused,
  blacklist, payload size, the SafeMath overflows, the balance), and it is the fee-0 path or
  the fee path. Its hypotheses: Berlin ≤ fork < Glamsterdam, the frame not static, the contract
  has an account.
- Round 13 adds the same for approve(address,uint256) and transferFrom(address,address,uint256)
  (not deprecated), and for the owner functions pause, unpause, addBlackList, removeBlackList,
  issue, redeem, setParams, deprecate, transferOwnership and destroyBlackFunds (the last not
  deprecated). Each conclusion lists the checks the run passed (for the owner functions: the
  caller is the owner, and each `require`). Two new specifications were needed to exclude
  cases: approve with call data shorter than 68 bytes reverts (`Approve.spec_payload`), and
  setParams with `m * 10^d ≥ 2^256` ends in INVALID (`SetParamsSpec.spec_mulOv`).
  Hypotheses: Berlin ≤ fork < Glamsterdam, the frame not static, the contract has an account,
  call data below 2^256 bytes, and not deprecated for approve, transferFrom, destroyBlackFunds.
- Round 13 also covers every getter (allowance: not deprecated) and name() / symbol(). For
  name and symbol the slot word must have one of the shapes Solidity writes (`StrForm`: empty,
  1 to 31 bytes in the short form, or the long form with a length below 2^180); this is a named
  hypothesis, since the other words have no specification.
- **The invariant over every successful call, not deprecated** (`Complete.inv_call`,
  `UsdtVerify/Complete/Inv.lean`). From Berlin to before Glamsterdam, take a fresh frame of the deployed
  code at pc 0, with any call data below 2^256 bytes, any value, any gas, any gas bound and any
  message runner. Assume:
  - `KeccakSep` (keccak keeps the storage slots apart; not proved);
  - the frame is not static, and the contract has an account;
  - the contract is not deprecated (byte 20 of slot 10 is 0);
  - slots 7 and 8 hold strings in a form Solidity writes (`StrForm`);
  - `Inv`: the sum of the 2^160 balances equals `_totalSupply` at the start.
  If the interpreter loop ends with no error, `Inv` holds in the end state.
- Deprecated totalSupply() (`Complete.dep_totalSupply_complete`, round 14), for any gas, any gas
  bound and ANY message runner (nothing is assumed of the runner). Every run that ends with no
  error is the forward to the upgraded address:
  - the runner was called with the `Forwarded` message and returned a frame with no error;
  - the run returns the word at 0x60 after the CALL wrote the start of that frame's output;
  - the gas left is exact, and the state and substate are those after the call.
  Assumed by name: the upgraded account's code is found in the state (`hcode`), and from Pectra
  it is no delegation (`hdel`). Too little gas at EXTCODESIZE, GAS, SUB, CALL or after the call,
  no code, and the greatest depth are proved to end with an error.
- Deprecated balanceOf(address) (`Complete.dep_balanceOf_complete`, round 14): the same
  statement, for the forward of `balanceOf(a)` (data: the selector, then the word of `a`), with
  the same named hypotheses.
- Deprecated transfer, approve and transferFrom (`Complete.dep_transfer_complete`,
  `dep_approve_complete`, `dep_transferFrom_complete`, round 15), for any gas, any gas bound and
  any runner. Every run that ends with no error passed the checks before the forward (transfer
  and transferFrom: not paused, and the caller or `_from` not blacklisted; approve: at least 68
  bytes of call data). The runner was called with the forward (`transferByLegacy`,
  `approveByLegacy`, `transferFromByLegacy` with the caller as first argument) and returned a
  frame with no error. The run stopped with no output, with the exact gas, and the state and
  substate are those after the call. The same named hypotheses `hcode` and `hdel`.
- Deprecated allowance(address,address) (`Complete.dep_allowance_complete`, round 15): the
  statement of balanceOf, for the forward of `allowance(owner, spender)`.
- Not yet proved: the same completeness for deprecated destroyBlackFunds (the part
  from EXTCODESIZE to after the CALL, `Complete.fromExt`, is proved for the call inside
  destroyBlackFunds), and so the invariant over every deprecated call.

## The invariant when deprecated: destroyBlackFunds (round 14)

`UsdtVerify/Complete/DepInv.lean`. When deprecated, `destroyBlackFunds(a)` asks the upgraded
contract for `balanceOf(a)`, gets a word `d`, and then, in this contract, sets `balances[a]` to 0
and `_totalSupply` to `_totalSupply - d` (no overflow check). Write `S` for the state the call
left. The callee may call back into this contract, so `S` can differ from the start state.

- `inv_tail_iff`: assume `KeccakSep`, the contract `C` has an account in `S`, `a` is below 2^160,
  and `Inv C S`. Then `Inv` holds after the two writes if and only if `d` equals `balances[a]` in
  `S`.
- `exists_breaks`: a concrete counterexample, assuming `KeccakSep`. The state is `zeroState C`:
  an empty account at `C` and no storage word set, so every word is 0 and `Inv` holds. With
  `a = 0` and the answer `d = 1`, `Inv` fails after the writes.
- `depD_breaks` is the same at the level of runs. Assume the hypotheses of `spec_depD` and
  `KeccakSep`, `Inv` at the start, and these callee hypotheses:
  - `hans`: the callee succeeds and answers an output `o` of at least 32 bytes;
  - `hsame`: it keeps the contract's account and every word of the contract's storage;
  - `hne`: the first word of `o` is not `balances[a]` at the start.
  Then under every runner that meets the callee assumption, the run ends with no error and `Inv`
  false, or the runner aborts. No concrete runner, message and state that meet all of these
  hypotheses at once is constructed.
- `depD_inv` assumes the hypotheses of `spec_depD`, `KeccakSep`, and a callee hypothesis
  `hcallee`: a successful forwarded call leaves the contract's account and `Inv`. It covers
  anything the callee does, including calls back into this contract. A run that ends with no
  error ends in `tailState S C a d` with `Inv C S`, and there `Inv` holds iff `d = balances[a]`
  in `S`. `depD_keeps` adds `hans`, that the answer is the local balance in the callee's end
  state, and concludes `Inv` at the end.
- So the invariant is not kept by deprecated `destroyBlackFunds` in general. It is kept exactly
  when the upgraded contract reports the balance that this contract stores.

## What is trusted

- The Lean 4 kernel (v4.35.0).
- The three standard axioms that `#print axioms` reports for every main theorem: `propext`,
  `Classical.choice` and `Quot.sound`. There is no `sorry`, no new axiom, and no `native_decide`
  or `bv_decide`. `decide +kernel` is used, and it is checked by the kernel.
- EthLib's EVM model is a faithful EVM. The proofs are only as good as that model.
- The bytecode file is the deployed code. The interpreted hash check ties `CODE` to the file,
  and `data/SOURCE.md` ties the file to the chain.
- A few generic opcode rules are proved locally in this repository, and EthLib's model is not
  modified. These rules are EXP with its price worked out and some instruction table
  entries (`UsdtVerify/Local/`). STOP, GAS and EXTCODESIZE now come from EthLib. They are proved from EthLib's semantics, not assumed.

## What is not covered

- That the proved success paths are all the successful runs of a call, for the deprecated
  paths, and name/symbol on slot words outside `StrForm`; the invariant over every deprecated
  call (destroyBlackFunds can break it, see above).
- `KeccakSep` (a hypothesis of the invariant theorems, about keccak).
- Runs that run out of gas below the stated bounds, except at the dispatcher (see above).
- Forks before Berlin, and Glamsterdam onwards on the writing and calling paths.
