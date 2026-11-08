# What is proved about the deployed USDT bytecode

This is a summary for a human reader. The Lean theorems are the reference; this page claims only
what they state. Theorem names in parentheses; the one-place index is `UsdtVerify/Summary.lean`;
the folders are described in `docs/LAYOUT.md`.

## The object

- The runtime bytecode of TetherToken (USDT) on Ethereum mainnet: 11,075 bytes, read at block
  26362952 (`data/usdt.runtime.hex`, provenance in `data/SOURCE.md`).
- The Lean constant `CODE` holds those bytes. A build-time check (`UsdtVerify/Test/Hash.lean`)
  compares `CODE` with the hex file and its keccak256 with `b44fb4e9…ea55`. The interpreter runs
  this check; it is a test, not a kernel-checked theorem.
- The semantics is EthLib's EVM model (pinned commit fd3457dbf), with its program logic and the
  one-counter gas meter. Forks: Berlin onwards, Glamsterdam included. Since round 17 the paths
  that write storage hold at Glamsterdam (each SSTORE costs `writeCost`, EthLib's `sstoreCost`
  plus its state gas of a new slot). Since round 19 the paths that make a call (deprecated) hold
  there too: EXTCODESIZE costs `extCost fork` (EthLib's `externalBaseCost`: 2600 cold / 100 warm
  before Glamsterdam, the access plus 100 from Glamsterdam, EIP-8038), an account access costs
  `accCost fork` (cold 2600, 3000 from Glamsterdam), and the CALL rules follow EthLib's order of
  the charges at Glamsterdam. Before Glamsterdam these prices are the old ones (`extCost_of_lt`,
  `accCost_of_lt`, `TAIL_MAX_of_lt`).

## What a theorem says

Each theorem starts from a fresh call frame running `CODE` at pc 0. Under the stated hypotheses on
the call data, the call value, the storage words read and the gas, every run reaches the stated
end frame. Every theorem from pc 0 is also given for the real interpreter loop `runFrame`, for every gas
bound and every message runner (`runFrame_*`).

The end frames are:
- a normal halt: RETURN with the given bytes, or STOP with an empty output;
- REVERT with empty output;
- an exceptional halt with INVALID (0xfe): a failed SafeMath `assert`, with no output and no gas
  left. The theorems state the frame's end; that the caller then discards the state is the
  message layer, outside them.

Gas left, the storage writes (in order), the logs, and the accessed slots and addresses are exact
(EIP-2929 cold and warm prices; SSTORE prices and refunds by EIP-2200 with EIP-2929's prices
from Berlin, and EIP-3529's refunds from London, as EthLib's model computes them).

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
- **Deprecated totalSupply / balanceOf** (`Usdt/Spec/Deprecated/TotalSupply.lean`, `BalanceOf.lean`). When the `deprecated` flag is set,
  USDT forwards the call to the address stored in slot 10. The theorems hold for every callee
  behaviour that meets a stated assumption, through EthLib's callee abstraction. These forward
  specifications (and those below, for the other deprecated functions) take the code `c` of the
  upgraded address as a hypothesis, with `0 < |c|`, and the route `r` of the CALL (`Routes`): no
  delegation, or, from Pectra, an EIP-7702 delegate `d` whose code is found (round 17: before, the
  hypothesis `hdel` excluded delegation). Along a delegated route the CALL also pays the access to
  `d`, and the message runs the code of `d` at `d`, with the upgraded address as its current
  target. The completeness theorems further down take neither the code nor the route as a
  hypothesis. USDT then:
  - sends exactly one message to the upgraded address, along the route, with no value and with the call data
    `0x18160ddd`, or `0x70a08231 ++ who` for balanceOf;
  - if the callee succeeds, returns the word at 0x60 after the first `min 32 |output|` bytes of
    its output are copied there (the first output word when the output has at least 32 bytes);
  - reverts with empty output if the callee fails;
  - reverts before any call if the address has no code.

  `runFrame_dep_process` instantiates this with EthLib's own message runner: for any code of the
  route whose specification ends with no error and a fixed output `o` of at least 32 bytes, with
  the route's address not a precompile and the forwarded message meeting the specification's
  precondition, the run returns the first word of `o`, unless the runner aborts.
- **Deprecated transfer / approve / transferFrom** (`Usdt/Spec/Deprecated/Transfer.lean`,
  `TransferFrom.lean`). The same callee abstraction. With the flag set (and, for transfer,
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
- **Deprecated allowance(owner, spender)** (`Usdt/Spec/Deprecated/Allowance.lean`). The same callee
  abstraction. With the flag set, USDT:
  - sends exactly one message to the upgraded address, with no value and the call data
    `0xdd62ed3e ++ owner ++ spender` (68 bytes, the addresses masked to 160 bits), with an output
    range of 32 bytes;
  - returns the first word of the callee's output if the callee succeeds with at least 32 bytes
    of output;
  - reverts with empty output if the callee fails;
  - reverts before any call if the address has no code.

  `runFrame_depAl_process` instantiates this with EthLib's own message runner, as for balanceOf.

- **A call that names no function** (`Usdt/Spec/Dispatch.lean`). TetherToken has no fallback function.
  - With at least 4 bytes of call data whose first four are not the selector of any of the 32
    functions, the run reverts with empty output, leaves the state and substate unchanged, and
    uses exactly 773 gas.
  - With fewer than 4 bytes of call data, the run reverts the same way after 46 gas.
  - Neither path checks the call value.

- **Nonzero call value** (`Usdt/Spec/Dispatch.lean`, `nonpayable`). All 32 functions are nonpayable. For
  every entry `i` of the selector table, a call whose selector is the key of entry `i` and whose
  value is not 0 reverts with empty output before reading storage: the state and substate are
  unchanged and the run uses exactly `87 + 22 * (i + 1)` gas.

- **The owner check** (`Usdt/Proofs/Owner.lean`). Every owner function starts with an inlined copy of
  `require(msg.sender == owner)`, where `owner` is the low 160 bits of slot 0. One pair of
  theorems covers all ten copies: if the caller is the owner the run goes on, and otherwise it
  reverts with empty output after reading slot 0.
- **pause() and unpause()** (`Usdt/Spec/Pause.lean`). `paused` is byte 20 of slot 0.
  - A caller that is not the owner gets a revert with empty output.
  - `pause()` reverts when already paused, and `unpause()` reverts when not paused.
  - On success the run stops after exactly one storage write, to slot 0. The new word has byte
    20 set to 1 (pause) or 0 (unpause), and every other bit unchanged, so the owner is unchanged
    too. One log is appended, with the topic of `Pause()` or `Unpause()` and no data. The gas is
    exact.
- **addBlackList(a) and removeBlackList(a)** (`Usdt/Spec/BlackList.lean`). `isBlackListed[a]` is the low
  byte of slot `keccak(a ++ 6)`.
  - A caller that is not the owner gets a revert with empty output.
  - The owner's call stops after exactly one storage write, to that slot. The low byte becomes 1
    (add) or 0 (remove), and the other bits are unchanged. Every other slot is unchanged. One log
    is appended: `AddedBlackList(a)` or `RemovedBlackList(a)`, with `a` as its data word. The old
    flag is not read, so adding twice or removing an absent address also succeeds. The gas is
    exact.
- **issue(a) and redeem(a)** (`Usdt/Spec/Issue.lean`). `_totalSupply` is slot 1 and `balances[owner]`
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
- **setParams(b, m)** (`Usdt/Spec/SetParams.lean`). `basisPointsRate`, `maximumFee` and `decimals`
  are slots 3, 4 and 9.
  - A caller that is not the owner gets a revert with empty output. The owner's call reverts
    when `b ≥ 20`, or when `b < 20` and `m ≥ 50`.
  - Otherwise, if `m * 10^decimals < 2^256`, the run stops after writing `b` to slot 3 and
    `m * 10^decimals` to slot 4. Every other slot is unchanged. One log `Params(b, f)` is
    appended, with the two new words as data. The gas is exact.
  - When that product overflows (it needs `decimals ≥ 75`), SafeMath's assert ends the run in
    INVALID (`SetParamsSpec.spec_mulOv`, round 13).
- **deprecate(a) and transferOwnership(a)** (`Usdt/Spec/AddrWrite.lean`).
  - A caller that is not the owner gets a revert with empty output.
  - `deprecate` stops after two writes of slot 10. Afterwards `deprecated` (byte 20) is 1,
    `upgradedAddress` (the low 160 bits) is `a`, and every other slot is unchanged. One log
    `Deprecate(a)` is appended.
  - `transferOwnership(0)` stops without writing anything. For `a ≠ 0` it stops after one write
    of slot 0. Afterwards the owner is `a`, `paused` is unchanged, and so is every other slot.
    No log is emitted (Ownable has no event here).
  - The gas is exact.
- **destroyBlackFunds(a)** (`Usdt/Spec/Destroy.lean`). `B` is the slot of
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
  - When the contract is deprecated (`Usdt/Spec/Deprecated/Destroy.lean`), the getter does not read `B`.
    It sends the upgraded address `ua` one message with no value and the data
    `0x70a08231 ++ a` (`balanceOf(a)`). The theorem holds for every callee behaviour that meets
    a stated assumption: when the call ends with no error, the contract's account still exists
    in the state the call left. It also needs a frame that is not static, and at least
    `TAIL_MAX fork` gas left after the price of the CALL (enough for both writes at their highest
    price, `Gas.writeMax`: 47,881 before Glamsterdam, 223,721 from Glamsterdam, where a write can
    also pay the state gas of a new slot).
    - If the call fails, the run reverts with no output.
    - If it succeeds, let `S` be the state the call left and `d` the first word of the reply
      (the word at 0x60 after the copy). The run stops after writing 0 to `B` and then
      `_totalSupply - d` (unchecked) to slot 1 of this contract, both over `S`, and logs
      `DestroyedBlackFunds(a, d)`. The gas is exact.
    - So `_totalSupply` drops by the balance that the upgraded contract reports, while the local
      `balances[a]` is set to 0 whatever it held.
    - If `ua` has no code, the run reverts before any call. The interpreter's own message runner
      is covered for an upgraded code with a proved specification.

- **The getters** (`Usdt/Spec/Getters.lean`). Each call with no value returns exactly
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
- **name() and symbol()** (`Usdt/Spec/Strings.lean`). They read the string in slot 7 (name) or slot 8
  (symbol). The theorems cover a string of 1 to 31 bytes in Solidity's short form: the bytes
  from the top of the slot word, and the low byte equal to twice the length `n`.
  - The call returns 96 bytes, the ABI encoding of a string: the word 0x20, the word `n`, and a
    word holding the first `n` bytes of the slot word followed by zeros.
  - The run goes through the code's copy loop once and through its padding branch. It reads
    the slot three times, writes nothing, and the gas is exact.
  - For the slot words of "Tether USD" and "USDT", the third word is the UTF-8 bytes of the
    string followed by zero bytes (`spec_name_tether`, `spec_symbol_usdt`).
  - The empty string (`Usdt/Spec/Strings.lean`; the low byte of the slot is 0): the call returns
    64 bytes, the word 0x20 and the word 0. It reads the slot twice, writes nothing, and the gas
    is exact.
  - The long form (`Usdt/Spec/Strings.lean`): the slot word is odd and `N` = word / 2 is at least 32.
    Solidity stores such a string from slot `keccak(k)` on. The call returns the word 0x20, the
    word `N`, then the words of the slots `keccak(k) + i` for i < ceil(N / 32). The last word
    keeps only its first `N mod 32` bytes followed by zeros, when `N` is not a multiple of 32.
    The run goes through the code's two copy loops (storage to memory, then memory to memory)
    and reads each data slot once. The gas is exact, with the price of each data read cold or
    warm. A bound `N < 2^180` is a hypothesis.
  - Together these cover every slot word that Solidity writes for a string. Odd words with
    `word / 2 < 32` are not covered; Solidity never writes them.

- **The global invariant** (`Usdt/Invariant/Supply.lean`). `Inv` says that the sum of `balances[a]` over all
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
    round 13 (`ok_*`, and `inv_call` below). This file proves nothing about the deprecated paths;
  see `inv_call_all` below.

## Completeness of the dispatcher, for every gas

- `runFrame_ok_dispatch` (`UsdtVerify/Usdt/Complete/Dispatch.lean`, alias `Summary.dispatch_complete`):
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
  the fee path. Its hypotheses: Berlin ≤ fork (Glamsterdam included since round 17); until
  round 18 also a frame that is not static and an account for the contract (see below).
- Round 13 adds the same for approve(address,uint256) and transferFrom(address,address,uint256)
  (not deprecated), and for the owner functions pause, unpause, addBlackList, removeBlackList,
  issue, redeem, setParams, deprecate, transferOwnership and destroyBlackFunds (the last not
  deprecated). Each conclusion lists the checks the run passed (for the owner functions: the
  caller is the owner, and each `require`). Two new specifications were needed to exclude
  cases: approve with call data shorter than 68 bytes reverts (`Approve.spec_payload`), and
  setParams with `m * 10^d ≥ 2^256` ends in INVALID (`SetParamsSpec.spec_mulOv`).
  Hypotheses: Berlin ≤ fork (Glamsterdam included since round 17), call data below 2^256 bytes,
  and not deprecated for approve, transferFrom, destroyBlackFunds.
- Round 18: the writing functions' completeness theorems (not deprecated) no longer assume a
  frame that is not static or an account for the contract. On every path that remains after the checks, the run
  reaches an SSTORE; in a static frame, or with no account, that SSTORE fails or halts with an
  error at any gas (`Gas.sstore_stuck`, UsdtVerify/Evm/Stuck.lean), so no such run ends with no
  error (`Gas.no_ok_stuck`, the per-path `bad_*` lemmas). Each `ok_X` of a writing path now also
  concludes `message.isStatic = false` and `hasAccount state C` (transferOwnership: on the
  `a ≠ 0` path, the only one that writes). `transferFrom`'s INVALID specifications
  `spec_feeGtF`/`spec_balLow` take these two facts only when the allowance `A` is not `MAX_UINT`
  (`hgood`; with `A = MAX_UINT` the allowance is not written before those INVALIDs).
- Round 13 also covers every getter (allowance: not deprecated) and name() / symbol(). For
  name and symbol the slot word must have one of the shapes Solidity writes (`StrForm`: empty,
  1 to 31 bytes in the short form, or the long form with a length below 2^180); this is a named
  hypothesis, since the other words have no specification.
- **The invariant over every successful call, not deprecated** (`Complete.inv_call`,
  `UsdtVerify/Usdt/Invariant/Calls.lean`). From Berlin on (Glamsterdam included since round 17), take a fresh frame of the deployed
  code at pc 0, with any call data below 2^256 bytes, any value, any gas, any gas bound and any
  message runner. Assume:
  - `KeccakSep` (keccak keeps the storage slots apart; not proved);
  - (until round 18: the frame is not static, and the contract has an account; both are now
    derived from the successful run, see above);
  - the contract is not deprecated (byte 20 of slot 10 is 0);
  - slots 7 and 8 hold strings in a form Solidity writes (`StrForm`);
  - `Inv`: the sum of the 2^160 balances equals `_totalSupply` at the start.
  If the interpreter loop ends with no error, `Inv` holds in the end state.
- Deprecated totalSupply() (`Complete.dep_totalSupply_complete`, round 14), from Berlin on,
  Glamsterdam included since round 19 (as every `dep_*_complete` below), for any gas, any gas
  bound and ANY message runner (nothing is assumed of the runner). Every run that ends with no
  error is the forward to the upgraded address:
  - the runner was called with the forwarded message (`SendsVia`, along the route `r`) and
    returned a frame with no error;
  - the run returns the word at 0x60 after the CALL wrote the start of that frame's output;
  - the gas left is exact, and the state and substate are those after the call.
  Also, the upgraded account's code `c` was found in the state (round 15: before, this was the
  hypothesis `hcode`), and the CALL followed a route `r` (round 16: before, the hypothesis `hdel`
  excluded delegation). Either `c` is no delegation (or the fork is before Pectra), and the message
  runs `c`; or, from Pectra, `c` is an EIP-7702 delegation indicator to an address `d`, the code
  `c'` of `d` was found in the state, and the message runs `c'` with `d` as its code address and
  the precompiles disabled. Its current target is still the upgraded address. In the delegated
  case the CALL also paid the access to `d` (`routeCost`: `accCost`, 100 warm, 2600 cold, 3000
  cold from Glamsterdam), and the caller's
  state and substate record the read and the access of `d`. No hypothesis on the code.
  Too little gas at EXTCODESIZE, GAS, SUB, CALL or after the call,
  no code, the greatest depth, and (from Pectra) a delegate whose code is not found in the state
  are proved to leave no run that ends with no error.
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
  substate are those after the call. The same route, and no hypothesis on the code.
- Deprecated allowance(address,address) (`Complete.dep_allowance_complete`, round 15): the
  statement of balanceOf, for the forward of `allowance(owner, spender)`.
- Deprecated destroyBlackFunds(address) (`Complete.dep_destroy_complete`, round 15), for any
  gas, any gas bound and any runner. Every run that ends with no error is the owner's, with `a`
  blacklisted. The runner was called with the forward of `balanceOf(a)` and returned a frame with
  no error. The run then stopped with no output, after setting, over the state `S` that the call
  left, `balances[a]` to 0 and `_totalSupply` to `_totalSupply - d` (unchecked), where `d` is the
  word the call wrote at 0x60, and logging `DestroyedBlackFunds(a, d)`; gas exact. The frame was
  not static and the contract has an account in the child's end state: both are in the
  conclusion (round 19), since otherwise the first SSTORE after the call is `Stuck`
  (`DeprecatedDestroy.tailBadD`). Through round 18 they were the hypotheses `hstatic` and `hkeep`
  (an assumption on the runner); no named hypothesis beyond the coldness flags remains.

## The invariant when deprecated: destroyBlackFunds (round 14)

`UsdtVerify/Usdt/Invariant/DeprecatedDestroy.lean`. When deprecated, `destroyBlackFunds(a)` asks the upgraded
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

## The invariant over every successful call, deprecated or not (round 15)

`UsdtVerify/Usdt/Invariant/All.lean`, `Complete.inv_call_ns` (until round 16 named
`inv_call_all`). It is `inv_call` without the
hypothesis "not deprecated". From Berlin on (Glamsterdam included; through round 18 before Glamsterdam when deprecated), take a fresh frame of the
deployed code at pc 0, with any call data below 2^256 bytes, any value, any gas, any gas bound
and any message runner. Assume `KeccakSep`, `StrForm` of slots 7
and 8, and `Inv` at the start (through round 18 also a frame that is not static). When the
contract is deprecated, also assume (through round 19 also an account for the contract `C`):
- `KeepsInv` (`hkeeps`): whenever the runner ends a message from `C` to `ua` with no error, and
  `Inv` held in the caller's state, then `Inv` holds in the child's end state. It asks nothing
  about the account of `C` (round 20). The callee may call back into `C`; this assumption is
  about the end state only, so it covers that;
- for destroyBlackFunds, `HonestBalance` (`hhonest`): the word that the forwarded `balanceOf(a)`
  writes at 0x60 is `balances[a]` in the child's end state.
If the interpreter loop ends with no error, `Inv` holds in the end state.
Nothing is assumed of the code of `ua` (round 16: the hypothesis `hdel` is gone). When that code
is an EIP-7702 delegation, the message still has `ua` as its current target, so `KeepsInv` and
`HonestBalance` apply to it as stated.

## Static frames, and the invariant over every successful call (round 17)

`UsdtVerify/Usdt/Invariant/Static.lean`. EthLib proves that a run of a static frame keeps the state up
to the records of reads (`staticStep_runFrame`), given that the runner ends every static child
message so. That premise is named here `StaticKeeps runChild`, and `staticKeeps_process` proves
it, from Paris, for the interpreter's own runner (EthLib's `processMessage_static`).
- `static_run`: for any fork, a fresh static frame of the deployed code, for a message whose code
  is that code (`message.code = CODE`) at an account that holds code (EthLib's `StaticCode`),
  under a runner that meets `StaticKeeps`: if the loop ends with `.ok`, the end state reads as
  the start state at every address (account, storage and transient storage).
- `inv_static`: so `Inv C` at the start gives `Inv C` at the end.
- `Complete.inv_call_all` now covers static frames: it takes `hstat` (when static:
  `message.code = CODE`, `StaticCode`, `StaticKeeps`), and is `inv_static` or `inv_call_ns` by
  the flag. The hypothesis "not static" is gone from it. Rounds 18 and 19 assumed the account
  only for a frame that is not static and when deprecated (`hacc`), for the premise of the
  callee assumption; round 20 removed `hacc` from `inv_call_ns`, `inv_call_all`, `GoodCall`,
  `goodCall_process` and `process_step` (see below).

## The invariant without `hacc` (round 20)

`UsdtVerify/Usdt/Invariant/All.lean`. The callee assumption was restated so that it does not
need the account of `C`. (In a static frame, `hstat` of `inv_call_all` still implies an account of
`C`: `StaticCode` for the nonempty code `CODE`.)
- `KeepsInv runChild C ua` now has `Inv C` of the caller state as its only premise and `Inv C` of
  the child's end state as its conclusion. The assumption of rounds 15 to 19 is kept as
  `KeepsInvAcc` (premise also an account of `C`, conclusion also that account), and
  `keepsInv_of_acc` proves that `KeepsInvAcc` together with its missing case `KeepsInvNoAcc` (a
  caller state with no account of `C`) gives `KeepsInv`.
- A missing account of `C` does not make a step of the forwarding paths fail: no completeness
  theorem of those paths takes an account, the forward specifications of the six forwarding
  functions take none, and those of destroyBlackFunds take none in the start state (their `hkeep`
  is an account at the end of each forwarded call). (In EthLib's
  `finishCall` the balance check is `balance < value`, and these calls send value 0.) The missing
  account reaches the runner: `LocalForward` now states that `C` has an account in the caller
  state of the CALL iff it has one in the start state, and `localForward_noAcc` restates it for
  the case with no account. So `KeepsInv` assumes that case of the runner; the code cannot rule
  it out.
- destroyBlackFunds needs the account in the child's end state (for `inv_tail_iff`);
  `dep_destroy_complete` proves it for every run that ends with no error, so `dep_destroy_local`,
  `inv_dep_destroy_iff` and `inv_dep_destroy` take no account either.
- `inv_call_ns`, `inv_call_all`, `GoodCall`, `goodCall_process` and `process_step` no longer
  take `hacc`.

## A finite sequence of calls (round 17)

`UsdtVerify/Usdt/Invariant/Seq.lean`. `Calls C S S'` is a finite sequence of steps, each either a
`GoodCall` (one successful run of the deployed code for a message to `C`, from the state at
that point, under the hypotheses of `inv_call_all` for that run, each with its own fork, message,
gas and runner) or `Untouched` (any change that keeps every storage word of `C`).
- `inv_calls`: under `KeccakSep`, `Inv C S` and `Calls C S S'` give `Inv C S'`.
- `goodCall_process`: from Paris on (Glamsterdam included since round 19), a top-level message to `C` with the
  deployed code, no value and no precompile, run by EthLib's `processMessage`, that ends with no
  error, is a `GoodCall` from its start state to its end state, under the named assumptions for
  the interpreter's own runner (`StaticKeeps` is proved for it).
- Failed top-level calls (round 18): `untouched_process_failed` proves that a top-level message
  run by `processMessage` (any code, any fork) that ends with an error is an `Untouched` step for
  every address. The rollback restores the storage of the start state because the run keeps the
  block of the state (`parent`). EthLib proves that only for static messages, from Paris
  (`processMessage_static`); the local
  `Local.parent_process` (UsdtVerify/Evm/Local/Parent.lean) proves it for every message and every
  creation, static or not, from any fork, by induction on the gas, from EthLib's semantics
  (`Local.processMessage_failed_getStorage` then applies EthLib's `getStorage_restoreTxState`).
- Calls with value (round 18): `process_value_fails` proves that, from Berlin, a top-level message
  of the deployed code (no precompile, call data below 2^256 bytes) with a nonzero value ends
  with an error, whether the value is moved or not. `process_step` (from Paris, Glamsterdam
  included) puts both together: every top-level message of the deployed code to `C`
  with no precompile that `processMessage` ends is a `GoodCall` (no error) or an `Untouched` step
  (an error). It takes the hypotheses of `goodCall_process` except "no value" (call data below
  2^256 bytes and the named assumptions) in both cases; the error case uses none of them.
- What the remaining `Untouched` steps stand for is assumed, not proved: a transaction that does
  not reach `C`, fees. A transaction that reaches `C` through another contract is not a
  top-level call and is not covered.

On the way (`dep_*_local`): when deprecated, the six forwarders (totalSupply, balanceOf,
allowance, approve, transfer, transferFrom) make one call, from a caller state with the start
storage of `C`, and end in exactly the child's end state: nothing is written locally after the
call. destroyBlackFunds ends in `tailState S C a d` over the child's end state `S`.

## What is trusted

- The Lean 4 kernel (v4.35.0).
- The three standard axioms that `#print axioms` reports for every main theorem: `propext`,
  `Classical.choice` and `Quot.sound`. There is no `sorry`, no new axiom, and no `native_decide`
  or `bv_decide`. `decide +kernel` is used, and it is checked by the kernel.
- EthLib's EVM model is a faithful EVM. The proofs are only as good as that model.
- The bytecode file is the deployed code. The interpreted hash check ties `CODE` to the file,
  and `data/SOURCE.md` ties the file to the chain.
- A few generic rules are proved locally in this repository, and EthLib's model is not
  modified. These rules are EXP with its price worked out, some instruction table
  entries, EXTCODESIZE at every fork from Berlin (`Local.extcodesize`; EthLib's rule stops
  before Glamsterdam), and that every message keeps the block of the state
  (`UsdtVerify/Evm/Local/`). STOP and GAS come from EthLib. The CALL step lemmas at every fork
  (`callStep_child_r`, `callWithR`, `callStep_low_r`, `callStep_deep_r`, `callStep_missing`) are
  computed from EthLib's `callStep`. They are proved from EthLib's semantics, not assumed.

## What is not covered

- name/symbol on slot words outside `StrForm`.
- The invariant over deprecated calls without the runner assumptions `KeepsInv` and
  `HonestBalance` (destroyBlackFunds can break it, see above). No concrete upgraded contract is
  shown to meet them.
- `KeccakSep` (a hypothesis of the invariant theorems, about keccak).
- Runs that run out of gas below the stated bounds, except at the dispatcher (see above).
- Forks before Berlin. Glamsterdam rests on EthLib's model of that fork at the pin (its prices
  and the order of its checks).
