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
- **approve(s, v)**: v = 0; v ≠ 0 over a zero allowance; and the revert when v ≠ 0 and the
  allowance is nonzero.
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
  - The overflow of that product is not covered. It needs `decimals ≥ 75`.
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
  - The deprecated case, where the getter calls the upgraded contract, is not covered.

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
  - The empty string and strings of 32 bytes or more are not covered.

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

- destroyBlackFunds when deprecated.
- name() and symbol() for the empty string or a string of 32 bytes or more.
- Properties across several calls (invariants), and the global "sum of all balances =
  `_totalSupply`". The global statement needs a sum over a mapping and is not stated.
- Runs that run out of gas below the stated bounds.
- Forks before Berlin, and Glamsterdam onwards on the writing and calling paths.
