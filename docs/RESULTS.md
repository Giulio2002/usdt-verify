# What is proved about the deployed USDT bytecode

This is a summary for a human reader. The Lean theorems are the reference; this page claims only
what they state. Theorem names in parentheses; the one-place index is `UsdtVerify/Summary.lean`.

## The object

- The runtime bytecode of TetherToken (USDT) on Ethereum mainnet: 11,075 bytes, read at block
  26362952 (`data/usdt.runtime.hex`, provenance in `data/SOURCE.md`).
- The Lean constant `CODE` holds those bytes. A build-time check (`UsdtVerify/Test/Hash.lean`)
  compares `CODE` with the hex file and its keccak256 with `b44fb4e9…ea55`. The interpreter runs
  this check; it is a test, not a kernel-checked theorem.
- The semantics is EthLib's EVM model (pinned commit d4d422780), with its program logic and the
  one-counter gas meter. Forks: Berlin onwards, and before Glamsterdam where storage is written or a
  call is made.

## What a theorem says

Each theorem starts from a fresh call frame running `CODE` at pc 0. Under the stated hypotheses on
the call data, the call value, the storage words read and the gas, every run reaches the stated
end frame. Most theorems are also given for the real interpreter loop `runFrame`, for every gas
bound and every message runner (`runFrame_*`).

The end frames are:
- a normal halt: RETURN with the given bytes, or STOP;
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

## What is trusted

- The Lean 4 kernel (v4.35.0).
- The three standard axioms that `#print axioms` reports for every main theorem: `propext`,
  `Classical.choice` and `Quot.sound`. There is no `sorry`, no new axiom, and no `native_decide`
  or `bv_decide`. `decide +kernel` is used, and it is checked by the kernel.
- EthLib's EVM model is a faithful EVM. The proofs are only as good as that model.
- The bytecode file is the deployed code. The interpreted hash check ties `CODE` to the file,
  and `data/SOURCE.md` ties the file to the chain.
- A few generic opcode rules are proved locally in this repository, and EthLib's model is not
  modified. These rules are EXTCODESIZE, GAS, STOP, EXP with its price worked out, and some
  instruction table entries (`UsdtVerify/Local/`). They are proved from EthLib's semantics, not assumed.

## What is not covered

- A nonzero call value (the nonpayable revert).
- The other functions: owner and admin functions, issue, redeem, setParams, blacklist management,
  the remaining getters, and the fallback.
- Properties across several calls (invariants), and the global "sum of all balances =
  `_totalSupply`". The global statement needs a sum over a mapping and is not stated.
- The output buffer after STOP. `At` does not track it, so for transfer the theorems do not say
  that the returned data is empty.
- Runs that run out of gas below the stated bounds.
- Forks before Berlin, and Glamsterdam onwards on the writing and calling paths.
