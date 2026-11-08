# usdt-verify

Formal verification, in Lean 4, of the USDT (TetherToken) runtime bytecode deployed on Ethereum mainnet at `0xdAC17F958D2ee523a2206206994597C13D831ec7`.

The proofs are about the deployed bytes themselves, not about the Solidity source. They use the EVM model and the program logic of [EthLib](https://github.com/ethereum/EthLib).

This is a work in progress. The sections below say exactly what is proved, what is assumed and what is not covered yet. The Lean theorems are the reference. This page claims nothing they do not state.

## How it is done

### 1. The bytecode

The runtime code was read from mainnet with one `eth_getCode` call at tag `latest`, just after `eth_blockNumber` returned 26362952. It is 11,075 bytes long. The hex is in `data/usdt.runtime.hex`, and `data/SOURCE.md` records where it came from.

A build-time test in `UsdtVerify/Test/Hash.lean` checks that the Lean constant holding the code equals that file. It also checks that EthLib's keccak256 of the code equals the hash computed by an independent Python implementation. This test is run by the Lean interpreter at build time. It is a test, not a kernel-checked theorem.

### 2. Storing a long code cheaply

A naive byte-array literal of 11 KB is too slow for Lean to reason about. Reading one byte recurses through the whole literal.

So the code is stored as one big natural number, and byte `i` is read with a single bit shift. Lean evaluates shifts on big numbers quickly, so any fact like "the byte at position 3565 is `0x5b`" is checked in milliseconds. This representation is now part of EthLib (`Logic/NatCode.lean`), where it came from this project.

### 3. Jump destinations

A `JUMP` is only valid if its target is a `JUMPDEST` byte that is not inside the data of a `PUSH`. That depends on the whole code before the target.

This is proved with a walk along opcode boundaries from position 0 to the target. The walk is a boolean function, and Lean's kernel checks that it returns true. That gives EthLib's validity predicate through a general lemma.

### 4. Reading the contract from its bytes

A small script in `scripts/` disassembles the code. From the bytes alone it finds:

- the dispatcher: the table of 32 function selectors and the jump target of each,
- the storage layout: for example `balances` is a mapping at base slot 2, `_totalSupply` is slot 1, and `paused` is a byte of slot 0.

The Solidity source was only used as a guide. Every fact the proofs rely on is checked against the bytes. The map is in `docs/MAP.md`.

### 5. Specifications

Each specification starts from a fresh call frame running the code at position 0. It says what the run does, in terms of:

- the call data and the call value,
- the storage words read and written, in order,
- the logs appended,
- the bytes returned, or a revert, or an exceptional halt,
- the exact gas used, with the EIP-2929 cold and warm prices and the EIP-2200 and EIP-3529 storage prices and refunds.

### 6. Proofs

The proofs step through the code one block at a time with EthLib's opcode rules. Shared stretches of code, such as the pause check or the blacklist lookup, are proved once and reused.

Most theorems are also stated for EthLib's real interpreter loop `runFrame`, for every gas bound and every message runner.

When USDT is deprecated, it forwards each call to an upgraded contract. Those paths are proved for any message runner that meets a stated assumption, through EthLib's abstraction for called code. The assumptions are about the runner on the message USDT actually forwards: from a caller state that agrees with the start state, running the code the upgraded address holds, with no value. EthLib's own runner meets them when the upgraded contract's code is a single `STOP`. Some deprecated exact-condition hypotheses still cannot hold for EthLib's own runner (see "What is not covered yet").

## Layout

- `UsdtVerify/Evm/` holds general EVM lemmas that are not about USDT, such as storage reads and writes, gas rules and call steps.
- `UsdtVerify/Usdt/Code.lean` and `UsdtVerify/Usdt/Map.lean` hold the bytecode, the dispatcher table and the storage layout.
- `UsdtVerify/Usdt/Spec/` says what each function does, one file per function.
- `UsdtVerify/Usdt/Proofs/` holds the block by block proofs, one file per function.
- `UsdtVerify/Usdt/Complete/` holds the completeness theorems.
- `UsdtVerify/Usdt/Exact/` holds the exact success conditions.
- `UsdtVerify/Usdt/Invariant/` holds the supply invariant.
- `UsdtVerify/Usdt/Security/` holds the access control, pause, blacklist, allowance and supply properties.
- `UsdtVerify/Usdt/Sanity/` shows that the named assumptions can hold, so the theorems are not vacuous.
- `UsdtVerify/Summary.lean` indexes the main theorems.

`docs/LAYOUT.md` describes each folder and maps the old paths to the new ones.

## What is proved

All of this holds from the Berlin fork onwards, Glamsterdam included. At Glamsterdam a storage write also pays the new state gas, EXTCODESIZE costs the account access plus 100 (EIP-8038), and CALL checks its gas before charging. The prices in the theorems take the fork, and before Glamsterdam they reduce to the earlier ones. Every theorem has explicit hypotheses, such as enough gas and a call value of 0. The index of all theorems is `UsdtVerify/Summary.lean`, and `docs/RESULTS.md` gives the full statements in prose.

- **totalSupply and balanceOf.** They return slot 1, or `balances[who]` at slot `keccak(who ++ 2)`.
- **transfer(to, v).**
  - It reverts when paused, when the sender is blacklisted, and when the call data is shorter than 68 bytes.
  - It halts at `INVALID` when the fee product overflows, when the fee exceeds `v`, when the balance is too low, and when a credit overflows.
  - On success, with a fee of 0 or above 0, it makes the exact balance writes and emits the exact `Transfer` logs.
  - It checks only the sender against the blacklist, not the recipient.
- **approve(spender, v).** All three paths: `v` of 0, a nonzero `v` over a zero allowance, and the revert when both are nonzero.
- **transferFrom(from, to, v).**
  - It reverts when paused, when `from` is blacklisted, and when the call data is short.
  - It halts at `INVALID` in every overflow and underflow case, including an allowance below `v`.
  - On success, with or without a fee, it makes the exact writes and logs. An allowance of `2^256 - 1` is never decreased.
- **Local conservation.** On every success path, the balance changes the path makes sum to zero. The payer changes by `-v`, the payee by `v - fee`, and the owner by `fee`. These theorems assume the slots involved are pairwise distinct. The slots are keccak outputs, and nothing about the hash function is assumed or proved.
- **Deprecated paths.** For all five functions above, when the deprecated flag is set, USDT sends exactly one message, with no value, to the address in slot 10, with the stated call data. It then returns or stops on success, and reverts with empty output on failure. It reverts before calling if that address has no code.
- **Getters.** `decimals`, `maximumFee`, `_totalSupply`, `basisPointsRate`, `MAX_UINT`, `deprecated`, `paused`, `upgradedAddress`, `owner`, `getOwner`, `balances`, `isBlackListed`, `getBlackListStatus`, `allowed` and `allowance` (when not deprecated) each return exactly the stated 32 bytes, read only the named slots and write nothing.
- **name and symbol.** Every slot word Solidity writes for a string is covered. An empty string returns the word 32 and the word 0. A string of 1 to 31 bytes in the short form returns the word 32, the length `n`, then the first `n` bytes of the slot padded with zeros. A string of 32 bytes or more in the long form returns the word 32, the length, then the bytes read in order from the data slots at `keccak(slot) + i`, with the last word padded with zeros. The long form assumes a length below 2^180. Both copy loops are proved by induction, and the gas is exact. For "Tether USD" and "USDT" the output is proved to be those strings. That mainnet stores those words is a hypothesis.
- **allowance when deprecated.** It forwards `0xdd62ed3e ++ owner ++ spender` to the upgraded address, for any callee, with the same cases as the other deprecated paths.
- **destroyBlackFunds when deprecated.** Its internal `balanceOf(a)` is forwarded as one message, with no value, to the upgraded address. If that call fails, the run reverts with empty output. If it succeeds, the run sets the local `balances[a]` to 0 and lowers the local total supply by the balance the upgraded contract reported, with an unchecked subtraction. So the local total supply drops by the upgraded contract's answer, not by the local balance. This is proved for any callee that leaves USDT's own account unchanged.
- **Fallback.** A selector that is not in the table reverts with no output and no state change after exactly 773 gas. Call data shorter than 4 bytes reverts the same way after 46 gas.
- **Dispatcher completeness.** From Berlin, for any gas, if a call to USDT ends without an error, then the call data is at least 4 bytes, the call value is 0, and the selector is one of the 32 in the table. This covers runs that run out of gas too. It is the first step toward proving that the proved paths are all the successful runs.
- **Completeness per function.** For `totalSupply`, `balanceOf`, `transfer`, `approve`, `transferFrom` and all ten owner functions, all the getters, `name` and `symbol`, when not deprecated, every successful run, with any gas, is one of the proved paths and ends exactly as its spec says. Each writing function's completeness theorem proves that a successful run was not static and that the contract has an account. For `name` and `symbol` the slot word must be in one of the three forms Solidity writes. When deprecated, all seven forwarding functions are complete too (`totalSupply`, `balanceOf`, `transfer`, `approve`, `transferFrom`, `allowance` and `destroyBlackFunds`), for any gas and any message runner: every successful run forwarded one call to the upgraded contract and then returns its answer or stops, with exact gas. It is also proved that every successful run found the upgraded contract's code. From Pectra, an upgraded code that is an EIP-7702 delegation is covered too: the call then runs the delegate's code, with the extra access charge. For `destroyBlackFunds` it proves that a successful run was not static and that USDT still had an account after the forwarded call.
- **No ether accepted.** Every one of the 32 functions reverts with empty output when called with a nonzero value, before any storage read.
- **Owner functions.** For each one, a caller that is not the owner (the low 160 bits of slot 0) gets a revert with empty output.
  - `pause` and `unpause` set or clear the paused byte of slot 0, keep the owner bits, and emit `Pause` or `Unpause`. They revert if the contract is already in that state.
  - `addBlackList` and `removeBlackList` set the blacklist byte of the address to 1 or 0 and emit the matching event. No other slot changes.
  - `issue` and `redeem` change the total supply and the owner's balance in code order and emit `Issue` or `Redeem`. They revert in the cases the code checks, and `issue(0)` reverts.
  - `setParams` sets the fee rate and the maximum fee and emits `Params`. It reverts when the rate is 20 or more, or the maximum is 50 or more. When the maximum fee times 10 to the decimals overflows, it halts at `INVALID`.
  - `deprecate` sets the deprecated byte and the upgraded address and emits `Deprecate`.
  - `transferOwnership` replaces the owner bits and keeps the paused byte. It does nothing for the zero address.
  - `destroyBlackFunds` reverts for a non-owner and for an address that is not blacklisted. Otherwise it sets the address's balance to 0, lowers the total supply by that balance with an unchecked subtraction, as the bytecode does, and emits `DestroyedBlackFunds`.

## The supply invariant

`UsdtVerify/Usdt/Invariant/Supply.lean` defines the invariant: the sum of `balances[a]` over all 2^160 addresses equals `_totalSupply` (slot 1).

- Every writing success path keeps it, for every function above: transfer and transferFrom with and without a fee, approve, pause, unpause, transferOwnership, addBlackList, removeBlackList, setParams, deprecate, issue, redeem and destroyBlackFunds.
- For destroyBlackFunds, the invariant itself shows that the destroyed balance is at most the total supply, so the unchecked subtraction cannot wrap.
- Read-only paths do not write storage, so they keep it too.
- Any finite sequence of these steps keeps the invariant, and each path's end state is shown to be one such step.

These theorems assume a keccak hypothesis, `SepOn`, which is stated and not proved. It is local to the call: for the few addresses the call involves (the caller, the address arguments and the owner), their balance slots are distinct from each other, from the balance slot of any other address, and from the fixed slots 0 to 10. Each such fact is about one given slot, so for the real keccak it fails with probability about 2^-96. An earlier version assumed the separation for all keys at once (`KeccakSep`), which is almost certainly false, so the audit flagged it. The global form still implies the local one (`sepOn_of_global`).

The main theorem is `inv_call` in `UsdtVerify/Usdt/Invariant/Calls.lean`. From Berlin, Glamsterdam included, take any call to USDT, with any call data, any value and any gas. If the invariant holds before and the call ends without an error, the invariant holds after. Its hypotheses are `SepOn` for the call's addresses, the contract not being deprecated, and the name and symbol slots being in a form Solidity writes. It needs no hypothesis about static frames or the contract's account: on every writing path, a static frame or a missing account makes the first storage write fail, which is proved path by path.

### When the contract is deprecated

In deprecated mode the invariant can break. `destroyBlackFunds` asks the upgraded contract for the balance of the address, sets the local balance to 0, and lowers the local total supply by the answer. `UsdtVerify/Usdt/Invariant/DeprecatedDestroy.lean` proves:

- after that call, the invariant holds exactly when the upgraded contract's answer equals the local balance (`inv_tail_iff`, `depD_inv`), and this covers callees that call back into USDT,
- assuming only that slot 1 is not a balance slot (`NotBal 1`), a concrete state where the invariant holds before and fails after, with an answer of 1 for a local balance of 0 (`exists_breaks`),
- the same failure for a whole run, for any callee that answers a different balance and leaves USDT's storage alone (`depD_breaks`).

So in deprecated mode the supply invariant depends on the upgraded contract answering honestly.

### Every call, deprecated or not

`inv_call_all` in `UsdtVerify/Usdt/Invariant/Static.lean` drops the "not deprecated" hypothesis. For any successful call to USDT, with any call data, value and gas, the invariant holds after if it held before. When the contract is deprecated it needs these named assumptions:

- `KeepsInvAt`: the forwarded message, when the runner ends it without an error, ends with the invariant if it started with it. It covers only the message USDT actually sends, running the upgraded address's code. This covers an upgraded contract that calls back into USDT. The earlier forms over every message, `KeepsInv` and `KeepsInvAcc`, imply it.
- `HonestBalanceAt`, only for `destroyBlackFunds`: on the forwarded message, the balance the upgraded contract reports equals the local balance.

The six other forwarding functions write nothing locally after the forwarded call, which is also proved.

`inv_call_all` also covers static calls, such as a `STATICCALL` into USDT. A static run of USDT changes no state, so the invariant holds trivially. This uses a named assumption, `StaticKeeps`, about the message runner, which is proved for EthLib's own runner from Paris. No theorem of the invariant assumes the contract's account any more. A missing account at the forwarded call is proved harmless to USDT's own code, so the case is left to `KeepsInv`.

### Sequences of calls

`inv_calls` in `UsdtVerify/Usdt/Invariant/Seq.lean` lifts the invariant to any finite sequence of steps. A step is either a successful call that meets the hypotheses of `inv_call_all`, each with its own fork, message and runner, or a step that leaves every storage word of USDT unchanged. `goodCall_process` shows that a successful top-level message to USDT with no value, from Paris, is such a call. A failed call is proved to leave every storage word unchanged after the rollback (`untouched_process_failed`), using a general lemma proved here from EthLib's semantics: every step keeps the parent block of the state. A top-level call to USDT with a nonzero value always fails (`process_value_fails`). So `process_step` shows that every top-level message to USDT, from Paris, is one of the two kinds of step, with no assumption about failed calls. When the contract is deprecated, its hypothesis is `KeepsInvAt`, which EthLib's runner meets when the upgraded code is `STOP`. Messages that reach USDT through another contract, and the rollback of an outer frame, are not shown to be such steps.

## Exact success conditions

`UsdtVerify/Usdt/Exact/` proves the converse of completeness: with enough gas, a call succeeds if and only if its stated conditions hold, so there are no unexpected reverts. With less gas than the success path costs, the call fails. The conditions are written out in `UsdtVerify/Usdt/Spec/Guards.lean`.

- The 19 read functions, including `totalSupply`, `balanceOf` and `allowance` when not deprecated, and `name` and `symbol` for the string forms Solidity writes, succeed exactly when the call data has at least 4 bytes and the call sends no ether.
- Every writing function, when not deprecated, has a theorem `X_ok_iff`. Given gas at least the cost of its success path, and more than 2300 gas left at each storage write as EIP-2200 requires, the call succeeds exactly when its condition holds. For `transfer` the condition is: at least 68 bytes of call data, no ether, not paused, sender not blacklisted, no overflow in the fee product, fee at most the amount, amount at most the sender's balance, no overflow at the recipient, a frame that is not static and an existing account. The owner functions add that the caller is the owner, plus each function's own checks.
- When the cost depends on the path, for example a fee of 0 or above 0, it is stated as an `if`.
- That gap is closed by `X_iff_gas` for all 13 writing functions when not deprecated: for every amount of gas, the call succeeds exactly when its condition holds and the gas is at least an exact threshold. The threshold is the larger of the success cost and the gas needed to keep more than 2300 at each storage write. A storage write with 2300 or less left is proved to fail, from Istanbul.
- The seven deprecated paths have `X_dep_ok_iff`. The never-fail hypothesis now covers only the messages the path actually sends (`NoFailOn`). With it, `totalSupply_dep_ok_iff_process_stop` shows that, from Paris, under EthLib's own runner and with `STOP` as the upgraded code, a deprecated `totalSupply` call succeeds exactly when its forwarding checks pass. The answer hypothesis now covers only the message the CALL sends, with the gas the CALL gives, so `A` may depend on that gas. With `STOP` as the upgraded code, EthLib's own runner meets it for all seven forwards, in both the plain and the every-gas forms (`UsdtVerify/Usdt/Sanity/ProcessExact.lean`). Every plain form now needs the runner not to fail only on the messages the path sends. The one-sided `X_dep_ok_or_fails` keep the older answer hypothesis. Given enough gas and a runner that never fails and ends each forwarded call without an error exactly when some condition `A` holds, the call succeeds exactly when the checks before the forward pass and `A` holds. With too little gas they fail for every runner. For the six forwards other than `destroyBlackFunds`, `X_dep_ok_iff_gas` covers every amount of gas: the condition `A` now includes that the gas left after the forwarded call pays for the short tail of the function. Runners that may fail are covered too, for all seven forwards (`X_dep_ok_iff_fails`): if a runner failure on the forwarded call rules out `A`, the call succeeds exactly when the checks before the forward pass and `A` holds, for every gas. `answerRunnerAt` meets the answer hypothesis of deprecated `destroyBlackFunds`. Deprecated `destroyBlackFunds` is covered for every gas too (`destroyBlackFunds_dep_ok_iff_gas`): after the forwarded call, the gas left must pay for its two storage writes, priced in the state the call left, and keep more than 2300 at each.

## Security properties

`UsdtVerify/Usdt/Security/` proves five whole-contract properties, for one successful call with any call data, value and gas, and for sequences of calls. They hold from Berlin, Glamsterdam included, for static and non-static frames, when the contract is not deprecated.

- **Access control** (`Access.lean`). A caller who is not the owner changes only balance and allowance slots. The owner, the paused and deprecated flags, the fee settings, the upgraded address, the blacklist and the total supply keep their values.
- **Pause** (`Pause.lean`). While paused, every balance stays the same, unless the call is the owner's `issue`, `redeem` or `destroyBlackFunds`.
- **Blacklist** (`Blacklist.lean`). A blacklisted address's balance never decreases, except through the owner's `redeem` or `destroyBlackFunds`. So it cannot send tokens, directly or through `transferFrom`.
- **Allowances** (`Allowance.lean`). `transferFrom` moves at most the allowance, unless the allowance is `2^256 - 1`. Only `approve` and `transferFrom` change an allowance.
- **Supply** (`Supply.lean`). The total supply changes only through `issue` (+v), `redeem` (-v) and `destroyBlackFunds` (minus the destroyed balance).

They assume a local keccak hypothesis, `SecSep`, for the call's addresses: `SepOn` plus the separation of their allowance and blacklist slots. Each sequence theorem carries it per call. Two conclusions are narrower than before the audit: the allowance result is about given allowance slots, and the protected blacklist slots are those of address words.

When the contract is deprecated, the six forwarding functions hand the call to the upgraded contract, and `destroyBlackFunds` asks it for a balance. Each property then has a `*_call_all` and a `*_seq_all` version that covers deprecated calls under a named assumption about the forwarded message, such as `KeepsSlots` (it leaves the protected slots alone). Some guarantees need no such assumption, deprecated or not:

- the owner functions, `destroyBlackFunds` included, succeed only for the owner (`owner_only`),
- a caller who is not the owner, calling any function other than the six forwards, changes only balances and allowances (`nonOwner_local`),
- a successful `transfer` or `transferFrom` always starts not paused, with the sender not blacklisted (`transfer_checks_all`, `transferFrom_checks_all`).

## What you have to trust

- The Lean 4 kernel.
- EthLib's EVM model being a faithful EVM. EthLib tests its model against the official Ethereum test vectors, but it does not prove the model correct. The proofs here are only as good as that model.
- The bytecode file being the deployed code, through the build-time test and `data/SOURCE.md`.

Every main theorem uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`. There is no `sorry` and no new axiom. Neither `native_decide` nor `bv_decide` is used. `decide +kernel` is used, and the kernel checks it.

A few general opcode rules are proved locally in `UsdtVerify/Evm/Local/` while they make their way into EthLib. They are proved from EthLib's semantics, not assumed.

## What is not covered yet

- Forks before Berlin.
- `SepOn` and `SecSep` are hypotheses about keccak, not theorems. They are local to each call, so they are plausibly true for the real hash function, but nothing here proves them.
- `KeepsInvAt`, `HonestBalanceAt` and the `Keeps*` assumptions are about the forwarded message only. The audit showed that the earlier forms, over every message, were false for EthLib's own runner. `UsdtVerify/Usdt/Sanity/Process.lean` shows that, from Paris, EthLib's own runner meets `KeepsInvAt` and the five `Keeps*` assumptions when the upgraded address holds the single byte `STOP`. `UsdtVerify/Usdt/Sanity/Mirror.lean` shows `HonestBalanceAt` for EthLib's own runner with real code: a 25 byte contract, `MIRROR`, that answers `balanceOf(a)` from slot `keccak(a ++ 2)` of its own storage. It holds from Paris when that slot of the upgraded contract equals USDT's balance slot for the queried address. `UsdtVerify/Usdt/Sanity/Runner.lean` also has mock runners, and one that answers each address's local balance without running code meets all of them. `UsdtVerify/Usdt/Sanity/` also gives, for every fork from Berlin, a concrete state and call where the success theorems of `transfer`, `approve`, `issue`, `redeem` and `destroyBlackFunds` apply and the run succeeds, so their hypotheses can all hold. The same is shown for `transferFrom`, the five security theorems and `inv_call_all`, except for the keccak hypotheses `SepOn` and `SecSep`, which no concrete run can discharge. These examples are not deprecated, so for them the runner assumptions hold because the contract is not deprecated. The runners above show those assumptions can hold when it is. Finally, the mainnet slot words for "Tether USD" and "USDT" are proved to be in the form `name` and `symbol` need (`strForm_name`, `strForm_symbol`), and `inv_call_all` is shown to apply to a state holding them.
- Slot words for `name` and `symbol` in a form Solidity never writes.
- The individual path specs still state exact gas bounds. Completeness and the invariant hold for any gas.

## Related work

Certora formally verified rules for Tether's newer TetherToken contracts (Solidity 0.8.4, the `tether-contracts-hardhat` repository) in February 2024. That work targets a different, newer contract and works from the Solidity source. This repository targets the original 2017 contract on mainnet, at the level of its deployed bytecode.

## Building

You need [elan](https://github.com/leanprover/elan). The toolchain is pinned in `lean-toolchain`.

```
lake exe cache get
lake build
```

EthLib is fetched as a dependency at the git commit pinned in `lakefile.lean` (`fd3457dbf`). Building EthLib from source takes a long time and several GB of memory. Once EthLib is built, this project builds from clean in about 140 seconds with two threads and needs about 1.8 GB.

## Credits

Built on [EthLib](https://github.com/ethereum/EthLib). The proofs were written with [Claude Code](https://claude.com/claude-code).
