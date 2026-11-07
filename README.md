# usdt-verify

Formal verification, in Lean 4, of the USDT (TetherToken) runtime bytecode deployed on Ethereum mainnet at `0xdAC17F958D2ee523a2206206994597C13D831ec7`.

The proofs are about the deployed bytes themselves, not about the Solidity source. They use the EVM model and the program logic of [EthLib](https://github.com/ethereum/EthLib).

This is a work in progress. The sections below say exactly what is proved, what is assumed and what is not covered yet. The Lean theorems are the reference. This page claims nothing they do not state.

## How it is done

### 1. The bytecode

The runtime code was read from mainnet with one `eth_getCode` call at block 26362952. It is 11,075 bytes long. The hex is in `data/usdt.runtime.hex`, and `data/SOURCE.md` records where it came from.

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

When USDT is deprecated, it forwards each call to an upgraded contract. Those paths are proved for any callee that meets a stated assumption, through EthLib's abstraction for called code. Nothing is assumed about what the upgraded contract actually does.

## What is proved

All of this holds from the Berlin fork onwards, and before Glamsterdam on paths that write storage or make a call. Every theorem has explicit hypotheses, such as enough gas and a call value of 0. The index of all theorems is `UsdtVerify/Summary.lean`, and `docs/RESULTS.md` gives the full statements in prose.

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
- **Completeness per function.** For `totalSupply`, `balanceOf`, `transfer`, `approve`, `transferFrom` and all ten owner functions, all the getters, `name` and `symbol`, when not deprecated, every successful run, with any gas, is one of the proved paths and ends exactly as its spec says. The writing functions assume a fork before Glamsterdam, a call frame that is not static and an existing account for the contract. For `name` and `symbol` the slot word must be in one of the three forms Solidity writes. When deprecated, `totalSupply` is complete too, for any gas and any message runner: every successful run forwarded one call to the upgraded contract and returns its answer, with exact gas. This assumes the upgraded code is found in the state and is not an EIP-7702 delegation. The other deprecated paths are in progress.
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

`UsdtVerify/Invariant.lean` defines the invariant: the sum of `balances[a]` over all 2^160 addresses equals `_totalSupply` (slot 1).

- Every writing success path keeps it, for every function above: transfer and transferFrom with and without a fee, approve, pause, unpause, transferOwnership, addBlackList, removeBlackList, setParams, deprecate, issue, redeem and destroyBlackFunds.
- For destroyBlackFunds, the invariant itself shows that the destroyed balance is at most the total supply, so the unchecked subtraction cannot wrap.
- Read-only paths do not write storage, so they keep it too.
- Any finite sequence of these steps keeps the invariant, and each path's end state is shown to be one such step.

These theorems assume a hypothesis called `KeccakSep`, which is stated and not proved. It says that distinct addresses get distinct balance slots, and that balance slots and slot 1 never collide with the fixed slots 0 to 10 or with the slots of the other mappings. Since the slots are keccak outputs, this is a claim about the hash function.

The main theorem is `inv_call` in `UsdtVerify/Complete/Inv.lean`. From Berlin and before Glamsterdam, take any call to USDT, with any call data, any value and any gas. If the invariant holds before and the call ends without an error, the invariant holds after. Its hypotheses are `KeccakSep`, a call frame that is not static, an existing account for the contract, the contract not being deprecated, and the name and symbol slots being in a form Solidity writes.

### When the contract is deprecated

In deprecated mode the invariant can break. `destroyBlackFunds` asks the upgraded contract for the balance of the address, sets the local balance to 0, and lowers the local total supply by the answer. `UsdtVerify/Complete/DepInv.lean` proves:

- after that call, the invariant holds exactly when the upgraded contract's answer equals the local balance (`inv_tail_iff`, `depD_inv`), and this covers callees that call back into USDT,
- a concrete state where the invariant holds before and fails after, with an answer of 1 for a local balance of 0 (`exists_breaks`),
- the same failure for a whole run, for any callee that answers a different balance and leaves USDT's storage alone (`depD_breaks`).

So in deprecated mode the supply invariant depends on the upgraded contract answering honestly. The other deprecated functions are still in progress.

## What you have to trust

- The Lean 4 kernel.
- EthLib's EVM model being a faithful EVM. EthLib tests its model against the official Ethereum test vectors, but it does not prove the model correct. The proofs here are only as good as that model.
- The bytecode file being the deployed code, through the build-time test and `data/SOURCE.md`.

Every main theorem uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`. There is no `sorry` and no new axiom. Neither `native_decide` nor `bv_decide` is used. `decide +kernel` is used, and the kernel checks it.

A few general opcode rules are proved locally in `UsdtVerify/Local/` while they make their way into EthLib. They are proved from EthLib's semantics, not assumed.

## What is not covered yet

- Completeness of the deprecated paths, and the invariant for the deprecated functions other than `destroyBlackFunds`.
- Runs with less gas than the stated bounds, and forks outside the stated range.

## Related work

Certora formally verified rules for Tether's newer TetherToken contracts (Solidity 0.8.4, the `tether-contracts-hardhat` repository) in February 2024. That work targets a different, newer contract and works from the Solidity source. This repository targets the original 2017 contract on mainnet, at the level of its deployed bytecode.

## Building

You need [elan](https://github.com/leanprover/elan). The toolchain is pinned in `lean-toolchain`.

```
lake exe cache get
lake build
```

EthLib is fetched as a dependency at the commit pinned in `lakefile.lean`. Building EthLib from source takes a long time and several GB of memory. Once EthLib is built, this project builds in about 90 seconds and needs about 1.4 GB.

## Credits

Built on [EthLib](https://github.com/ethereum/EthLib). The proofs were written with [Claude Code](https://claude.com/claude-code).
