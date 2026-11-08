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

## Layout

- `UsdtVerify/Evm/` holds general EVM lemmas that are not about USDT, such as storage reads and writes, gas rules and call steps.
- `UsdtVerify/Usdt/Code.lean` and `UsdtVerify/Usdt/Map.lean` hold the bytecode, the dispatcher table and the storage layout.
- `UsdtVerify/Usdt/Spec/` says what each function does, one file per function.
- `UsdtVerify/Usdt/Proofs/` holds the block by block proofs, one file per function.
- `UsdtVerify/Usdt/Complete/` holds the completeness theorems.
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

These theorems assume a hypothesis called `KeccakSep`, which is stated and not proved. It says that distinct addresses get distinct balance slots, and that balance slots and slot 1 never collide with the fixed slots 0 to 10 or with the slots of the other mappings. Since the slots are keccak outputs, this is a claim about the hash function.

The main theorem is `inv_call` in `UsdtVerify/Usdt/Invariant/Calls.lean`. From Berlin, Glamsterdam included, take any call to USDT, with any call data, any value and any gas. If the invariant holds before and the call ends without an error, the invariant holds after. Its hypotheses are `KeccakSep`, the contract not being deprecated, and the name and symbol slots being in a form Solidity writes. It needs no hypothesis about static frames or the contract's account: on every writing path, a static frame or a missing account makes the first storage write fail, which is proved path by path.

### When the contract is deprecated

In deprecated mode the invariant can break. `destroyBlackFunds` asks the upgraded contract for the balance of the address, sets the local balance to 0, and lowers the local total supply by the answer. `UsdtVerify/Usdt/Invariant/DeprecatedDestroy.lean` proves:

- after that call, the invariant holds exactly when the upgraded contract's answer equals the local balance (`inv_tail_iff`, `depD_inv`), and this covers callees that call back into USDT,
- a concrete state where the invariant holds before and fails after, with an answer of 1 for a local balance of 0 (`exists_breaks`),
- the same failure for a whole run, for any callee that answers a different balance and leaves USDT's storage alone (`depD_breaks`).

So in deprecated mode the supply invariant depends on the upgraded contract answering honestly.

### Every call, deprecated or not

`inv_call_all` in `UsdtVerify/Usdt/Invariant/Static.lean` drops the "not deprecated" hypothesis. For any successful call to USDT, with any call data, value and gas, the invariant holds after if it held before. When the contract is deprecated it needs these named assumptions:

- `KeepsInv`: every message USDT sends to the upgraded contract that starts with the invariant and ends without an error ends with the invariant. It says nothing about USDT's account. This covers an upgraded contract that calls back into USDT. An earlier form that also tracked the account is kept as `KeepsInvAcc`. Neither form implies the other.
- `HonestBalance`, only for `destroyBlackFunds`: the balance the upgraded contract reports equals the local balance.

The six other forwarding functions write nothing locally after the forwarded call, which is also proved.

`inv_call_all` also covers static calls, such as a `STATICCALL` into USDT. A static run of USDT changes no state, so the invariant holds trivially. This uses a named assumption, `StaticKeeps`, about the message runner, which is proved for EthLib's own runner from Paris. No theorem of the invariant assumes the contract's account any more. A missing account at the forwarded call is proved harmless to USDT's own code, so the case is left to `KeepsInv`.

### Sequences of calls

`inv_calls` in `UsdtVerify/Usdt/Invariant/Seq.lean` lifts the invariant to any finite sequence of steps. A step is either a successful call that meets the hypotheses of `inv_call_all`, each with its own fork, message and runner, or a step that leaves every storage word of USDT unchanged. `goodCall_process` shows that a successful top-level message to USDT with no value, from Paris, is such a call. A failed call is proved to leave every storage word unchanged after the rollback (`untouched_process_failed`), using a general lemma proved here from EthLib's semantics: every step keeps the parent block of the state. A top-level call to USDT with a nonzero value always fails (`process_value_fails`). So `process_step` shows that every top-level message to USDT, from Paris, is one of the two kinds of step, with no assumption about failed calls.

## Security properties

`UsdtVerify/Usdt/Security/` proves five whole-contract properties, for one successful call with any call data, value and gas, and for sequences of calls. They hold from Berlin, Glamsterdam included, for static and non-static frames, when the contract is not deprecated.

- **Access control** (`Access.lean`). A caller who is not the owner changes only balance and allowance slots. The owner, the paused and deprecated flags, the fee settings, the upgraded address, the blacklist and the total supply keep their values.
- **Pause** (`Pause.lean`). While paused, every balance stays the same, unless the call is the owner's `issue`, `redeem` or `destroyBlackFunds`.
- **Blacklist** (`Blacklist.lean`). A blacklisted address's balance never decreases, except through the owner's `redeem` or `destroyBlackFunds`. So it cannot send tokens, directly or through `transferFrom`.
- **Allowances** (`Allowance.lean`). `transferFrom` moves at most the allowance, unless the allowance is `2^256 - 1`. Only `approve` and `transferFrom` change an allowance.
- **Supply** (`Supply.lean`). The total supply changes only through `issue` (+v), `redeem` (-v) and `destroyBlackFunds` (minus the destroyed balance).

Besides `KeccakSep`, some of these use a second hypothesis about keccak, `AllowSep`: an allowance slot is never one of the fixed slots or a blacklist slot.

When the contract is deprecated, the six forwarding functions hand the call to the upgraded contract, and `destroyBlackFunds` asks it for a balance. Each property then has a `*_call_all` and a `*_seq_all` version that covers deprecated calls under a named assumption about the upgraded contract, such as `KeepsSlots` (it leaves the protected slots alone). Some guarantees need no such assumption, deprecated or not:

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
- `KeccakSep` and `AllowSep` are hypotheses about keccak, not theorems.
- `KeepsInv`, `HonestBalance` and the `Keeps*` assumptions are not shown to hold for any real upgraded contract. They say what the upgraded contract must do. `UsdtVerify/Usdt/Sanity/Runner.lean` shows they can all hold at once: a runner whose upgraded contract only runs `STOP` meets every runner assumption except `HonestBalance`, and a runner that answers each address's local balance meets all of them. `UsdtVerify/Usdt/Sanity/` also gives, for every fork from Berlin, a concrete state and call where the success theorems of `transfer`, `approve`, `issue`, `redeem` and `destroyBlackFunds` apply and the run succeeds, so their hypotheses can all hold. The same is shown for `transferFrom`, the five security theorems and `inv_call_all`, except for the keccak hypotheses `KeccakSep` and `AllowSep`, which no concrete run can discharge. These examples are not deprecated, so for them the runner assumptions hold because the contract is not deprecated. The runners above show those assumptions can hold when it is.
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

EthLib is fetched as a dependency at the commit pinned in `lakefile.lean`. Building EthLib from source takes a long time and several GB of memory. Once EthLib is built, this project builds from clean in about 120 seconds with two threads and needs about 1.8 GB.

## Credits

Built on [EthLib](https://github.com/ethereum/EthLib). The proofs were written with [Claude Code](https://claude.com/claude-code).
