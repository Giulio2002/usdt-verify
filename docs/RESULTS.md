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
  one-counter gas meter (`Nat`). EthLib itself runs transactions with that meter up to BPO5. From
  Glamsterdam it runs them with the EIP-8037 meter `StateGasMeter` (docs/AUDIT.md, third audit,
  T1). So the Glamsterdam instances below are about the one-counter meter at that fork's prices,
  except the results of the sections "The EIP-8037 meter" (rounds 34 to 36) below. Forks: Berlin onwards, Glamsterdam included. Since round 17 the paths
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
  - Since round 29 the theorems assume `SepOn (callKeys message state)`, a stated hypothesis
    about keccak that is not proved. `callKeys message state` is the list of the four address
    words the call uses as mapping keys: the caller (masked), the first two address arguments,
    and the owner (the low 160 bits of slot 0 of the start state). `SepOn A` says, with "balance
    slot" meaning `keccak(x ++ 2)` for one of the 2^160 address words `x`:
    - `fixed`: none of the slots 0 to 10 is a balance slot (`FixedSep`);
    - `uniq`: for each address word `x` of `A`, no other address word has the balance slot of `x`
      (`UniqBal x`);
    - `list`: for each `y` of `A`, the slot `keccak(y ++ 6)` of `isBlackListed` is no balance slot
      and is not slot 1;
    - `allow`: for each `y`, `z` of `A`, the slot `keccak(y ++ keccak(z ++ 5))` of `allowed` is no
      balance slot and none of the slots 0 to 10.
    Each field is a finite number of facts, each comparing one given slot with the 2^160 balance
    slots (or with the 11 fixed slots). Treating keccak as a random function, each fails with
    probability about 2^160 / 2^256 = 2^-96, so for any given call the hypothesis is expected to
    hold; a call for which it fails would exhibit a keccak collision between a given slot and one
    of 2^160 others. It is not proved, and it is not shown for any particular call.
  - How the hypothesis changed (round 29, docs/AUDIT.md finding 1). Through round 28 the theorems
    assumed `KeccakSep`, the same separation for ALL key words at once: distinct addresses have
    distinct balance slots, no balance slot is a fixed slot or any slot of `isBlackListed` or
    `allowed`, slot 1 is no slot of `isBlackListed` or `allowed`. As written it quantifies over all
    2^256 key words (2^512 for `allowed`, 2^160 for `inj`), and by counting it is almost certainly
    false (about 11 expected hits for `fixed`, 2^256 collisions for `list` and `allow`, 2^63 for
    `inj`), so the theorems that assumed it were, as far as anyone can tell, vacuous. The new
    hypothesis is per call and about the slots the call writes. It is weaker: `KeccakSep` with
    `AllowSep` implies `SepOn A` and `SecSep A` for every `A` (`Security.sepOn_of_global`), so
    each old statement follows from the new one, with one exception: `Protected` (access
    control) now names the slots of `isBlackListed` of address words only, where it named those
    of every word (the code reads and writes only the former). `KeccakSep` and `AllowSep` are kept as
    definitions only for that corollary.
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

## The EIP-8037 meter, round 37: the security properties (Usdt/Security/)

From a frame `m` whose `toNat` is the fresh frame of `CODE`, for any gas bound and message runner
over `StateGasMeter`, any reservoir, refills allowed, no bound on the gas of the transaction,
from Berlin, with the hypotheses of the Nat form:

- One call, not deprecated: `nonOwner_call_any` (a caller other than the owner changes only
  slots of `balances` and `allowed`, and under `SecSep` every `Protected` slot keeps its word),
  `paused_call_any`, `listed_call_any`, `allowKept_call_any`, `transferFrom_bound_any`,
  `supply_call_any`. `owner_only_any` (every successful run of one of the ten owner functions is
  a call by the owner) and `nonOwner_local_any` hold deprecated or not, except for deprecated
  destroyBlackFunds.
- Sequences: `SeqS C Q` has steps over the meter `Nat` (`RunOk`), steps over `StateGasMeter`
  (`RunOkS`) and `Untouched` steps. `nonOwner_seqS`, `paused_seqS`, `listed_seqS`,
  `allowKept_seqS`, `supply_seqS` state the five properties over it. `process_stepSec`: from
  Paris, every top-level message with code `CODE`, no precompile, that EthLib's `processMessage`
  over `StateGasMeter` ends, from any starting meter (round 41), is a `RunOkS` step or an
  `Untouched` step.
- Route: `ends_any` gives, from such a run with no error, a loop of the meter `Nat` from a fresh
  frame of `CODE` with more gas that ends (`Gas.Ends`) in the same state (`Shadow.shadow_ends`).
  The properties depend only on the state.
- CALL over `StateGasMeter` (Evm/CallMeter.lean): `callStep_child_rS` (the message of a CALL
  with no value carries the reservoir of the frame, the caller keeps 0, and pays the execution
  gas of the CALL over `Nat`) and `resumeCall_sgm` (after the child, the caller has the fields of
  the resume over `Nat` but the gas, and its execution gas left and reservoir add up to those of
  the caller and the child).
- Not covered here: the deprecated paths over `StateGasMeter` (round 39, below).
- Round 38, one step at EXTCODESIZE, GAS and CALL (Evm/CallSim.lean, Evm/StepSim.lean):
  `Meter.step_simX` is `step_sim` at EXTCODESIZE and GAS too, from reservoir 0 (GAS pushes the
  execution gas left, which is the gas of the `toNat` frame). `Meter.step_callX`: at a CALL with
  0 as the value and the code of the called address found, from reservoir 0 and Berlin, the step
  over `StateGasMeter` fails or halts with an error (`callStep_low_rS`, `callStep_missingS`), or
  both steps give the same error or corresponding next frames (`callStep_deep_sim`), or both send
  the same message from callers related by `toNat`, the caller over `StateGasMeter` with
  reservoir 0 (`callStep_child_sim`). These are steps only. No run with a CALL over
  `StateGasMeter` is related to a run over `Nat` yet.

## The EIP-8037 meter, round 39: the deprecated paths

From Berlin, from a frame `m` of `StateGasMeter` with reservoir 0 whose `toNat` is the fresh frame
of `CODE`, deprecated, for any gas bound and message runner over `StateGasMeter`:

- Completeness (Usdt/Complete/Deprecated/Meter.lean): `dep_totalSupply_completeS`,
  `dep_balanceOf_completeS`, `dep_allowance_completeS`, `dep_transfer_completeS`,
  `dep_approve_completeS`, `dep_transferFrom_completeS`, `dep_destroy_completeS`. Each states the
  conclusion of its `dep_X_complete` for the caller, message, runner and child over
  `StateGasMeter`, without the gas left at the end and the bound on the gas after the CALL (for
  destroyBlackFunds also without `tailCost` and `tailStip`). The gas before the CALL and the gas of
  the message are exact.
- Invariant (Usdt/Invariant/DepMeter.lean): `inv_call_depS` under `KeepsInvAtS` and, for
  destroyBlackFunds, `HonestBalanceAtS`. `inv_call_anyD` adds the case not deprecated at any
  reservoir. `process_stepDS`: from Paris, a deprecated top-level message that `processMessage`
  over `StateGasMeter` ends from a starting meter with reservoir 0 (round 41: any such meter, not
  only the fresh meter of the message) is a `GoodCallDS` or an `Untouched` step.
  `process_stepSD` covers every case.
- Security (Usdt/Security/DepMeter.lean): `effect_allS` (deprecated or not, reservoir 0 when
  deprecated), `paused_call_allS`, `nonOwner_call_allS`, `listed_call_allS`,
  `allowKept_call_allS`, `supply_call_allS`, with the runner assumptions of the `_call_all` forms
  stated for the runner over `StateGasMeter` (`KeepsAtS`).
- Route: `RunC` (Evm/RunC.lean), `runC_of_sgm` (Evm/RunCS.lean). The `dep_X_complete` theorems
  over `Nat` now follow from `dep_X_completeC` over `RunC`, with unchanged statements.
- Not covered: a reservoir other than 0 when deprecated, the gas left after the CALL, the
  deprecated sequence forms of the security properties over `StateGasMeter`.

## The EIP-8037 meter, round 41: the fourth audit

- U1, the starting meter of `processMessage`. EthLib's `processMessageCall` runs the first frame
  with the meter left by the preparation of that frame. At Glamsterdam the authorizations of a
  type-4 transaction charge state gas to it and commit it, so it is not the fresh meter of the
  message. `goodCall_processS`, `process_value_failsS`, `process_stepS` (Usdt/Invariant/SeqMeter.lean),
  `process_stepDS`, `process_stepSD` (Usdt/Invariant/DepMeter.lean), `runOkS_process` and
  `process_stepSec` (Usdt/Security/Meter.lean) now take `processMessage fork message state
  substate meter held = .ok ended` for any `meter : StateGasMeter`. The deprecated forms ask
  `meter.reservoir = 0` in place of `message.reservoir = 0`. The forms for the fresh meter are the
  `_start` corollaries. `ProcessMeter.processMessage_map_valM`, `processMessage_map_val_valueM`
  and `at_startFrameS` take the starting meter too.

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
- Round 33 (docs/AUDIT.md, third audit, T5): each of these completeness theorems not deprecated
  (`ok_X`, the 19 read functions and the 13 writing ones, aliases `X_complete`) states the gas
  left as `cost ≤ gas ∧ s.gas = gas - cost`. Through round 32 the bound was not stated, so the
  `Nat` subtraction alone did not rule out a truncated 0.
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
  - `SepOn (callKeys message state)` (keccak keeps the slots keyed by the call's words apart from
    the balance slots; not proved; through round 28 `KeccakSep`);
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

- `inv_tail_iff`: assume `FixedSep`, `UniqBal a` (through round 28 `KeccakSep`), the contract `C`
  has an account in `S`, `a` is below 2^160, and `Inv C S`. Then `Inv` holds after the two writes if and only if `d` equals `balances[a]` in
  `S`.
- `exists_breaks`: a concrete counterexample, assuming only `NotBal 1` (slot 1 is the balance slot
  of no address word; through round 28 `KeccakSep`). The state is `zeroState C`: an empty account
  at `C` and no storage word set, so every word is 0 and `Inv` holds. With `a = 0` and the answer
  `d = 1`, `Inv` fails after the writes. Some hypothesis on slot 1 is needed: if slot 1 were the
  balance slot of exactly one address word, `Inv` would force every other balance to 0 and every
  such tail would keep `Inv` (argued, not proved).
- `depD_breaks` is the same at the level of runs. Assume the hypotheses of `spec_depD` and
  `SepOn (callKeys message state)`, `Inv` at the start, and these callee hypotheses:
  - `hans`: the callee succeeds and answers an output `o` of at least 32 bytes;
  - `hsame`: it keeps the contract's account and every word of the contract's storage;
  - `hne`: the first word of `o` is not `balances[a]` at the start.
  Then under every runner that meets the callee assumption, the run ends with no error and `Inv`
  false, or the runner aborts. No concrete runner, message and state that meet all of these
  hypotheses at once is constructed.
- `depD_inv` assumes the hypotheses of `spec_depD`, `SepOn (callKeys message state)`, and a callee hypothesis
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
and any message runner. Assume `SepOn (callKeys message state)`, `StrForm` of slots 7
and 8, and `Inv` at the start (through round 18 also a frame that is not static). When the
contract is deprecated, also assume (through round 19 also an account for the contract `C`):
- `KeepsInvAt` (`hkeeps`; round 29, see below): whenever the runner ends with no error a call
  that the code of `C` makes from `state` to `ua` (`SentVia`), and `Inv` held in the caller's
  state, then `Inv` holds in the child's end state. It asks nothing about the account of `C`
  (round 20). The callee may call back into `C`; this assumption is about the end state only, so
  it covers that;
- for destroyBlackFunds, `HonestBalanceAt` (`hhonest`): for such a call with the data
  `balanceOf(a)`, the word written at 0x60 is `balances[a]` in the child's end state.

How these changed (round 29, docs/AUDIT.md finding 2). Through round 28 they were `KeepsInv` and
`HonestBalance`, which quantify over every caller frame and every message from `C` to `ua`,
including the message's code; EthLib's runner `processRunner` runs that code, so it met them for
no `ua`. `SentVia message state ua caller msg` (Evm/Keeps.lean) now restricts them to the calls
the code actually makes: the caller state has the storage and the code of `state` at every
address (`SameView`; the code only records reads before its CALL), and `msg` is the message of
`SendsVia`: from `C` to `ua`, with the code that `ua` holds in `state` (along its EIP-7702 route),
no value, the depth and static flag of the call to `C`; its data and gas are any. The completeness
theorems give these facts for every forwarding CALL (`dep_*_local`). The old forms imply the new
ones (`keepsInv_at`, `honest_at`, `Keeps.at`). Round 33: `KeepsInvAcc` gives `KeepsInvAt` only
together with `KeepsInvNoAcc` (`keepsInvAt_of_acc`), since `SameView` allows a caller state where
`C` has no account. No theorem gives `KeepsInvAt` from `KeepsInvAcc` alone. EthLib's `processRunner` meets `KeepsInvAt` (and
the five `Keeps*` of the security theorems) from Paris when `ua` holds the one byte STOP and is no
precompile (`Sanity.processRunner_stop_keepsAll`, `Sanity.keepsInvAt_process_stop`).
Round 30: `processRunner` meets `HonestBalanceAt` from Paris when `ua` holds `MIRROR` (a 25-byte
contract that answers `balanceOf(a)` with slot `keccak(a ++ 2)` of its own storage), is no
precompile, and that slot of `ua` holds in `state` the word of `balances[a]` of `C`
(`Sanity.honestBalanceAt_process_mirror`). The last condition is a hypothesis on `state` for the
one queried slot; nothing makes a deployed upgraded contract keep it.
If the interpreter loop ends with no error, `Inv` holds in the end state.
Nothing is assumed of the code of `ua` (round 16: the hypothesis `hdel` is gone). When that code
is an EIP-7702 delegation, the message still has `ua` as its current target and runs the
delegate's code (`SendsVia` along the route), so `KeepsInvAt` and `HonestBalanceAt` apply to it as
stated.

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
- `inv_calls`: `Inv C S` and `Calls C S S'` give `Inv C S'`. Since round 29 each `GoodCall` carries
  its own keccak hypothesis `SepOn (callKeys message S)` at its start state `S` (through round 28,
  `inv_calls` took one global `KeccakSep`); `goodCall_process` and `process_step` take it for the
  message they classify.
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

## Security properties (round 22)

`UsdtVerify/Usdt/Security/`. Each theorem is about one run of the deployed code from Berlin on
(Glamsterdam included): a fresh frame of the code at pc 0, any call data below 2^256 bytes, any
value, any gas, any gas bound and any message runner, static or not, that ends with no error.
Each single-call theorem and `nonOwner_seq`, `paused_seq`, `listed_seq` take "not deprecated"
(`hdep`: byte 20 of slot 10 is 0) and, except `transferFrom_bound`, slots 7 and 8 of `StrForm`
(`h7`, `h8`; the completeness proofs of name() and symbol() use them); `allowKept_seq` and
`supply_seq` take both in each call's predicate instead; the `Effect.*` lemmas take neither.
The keccak hypotheses (round 29) are `SepOn (callKeys message state)` (as for the invariant) and,
where named, `SecSep (callKeys message state)`: `SepOn`, and moreover the balance slots of the
call's address words and the slots of `allowed` keyed by two of them are no slot of
`isBlackListed` of an address word (each one given slot against 2^160 others; not proved).
Through round 28 they were the global `KeccakSep` and `AllowSep`, almost certainly false
(docs/AUDIT.md, finding 1). Two conclusions were narrowed with the hypothesis, because a global
conclusion would need a global hypothesis: the protected slots of `isBlackListed` are those of
address words (through round 28 of every word), and `allowKept_*` keep the one slot of `allowed`
keyed by given words `y`, `z`, under `SecSep` of the call's keys and `y`, `z` (through round 28
every slot of `allowed` at once). The owner functions' write class `OwnW message` names the one
slot of `isBlackListed` they write (that of the first address argument).
The owner is the low 160 bits of slot 0; the caller is compared with it masked to 160 bits, as
the code does.

- `effect_call` (Effect.lean): every such run ends in a state described by one case of `Effect`,
  built from the completeness theorems: no slot changed; transfer or transferFrom (fee 0 or not)
  with the checks the run passed (not paused, the sender, or `_from`, not blacklisted, the
  allowance check) and its end state; approve (only `allowed[caller][spender]` may change); an
  owner function that writes only slots 0, 3, 4, 10 and slots of `isBlackListed`; issue, redeem,
  destroyBlackFunds by the owner, with their end states.
- Access control, `nonOwner_call` (Access.lean): if the caller is not the owner, only slots of
  `balances` and of `allowed` change. Under `SecSep` of the call's keys, slots 0 (owner, `paused`),
  1 (`_totalSupply`), 3, 4, 10 (`upgradedAddress`, `deprecated`) and the slot of `isBlackListed`
  of every address word keep their words.
- Pause, `paused_call` (Pause.lean): from a paused state (byte 20 of slot 0 not 0), under
  `SepOn` of the call's keys, every balance keeps its word, or the caller is the owner and the function is
  issue, redeem or destroyBlackFunds.
- Blacklist, `listed_call` (Blacklist.lean): for an address word `a < 2^160` whose
  `isBlackListed` low byte is not 0 at the start, under `SepOn` of the call's keys, `balances[a]` is not lower
  at the end, unless the run is the owner's redeem or destroyBlackFunds (`hsel`). This covers
  transfer by `a` and transferFrom with `_from = a`.
- Allowances (Allowance.lean): `transferFrom_bound` (under `SepOn` of the call's keys): with `A` the allowance
  `allowed[_from][caller]` at the start, `A = MAX_UINT` or `v ≤ A`; `balances[_from]` at the
  start is at most `balances[_from]` at the end plus `v`; if `A ≠ MAX_UINT` the allowance at the
  end plus `v` is `A`; if `A = MAX_UINT` the allowance stays `MAX_UINT`. `allowKept_call` (for
  words `y`, `z`, under `SecSep` of the call's keys and `y`, `z`): when the selector is neither
  approve nor transferFrom, the slot of `allowed` keyed by `y` and `z` keeps its word
  (`AllowKeptAt y z`).
- Supply, `supply_call` (Supply.lean, under `SepOn` of the call's keys): slot 1 keeps its word, or the owner
  called issue (slot 1 becomes `T + v` as numbers), redeem (`T - v` as numbers) or
  destroyBlackFunds (`T - balances[a]` as a 256-bit subtraction, unchecked in the code), with `T`
  and `balances[a]` read at the start.

Over sequences: `Seq C Q S S'` is a finite sequence of successful runs of the code for messages
to `C` (each as above, with the predicate `Q` on its message and start state) and of `Untouched`
steps (any change that keeps every storage word of `C`); `seq_lift` lifts a reflexive and
transitive relation with an invariant to it.
- `nonOwner_seq`, `paused_seq`, `listed_seq` (`Q` = `NotOwnerK`: the caller is not the owner of
  that call's start state, and `SecSep` of the call's keys there): from a state that is not
  deprecated with slots 7 and 8 of `StrForm` (and paused, for `paused_seq`; with `a` blacklisted,
  for `listed_seq`):
  only slots of `balances` and `allowed` change and the `Protected` slots keep their words; every
  balance keeps its word; `balances[a]` is not lower at the end. Not deprecated, `StrForm`, the
  flags and the owner are kept along the sequence, so they are needed only at the start.
- `allowKept_seq` (`Q` = `NoAllowFn y z`: neither approve nor transferFrom, not deprecated,
  `StrForm` and `SecSep` of the call's keys and `y`, `z` at that call's start state; any caller):
  the slot of `allowed` keyed by `y` and `z` keeps its word.
- `supply_seq` (`Q`: none of issue, redeem, destroyBlackFunds, not deprecated, `StrForm` and `SepOn`
  of the call's keys at that call's start state; any caller): slot 1 keeps its word.

Not covered by these theorems: deprecated calls (the forwarding functions end in the state the
upgraded contract's call left, which is the runner's; round 23 below), and runs that are not a
fresh frame of the code (a call through another contract is covered only as a run of the code,
not as part of the outer transaction).

## Security properties, deprecated or not (round 23)

Same runs as in round 22 (from Berlin, Glamsterdam included; a fresh frame of the code at pc 0;
any call data below 2^256 bytes, any value, any gas, any gas bound and any message runner;
static or not; ending with no error; slots 7 and 8 of `StrForm` where taken), with no `hdep`.

Which functions read the flag. Seven functions branch on the `deprecated` flag: approve,
totalSupply, transferFrom, balanceOf, transfer, allowance (`FwdFn`: when deprecated they call the
upgraded contract; what they return is in their forward specifications, Spec/Deprecated/, not in
the theorems of this section) and destroyBlackFunds (`FlagFn` adds it: when
deprecated it asks the upgraded contract for `balanceOf(a)` and then writes locally). The other
25 entries of the table (the nine owner functions other than destroyBlackFunds, 14 getters,
name and symbol) have completeness theorems `ok_X` that take no hypothesis on the flag, so
those theorems hold when deprecated too. Cross-check by a script over the bytecode (not a proof):
it has six CALL opcodes and no CALLCODE, DELEGATECALL or STATICCALL; destroyBlackFunds reaches
the CALL of balanceOf (at 4891) through an internal jump (Spec/Deprecated/Destroy.lean).

The effect of a run (Effect.lean):
- `effect_local`: `effect_call` with `hdep` replaced by "not deprecated, or the selector is not
  one of the seven of `FlagFn`". So when deprecated, those 25 functions have the same `Effect`
  as when not deprecated, with no assumption on the runner.
- `effect_all`: every run ends in a state described by one case of `EffectD`, with no
  assumption on the runner: `loc` (an `Effect`); `fwd` (deprecated, one of the six of `FwdFn`:
  the runner ended with no error one call whose caller is `C` and whose current target is the
  upgraded address `upAddr` (the low 160 bits of slot 10), sent from a caller state whose storage
  at `C` is the start storage at `C`, and the end state is that call's child end state; for
  transfer, not paused and the caller not blacklisted at the start; for transferFrom, not paused
  and `_from` not blacklisted at the start); `dfwd` (deprecated destroyBlackFunds: the caller is
  the owner, `a` is blacklisted at the start, the same kind of call from a state with the start
  storage at `C` to a child end state `Y` in which `C` has an account, and the end state is
  `tailState Y C a d`: `balances[a] := 0`, then slot 1 `:=` (slot 1 in that state) `- d`, for some
  word `d`; the proof uses the word the call returned, the statement does not record it).

The runner assumptions (Evm/Keeps.lean, and one definition per property). Since round 29
`KeepsAt runChild message S ua R`: every call that the code of `C` makes from `S` to `ua`
(`SentVia`, as for `KeepsInvAt` above) that the runner ends with no error goes from its caller
state `X` to its child's end state `Y` with `R X Y`. It covers whatever the callee does (reentrant
calls into `C` included). Each single-call theorem below takes it as `hkeeps : byte20 (slot 10) ≠ 0 →
Keeps… runChild message state`, so it is used only when deprecated; the sequence forms carry it
in each `RunOkR` step. Through round 28 they were `Keeps runChild C ua R`, over every message from
`C` to `ua` (finding 2, below). EthLib's `processRunner` meets all five from Paris when the
upgraded address holds STOP and is no precompile (`Sanity.processRunner_stop_keepsAll`).
- `KeepsSlots`: every `Protected` slot of `C` keeps its word (`ProtKept`: slots 0, 1, 3, 4, 10
  and every slot of `isBlackListed`).
- `KeepsBal`: every slot of `balances` of `C` (address word below 2^160) keeps its word.
- `KeepsListed`: for every address word `a < 2^160` blacklisted in `X`, `balances[a]` in `Y` is
  not lower than in `X`.
- `KeepsAllow`: every slot of `allowed` of `C` keeps its word.
- `KeepsSupply`: slot 1 of `C` keeps its word.

Audit finding 2 (docs/AUDIT.md), resolved in round 29: through round 28 these assumptions, like
`KeepsInv` and `HonestBalance`, quantified over every caller frame and every message from `C` to
`ua`, the message's code included, and were false for EthLib's own runner `processRunner`,
whatever the upgraded contract (a message whose code writes `C`'s slot 1 broke each of them).
The `At` forms quantify only over the calls the code makes, whose code is the code `ua` holds.

One call, deprecated or not:
- `nonOwner_call_all` (`SecSep` of the call's keys, `KeepsSlots`): if the caller is not the owner,
  every `Protected` slot keeps its word. (When not deprecated, `nonOwner_call` also gives that
  only slots of `balances` and `allowed` change; this form does not state it.)
- `paused_call_all` (`SepOn` of the call's keys, `KeepsBal`): from a paused state, every balance keeps its word,
  or the caller is the owner and the function is issue, redeem or destroyBlackFunds.
- `listed_call_all` (`SepOn` of the call's keys, `KeepsListed`): for `a < 2^160` blacklisted at the start,
  `balances[a]` is not lower at the end unless it is the owner's redeem or destroyBlackFunds.
- `allowKept_call_all` (`SecSep` of the call's keys and `y`, `z`, `KeepsAllow`): when the selector
  is neither approve nor transferFrom, the slot of `allowed` keyed by `y` and `z` keeps its word.
- `supply_call_all` (`SepOn` of the call's keys, `KeepsSupply`): `SupplyStepD`, that is `SupplyStep` (slot 1
  kept, or the owner's issue `+ v`, redeem `- v`, destroyBlackFunds `- balances[a]`), or the
  owner's destroyBlackFunds with slot 1 at the end equal to slot 1 at the start minus some word
  `d` (256-bit subtraction). Neither this statement nor `EffectD.dfwd` says what `d` is; only the
  proof of `effect_all` takes it to be the word the call returned.

What the code alone guarantees when deprecated (no runner assumption):
- `owner_only` (Access.lean): every successful run of one of the ten `onlyOwner` functions
  (`OwnerFn`: deprecate, addBlackList, unpause, pause, setParams, issue, redeem, removeBlackList,
  transferOwnership, destroyBlackFunds) is a call by the owner of the start state, deprecated or
  not. No `StrForm` hypothesis.
- `nonOwner_local` (`SecSep` of the call's keys): for a caller other than the owner and any function
  outside the six of `FwdFn`, deprecated or not, only slots of `balances` and `allowed` change
  and every `Protected` slot keeps its word.
- `transfer_checks_all`, `transferFrom_checks_all` (Pause.lean): every successful transfer
  starts from a state that is not paused, with the caller not blacklisted; every successful
  transferFrom from a state that is not paused, with `_from` not blacklisted; deprecated or not.
  No `StrForm` hypothesis.
- With `effect_local`: pause, unpause, addBlackList, removeBlackList, setParams, deprecate,
  transferOwnership, issue and redeem do not branch on the flag (their `ok_X` take no hypothesis
  on it). So when deprecated their effect on
  the storage is the same `Effect`, with no runner assumption.
- Where the proofs use the runner assumptions (the statements take each one whenever
  deprecated): in `EffectD.paused` the forwarded transfer and transferFrom are ruled out by their
  pause check, so `KeepsBal` is used only for the forwarded approve, totalSupply, balanceOf and
  allowance. Deprecated destroyBlackFunds is ruled out by "not the owner" in
  `nonOwner_call_all` and by `hsel` in `listed_call_all`. `allowKept_call_all` and
  `supply_call_all` use their assumption for its call too.
- `transferFrom_bound` has no deprecated form: deprecated transferFrom forwards, so the
  allowance it reads and writes is the upgraded contract's.

Over sequences: `SeqR C R Q` is `Seq` with steps `RunOkR C R` (a `RunOk` step whose runner meets
`Keeps runChild C (upAddr S message) R` when `C` is deprecated at its start state `S`), and
`seqR_lift` lifts as `seq_lift` does. `Strs` is "slots 7 and 8 of `StrForm` at the call's start
state"; it is part of each call's predicate `Q` here (in round 22 it was kept from the start for
`nonOwner_seq`, `paused_seq`, `listed_seq`, and was already per call for `allowKept_seq`,
`supply_seq`). The keccak hypotheses are per call, in `Q` (round 29): `SecSep` of the call's keys
for the first three below, `SecSep` of the call's keys and `y`, `z` for `allowKept_seq_all`,
`SepOn` of the call's keys for `supply_seq_all`.
- `nonOwner_seq_all` (`R = ProtKept C`, `Q = NotOwnerS`: not the owner, `Strs`, `SecSep`): every `Protected`
  slot keeps its word.
- `paused_seq_all` (`R`: `ProtKept C` and `BalKept C`, `Q = NotOwnerS`), from a paused state:
  every balance keeps its word.
- `listed_seq_all` (`R`: `ProtKept C` and `ListedNoDec C`, `Q = NotOwnerS`), with `a < 2^160`
  blacklisted at the start: `balances[a]` is not lower at the end.
- `allowKept_seq_all` (`R = AllowKept C`, `Q = NoAllowFnS y z`: neither approve nor transferFrom,
  `Strs`, `SecSep` of the keys and `y`, `z`): the slot of `allowed` keyed by `y` and `z` keeps its
  word.
- `supply_seq_all` (`R = SupplyKept C`, `Q`: none of issue, redeem, destroyBlackFunds, `Strs`,
  `SepOn`):
  slot 1 keeps its word.

## Non-vacuity: the assumptions can hold together (round 24)

`UsdtVerify/Usdt/Sanity/`. These theorems show that the hypotheses of the main theorems can all
hold at once, for some runner, state, message and gas. They do not prove the keccak hypotheses
`SepOn` / `SecSep` of the witness calls' keys (finitely many separation facts, each expected to
hold, see the invariant above; through round 28 they assumed the global `KeccakSep` and
`AllowSep`, almost certainly false, docs/AUDIT.md finding 1). Most runners here are not
`processRunner`; `Sanity/Process.lean` (round 29) shows that `processRunner` meets the `At` forms
of the runner assumptions when the upgraded address holds STOP, and `Sanity/Mirror.lean` (round
30) that it meets `HonestBalanceAt` when the upgraded address holds `MIRROR` and its queried slot
mirrors USDT's.

Runner assumptions (`Sanity/Runner.lean`, `Evm/Runners.lean`):
- `keepsAll_of_same`: if every message from `C` to `ua` that the runner ends with no error
  leaves the storage of `C` as it was in the caller state, then the runner meets `KeepsSlots`,
  `KeepsBal`, `KeepsListed`, `KeepsAllow`, `KeepsSupply` and `KeepsInvAt`.
- `stop_keeps_all`: `stopRunner fork bound (upAddr S message)` meets all six, for every message
  and state, at every fork.
  On a message to `ua` whose code is the one byte STOP and that has a target, no value and no
  precompile, `stopRunner` is EthLib's `processRunner`, and on a message to another address it is
  `processRunner` too. It fails every other message to `ua`.
  `stop_staticKeeps`: from Paris it meets `StaticKeeps`.
  `stopRunner` is not `processRunner`; for `processRunner` itself see `Sanity/Process.lean` below.
- `balRunner` ends every message at once with no error and keeps the state. Its answer is the 32
  bytes of the word at slot `keccak(x ++ 2)` of the message's caller, where `x` is the word at
  byte 4 of the message's data. `runner_assumptions_hold`: it meets all six, `StaticKeeps` at
  every fork, and `HonestBalanceAt` for every message and state.
  `honestBalance_of_answers`: `HonestBalance` holds whenever each forwarded `balanceOf(a)` that
  ends with no error answers at least 32 bytes whose first word is `balances[a]` of the contract
  in the child's end state.
- `balRunner` is not the run of any code.
- `Sanity/Process.lean` (round 29): `processRunner_stop_keepsAt`: from Paris, when the upgraded
  address of `message` in `S` holds `STOP_CODE` (the one byte STOP) and is no precompile, EthLib's
  `processRunner` at any bound meets `KeepsAt … R` for every reflexive `R` (each call the code
  makes ends with no error in its caller state, `process_stop`). So it meets all six `At` forms
  (`processRunner_stop_keepsAll`), and `KeepsInvAt (processRunner fork message.gas) message S`,
  the deprecated-case hypothesis of `goodCall_process` and `process_step`
  (`keepsInvAt_process_stop`). STOP is a real contract, though not a useful one; it answers no
  word, so it does not give `HonestBalanceAt`.
- `Sanity/Mirror.lean` (round 30): `honestBalanceAt_process_mirror`: from Paris, when the upgraded
  address of `message` in `S` holds `MIRROR` (Evm/Mirror.lean: `PUSH1 2 PUSH1 32 MSTORE PUSH1 4
  CALLDATALOAD PUSH1 0 MSTORE PUSH1 64 PUSH1 0 KECCAK256 SLOAD PUSH1 0 MSTORE PUSH1 32 PUSH1 0
  RETURN`), is no precompile, and `storageAt S ua (balSlot message) = storageAt S C (balSlot
  message)` (`hmirror`), `processRunner` at any bound meets `HonestBalanceAt … message S`. MIRROR
  reads its own storage, so `hmirror` is needed: its answer is USDT's balance only when its slot
  holds the same word. Every gas is covered: `process_mirror` (from `mirror_spec`, the exact
  gas `87 + slotCost`, and `Complete.ok_exact`) says that a run that ends with no error returns
  the word, and `HonestBalanceAt` asks nothing of a run that ends with an error. MIRROR only reads,
  so USDT's slot in the child's end state is the slot of `S`.

Spec preconditions (`Sanity/Transfer.lean`, `Calls.lean`, `TransferFrom.lean`). Each `*_sat` holds
at every fork from Berlin and for every block, transaction, contract address `C` and substate.
It gives a message to `C` running `CODE`, a start state `sState C kvs` and a gas. `sState C kvs`
has one account, at `C`, and the slots `kvs`. From these the interpreter loop, with
`processRunner`, ends with no error. The proof applies the spec theorem in parentheses, so every
hypothesis of that theorem holds there:
- `transfer_ok_sat` (`TransferOk.runFrame_ok`): `transfer(to, 1)` by any caller, with
  `balances[caller]` = 256.
- `transferFrom_ok_sat` (`TransferFrom.runFrame_ok`): `transferFrom(f, to, 1)` by any caller,
  with `allowed[f][caller]` = `balances[f]` = 256.
- `approve_set_sat` (`Approve.runFrame_set`): `approve(s, 1)`, with every slot 0.
- `issue_sat`, `redeem_sat` (`IssueSpec.runFrame_issue`, `runFrame_redeem`): `issue(1)`,
  `redeem(1)` by the owner `CALLER_A` (twenty bytes 0x01).
- `destroy_sat` (`DestroySpec.runFrame_spec`): `destroyBlackFunds(a)` by the owner, for any `a`,
  with `isBlackListed[a]` = 1.
No fact about keccak is used. In each state every slot holds one of a few words, and each check
passes for each of them, whichever slots collide.

Security theorems and the invariant (`Sanity/Security.lean`, `TransferFrom.lean`). `OkRun M S
ss`: some gas and a frame for which `At CODE M 0 [] .empty gas S ss` holds, from which the
interpreter loop with `processRunner` ends with no error. There are four witnesses, each with
`OkRun` and the other hypotheses that are not about keccak:
- `transfer_witness`: not deprecated, slots 7 and 8 of `StrForm`, the caller is not the owner,
  and the selector is transfer's.
- `paused_witness`: `approve(s, 0)` while paused.
- `listed_witness`: `approve(s, 0)` with `Listed C S a`.
- `inv_witness`: `approve(s, 1)` from the state with every slot 0, where `Inv` holds (`inv_empty`).
Each `_applies` theorem takes `SepOn` or `SecSep` of the witness call's keys (and of `y`, `z` for
the allowance), and applies the theorem to
a witness, so it discharges every other hypothesis. They cover `nonOwner_call` and `_call_all`,
`allowKept_call` and `_call_all`, `supply_call` and `_call_all`, `paused_call` and `_call_all`,
`listed_call` and `_call_all`, `inv_call_ns`, `inv_call_all` and `transferFrom_bound`.
No witness run is deprecated. So the runner hypotheses of the `_call_all` forms and of
`inv_call_all`, which these theorems take only when deprecated, hold there because they are never
needed. Their satisfiability is shown separately, above.

`StrForm` (`Sanity/Strings.lean`): `strForm_name` and `strForm_symbol` prove that `NAME_WORD` and
`SYMBOL_WORD`, the slot words of "Tether USD" and "USDT", are of `StrForm`.
`inv_mainnet`: under `FixedSep`, `Inv` holds in the state whose slots 7 and 8 hold them.
`strings_applies`: under `SepOn` of the call's keys, `inv_call_all` and `supply_call` apply to `approve(s, 0)`
from that state.

## Exact success conditions (rounds 25, 26)

`UsdtVerify/Usdt/Exact/`, with the conditions in `UsdtVerify/Usdt/Spec/Guards.lean` and the generic
lemmas in `UsdtVerify/Evm/Iff.lean`.
Completeness says that every run that ends with no error is a proved success path.
These theorems add the converse: with the gas of the success path (its cost and stipend bounds),
the success path is taken whenever its condition holds.
`RunsOk fork bound runChild evm within` says that the loop of the interpreter, run from `evm`,
returns a frame with no error (a REVERT or a fault sets an error).

For each function below, from Berlin, a fresh frame of `CODE` at pc 0, call data below `2^256`
bytes with the function's selector, the coldness flags named as in the specs, any gas bound and
any message runner:
- `X_ok_iff`: if the gas is at least the cost of the success path, and at least each stipend bound
  the success specification takes (more than 2300 gas left at an SSTORE, EIP-2200), then
  `RunsOk` holds if and only if the condition holds.
- `X_low`: if the gas is below the cost of the success path, `RunsOk` does not hold, whatever the
  condition.

Round 26 closes the gap between the two, for the 13 functions that write:
- `X_mid`: if the gas is at least the cost but below the stipend bound, `RunsOk` does not hold,
  whatever the condition. When the condition holds, the run reaches an SSTORE with at most 2300
  gas left. From Istanbul such an SSTORE fails (EIP-2200), with that gas and with any less
  (`Gas.sstore_low_stuck`, `Gas.NoWrite`, `Gas.no_ok_stuck_at`, `Exact.not_runsOk_stuck`). On a
  path with two SSTOREs the proof splits on which one is reached with at most 2300 gas left
  (`low_issue2`, `low_redeem2`, `low_setParams2`, `low_deprecate2`, `DestroySpec.low2`,
  `low_transfer2`). On transferFrom only the last SSTORE can be reached so, since the cost covers
  the stipends of the earlier ones (`low_transferFrom2`).
- `X_iff_gas`: for every gas, `RunsOk` holds if and only if the condition holds and the gas is at
  least `max cost stip` (`iff_max`). The stipend bound `stip`: pause `3297 + price(slot 0)`,
  unpause `3184 + price(slot 0)`, addBlackList `2779 + ...`, removeBlackList `3307 + ...`, issue,
  redeem, setParams, deprecate: the bound of their second SSTORE, as in `X_ok_iff`;
  destroyBlackFunds: the larger of its two bounds; transferOwnership: `ownershipStip` (none when
  `a = 0`); approve: `approveStip`; transfer: `transferStip` (`transferStip2` with a fee of 0,
  none with a fee); transferFrom: `transferFromStip` (`stipCostF` with a fee of 0, none with a
  fee). With a fee the logs after each SSTORE cost more than 2300, so the cost covers the
  stipends.

The conditions, in plain terms (each is a `def` in `Guards.lean`):
- `CallOk`: at least 4 bytes of call data and no value.
  The 19 functions that only read succeed exactly when `CallOk` holds: decimals, maximumFee,
  _totalSupply, basisPointsRate, deprecated, paused, upgradedAddress, owner, getOwner, MAX_UINT,
  balances, isBlackListed, getBlackListStatus, allowed; totalSupply, balanceOf and allowance when
  not deprecated (`hdep`); name and symbol when their slot word is of `StrForm` (gas `strCost`,
  by the form of the word).
- `CanWrite`: the frame is not static and `C` has an account. `IsOwner`: the caller, as a word,
  is the low 160 bits of slot 0.
- pause: `CallOk`, `CanWrite`, `IsOwner`, not paused. unpause: the same, but paused.
- addBlackList, removeBlackList, deprecate: `CallOk`, `CanWrite`, `IsOwner` (`OwnerWriteGuard`).
- issue(a): `CallOk`, `CanWrite`, `IsOwner`, `0 < a`, `_totalSupply + a < 2^256`,
  `balances[owner] + a < 2^256`.
- redeem(a): `CallOk`, `CanWrite`, `IsOwner`, `a ≤ _totalSupply`, `a ≤ balances[owner]`.
- setParams(b, m): `CallOk`, `CanWrite`, `IsOwner`, `b < 20`, `m < 50`, `m * 10^decimals < 2^256`
  (`10^decimals` as the EVM word `exp 10 (slot 9)`).
- transferOwnership(a): `CallOk`, `IsOwner`, and `CanWrite` when `a ≠ 0` (gas `ownershipCost`,
  by `a`).
- destroyBlackFunds(a), not deprecated: `CallOk`, `CanWrite`, `IsOwner`, `a` blacklisted.
- approve(s, v), not deprecated: `CallOk`, `CanWrite`, at least 68 bytes, and if `v ≠ 0` the
  allowance `allowed[caller][s]` is 0 (gas `approveCost`, stipend `approveStip`, by `v`).
- transfer(a, v), not deprecated: `CallOk`, `CanWrite`, at least 68 bytes, not paused, the caller
  not blacklisted, `v * basisPointsRate < 2^256`, `fee ≤ v`, `v ≤ balances[caller]`,
  `balances[a] + (v - fee) < 2^256` (read after the sender's write), and if `fee ≠ 0`
  `balances[owner] + fee < 2^256` (read after the recipient's write). Gas `transferCost` (by the
  fee); with a fee of 0 also the stipends `transferStip1`, `transferStip2`.
- transferFrom(f, t, v), not deprecated: `CallOk`, `CanWrite`, at least 100 bytes, not paused,
  `f` not blacklisted (the caller's status is not read), `v * basisPointsRate < 2^256`, the
  allowance `allowed[f][caller]` is `MAX_UINT` or at least `v`, `fee ≤ v`, `v ≤ balances[f]`,
  `balances[t] + (v - fee) < 2^256`, and if `fee ≠ 0` `balances[owner] + fee < 2^256` (each read
  where the code reads it). Gas `transferFromCost`; with a fee of 0 also the stipend `stipCostF`.

The terms of transfer and transferFrom are the words the bytecode computes (`feeOf`, `balS`,
`balT`, `balO`, `allowOf`, `balFrom`, `balTo`, `balOF`), read in the state after the reads of the
checks; reads change no slot, so the slots hold the words of the start state, except the balances
read after a write, as stated.

When deprecated (`Usdt/Exact/Deprecated.lean`), the seven functions that forward to the upgraded
address (totalSupply, balanceOf, allowance, transfer, approve, transferFrom, destroyBlackFunds)
have `X_dep_ok_iff` and `X_dep_low`. Their hypotheses: the flag set (`hdep`), the code `c` of the
upgraded address found in the state (and, for `X_dep_ok_iff`, `c.size < 2^256`), the route `r` of the CALL, the
coldness flags, the gas up to the CALL (`hg`) and after its price (`htail`), and two hypotheses on
the message runner: it fails on none of the messages the path sends (`NoFailOn`, since round 29;
`NoFail`, a frame for every message, through round 28), and each
message it is given that is the forward along the route ends with no error exactly when a
condition `A` holds (`hans`; round 30: only the message the CALL sends with the gas it gives, from
the caller frame at the CALL, whose state and substate are given, `CallFrom`). For destroyBlackFunds, `A` is instead the condition for "the forward
ends with no error and the contract has an account in its end state".
- `X_dep_ok_iff`: `RunsOk` holds if and only if the checks before the forward hold and `A` holds.
  The checks: `ForwardOk` (`CallOk`, `0 < c.size`, the depth leaves room for one more frame) for
  totalSupply, balanceOf, allowance; `TransferDepGuard` (also not paused, the caller not
  blacklisted); `ApproveDepGuard` (also at least 68 bytes); `TransferFromDepGuard` (also not
  paused, `f` not blacklisted); `DestroyDepGuard` (also `IsOwner`, `a` blacklisted, not static).
  Since round 27 the six other than destroyBlackFunds are derived from `X_dep_ok_iff_fails`
  (below): with `htail` the gas after the CALL is enough, and under `NoFailOn` `hfail` holds.
  Since round 29 they (and the six `X_dep_ok_iff_gas`, and `destroyBlackFunds_dep_ok_iff_gas`)
  take `NoFailOn runChild (SendsVia message ua c r d)`: the runner fails on none of the messages
  the path sends, in place of `NoFail` (it fails on no message at all). `NoFail.on` gives the new
  form from the old. Round 30: `destroyBlackFunds_dep_ok_iff` takes `NoFailOn` too; it is derived
  from `destroyBlackFunds_dep_ok_iff_fails` (with `htail` the tail has its gas, `tail_le_max`).
- `X_dep_low`: if the gas is below the bound of `hg`, `RunsOk` does not hold, for every runner.
- Audit finding 3 (docs/AUDIT.md), rounds 29 and 30. `NoFail` is false for `processRunner`, which
  fails a message whose value exceeds the caller's balance; the messages the path sends carry no
  value, and `NoFailOn` asks only of them. Through round 29, `hans` asked one `A` for every caller
  frame and every gas of the forwarded message (`SendsVia` does not fix the gas); in
  `X_dep_ok_iff_gas` and `X_dep_ok_iff_fails` the condition inside `hans` reads the child's gas
  left, which for `processRunner` depends on the message's gas, so no `A` fit. Since round 30,
  `hans` of `X_dep_ok_iff`, `X_dep_ok_iff_gas` and `X_dep_ok_iff_fails` (the seven paths) asks
  only of a forwarded message `msg` from a caller frame `caller` with `CallFrom g st ss caller msg`:
  `msg.gas` is the gas `g` the CALL gives (`callGas…` of the path), and `caller` has the state
  `st` and substate `ss` of the frame at the CALL (`atCallState`, `atCallSub`). `A` can be a
  condition on `g`, `st` and `ss`. The specifications `spec_dep*_g` and `spec_depD_g` pass
  `CallFrom` to their callee assumption `hcg`; `fwd_ok_iff_fails` takes a call condition `Cl`.
  Round 31: `X_dep_ok_or_fails` takes the same `hans` (below).
  `Sanity/ProcessExact.lean`: from Paris, with the upgraded address holding STOP and no
  precompile, every message the path sends ends under `processRunner` with no error, all its
  gas, the caller's state and accesses, and no output (`process_stop_child`). So `processRunner`
  meets `NoFailOn` and the new `hans` (`hans_process_stop`, `hans_gas_process_stop`,
  `hans_destroy_process_stop`, `hans_destroy_gas_process_stop`), and for the seven forwards:
  `X_dep_ok_iff_process_stop` (with `hg`, `htail`: `RunsOk` iff the checks hold; for
  destroyBlackFunds also an account of `C` in the state at the CALL) and
  `X_dep_ok_iff_gas_process_stop` (with `hg` only: iff the checks hold and the gas left after the
  CALL plus the gas it gives is at least the gas of the code after the CALL; for destroyBlackFunds
  an account of `C` and `max tailCost tailStip`, over the state and accesses at the CALL and the
  empty output).
  Round 31, `Sanity/MirrorExact.lean`: an instance with an upgraded code whose success depends on
  its gas. From Paris, with the upgraded address holding `MIRROR` (Evm/Mirror.lean) and no
  precompile, every `balanceOf(a)` message the path sends gives under `processRunner` a frame,
  never an error, at any gas (`process_mirror_sends`, from `process_mirror_iff` and the generic
  `Gas.no_error_ga` of Evm/NoAbort.lean). That frame ends with no error exactly when the message's
  gas is at least `mirrorCost c = 87 + slotCost c`, `c` the coldness of the queried slot in the
  caller's substate (below it the run halts with an error); then it keeps the rest of its gas.
  So `processRunner` meets `NoFailOn` (`noFailOn_process_mirror`) and the gas-aware `hans`
  (`hans_gas_process_mirror`, `hans_destroy_gas_process_mirror`).
  `balanceOf_dep_ok_iff_gas_process_mirror` (with `hg` only, and `hcM`, the coldness `cM` of the
  queried slot of the upgraded address after slot 10 is accessed): `RunsOk` iff `ForwardOk`, the
  gas the CALL gives is at least `mirrorCost cM`, and the gas left after the CALL plus what is left
  of that gas is at least 126. `destroyBlackFunds_dep_ok_iff_gas_process_mirror` (with `hg` only and
  `hmirror`, the hypothesis of `honestBalanceAt_process_mirror`): `RunsOk` iff `DestroyDepGuard`,
  the gas the CALL gives covers `mirrorCost` (coldness in the substate at the CALL), the state at
  the CALL has an account of `C`, and the gas left after the CALL plus what is left of the gas it
  gives covers `max tailCost tailStip`, over the state at the CALL with the slot recorded read,
  USDT's `balances[a]` in the start state as the subtracted word, and the substate at the CALL with
  the slot accessed. These are two of the seven paths; the other five forwards are not
  instantiated with `MIRROR` (it answers only `balanceOf`).
  `Sanity/MirrorState.lean`: a concrete deprecated state `S1 C H` (slot 10 of `C` with byte 20 = 1
  and upgraded address 0x1234, which holds `MIRROR`; both accounts have the same storage).
  `balanceOf_mirror_sat`: from Paris and before Glamsterdam, every hypothesis of
  `balanceOf_dep_ok_iff_gas_process_mirror` holds there for a `balanceOf(a)` call with 1000000 gas.
  `keepsInvAt_process_mirror`, `process_step_dep_hyps`: `processRunner` meets `KeepsInvAt` with
  `MIRROR`, and in `S1 C H`, for a `destroyBlackFunds(a)` call, the flag, `KeepsInvAt` and
  `HonestBalanceAt` hold together.
- `X_dep_ok_iff_gas` (round 26, the six forwards other than destroyBlackFunds): the hypotheses of
  `X_dep_ok_iff` without `htail`, and `hans` with "ends with no error" replaced by "ends with no
  error, and the gas the CALL keeps plus the gas left in the ended frame is at least the gas of
  the code after the CALL" (121 for totalSupply, 126 balanceOf, 128 allowance, 51 transfer, 53
  approve, 53 transferFrom). Then `RunsOk` holds if and only if the checks and `A` hold. With
  `X_dep_low`, every gas is covered for these six. The specifications behind it
  (`spec_dep_g`, `spec_depB_g`, `spec_depAl_g`, `spec_depT_g`, `spec_depA_g`, `spec_depF_g`) take
  that bound on the callee (`hcg`) in place of `htail`; the old specifications follow from them.
- `X_dep_ok_or_fails` (round 31, the seven paths): the hypotheses of `X_dep_ok_iff_fails` (below)
  without `hfail`, for a runner that may fail with any error: a run that ends with no error gives
  the checks and `A`; the checks and `A` give a run that ends with no error, or a failure of the
  runner on a message the path sends (`SendsVia`). This is not an iff. `X_dep_ok_iff_fails` is
  derived from it (`hfail` rules out the failure). Through round 30 the six forwards other than
  destroyBlackFunds had a weaker form: it took `htail`, a `hans` asked of every gas of the
  forwarded message (unsatisfiable for `processRunner` with a code that can run out of gas,
  docs/AUDIT.md finding 3) and errors that abort, and its failure was on some message, not shown to
  be the forward. The new form implies it: the old `hans` with `htail` gives the new one, as in
  `X_dep_ok_iff`.
- `NoFail` excludes a runner that fails, which makes the run abort (EthLib's `Meets` allows such
  errors). `Sanity/Exact.lean`: every `answerRunner` never fails and ends every message with no
  error, so it meets `hans` with `A = True` for the six forwards other than destroyBlackFunds.
  Round 26: `answerRunnerAt S f` (each message ends at once with no error, gas 0, in the state
  `S`) never fails; with `S = sState C kvs` it meets the `hans` of deprecated destroyBlackFunds
  with `A = True`, for a message whose current target is `C` (`answerRunnerAt_hans`); and each
  ended frame meets the condition of the `hans` of `X_dep_ok_iff_gas` exactly when `T ≤ R`, for `T`
  the tail gas and `R` the gas the CALL keeps (`answerRunnerAt_ans_gas`, stated per frame).
- `destroyBlackFunds_dep_ok_iff_gas` (round 26, second part): the hypotheses of
  `destroyBlackFunds_dep_ok_iff` without `htail`, and `hans` with its condition replaced by "ends
  with no error, the contract has an account in the ended frame's state, and the gas the CALL
  keeps plus the gas left in the ended frame is at least the larger of `tailCost` and `tailStip`".
  Both are computed over the state and substate after the call (`incorporateChild` of the caller's
  frame and the ended frame): `tailCost` is the gas of the code after the CALL (the two writes at
  their prices, from the coldness and the original and current words of `balances[a]` and slot 1
  there); `tailStip = 2518 + (price of the write of balances[a]) + (price of the read of slot 1)`
  is the gas below which (from `tailCost` up) an `SSTORE` of the tail is reached with at most 2300
  gas left (`tailMidD`: the first one when the gas is below 2485, else that of `_totalSupply`). Then `RunsOk` holds if and only
  if `DestroyDepGuard` and `A` hold; with `destroyBlackFunds_dep_low` every gas is covered. Behind
  it: `tailD_g`, `tailMidD`, `spec_depD_g` (only the forwarded messages that end with no error),
  and `dep_destroy_complete`, which now also gives the stipend bound.
- `X_dep_ok_iff_fails` (round 26, second part, the seven paths): the hypotheses of
  `X_dep_ok_iff_gas` with `NoFail` replaced by `hfail`: a failure of the runner (with any error,
  aborting or not) on a message that is the forward along the route excludes `A`. Then `RunsOk`
  holds if and only if the checks and `A` hold. So a runner may fail, on the forward or on any
  other message, and a failure on the forward is an outcome in which `A` is false. The
  `X_dep_ok_iff_gas` theorems are derived from these (`NoFail` gives `hfail`). Behind it: the
  forward specifications `spec_dep*_g` and `spec_depD_g` are stated as `Sends.SpecOn` (Evm/Sends.lean):
  under every runner whose ended messages meet the callee assumption, with no assumption on its
  errors, the run ends in the postcondition or at a failure of the runner on a message that is the
  forward (`SendsVia`); EthLib's `SpecUnder` follows from it (`toUnder`). `Sanity.failRunner_hans`,
  `Sanity.failRunner_hfail`: the runner that fails on every message meets both with `A = False`.
- Since round 30, `hans` is asked only of the caller frame at the CALL (`CallFrom`). Through the
  first part of round 31, `NoFailOn`, `hfail` and the failure in the conclusion of
  `X_dep_ok_or_fails` still ranged over every caller frame (docs/AUDIT.md, second audit, M1): for
  a code that reads another account's code, `processRunner` fails with a state error from a caller
  state where that code is missing (argued). Since round 31 they too are asked only of the message
  the CALL sends from the caller frame at the CALL, with its gas (`CallFrom`): `NoFailOn` takes a
  condition on the caller frame and the message, `hfail` takes `CallFrom`, and the failure in
  `X_dep_ok_or_fails` comes with `CallFrom`. Behind them, `Sends.AbortsOn` / `HoareOn` / `SpecOn`
  name the failing message by a condition on the caller frame and the message, and `callWithRS`
  gives the caller's state and substate and the message's gas in it.
- Round 33 (docs/AUDIT.md, third audit, T2): `SendsVia` also fixes the block and transaction
  environments of the forwarded message to those of `message`, and says that it transfers value,
  as EthLib's CALL builds it. Through round 32, `hans`, `NoFailOn`, `hfail`, `KeepsInvAt`,
  `HonestBalanceAt` and the `KeepsAt` forms were asked of the forwarded message under every
  block and transaction environment. For an upgraded code whose success reads the timestamp, no
  `A` met `hans` under `processRunner` (argued). `SentVia` still leaves the call data and the gas
  free.

## What is trusted

- The Lean 4 kernel (v4.35.0).
- The three standard axioms that `#print axioms` reports for every main theorem: `propext`,
  `Classical.choice` and `Quot.sound`. There is no `sorry`, no new axiom, and no `native_decide`
  or `bv_decide`. `decide +kernel` is used, and it is checked by the kernel.
- EthLib's EVM model is a faithful EVM. The proofs are only as good as that model.
- The bytecode file is the deployed code. The interpreted hash check ties `CODE` to the file,
  and `data/SOURCE.md` ties the file to the chain.
- A few generic rules are proved locally in this repository, and EthLib's model is not
  modified. These rules are some instruction table entries, EXTCODESIZE at every fork from
  Berlin (`Local.extcodesize`; EthLib's rule stops before Glamsterdam), and that every message
  keeps the block of the state (`UsdtVerify/Evm/Local/`), and EXP with its price worked out
  (`Gas.expLG`, `UsdtVerify/Evm/GasRules.lean`). STOP and GAS come from EthLib. The CALL step lemmas at every fork
  (`callStep_child_r`, `callWithRS`, `callWithR`, `callStep_low_r`, `callStep_deep_r`, `callStep_missing`) are
  computed from EthLib's `callStep`. They are proved from EthLib's semantics, not assumed.

## What is not covered

- name/symbol on slot words outside `StrForm`.
- The invariant over deprecated calls without the runner assumptions `KeepsInvAt` and
  `HonestBalanceAt` (destroyBlackFunds can break it, see above). `KeepsInvAt` is shown for
  `processRunner` with the upgraded code STOP (round 29); `HonestBalanceAt` with the upgraded code
  `MIRROR` under `hmirror` (round 30). Round 31: `Sanity.process_step_dep_hyps` gives one concrete
  deprecated state with `MIRROR` where `processRunner` meets both. In that state no
  destroyBlackFunds call reaches the CALL (the owner is 0 and nobody is blacklisted). Round 33:
  `Sanity.process_step_dep_hyps2` gives a second state `S2`, where the caller is the owner, `a` is
  blacklisted and `balances[a]` is not 0, and `processRunner` meets both there.
  `Sanity.destroy_mirror_runs` (Paris to before Glamsterdam, 1000000 gas): the deprecated
  destroyBlackFunds call there ends with no error, through the CALL. `Inv` in `S2` is not proved.
- The keccak hypotheses `SepOn` and `SecSep` of a call's keys (finitely many separation facts about
  given slots; not proved, and not shown for any particular call).
- The security properties for deprecated calls of the six forwarding functions (and, for the
  allowance and supply properties, of destroyBlackFunds) without the runner assumptions `KeepsSlots`, `KeepsBal`, `KeepsListed`,
  `KeepsAllow`, `KeepsSupply` (round 23). `processRunner` with the upgraded code STOP meets them
  (round 29); no other real upgraded contract is shown to.
- A deprecated run in the non-vacuity witnesses of round 24: no witness run is deprecated.
- A theorem that neither `KeepsInv` nor `KeepsInvAcc` implies the other (it holds by the
  definitions; it is not stated).
- Runs that run out of gas below the stated bounds, except at the dispatcher (see above), every
  gas for the exact conditions not deprecated (rounds 25 and 26, `X_low`, `X_mid`, `X_iff_gas`),
  and every gas for the seven deprecated forwards (`X_dep_low`, `X_dep_ok_iff_gas`,
  `X_dep_ok_iff_fails`), under the runner hypotheses `hans` and `NoFailOn` or `hfail`.
- Forks before Berlin. Glamsterdam rests on EthLib's model of that fork at the pin (its prices
  and the order of its checks).
- Runs under EthLib's EIP-8037 meter `StateGasMeter`, which EthLib's `processTransaction` uses
  from Glamsterdam, beyond the results of rounds 34 to 36 below: the deprecated paths (their
  CALL); the split of the gas between the execution gas left and the reservoir at a reservoir
  other than 0; the gas of a run with a refill (only a lower bound, `Shadow.gas_ge_any`); the
  security properties. See docs/STATUS.md (rounds 33 to 36).

## The EIP-8037 meter (round 34; UsdtVerify/Evm/Meter.lean, UsdtVerify/Usdt/Meter.lean)

- `Gas.Ends fork l s`: `s` is a stopped frame that `l` reaches along EthLib's `Step`, or the steps
  from `l` reach a running frame that is not `SimAt` (an opcode outside the list `simulated`, which
  holds the opcodes of the rules here; CALL is not in it). `Ends.run`: every end of `runFrame`, for
  any gas bound and message runner, meets it. Since round 34 the completeness theorems not
  deprecated (`ok_X`, `ends_ok_dispatch`), the per-function `inv_X` and `inv_call` take
  `hrun : Ends fork evm s` in place of a `runFrame` equation. A `runFrame` end gives it through
  `Ends.run`, and `runFrame_ok_dispatch` keeps its `runFrame` form.
- `Meter.step_sim`: from a frame of `StateGasMeter` with reservoir 0, `SimAt`, and where an SSTORE
  refills no state gas (`NoRefillAt`), one step gives the same error as the step of the meter
  `Nat` from its `toNat` (the same fields, the execution gas left as gas), or the next frame and
  its `toNat`, with reservoir 0 or stopped.
- `Meter.ends_of_sgm`: a run of `runFrame` over `StateGasMeter`, for any gas bound and message
  runner, from a frame with reservoir 0 where no SSTORE that the steps reach refills, gives
  `Ends` from `toNat` of its start to `toNat` of its end.
- `Meter.allocateGas_reservoir`: a transaction with a gas limit of at most 2^24 gives its first
  frame a reservoir of 0 (EthLib's `allocateGas`), at every fork.
- `Complete.inv_call_sgm`: `inv_call` for such a run over `StateGasMeter`. `ok_transfer_sgm`,
  `ok_approve_sgm`, `ok_transferFrom_sgm`: the conclusions of `ok_transfer`, `ok_approve`,
  `ok_transferFrom` for such a run, with the execution gas left `s.gas.gasLeft` in place of the
  gas. Every other `ok_X` applies the same way, through `ends_of_sgm`, to `toNat s`.
- Hypotheses of these, beyond those of the `Nat` theorem: the reservoir of the start frame is 0
  (`hres`), and no SSTORE that the steps reach refills state gas (`hnr`, over every frame that the
  start reaches along `Step`). Neither is derived from the call: `hnr` is not proved for any
  path, and `hres` holds for the first frame of a transaction of at most 2^24 gas.
- Not covered by round 34: the deprecated paths, a reservoir other than 0, runs with a refill, and
  the direction of `X_ok_iff` and `X_iff_gas` that says enough gas gives success.

## The EIP-8037 meter, round 35 (UsdtVerify/Evm/Refill.lean, Evm/Shadow.lean, Usdt/Refill/, Usdt/MeterIff.lean)

- When an SSTORE refills: from Glamsterdam, when it writes 0 over a word that is not 0, in a slot
  that was 0 at the start of the transaction (EthLib's `sstoreStateRefill`).
- `Refill.noRefill_cheap`, `Refill.noRefill_one`: over the meter `Nat`, no frame of a `StepG` chain
  refills, when the two ends of the chain have the same storage (or differ at one word, which does
  not go from not 0 to 0 while it was 0 before the transaction), the end has no error, and the
  chain pays less than 97,920 gas (twice that if the word is created). `HoareG.toIA`,
  `HoareG.toIW`, `sstoreWI` lift triples over `StepG` to `StepI` (steps from frames that refill
  nothing) under these conditions.
- `Refill.ends_of_sgmN`: `ends_of_sgm` with `hnr` stated for the run of the meter `Nat` from
  `toNat m`. `Refill.noRefill_low`: a `StepI` chain from `sh k lo` to a stopped frame gives that
  hypothesis for the run from `lo`. `Refill.sgm_of_reaches`: a `StepG` chain from `toNat m` to a
  stopped frame `z`, from reservoir 0 with no refill on the run, gives a run over `StateGasMeter`
  from `m`, for any gas bound and message runner, that ends in a frame whose `toNat` is `z`.
- `Shadow.shadow_run`: a run over `StateGasMeter` from `m`, for any gas bound and message runner,
  that ends with no error is followed, in every field but the gas, by the run of the meter `Nat`
  from a frame with the fields of `m` and at least `budget m` gas (gas left, reservoir, and 97,920
  for each unit of the measure): `Ends` holds to a frame with the fields of the end. Any reservoir;
  SSTORE may refill.
- `Exact.ok_approve_any`, `ok_transfer_any`, `ok_transferFrom_any`: a run of approve, transfer or
  transferFrom over `StateGasMeter`, any reservoir, that ends with no error meets the guard
  (`ApproveGuard`, `TransferGuard`, `TransferFromGuard`), with an empty output and the state and
  substate of the Nat path. Hypotheses: Berlin ≤ fork, size < 2^256, the selector, not
  deprecated, `toNat m` the fresh frame of `CODE`.
- `Exact.approve_iff_gas_sgm`: from reservoir 0, when the write of the allowance refills nothing
  (`hnr`), the run over `StateGasMeter` ends with no error if and only if `ApproveGuard` holds and
  the gas is at least `max approveCost approveStip`. `approve_ok_sgm`: then the execution gas left
  is `gas - approveCost`. The write refills exactly when `v = 0`, the allowance slot was 0 at the
  start of the transaction, and it is not 0 at the call.
- `Exact.transfer_iff_gas_sgm`, `transfer_ok_sgm`: the same for transfer with a fee of 0 (`hfee`),
  when the write of the sender's balance refills nothing (`hnrD`; it refills exactly when that slot
  was 0 at the start of the transaction, is not 0 at the call, and `v` is the whole balance). The
  write of the recipient's balance adds without overflow, so it never refills.
- Not covered by round 35 (round 36 below covers the first, third and fourth): transfer with a fee
  above 0 and transferFrom in the exact form, the gas of a run with a reservoir other than 0 or
  with a refill, the deprecated paths, `process_step` and `goodCall_process` over
  `StateGasMeter`.

## The EIP-8037 meter, round 36 (Usdt/Refill/, Usdt/MeterIff.lean, Usdt/MeterOwner.lean, Usdt/MeterGas.lean, Usdt/Invariant/SeqMeter.lean, Evm/Refill.lean, Evm/Shadow.lean, Evm/ProcessMeter.lean)

From a frame `m` whose `toNat` is the fresh frame of `CODE` with `gas` execution gas, for any gas
bound and message runner, not deprecated, from Berlin:

- Exact success condition, reservoir 0. For the 13 writing functions (transfer with any fee,
  transferFrom on all paths, approve, and the ten owner functions), `X_iff_gas_sgm`: the run over
  `StateGasMeter` ends with no error if and only if the guard of `Usdt/Spec/Guards.lean` holds and
  the gas is at least the bound of `X_iff_gas`. `X_ok_sgm`: then the execution gas left is
  `gas - cost`. Refill hypotheses, each on the start state, one per write that can refill:
  approve `hnr`; transfer `hnrD`; transferFrom `hnrA` (only when the allowance is not
  `MAX_UINT`) and `hnrD`; unpause `hnr`; removeBlackList `hnr`; issue `hnrT`; redeem `hnrT`,
  `hnrO`; setParams `hnr3`, `hnr4`; destroyBlackFunds `hnrB`, `hnrT`; none for pause,
  addBlackList, deprecate, transferOwnership. A write of a word that is not 0 never refills
  (`refill_of_ne`), nor does an addition with no overflow (`refill_add`).
- The gas at any reservoir. `X_gas_any` (Usdt/MeterGas.lean), same 13 functions, same
  hypotheses: a run over `StateGasMeter` that ends with no error has
  `s.gas.gasLeft + s.gas.reservoir + cost = gas + m.gas.reservoir`. `Shadow.gas_ge_any`: for a path
  given as a triple over `StepG`, with no refill hypothesis, `gas + reservoir ≤ s.gas.gasLeft +
  s.gas.reservoir + cost`.
- The invariant over `StateGasMeter`, any reservoir, refills allowed, no bound on the gas of the
  transaction. `inv_call_any`; `GoodCallS`, `CallsS` (steps over `Nat`, steps over
  `StateGasMeter`, `Untouched` steps), `inv_callsS`; `goodCall_processS`, `process_value_failsS`,
  `process_stepS`: from Paris, every top-level message to `C` with code `CODE`, no precompile,
  not deprecated, that EthLib's `processMessage` over `StateGasMeter` ends (round 41: from any
  starting meter), is a `GoodCallS` or an `Untouched` step. These carry the keccak hypothesis `SepOn (callKeys message S)` and `StrForm`
  of slots 7 and 8, as `goodCall_process`.
- Generic: `Refill.HoareG.toIW'`, `HoareG.toI1`, `SpecG.toIW'`, `SpecG.toIS` (lifts of a stretch
  or a whole path that changes one word); `Shadow.runsOk_of_specI` (a run over `StateGasMeter`
  with no error gives a run of the meter `Nat` with no error from `toNat m`, any runner);
  `Shadow.shadow_runQ`, `gas_ge_any`, `gas_eq_any`; `ProcessMeter.processMessage_map_valM` and
  `processMessage_map_val_valueM` (EthLib's lemmas over any lawful meter).

