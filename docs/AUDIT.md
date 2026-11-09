# Adversarial audit of the headline theorems (USDT-28)

Scope: the public README (`README.md`), `docs/RESULTS.md`, `docs/STATUS.md`,
`docs/LAYOUT.md`, `UsdtVerify/Summary.lean`, and the statements of `inv_call`, `inv_call_all`,
`inv_calls`, `goodCall_process`, `process_step`, the `*_complete`, `X_ok_iff`, `X_iff_gas`,
`X_dep_ok_iff`, `X_dep_ok_iff_fails`, the five Security `*_call_all` / `*_seq_all`, and the
Sanity witnesses. The question asked: can a headline theorem be weaker than the docs make it
sound? Nothing in the theorem statements was changed. Findings are ranked by severity.

Checked against EthLib at commit `fd3457dbf` (an ancestor of upstream
`origin/master`). Every Lean command ran under a 9 GB memory cap.

## Summary

| # | Severity | Finding |
|---|---|---|
| 1 | Critical | `KeccakSep` and `AllowSep` are almost certainly false for the real keccak, so every theorem that assumes them is, as far as anyone can tell, vacuous |
| 2 | High | `KeepsInv` and the `Keeps*` assumptions are false for EthLib's real runner `processRunner`. So the deprecated case of `goodCall_process` / `process_step` is vacuous. Machine-checked for `ua = C` |
| 3 | High | The deprecated exact theorems (`X_dep_ok_iff`, `X_dep_ok_iff_gas`, `X_dep_ok_iff_fails`) cannot be instantiated with `processRunner` and any real upgraded code |
| 4 | Medium | The README describes `stopRunner` as "a runner whose upgraded contract only runs STOP". It is not: it fails every message whose code is not STOP |
| 5 | Medium | The sequence results cover top-level messages to USDT only. Calls that reach USDT through other contracts, and rollbacks of outer frames, are not shown to fit `Calls` |
| 6 | Resolved | The published repository pins EthLib by git commit |
| 7 | Low | `exists_breaks` and `depD_breaks` assume `KeccakSep`. The README presents `exists_breaks` as an unconditional concrete counterexample |
| 8 | Low | The README says the code was read "at block 26362952". `data/SOURCE.md` says it was read at tag `latest`, just after `eth_blockNumber` returned 26362952 |
| 9 | Info | Checked and found sound: the bytecode is the mainnet code, there is a single `CODE` constant, `Inv` does not wrap, the trusted base is as stated, and the slot layout is consistent |

## 1. `KeccakSep` / `AllowSep` are almost certainly false (Critical)

**Statement** (`Usdt/Invariant/Supply.lean:39`, `Usdt/Security/Effect.lean:75`). `mapSlot k b`
is the concrete `Evm.keccak (wordBytes k ++ wordBytes b)` (`Evm/Storage.lean:54`), so
`KeccakSep` is a closed proposition about one fixed function. It is either true or false, and
nothing is varied. Its fields quantify over all 2^256 key words, except `inj`, which quantifies
over the 2^160 address words. The counts below treat keccak, restricted to these inputs, as a
random function. That is the standard heuristic, and no better model is known.

- `fixed : ∀ x : U256, ∀ n < 11, mapSlot x 2 ≠ n`. There are 2^256 inputs and 11 target values.
  The expected number of hits is 11, so the field is true with probability about e^-11, roughly
  2·10^-5.
- `list : ∀ x y : U256, mapSlot x 2 ≠ mapSlot y 6`. This needs two images of 2^256 inputs each
  in a space of 2^256 to be disjoint. The expected number of collisions is about 2^256. The
  field is false.
- `allow : ∀ x y z, mapSlot x 2 ≠ mapSlot y (mapSlot z 5)` and
  `one_allow : ∀ y z, mapSlot y (mapSlot z 5) ≠ 1`. These have 2^512 inputs, with the same
  conclusion. The fields are false.
- `inj` (address words only). There are about 2^319 pairs, and each collides with probability
  2^-256. That is about 2^63 expected collisions among the 2^160 balance slots: the birthday
  bound is 2^128. The field is false.
- `AllowSep.fixed` and `AllowSep.list` are false in the same way.

So `KeccakSep → P` and `AllowSep → P` are, with overwhelming likelihood, true only because
their premises are false. This cannot be shown in Lean, because that would need explicit keccak
collisions. But nothing supports the README's framing, "since the slots are keccak outputs, this
is a claim about the hash function", as if the claim were plausible. The real safety argument
is computational: nobody can find such a collision. It is not that none exists.

**Affected statements.** Every invariant theorem (`inv_call`, `inv_call_ns`, `inv_call_all`,
`inv_calls`, `steps_inv`, `destroy_inv`, `inv_tail_iff`, `depD_inv`), the counterexamples
`exists_breaks` and `depD_breaks` (finding 7), and every Security theorem that takes `K` or `A`
(`nonOwner_call(_all)`, `nonOwner_local`, `paused_call(_all)`, `listed_call(_all)`,
`allowKept_call(_all)`, `supply_call(_all)`, `transferFrom_bound`, and the `_seq` / `_seq_all`
forms). The Sanity `*_applies` theorems take `KeccakSep` as a hypothesis, so they do not reduce
this risk. The README says so for the keccak hypotheses.

Not affected: specs, completeness, `dispatch_complete`, `owner_only`, `transfer_checks_all`,
`transferFrom_checks_all`, the `Exact` theorems, local conservation (whose distinctness
hypotheses are about the concrete slots of one run), `effect_call` / `effect_all`.

**Suggested fix (statements, not done here).** Replace the global separation by finitely many
facts about the slots a run actually touches. Each such fact fails only with probability about
2^-96, and a counterexample would amount to finding a keccak preimage or collision. Two options:

- Make the hypothesis per call. For each slot `w` the path writes: if it is a balance write,
  `w` is the balance slot of exactly one address word (`∀ x < 2^160, mapSlot x 2 = w → x = a`).
  Otherwise, `w` is the balance slot of no address word. Also add the few pairwise inequalities
  between the touched slots. This is what the proofs use. `Inv` over 2^160 addresses needs only
  that each written slot moves one term of the sum.
- Or define `Inv` as a sum over the set of distinct balance slots, the image of the address
  words. This drops `inj` altogether. Then require only "a non-balance write is not a balance
  slot" for the slots written.

In the docs, state plainly that `KeccakSep` and `AllowSep` as written are almost certainly false
(done in `docs/RESULTS.md`, see below).

**Resolution (round 29).** Restated locally. Every theorem that took `KeccakSep` (and `AllowSep`)
now takes `SepOn (callKeys message state)` (or `SecSep (callKeys message state)`): separation facts
about the slots keyed by the four address words of that one call (caller, first two address
arguments, owner) and about the fixed slots 0..10, each comparing one given slot with the 2^160
balance (or `isBlackListed`) slots. Sequences carry it per call (`GoodCall`, the security
predicates `Q`). The allowance conclusions are now per slot (`AllowKeptAt y z`, with `y`, `z`
added to the keys), and `Protected` names the `isBlackListed` slots of address words only.
`KeccakSep` with `AllowSep` implies the new hypothesis for every list (`sepOn_of_global`). See
docs/STATUS.md, round 29, and docs/RESULTS.md (the invariant).

## 2. `KeepsInv` / `Keeps*` are false for `processRunner` (High)

**Statement** (`Usdt/Invariant/All.lean:74`, `Evm/Keeps.lean:35`).
`KeepsInv runChild C ua := ∀ caller msg lt child, runChild caller msg lt = .ok child →
msg.caller = C → msg.currentTarget = ua → child.1.error = none → Inv C caller.state →
Inv C child.1.state`. It quantifies over every caller frame and every message from `C` to `ua`,
including `msg.code`, `msg.codeAddress`, the gas, and the codes of all accounts in
`caller.state`. `processRunner` runs `msg.code` (`startFrame message`). A message with
currentTarget `ua` and code that writes to `C`'s storage, or that CALLs `C` in a caller state
where `C`'s code writes slot 1, breaks `Inv C`. No property of the real upgraded contract can
prevent that.

**Machine-checked (scratch, not committed).** For `ua = C`, with `EVIL = PUSH1 1 PUSH1 1 SSTORE
STOP`, `sState C []` (all storage 0, so `Inv` holds), and `codeAddress := none`:

```lean
theorem not_keepsInv_process (K : KeccakSep) (b : BlockEnvironment .dencun)
    (t : TransactionEnvironment .dencun) (C : Address) (ss : Substate) :
    ¬ KeepsInv (processRunner .dencun 100000) C C
-- 'UsdtVerify.AuditScratch.not_keepsInv_process' depends on axioms:
--   [propext, Classical.choice, Quot.sound]
```

The run is built from EthLib's `push1`, `sstore_of_account`, `stop` and
`processMessage_of_spec`. After it, slot 1 is 1 and every balance slot is still 0, by
`KeccakSep.fixed`. The file was checked with exit 0, and the proof needs about 90 lines.
For `ua ≠ C` the same counterexample works with one nested CALL (the message code calls `C`,
whose code in `caller.state` is `EVIL`). That case was argued, not machine-checked. `KeepsSlots`
and `KeepsSupply` (slot 1 is `Protected`), `KeepsBal`, `KeepsListed` and `KeepsAllow` fail the
same way. `HonestBalance` (`All.lean:103`) also quantifies over every caller frame and
`msg.code`, and fails for `processRunner` with any message code that returns a wrong word.

**Consequences.**
- `goodCall_process` and `process_step` instantiate `hkeeps` with
  `processRunner fork message.gas`. In a deprecated state that hypothesis cannot be met (proved
  above for `upAddr = C`, argued for every `upAddr`). So "every top-level message to USDT is a
  `GoodCall` or `Untouched`" is shown only for states that are not deprecated. Mainnet is not
  deprecated today (slot 10 reads 0), so the practical sequence result stands. The deprecated
  half does not.
- `inv_call_all` and the Security `*_call_all` / `*_seq_all` are stated for an arbitrary runner.
  With the real runner, their deprecated branch has an unsatisfiable premise. Sanity meets these
  assumptions only with `stopRunner`, which is not `processRunner` (finding 4), and with
  `balRunner`, which is not the run of any code.

**Suggested fix (statements).** Make the callee assumption per call. Quantify only over the
frame and message the run actually reaches. For example, take
`SendsVia message ua c r d msg`, with `msg.code = routeCode c r`, and the caller state equal to
the state at the CALL (the path's proofs already compute it). Then it is a property of the real
upgraded code `c` in the real state, and it can be discharged for a concrete contract. At
minimum, constrain `msg` by `SendsVia`, which fixes the code.

**Doc fix (done).** `docs/RESULTS.md` now says that these assumptions are false for
`processRunner` itself.

**Resolution (round 29).** Restated over the calls the code makes. `KeepsInvAt`, `HonestBalanceAt`
and the security `Keeps*` (now `KeepsAt … (upAddr S message) R`) quantify only over caller frames
whose state has the storage and code of the start state (`SameView`) and messages that run the
code the upgraded address holds there (`SentVia`, built on `SendsVia`); gas and data stay free.
Every theorem, `goodCall_process` and `process_step` included, takes these forms; the old forms
imply them. `Sanity.processRunner_stop_keepsAll` proves that `processRunner`, from Paris, meets
all six when the upgraded address holds STOP and is no precompile, so the deprecated branch of
`process_step` is no longer vacuous for the real runner. Not done: `HonestBalanceAt` for
`processRunner` with a real code.

**Resolution (round 30).** `Sanity.honestBalanceAt_process_mirror`: from Paris, `processRunner`
meets `HonestBalanceAt` when the upgraded address holds `MIRROR` (Evm/Mirror.lean, 25 bytes that
answer `balanceOf(a)` with slot `keccak(a ++ 2)` of their own storage), is no precompile, and
that slot holds in the start state the word of USDT's `balances[a]` (`hmirror`, a hypothesis on
the state for the one queried slot). Every gas is covered (`process_mirror`, from the exact
`mirror_spec` and `Complete.ok_exact`). Not shown: one state where a useful upgraded code meets
both `KeepsInvAt` and `HonestBalanceAt` for `process_step`.

## 3. Deprecated exact theorems: `NoFail` and `hans` vs `processRunner` (High)

- `NoFail runChild := ∀ caller msg lt e, runChild caller msg lt ≠ .error e`
  (`Evm/Iff.lean:169`). `processMessage` returns `.error (.state _)` when `moveEther` fails, for
  a message whose value exceeds the caller's balance (`MessageCall.lean:301-304`). The proof of
  `process_value_fails` uses exactly this branch. So `NoFail (processRunner …)` is false, and
  every `X_dep_ok_iff` that takes `hnf` cannot be applied to the real runner.
- `hans` in `X_dep_ok_iff_gas` and `X_dep_ok_iff_fails` (for example `Exact/Deprecated.lean:446`)
  is `∀ caller msg lt child, runChild … = .ok child → SendsVia … msg → (child ok ∧ gas … ↔ A)`
  for one fixed proposition `A`. `SendsVia` (`Evm/Route.lean:134`) fixes the code, data, value
  and depth, but not `msg.gas` and not the caller frame. Under `processRunner`, take an upgraded
  code `c` that can both succeed and run out of gas, which is every real contract. With
  `msg.gas = 0` the child fails, so `A` must be false. With enough gas it succeeds, so `A` must
  be true. So `hans` is unsatisfiable, and the "exact success condition" says nothing about a
  real deployment. Only gas-insensitive mock runners (`answerRunner`, `answerRunnerAt`,
  `failRunner`) meet it. This was argued, not machine-checked.

**Suggested fix.** Let the answer depend on the call: `A : Evm fork Nat → Message fork → … →
Prop`, with the conclusion "the checks hold, and `A` holds of the frame and message at the
CALL". Or state `hans` only for the caller frame the path reaches at the CALL, with `msg.gas`
the EIP-150 gas the theorem already computes (`callGasT …`).

**Resolution (round 29), partial.** `NoFail` is replaced by `NoFailOn` the messages the path sends
(`SendsVia`, no value) in the six `X_dep_ok_iff`, the six `X_dep_ok_iff_gas` and
`destroyBlackFunds_dep_ok_iff_gas` (`destroyBlackFunds_dep_ok_iff` keeps `NoFail`).
`Sanity.totalSupply_dep_ok_iff_process_stop` instantiates `totalSupply_dep_ok_iff` with
`processRunner` and the upgraded code STOP (from Paris, no precompile): the run succeeds iff
`ForwardOk`. Not resolved: the `hans` of `X_dep_ok_iff_gas` and `X_dep_ok_iff_fails` still asks
one `A` for every gas of the forwarded message, so it is unsatisfiable for `processRunner`; a fix
needs the CALL step and the forwarding specifications to pass `msg.gas` to the callee assumption.

**Resolution (round 30).** `hans` of the seven `X_dep_ok_iff`, `X_dep_ok_iff_gas` and
`X_dep_ok_iff_fails` takes `CallFrom g st ss caller msg` (Evm/Route.lean): it is asked only of the
message the CALL sends, with the gas `g` the CALL gives, from a caller frame with the state and
substate at the CALL, so `A` may depend on that gas. `spec_dep*_g` / `spec_depD_g` pass `CallFrom`
to `hcg` (`callWithRS` already gave the facts). `destroyBlackFunds_dep_ok_iff` takes `NoFailOn`.
Sanity/ProcessExact.lean: from Paris, with the upgraded code STOP and no precompile,
`processRunner` meets `NoFailOn` and the new `hans` for the seven forwards;
`X_dep_ok_iff_process_stop` and `X_dep_ok_iff_gas_process_stop` instantiate both forms (the
gas-exact condition: the gas left after the CALL plus the gas it gives covers the code after it).
Not done: an instance with an upgraded code whose success depends on its gas; the
`X_dep_ok_or_fails` theorems keep the old `hans`.

**Resolution (round 31), the instance.** Sanity/MirrorExact.lean, from Paris, with the upgraded
address holding `MIRROR` (whose success depends on its gas) and no precompile:
`process_mirror_sends` shows that `processRunner` returns a frame, never an error, for every
`balanceOf(a)` message the path sends, at any gas (Evm/NoAbort.lean: `no_error_ga`, from
`mirror_specA` over steps whose failures with less gas only halt the frame), and that the frame
ends with no error exactly when the message's gas covers `87 + slotCost c`. So `processRunner`
meets `NoFailOn` and the gas-aware `hans` for this code, and
`balanceOf_dep_ok_iff_gas_process_mirror` and `destroyBlackFunds_dep_ok_iff_gas_process_mirror`
(the latter under `hmirror`, the hypothesis of `honestBalanceAt_process_mirror`) are the
instances: the run succeeds iff the checks hold, the gas the CALL gives covers `MIRROR`'s cost,
and the gas left after the CALL plus what `MIRROR` returns covers the code after it. Only these
two of the seven paths are instantiated with `MIRROR`.

**Resolution note (round 48).** `NoAbort`, `NoAbortLow` and the no-abort facts of the instructions
are EthLib's since #1616 (Execution/Proofs/Evm/Logic/NoAbort.lean), with the same bodies.
`no_error_of_reaches` is EthLib's, applied to the local `StepGA` (EthLib's `StepGA` with `SimAt`),
and `no_error_ga` and `process_mirror_sends` keep their statements.

**Resolution (round 31), `X_dep_ok_or_fails`.** Moved to the gas-aware `hans`: the seven
`X_dep_ok_or_fails` (destroyBlackFunds added) take the hypotheses of `X_dep_ok_iff_fails` without
`hfail` (no `htail`, no requirement that the runner's errors abort), and the failure in their
conclusion is on a message the path sends (`SendsVia`). `X_dep_ok_iff_fails` is now derived from
them. The old form follows from the new one (argued, not kept as a theorem: the old `hans` with
`htail` gives the new `hans`, as the proof of `X_dep_ok_iff` does, and a failure on a `SendsVia`
message is a failure on some message).

## 4. `stopRunner` is not "a runner whose upgraded contract only runs STOP" (Medium)

`stopRunner fork bound ua` (`Evm/Runners.lean:57`) is `processRunner` on messages to `ua` whose
code is STOP, and `.error .outOfGas` on every other message to `ua`. It filters on `msg.code`, so
it is not the interpreter's runner, whatever code `ua` holds. Combined with finding 2: if `ua`
holds STOP, `processRunner` still fails `KeepsInv`. `docs/RESULTS.md` already says "nothing is
claimed of `processRunner` itself". The README sentence in "What is not covered yet" does not.
Doc fix: see the README section below.

## 5. Scope of the sequence results (Medium)

`Calls C` (`Invariant/Seq.lean:71`) is a linear chain of `GoodCall` and `Untouched` steps.
`process_step` classifies only top-level `processMessage` runs whose code is `CODE`, that is,
transactions sent straight to USDT. Two things are not shown to fit `Calls`: a transaction to
another contract that calls USDT (most USDT traffic, through routers and wallets), and the
rollback of an outer frame after an inner successful USDT call, which restores `C`'s storage
and so is not an `Untouched` step. The theorems claim neither. But the README's "Any finite
sequence of these steps keeps the invariant", next to "every top-level message to USDT … is one
of the two kinds of step", invites the chain-level reading. Suggested fix: say explicitly that
history-level coverage is limited to top-level messages to USDT. Possible statement-level work:
an `Untouched`-or-rollback step, or a nested-call lemma.

## 6. EthLib dependency (resolved in the published repository)

The working copy took EthLib from a local checkout at commit `fd3457dbf`, which is on upstream
master. The published repository pins the same commit as a git dependency in `lakefile.lean`
(`require EthLib from git "https://github.com/ethereum/EthLib" @ "fd3457dbf…"`), so a fresh
clone fetches it.

## 7. `exists_breaks` assumes `KeccakSep` (Low)

`exists_breaks (K : KeccakSep) (C : Address) : ∃ S a d, …`
(`Invariant/DeprecatedDestroy.lean:113`). By finding 1, this "concrete counterexample" is itself
conditional on a hypothesis that is almost certainly false. It could be made unconditional with
a much weaker fact, for example "slot 1 is not the balance slot of exactly one address word".
`docs/RESULTS.md` says "assuming `KeccakSep`". The README did not; fixed there.

**Resolution (round 29).** `exists_breaks` now assumes only `NotBal 1` (slot 1 is the balance slot of
no address word), one given slot against 2^160. It cannot be made unconditional: if slot 1 were
the balance slot of exactly one address word, `Inv` would force every other balance to 0 and every
`tailState` would keep `Inv` (argued, not machine-checked). `depD_breaks` takes `SepOn` of its
call's keys.

## 8. Fetch block wording (Low)

`data/SOURCE.md`: fetched with `eth_getCode` at tag `latest`, and `eth_blockNumber` just before
returned 26362952. The README said "at block 26362952". This is harmless, because the code
cannot change (no SELFDESTRUCT or DELEGATECALL path in `CODE`). Reworded in the README.

## 9. Checked and found sound (Info)

- **Bytecode.** `UsdtVerify/Test/Hash.lean` compares `hexOf CODE.toList` to
  `data/usdt.runtime.hex`, checks the size 11075, and checks EthLib's keccak against
  `b44fb4e9…ea55`. A failure throws in `#eval`, which fails the build. Independent re-check
  during this audit: `eth_getCode` at `latest` (publicnode) returned 11075 bytes, identical to
  the file, and `eth_getProof` returned `codeHash = 0xb44fb4e949d0f78f87f79ee46428f23a2a5713ce6fc6e0beb3dda78c2ac1ea55`,
  the state trie's code hash. There is one `CODE` (`@[irreducible] def CODE := ofNat CODE_NAT
  CODE_SIZE`), the test checks exactly that constant, and every spec uses `At CODE …`.
- **Trusted base.** No `sorry`, `axiom`, `native_decide`, `bv_decide`, `implemented_by`,
  `extern`, `unsafe` or `partial` in `UsdtVerify/`, and none in the pinned EthLib (only comments
  mention them). There are 35 uses of `decide +kernel`, which the kernel checks. `#print axioms`
  on `inv_call_all`, `inv_calls`, `process_step`, `inv_call`, `runFrame_ok_dispatch`,
  `transfer_complete`, `transferFrom_complete`, `destroyBlackFunds_dep_complete`,
  `transfer_ok_iff`, `transfer_iff_gas`, `transfer_dep_ok_iff_fails`,
  `destroyBlackFunds_dep_ok_iff_gas`, the five `*_call_all`, `supply_seq_all`,
  `runner_assumptions_hold` and `transfer_ok_sat` gives `[propext, Classical.choice,
  Quot.sound]` for each (exit 0). The hash test is an interpreter test, as the README says.
- **`Inv` arithmetic.** `sumBal` is a sum in `Int` of `toNat` words over `i < 2^160`, and `tot`
  is the `toNat` of slot 1. There is no U256 wrap in the invariant itself.
- **Slot layout.** Bases 1 (`_totalSupply`), 2 (`balances`), 5 (`allowed`), 6 (`isBlackListed`),
  7, 8, 9, 10, and byte 20 of slots 0 and 10, are fixed by the proofs, which execute `CODE`. A
  wrong base would not prove. Mainnet storage read during the audit matches: slot 7 holds
  "Tether USD", slot 8 "USDT", slot 9 is 6, byte 20 of slots 0 and 10 is 0 (not paused, not
  deprecated). The `StrForm` bounds (short `2n`, `1 ≤ n ≤ 31`; long odd with `32 ≤ w/2 < 2^180`)
  match Solidity's encoding and the stated hypothesis.
- **Non-deprecated headline theorems.** `inv_call` takes no static or account hypothesis, as the
  README says. `inv_call_all`'s static branch needs `StaticKeeps`, which is proved for
  `processRunner` from Paris only. Between Berlin and Paris it is an open runner assumption, and
  the README says "from Paris". The `X_ok_iff` / `X_iff_gas` coldness hypotheses are
  definitional (`c0 = coldIn …`), so they are always satisfiable.
- **Access control.** The README's "a caller who is not the owner changes only balance and
  allowance slots" matches `nonOwner_call` / `nonOwner_local` (`Writes … BalOrAllow`).
  `nonOwner_call_all` gives only `ProtKept` (slots 0, 1, 3, 4, 10 and the blacklist), which the
  README describes correctly.

## Doc changes made in this audit

- `docs/RESULTS.md`: under the invariant, a note that `KeccakSep` and `AllowSep` as stated are
  almost certainly false (finding 1). Under the runner assumptions, a note that they are false
  for `processRunner` itself (finding 2) and that `NoFail` / `hans` cannot hold for it
  (finding 3). In the non-vacuity section, the "so the main theorems do not hold only because
  their hypotheses are never true" sentence is qualified.
- `README.md`: findings 1, 2, 3, 4, 6, 7 and 8 reworded as sentences about
  what the statements say. No theorem statement was changed.

# Second audit (USDT-31)

An independent read-only reviewer that wrote none of this code ran it after round 31 (commits
157eebb and c468aaf). It had the same brief as the first audit (vacuity, definitions against the
bytecode and EthLib, overclaims in the README and docs/RESULTS.md, the trusted base), plus a check
that every Round 29/30/31 Resolution above holds. It changed no file. Its scratch proofs are not
committed. It found nothing Critical or High.

## Summary

| # | Severity | Finding | Touches |
|---|---|---|---|
| M1 | Medium | `NoFailOn`, `hfail` and the failure disjunct of `X_dep_ok_or_fails` still range over every caller frame, so for a code that reads another account's code they can be false or trivially true for `processRunner` | statements (not changed) |
| L1 | Low | README: `process_step` when deprecated is said to need only `KeepsInvAt`; it also takes `HonestBalanceAt` (and `SepOn`, `StrForm`, `StaticCode`) | README |
| L2 | Low | README: a pointer to "What is not covered yet" for deprecated exact hypotheses that cannot hold, with no such item there | README |
| L3 | Low | Stale `NoFail` / "every caller frame" / "`HonestBalanceAt` for no real code" text in RESULTS, STATUS and a docstring | docs (fixed) |
| L4 | Low | No file builds a deprecated state; every `processRunner` instance takes the upgraded code as a hypothesis | docs, possible new Sanity theorem |
| I1 | Info | The "not shown" item (one state where a useful code meets `KeepsInvAt` and `HonestBalanceAt`) is cheap to close with `MIRROR` | possible new Sanity theorem |
| I2 | Info | The local `lakefile.lean` takes EthLib by path (`../ethlib-usdt-pin5`, at `fd3457dbf`, clean); the published pin was not visible to the reviewer | none |

## M1. The runner-failure hypotheses still cover every caller frame (Medium)

`NoFailOn runChild S` (Evm/Iff.lean) is `∀ caller msg lt e, S msg → runChild caller msg lt ≠
.error e`. `hfail` in `X_dep_ok_iff_fails` and the existential of `X_dep_ok_or_fails` (from
`fwd_ok_or_fails`) also range over every caller frame, with any state. Round 30 restricted only
`hans` to the frame at the CALL (`CallFrom`). EthLib's `TransactionState.getCode` returns a
`StateError` for a code hash with no entry (State/Tracker.lean, checked), and `EvmError.state`
aborts. So, argued and not machine-checked by the reviewer: for an upgraded code that CALLs or
EXTCODESIZEs another account, there is a caller state where `processRunner` returns `.error` on a
forwarded message. Then `NoFailOn` is false (so `X_dep_ok_iff` and `X_dep_ok_iff_gas` cannot be
applied), `hfail` forces `¬ A` (against `hans` at the real frame when success is possible), and
the failure disjunct of `X_dep_ok_or_fails` holds whatever the actual run does. The STOP and
`MIRROR` instances escape only because those codes read no other account. Suggested fix
(statements, not done here): add `CallFrom` of the CALL (or `SameView` of the start state) to
`NoFailOn`, `hfail` and the existential. `fwd_ok_or_fails` already carries `Cl`.

**Resolution (round 31).** Done as suggested. `Sends.AbortsOn`, `HoareOn` and `SpecOn` take the set
of failing messages as a condition on the caller frame and the message; `callWithRS` (Evm/Route.lean)
puts in it the caller's state and substate at the CALL and the message's gas, and the seven
`spec_dep*_g` / `spec_depD_g` state their set as `SendsVia … msg ∧ CallFrom g st ss caller msg`.
`NoFailOn runChild S` takes `S` over the caller frame and the message. In the seven paths,
`X_dep_ok_iff` and `X_dep_ok_iff_gas` take `NoFailOn` of `SendsVia ∧ CallFrom`, `X_dep_ok_iff_fails`
takes `hfail` with `CallFrom`, and the failure in `X_dep_ok_or_fails` comes with `CallFrom`. So all
three are asked only of the message the CALL sends, from the caller frame at the CALL, with the gas
it gives; a runner failure from another caller state no longer matters. The STOP and `MIRROR`
instances (`noFailOn_process_stop`, `noFailOn_process_mirror`, for any caller condition) and every
`X_dep_*_process_*` theorem are re-derived unchanged in their conclusions.

**Resolution note (round 47).** The resolution above cites Evm/Sends.lean, now removed. Its
definitions are EthLib's since #1605 (Execution/Proofs/Evm/Logic/FailsOn.lean), with the same
bodies: `Sends.AbortsOn` is `FailsOn`, `Sends.HoareOn` and `Sends.SpecOn` are `HoareOn` and
`SpecOn`, and `mono_S` is `HoareOn.mono`. The set `S` is still a condition on the caller frame and
the message, so the resolution holds as stated.

## L1–L4, I1, I2

- L1, L2: README text; reported to the main session for the README.
- L3, fixed: RESULTS (the `X_dep_ok_iff` hypotheses now say `NoFailOn`; the paragraph on `hans` and
  `hfail` now says that only `hans` is restricted to the CALL's frame and states M1; "What is not
  covered" now cites `MIRROR` for `HonestBalanceAt`; `NoFailOn or hfail`), STATUS (Open, exact
  conditions), Exact/Deprecated.lean module doc.
- L4 and I1: the reviewer built, in scratch files that are not committed, a concrete Dencun state
  where slot 10 is deprecated with upgraded address 0x1234 holding `MIRROR`, and discharged every
  hypothesis of `balanceOf_dep_ok_iff_gas_process_mirror` in it. It also proved `KeepsInvAt` for
  `processRunner` with `MIRROR`, and built a deprecated destroyBlackFunds state where `KeepsInvAt`
  and `HonestBalanceAt` hold together. These are reported results of the reviewer's scratch run
  (exit 0, axioms within `[propext, Classical.choice, Quot.sound]`); they are not in the repository.
- I2: no change.

**Resolution (round 31) of L4 and I1.** Usdt/Sanity/MirrorState.lean restates the reviewer's
scratch results as committed theorems. `keepsInvAt_process_mirror`: from Paris, `processRunner`
meets `KeepsInvAt` when the upgraded address holds `MIRROR` (no precompile). `S1 C H` is a
concrete deprecated state (slot 10 of `C`: byte 20 is 1, upgraded address 0x1234, which holds
`MIRROR` under a code hash `H` other than the empty one; `exists_hash` gives one; both accounts have
the same storage). `balanceOf_mirror_sat`: from Paris and before Glamsterdam, every hypothesis of
`balanceOf_dep_ok_iff_gas_process_mirror` holds there for a `balanceOf(a)` call with 1000000 gas.
`process_step_dep_hyps`: from Paris, for a `destroyBlackFunds(a)` call there, the flag is set and
`processRunner` meets `KeepsInvAt` and `HonestBalanceAt` together. Not shown: these with the
keccak hypotheses `SepOn` of the call, which `process_step` also takes.

## Verdicts on the resolutions

- Finding 1, round 29: holds. `SepOn` / `SecSep` compare one given slot against the 2^160 address
  slots or the 11 fixed slots; `callKeys` and `sepOn_of_global` are as stated; `exists_breaks` takes
  only `NotBal 1`.
- Finding 2, round 29: holds, with a caveat. `KeepsAt`, `SentVia`, `SameView`, `Keeps.at`,
  `keepsInv_at` are as stated; `processRunner_stop_keepsAll` is conditional on the upgraded code
  (`hcode`). "The deprecated branch of `process_step` is no longer vacuous" holds for the selectors
  other than destroyBlackFunds, which also needs `HonestBalanceAt` (see L1, I1).
- Finding 2, round 30: holds. `honestBalanceAt_process_mirror` has exactly the stated hypotheses.
- Finding 3, round 29: superseded by round 30; its "not resolved" was correct at the time.
- Finding 3, round 30: holds for `hans` (`CallFrom` in all seven; the STOP instances exist).
  `NoFailOn` is still over-broad (M1).
- Finding 3, round 31, the instance: holds. Both `MIRROR` instances exist as stated; the hypotheses
  of `balanceOf_dep_ok_iff_gas_process_mirror` were shown jointly satisfiable (scratch, above).
- Finding 3, round 31, `X_dep_ok_or_fails`: partly. All seven exist with the gas-aware `hans`, and
  `X_dep_ok_iff_fails` is derived from them, but the failure disjunct is over any caller frame (M1).

## Checked and found sound

- Trusted base: no `sorry`, `admit`, `axiom`, `native_decide`, `bv_decide`, `implemented_by`,
  `extern`, `unsafe` or `partial` in `UsdtVerify/`; `lake env lean UsdtVerify/Test/Axioms.lean`
  exit 0, 821 reports, each `[propext, Classical.choice, Quot.sound]` or a subset.
- Definitions against EthLib: `processRunner` is `processMessage` of `msg.code` from
  `caller.state` and `caller.substate.child`; `SendsVia`, `atCallState`, `atCallSub` match
  `callStep_child_r`; `runFrame` turns non-aborting step errors into halts, as `NoAbort` / `StepGA`
  assume; `MIRROR`'s 87 gas base matches the opcode prices.
- Statements: `inv_call` and `inv_call_all` match the README; `SameView` (storage and code) suffices
  for `Inv`; `HonestBalanceAt` compares with the child's end state as documented. Apart from L1–L4
  the README and RESULTS claims compared match their statements (the README's access-control claim
  was checked only against the first audit's verdict).

# Third audit (USDT-32)

A third independent reviewer, who wrote none of this code, read the public README sentence by
sentence after round 31 (head `cb14650`) and compared each factual claim with the Lean statement
it cites (`#check` / `#print` in scratch files outside the repository, never committed). It also
re-checked the round-31 changes (M1, `Sanity/MirrorState.lean`, `Sanity/MirrorExact.lean`) for
vacuity, and looked for `True` hypotheses, `Nat` truncation in gas and supply statements,
quantification over empty types and misuse of `decide +kernel`. No theorem statement or README
sentence was changed; README replacements were sent to the main session. Every Lean command ran
under `safe.sh -m 9G`; `lake build` exit 0, 1400 jobs.

## Summary

| # | Severity | Finding | Touches |
|---|---|---|---|
| T1 | High | Every theorem is stated for EthLib's one-counter `Nat` meter, which EthLib uses only up to BPO5. At Glamsterdam EthLib runs transactions with the EIP-8037 `StateGasMeter`. "Glamsterdam included" is not about EthLib's Glamsterdam | statements or README |
| T2 | Medium | The runner hypotheses still range over every block and transaction environment of the forwarded message (and, for `KeepsAt`, any call data and gas). Under `processRunner`, `hans` cannot hold for an upgraded code whose success reads the block or the transaction | statements, README |
| T3 | Low | `process_step_dep_hyps` is satisfiable only degenerately: in `S1` every deprecated destroyBlackFunds call fails its guard before the CALL, and every balance is 0 | Sanity, README |
| T4 | Low | README: "`KeepsInvAcc` implies `KeepsInvAt`". No theorem says so, and it does not hold for every runner | README |
| T5 | Low | Completeness gas equalities (`s.gas = gas - okCost …`) use truncated `Nat` subtraction and do not state `okCost ≤ gas` | statements (optional) |
| T6 | Low | README: smaller overstatements (fork range of `balanceOf_mirror_sat`, `StaticCode` left out for `inv_call_all`, `depD_inv`'s `d` called "the answer", a stale `KeepsInv`) | README |
| T7 | Info | Checked and found sound (below) | none |

## T1. Glamsterdam is proved for the one-counter meter, not for EthLib's EIP-8037 meter (High)

**Evidence.** Every theorem is about `Evm fork Nat`. In `inv_call`, `inv_call_all`, the `*_complete`, the
`X_ok_iff`, `X_iff_gas` and `X_dep_*` theorems, `runner : MessageRunner fork Nat bound`.
`goodCall_process` and `process_step` take `ended : {evm : Evm fork Nat // …}`, so their
`processMessage` runs with `Meter := Nat`. EthLib at `fd3457dbf`:

- `Execution/Evm/Machine/Frame.lean:124-143`: "The meter of every fork up to BPO5: one counter of
  the gas left. These forks have no state gas … There is no reservoir, and nothing to refill, to
  roll back or to commit." (`reservoir _ := 0`, `rollback gas := gas`, `chargeState` takes
  from the one counter.)
- `Execution/Transactions/Process.lean:435-438`: `processTransaction` runs
  `runTransaction StateGasMeter …` when `fork ≥ .glamsterdam`, and `runTransaction Nat …` before.
- `Execution/Evm/Gas/StateGas.lean`: the Glamsterdam meter charges state gas from a reservoir
  first, spills the rest into execution gas, and gives the spill back on a revert
  (`gasLeft + spill`, `reservoir := baseline`). A CALL passes on the reservoir
  (`Call/Instructions.lean:248`, `reservoir := GasMeter.reservoir evm.gas`).
- No file in `UsdtVerify/` mentions `StateGasMeter`. `grep -i "8037\|StateGasMeter\|reservoir" docs/*.md`
  finds only "one-counter meter … no reservoir" (STATUS.md:924), and nothing that says EthLib
  uses another meter at Glamsterdam.

**Consequence.** At Glamsterdam the theorems are about a machine that EthLib itself does not
run for that fork. The exact gas figures, the `X_iff_gas` thresholds, `Gas.writeMax` (223,721 from Glamsterdam) and
the 2300 bound at a storage write all assume that a new slot's state gas comes out of the same
counter. Under EIP-8037 it comes from the reservoir first. So a call can succeed with less execution
gas than the stated threshold, and the gas left differs. `process_step` / `goodCall_process` "from
Paris, Glamsterdam included" classify `processMessage … (Meter := Nat)` runs, but
`processTransaction` at Glamsterdam never produces them. The invariant and the security properties
at Glamsterdam are shown only for successful one-counter runs. Nothing transfers them to
`StateGasMeter` runs. Berlin to BPO5 are not affected.

**Suggested fix.** Either (a) state the fork range as Berlin ≤ fork < Glamsterdam for the
`processMessage`-level results, and say that the Glamsterdam instances are for the one-counter
meter, or (b) generalise the gas-independent results (invariant, security, completeness of
effects) over `[LawfulGasMeter Meter]` and prove the gas-exact ones for `StateGasMeter` separately.
The README sentence "All of this holds from the Berlin fork onwards, Glamsterdam included" should
name the meter (replacement sent).

**Resolution (round 33): investigated, not resolved; the claims are restricted.** No
statement was generalised. EthLib's symbolic logic (`At`, the opcode rules, NatCode) is fixed to
`Evm fork Nat`, and so is every file of this repository that proves a path. A restatement for
`StateGasMeter` needs either a second copy of the gas framework and of the path specifications,
or a simulation lemma between the two meters' `step`, proved opcode by opcode. That lemma would
cover a top frame with reservoir 0 (a transaction gas limit of at most 2^24), no CALL and no
refill. docs/STATUS.md (round 33, T1) gives the details and the route. RESULTS.md and
STATUS.md now say that every theorem, at Glamsterdam included, is about the one-counter meter,
and that EthLib runs Glamsterdam transactions with `StateGasMeter`. The README keeps its claims
to the one-counter meter.

**Progress (round 34): part of route (b), through a simulation lemma.** Not resolved for every
result.
- Generic (UsdtVerify/Evm/Meter.lean): `step_sim` relates one step over `StateGasMeter` to one
  step over `Nat` from `toNat` of the frame (the same fields, the execution gas left as gas), for a
  frame with reservoir 0, at an opcode of the list `simulated` (the opcodes of the rules of
  Evm/GasRules.lean, CALL not included) or at a byte that is no opcode, and where an SSTORE
  refills no state gas. `ends_of_sgm` lifts it to a run of `runFrame` over `StateGasMeter`, for
  any gas bound and message runner: it gives `Gas.Ends` between the `toNat` frames.
- `Gas.Ends` (Evm/Gas.lean) is the hypothesis that the completeness theorems not deprecated,
  `inv_X` and `inv_call` now take in place of a `runFrame` equation. `Ends.run` gives it from every
  `runFrame` end. A CALL needs no hypothesis: `GasMono` and `Stuck` now name a `simulated` opcode
  (`SimAt`), so a run that `Ends` with a CALL in it contradicts every `StepG` chain.
  Round 48 note: `GasMono` is no longer a local definition. The local `StepG` is
  `Step ∧ SimAt ∧ Logic.GasMono` (EthLib's `GasMono`, #1612), and `Stuck` keeps `SimAt`, so the
  argument above holds as stated.
- USDT (UsdtVerify/Usdt/Meter.lean): `inv_call_sgm`, `ok_transfer_sgm`, `ok_approve_sgm`,
  `ok_transferFrom_sgm`, with the hypotheses `hres` (reservoir 0) and `hnr` (no SSTORE that the
  steps reach refills). `allocateGas_reservoir`: a transaction gas limit of at most 2^24 gives the
  first frame reservoir 0. Every other `ok_X` applies the same way.
- Still open: `hnr` is a hypothesis about the run, not derived from the call; the deprecated
  paths; a reservoir other than 0; the direction "enough gas gives success" of `X_ok_iff`,
  `X_iff_gas` under `StateGasMeter`; `process_step` / `goodCall_process` at Glamsterdam (their
  `processMessage` still runs over `Nat`).

**Progress (round 35).** Not resolved for every result.
- `hnr` is derived for approve and for transfer with a fee of 0, from the facts of their success
  paths. The derivation lifts a path over `StepG` to `StepI` (steps from frames that refill nothing):
  a stretch with the same storage at both ends, or one word written, and less than 97,920 gas paid,
  has no refill (`Refill.noRefill_cheap`, `noRefill_one`); each write of the path is checked from
  its original, current and new words. The one case that refills is stated as a hypothesis: approve
  writing 0 over an allowance that was 0 at the start of the transaction and is not 0 at the call
  (`hnr`), and transfer moving the whole balance of a sender whose slot was 0 at the start of the
  transaction (`hnrD`).
- Converse: `Exact.approve_iff_gas_sgm` and `Exact.transfer_iff_gas_sgm` (fee 0): from reservoir 0,
  under that hypothesis, the run over `StateGasMeter` ends with no error if and only if the guard
  holds and the gas reaches the threshold (`Refill.sgm_of_reaches`).
- Any reservoir, refills allowed: `Shadow.shadow_run` follows a run over `StateGasMeter` that ends
  with no error by a run of the meter `Nat` with more gas. `ok_approve_any`, `ok_transfer_any`,
  `ok_transferFrom_any` give the guard and the effects from it, with no hypothesis on the reservoir
  or on refills, but no gas figure.
- Still open: transfer with a fee above 0 and transferFrom in the exact form, the gas of a run with
  a reservoir other than 0 or with a refill, the deprecated paths, `process_step` and
  `goodCall_process` over `StateGasMeter`.

**Progress (round 36).** Resolved for the paths not deprecated, under named refill hypotheses.
Not resolved for the deprecated paths.
- Exact success conditions over `StateGasMeter` from reservoir 0, for the 13 writing functions not
  deprecated: `transfer_iff_gas_sgm` (any fee), `transferFrom_iff_gas_sgm` (all paths), and
  `X_iff_gas_sgm` for pause, unpause, addBlackList, removeBlackList, issue, redeem, setParams,
  deprecate, transferOwnership, destroyBlackFunds (Usdt/MeterIff.lean, Usdt/MeterOwner.lean),
  with `X_ok_sgm` (execution gas left `gas - cost`). Each takes a hypothesis on the start state
  for each write that can refill, and none for a write proved never to refill (a word that is
  not 0, or an addition with no overflow). For each function the hypotheses are listed in
  Usdt/MeterOwner.lean and Usdt/MeterIff.lean.
- The gas at any reservoir: `X_gas_any` (Usdt/MeterGas.lean), for the same 13 functions and the
  same hypotheses. A run over `StateGasMeter` that ends with no error ends with its execution gas
  left and its reservoir adding up to `gas + reservoir - cost`. The split between the two parts
  is not stated. `Shadow.gas_ge_any` gives the lower bound `gas + reservoir - cost` with no refill
  hypothesis, for a path given as a triple over `StepG`.
- `process_step` / `goodCall_process` over `StateGasMeter`: `process_stepS`,
  `goodCall_processS`, `process_value_failsS`, `inv_call_any`, `CallsS`, `inv_callsS`
  (Usdt/Invariant/SeqMeter.lean), from Paris, not deprecated. They take no hypothesis on the
  reservoir, on refills or on the gas limit of the transaction: the invariant depends only on the
  state, and `shadow_run` gives a run of the meter `Nat` that ends in the same state.
- Still open: the deprecated paths over `StateGasMeter` (CALL is not `simulated`), and the
  security properties of Usdt/Security/ over `StateGasMeter`.

**Progress (round 37).** The security properties over `StateGasMeter`, not deprecated.
- Every single-call security theorem not deprecated has a form for a run of the loop over
  `StateGasMeter`, for any gas bound, message runner and reservoir, with no refill hypothesis and
  no bound on the gas limit: `nonOwner_call_any`, `owner_only_any` and `nonOwner_local_any` (both
  except deprecated destroyBlackFunds), `paused_call_any`, `listed_call_any`,
  `allowKept_call_any`, `transferFrom_bound_any`, `supply_call_any` (Usdt/Security/). They go
  through `Security.ends_any` (from `Shadow.shadow_ends`): the run gives a loop of the meter `Nat`
  from a fresh frame of `CODE` with more gas that ends (`Gas.Ends`) in the same state. The Nat
  theorems they use take `Ends` (`effect_localE`, `owner_onlyE`, `transferFrom_boundE`).
- Sequences: `SeqS` mixes calls over the meter `Nat` (`RunOk`) and over `StateGasMeter`
  (`RunOkS`) with `Untouched` steps. `nonOwner_seqS`, `paused_seqS`, `listed_seqS`,
  `allowKept_seqS`, `supply_seqS` state the properties over it, with the hypotheses of the `Seq`
  forms. The `Seq` forms are now proved from them (`Seq.toS`). `Security.process_stepSec`
  (Usdt/Security/Meter.lean): from Paris, every top-level message with code `CODE` (no
  precompile) that `processMessage` ends over `StateGasMeter` is a `RunOkS` step or an
  `Untouched` step.
- CALL over `StateGasMeter` (Evm/CallMeter.lean): `callStep_child_rS` and `resumeCall_sgm` give
  the CALL step and the resume after the child over `StateGasMeter`, in terms of the same steps
  over `Nat`: the CALL passes on the whole reservoir in the message, and the caller gets back the
  child's execution gas left and reservoir.
- Still open: the deprecated paths over `StateGasMeter`, including the security properties when
  deprecated. EXTCODESIZE and GAS, which the deprecated paths also run, are `Lifts` of their
  instructions over `Nat` (`lifts_gasStep`, `lifts_extcodesizeStep`), but `step_sim` does not
  include them yet.


**Progress (round 38).** Not resolved for the deprecated paths. One step at EXTCODESIZE, GAS and
CALL over `StateGasMeter` is related to the step over `Nat`, from reservoir 0
(`Meter.step_simX`, `Meter.step_callX`, Evm/StepSim.lean). The message of the CALL is the same
over both meters, with reservoir 0. Not done: a run of the deprecated paths over
`StateGasMeter`, so the deprecated cases of `inv_call_any`, `process_stepS`, the `dep_*_complete`
theorems and the deprecated security properties over `StateGasMeter`.

**Progress (round 39).** Resolved for the deprecated paths from reservoir 0, except the gas left
after the CALL. Not resolved from a reservoir other than 0 when deprecated.
- `RunC` (Evm/RunC.lean): a run of the meter `Nat` with an abstract relation for the child and an
  exit at the frames the step-by-step simulation does not cover. `runC_of_sgm` (Evm/RunCS.lean):
  from reservoir 0, a run over `StateGasMeter` that ends with no error gives `RunC`, exactly up to
  the CALL and through `Shadow.shadow_run` after it.
- The seven `dep_X_complete` are proved from `dep_X_completeC` (over `RunC`) with their
  statements unchanged. `dep_X_completeS`: the same over `StateGasMeter` from reservoir 0,
  without the gas after the CALL.
- `inv_call_depS`, `inv_call_anyD`, `process_stepDS`, `process_stepSD`
  (Usdt/Invariant/DepMeter.lean): the invariant on the deprecated paths over `StateGasMeter`,
  under `KeepsInvAtS` and `HonestBalanceAtS` (the runner assumptions for a runner over
  `StateGasMeter`), from reservoir 0 (`message.reservoir = 0` for `processMessage`).
- `effect_allS` and `X_call_allS` (Usdt/Security/DepMeter.lean): the five single-call security
  properties deprecated or not over `StateGasMeter`, reservoir 0 when deprecated, with the runner
  assumptions stated by `KeepsAtS`.
- Still open: a reservoir other than 0 when deprecated, the gas left after the CALL over
  `StateGasMeter`, the deprecated sequence forms of the security properties over
  `StateGasMeter`.

**Progress (round 42).** The two items left open in round 41 are resolved for completeness. The
refill cases are resolved for success above the one-counter threshold, not for the exact
threshold.
- Deprecated, any reservoir: `dep_X_completeR` (Usdt/Complete/Deprecated/MeterR.lean) for the
  seven deprecated functions over `StateGasMeter`, from any reservoir. GAS before the CALL is no
  obstacle: no step before the CALL charges state gas, so the execution gas left follows the
  one-counter gas exactly (`Meter.step_simXR`, `Meter.step_callXR`). The forwarded message carries
  the reservoir of the frame.
- The gas after the CALL: in the same theorems, the execution gas left plus the reservoir at the
  end is exact for six paths (the gas before the CALL less its price, plus what the child returned,
  less the tail), and a lower bound for destroyBlackFunds, whose two writes after the CALL may
  refill. The split between execution gas and reservoir is not stated.
- Refills: `X_ok_dom` (Usdt/Exact/) for the 13 writing functions: under the guard and the
  one-counter threshold, the run over `StateGasMeter` succeeds at any reservoir with no refill
  hypothesis (`Shadow.dom_run`). The exact threshold and gas left when a write refills are not
  proved: a refill can pay for a later write's state gas from the reservoir, so the run can
  succeed below the one-counter threshold. `X_iff_gas_sgm` and `X_gas_any` keep their refill
  hypotheses.
- Exact with refills, approve: `approve_zero_sgm`, `approve_set_sgm` (Usdt/Refill/ApproveS.lean,
  through `one_write_sgm`, Evm/OneWrite.lean): the exact success condition and the exact gas over
  `StateGasMeter` at any reservoir, with no refill hypothesis. The threshold is
  `cost ≤ gas + sstoreBump`, a function of the start state (the refill and state gas of the write)
  and of the meter (reservoir and spill).
- Still open: the exact threshold and gas with refills for transfer, transferFrom and the owner
  functions, the split of the gas after the CALL, the invariant and the security properties from a
  reservoir other than 0 when deprecated, and a concrete deprecated state over `StateGasMeter` with
  a successful run.

**Resolution (round 43, READY): the exact threshold and gas with refills, success paths not
deprecated.**
The item left open in round 42 ("the exact threshold and gas with refills for transfer,
transferFrom and the owner functions") is resolved for every writing function on its success path
not deprecated. Evidence:
- Evm/Chain.lean: `exactS_write` composes a cheap stretch, one SSTORE and the rest of a path over
  `StateGasMeter`, with the meter after the SSTORE (`wMeter`, from `sstoreMeter`) as the meter of
  the rest. So a refill of one write, credited to the reservoir and the spill, is read by the next
  write's `wBump`. With `exactS_halt` this gives, for any number of writes, success if and only if
  the chain condition, and the exact meter at the end.
- The instances, each from any meter, for any gas bound and message runner, under the guard of
  the Nat specification, with no refill or reservoir hypothesis: `approve_zero_sgm`,
  `approve_set_sgm` (round 42), `pause_sgm`, `unpause_sgm`, `addBlackList_sgm`,
  `removeBlackList_sgm`, `transferOwnership_sgm`, `deprecate_sgm`, `issue_sgm`, `redeem_sgm`,
  `setParams_sgm`, `destroyBlackFunds_sgm`, `transfer_sgm`, `transferFee_sgm`, `transferFrom_max_sgm`, `transferFrom_sgm`, `transferFromFee_max_sgm`, `transferFromFee_sgm`.
- Clean rebuild of 95aa5ad from an empty build directory: exit 0, 1440 jobs. `#print axioms` on each: [propext, Classical.choice,
  Quot.sound]. Independent read-only review (round 43): PASS WITH FIXES, the fixes applied in 7f29631 (the approve conclusions state the
  substate, docstrings name the hypotheses, `#print axioms` for the path pieces).
- Still open under T1, unchanged: the split of the gas after the CALL when deprecated
  (`dep_X_completeR` states the sum), equality of that sum for deprecated destroyBlackFunds, the
  invariant and the security properties from a reservoir other than 0 when deprecated, and a
  concrete deprecated state over `StateGasMeter` with a successful run. The trust assumptions
  (local keccak hypotheses `SepOn` / `SecSep`, the runner assumptions, EthLib's model, the Lean
  kernel) are unchanged.

**Resolution (round 44, READY): the deprecated paths from any reservoir.**
Three of the four items left open in round 43 are resolved. Evidence:
- The invariant and the security properties from a reservoir other than 0 when deprecated:
  Usdt/Invariant/DepMeterR.lean (`inv_call_depR`, `inv_call_anyDR`, `inv_callsDR`,
  `process_stepDR`, `process_stepSDR`) and Usdt/Security/DepMeterR.lean (`effect_allSR`, the five
  `_call_allSR`, the five `_seq_allSR`, `owner_only_allSR`, `process_stepSecDR`). The runner
  assumptions are stated for the calls from a caller of reservoir 0 with a message of the
  reservoir of the first frame, as `RunSR` gives them, and at reservoir 0 they are those of round
  41. Usdt/Sanity/ProcessMeterR.lean shows `processRunnerM` meets them at every reservoir with STOP
  (`KeepsInvAtSR`, `KeepsAtSR`) and with `MIRROR` (`HonestBalanceAtSR`).
- Equality of the gas for deprecated destroyBlackFunds: `dep_destroy_exactR` states the meter after
  the CALL (`GasMeter.absorb` of the caller's and the child's meters), its split between execution
  gas and reservoir, and the exact end through the two writes, refills included.
- A concrete deprecated state over `StateGasMeter` with a successful run: `destroy_mirror_runsS`
  (from Paris, Glamsterdam included, any reservoir, at least 1000000 execution gas, in `S2` with
  `MIRROR`).
- Clean rebuild of cb60c64 from an empty build directory: exit 0, 1448 jobs. `#print axioms` on each: [propext,
  Classical.choice, Quot.sound]. Independent read-only review (round 44): PASS WITH FIXES, fixes applied in 5d949a9 (docstrings).
- Still open under T1: the split of the gas after the CALL for the six deprecated paths other than
  destroyBlackFunds (`dep_X_completeR` states the sum), and the preparation of the first frame
  (`prepareFirstFrame`). The trust assumptions are unchanged.

**Resolution (round 45, READY): the items left open in round 44.**
- The split of the gas after the CALL for the six other deprecated paths: `dep_X_exactR`
  (Usdt/Complete/Deprecated/PathsS.lean) for totalSupply, balanceOf, allowance, transfer, approve
  and transferFrom states the caller's meter, the meter after the CALL
  (`GasMeter.absorb caller.gas child.gas true`), that the tail's gas is at most its execution gas
  left, and the exact end meter (that meter less the tail's gas in execution gas), through
  `fromExtSG`, `resumeG` and `dep_call_exactS`.
- The preparation of the first frame: `FirstFrame.prepareFirstFrame_call` (Evm/FirstFrame.lean)
  for a call with no value and no authorization, and `destroy_mirror_callS`
  (Usdt/Sanity/MirrorCallS.lean), a concrete deprecated destroyBlackFunds through EthLib's
  `processMessageCall` over `StateGasMeter` in `S3` (`S2` with `CODE` at `C`) that gives an output
  with no error. With authorizations it is not done: `applyAuthorization` recovers each authority
  by secp256k1 ECDSA recovery over a keccak hash, out of reach for given signatures; a form with
  the recovered authorities as hypotheses is possible and open. The `processMessage` forms hold
  for any starting meter (U1).
- Evidence: clean rebuild of fd2e8e7 from an empty build directory, exit 0, 1452 jobs, 3:04 wall; `#print axioms` on each new theorem gives [propext, Classical.choice, Quot.sound] or a subset (UsdtVerify/Test/Axioms.lean); independent read-only review (round 45) PASS WITH FIXES, fixes applied in 6f779e5 (docstrings) and in these docs (the authorizations assessment). The trust assumptions are unchanged.
- Still open under T1: `prepareFirstFrame` with authorizations (see above).

**Resolution note (round 47).** `FirstFrame.prepareFirstFrame_call` (Evm/FirstFrame.lean, removed)
is EthLib's `prepareFirstFrame_of_value_eq_zero` since #1599, the same statement.
`destroy_mirror_callS` now uses it.

**Resolution (round 46, READY): `prepareFirstFrame` with authorizations.**
- With the recovered authorities as hypotheses (Evm/Auth.lean). `apply_out`, `apply_none`,
  `apply_refused` and `apply_accepted` state what one `applyAuthorization` returns once
  `recoverAuthority auth` is given (or the authorization is out of scope), and `apply_cases` says
  every `.ok` result is one of these. `delegate_ok` states the state change of an accepted
  authority: the code hash of `delegationCode auth`, the nonce plus one, every other address
  unchanged, and the refund `delegateRefund`. `pay_pre` and `pay_glam` state the meter (unchanged
  before Glamsterdam, the meter of `chargeAuthorization` from Glamsterdam).
  `prepareFirstFrame_auths` states the first frame of a call with no value after authorizations
  that end with `.ok done`: `done.state` with the read of the recipient, the accesses and the
  refund of `done`, and the meter `GasMeter.commit done.meter`.
- An address whose code is not empty and no delegation indicator (USDT's `C`, `MIRROR`'s `UA`) is
  refused as an authority (`accepts_code`, `apply_code`). When no `delegationCode` of the list
  hashes to its code hash (a keccak hypothesis), its account, storage and code are kept
  (`fold_keeps`). Over `StateGasMeter`,
  `fold_exists` shows that the authorizations of any list succeed when every code hash resolves,
  and from Glamsterdam with 227790 execution gas per authorization; they take at most that much. It holds with no hypothesis
  on `recoverAuthority`.
- End to end (Usdt/Sanity/MirrorAuth.lean). `destroy_mirror_call_auths`: from Paris, in `S3`, a
  deprecated `destroyBlackFunds(a)` from `CALLER_A` to `C` with any list of authorizations (no
  `delegationCode` hashing to `H` or `HC`), any paid writes, and enough gas goes through
  `processMessageCall` over `StateGasMeter` to an output with no error. `apply_usdt`: an authorization in
  scope whose authority is `C` is refused. `apply_caller_S3`: before Glamsterdam, the first
  authorization of a list from `S3`, with authority the caller and nonce 0, is accepted, and the
  result is given exactly. In a real transaction `buyGas` raises the sender's nonce first, so that
  instance only illustrates the lemmas.
- Evidence: Clean rebuild of fb104c2 from an empty build directory, exit 0, 1454 jobs, 188.85 s wall, 483 s user; `#print axioms` on each new theorem gives [propext, Classical.choice, Quot.sound] or a subset (UsdtVerify/Test/Axioms.lean); independent read-only review (round 46) PASS WITH FIXES, fixes applied in 5e376ee (docstrings, one proof step; incremental build exit 0, 1454 jobs) and in these docs (the scope, the `buyGas` caveat). The trust assumptions are unchanged.
- Still open under T1: nothing on the authorizations of a message to USDT. The transaction around
  the message (`processTransaction`) is not stated for a type-4 transaction. The keccak
  hypothesis on `H` and `HC` is assumed.

## T2. The runner hypotheses range over every block and transaction environment (Medium)

**Evidence.** `SendsVia` (Evm/Route.lean:134) fixes `caller`, `currentTarget`, `target`,
`codeAddress`, `code`, `disablePrecompiles`, `data`, `value`, `depth`, `isStatic`. `CallFrom`
fixes `msg.gas`, `caller.state`, `caller.substate`. Neither fixes `msg.blockEnv`, `msg.txEnv` or
`msg.shouldTransferValue` (EthLib `Message`, Machine/Frame.lean:238). EthLib's CALL builds the
child message with `blockEnv := evm.message.blockEnv`, `txEnv := evm.message.txEnv`
(Call/Instructions.lean:258-259), and TIMESTAMP, NUMBER, ORIGIN, GASPRICE, COINBASE, CHAINID, BASEFEE
… read `evm.message.blockEnv` / `txEnv` (Instructions/EnvironmentData.lean:70-133). Machine-checked
in scratch (exit 0, axioms `[propext, Classical.choice, Quot.sound]`):

```lean
theorem sendsVia_callFrom_env (h1 : SendsVia message ua c r d msg) (h2 : CallFrom g st ss caller msg)
    (b : BlockEnvironment fork) (t : TransactionEnvironment fork) :
    SendsVia message ua c r d { msg with blockEnv := b, txEnv := t } ∧
      CallFrom g st ss caller { msg with blockEnv := b, txEnv := t } := ⟨h1, h2⟩
theorem sentVia_env (h : SentVia message S ua caller msg) (b t) :
    SentVia message S ua caller { msg with blockEnv := b, txEnv := t } := h
```

`SentVia` (the set of `KeepsInvAt`, `HonestBalanceAt` and the security `KeepsAt`) also leaves the call
data free (`SendsVia … msg.data msg`). It also leaves free the gas, the caller's substate, and every
account field except storage and code (`SameView`).

**Consequence (argued, not machine-checked).** Take `processRunner` and an upgraded code whose
success depends on the environment, for example `TIMESTAMP PUSH1 5 JUMPI INVALID JUMPDEST STOP`.
With the gas of the CALL fixed, the forwarded message succeeds for one timestamp and fails for
another. Both messages are in the set of `hans`, so no `A` makes `hans` true. So `X_dep_ok_iff`,
`X_dep_ok_iff_gas`, `X_dep_ok_iff_fails` and `X_dep_ok_or_fails` are vacuous for such a code
under the real runner. `KeepsInvAt` and `HonestBalanceAt` likewise demand the property under every
environment and every call data. `NoFailOn`, `hfail` and the failure disjunct concern `.error`
results. For `processRunner` these come from the state, which `CallFrom` fixes, so the M1 fix holds
for them in practice. STOP and `MIRROR` read no environment, so every existing instance stands.
This is the same class of issue as finding 3 and M1, one field set further.

**Suggested fix.** Add `msg.blockEnv = message.blockEnv ∧ msg.txEnv = message.txEnv` (and
`msg.shouldTransferValue = true`) to `SendsVia`. `callStep_child_r` gets them from `finishCall`.
For `KeepsAt`, either fix the data (`dataB` for destroyBlackFunds, the forwarded data otherwise) or
state in the README that it is free.

**Resolution (round 33).** `SendsVia` (Evm/Route.lean) adds `msg.blockEnv = message.blockEnv`,
`msg.txEnv = message.txEnv` and `msg.shouldTransferValue = true`. `callStep_child_r` proves them
from EthLib's `finishCall`, and `callWithRS`, `callWithR` and `CallEnd` carry them. `SentVia`
contains `SendsVia`, so `KeepsAt`, `KeepsInvAt` and `HonestBalanceAt` get them. `CallFrom` is
unchanged, because every hypothesis that takes `CallFrom` also takes `SendsVia` of the same
message. The reviewer's `sendsVia_callFrom_env` and `sentVia_env` no longer hold for a changed
environment (`SendsVia.env`). The whole repository builds with no other proof changed, and the
STOP and `MIRROR` instances stand. `SentVia` still leaves the call data, the gas and the caller's
substate free. No instance with an environment-reading upgraded code is proved.

**Resolution note (round 48).** `callStep_child_r` keeps its statement, the environments and
`shouldTransferValue` included. It is now proved from EthLib's `callStep_child_of_routes` (#1611)
for CALL, whose `CallSends` states the same fields (and a message reservoir of 0, not used here).

## T3. `S1` exercises no deprecated destroyBlackFunds forward (Low)

**Evidence.** In `S1 C H` the only nonzero slot of `C` is 10. So the owner is the zero address,
`isBlackListed[a]` is 0, and every `balances[a]` is 0 on both `C` and `UA`. Machine-checked in
scratch (exit 0, standard axioms):

```lean
theorem S1_destroy_guard_false (b t C caller a H c)
    (h10 : BlackList.listSlot (addrArg (mD b t C caller a).data 0) ≠ 10) :
    ¬ DestroyDepGuard (S1 C H) (mD b t C caller a) c
```

By `dep_destroy_complete` (which concludes the listed check), no deprecated destroyBlackFunds call
in `S1` succeeds. Every one stops before the CALL. `process_step_dep_hyps` therefore shows that
`KeepsInvAt` and `HonestBalanceAt` can hold together, but only in a state where the branch they
guard is never taken. `HonestBalanceAt` holds there as `0 = 0`. `balanceOf_mirror_sat` is not
degenerate in this way: the reviewer proved its right-hand side at Pectra for every substate
(`mirror_run_succeeds`, scratch, exit 0, standard axioms), so the run in `S1` really succeeds
through the `MIRROR` call.

**Suggested fix.** A second state with the caller as owner, `a` blacklisted, and the same nonzero
`balances[a]` at `C` and `UA` (with `Inv` from `UniqBal`-style facts on the few slots set), and a
proof that the destroyBlackFunds run there succeeds and ends with `Inv`.

**Resolution (round 33).** Usdt/Sanity/MirrorState.lean adds the state `S2 C H a`. `C` and
`UA` have the same slots: 10 (deprecated, upgraded address `UA`), 0 (owner `CALLER_A`, not
paused), `isBlackListed[a]` 1 and `balances[a]` 1. `UA` holds `MIRROR`. The proofs split on every
equality between the keccak slots and 0, 10 and each other, so they compute no keccak value.
`process_step_dep_hyps2` (from Paris): the flag is set, the caller is the owner, `a` is
blacklisted, `balances[a] ≠ 0` at `C`, `MIRROR`'s slot holds the same word, and `processRunner`
meets `KeepsInvAt` and `HonestBalanceAt`. `destroy_mirror_runs` (Paris ≤ fork < Glamsterdam,
1000000 gas, any substate): the deprecated destroyBlackFunds call ends with no error under
`processRunner`. It is derived from `destroyBlackFunds_dep_ok_iff_gas_process_mirror`, so the run
passes the checks and goes through the CALL. Not done: `Inv` in `S2`, which needs keccak
separation facts about the balance slots, so `Inv` after the run is not proved either.

**Resolution (round 45).** Through round 44 slot 1 (`_totalSupply`) was not set in `S2`, so `Inv`
failed there unless a keccak slot of `a` is slot 1. `S2` now has `_totalSupply` 1 (a fifth pair of
`KD`, after the others, so the earlier lemmas keep their statements). `inv_S2`: `Inv` in `S2` under
`SepOn [kD a]`. `destroy_mirror_inv` (Paris to before Glamsterdam): under `SepOn` of the call's
keys, `Inv` holds in `S2`, the call ends with no error, and `Inv` holds after every successful run
of it. The separation is assumed, not proved.

## T4. `KeepsInvAcc` does not imply `KeepsInvAt` (Low, README)

README: "The earlier forms over every message, `KeepsInv` and `KeepsInvAcc`, imply it."
`keepsInv_at` gives `KeepsInv → KeepsInvAt`. For `KeepsInvAcc` the only theorem is
`keepsInv_of_acc : KeepsInvAcc → KeepsInvNoAcc → KeepsInv`. `KeepsInvAcc` says nothing from a caller
state with no account of `C`, and `SameView` (storage and code only) allows such a caller state.
So a runner that breaks `Inv` only there meets `KeepsInvAcc` and not `KeepsInvAt` (argued).
Replacement sent.

**Resolution (round 33).** The true direction is now a theorem. `keepsInvAt_of_acc`
(Usdt/Invariant/All.lean): `KeepsInvAcc` and `KeepsInvNoAcc` together give `KeepsInvAt`. No
theorem gives `KeepsInvAt` from `KeepsInvAcc` alone, and the reviewer's argument against it
stands. A machine-checked counterexample would need a keccak fact such as `NotBal 1` to break
`Inv`, so none is given. The README was corrected before this round.

## T5. Truncated subtraction in completeness gas equalities (Low)

`ok_transfer` and the other non-deprecated `ok_*` conclude `s.gas = gas - okCost …` (`Nat`) and
do not conclude `okCost … ≤ gas`. If that bound failed, the equality would read `s.gas = 0`. The
exactness claim holds only together with `X_iff_gas` (success gives `max cost stip ≤ gas`), and the
README's "ends exactly as its spec says" does not say so. The deprecated `dep_*_complete` are
fine: they conclude `preCost + 100 + R ≤ gas`, and `messageCallGas` keeps the CALL's cost within
the gas left, so no subtraction there truncates. Hypotheses like `121 ≤ gas - preCost - cost` can
only become stronger by truncation. The supply statements (`SupplyStep`) are additive in `Nat`,
and `Inv` is in `Int`, so neither truncates. Suggested fix: add the `okCost ≤ gas` conjunct.

**Resolution (round 33).** Done as suggested. Every non-deprecated `ok_X` in
Usdt/Complete/ (Read, Getters, Owner, Approve, Transfer, TransferFrom) concludes
`(cost ≤ gas ∧ s.gas = gas - cost)` where it concluded `s.gas = gas - cost`. The bound comes
from `ok_exact`, `ok_exact2` and `ok_exact3`. It is one conjunct at the same position, so every
caller builds unchanged.

## T6. Smaller README overstatements (Low)

- "In it, every hypothesis of the gas-exact deprecated `balanceOf` theorem holds" leaves out
  that `balanceOf_mirror_sat` is from Paris and before Glamsterdam, and that it is the `MIRROR`
  instance. "Only the keccak hypothesis `SepOn` is not discharged there" also leaves out the other
  hypotheses of `process_step` (`StrForm`, size, no precompile, static), and the T3 caveat.
- `inv_call_all`'s static branch needs `message.code = CODE ∧ StaticCode state message ∧
  StaticKeeps`. The README names only `StaticKeeps` there. It also says "left to `KeepsInv`",
  but the hypothesis is now `KeepsInvAt`.
- `depD_inv` concludes `∃ S d, … evm.state = tailState S C a d ∧ (Inv ↔ d = balance in S)`. `d` is
  not tied to the upgraded contract's answer in this statement (the specification of the path ties
  it). The README says "the upgraded contract's answer".
- "Logic/NatCode.lean" is `EthLib/Execution/Proofs/Evm/Logic/NatCode.lean` (Info).

**Resolution (round 33).** The main session corrected the README before this round. No Lean
statement was involved.

## T7. Checked and found sound (Info)

- Every file path the README names exists after the reorganisation into `Evm/` and `Usdt/`, and
  every theorem or definition it names exists with the stated name (`StaticCode` is EthLib's). The
  file names given for theorems are right (`inv_call` in Invariant/Calls.lean, `inv_call_all` in
  Static.lean, `inv_calls` and `process_step` in Seq.lean, `inv_tail_iff` … in
  DeprecatedDestroy.lean, `owner_only` in Access.lean).
- Numbers: 11,075 bytes, keccak `b44fb4e9…ea55` (build output), byte 3565 is `0x5b`, 32 selectors
  (`ENTRIES.length = 32`), 19 read functions, 13 writing functions, 10 owner functions, 7 forwards,
  fallback 773 and 46 gas with `773 ≤ gas` / `46 ≤ gas`, nonpayable revert at `87 + 22 (i+1)` gas,
  `MIRROR` 25 bytes, `StrForm` long form below 2^180, the 2300 bound (`sstore_low_stuck`, from Istanbul),
  `X_iff_gas` threshold `max cost stip`.
- `SepOn`: every field compares one given slot with the 2^160 balance slots or with the 11 fixed
  slots, as the README says. The 2^-96 is per key. For keys an adversary chooses, a violation is a
  two-function keccak collision, about 2^128 work. That is consistent with the README.
- No `sorry`, `axiom`, `native_decide`, `bv_decide`, `admit`, `implemented_by`, `extern`, `unsafe` or
  `partial def` in `UsdtVerify/`. The build reports 833 `#print axioms` lines: 827 with a subset of
  `[propext, Classical.choice, Quot.sound]`, 6 with none, 0 with `sorryAx`. All 35 `decide +kernel`
  are on closed goals (exp constants, selector bytes, sizes, the jumpdest walk, string bytes).
- No hypothesis of a main theorem is `True`. The `True` occurrences are `A = True` in Sanity
  instances and `I := fun _ => True` in sequence lifts. `BlockEnvironment fork` and
  `TransactionEnvironment fork` are inhabited (their fork-dependent fields are `Since`, a function
  type), so the Sanity `∀ b t, ∃ …` are not vacuous. `exists_hash` gives a hash for `S1`.
- Round 31 M1: `NoFailOn`, `hfail` and the failure disjunct now carry `CallFrom` (state, substate,
  gas). Apart from T2 they are asked of the frame and gas at the CALL. `balanceOf_mirror_sat`'s
  hypotheses are jointly satisfiable, and its success side holds (T3).
- Measurement caveat (Info): the 1.8 GB in the README is the `max RSS` from `/usr/bin/time -l`,
  the largest single process, not the sum over parallel jobs.

# Fourth audit (USDT-40)

A fourth independent reviewer, who wrote none of this code, audited the EIP-8037 work of rounds
33 to 39 (head `81d7cd1`): Evm/{Meter, Refill, Shadow, ProcessMeter, CallMeter, CallSim, StepSim,
RunC, RunCS}.lean, Usdt/Meter*.lean, Usdt/Refill/, Usdt/Invariant/{SeqMeter, DepMeter}.lean,
Usdt/Security/{Meter, DepMeter}.lean, Usdt/Complete/Deprecated/Meter.lean, the T2 to T5 fixes, and
the Glamsterdam sentences of the public README. Each claim was compared with the Lean statement
(`#check`, `#print axioms`) and with EthLib at `fd3457dbf` (the pin of `lakefile.lean`). Scratch
files lived outside the repository and are not committed. No theorem statement or README sentence
was changed; README replacements were sent to the main session. Every Lean command ran under
`safe.sh -m 9G`. `lake build`: exit 0, 1423 jobs, `CODE` 11075 bytes, keccak256
`b44fb4e9…ea55`, 1064 `depends on axioms` lines and 7 `does not depend` lines, none with `sorryAx`.

## Summary

| # | Severity | Finding | Touches |
|---|---|---|---|
| U1 | Medium | The `processMessage` theorems over `StateGasMeter` use the default start meter. At Glamsterdam, `processTransaction` passes the meter left by the authorizations, which differs whenever an authorization pays state gas, so type-4 transactions to USDT are not covered | statements, README |
| U2 | Low | No instance of `KeepsInvAtS`, `KeepsAtS` or `HonestBalanceAtS` for EthLib's runner, and no concrete run over `StateGasMeter`. The reviewer proved the first two for `processRunnerM` with STOP | Sanity, README |
| U3 | Low | The `…AtS` runner hypotheses leave the reservoir of the forwarded message and the caller's meter free, although the CALL from reservoir 0 sends reservoir 0 | statements (optional) |
| U4 | Low | README: smaller overstatements in the Glamsterdam paragraph | README |
| U5 | Info | Checked and found sound (below) | none |

## U1. The `processMessage` forms use a meter that `processTransaction` does not always use (Medium)

**Evidence.** `goodCall_processS`, `process_value_failsS`, `process_stepS`
(Usdt/Invariant/SeqMeter.lean), `process_stepDS`, `process_stepSD` (Usdt/Invariant/DepMeter.lean),
`runOkS_process` and `process_stepSec` (Usdt/Security/Meter.lean) take
`hproc : processMessage fork message state substate = .ok ended`. `#check` shows the elaborated
term `processMessage fork message state substate (GasMeter.start message.gas message.reservoir) ⋯`.
EthLib's `processMessageCall` (Transactions/Process.lean:337) calls
`processMessage fork first.message first.state first.substate first.meter first.held`, where
`first.meter` comes from `prepareFirstFrame` (Process.lean:275-312). At Glamsterdam that function
applies the authorizations, whose `chargeAuthorization` (Transactions/Authorization.lean:172-182)
charges `NEW_ACCOUNT_STATE_GAS` and `AUTH_BASE_STATE_GAS` with `chargeState`, and then calls
`GasMeter.commit`. From reservoir 0 the charge spills, and the commit moves the spill to
`committed`. From a reservoir above 0 it lowers `reservoir` below `grant`. Either way the meter is
not `start (gasHeld meter) reservoir`. Machine-checked in scratch (exit 0, axioms
`[propext, Quot.sound]`):

```lean
theorem commit_ne_start (g a : Nat) (ha : 0 < a) (hag : a ≤ g) (m : StateGasMeter)
    (h : StateGasMeter.chargeState (StateGasMeter.start g 0) a = .ok m) :
    StateGasMeter.commit m ≠
      StateGasMeter.start (StateGasMeter.gasHeld (StateGasMeter.commit m))
        (StateGasMeter.commit m).reservoir
```

**Consequence.** For a Glamsterdam transaction to USDT whose authorization list pays any state gas
(the usual case for an authorization that sets a delegation), the `processMessage` term that EthLib
evaluates is not the one in `hproc`, and none of the seven theorems applies to it. The README
sentence "every top-level message to USDT that EthLib runs with the EIP-8037 meter, from Paris on,
is a step that keeps the invariant" is wider than the statements. Before Glamsterdam no
authorization touches the meter, so the `Nat` forms are not affected. The substance is very likely
true: the start meter differs only in `committed`, `grant` and `baseline`, which matter only for a
rollback, and the step `shadow_ends` already allows any meter. It is not proved.

**Suggested fix.** State the seven theorems for `processMessage fork message state substate meter
held` with any `meter : StateGasMeter` and `held`, and `GasMeter.reservoir meter = 0` in place of
`message.reservoir = 0` for the deprecated forms. This needs `processMessage_map_valM` and
`at_startFrameS` for a given start meter (the frame's `toNat` is the fresh frame of `CODE` with gas
`meter.gasLeft`). Until then, the README should say that the top-level results are for a message
whose frame starts with a fresh meter, which excludes transactions whose authorizations pay state
gas (replacement sent).

**Resolution (round 41).** Fixed as suggested. The seven theorems take
`processMessage fork message state substate meter held = .ok ended` for any
`meter : StateGasMeter` and `held`, and the deprecated forms take `meter.reservoir = 0`.
`processMessage_map_valM`, `processMessage_map_val_valueM` and `at_startFrameS` take the starting
meter. The old statements remain as `goodCall_processS_start`, `process_value_failsS_start`,
`process_stepS_start`, `process_stepDS_start`, `process_stepSD_start`, `runOkS_process_start` and
`process_stepSec_start`.

**Resolution (round 46).** The link from a type-4 message to the starting meter is now stated.
`Auth.prepareFirstFrame_auths` gives the first frame after the authorizations, with the meter
`GasMeter.commit done.meter`. `Sanity.destroy_mirror_call_auths` runs a concrete deprecated call to
USDT through `processMessageCall` over `StateGasMeter`, with any list of authorizations, to an
output with no error (see T1, round 46). The transaction around the message
(`processTransaction`) is still not stated for a type-4 transaction.

**Resolution note (round 47).** `processMessage_map_valM` and `processMessage_map_val_valueM`
(Evm/ProcessMeter.lean, removed) are EthLib's `processMessage_map_val` and
`processMessage_map_val_value` since #1599, which take any lawful meter and any starting meter.
`at_startFrameS` moved to Evm/Meter.lean (`Meter.at_startFrameS`), unchanged.

## U2. No instance of the runner assumptions over `StateGasMeter` (Low)

**Evidence.** No file in Usdt/Sanity/ mentions `StateGasMeter`. `KeepsInvAtS`, `HonestBalanceAtS`
and `KeepsAtS` appear only in Invariant/DepMeter.lean, Security/DepMeter.lean, Summary.lean and
Test/Axioms.lean. So the repository shows no instance of any of them, for EthLib's runner or any
other, and no concrete run over `StateGasMeter` where an `_sgm`, `_any` or `S` theorem applies.

**Reviewer's instances (scratch, exit 0, axioms `[propext, Classical.choice, Quot.sound]`).** The
proof of `Sanity.process_stop` carries over to `processRunnerM` with a direct computation of the
one STOP step:

```lean
theorem step_stopS (f : Evm fork StateGasMeter) (hc : f.code = Sanity.STOP_CODE) (hpc : f.pc = 0) :
    step fork f = .ok (.next (advance { f with running := false })) := by
  have h : f.pc < f.code.size := by rw [hc, hpc]; decide
  have hd : Op.ofByte fork f.code[f.pc] = some .stop := by simp only [hc, hpc]; rfl
  rw [step_of_instruction h hd (by rfl)]; rfl

theorem process_stopS (hparis : .paris ≤ fork) {bound : Nat} (caller : Evm fork StateGasMeter)
    {msg : Message fork} (lt : msg.gas < bound) (hcode : msg.code = Sanity.STOP_CODE)
    {ua : Address} (ht : msg.target = some ua) (hv : msg.value = 0)
    (hpre : precompileAddress fork msg = none)
    {child : { evm : Evm fork StateGasMeter // GasMeter.gasHeld evm.gas ≤ msg.gas }}
    (hch : ProcessMeter.processRunnerM fork bound caller msg lt = .ok child) :
    child.1.error = none ∧ child.1.state = caller.state
  -- runFrame_of_step_eq_next, runFrame_of_running_eq_false, processMessage_map_valM

theorem keepsInvAtS_process_stop (hparis : .paris ≤ fork) {bound : Nat}
    {message : Message fork} {S : State.TransactionState}
    (hcode : S.getCode (S.getAccount (upAddr S message)).codeHash = .ok Sanity.STOP_CODE)
    (hnp : Precompiles.isPrecompile fork (upAddr S message).toU256.toNat = false) :
    KeepsInvAtS (ProcessMeter.processRunnerM (Meter := StateGasMeter) fork bound) message S

theorem keepsAtS_process_stop … {R} (hR : ∀ X, R X X) :
    Security.KeepsAtS (ProcessMeter.processRunnerM (Meter := StateGasMeter) fork bound) message S
      (upAddr S message) R
```

So `KeepsInvAtS` and every `KeepsAtS` of Security/DepMeter.lean (all five relations are reflexive
in the `Nat` instances) can hold for EthLib's runner. `HonestBalanceAtS` with real code (the
`MIRROR` contract over `StateGasMeter`) was not attempted. The other new hypotheses are decidable
facts of the start state or of the frame: `hres` holds for the frame of `processMessage` when
`message.reservoir = 0`, which `allocateGas` gives for a gas limit of at most 2^24, and `hnr`,
`hnrD`, `hnrA` and the owner forms hold whenever the written word is not 0 or the slot was not 0
at the start of the transaction. None of them was found to be vacuous.

**Suggested fix.** Add the two theorems above to Usdt/Sanity/ (for example Sanity/ProcessMeter.lean)
and, if possible, an `HonestBalanceAtS` instance with `MIRROR`.

**Resolution (round 41).** Fixed. Usdt/Sanity/ProcessMeter.lean has the reviewer's `step_stopS`,
`process_stopS`, `keepsInvAtS_process_stop` and `keepsAtS_process_stop`, restated for the U3 forms
of the definitions. It also has `process_mirrorS` and `honestBalanceAtS_process_mirror`: from
Paris, `processRunnerM` over `StateGasMeter`, at any bound, meets `HonestBalanceAtS` when the
upgraded address holds `MIRROR`, is no precompile, and its slot `balSlot message` holds in `S` the
word of USDT's `balances[a]`. A concrete deprecated state over `StateGasMeter` where these hold
together with a run of USDT that ends with no error is not shown.

**Resolution note (round 47).** `ProcessMeter.processRunnerM` (Evm/ProcessMeter.lean, removed) is
EthLib's `processRunner`, generic in the meter since #1599. The theorems of
Usdt/Sanity/ProcessMeter.lean and ProcessMeterR.lean now name `processRunner` with the meter
`StateGasMeter`, the same function.

## U3. The `…AtS` hypotheses leave the message reservoir and the caller meter free (Low)

**Evidence.** `KeepsInvAtS`, `HonestBalanceAtS` and `KeepsAtS` constrain the caller only through
`SentVia … (toNat caller) msg`, and `SendsVia` does not mention `msg.reservoir`. Scratch (exit 0):

```lean
theorem sentVia_reservoir (h : SentVia message S ua caller msg) (r : Nat) :
    SentVia message S ua caller { msg with reservoir := r } := h
```

At the CALL the theorems actually use, the frame has reservoir 0 and the message carries it
(`callStep_child_rS`: `msg.reservoir = evm.gas.reservoir`, `CallCorr`: `caller.gas.reservoir = 0`).
Under `processRunnerM` a child with a reservoir can succeed where the same child from reservoir 0
runs out of gas, and an upgraded code that branches on `GAS` can then reach a different state. The
hypotheses therefore ask the property of runs that the deprecated paths of USDT never make. This
is the T2 pattern for one more field. It does not affect the STOP instances of U2.

**Suggested fix.** Add `msg.reservoir = 0` (and, if wanted, `caller.gas.reservoir = 0`) to the
three definitions, carried by `RunS` from `CallCorr`. Otherwise say in the README that the gas and
the reservoir of the forwarded message are free.

**Resolution (round 41).** Fixed as suggested, with both facts. `callStep_child_res0`
(Evm/CallMeter.lean): from a frame with reservoir 0, the CALL sends a message with reservoir 0
and the caller frame has reservoir 0. `CallCorr` states `msg.reservoir = 0`, and `RunS` carries
`cS.gas.reservoir = 0` and `msg.reservoir = 0`. `KeepsInvAtS`, `HonestBalanceAtS` and `KeepsAtS`
take `caller.gas.reservoir = 0 → msg.reservoir = 0 →` before the run of the runner. `FwdAtS` and
the conclusions of the seven `dep_X_completeS` state both facts. The gas of the forwarded message
and the other fields of the caller's meter stay free in the three definitions, as before.

## U4. Smaller README overstatements in the Glamsterdam paragraph (Low)

- "`UsdtVerify/Usdt/Meter.lean` carries the completeness theorems outside the deprecated mode …
  over to that meter". That file states `ok_transfer_sgm`, `ok_approve_sgm`, `ok_transferFrom_sgm`
  and `inv_call_sgm`. The other `ok_X` apply through `ends_of_sgm` but are not stated. The exact
  conditions for the 13 writing functions are in MeterIff.lean and MeterOwner.lean.
- "is not 0 at the call". `sstoreStateRefill` compares the word just before the write
  (`getStorage` at the SSTORE). For `approve` that is the word at the call. For the second write of
  `transferFrom`, `issue`, `redeem` and `destroyBlackFunds` it is the word after the first write.
- "it succeeds exactly when … unless the call writes 0 over such an allowance". The theorem
  assumes that case away (`hnr`). It does not say that such a call fails.
- "(`UsdtVerify/Usdt/Security/Meter.lean`)" for the single-call security properties at any
  reservoir. That file has only the `processMessage` steps. The single-call `_any` theorems are in
  Security/Access.lean, Pause.lean, Blacklist.lean, Allowance.lean and Supply.lean.
- "the steps at `EXTCODESIZE`, `GAS` and `CALL` match those of the one-counter meter". At CALL,
  `step_callX` is one-sided in its first case (`StepBadS`): when the step over `StateGasMeter` fails
  (too little execution gas, or a delegate whose code is missing), nothing is said about the step
  over `Nat`. The match holds whenever the step over `StateGasMeter` does not fail.
- "every top-level message to USDT that EthLib runs with the EIP-8037 meter" (U1).

**Resolution (round 41).** The public README is kept outside this repository. Its Glamsterdam
sentences are edited by the main session, not by a commit here. Since round 41 the last item is
covered by U1. Replacement sentences for the changes of U1 to U3
were sent to the main session.

## U5. Checked and found sound (Info)

- The meter. Every theorem over `StateGasMeter` uses EthLib's `GasMeter StateGasMeter` instance
  (Evm/Machine/Frame.lean:179-193), and the repository declares no meter instance of its own.
  `processTransaction` runs `runTransaction StateGasMeter` for `glamsterdam ≤ fork < hegota`
  (Process.lean:435-439). `processRunnerM` is EthLib's `processRunner` for any meter.
- `allocateGas_reservoir` matches EthLib: `allocateGas` (Transactions/Settlement.lean:145-150) sets
  the reservoir to `evmGas - min (TX_MAX_GAS_LIMIT - intrinsic) evmGas`, with
  `TX_MAX_GAS_LIMIT = 16777216`, so a gas limit of at most 2^24 gives 0. EthLib's validity
  (Proofs/Transactions/Validity.lean:163-165) lifts the 2^24 cap at Glamsterdam, so a reservoir
  above 0 is reachable, and the README limits the claim correctly. `prepareFirstFrame` has no
  refill, so the first frame's meter keeps reservoir 0.
- The refill. `sstoreStateRefill` (Instructions/Storage.lean:148-149) is `STORAGE_SET_STATE_GAS`
  (64 × 1530 = 97,920) when `fork ≥ glamsterdam`, `original = 0`, `current ≠ 0` and `new = 0`,
  and 0 otherwise. `getStorageOriginal` is the word before the transaction (0 for an account the
  transaction created). `NoRefill`, `hnr`, `hnrD`, `hnrA` and the owner hypotheses are this
  quantity at 0, so the README's characterization holds (up to U4).
- `step_sim` and `sim_sstoreStep`. At reservoir 0, `StateGasMeter.chargeState` fails exactly when
  the `Nat` charge fails and takes the same amount from the execution gas (the rest goes to
  `spill`, which no theorem reads). The 2300 check reads `gasLeft` on both meters. A refill of 0 is
  the identity. GAS pushes `gasLeft` on both meters.
- "Any reservoir" claims. `inv_call_any`, `ok_X_any`, the security `_any` theorems,
  `process_stepS` and `X_gas_any` have no hypothesis on the reservoir. They go through
  `shadow_run`, whose `budget` gives the `Nat` run enough gas for every refill. The deprecated
  forms take reservoir 0 explicitly, as the README says.
- `Nat` truncation. `gas_eq_any`, `gas_ge_any`, `X_gas_any` and `resumeCall_sgm` are additive.
  `X_ok_sgm` assumes `max cost stip ≤ gas`. `ok_X_sgm` keep the T5 conjunct `cost ≤ gas`.
  `dep_X_completeS` keep `preCost + 100 + routeCost ≤ gas`. No gas statement truncates.
- No hypothesis of a new theorem was found to imply `False` (U2). `RunC.out` and `RunC.bad` relate
  any frames, but every consumer pairs `RunC` with `hok` and `EndsOk`, and the statements of
  `dep_X_completeS` are as strong as their prose says.
- T2 to T5. `SendsVia` has the environments and `shouldTransferValue`. `destroy_mirror_runs` and
  `process_step_dep_hyps2` exist. `keepsInvAt_of_acc` exists. Every non-deprecated `ok_X` in
  Usdt/Complete/ has the `cost ≤ gas` conjunct.

**Resolution (round 41).** No change needed. The statements U5 lists are unchanged, except that
the U1 forms now take any starting meter and the U3 runner assumptions ask reservoir 0 of the
caller and the message.

**Resolution note (round 49).** Finding 2 (round 29), T4 (third audit) and U3 (fourth audit)
are about the set `SentVia` of the runner assumptions. Since round 49 that set is EthLib's
`Logic.SentVia` (#1613), and Evm/Keeps.lean is removed. The caller state now reads as the start
state (`ReadsAs`: the same account, storage and transient storage at every address, and the same
code at every code hash) where it had only the same storage and code (`SameView`). The message
conditions are unchanged. The set is smaller, so each runner assumption is implied by its old
form, and each theorem that takes one is at least as strong as before. The conclusions that
exhibit a call of the set (`LocalForward`, `FwdAt`, `EffectD`, `EffectDF`) say more. The
non-vacuity instances under `processRunner` (STOP, `MIRROR`, every reservoir over
`StateGasMeter`) are proved for the new set. On T4: the caller state now has the accounts of the
start state, so the case `KeepsInvNoAcc` covers arises only when the start state has no account
of `C` (`keepsInvAt_of_acc_hasAccount`). U3 is unchanged: the `S` and `SR` forms still ask reservoir 0 of
the caller and the given reservoir of the message.

**Review note (round 49).** The independent review of round 49 found one point. The theorems that
turn a step under `processRunner` into a certificate (`goodCall_process`, `process_step` and its
meter and security forms `process_stepDS`, `process_stepSD`, `process_stepDR`, `process_stepSDR`,
`process_stepSecD`, `process_stepSecDR`, `runOkRS_process`, `runOkRSR_process`) are incomparable
with their round 48 statements: the certificate carries the runner hypothesis as a conjunct, and
both got weaker. The consumers of the certificates got stronger, so every composed result is at
least as strong. Fixed in f66e08b: the one-step theorems `Complete.process_step_inv` (and its
`DS`, `SD`, `DR`, `SDR`, `_start` forms) and `Security.*_processS`, `*_processSR` go from the
round 49 hypotheses on `processRunner` straight to `Inv` or to each security property, and are at
least as strong as the round 48 certificate lemma followed by its consumer. The certificate
lemmas keep their statements, which stay incomparable. T4: `keepsInvAt_of_acc_hasAccount` gives
`KeepsInvAt` from `KeepsInvAcc` alone when the start state has an account of `C`.
A second, fresh independent review of f66e08b: PASS. No headline result is weaker than at round
48, and each old end result about one top-level message was re-derived in Lean from the new
one-step theorems.

**Resolution note (round 50).** No audit finding is about the code changed in round 50, and no
statement of a USDT theorem changed. Evm/Local/Rules.lean is removed: the seven instruction
table entries it held are EthLib's `instruction_of_stackOnlyStep rfl` at each use. The rules over
`StepG` of PUSH, CALLDATALOAD, MSTORE, KECCAK256, SLOAD and RETURN now follow from their forms
over `StepGA`, with the same statements. `At.caller`, `At.stop`, `At.revert`, `At.invalid_fe` and
six unused lemmas with a `runFrame` equation (`low_of_reaches`, `SpecG.low`, `SpecG.halted`,
`SpecG.not_ok`, `not_ok_of_reaches`, `no_ok_stuck`) are removed; each of the six follows from
EthLib's lemma of the same name. The local `At`, `StepG` with `SimAt`, the triples over it and the
opcode rules over the local `At` stay, for the reasons in docs/STATUS.md (round 50). The trust
assumptions of "What is trusted" in docs/RESULTS.md are unchanged.

# Fifth audit (USDT-AUDIT-5)

A fifth independent reviewer, who wrote none of this code, audited the whole state at head
`e548cb7` (rounds 41 to 50 included: exact refill gas over `StateGasMeter`, deprecated paths from
any reservoir, the concrete deprecated runs `S2` and `S3`, the type-4 authorizations, the `RunC`
bridge, and the cleanup rounds 47 to 50 with EthLib's `KeepsOn`, `SentVia` and `ReadsAs`), and
every claim of the public README against the Lean statements. EthLib was read at the pin
`bc16ee428` (the local checkout `../ethlib-usdt-pin7`, clean, an ancestor of `origin/master`) and
not modified. Scratch files lived outside the repository and are not committed. No theorem
statement or README sentence was changed. README replacements were sent to the main session.
Every Lean command ran under `safe.sh -m 9G`. `lake build`: exit 0, 1467 jobs (replayed),
`CODE` 11075 bytes, keccak256 `b44fb4e9…ea55` (also recomputed by `scripts/keccak.py`), 1329
`depends on axioms` entries and 9 `does not depend` entries, none with `sorryAx`.

## Summary

| # | Severity | Finding | Touches |
|---|---|---|---|
| V1 | Low | At any reservoir with refills, the ten owner functions have the exact gas condition only for a call that meets its condition. No theorem says that a successful run meets the condition (only the owner part, `owner_only_any`). The README says every writing function "succeeds exactly when its condition holds" there | README, statements (optional) |
| V2 | Low | No instance of `KeepsInvAtS(R)` and `HonestBalanceAtS(R)` together for one runner and state, and no Sanity file applies any `inv_call_depR`, `process_stepD*` or `_processS*` theorem. The reviewer proved both, and an end-to-end instance of `process_stepDR_inv` in `S2` | Sanity |
| V3 | Low | The type-4 result runs `processMessageCall` over `StateGasMeter` from Paris. EthLib uses that meter only from Glamsterdam. From Prague to BPO5, where type-4 transactions run over `Nat`, no `processMessageCall` theorem exists | README |
| V4 | Low | README: "apart from two entries proved by `rfl`". There are seven local instruction-table lemmas (six by `rfl`, one by `simp`), and many entries come from EthLib's named lemmas, not `instruction_of_stackOnlyStep` | README |
| V5 | Info | Smaller README points: the caller-state set of `KeepsInvAt` is described as "the storage and code" (it is `ReadsAs` since round 49), the `KeepsInvAcc` sentence predates `keepsInvAt_of_acc_hasAccount`, "assumes only" omits `G < 2^255`, and `lakefile.lean` at HEAD uses a local path | README |
| V6 | Info | Checked and found sound (below) | none |

## V1. Owner functions at any reservoir: one direction is missing (Low)

**Evidence.** `pause_sgm`, `unpause_sgm`, `addBlackList_sgm`, `removeBlackList_sgm`,
`transferOwnership_sgm` (Usdt/Refill/OwnerS.lean) and the two-write forms of
Usdt/Refill/ChainOwner.lean (for example `issue_sgm`) take the guard as hypotheses (`hown`,
`hnp`, `hT`, `hB`, `hstatic`, `hacc`, ...) and state `RunsOkS ↔` the gas chain. That is: for a call
that meets its condition, success is exactly the gas condition. The converse, that a successful
run meets the condition, is stated at any reservoir only for `approve`, `transfer` and
`transferFrom` (`ok_approve_any`, `ok_transfer_any`, `ok_transferFrom_any` in Usdt/MeterIff.lean).
For the owner functions it is stated only at reservoir 0 without refills (`X_iff_gas_sgm`, which
takes `hres`), plus the owner check at any reservoir (`owner_only_any`). The README says, for
approve, that "at any reservoir, it succeeds exactly when its condition holds, ..." and then "The
same exact result, at any reservoir with refills allowed, holds for every other writing function
except `transferFrom`", and "So every writing function of USDT has a proved exact success
condition ... at any reservoir and with refills allowed". For the ten owner functions the
success-implies-condition half is not stated. For approve the full iff follows from two theorems
(`ok_approve_any` with `approve_zero_sgm` or `approve_set_sgm`), of which the README cites only the
second.

**The gap is small.** The forward half of `pause_iff_gas_sgm` never uses `hres`. Machine-checked
in scratch (exit 0, axioms `[propext, Classical.choice, Quot.sound]`):

```lean
theorem ok_pause_any (hfork : .berlin ≤ fork) (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x8456cb59)
    (start : At CODE message 0 [] .empty gas state substate (toNat m))
    {within : GasMeter.gasHeld m.gas ≤ bound}
    (hs : Evm.runFrame (step fork) (step_decreases fork) bound runChild m within = .ok s)
    (hok : s.error = none) : PauseGuard state message := by
  obtain ⟨G, hE⟩ := shadow_ends hfork hs hok
  have st' := at_addGas start (budget m)
  obtain ⟨h4, hv, -⟩ := ends_ok_dispatch hfork hsize' st' hE hok
  obtain ⟨hst, hacc, hown, hp, -⟩ := ok_pause hfork hsize' hsel rfl st' hE hok
  exact ⟨⟨h4, hv⟩, ⟨hst, hacc⟩, hown, hp⟩
```

**Suggested fix.** Add `ok_X_any` for the ten owner functions (the first half of each
`X_iff_gas_sgm` with `hres` dropped), or reword the README (replacement sent).

## V2. No joint instance of the deprecated runner assumptions over `StateGasMeter` (Low)

**Evidence.** Deprecated `destroyBlackFunds` over `StateGasMeter` needs `KeepsInvAtS` (or
`KeepsInvAtSR`) and `HonestBalanceAtS` (or `HonestBalanceAtSR`) for the same runner and state
(`inv_call_depS`, `inv_call_depR`, `process_stepDS`, `process_stepDR`, their `_inv` forms). The
repository proves `KeepsInvAtS(R)` for `processRunner` only with `STOP` and `HonestBalanceAtS(R)`
only with `MIRROR` (Sanity/ProcessMeter.lean, ProcessMeterR.lean). `STOP` leaves the output word at
0x60 as it was, so it does not meet `HonestBalanceAtS` in general. No file proves `KeepsInvAtS`
with `MIRROR`, and `grep` finds no Sanity file that applies `process_step_inv`, `process_stepS`,
`process_stepDS`, `process_stepDR`, `inv_callsS`, `inv_call_any`, an `_sgm` theorem, a `dep_X_exactR`
or a `_processS` theorem. The Nat analogue exists (`process_step_dep_hyps2`, `destroy_mirror_inv`).

**Reviewer's instances (scratch, exit 0, axioms `[propext, Classical.choice, Quot.sound]`).**

```lean
theorem keepsInvAtSR_process_mirror (hparis : .paris ≤ fork) {bound : Nat}
    {message : Message fork} {S : State.TransactionState}
    (hcode : S.getCode (S.getAccount (upAddr S message)).codeHash = .ok MIRROR)
    (hnp : Precompiles.isPrecompile fork (upAddr S message).toU256.toNat = false) (r : Nat) :
    KeepsInvAtSR (processRunner (Meter := StateGasMeter) fork bound) message S r
  -- process_mirrorS, then DepInv.inv_congr with storageAt_readSlot

theorem destroy_mirror_stepDR {fork : Fork} (hparis : .paris ≤ fork)
    (b : BlockEnvironment fork) (t : TransactionEnvironment fork) (C : Address) (a : U256)
    (ss : Substate) (H : Hash32) (hH : H ≠ State.EMPTY_CODE_HASH)
    (hnp : Precompiles.isPrecompile fork C.toU256.toNat = false) (G R : Nat)
    (meter : StateGasMeter) (hg : 1000000 ≤ meter.gasLeft) (hg' : meter.gasLeft < 2 ^ 255)
    (held : GasMeter.gasHeld meter ≤ (mDOG b t C a G R).gas)
    (K : SepOn (callKeys (mDOG b t C a G R) (S2 C H a)))
    (h7 : StrForm (storageAt (S2 C H a) C 7)) (h8 : StrForm (storageAt (S2 C H a) C 8)) :
    ∃ ended, processMessage fork (mDOG b t C a G R) (S2 C H a) ss meter held = .ok ended ∧
      ended.1.error = none ∧ Invariant.Inv C ended.1.state
  -- destroy_mirror_processS, inv_S2, and process_stepDR_inv with
  -- keepsInvAtSR_process_mirror and honestBalanceAtSR_process_mirror at meter.reservoir
```

So the hypotheses of `process_stepDR_inv` hold together, under EthLib's runner, at every fork
from Paris (Glamsterdam included) and from any starting meter with enough execution gas, apart
from the keccak hypothesis `SepOn` and the string-slot facts `StrForm` of slots 7 and 8 (both 0 in
`S2` unless a keccak slot of `S2` is 7 or 8). The theorems are not vacuous. The repository does
not show it.

**Suggested fix.** Add the two theorems above to Usdt/Sanity/ (for example MirrorStateS.lean).

## V3. The type-4 result is over the meter EthLib uses from Glamsterdam (Low)

**Evidence.** `destroy_mirror_call_auths` (Usdt/Sanity/MirrorAuth.lean) and `destroy_mirror_callS`
take `.paris ≤ fork` and state `processMessageCall (Meter := StateGasMeter)`. EthLib's
`processTransaction` (Transactions/Process.lean:434-439) runs `runTransaction StateGasMeter` only
for `glamsterdam ≤ fork < hegota` and `runTransaction Nat` before. Type-4 transactions exist from
Prague, so from Prague to BPO5 EthLib runs them with the one-counter meter, and no theorem here
runs `processMessageCall` over `Nat`. The README says "Type-4 calls are covered too" and "From
Paris, for any authorization list ... EthLib's `processMessageCall` of that call over the EIP-8037
meter returns with no error". Both are literally true, but before Glamsterdam they describe a
combination EthLib does not run, and the forks where type-4 transactions are live on mainnet today
are not covered. The same holds for "at every fork from Paris" in the `destroy_mirror_runsS`
sentence, which is less likely to mislead.

**Suggested fix.** Either a `Nat` form of `destroy_mirror_call_auths` before Glamsterdam (the
authorizations keep a `Nat` meter there, `fold_meter_pre`), or the README replacement sent.

## V4. The instruction-table sentence (Low)

**Evidence.** The README says the entries are "proved at each use by EthLib's
`instruction_of_stackOnlyStep`, apart from two entries proved by `rfl`". The repository has seven
local table lemmas: `instruction_extcodesizeS`, `instruction_extcodesizeN`, `instruction_gasN`,
`instruction_gasS` (Evm/StepSim.lean), `instruction_gas'`, `instruction_extcodesize'`
(Evm/Call.lean), all by `rfl`, and `instruction_sstoreM` (Evm/Shadow.lean) by `simp`. It also uses
EthLib's named lemmas `instruction_iszero`, `instruction_add`, `instruction_sub`, `instruction_eq`,
`instruction_sstore`, `instruction_call` and others (EthLib Logic/Rules.lean, Logic/Call.lean).
This does not change what is trusted: all of them are kernel-checked.

**Suggested fix.** README replacement sent.

## V5. Smaller README points (Info)

- Lines on `KeepsInvAt` ("from a caller state with the storage and code of the start state", in
  "How it is done" and in "Every call, deprecated or not"): since round 49 the set is EthLib's
  `SentVia`, whose caller state `ReadsAs` the start state (accounts, storage, transient storage
  and code). The README describes a larger set than the hypothesis asks for, so it overstates the
  burden of the assumption, not the result. The later paragraph of "What you have to trust" is
  right.
- "`KeepsInvAcc` gives `KeepsInv` only together with `KeepsInvNoAcc`": true, but since round 49
  `keepsInvAt_of_acc_hasAccount` gives `KeepsInvAt` from `KeepsInvAcc` alone when the start state
  has an account of `C`.
- "This assumes only that no authorization's delegation code hashes to the code hash of USDT or of
  the upgraded contract": the theorem also takes `G < 2^255`, `C ≠ UA`, `C` no precompile and the
  hash facts of `S3`. The sentence is about the list, so this is Info.
- "Building": `lakefile.lean` at HEAD is `require EthLib from "../ethlib-usdt-pin7"`, a local
  path. That checkout is at `bc16ee428`, clean and an ancestor of `origin/master`. The git pin the
  README describes is that of the published copy (finding 6 of the first audit). The build time
  and memory figures were not re-measured.
- `apply_usdt` and `apply_caller_S3` assume `recoverAuthority auth = some C` (or `CALLER_A`).
  `recoverAuthority` is EthLib's concrete ECDSA recovery, so a witness needs a signature that
  recovers to that address, which nothing here can exhibit. These are illustrations. The headline
  `destroy_mirror_call_auths` takes no hypothesis on recovery, so the README sentence "The list may
  include authorizations whose authority is USDT's address or the caller" is about that theorem and
  is right.

## V6. Checked and found sound (Info)

- **Name resolution of `At`.** A scan of every constant of `UsdtVerify` (scratch meta program):
  8 types mention EthLib's `Logic.At`, all in Evm/At.lean (`At.toLogic`, `At.ofLogic`,
  `At.iff_logic`, `liftPre`, `liftAt`, `lowerPre` and two matchers), and 1352 mention
  `UsdtVerify.At`. No other statement resolves to `Logic.At`. The other local names that EthLib
  also defines and that a file may open together are `Gas.StepG`, `Gas.SpecG`, `Gas.HoareG`,
  `Gas.Stuck` (EthLib's with the extra conjunct `SimAt`, so the local forms are stronger
  triples), `Deprecated.Fails` and `Invariant.Step` (different types, so a swap cannot
  elaborate), and `TransferOk.TRANSFER_TOPIC` (a `U256` equal to keccak of
  `Transfer(address,address,uint256)`, checked in Python). An ambiguous bare name would not
  elaborate, so the build shows each use resolved to one of them, and the scan shows which for
  `At`. No statement changes meaning through resolution.
- **Axioms.** A traversal of every constant of `UsdtVerify` (12842, types and values) reaches only
  `propext`, `Classical.choice` and `Quot.sound`. There is no `opaque` or `axiom` declaration in
  the repository, and no `Lean.ofReduceBool`. `decide +kernel` appears 35 times, on closed facts
  (sizes and bytes of fixed memory images, selectors, `exp` and `mul` of constants, the jump
  destination walk) or a bounded `∀ m < 32`, and the kernel checks each.
- **Fork ranges.** A scan of the 2657 theorems of `UsdtVerify` for hypotheses `F ≤ fork`,
  `fork < F` (and `≥`, `>`) with a constant fork: none has an empty range (1224 have a lower bound,
  16 an upper bound).
- **Numbers.** `authMax = 227790` by `rfl` (183600 + 9000 + 35190, EthLib's
  `NEW_ACCOUNT_STATE_GAS`, `ACCOUNT_WRITE`, `AUTH_BASE_STATE_GAS`). `STORAGE_SET_STATE_GAS = 97920`
  (EthLib `storageSetStateGas_eq`). `TX_MAX_GAS_LIMIT = 16777216`, and `allocateGas` gives
  reservoir 0 for a gas limit of at most 2^24. 1000000 is the hypothesis of every `destroy_mirror`
  theorem cited. 773 and 46 are `spec_unknown` and `spec_short`. 2^180 is the bound of
  `name_long`. 11075 bytes and the hash are checked by Test/Hash.lean.
- **Paths and names.** Every path in the README exists at HEAD (short names are relative to the
  folder named just before). Every theorem and definition named in the README exists, as do the
  13 `X_ok_dom`, 13 `X_gas_any`, 13 `X_iff_gas_sgm`, 7 `dep_X_completeS`, 7 `dep_X_completeR` and
  7 `dep_X_exactR`. `StaticCode` is EthLib's.
- **`KeepsOn`, `SentVia`, `ReadsAs`.** The local definitions `KeepsInvAt`, `KeepsSlots` are
  `KeepsOn` over `SentVia` and `HonestBalanceAt`, `KeepsInvAtS(R)`, `HonestBalanceAtS(R)`,
  `KeepsAtS(R)` quantify over `SentVia` of the `toNat` caller. `ReadsAs` fixes accounts, storage,
  transient storage and code but not the original storage, so the assumptions quantify over caller
  states with any original storage. That makes them harder to meet, not vacuous: the `STOP` and
  `MIRROR` instances hold for all of them, and V2 shows the deprecated hypotheses together.
- **Authorizations.** `hk` (no `delegationCode` hashes to `H` or `HC`) is satisfiable: `H` and
  `HC` are free, and for the real code hashes it is a collision hypothesis on 23-byte inputs.
  `fold_exists` and `destroy_mirror_call_auths` take no hypothesis on `recoverAuthority`.
  `chargeState_ok` and `charge_bound` match EthLib's `chargeAuthorization`
  (Transactions/Authorization.lean:172-182).
- **Refill-exact theorems.** `wOk`, `wMeter`, `sstoreBump` and `sstoreMeter` are explicit
  arithmetic over the meter fields, not defined through a run, and `sgm_sstore_charges` ties them
  to EthLib's `refill`, `charge` and `chargeState`. The truncated `g.gasLeft - P` in `wMeter` is
  guarded by `P + 2301 ≤ g.gasLeft` in the same `wOk`. In `dep_X_exactR` and `dep_destroy_exactR`,
  `gas - preCost - cost` is guarded by the conjunct `preCost + 100 + routeCost ≤ gas`, and the
  CALL's cost is at most the gas left once its extra cost is paid.
- **"Any reservoir".** The `_sgm`, `_ok_dom`, `_gas_any`, `ok_X_any`, `inv_call_any`, security
  `_any`, `dep_X_completeR`, `dep_X_exactR`, `dep_destroy_exactR`, `owner_only_allSR` and the
  `DepMeterR` theorems take no hypothesis `reservoir = 0`. The `= 0` in MeterR.lean and
  DepMeterR.lean are conclusions or conditions on the caller after the CALL, which passes its
  whole reservoir to the callee.
- **`S2` and `S3`.** `inv_S2` uses only `SepOn [kD a]`, whose `fixed`, `uniq` and `list` parts are
  what the proof uses for the five slots of `KD a`. `S3` has the code of `C` and `UA` under free
  hashes, which the model allows, and the README calls it a variant.

**Resolution.** Open. V1 to V5 are recorded for the main session.

**Resolution (round 51).** V1 to V3 are closed by new theorems. No existing statement changed.
- V1: `Exact.ok_X_any` for the ten owner functions (Usdt/MeterOwnerAny.lean): a run over
  `StateGasMeter` at any reservoir, refills allowed, that ends with no error meets the condition of
  the function, with an empty output and the state and substate of `Complete.ok_X`. With the
  exact forms of Usdt/Refill/OwnerS.lean and ChainOwner.lean this gives both directions at any
  reservoir.
- V2: the reviewer's `keepsInvAtSR_process_mirror` and `destroy_mirror_stepDR`, and the joint
  instance `joint_S2_R`, are in Usdt/Sanity/MirrorJointS.lean.
- V3: `destroy_mirror_call_authsN` (Usdt/Sanity/MirrorAuthN.lean): from Paris and before
  Glamsterdam, EthLib's `processMessageCall` over the meter `Nat` of the concrete deprecated call in
  `S3` with any list of authorizations gives an output with no error. It rests on
  `Auth.fold_exists_pre` (Evm/Auth.lean): before Glamsterdam the authorizations of any list
  succeed over any meter, with no hypothesis on `recoverAuthority`.
- V4, V5: about the README, kept outside this repository. Replacement sentences were sent to the
  main session.
Evidence (docs/STATUS.md, round 51): clean rebuild of 2a96c23, exit 0, 1471 jobs; every new
theorem depends on [propext, Classical.choice, Quot.sound]; independent read-only review PASS (no statement changed, 28 constants added, none
removed).
