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
- USDT (UsdtVerify/Usdt/Meter.lean): `inv_call_sgm`, `ok_transfer_sgm`, `ok_approve_sgm`,
  `ok_transferFrom_sgm`, with the hypotheses `hres` (reservoir 0) and `hnr` (no SSTORE that the
  steps reach refills). `allocateGas_reservoir`: a transaction gas limit of at most 2^24 gives the
  first frame reservoir 0. Every other `ok_X` applies the same way.
- Still open: `hnr` is a hypothesis about the run, not derived from the call; the deprecated
  paths; a reservoir other than 0; the direction "enough gas gives success" of `X_ok_iff`,
  `X_iff_gas` under `StateGasMeter`; `process_step` / `goodCall_process` at Glamsterdam (their
  `processMessage` still runs over `Nat`).

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
