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
