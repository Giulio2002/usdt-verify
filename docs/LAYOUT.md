# Layout of the Lean sources

Where to look:

- What a USDT function does: `UsdtVerify/Usdt/Spec/<Function>.lean`.
- The block-by-block proofs behind it: `UsdtVerify/Usdt/Proofs/<Function>.lean`.
- That the specification covers every successful run (any gas): `UsdtVerify/Usdt/Complete/`.
- When each function succeeds, exactly (with the gas of its success path): the conditions in `UsdtVerify/Usdt/Spec/Guards.lean`, the theorems in `UsdtVerify/Usdt/Exact/`.
- The supply invariant: `UsdtVerify/Usdt/Invariant/`.
- The security properties (access control, pause, blacklist, allowances, supply): `UsdtVerify/Usdt/Security/`.
- Lemmas about the EVM that hold for every code: `UsdtVerify/Evm/`.
- That the assumptions of the main theorems can hold together (non-vacuity): `UsdtVerify/Usdt/Sanity/`.
- One index of the main theorems, with aliases: `UsdtVerify/Summary.lean`.

## Folders

`UsdtVerify/Evm/` holds what is not specific to USDT.
No file there imports a file outside `Evm/`.

- `Gas.lean`, `GasRules.lean`: runs with less gas (`StepG`, `HoareG`, `SpecG`), and the opcode rules over `StepG`.
- `Refill.lean` (round 35): where SSTORE refills over the meter `Nat` (`step_store`, `create_gas`, `create2_gas`, `noRefill_cheap`, `noRefill_one`), `StepI` / `HoareI` and the lifts `HoareG.toIA`, `HoareG.toIW`, `sstoreWI`, `noRefill_low`, `ends_of_sgmN`, `sgm_of_reaches`.
- `Shadow.lean` (round 35): `SstoreOk`, `sstoreAfter`, `runMono_of_simulated`, `lifts_of_simulated`, `budget`, `shadow_step`, `shadow_run` (a StateGasMeter run followed by a Nat run with more gas), `RunsOkS`, `runFrame_of_specI`, `ends_of_specI`.
- `Meter.lean` (round 34): the EIP-8037 meter `StateGasMeter` against `Nat`: `toNat`, `lift`, `Lifts` (the instructions that charge only execution gas), `sim_sstoreStep`, `step_sim` (one step, reservoir 0, no refill), `ends_of_sgm` (a run gives `Ends`), `allocateGas_reservoir`. `Gas.lean` holds `simulated`, `SimAt` (in `GasMono` and `Stuck` since round 34) and `Ends` with the `E` forms of the primitives (`low_of_reachesE`, `SpecG.lowE`, ...; `Exact.lean` and `Stuck.lean` have `ok_exactE`, `no_okE`, `no_ok_stuckE`, ...).
- `Stuck.lean`: an SSTORE that cannot complete (static frame, or no account; round 26: at most 2300 gas left from Istanbul, `NoWrite`, `sstore_low_stuck`).
- `Storage.lean`, `Write.lean`: slots, reads and writes (`storageAt`, `readSlot`, `writeSlot`, `mapSlot`, `byte20`).
- `Calldata.lean`: the selector and the argument words of the call data.
- `Steps.lean`: `repc`, `restate`, `slotCost` and the tactics `gas_ok`, `stk_ok`, `step`, `at_pc`.
- `Frame.lean`: which slots a change of state may write (`Writes`), and a slot that does not decrease (`NoDec`).
- `Keeps.lean`: a call from one account to another that a message runner ends with no error (`Forwarded`), and a relation the runner keeps over such calls (`Keeps`); round 29: `SameView`, `SentVia` (the calls the code of `C` actually makes), `KeepsAt` and `FwdAt`, the form of the runner assumptions when deprecated.
- `Runners.lean`: two concrete message runners that keep the storage of every account (`stopRunner`: EthLib's `processRunner` on the messages to `ua` that run the one byte STOP, the other messages to `ua` fail; `answerRunner`), and `SameStore`; round 26: a third runner, `answerRunnerAt`, that ends every message in a given state `S` (so it does not keep storage in general); `failRunner`, which fails on every message.
- `Sample.lean`: sample states (`sState`: one account with given slots), messages (`sMsg`), frames (`sFrame`) and call data (`data1`, `data2`), with their lemmas.
- `Sends.lean` (round 26): triples under a runner that may fail with any error, whose runs end in the postcondition or at a failure on a message of a given set (`HoareOn`, `SpecOn`, `toUnder`).
- `MemRev.lean`: a read across two adjacent memory writes made in reverse order.
- `Exact.lean`, `Split.lean`: from a specification over `StepG` to every successful run of the interpreter loop.
- `Iff.lean` (round 25): `NoFail` (round 29: `NoFailOn`, the messages of a set; round 30: `fwd_ok_iff_fails` asks the runner hypothesis only of messages from a caller frame meeting a condition `Cl`), `AnsIff`, `runsOk_of_specUnder`, `routes_unique`; round 26: `not_runsOk_stuck`, `iff_max`, `fwd_ok_or_fails`, `fwd_ok_iff_fails` (a path that forwards one message, under a runner that may fail; round 31: `fwd_ok_or_fails` is the one-sided form of `fwd_ok_iff_fails` without `hfail`, which is derived from it; round 27: the forms `fwd_ok_iff` and `fwd_ok_iffQ` for a runner that never fails were removed, `fwd_ok_iff_fails` gives them); `RunsOk` (the interpreter loop ends with no error), `runsOk_iff` (a condition that gives a specification to no error, and that every successful run meets, is equivalent to `RunsOk`), `not_runsOk_low` (no successful run with less gas than the cost of the success path).
- `Route.lean`, `Call.lean`: the route of a CALL (EIP-7702 delegation included), and the EXTCODESIZE, GAS, SUB and CALL steps for any gas and any runner (round 26: `callWithRS`, the CALL rule as a `Sends.HoareOn`; round 30: `CallFrom`, `atCallState`, `atCallSub`, the gas, state and substate of the call a deprecated path makes; round 33: `SendsVia` fixes the block and transaction environments, and `SendsVia.env`).
- `Mirror.lean` (round 30): `MIRROR`, a 25-byte contract that answers `balanceOf(a)` with slot `keccak(a ++ 2)` of its own storage; `mirror_spec` (its exact gas) and `process_mirror` (a run under `processRunner` that ends with no error returns that word). Round 31: `mirror_specA` (over `StepGA`) and `process_mirror_iff` (under `processRunner`, at any gas, a frame and never an error; no error exactly when the gas covers the cost).
- `NoAbort.lean` (round 31): `NoAbort` (a result that is no error aborting the run), the no-abort facts of PUSH, MSTORE, CALLDATALOAD, KECCAK256, SLOAD, RETURN, the steps `StepGA` (a `StepG` step whose failures with less gas only halt the frame), `HoareGA`, `SpecGA`, `At.ruleGA` and the rules of those six opcodes over it, and `no_error_ga` (a `SpecGA` from every gas on gives a loop run that never returns an error, at any gas).
- `Local/`: generic rules missing from EthLib at the pinned commit: `Rules.lean` (instruction-table lemmas of LT, GT, DIV, AND, OR, SUB, MUL, NOT), `Extcodesize.lean` (EXTCODESIZE at every fork from Berlin), `Parent.lean` (every message keeps the block of the state; a message that `processMessage` ends with an error keeps the storage).

`UsdtVerify/Usdt/` holds what is about the deployed bytecode.

- `Code.lean`, `Code/Bytes.lean`: the bytecode `CODE` (generated by `scripts/gen_code.py`) and its byte lemmas.
- `Steps.lean`: the tactics that step through `CODE` (`code_fact`, `valid_dest`, `pushR`, `binR`, `jumpiR`, ...).
- `Map.lean`: the prelude, the selector table and `dispatch`; its header lists the storage layout of TetherToken.
- `Spec/`: one file per function or small family, with the specifications from pc 0 (`spec_*`, `runFrame_*`) and the reverts and failed asserts:
  `TotalSupply`, `BalanceOf`, `Transfer`, `Approve`, `TransferFrom`, `Pause` (pause, unpause), `BlackList` (addBlackList, removeBlackList), `Issue` (issue, redeem), `SetParams`, `AddrWrite` (deprecate, transferOwnership), `Destroy` (destroyBlackFunds), `Getters`, `Strings` (name, symbol).
  `Spec/Deprecated/` holds the forwards to the upgraded contract: `TotalSupply`, `BalanceOf`, `Transfer` (transfer and approve), `TransferFrom`, `Allowance`, `Destroy` (destroyBlackFunds).
  `Spec/Dispatch.lean` holds the nonpayable revert and the fallback; `Spec/RunFrames.lean` the `runFrame` wrappers that lacked one.
  `Spec/Guards.lean` (round 25) states, for each function, the condition under which it succeeds, in plain terms (`CallOk`, ...).
- `Proofs/`: the blocks that the specifications compose: `Common`, `SafeMath`, `Owner` (the `onlyOwner` check), `Admin` (blocks of the owner functions), then `Transfer`, `TransferFrom`, `Approve`, `Pause`, `BlackList`, `Issue`, `SetParams`, `AddrWrite`; `Fee.lean` is the fee path shared by transfer and transferFrom.
  No file in `Proofs/` imports a file in `Spec/`.
- `Complete/`: completeness, every successful run with any gas follows the specification: `Dispatch` (the dispatcher), `Read` (totalSupply, balanceOf), `Transfer`, `Approve`, `TransferFrom`, `Owner` (the ten owner functions), `Getters` (the getters, name and symbol).
  `Complete/Deprecated/` for the deprecated paths: `Call` (the steps from EXTCODESIZE on, for `CODE`), `TotalSupply`, `BalanceOf`, `Transfer` (transfer, approve, transferFrom), `Allowance`, `Destroy`.
- `Meter.lean` (round 34): the results not deprecated over EthLib's EIP-8037 meter: `inv_call_sgm`, `ok_transfer_sgm`, `ok_approve_sgm`, `ok_transferFrom_sgm`.
- `Refill/Approve.lean`, `Refill/Transfer.lean` (round 35): the success paths of approve and of transfer with a fee of 0 over `StepI` (`spec_zeroI`, `spec_setI`, `bodyI`, `spec_okI`).
- `MeterIff.lean` (round 35): `ok_approve_any`, `ok_transfer_any`, `ok_transferFrom_any` (any reservoir), `approve_iff_gas_sgm`, `approve_ok_sgm`, `transfer_iff_gas_sgm`, `transfer_ok_sgm` (reservoir 0, no refill).
- `Invariant/`: `Supply.lean` (the invariant and its effects; the keccak hypotheses `SepOn`, `FixedSep`, `UniqBal`, `NotBal` and the keys of a call `callKeys`, round 29), `Calls.lean` (every successful call, not deprecated), `DeprecatedDestroy.lean`, `All.lean` (deprecated or not; round 33: `keepsInvAt_of_acc`), `Static.lean` (static frames), `Seq.lean` (a finite sequence of calls).

- `Security/`: `Effect.lean` (what every successful call, not deprecated, does to the storage: `Effect`, `effect_call`; the slot classes; the keccak hypothesis `SecSep` and the keyed write class `KeyBA` (round 29); sequences `Seq` and `seq_lift`), `Access.lean` (access control), `Pause.lean` (no balance moves while paused), `Blacklist.lean` (a blacklisted address cannot lower its balance), `Allowance.lean` (transferFrom within the allowance; only approve and transferFrom change allowances), `Supply.lean` (`_totalSupply` changes only through issue, redeem and destroyBlackFunds).
  Since round 23 each file also has the forms deprecated or not (`*_call_all`, `*_seq_all`, with the runner assumptions `KeepsSlots`, `KeepsBal`, `KeepsListed`, `KeepsAllow`, `KeepsSupply`); `Effect.lean` has `effect_local`, `EffectD`, `effect_all`, `RunOkR`, `SeqR`, `seqR_lift`; `Access.lean` has `owner_only` and `nonOwner_local`; `Pause.lean` has `transfer_checks_all` and `transferFrom_checks_all`.

- `Exact/` (round 25): exact success conditions. For each function, `X_ok_iff`: with the gas of the success path (the cost, and the stipends of the SSTOREs where the specification asks for them), the run ends with no error if and only if the condition of `Spec/Guards.lean` holds; `X_low`: with less gas than the cost of the success path, no run ends with no error. `Getters.lean`: the 19 functions that only read (name and symbol under `StrForm`; totalSupply, balanceOf and allowance when not deprecated). `Owner.lean`: the ten owner functions (destroyBlackFunds when not deprecated); `X_mid` (round 26) covers a gas between the cost and a stipend bound. `Approve.lean`, `Transfer.lean`, `TransferFrom.lean`: approve, transfer, transferFrom when not deprecated. `Deprecated.lean`: the seven paths that forward when deprecated (`X_dep_ok_iff`, `X_dep_low`), under a runner that never fails (`NoFail`) and whose answer to the forwarded message is given by a condition `A`. Round 26: `X_mid` and `X_iff_gas` (every gas) for the 13 writing functions; `X_dep_ok_iff_gas` (no bound after the CALL) and `X_dep_ok_or_fails` (a runner that may fail, one-sided; round 31: for the seven paths, with the hypotheses of `X_dep_ok_iff_fails` but no `hfail`) for the six forwards other than destroyBlackFunds; then `destroyBlackFunds_dep_ok_iff_gas`, and `X_dep_ok_iff_fails` (an iff for a runner that may fail with any error) for the seven.

- `Sanity/` (round 24): the assumptions of the main theorems hold for some runner, state, message and gas. `Runner.lean`: runners that meet `KeepsSlots`, `KeepsBal`, `KeepsListed`, `KeepsAllow`, `KeepsSupply`, `KeepsInvAt`, `StaticKeeps`, `HonestBalanceAt`. `Transfer.lean`, `Calls.lean`: a state, message and gas where all the hypotheses of `transfer_ok`, `approve_set`, `issue`, `redeem`, `destroyBlackFunds` hold, and the run ends with no error; `TransferFrom.lean` the same for `transferFrom_ok`. `Security.lean`: `OkRun`, witnesses of the non-keccak hypotheses of the security theorems and of `inv_call_all`, and the `_applies` theorems that apply them. `Process.lean` (round 29): EthLib's `processRunner` meets the runner assumptions (`KeepsAt` forms, `NoFailOn` and the `hans` of `X_dep_ok_iff`, with the instance `totalSupply_dep_ok_iff_process_stop`) when the upgraded address holds STOP (round 30: the deprecated exact instances moved to `ProcessExact.lean`, which covers the seven forwards, `X_dep_ok_iff` and `X_dep_ok_iff_gas`, with the gas-aware `hans`). `Mirror.lean` (round 30): `processRunner` meets `HonestBalanceAt` when the upgraded address holds `MIRROR` and its slot mirrors USDT's `balances[a]`. `MirrorExact.lean` (round 31): with `MIRROR` at the upgraded address, `processRunner` meets `NoFailOn` and the gas-aware `hans` of deprecated balanceOf and destroyBlackFunds, with the instances `balanceOf_dep_ok_iff_gas_process_mirror` and `destroyBlackFunds_dep_ok_iff_gas_process_mirror`. `MirrorState.lean` (round 31): `KeepsInvAt` for `MIRROR`, a concrete deprecated state `S1` with `MIRROR` where the hypotheses of the balanceOf instance hold (`balanceOf_mirror_sat`) and where `KeepsInvAt` and `HonestBalanceAt` hold together (`process_step_dep_hyps`). Round 33: a second state `S2` where the caller is the owner, `a` is blacklisted and `balances[a]` is not 0 (`process_step_dep_hyps2`), and a deprecated destroyBlackFunds run there that ends with no error through the CALL (`destroy_mirror_runs`). `Strings.lean`: the words of "Tether USD" and "USDT" are of `StrForm`, and `inv_call_all`, `supply_call` apply with them in slots 7 and 8. `Exact.lean` (round 25): every `answerRunner` never fails and ends every message with no error (`NoFail`, and `hans` with `A = True` for the six forwards other than destroyBlackFunds); round 26: `answerRunnerAt` meets the `hans` of deprecated destroyBlackFunds, and its ended frames meet the condition of the `hans` of `X_dep_ok_iff_gas` exactly when the gas the CALL keeps covers the tail (`answerRunnerAt_ans_gasD` for destroyBlackFunds, when `S` has an account of `C`); `failRunner` meets `hans` and `hfail` with `A = False`.

`UsdtVerify/Summary.lean`: the index of the main theorems, with aliases. `UsdtVerify.lean` imports every module.

`UsdtVerify/Test/`: `Hash.lean` (the build checks that `CODE` is the bytes of `data/usdt.runtime.hex` with the recorded keccak256) and `Axioms.lean` (`#print axioms` of the main theorems).

Outside `UsdtVerify/`: `data/` (the runtime bytecode `usdt.runtime.hex` and its provenance `SOURCE.md`), `scripts/` (`gen_code.py` writes `Usdt/Code/Bytes.lean`, `keccak.py` the hash of `Test/Hash.lean`, `disasm.py` and `map.py` the disassembly and `docs/MAP.md`), `docs/` (`RESULTS.md`, `STATUS.md`, this file, `MAP.md`).

## Names

- Block lemmas (`Proofs/`, and the blocks inside `Spec/` and `Complete/`) are named after the code
  block they cover, in lowerCamelCase (`bodyFee`, `hashTail`, `creditStore`); most are over `StepG`
  already, and a suffix `G` marks the `StepG` form where a `Step` form of the same block also
  exists (`okTailAG`, `midG`, `prefixG_*`); `Bad`, `Low`, `Mid` mark the forms that fail.
- Path theorems from pc 0: `spec_*` (a `SpecG` or `Spec`) and `runFrame_*` (the same for the
  interpreter loop). Completeness: `ok_*` (not deprecated) and `dep_*_complete` (deprecated).
  Exact conditions: `X_ok_iff`, `X_low`, `X_mid`, `X_iff_gas`, `X_dep_ok_iff`, `X_dep_low`,
  `X_dep_ok_iff_gas`, `X_dep_ok_iff_fails`, `X_dep_ok_or_fails`.
- `Summary.lean` gives the per-function theorems aliases in the form `function_case`
  (`transfer_ok`, `approve_dep_complete`, `destroyBlackFunds_dep_noCode`; `runFrame_function_case`
  for the loop forms) and cites the exact, security and invariant theorems by their full names.

A file made of several older files keeps each one in its own `section`, under its own header.
Theorem names did not change: the namespaces are those of the older files (for example `UsdtVerify.TransferOk.spec_ok` is in `Usdt/Spec/Transfer.lean`, `UsdtVerify.Complete.ok_split` in `Evm/Split.lean`).

## Old path to new path (round 21)

| old | new |
|---|---|
| Code.lean, Code/Bytes.lean | Usdt/Code.lean, Usdt/Code/Bytes.lean |
| Steps.lean | Evm/Steps.lean (generic) and Usdt/Steps.lean (the `CODE` tactics) |
| Dispatch.lean, Table.lean | Usdt/Map.lean |
| Gas.lean | Evm/Gas.lean |
| GasRules.lean, GasRules2.lean | Evm/GasRules.lean |
| Stuck.lean | Evm/Stuck.lean |
| Spec/Storage.lean, Spec/Write.lean, Spec/Calldata.lean | Evm/Storage.lean, Evm/Write.lean, Evm/Calldata.lean |
| Local/Rules.lean, Local/Parent.lean, Local/Extcodesize.lean | Evm/Local/ (same names) |
| Functions/MemRev.lean | Evm/MemRev.lean |
| Functions/Route.lean | Evm/Route.lean |
| Complete/Exact.lean | Evm/Exact.lean |
| Complete/Split.lean | Evm/Split.lean; `prefixG_totalSupply`, `dep_totalSupply_split` to Usdt/Complete/Deprecated/TotalSupply.lean |
| Complete/DepCall.lean | Evm/Call.lean (the steps for any gas and runner); `midG`, `noCodeG`, `subG`, `fromExt_found`, `fromExt` to Usdt/Complete/Deprecated/Call.lean |
| Functions/Common.lean | Usdt/Proofs/Common.lean |
| Functions/SafeMath.lean | Usdt/Proofs/SafeMath.lean |
| Functions/Owner.lean | Usdt/Proofs/Owner.lean |
| Functions/Transfer.lean | the blocks to Usdt/Proofs/Transfer.lean; `spec_paused`, `spec_blacklisted`, `spec_short` (with their `runFrame_*`, costs and states) to Usdt/Spec/Transfer.lean |
| Functions/TransferOk.lean, Functions/TransferBody.lean | Usdt/Proofs/Transfer.lean |
| Functions/TransferSuccess.lean, TransferFault.lean, TransferFeeSpec.lean, TransferFaults.lean | Usdt/Spec/Transfer.lean |
| Functions/TransferFrom.lean, TransferFromBody.lean | Usdt/Proofs/TransferFrom.lean |
| Functions/TransferFee.lean, TransferFeeBody.lean, TransferFromFee.lean | Usdt/Proofs/Fee.lean |
| Functions/TransferFromSpec.lean, TransferFromFault.lean, TransferFromFeeSpec.lean, TransferFromFault2.lean | Usdt/Spec/TransferFrom.lean |
| Functions/Approve.lean | Usdt/Proofs/Approve.lean |
| Functions/ApproveSpec.lean, ApproveRevert.lean | Usdt/Spec/Approve.lean |
| Functions/TotalSupply.lean, BalanceOf.lean | Usdt/Spec/TotalSupply.lean, Usdt/Spec/BalanceOf.lean |
| Functions/Nonpayable.lean, Fallback.lean | Usdt/Spec/Dispatch.lean |
| Functions/Pause.lean, Admin.lean, BlackList.lean, Issue.lean, SetParams.lean, AddrWrite.lean | Usdt/Proofs/ (same names) |
| Functions/PauseSpec.lean, BlackListSpec.lean, IssueSpec.lean, AddrWriteSpec.lean | Usdt/Spec/Pause.lean, BlackList.lean, Issue.lean, AddrWrite.lean |
| Functions/SetParamsSpec.lean, SetParamsFault.lean | Usdt/Spec/SetParams.lean |
| Functions/Destroy.lean, DestroySpec.lean | Usdt/Spec/Destroy.lean |
| Functions/Getters.lean, GettersMap.lean | Usdt/Spec/Getters.lean |
| Functions/Strings.lean, StringsGen.lean | Usdt/Spec/Strings.lean |
| Functions/RunFrames.lean | Usdt/Spec/RunFrames.lean |
| Functions/Deprecated.lean | Usdt/Spec/Deprecated/TotalSupply.lean |
| Functions/DeprecatedBalance.lean, DeprecatedTransfer.lean, DeprecatedTransferFrom.lean, DeprecatedAllowance.lean, DeprecatedDestroy.lean | Usdt/Spec/Deprecated/BalanceOf.lean, Transfer.lean, TransferFrom.lean, Allowance.lean, Destroy.lean |
| Complete/Dispatch.lean, Read.lean, Transfer.lean, TransferFrom.lean, Approve.lean, Owner.lean, Getters.lean | Usdt/Complete/ (same names) |
| Complete/DepTotalSupply.lean, DepBalance.lean, DepTransfer.lean, DepAllowance.lean, DepDestroy.lean | Usdt/Complete/Deprecated/TotalSupply.lean, BalanceOf.lean, Transfer.lean, Allowance.lean, Destroy.lean |
| Invariant.lean | Usdt/Invariant/Supply.lean |
| Complete/Inv.lean, DepInv.lean, DepInvAll.lean, Static.lean, Seq.lean | Usdt/Invariant/Calls.lean, DeprecatedDestroy.lean, All.lean, Static.lean, Seq.lean |
| Summary.lean, Test/Hash.lean, Test/Axioms.lean | unchanged |

All paths are under `UsdtVerify/`.
