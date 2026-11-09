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

- `At.lean` (round 47): `At`, a running frame of a code with no condition on its return data (EthLib's `At` names the return data since EthLib #1351), its relation to EthLib's `At` (`At.toLogic`, `At.ofLogic`, `liftAt`, `liftPre`, `lowerPre`), and the EthLib rules used directly, for `At` (`At.rule`, `At.extcodesize`, `At.gas_rule`, `At.reshape`, `At.startFrame`, `meets_of_specAt`; round 50: `At.caller`, `At.stop`, `At.revert`, `At.invalid_fe` removed, see the table below).
- `Gas.lean`, `GasRules.lean`: runs with less gas (`StepG`, `HoareG`, `SpecG`), and the opcode rules over `StepG`. Round 48: `addGas`, `Fails`, `Follows`, `RunMono`, `StepFollows`, `Logic.GasMono` and every `runMono_*` fact are EthLib's (Logic/GasMono.lean, Logic/RunMono.lean). The local `StepG` is EthLib's `Logic.StepG` with `SimAt` (the meter link needs it), so `StepG`, `HoareG`, `SpecG`, `At.ruleG` and the rules over the local `At` stay; `HoareG.toLogic`, `SpecG.toLogic` give EthLib's triples. Round 50: `GasRules.lean` also holds `StepGA`, `HoareGA`, `SpecGA`, `At.ruleGA` and the rules of PUSH, MSTORE, CALLDATALOAD, KECCAK256, SLOAD and RETURN over `StepGA` (moved from `NoAbort.lean`), from which their rules over `StepG` follow.
- `Refill.lean` (round 35): where SSTORE refills over the meter `Nat` (`step_store`, `create_gas`, `create2_gas`, `noRefill_cheap`, `noRefill_one`), `StepI` / `HoareI` and the lifts `HoareG.toIA`, `HoareG.toIW`, `sstoreWI`, `noRefill_low`, `ends_of_sgmN`, `sgm_of_reaches`. Round 36: `HoareG.toIW'`, `HoareG.toI1`, `SpecG.toIW'`, `SpecG.toIS`, `getStorage_writeSlot_ne`, `writeCost_le_of_no_create`, `writeCost_le_max`, `exponentBytes_le`.
- `Shadow.lean` (round 35): `SstoreOk`, `sstoreAfter`, `runMono_of_simulated`, `lifts_of_simulated`, `budget`, `shadow_step`, `shadow_run` (a StateGasMeter run followed by a Nat run with more gas), `RunsOkS`, `runFrame_of_specI`, `ends_of_specI`. Round 36: `shadow_step` also relates the gas; `shadow_runQ`, `gas_ge_any`, `gas_eq_any` (the gas at any reservoir); `simAt_low`, `runFrame_of_reachesN`, `runsOk_of_specI` (a StateGasMeter run gives a Nat run).
- `CallMeter.lean` (round 37): CALL over `StateGasMeter`, `callStep_child_rS`, `resumeCall_sgm`, `lifts_gasStep`, `lifts_extcodesizeStep`. Round 41: `callStep_child_res0` (the CALL from reservoir 0 sends reservoir 0).
- `CallSim.lean` (round 38): CALL over both meters from reservoir 0, `callStep_child_sim`, `callStep_deep_sim`, and the failing steps `callStep_low_rS`, `callStep_missingS` (`StepBadS`).
- `StepSim.lean` (round 38): one step over both meters at EXTCODESIZE, GAS and CALL, `SimAtX`, `step_simX`, `CallX`, `CallCorr`, `step_callX`.
- `RunC.lean` (round 39): `Fwd`, `RunC` (a run of the meter `Nat` with an abstract relation for the child), `RunN`, `EndsOk`, `RunC.of_runFrame`, and the lemmas over `RunC` (`low_to_runningC`, `ok_splitC`, `ok_splitCA`, `no_okC`, `RunC.extcodesize`, `RunC.gasOp`, `call_okC`, `CallEndC`).
- `RunCS.lean` (round 39): `RunS`, `resumeCall_withGas`, `runC_of_sgm` (a run over `StateGasMeter` from reservoir 0 gives `RunC`), `endsOk_of_sgm`.
- `NoState.lean` (round 42): `NoStateN`, `NoStateAtN` (an SSTORE that charges no state gas), `noState_cheapE`, `StepJ`, `HoareJ`, `HoareG.toJE`, `HoareG.toJA`, `SpecG.toJA`. Since round 42 `Fwd` (RunC.lean) asks `NoStateAtN`, and the `RunC` lemmas take triples over `StepJ`.
- `StepSimR.lean` (round 42): one step over both meters at any reservoir, `CorrR`, `sim_sstoreStepR`, `sim_of_simulatedR`, `step_simXR`, `CallCorrR`, `step_callXR`. `CallSim.lean` has `callStep_child_simR` and `callStep_deep_simR`.
- `RunCR.lean` (round 42): `RunSR`, `TailQ`, `runC_of_sgmR` (a run over `StateGasMeter` at any reservoir gives `RunC`, with the gas after the CALL). Since round 42 `RunC` has a third parameter, a predicate on the frame after the CALL, and `RunC.lean` has `noRefill_of_specA`.
- `SgmSplit.lean`, `SstoreS.lean`, `OneWrite.lean` (round 42): splitting a run over `StateGasMeter` along `StepJ` triples (`low_to_runningS`, `ok_splitS`, `fwd_reachesJ`), SSTORE over `StateGasMeter` exactly (`sstoreBump`, `sstoreMeter`, `sstoreS_of_cond`, `cond_of_sstoreS`), and a path with one write (`ok_exactS`, `one_write_end`, `one_write_run`, `one_write_sgm`).
- `Chain.lean` (round 43): a path with a chain of writes over `StateGasMeter`, exact at any meter: `ExactS`, `ExactS.run`, `exactS_halt`, `exactS_write`, `wOk`, `wMeter`, `wBump`, `wSgm`, `wMeter_gasLeft`, `getStorage_readSlot`.
- `FwdS.lean` (round 44): a path followed forward over `StateGasMeter` through a CALL, any reservoir: `fwd_splitS`, `fwd_stepS`, `step_callS`, `resumeCall_okS`, `absorb_sum`, `runFrame_childS`, `runFrame_child_fwdS`.
- `Auth.lean` (round 46): the EIP-7702 authorizations of a call, with what `recoverAuthority` returns as hypotheses: one authorization (`apply_out`, `apply_none`, `apply_refused`, `apply_accepted`, `apply_cases`, `delegate_ok`, `pay_pre`, `pay_glam`), an address with code that is no delegation indicator is refused and kept (`apply_code`, `fold_keeps`), the meter before Glamsterdam (`fold_meter_pre`), the first frame after the authorizations (`prepareFirstFrame_auths`), and their success over `StateGasMeter` with no hypothesis on the authorities (`charge_bound`, `apply_exists`, `fold_exists`).
- `Dom.lean` (round 42): a `StepG` run of the meter `Nat` followed over `StateGasMeter` at any reservoir with refills allowed, with at least its gas: `sgm_charges_dom`, `dom_step`, `dom_run`, `runsOkS_of_specG`.
- `Meter.lean` (round 34): the EIP-8037 meter `StateGasMeter` against `Nat`: `toNat`, `lift`, `Lifts` (the instructions that charge only execution gas), `sim_sstoreStep`, `step_sim` (one step, reservoir 0, no refill), `ends_of_sgm` (a run gives `Ends`), `allocateGas_reservoir`. `Gas.lean` holds `simulated`, `SimAt` (in `StepG` and `Stuck` since round 34) and `Ends` with the `E` forms of the primitives (`low_of_reachesE`, `SpecG.lowE`, ...; `Exact.lean` and `Stuck.lean` have `ok_exactE`, `no_okE`, `no_ok_stuckE`, ...). Round 47: `at_startFrameS` (moved from the removed `ProcessMeter.lean`).
- `Stuck.lean`: an SSTORE that cannot complete (static frame, or no account; round 26: at most 2300 gas left from Istanbul, `NoWrite`, `sstore_low_stuck`). Round 48: `Stuck` is EthLib's `Stuck` with `SimAt`; `At.stuck` is EthLib's `At.stuck` for the local `At`; the SSTORE facts under it are EthLib's (`sstoreStep_halts`, `sstoreStep_of_isStatic`, `sstoreStep_of_gasLeft_le`).
- `Storage.lean`, `Write.lean`: slots, reads and writes (`storageAt`, `readSlot`, `writeSlot`, `mapSlot`, `byte20`).
- `Calldata.lean`: the selector and the argument words of the call data.
- `Steps.lean`: `repc`, `restate`, `slotCost` and the tactics `gas_ok`, `stk_ok`, `step`, `at_pc`.
- `Frame.lean`: which slots a change of state may write (`Writes`), and a slot that does not decrease (`NoDec`; round 49: `NoDec.congr_left`, moved from the removed `Keeps.lean`).
- `Keeps.lean`: removed in round 49. The runner assumptions when deprecated are EthLib's `KeepsOn` over EthLib's `SentVia` (the calls the code of `C` actually makes, from a caller state that `ReadsAs` the start state); see the table below.
- `Runners.lean` (round 49: `FromTo C ua`, every message from `C` to `ua`, the set of the removed `Keeps`, and `fromTo_of_sentVia`): two concrete message runners that keep the storage of every account (`stopRunner`: EthLib's `processRunner` on the messages to `ua` that run the one byte STOP, the other messages to `ua` fail; `answerRunner`), and `SameStore`; round 26: a third runner, `answerRunnerAt`, that ends every message in a given state `S` (so it does not keep storage in general); `failRunner`, which fails on every message.
- `Sample.lean`: sample states (`sState`: one account with given slots), messages (`sMsg`), frames (`sFrame`) and call data (`data1`, `data2`), with their lemmas.
- `MemRev.lean`: a read across two adjacent memory writes made in reverse order.
- `Exact.lean`, `Split.lean`: from a specification over `StepG` to every successful run of the interpreter loop.
- `Iff.lean` (round 25): `NoFail` (round 29: `NoFailOn`, the messages of a set; round 30: `fwd_ok_iff_fails` asks the runner hypothesis only of messages from a caller frame meeting a condition `Cl`), `AnsIff`, `runsOk_of_specUnder`, `routes_unique`; round 26: `not_runsOk_stuck`, `iff_max`, `fwd_ok_or_fails`, `fwd_ok_iff_fails` (a path that forwards one message, under a runner that may fail; round 31: `fwd_ok_or_fails` is the one-sided form of `fwd_ok_iff_fails` without `hfail`, which is derived from it; round 27: the forms `fwd_ok_iff` and `fwd_ok_iffQ` for a runner that never fails were removed, `fwd_ok_iff_fails` gives them); `RunsOk` (the interpreter loop ends with no error), `runsOk_iff` (a condition that gives a specification to no error, and that every successful run meets, is equivalent to `RunsOk`), `not_runsOk_low` (no successful run with less gas than the cost of the success path).
- `Route.lean`, `Call.lean`: the route of a CALL (EIP-7702 delegation included; round 48: `Route`, `Routes`, `routeCost`, `routeState`, `routeSub`, `routeAddr`, `routeCode` are EthLib's Logic/Route.lean, and `callStep_child_r` follows from EthLib's `callStep_child_of_routes`), and the EXTCODESIZE, GAS, SUB and CALL steps for any gas and any runner (round 26: `callWithRS`, the CALL rule as a `HoareOn`, EthLib's since round 47; round 30: `CallFrom`, `atCallState`, `atCallSub`, the gas, state and substate of the call a deprecated path makes; round 33: `SendsVia` fixes the block and transaction environments, and `SendsVia.env`; round 49: `sentVia_of_sendsVia`, `sendsVia_of_sentVia` between `SendsVia` and EthLib's `SentVia`, `storageAt_of_readsAs`, `FwdAt` (one call of `SentVia` ended with no error) and `FwdAt.keeps`, and the tactic `reads_as`).
- `Mirror.lean` (round 30): `MIRROR`, a 25-byte contract that answers `balanceOf(a)` with slot `keccak(a ++ 2)` of its own storage; `mirror_spec` (its exact gas) and `process_mirror` (a run under `processRunner` that ends with no error returns that word). Round 31: `mirror_specA` (over `StepGA`) and `process_mirror_iff` (under `processRunner`, at any gas, a frame and never an error; no error exactly when the gas covers the cost).
- `NoAbort.lean` (round 31): `no_error_of_reaches` and `no_error_ga`. Round 50: the steps `StepGA` (a `StepG` step whose failures with less gas only halt the frame; EthLib's `StepGA` with `SimAt`), `HoareGA`, `SpecGA`, `At.ruleGA` and the rules over `StepGA` moved to `GasRules.lean` (round 48: `NoAbort`, `NoAbortLow` and the no-abort facts of the instructions are EthLib's Logic/NoAbort.lean). `no_error_ga` (a `SpecGA` from every gas on gives a loop run that never returns an error, at any gas).
- `Local/`: removed in round 50. Its last file, `Rules.lean` (instruction-table lemmas of LT, GT, DIV, AND, OR, MUL, NOT), is EthLib's `instruction_of_stackOnlyStep rfl` at each use.

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
  `Complete/Deprecated/` for the deprecated paths: `Call` (the steps from EXTCODESIZE on, for `CODE`), `TotalSupply`, `BalanceOf`, `Transfer` (transfer, approve, transferFrom), `Allowance`, `Destroy`. Round 39: each has `dep_X_completeC` (over `RunC`); `Meter.lean` has `dep_X_completeS` (over `StateGasMeter`, reservoir 0). Round 42: `MeterR.lean` has `dep_X_completeR` (over `StateGasMeter`, any reservoir, with the gas after the CALL). Round 44: `CallS.lean` has `fromExtS` (EXTCODESIZE at 4874 to the CALL, forward over `StateGasMeter`) and `DestroyS.lean` has `resumeD` and `dep_destroy_exactR` (deprecated destroyBlackFunds, the exact gas after the CALL, refills included). Round 45: `CallS.lean` has `fromExtSG` (the same at the six sites), `CallExactS.lean` has `resumeG` and `dep_call_exactS` (a forward from EXTCODESIZE to a tail with no write, exactly), and `PathsS.lean` has `dep_X_exactR` for the six other deprecated paths (the exact meter after the CALL and at the end).
- `Meter.lean` (round 34): the results not deprecated over EthLib's EIP-8037 meter: `inv_call_sgm`, `ok_transfer_sgm`, `ok_approve_sgm`, `ok_transferFrom_sgm`. Round 47: `at_startFrameS` (moved from the removed `ProcessMeter.lean`).
- `Refill/Approve.lean`, `Refill/Transfer.lean` (round 35): the success paths of approve and of transfer with a fee of 0 over `StepI` (`spec_zeroI`, `spec_setI`, `bodyI`, `spec_okI`). Round 36: `Refill/Fee.lean` (transfer with a fee above 0: `feeHeadI`, `ownerPartI`, `bodyFeeI`, `spec_feeI`), `Refill/TransferFrom.lean` (`allowStepI`, `bodyFI`, `spec_okFI`, `headFI`, `ownerPartFI`, `bodyFeeFI`, `spec_feeFI`), `Refill/Owner.lean` (the owner functions with two writes: `spec_issueI`, `spec_redeemI`, `spec_setParamsI`, `DestroySpec.specI`).
- `MeterIff.lean` (round 35): `ok_approve_any`, `ok_transfer_any`, `ok_transferFrom_any` (any reservoir), `approve_iff_gas_sgm`, `approve_ok_sgm`, `transfer_iff_gas_sgm`, `transfer_ok_sgm` (reservoir 0, no refill). Round 36: transfer with any fee, `transferFrom_specI`, `transferFrom_ok_sgm`, `transferFrom_iff_gas_sgm`.
- `MeterOwner.lean` (round 36): `X_specI`, `X_ok_sgm`, `X_iff_gas_sgm` for the ten owner functions, through `runsOk_toNat` and the Nat `X_iff_gas`.
- `MeterGas.lean` (round 36): `X_gas_any` for the 13 writing functions (the gas at any reservoir).
- `Refill/ApproveS.lean` (round 42): `approve_zero_sgm`, `approve_set_sgm` (approve over `StateGasMeter`, exact, any reservoir, refills included), `storePre`, `postA`, `preZero`, `preSet`.
- `Refill/OwnerS.lean` (round 43): the owner functions with one write over `StateGasMeter`, exact (`pause_sgm`, `unpause_sgm`, `addBlackList_sgm`, `removeBlackList_sgm`, `list_sgm`, `transferOwnership_sgm`) and their path pieces. `Refill/ChainOwner.lean` (round 43): two writes (`deprecate_sgm`, `issue_sgm`, `redeem_sgm`, `setParams_sgm`, `destroyBlackFunds_sgm`). `Refill/ChainTransfer.lean`, `Refill/ChainFee.lean` (round 43): `transfer_sgm` (fee 0), `transferFee_sgm` (fee above 0). `Refill/TransferFromS.lean` (round 43): `transferFrom_max_sgm`, `transferFrom_sgm`, `transferFromFee_max_sgm`, `transferFromFee_sgm`. `Refill/DestroyDepS.lean` (round 44): the tail of deprecated destroyBlackFunds over `StateGasMeter`, exact (`tailD_sgm`, `zeroToWD`, `tailW1D`, `tailPostD`, `tailDM1`, `tailDM2`).
- `Exact/Approve.lean`, `Exact/Transfer.lean`, `Exact/TransferFrom.lean`, `Exact/Owner.lean` (round 42): `X_ok_dom` for the 13 writing functions (success over `StateGasMeter` at any reservoir, refills allowed, from the threshold of `X_ok_iff`).
- `Invariant/`: `Supply.lean` (the invariant and its effects; the keccak hypotheses `SepOn`, `FixedSep`, `UniqBal`, `NotBal` and the keys of a call `callKeys`, round 29), `Calls.lean` (every successful call, not deprecated), `DeprecatedDestroy.lean`, `All.lean` (deprecated or not; round 33: `keepsInvAt_of_acc`), `Static.lean` (static frames), `Seq.lean` (a finite sequence of calls), `SeqMeter.lean` (round 36: the same over `StateGasMeter`, `inv_call_any`, `CallsS`, `process_stepS`; round 41: any starting meter, and the `_start` corollaries), `DepMeter.lean` (round 39: the deprecated paths over `RunC` and over `StateGasMeter`, `inv_call_depS`, `inv_call_anyD`, `CallsDS`, `process_stepDS`, `process_stepSD`; round 41: any starting meter with reservoir 0, and the `_start` corollaries), `DepMeterR.lean` (round 44: any reservoir when deprecated, `KeepsInvAtSR`, `HonestBalanceAtSR`, `inv_call_depR`, `inv_call_anyDR`, `CallsDR`, `process_stepDR`, `process_stepSDR`). Round 49: `process_step_inv` (Seq.lean), `process_stepDS_inv`, `process_stepSD_inv` and their `_start` forms (DepMeter.lean), `process_stepDR_inv`, `process_stepSDR_inv` (DepMeterR.lean), one top-level message straight to `Inv`; `keepsInvAt_of_acc_hasAccount` (All.lean).

- `Security/`: `Effect.lean` (what every successful call, not deprecated, does to the storage: `Effect`, `effect_call`; the slot classes; the keccak hypothesis `SecSep` and the keyed write class `KeyBA` (round 29); sequences `Seq` and `seq_lift`), `Access.lean` (access control), `Pause.lean` (no balance moves while paused), `Blacklist.lean` (a blacklisted address cannot lower its balance), `Allowance.lean` (transferFrom within the allowance; only approve and transferFrom change allowances), `Supply.lean` (`_totalSupply` changes only through issue, redeem and destroyBlackFunds). Round 37: each file has the `_any` forms over `StateGasMeter` and the `_seqS` forms over `SeqS` (calls over `Nat` or `StateGasMeter`); `Effect.lean` has `effect_localE`, `ends_any`, `effect_any`, `RunOkS`, `SeqS`, `seqS_lift`; `Meter.lean` has `runOkS_process` and `process_stepSec` (round 41: any starting meter, and the `_start` corollaries). Round 39: `DepMeter.lean` has `effect_allS`, `EffectDF` and the `_call_allS` forms over `StateGasMeter` (round 41: `owner_only_allS`). Round 41: `SeqDepMeter.lean` has `RunOkRS`, `SeqRS`, `seqRS_lift`, the `_seq_allS` forms and `process_stepSecD`. Round 44: `DepMeterR.lean` has the same from any reservoir when deprecated (`FwdAtSR`, `KeepsAtSR`, `effect_allSR`, the `_call_allSR` forms, `owner_only_allSR`, `RunOkRSR`, `SeqRSR`, the `_seq_allSR` forms, `process_stepSecDR`). Round 49: `seqRS_process` and the `*_processS` forms (SeqDepMeter.lean), `seqRSR_process` and the `*_processSR` forms (DepMeterR.lean), one top-level message straight to each security property.
  Since round 23 each file also has the forms deprecated or not (`*_call_all`, `*_seq_all`, with the runner assumptions `KeepsSlots`, `KeepsBal`, `KeepsListed`, `KeepsAllow`, `KeepsSupply`); `Effect.lean` has `effect_local`, `EffectD`, `effect_all`, `RunOkR`, `SeqR`, `seqR_lift`; `Access.lean` has `owner_only` and `nonOwner_local`; `Pause.lean` has `transfer_checks_all` and `transferFrom_checks_all`.

- `Exact/` (round 25): exact success conditions. For each function, `X_ok_iff`: with the gas of the success path (the cost, and the stipends of the SSTOREs where the specification asks for them), the run ends with no error if and only if the condition of `Spec/Guards.lean` holds; `X_low`: with less gas than the cost of the success path, no run ends with no error. `Getters.lean`: the 19 functions that only read (name and symbol under `StrForm`; totalSupply, balanceOf and allowance when not deprecated). `Owner.lean`: the ten owner functions (destroyBlackFunds when not deprecated); `X_mid` (round 26) covers a gas between the cost and a stipend bound. `Approve.lean`, `Transfer.lean`, `TransferFrom.lean`: approve, transfer, transferFrom when not deprecated. `Deprecated.lean`: the seven paths that forward when deprecated (`X_dep_ok_iff`, `X_dep_low`), under a runner that never fails (`NoFail`) and whose answer to the forwarded message is given by a condition `A`. Round 26: `X_mid` and `X_iff_gas` (every gas) for the 13 writing functions; `X_dep_ok_iff_gas` (no bound after the CALL) and `X_dep_ok_or_fails` (a runner that may fail, one-sided; round 31: for the seven paths, with the hypotheses of `X_dep_ok_iff_fails` but no `hfail`) for the six forwards other than destroyBlackFunds; then `destroyBlackFunds_dep_ok_iff_gas`, and `X_dep_ok_iff_fails` (an iff for a runner that may fail with any error) for the seven.

- `Sanity/` (round 24): the assumptions of the main theorems hold for some runner, state, message and gas. `Runner.lean`: runners that meet `KeepsSlots`, `KeepsBal`, `KeepsListed`, `KeepsAllow`, `KeepsSupply`, `KeepsInvAt`, `StaticKeeps`, `HonestBalanceAt`. `Transfer.lean`, `Calls.lean`: a state, message and gas where all the hypotheses of `transfer_ok`, `approve_set`, `issue`, `redeem`, `destroyBlackFunds` hold, and the run ends with no error; `TransferFrom.lean` the same for `transferFrom_ok`. `Security.lean`: `OkRun`, witnesses of the non-keccak hypotheses of the security theorems and of `inv_call_all`, and the `_applies` theorems that apply them. `Process.lean` (round 29): EthLib's `processRunner` meets the runner assumptions (`KeepsAt` forms, `NoFailOn` and the `hans` of `X_dep_ok_iff`, with the instance `totalSupply_dep_ok_iff_process_stop`) when the upgraded address holds STOP (round 30: the deprecated exact instances moved to `ProcessExact.lean`, which covers the seven forwards, `X_dep_ok_iff` and `X_dep_ok_iff_gas`, with the gas-aware `hans`). `Mirror.lean` (round 30): `processRunner` meets `HonestBalanceAt` when the upgraded address holds `MIRROR` and its slot mirrors USDT's `balances[a]`. `MirrorExact.lean` (round 31): with `MIRROR` at the upgraded address, `processRunner` meets `NoFailOn` and the gas-aware `hans` of deprecated balanceOf and destroyBlackFunds, with the instances `balanceOf_dep_ok_iff_gas_process_mirror` and `destroyBlackFunds_dep_ok_iff_gas_process_mirror`. `MirrorState.lean` (round 31): `KeepsInvAt` for `MIRROR`, a concrete deprecated state `S1` with `MIRROR` where the hypotheses of the balanceOf instance hold (`balanceOf_mirror_sat`) and where `KeepsInvAt` and `HonestBalanceAt` hold together (`process_step_dep_hyps`). Round 33: a second state `S2` where the caller is the owner, `a` is blacklisted and `balances[a]` is not 0 (`process_step_dep_hyps2`), and a deprecated destroyBlackFunds run there that ends with no error through the CALL (`destroy_mirror_runs`). `ProcessMeter.lean` (round 41): EthLib's runner over `StateGasMeter` meets `KeepsInvAtS` and `KeepsAtS` with STOP at the upgraded address (`keepsInvAtS_process_stop`, `keepsAtS_process_stop`), and `HonestBalanceAtS` with `MIRROR` (`honestBalanceAtS_process_mirror`). `ProcessMeterR.lean` (round 44): the same at every reservoir (`keepsInvAtSR_process_stop`, `keepsAtSR_process_stop`, `honestBalanceAtSR_process_mirror`). `MirrorStateS.lean` (round 44): the call of `destroy_mirror_runs` over `StateGasMeter` under `processRunnerM`, from Paris and any reservoir, ends with no error (`destroy_mirror_runsS`, `process_mirrorS_ok`). Round 45: `MirrorState.lean` gives `S2` `_totalSupply` 1 and proves `Inv` there under `SepOn` of its key (`inv_S2`, `destroy_mirror_inv`); `MirrorStateS.lean` has `mDOG`, `destroy_mirror_runsT`, `destroy_mirror_runsG` and the `processMessage` form `destroy_mirror_processS`; `MirrorCallS.lean` has the state `S3` (`S2` with `CODE` at `C`) and the `processMessageCall` form `destroy_mirror_callS`. Round 46: `MirrorAuth.lean` has the same call with EIP-7702 authorizations: an authority equal to `C` is refused (`apply_usdt`), an authority with no account is accepted before Glamsterdam (`apply_fresh`, `apply_caller_S3`), the first frame in `S3` after any authorizations (`prepareFirstFrame_S3`), and `processMessageCall` with any list of authorizations (`destroy_mirror_call_auths`). `Strings.lean`: the words of "Tether USD" and "USDT" are of `StrForm`, and `inv_call_all`, `supply_call` apply with them in slots 7 and 8. `Exact.lean` (round 25): every `answerRunner` never fails and ends every message with no error (`NoFail`, and `hans` with `A = True` for the six forwards other than destroyBlackFunds); round 26: `answerRunnerAt` meets the `hans` of deprecated destroyBlackFunds, and its ended frames meet the condition of the `hans` of `X_dep_ok_iff_gas` exactly when the gas the CALL keeps covers the tail (`answerRunnerAt_ans_gasD` for destroyBlackFunds, when `S` has an account of `C`); `failRunner` meets `hans` and `hfail` with `A = False`.

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

## Files removed in round 47 (now in EthLib)

| removed | EthLib (pinned at 0c34dc001) |
|---|---|
| Evm/Local/Parent.lean | Execution/Proofs/Evm/Call/Parent.lean (#1597): `parent_processMessage`, `processMessage_sameOutside_of_error`, `getStorage_processMessage_of_error` (was `Local.processMessage_failed_getStorage`) |
| Evm/Local/Extcodesize.lean | `Logic.extcodesize_of_berlin_le` (#1599), used through `At.extcodesize` (Evm/At.lean) |
| Evm/ProcessMeter.lean | `Logic.processRunner`, `processMessage_map_val`, `processMessage_map_val_value` over any lawful meter (#1599, were `processRunnerM`, `processMessage_map_valM`, `processMessage_map_val_valueM`); `at_startFrameS` moved to Evm/Meter.lean |
| Evm/FirstFrame.lean | `Transactions.prepareFirstFrame_of_value_eq_zero` (#1599, was `FirstFrame.prepareFirstFrame_call`) |
| Evm/Sends.lean | Execution/Proofs/Evm/Logic/FailsOn.lean (#1605): `FailsOn` (was `AbortsOn`), `MeetsOk`, `HoareOn`, `SpecOn`, `HoareOn.mono` (was `mono_S`) |
| `Local.instruction_sub` (Evm/Local/Rules.lean) | `Logic.instruction_sub` |

All paths are under `UsdtVerify/`.

## Local copies removed in round 48 (now in EthLib)

No file is removed. The declarations below are removed, and the EthLib ones (pinned at bc16ee428) take their place.

| removed | EthLib |
|---|---|
| `Gas.sh`, `Gas.Fails`, `Gas.Rel`, `Gas.RunMono`, `Gas.RelS`, `Gas.relS_of_rel`, the `*_sh` simp facts | `Logic.addGas`, `Fails`, `Follows`, `RunMono`, `StepFollows`, `Follows.next`, the `*_addGas` simp facts (#1612) |
| `Gas.GasMono`, `Gas.gasMono_of_run`, `Gas.gasMono_of_none` | `SimAt ∧ Logic.GasMono` inside the local `StepG`; `Logic.gasMono_of_run`, `Logic.gasMono_of_none` with `simAt_of`, `simAt_of_none` (#1612) |
| every `Gas.runMono_*`, `rel_map_charge`, `stack_of_chargeGas`, `fails_keepReads`, `chargeGas_sh`, `chargeStateGas_sh`, `popWord_sh`, `popTopics_sh`, and their helpers (Evm/GasRules.lean) | `Logic.runMono_*`, `follows_map_charge`, `stack_of_chargeGas`, `fails_keepReads`, `chargeGas_addGas`, `chargeStateGas_addGas`, `popWord_addGas`, `popTopics_addGas` (#1615) |
| `Gas.NoAbort`, `NoAbort.ok`, `NoAbort.bind`, `NoAbort.map`, the ten `Gas.noAbort_*`, `Gas.NoAbortLow` (Evm/NoAbort.lean) | the same names in `Logic` (#1616) |
| `Gas.sstoreStep_bad`, `Gas.sstoreStep_low` (Evm/Stuck.lean) | `sstoreStep_halts`, `sstoreStep_of_isStatic`, `sstoreStep_of_gasLeft_le`, used through the new local `Gas.At.stuck` |
| `Complete.Route`, `Routes`, `routeAddr`, `routeCode`, `routeCost`, `routeState`, `routeSub`, `routes_congr`, `routes_rec` (Evm/Route.lean) | the same names in `Logic`, `Routes.congr`, `Routes.recordAccountRead` (#1611); `callStep_child_r` is now proved from `callStep_child_of_routes` |

Renamed: `Gas.at_sh` is `Gas.at_addGas`.

## Removed in round 49 (now in EthLib)

`Evm/Keeps.lean` is removed. EthLib's Logic/Keeps.lean (#1613, pinned at bc16ee428) takes its place.

| removed | replacement |
|---|---|
| `SentVia`, `SameView` | `Logic.SentVia`, whose caller state `Logic.ReadsAs` the start state (a smaller set of calls) |
| `KeepsAt runChild message S ua R` | `Logic.KeepsOn runChild (Logic.SentVia message S ua) R` |
| `Keeps runChild C ua R` | `Logic.KeepsOn runChild (FromTo C ua) R` (`FromTo` in Evm/Runners.lean) |
| `KeepsAt.mono`, `Keeps.mono` | `Logic.KeepsOn.mono` |
| `Keeps.at` | `Logic.KeepsOn.mono` with `fromTo_of_sentVia` |
| `FwdAt`, `KeepsAt.fwd` | `FwdAt` over `Logic.SentVia` and `FwdAt.keeps` (Evm/Route.lean) |
| `SameView.refl`, `sameView_recordAccountRead`, `sameView_readSlot`, `sameView_route` | `Logic.ReadsAs.refl`, `recordAccountRead`, `recordStorageRead`, `routeState` (through `reads_as`) |
| `sendsVia_data` | `sentVia_of_sendsVia`, `sendsVia_of_sentVia` (Evm/Route.lean) |
| `Forwarded`, `Keeps.fwd` | unused, not restated |
| `NoDec.congr_left` | moved to Evm/Frame.lean, same statement |

## Removed in round 50

`Evm/Local/Rules.lean` is removed, and `Evm/Local/` with it. The other entries below are declarations.

| removed | replacement |
|---|---|
| `Local.instruction_lt`, `instruction_gt`, `instruction_div`, `instruction_and`, `instruction_or`, `instruction_mul`, `instruction_not` (Evm/Local/Rules.lean) | `Logic.instruction_of_stackOnlyStep rfl` at each use |
| `At.caller`, `At.stop`, `At.revert`, `At.invalid_fe` (Evm/At.lean) | `Gas.callerG`, `Gas.stopG`, `Gas.revertG` with `SpecG.toSpec`, `Gas.invalid_feG`; `liftPre` of `Logic.stop` in Evm/Runners.lean |
| `Gas.push_of_decodeG` (Evm/GasRules.lean) | unused but for `pushG`, which is now `Triple.lift` of `pushGA` |
| `Gas.low_of_reaches`, `Gas.SpecG.low`, `Gas.SpecG.halted`, `Gas.SpecG.not_ok` (Evm/Gas.lean) | unused; `Logic.low_of_reaches`, `Logic.SpecG.low`, `Logic.SpecG.halted`, `Logic.SpecG.not_ok` with `HoareG.toLogic`, `SpecG.toLogic`, `At.toLogic` |
| `Gas.not_ok_of_reaches`, `Gas.no_ok_stuck` (Evm/Stuck.lean) | unused; `Logic.not_ok_of_reaches`, `Logic.no_ok_stuck` with the local `StepG` and `Stuck` without `SimAt` |

Moved: `StepGA`, `HoareGA`, `SpecGA`, `StepLift.stepGA`, `SpecGA.toG`, `SpecGA.toLogic`, `SpecGA.consequence`, `At.ruleGA`, `pushGA`, `calldataloadGA`, `mstoreGA`, `keccak256GA`, `sloadGA`, `returnGA` from Evm/NoAbort.lean to Evm/GasRules.lean, same statements.
