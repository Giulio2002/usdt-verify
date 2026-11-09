import UsdtVerify.Usdt.Sanity.MirrorStateS
import EthLib.Execution.Proofs.Transactions.Process

/-!
# Sanity: the concrete deprecated call through `processMessageCall` over the EIP-8037 meter (round 45)

In `S2` the account of `C` has the empty code hash, so EthLib's `processMessageCall`, which takes
the code of the recipient from the state, would not run USDT there. `S3 C H HC a` is `S2 C H a`
with the code `CODE` at `C` under the code hash `HC`: the same storage at `C` and `UA` (`storageAt`
agrees with `S2` by definition), `MIRROR` at `UA` under `H`.

- `destroy_mirror_runsT` (Usdt/Sanity/MirrorStateS.lean) runs the call from any state with the
  facts it needs. `destroy_mirror_processT`: the same as a `processMessage` over `StateGasMeter`,
  from any such state.
- `destroy_mirror_callS`: from Paris (Glamsterdam included), in `S3 C H HC a` with `C ≠ UA`, `C` no
  precompile, `H` and `HC` not the empty code hash and `HC ≠ H`, on any chain, the message
  `destroyBlackFunds(a)` from `CALLER_A` to `C` with any gas field `G` from 1000000 to below 2^255
  and any reservoir field `R`, from any substate, with no authorization and no paid writes (the
  defaults `[]` and `∅`): EthLib's `processMessageCall` over `StateGasMeter` gives an output with
  no error. (The proof takes the first frame from EthLib's `prepareFirstFrame_of_value_eq_zero`.)

Usdt/Sanity/MirrorAuth.lean (round 46) runs the same call with a list of EIP-7702 authorizations
(`destroy_mirror_call_auths`).
-/

namespace UsdtVerify.Sanity

open EthLib.Base (Fork U256 Address toAddressMasked Hash32)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open EthLib.Execution.Transactions
open UsdtVerify.Meter (toNat)
open Complete Deprecated DeprecatedBalance DeprecatedDestroy DestroySpec Owner BlackList
  Transfer TransferOk

variable {fork : Fork}

/-- `SM C H kvs` with the code `CODE` at `C` under the code hash `HC`. -/
def SMc (C : Address) (H HC : Hash32) (kvs : List (U256 × U256)) : State.TransactionState :=
  State.TransactionState.ofBlock
    { preState :=
        { accounts := ((∅ : Std.ExtTreeMap Address State.Account).insert C ⟨1, 0, HC⟩).insert UA
            ⟨1, 0, H⟩
          storage := ((∅ : State.StorageMap).insert C (slotMap kvs)).insert UA (slotMap kvs)
          code := ((∅ : Std.ExtTreeMap Hash32 ByteArray).insert HC CODE).insert H MIRROR }
      accountWrites := ∅
      storageWrites := ∅
      codeWrites := ∅
      storageClears := ∅ }

/-- `S2 C H a` with the code `CODE` at `C` under the code hash `HC`. -/
abbrev S3 (C : Address) (H HC : Hash32) (a : U256) : State.TransactionState := SMc C H HC (KD a)

/-- The storage of `S3` is that of `S2`. -/
theorem storageAt_S3 (C : Address) (H HC : Hash32) (a : U256) (x : Address) (n : U256) :
    storageAt (S3 C H HC a) x n = storageAt (S2 C H a) x n := rfl

theorem hcodeU_S3 (C : Address) (H HC : Hash32) (a : U256) (hH : H ≠ State.EMPTY_CODE_HASH) :
    (S3 C H HC a).getCode ((S3 C H HC a).getAccount UA).codeHash = .ok MIRROR := by
  simp [SMc, State.TransactionState.ofBlock, State.TransactionState.getAccount,
    State.TransactionState.getAccountOptional, State.State.getAccountOptional,
    State.TransactionState.getCode, State.State.getCode, hH]

theorem hcodeC_S3 (C : Address) (H HC : Hash32) (a : U256) (hCU : C ≠ UA)
    (hHC : HC ≠ State.EMPTY_CODE_HASH) (hne : HC ≠ H) :
    (S3 C H HC a).getCode ((S3 C H HC a).getAccount C).codeHash = .ok CODE := by
  simp [SMc, State.TransactionState.ofBlock, State.TransactionState.getAccount,
    State.TransactionState.getAccountOptional, State.State.getAccountOptional,
    State.TransactionState.getCode, State.State.getCode, hHC, Std.ExtTreeMap.getElem?_insert,
    Std.ExtTreeMap.getElem_insert, Std.ExtTreeMap.getElem_insert_self,
    Ne.symm hCU, Ne.symm hne]

theorem hasAccount_S3 (C : Address) (H HC : Hash32) (a : U256) : hasAccount (S3 C H HC a) C := by
  by_cases h : C = UA
  · subst h
    simp [hasAccount, SMc, State.TransactionState.ofBlock,
      State.TransactionState.getAccountOptional, State.State.getAccountOptional]
  · simp [hasAccount, SMc, State.TransactionState.ofBlock,
      State.TransactionState.getAccountOptional, State.State.getAccountOptional, Ne.symm h]

/-- The code of USDT is no delegation indicator. -/
theorem delegatedAddress_CODE : delegatedAddress CODE = none := by
  unfold delegatedAddress
  split
  · rename_i h
    exfalso
    simp [isValidDelegation, size_CODE, CODE_SIZE, DELEGATION_SIZE] at h
  · rfl

/-- **The concrete deprecated run as a `processMessage` from any state with its facts.** From
Paris, with `C` no precompile, the message `M = mDOG b t C a G R`, from a state `S` with the facts
of `destroy_mirror_runsT`, any substate and any starting meter with at least 1000000 and below
2^255 execution gas left (whose held gas is at most `G`): `processMessage` over `StateGasMeter` ends with a frame with no error. -/
theorem destroy_mirror_processT (hparis : .paris ≤ fork)
    (b : BlockEnvironment fork) (t : TransactionEnvironment fork) (C : Address) (a : U256)
    (ss : Substate) (G R : Nat) {S : State.TransactionState} (hS10 : storageAt S C 10 = W)
    (hown : IsOwner S (mDOG b t C a G R))
    (hlist : (storageAt S (mDOG b t C a G R).currentTarget
      (listSlot (addrArg (mDOG b t C a G R).data 0))).toNat % 256 ≠ 0)
    (hcodeU : S.getCode (S.getAccount UA).codeHash = .ok MIRROR) (hacc : hasAccount S C)
    (hnp : Precompiles.isPrecompile fork C.toU256.toNat = false)
    {M : Message fork} (hM : M = mDOG b t C a G R)
    (meter : StateGasMeter) (hg : 1000000 ≤ meter.gasLeft) (hg' : meter.gasLeft < 2 ^ 255)
    (held : GasMeter.gasHeld meter ≤ M.gas) :
    ∃ child, processMessage fork M S ss meter held = .ok child ∧ child.1.error = none := by
  subst hM
  have hst : startState fork (mDOG b t C a G R) S = S := by
    simp only [startState, show ¬fork < Fork.paris from Nat.not_lt.mpr hparis, ite_false]
  have start := Meter.at_startFrameS (code := CODE) (message := mDOG b t C a G R) rfl
    (startState fork (mDOG b t C a G R) S) ss meter
  rw [hst] at start
  obtain ⟨s, hs, hse⟩ := destroy_mirror_runsT hparis G R b t C a ss hS10 hown hlist hcodeU hacc
    (m := startFrame (mDOG b t C a G R) S ss meter) start hg hg' held
  rw [← hst] at hs
  have hpre : precompileAddress fork (mDOG b t C a G R) = none :=
    precompile_none_of (fork := fork) hnp rfl
  have hmap := processMessage_map_val (fun h => h.2 rfl) hpre hs
  rcases hch : processMessage fork (mDOG b t C a G R) S ss meter held with e | child
  · rw [hch] at hmap; cases hmap
  rw [hch] at hmap
  simp only [Except.map, Except.ok.injEq] at hmap
  refine ⟨child, rfl, ?_⟩
  rw [hmap]
  unfold rollbackOnError
  simp [hse]

/-- **The concrete deprecated call through `processMessageCall` over the EIP-8037 meter.** See the
module doc. -/
theorem destroy_mirror_callS (hparis : .paris ≤ fork)
    (b : BlockEnvironment fork) (t : TransactionEnvironment fork) (C : Address) (a : U256)
    (ss : Substate) (H HC : Hash32) (hH : H ≠ State.EMPTY_CODE_HASH)
    (hHC : HC ≠ State.EMPTY_CODE_HASH) (hne : HC ≠ H) (hCU : C ≠ UA)
    (hnp : Precompiles.isPrecompile fork C.toU256.toNat = false) (chainId : Nat)
    (G R : Nat) (hg : 1000000 ≤ G) (hg' : G < 2 ^ 255) :
    ∃ out, processMessageCall (Meter := StateGasMeter) chainId (mDOG b t C a G R) (S3 C H HC a) ss
      = .ok out ∧ out.error = none := by
  obtain ⟨-, hown0, hlist0, -, -, -, -, -, -⟩ := process_step_dep_hyps2 hparis b t C a H hH 0
  have hff := prepareFirstFrame_of_value_eq_zero (Meter := StateGasMeter) (chainId := chainId)
    (message := mDOG b t C a G R) (state := S3 C H HC a) (substate := ss) (paid := ∅)
    (target := C) rfl rfl (hcodeC_S3 C H HC a hCU hHC hne) (fun _ => delegatedAddress_CODE)
  have hacc : hasAccount ((S3 C H HC a).recordAccountRead C) C := by
    simp only [hasAccount, State.TransactionState.getAccountOptional_recordAccountRead]
    exact hasAccount_S3 C H HC a
  obtain ⟨child, hch, he⟩ := destroy_mirror_processT hparis b t C a ss
    (GasMeter.gasHeld (GasMeter.commit (GasMeter.start G R) : StateGasMeter)) R
    (S := (S3 C H HC a).recordAccountRead C) (slot10_S2 C H a) hown0 hlist0
    (hcodeU_S3 C H HC a hH) hacc hnp
    (M := { mDOG b t C a G R with
      code := CODE
      gas := GasMeter.gasHeld (GasMeter.commit (GasMeter.start (mDOG b t C a G R).gas
        (mDOG b t C a G R).reservoir) : StateGasMeter) }) rfl
    (GasMeter.commit (GasMeter.start (mDOG b t C a G R).gas (mDOG b t C a G R).reservoir) :
      StateGasMeter) hg hg' (Nat.le_refl _)
  have ht : (mDOG b t C a G R).target = some C := rfl
  unfold processMessageCall
  rw [hff]
  simp only [FirstFrame.ofMeter, ht]
  rw [hch]
  refine ⟨_, rfl, ?_⟩
  simp [CallOutput.ofFrame, he]

end UsdtVerify.Sanity
