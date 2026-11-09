import UsdtVerify.Usdt.Sanity.MirrorAuth

/-!
# Sanity: the concrete type-4 call to USDT over the one-counter meter, before Glamsterdam (round 51)

EthLib's `processTransaction` runs a transaction over the meter `Nat` before Glamsterdam and over
`StateGasMeter` from Glamsterdam. Type-4 transactions (EIP-7702) exist from Pectra, so from Pectra
to BPO5 EthLib runs their message with the meter `Nat`. `destroy_mirror_call_auths`
(Usdt/Sanity/MirrorAuth.lean) is over `StateGasMeter`. Here the same call runs over `Nat`, at every
fork from Paris and before Glamsterdam.

- `destroy_tail_bounds`: before Glamsterdam, with at least 1000000 and below 2^255 gas, the CALL of
  deprecated destroyBlackFunds gives `MIRROR` its gas, and the gas after it covers `TAIL_MAX`, at
  every coldness.
- `destroy_mirror_runsN`: from Paris and before Glamsterdam, from any state with the facts of
  `destroy_mirror_runsT` and the slot of `balances[a]` at `UA` equal to that at `C`, the deprecated
  destroyBlackFunds message `mDOG` with gas `G` in [1000000, 2^255) and any substate: the loop of
  the interpreter over `Nat`, with `processRunner` and bound `G`, ends with no error.
- `destroy_mirror_processN`: the same as EthLib's `processMessage` over `Nat`, with `C` no
  precompile, ends with a frame with no error.
- `destroy_mirror_call_authsN`: from Paris and before Glamsterdam, in `S3` with the hypotheses of
  `destroy_mirror_call_auths`, for any list `auths` (no hypothesis on the authorities the
  signatures give) such that no `delegationCode` of the list hashes to `H` or `HC`, any paid
  writes, any reservoir field and substate, and a gas field `G` in [1000000, 2^255):
  `processMessageCall` over `Nat` gives an output with no error.

Not covered, as in Usdt/Sanity/MirrorAuth.lean: the transaction around the message
(`processTransaction`), anything about the output beyond "no error", and the recovery of any
concrete signature.
-/

namespace UsdtVerify.Sanity

open EthLib.Base (Fork U256 Address toAddressMasked Hash32)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open EthLib.Execution.Transactions
open UsdtVerify.Auth
open Complete Deprecated DeprecatedBalance DeprecatedDestroy DestroySpec Owner BlackList
  Transfer TransferOk Exact

variable {fork : Fork}

/-- **The gas of the forward and of the tail, before Glamsterdam.** With `G` gas in
[1000000, 2^255), at every coldness: the CALL of deprecated destroyBlackFunds gives at least
`mirrorCost cM`, and the gas after it, with what `MIRROR` returns, covers `TAIL_MAX`. -/
theorem destroy_tail_bounds (hberlin : .berlin ≤ fork) (hglam : fork < .glamsterdam) {G : Nat}
    (hg : 1000000 ≤ G) (hg' : G < 2 ^ 255) {c0 cL c10 cU cM : Bool} :
    mirrorCost cM ≤ (callGasD fork G c0 cL c10 cU 0).subCall ∧
    TAIL_MAX fork ≤ G - preCostD fork c0 cL c10 cU - (callGasD fork G c0 cL c10 cU 0).cost +
      ((callGasD fork G c0 cL c10 cU 0).subCall - mirrorCost cM) := by
  have hp : 1500 + slotCost c0 + slotCost cL + slotCost c10 + extCost fork cU ≤ 10400 :=
    preCostD_le hberlin hglam c0 cL c10 cU
  have e : askedOfD fork G c0 cL c10 cU = asked (G - preCostD fork c0 cL c10 cU + 3) := by
    show asked (G - (1497 + slotCost c0 + slotCost cL + slotCost c10 + extCost fork cU)) =
      asked (G - (1500 + slotCost c0 + slotCost cL + slotCost c10 + extCost fork cU) + 3)
    congr 1
    omega
  have hc : callGasD fork G c0 cL c10 cU 0 = depCallGas fork
      (asked (G - preCostD fork c0 cL c10 cU + 3)) (G - preCostD fork c0 cL c10 cU) 0 := by
    show messageCallGas fork 0 (askedOfD fork G c0 cL c10 cU).toNat _ 0 (100 + 0) = _
    rw [e]
  have hp' : preCostD fork c0 cL c10 cU ≤ 10400 := hp
  obtain ⟨h1, h2, h3⟩ := callGas_bounds hberlin (G := G - preCostD fork c0 cL c10 cU)
    (by omega) (by omega)
  have hm : mirrorCost cM ≤ 2187 := by
    have := slotCost_le cM
    show 87 + slotCost cM ≤ 2187
    omega
  rw [hc, TAIL_MAX_of_lt hglam]
  generalize (depCallGas fork (asked (G - preCostD fork c0 cL c10 cU + 3))
    (G - preCostD fork c0 cL c10 cU) 0).subCall = sc at h1 h2 h3 ⊢
  generalize preCostD fork c0 cL c10 cU = pc at hp' h1 h2 h3 ⊢
  generalize mirrorCost cM = mc at hm ⊢
  rw [h2]
  omega

/-- **The concrete deprecated run over the meter `Nat`, at any gas from 1000000.** See the module
doc. -/
theorem destroy_mirror_runsN (hparis : .paris ≤ fork) (hglam : fork < .glamsterdam) (G R : Nat)
    (b : BlockEnvironment fork) (t : TransactionEnvironment fork) (C : Address) (a : U256)
    (ss : Substate) {S : State.TransactionState} (hS10 : storageAt S C 10 = W)
    (hown : IsOwner S (mDOG b t C a G R))
    (hlist : (storageAt S (mDOG b t C a G R).currentTarget
      (listSlot (addrArg (mDOG b t C a G R).data 0))).toNat % 256 ≠ 0)
    (hcodeU : S.getCode (S.getAccount UA).codeHash = .ok MIRROR) (hacc : hasAccount S C)
    (hmir : storageAt S UA (balSlot (mDOG b t C a G R)) =
      storageAt S C (balSlot (mDOG b t C a G R)))
    (hg : 1000000 ≤ G) (hg' : G < 2 ^ 255) :
    RunsOk fork G (processRunner fork G) (sFrame (mDOG b t C a G R) S ss G) (Nat.le_refl _) := by
  have hberlin : .berlin ≤ fork := Nat.le_trans (by decide) hparis
  have hdep : byte20 (storageAt S (mDOG b t C a G R).currentTarget 10) ≠ 0 := by
    show byte20 (storageAt S C 10) ≠ 0
    rw [hS10]; decide
  have hup : upAddr S (mDOG b t C a G R) = UA := by
    show toAddressMasked (upWord (storageAt S C 10)) = UA
    rw [hS10]; rfl
  have hc : S.getCode (S.getAccount (upAddr S (mDOG b t C a G R))).codeHash = .ok MIRROR := by
    rw [hup]; exact hcodeU
  have hR : ∀ A, routeCost fork A (none : Route) = 0 := fun _ => rfl
  have h := destroyBlackFunds_dep_ok_iff_gas_process_mirror (fork := fork)
    (message := mDOG b t C a G R) (state := S) (substate := ss) (gas := G) (bound := G) hparis
    (by show (data1 SEL_D a).size < 2 ^ 256; rw [size_data1 size_SEL_D]; decide)
    (by show selector (data1 SEL_D a) = _; rw [selector_data1 size_SEL_D]; decide)
    hdep hc (r := none) (fun _ => delegatedAddress_mirror) rfl rfl rfl rfl
    (at_sFrame (mDOG b t C a G R) rfl _ _ _) (Nat.le_refl _)
    (by rw [hup]; exact hnp_UA fork)
    (by
      simp only [callRD, hR]
      have := preCostD_le hberlin hglam (coldIn ss (mDOG b t C a G R).currentTarget 0)
        (coldIn (accessSlot ss (mDOG b t C a G R).currentTarget 0)
          (mDOG b t C a G R).currentTarget (listSlot (addrArg (mDOG b t C a G R).data 0)))
        (coldIn (preSub ss (mDOG b t C a G R)) (mDOG b t C a G R).currentTarget 10)
        (decide (upAddr S (mDOG b t C a G R) ∉ ss.accessedAddresses))
      omega)
    (by rw [hup]; exact hmir)
  simp only [callRD, hR] at h
  refine h.mpr ⟨⟨⟨⟨?_, rfl⟩, by rw [size_MIRROR]; decide,
      show 0 + 1 ≤ STACK_DEPTH_LIMIT by decide⟩, hown, hlist, rfl⟩,
    (destroy_tail_bounds hberlin hglam hg hg').1, ?_,
    Nat.le_trans (tail_le_max hberlin _ _ _ _ _ _) (destroy_tail_bounds hberlin hglam hg hg').2⟩
  · show 4 ≤ (data1 SEL_D a).size
    rw [size_data1 size_SEL_D]; decide
  · have h0 : hasAccount (readSlot (preState S (mDOG b t C a G R)) C 10) C :=
      hasAccount_readSlot (hasAccount_readSlot (hasAccount_readSlot hacc))
    simp only [atCallState, callStateD, routeState, hasAccount,
      State.TransactionState.getAccountOptional_recordAccountRead]
    exact h0

/-- **The concrete deprecated run as a `processMessage` over the meter `Nat`.** From Paris and
before Glamsterdam, with `C` no precompile, the message `M = mDOG b t C a G R` with `G` in
[1000000, 2^255), from a state `S` with the facts of `destroy_mirror_runsN`, any substate and the
meter `G`: `processMessage` over `Nat` ends with a frame with no error. -/
theorem destroy_mirror_processN (hparis : .paris ≤ fork) (hglam : fork < .glamsterdam)
    (b : BlockEnvironment fork) (t : TransactionEnvironment fork) (C : Address) (a : U256)
    (ss : Substate) (G R : Nat) {S : State.TransactionState} (hS10 : storageAt S C 10 = W)
    (hown : IsOwner S (mDOG b t C a G R))
    (hlist : (storageAt S (mDOG b t C a G R).currentTarget
      (listSlot (addrArg (mDOG b t C a G R).data 0))).toNat % 256 ≠ 0)
    (hcodeU : S.getCode (S.getAccount UA).codeHash = .ok MIRROR) (hacc : hasAccount S C)
    (hmir : storageAt S UA (balSlot (mDOG b t C a G R)) =
      storageAt S C (balSlot (mDOG b t C a G R)))
    (hnp : Precompiles.isPrecompile fork C.toU256.toNat = false)
    {M : Message fork} (hM : M = mDOG b t C a G R) (meter : Nat) (hmeter : meter = G)
    (held : GasMeter.gasHeld meter ≤ M.gas) (hg : 1000000 ≤ G) (hg' : G < 2 ^ 255) :
    ∃ child, processMessage fork M S ss meter held = .ok child ∧ child.1.error = none := by
  subst hM hmeter
  have hst : startState fork (mDOG b t C a meter R) S = S := by
    simp only [startState, show ¬fork < Fork.paris from Nat.not_lt.mpr hparis, ite_false]
  obtain ⟨s, hs, hse⟩ := destroy_mirror_runsN hparis hglam meter R b t C a ss hS10 hown hlist
    hcodeU hacc hmir hg hg'
  have hs' : Evm.runFrame (step fork) (step_decreases fork) (mDOG b t C a meter R).gas
      (processRunner fork (mDOG b t C a meter R).gas)
      (startFrame (mDOG b t C a meter R) (startState fork (mDOG b t C a meter R) S) ss meter)
      held = .ok s := by
    rw [hst]; exact hs
  have hpre : precompileAddress fork (mDOG b t C a meter R) = none :=
    precompile_none_of (fork := fork) hnp rfl
  have hmap := processMessage_map_val (fun h => h.2 rfl) hpre hs'
  rcases hch : processMessage fork (mDOG b t C a meter R) S ss meter held with e | child
  · rw [hch] at hmap; cases hmap
  rw [hch] at hmap
  simp only [Except.map, Except.ok.injEq] at hmap
  refine ⟨child, rfl, ?_⟩
  rw [hmap]
  unfold rollbackOnError
  simp [hse]

/-- **The concrete deprecated call with authorizations through `processMessageCall` over the meter
`Nat`, from Paris and before Glamsterdam.** See the module doc. -/
theorem destroy_mirror_call_authsN (hparis : .paris ≤ fork) (hglam : fork < .glamsterdam)
    (b : BlockEnvironment fork) (t : TransactionEnvironment fork) (C : Address) (a : U256)
    (ss : Substate) (H HC : Hash32) (hH : H ≠ State.EMPTY_CODE_HASH)
    (hHC : HC ≠ State.EMPTY_CODE_HASH) (hne : HC ≠ H) (hCU : C ≠ UA)
    (hnp : Precompiles.isPrecompile fork C.toU256.toNat = false) (chainId : Nat)
    (auths : List Authorization) (pw : Std.ExtTreeSet Address)
    (hk : ∀ auth ∈ auths,
      hashOf (delegationCode auth) ≠ HC ∧ hashOf (delegationCode auth) ≠ H)
    (G R : Nat) (hg : 1000000 ≤ G) (hg' : G < 2 ^ 255) :
    ∃ out, processMessageCall (Meter := Nat) chainId (mDOG b t C a G R) (S3 C H HC a) ss
      auths pw = .ok out ∧ out.error = none := by
  obtain ⟨done, hdone⟩ := fold_exists_pre (fork := fork) (Meter := Nat) hglam (chainId := chainId)
    auths ⟨S3 C H HC a, ss.accessedAddresses, 0, GasMeter.start G R, pw, ∅⟩
    (resolves_S3 C H HC a hH hHC hne hCU) (preResolves_S3 C H HC a hH hHC hne hCU)
  have hdone' : applyAuthorizations fork chainId (S3 C H HC a) ss.accessedAddresses
      (GasMeter.start G R) pw auths = .ok done := hdone
  have hm : done.meter = G := fold_meter_pre hglam auths _ done hdone
  obtain ⟨hff, haC, hsC, -, -, hsU, hcU⟩ := prepareFirstFrame_S3 (Meter := Nat) b t C a
    ss H HC hH hHC hne hCU chainId G R auths pw hk hdone'
  obtain ⟨-, hown0, hlist0, -, -, -, -, -, -⟩ := process_step_dep_hyps2 hparis b t C a H hH 0
  have hst : ∀ n, storageAt (done.state.recordAccountRead C) C n = storageAt (S3 C H HC a) C n :=
    fun n => hsC _
  have hstU : ∀ n, storageAt (done.state.recordAccountRead C) UA n =
      storageAt (S3 C H HC a) UA n := fun n => hsU _
  have hacc : hasAccount (done.state.recordAccountRead C) C := by
    simp only [hasAccount, State.TransactionState.getAccountOptional_recordAccountRead, haC]
    exact hasAccount_S3 C H HC a
  have hS10 : storageAt (done.state.recordAccountRead C) C 10 = W := by
    rw [hst]; exact slot10_S2 C H a
  have hcodeU : (done.state.recordAccountRead C).getCode
      ((done.state.recordAccountRead C).getAccount UA).codeHash = .ok MIRROR := hcU
  let G' := GasMeter.gasHeld (GasMeter.commit done.meter : Nat)
  have hG' : G' = G := hm
  have hown : IsOwner (done.state.recordAccountRead C) (mDOG b t C a G' R) := by
    have h0 : IsOwner (S3 C H HC a) (mDOG b t C a G' R) := hown0
    unfold IsOwner ownerOf at h0 ⊢
    rw [show (mDOG b t C a G' R).currentTarget = C from rfl, hst]
    exact h0
  have hlist : (storageAt (done.state.recordAccountRead C) (mDOG b t C a G' R).currentTarget
      (listSlot (addrArg (mDOG b t C a G' R).data 0))).toNat % 256 ≠ 0 := by
    have h0 : (storageAt (S3 C H HC a) (mDOG b t C a G' R).currentTarget
        (listSlot (addrArg (mDOG b t C a G' R).data 0))).toNat % 256 ≠ 0 := hlist0
    rw [show (mDOG b t C a G' R).currentTarget = C from rfl, hst]
    exact h0
  have hmir : storageAt (done.state.recordAccountRead C) UA (balSlot (mDOG b t C a G' R)) =
      storageAt (done.state.recordAccountRead C) C (balSlot (mDOG b t C a G' R)) := by
    rw [hstU, hst, storageAt_S3, storageAt_S3, storageAt_S2 C H a UA (.inr rfl),
      storageAt_S2 C H a C (.inl rfl)]
  obtain ⟨child, hch, he⟩ := destroy_mirror_processN hparis hglam b t C a
    { ss with accessedAddresses := done.accessed } G' R hS10 hown hlist hcodeU hacc hmir hnp
    (M := { mDOG b t C a G R with code := CODE, gas := G' }) rfl
    (GasMeter.commit done.meter : Nat) rfl (Nat.le_refl _) (hG' ▸ hg) (hG' ▸ hg')
  have ht : (mDOG b t C a G R).target = some C := rfl
  unfold processMessageCall
  rw [hff]
  simp only [FirstFrame.ofMeter, ht]
  rw [hch]
  refine ⟨_, rfl, ?_⟩
  simp [CallOutput.ofFrame, he]

end UsdtVerify.Sanity
