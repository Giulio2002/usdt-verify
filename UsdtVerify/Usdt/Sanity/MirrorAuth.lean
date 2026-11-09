import UsdtVerify.Usdt.Sanity.MirrorCallS
import UsdtVerify.Evm.Auth

/-!
# Sanity: the concrete deprecated call to USDT with EIP-7702 authorizations (round 46)

`destroy_mirror_callS` (round 45) runs `destroyBlackFunds(a)` from `CALLER_A` to `C` in `S3` through
EthLib's `processMessageCall` over `StateGasMeter` with no authorization. Here the same call is a
set code transaction: it carries a list `auths` of authorizations, which `prepareFirstFrame` applies
before the message (EthLib's `Proofs/Transactions/Authorization.lean`; Evm/Auth.lean).

- `apply_usdt`: an authorization in scope whose recovered authority is `C` is refused, in a state
  where the code of `C` is `CODE`. The delegations get only the read and the access of `C`. For
  `UA` with `MIRROR` the same follows from EthLib's `applyAuthorization_of_code` with
  `code_MIRROR`.
- `apply_fresh`: before Glamsterdam, an authorization in scope with nonce 0 whose recovered
  authority `x` has no account is accepted. The delegations hold the state that `delegate`
  leaves and the access of `x`, and keep the refund and the meter. In that state `x` has nonce 1,
  balance 0 and the hash of `delegationCode auth`. Every other address reads as before, and the
  code under every other hash is kept.
- `apply_caller_S3`: its instance for the first authorization of a list, from the delegations
  `⟨S3, acc, 0, m, pw, ∅⟩`, with authority the caller `CALLER_A`, `CALLER_A ≠ C` and
  `CALLER_A ≠ UA` (so `CALLER_A` has no account in `S3`). In a real transaction the sender's nonce
  is raised before `processMessageCall` (`buyGas`), so `S3` is not the state in which a
  transaction from `CALLER_A` reaches its message; this instance illustrates the lemmas only.
- `prepareFirstFrame_S3`: in `S3`, for any list `auths` whose authorizations end with `.ok done`,
  and such that no `delegationCode` of the list hashes to `H` or `HC`: `prepareFirstFrame` is
  `.ok` of the frame with the code `CODE`, the state `done.state` with the read of `C`, the
  accesses of `done`, the refund of `done` and the meter `commit done.meter`. `done.state` keeps
  the account, the storage and the code of `C` and of `UA`.
- `destroy_mirror_call_auths`: from Paris, in `S3` with the hypotheses of `destroy_mirror_callS`,
  for any list `auths` (no hypothesis on the authorities the signatures give) such that no
  `delegationCode` of the list hashes to `H` or `HC`, any paid writes, any reservoir field and
  substate, and a gas field `G` below 2^255 with at least 1000000 and, from Glamsterdam, 227790
  more per authorization: `processMessageCall` over `StateGasMeter` gives an output with no error.

The hypothesis on `H` and `HC` is a Keccak-256 hypothesis: `setCode` keeps a code under its hash,
so an authorization whose `delegationCode` hashed to `HC` would change the code read at `C`.

Not covered: the transaction around the message (`processTransaction`: the checks of a type-4
transaction, the intrinsic gas, `buyGas`, the sender's nonce, the settlement and the deletions);
anything about the output beyond "no error" (its refund, gas, state, logs and accesses); a call
with value or to a recipient with a delegation indicator; forks before Paris; the error path of
the authorizations in `S3` (the gas hypothesis rules out running out of gas); the recovery of any
concrete signature.
-/

namespace UsdtVerify.Sanity

open EthLib.Base (Fork U256 Address toAddressMasked Hash32)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open EthLib.Execution.Transactions
open EthLib.Execution.State.TransactionState (SameOutside)
open UsdtVerify.Auth
open Complete Deprecated DeprecatedBalance DeprecatedDestroy DestroySpec Owner BlackList
  Transfer TransferOk

variable {fork : Fork}

/-- The code of USDT is not empty and no delegation indicator. -/
theorem code_CODE : (CODE.size = 0 || isValidDelegation CODE) = false := by
  simp [isValidDelegation, size_CODE, CODE_SIZE, DELEGATION_SIZE]

/-- `MIRROR` is not empty and no delegation indicator. -/
theorem code_MIRROR : (MIRROR.size = 0 || isValidDelegation MIRROR) = false := by
  simp [isValidDelegation, size_MIRROR, DELEGATION_SIZE]

theorem getAccount_S3_C (C : Address) (H HC : Hash32) (a : U256) (hCU : C ≠ UA) :
    (S3 C H HC a).getAccount C = ⟨1, 0, HC⟩ := by
  simp [SMc, State.TransactionState.ofBlock, State.TransactionState.getAccount,
    State.TransactionState.getAccountOptional, State.State.getAccountOptional,
    Std.ExtTreeMap.getElem_insert, Std.ExtTreeMap.getElem_insert_self, Ne.symm hCU]

theorem getAccount_S3_UA (C : Address) (H HC : Hash32) (a : U256) :
    (S3 C H HC a).getAccount UA = ⟨1, 0, H⟩ := by
  simp [SMc, State.TransactionState.ofBlock, State.TransactionState.getAccount,
    State.TransactionState.getAccountOptional, State.State.getAccountOptional]

theorem getAccount_S3_other (C : Address) (H HC : Hash32) (a : U256) {x : Address}
    (hC : x ≠ C) (hU : x ≠ UA) : (S3 C H HC a).getAccount x = State.EMPTY_ACCOUNT := by
  simp [SMc, State.TransactionState.ofBlock, State.TransactionState.getAccount,
    State.TransactionState.getAccountOptional, State.State.getAccountOptional, Ne.symm hC,
    Ne.symm hU]

theorem getPreStateAccount_S3 (C : Address) (H HC : Hash32) (a : U256) (x : Address) :
    (S3 C H HC a).getPreStateAccount x = (S3 C H HC a).getAccount x := by
  simp [SMc, State.TransactionState.ofBlock, State.TransactionState.getAccount,
    State.TransactionState.getAccountOptional, State.TransactionState.getPreStateAccount,
    State.TransactionState.getPreStateAccountOptional]

/-- In `S3` every account's code hash has a code. -/
theorem resolves_S3 (C : Address) (H HC : Hash32) (a : U256) (hH : H ≠ State.EMPTY_CODE_HASH)
    (hHC : HC ≠ State.EMPTY_CODE_HASH) (hne : HC ≠ H) (hCU : C ≠ UA) :
    Resolves (S3 C H HC a) := by
  intro x
  by_cases hC : x = C
  · subst hC; exact ⟨_, hcodeC_S3 x H HC a hCU hHC hne⟩
  by_cases hU : x = UA
  · subst hU; exact ⟨_, hcodeU_S3 C H HC a hH⟩
  rw [getAccount_S3_other C H HC a hC hU]
  exact ⟨_, getCode_empty _⟩

theorem preResolves_S3 (C : Address) (H HC : Hash32) (a : U256) (hH : H ≠ State.EMPTY_CODE_HASH)
    (hHC : HC ≠ State.EMPTY_CODE_HASH) (hne : HC ≠ H) (hCU : C ≠ UA) :
    PreResolves (S3 C H HC a) := by
  intro x
  rw [getPreStateAccount_S3]
  exact resolves_S3 C H HC a hH hHC hne hCU x

/-- **An authorization in scope whose authority is USDT's address is refused.** See the module
doc. -/
theorem apply_usdt {Meter : Type} [GasMeter Meter] (chainId : Nat) (done : Delegations Meter)
    {auth : Authorization} {C : Address} (hs : authorizationInScope chainId auth = true)
    (hr : recoverAuthority auth = some C)
    (hcode : done.state.getCode (done.state.getAccount C).codeHash = .ok CODE) :
    applyAuthorization fork chainId done auth = .ok (seen done C) :=
  have h := Bool.or_eq_false_iff.mp code_CODE
  applyAuthorization_of_code hs hr hcode (by simpa using h.1) h.2

/-- Before Glamsterdam, an authorization in scope with nonce 0 whose recovered authority `x` has
no account is accepted: the delegations hold the state of `delegate`, the access of `x` and the
refund as before, and keep the meter. -/
theorem apply_fresh {Meter : Type} [GasMeter Meter] (hf : fork < .glamsterdam) (chainId : Nat)
    (done : Delegations Meter) {auth : Authorization} {x : Address}
    (hs : authorizationInScope chainId auth = true) (hr : recoverAuthority auth = some x)
    (hn : auth.nonce.toNat = 0) (hnone : done.state.getAccountOptional x = none) :
    ∃ st, applyAuthorization fork chainId done auth =
        .ok { done with state := st, accessed := done.accessed.insert x } ∧
      st.getAccount x = ⟨1, 0, hashOf (delegationCode auth)⟩ ∧
      SameOutside [x] done.state st ∧
      ∀ hash : Hash32, hash ≠ hashOf (delegationCode auth) →
        st.getCode hash = done.state.getCode hash := by
  have hA : done.state.getAccount x = State.EMPTY_ACCOUNT := by
    simp [State.TransactionState.getAccount, hnone]
  have hcode : (done.state.recordAccountRead x).getCode State.EMPTY_ACCOUNT.codeHash =
      .ok .empty := getCode_empty _
  have hacc : authorityAccepts (done.state.recordAccountRead x) x auth = .ok true := by
    simp only [authorityAccepts, State.TransactionState.getAccount_recordAccountRead, hA, hcode,
      bind, Except.bind, pure, Except.pure, hn]
    rfl
  have hp := payAuthorization_of_lt_glamsterdam (done := seen done x) (authority := x)
    (auth := auth) hf
  obtain ⟨st, hdel⟩ := delegate_isOk (fork := fork) (authority := x) (auth := auth)
    (done.state.recordAccountRead x)
  have href : (if fork < .glamsterdam ∧ (done.state.recordAccountRead x).accountExists x
      then 12500 else 0) = 0 := by
    simp [State.TransactionState.accountExists, hnone]
  rw [href] at hdel
  refine ⟨st, ?_, ?_, ?_, fun hash hh => getCode_delegate_of_ne hdel hh⟩
  · rw [applyAuthorization_of_accepts_of_pay (done := done) hs hr hacc hp, hdel]
    rfl
  · rw [(delegate_eq_ok hdel).2.1]
    simp only [State.TransactionState.getAccount_recordAccountRead, hA]
    rfl
  · exact ((State.TransactionState.sameOutside_recordAccountRead _ x).trans
      (sameOutside_delegate hdel).1).mono (by simp)

theorem getAccountOptional_S3_other (C : Address) (H HC : Hash32) (a : U256) {x : Address}
    (hC : x ≠ C) (hU : x ≠ UA) : (S3 C H HC a).getAccountOptional x = none := by
  simp [SMc, State.TransactionState.ofBlock, State.TransactionState.getAccountOptional,
    State.State.getAccountOptional, Ne.symm hC, Ne.symm hU]

/-- **The first authorization of a list, from the caller, accepted in `S3`.** See the module doc
for the hypotheses and why this instance only illustrates the lemmas. -/
theorem apply_caller_S3 {Meter : Type} [GasMeter Meter] (hf : fork < .glamsterdam)
    (chainId : Nat) (C : Address) (H HC : Hash32) (a : U256) (acc : Std.ExtTreeSet Address)
    (m : Meter) (pw : Std.ExtTreeSet Address) {auth : Authorization}
    (hs : authorizationInScope chainId auth = true) (hr : recoverAuthority auth = some CALLER_A)
    (hn : auth.nonce.toNat = 0) (hAC : CALLER_A ≠ C) (hAU : CALLER_A ≠ UA) :
    ∃ st, applyAuthorization fork chainId
        (⟨S3 C H HC a, acc, 0, m, pw, ∅⟩ : Delegations Meter) auth =
        .ok ⟨st, acc.insert CALLER_A, 0, m, pw, ∅⟩ ∧
      st.getAccount CALLER_A = ⟨1, 0, hashOf (delegationCode auth)⟩ ∧
      SameOutside [CALLER_A] (S3 C H HC a) st ∧
      ∀ hash : Hash32, hash ≠ hashOf (delegationCode auth) →
        st.getCode hash = (S3 C H HC a).getCode hash :=
  apply_fresh hf chainId _ hs hr hn (getAccountOptional_S3_other C H HC a hAC hAU)

/-- **The first frame of the call in `S3` after any authorizations.** See the module doc. -/
theorem prepareFirstFrame_S3 {Meter : Type} [GasMeter Meter] (b : BlockEnvironment fork)
    (t : TransactionEnvironment fork) (C : Address) (a : U256) (ss : Substate) (H HC : Hash32)
    (hH : H ≠ State.EMPTY_CODE_HASH) (hHC : HC ≠ State.EMPTY_CODE_HASH) (hne : HC ≠ H)
    (hCU : C ≠ UA) (chainId G R : Nat) (auths : List Authorization)
    (pw : Std.ExtTreeSet Address)
    (hk : ∀ auth ∈ auths,
      hashOf (delegationCode auth) ≠ HC ∧ hashOf (delegationCode auth) ≠ H)
    {done : Delegations Meter}
    (hdone : applyAuthorizations fork chainId (S3 C H HC a) ss.accessedAddresses
      (GasMeter.start G R) pw auths = .ok done) :
    prepareFirstFrame (Meter := Meter) chainId (mDOG b t C a G R) (S3 C H HC a) ss auths pw =
      .ok (FirstFrame.ofMeter { mDOG b t C a G R with code := CODE }
        (done.state.recordAccountRead C) { ss with accessedAddresses := done.accessed }
        done.refund (GasMeter.commit done.meter)) ∧
      done.state.getAccountOptional C = (S3 C H HC a).getAccountOptional C ∧
      (∀ key, done.state.getStorage C key = (S3 C H HC a).getStorage C key) ∧
      done.state.getCode (done.state.getAccount C).codeHash = .ok CODE ∧
      done.state.getAccountOptional UA = (S3 C H HC a).getAccountOptional UA ∧
      (∀ key, done.state.getStorage UA key = (S3 C H HC a).getStorage UA key) ∧
      done.state.getCode (done.state.getAccount UA).codeHash = .ok MIRROR := by
  have hfold : auths.foldlM (applyAuthorization fork chainId)
      (⟨S3 C H HC a, ss.accessedAddresses, 0, GasMeter.start G R, pw, ∅⟩ : Delegations Meter) =
      .ok done := hdone
  have hC := Bool.or_eq_false_iff.mp code_CODE
  have hU := Bool.or_eq_false_iff.mp code_MIRROR
  obtain ⟨haC, hsC, -, hcC⟩ := foldlM_applyAuthorization_keeps (address := C)
    (by simpa using hC.1) hC.2 hfold (hcodeC_S3 C H HC a hCU hHC hne)
    (fun auth h => by rw [getAccount_S3_C C H HC a hCU]; exact (hk auth h).1)
  obtain ⟨haU, hsU, -, hcU⟩ := foldlM_applyAuthorization_keeps (address := UA)
    (by simpa using hU.1) hU.2 hfold (hcodeU_S3 C H HC a hH)
    (fun auth h => by rw [getAccount_S3_UA C H HC a]; exact (hk auth h).2)
  have hgC : done.state.getAccount C = (S3 C H HC a).getAccount C := by
    unfold State.TransactionState.getAccount; rw [haC]
  have hgU : done.state.getAccount UA = (S3 C H HC a).getAccount UA := by
    unfold State.TransactionState.getAccount; rw [haU]
  have hcC' : done.state.getCode (done.state.getAccount C).codeHash = .ok CODE := by
    rw [hgC]; exact hcC
  refine ⟨?_, haC, hsC, hcC', haU, hsU, by rw [hgU]; exact hcU⟩
  exact prepareFirstFrame_of_applyAuthorizations (message := mDOG b t C a G R) (substate := ss)
    rfl rfl hdone hcC' (fun _ => delegatedAddress_CODE)

/-- **The concrete deprecated call with authorizations through `processMessageCall`.** See the
module doc. -/
theorem destroy_mirror_call_auths (hparis : .paris ≤ fork)
    (b : BlockEnvironment fork) (t : TransactionEnvironment fork) (C : Address) (a : U256)
    (ss : Substate) (H HC : Hash32) (hH : H ≠ State.EMPTY_CODE_HASH)
    (hHC : HC ≠ State.EMPTY_CODE_HASH) (hne : HC ≠ H) (hCU : C ≠ UA)
    (hnp : Precompiles.isPrecompile fork C.toU256.toNat = false) (chainId : Nat)
    (auths : List Authorization) (pw : Std.ExtTreeSet Address)
    (hk : ∀ auth ∈ auths,
      hashOf (delegationCode auth) ≠ HC ∧ hashOf (delegationCode auth) ≠ H)
    (G R : Nat) (hg : 1000000 + (if fork ≥ .glamsterdam then authMax * auths.length else 0) ≤ G)
    (hg' : G < 2 ^ 255) :
    ∃ out, processMessageCall (Meter := StateGasMeter) chainId (mDOG b t C a G R) (S3 C H HC a) ss
      auths pw = .ok out ∧ out.error = none := by
  obtain ⟨done, hdone, l, u⟩ := foldlM_applyAuthorization_isOk (fork := fork) (chainId := chainId)
    (fun _ => chargesWithin_stateGasMeter) auths
    (start := ⟨S3 C H HC a, ss.accessedAddresses, 0, GasMeter.start G R, pw, ∅⟩)
    (fun hf => by
      simp only [GE.ge, hf, ↓reduceIte] at hg
      show authMax * auths.length ≤ G
      omega)
    (resolves_S3 C H HC a hH hHC hne hCU) (fun _ => preResolves_S3 C H HC a hH hHC hne hCU)
  have hdone' : applyAuthorizations fork chainId (S3 C H HC a) ss.accessedAddresses
      (GasMeter.start G R) pw auths = .ok done := hdone
  have hlo : 1000000 ≤ done.meter.gasLeft := by
    by_cases hf : fork ≥ .glamsterdam
    · simp only [hf, ↓reduceIte] at hg
      have l' : G - authMax * auths.length ≤ done.meter.gasLeft := l
      generalize authMax * auths.length = k at hg l'
      omega
    · have hm := meter_foldlM_applyAuthorization_of_lt_glamsterdam (Nat.lt_of_not_le hf) hdone
      rw [hm]
      show 1000000 ≤ G
      omega
  have hhi : done.meter.gasLeft < 2 ^ 255 := Nat.lt_of_le_of_lt u hg'
  obtain ⟨hff, haC, hsC, -, -, -, hcU⟩ := prepareFirstFrame_S3 (Meter := StateGasMeter) b t C a
    ss H HC hH hHC hne hCU chainId G R auths pw hk hdone'
  obtain ⟨-, hown0, hlist0, -, -, -, -, -, -⟩ := process_step_dep_hyps2 hparis b t C a H hH 0
  have hst : ∀ n, storageAt (done.state.recordAccountRead C) C n = storageAt (S3 C H HC a) C n :=
    fun n => hsC _
  have hacc : hasAccount (done.state.recordAccountRead C) C := by
    simp only [hasAccount, State.TransactionState.getAccountOptional_recordAccountRead, haC]
    exact hasAccount_S3 C H HC a
  have hS10 : storageAt (done.state.recordAccountRead C) C 10 = W := by
    rw [hst]; exact slot10_S2 C H a
  have hcodeU : (done.state.recordAccountRead C).getCode
      ((done.state.recordAccountRead C).getAccount UA).codeHash = .ok MIRROR := hcU
  let G' := GasMeter.gasHeld (GasMeter.commit done.meter : StateGasMeter)
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
  obtain ⟨child, hch, he⟩ := destroy_mirror_processT hparis b t C a
    { ss with accessedAddresses := done.accessed } G' R hS10 hown hlist hcodeU hacc hnp
    (M := { mDOG b t C a G R with code := CODE, gas := G' }) rfl
    (GasMeter.commit done.meter : StateGasMeter) hlo hhi (Nat.le_refl _)
  have ht : (mDOG b t C a G R).target = some C := rfl
  unfold processMessageCall
  rw [hff]
  simp only [FirstFrame.ofMeter, ht]
  rw [hch]
  refine ⟨_, rfl, ?_⟩
  simp [CallOutput.ofFrame, he]

end UsdtVerify.Sanity
