import UsdtVerify.Evm.FirstFrame
import EthLib.Execution.Proofs.State.Frame
import EthLib.Execution.Proofs.State.Tracker

/-!
# The authorizations of a call (round 46)

EthLib's `applyAuthorization` (EIP-7702) recovers the authority of each authorization by ECDSA
public key recovery over a Keccak-256 hash (`recoverAuthority`), which is out of reach for given
signatures here. The statements below take what `recoverAuthority` returns as a hypothesis.

One authorization, with `seen done a` the delegations with the read and the access of `a`:
- `apply_out`, `apply_none`: out of scope, or no authority recovered: the delegations are kept.
- `apply_refused`: an authority `a` that `authorityAccepts` refuses: `seen done a`.
- `apply_accepted`: an authority `a` that it accepts: `payAuthorization` of `seen done a`, then
  the state and the refund of `delegate`.
- `delegate_ok`: `delegate` never fails. Its state sets the account of `a` to its account with the
  code hash of `delegationCode auth` and the nonce one more, reads as before at every other
  address, and keeps the code under every other hash. Its refund is `delegateRefund`.
- `pay_pre`, `pay_glam`: before Glamsterdam `payAuthorization` keeps the delegations; from
  Glamsterdam it sets the meter of `chargeAuthorization`, records the paid write and the
  delegation, and keeps the state, the accesses and the refund.
- `apply_cases`: every successful `applyAuthorization` is one of the cases above.

The list:
- `prepareFirstFrame_auths`: for a call with no value whose authorizations end with `.ok done`, and
  whose recipient `C` has in `done.state` a code `c` that is no delegation indicator (or before
  Pectra): `prepareFirstFrame` is `.ok` of the frame with the code `c`, the state `done.state` with
  the read of `C`, the accesses of `done`, the refund of `done` and the meter `commit done.meter`.
  `prepareFirstFrame_auths_error`: an error of the authorizations is the error of
  `prepareFirstFrame`.
- `fold_keeps`: an address `X` whose code is not empty and no delegation indicator is never an
  accepted authority. When no authorization of the list sets a code with the hash of `X`'s code,
  the authorizations keep the account of `X`, its storage and its code.
- `fold_meter_pre`: before Glamsterdam the authorizations keep the meter.
-/

namespace UsdtVerify.Auth

open EthLib.Base (Fork U256 Address Hash32)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Transactions
open EthLib.Execution.State (TransactionState)
open EthLib.Execution.State.TransactionState (SameOutside)

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-! ## The state -/

/-- The Keccak-256 hash of a code, under which `setCode` keeps it. -/
abbrev hashOf (code : ByteArray) : Hash32 := EthLib.Cryptography.Hash.Keccak.keccak256 code

/-- A change of an account keeps the code under every hash. -/
theorem getCode_modifyState {tx tx' : TransactionState} {address : Address}
    {f : State.Account → Except State.StateError State.Account}
    (h : tx.modifyState fork address f = .ok tx') (hash : Hash32) :
    tx'.getCode hash = tx.getCode hash := by
  obtain ⟨account, -, rfl⟩ := TransactionState.modifyState_eq_ok_iff.mp h
  split <;> rfl

/-- The code under each hash once `v` is kept under `k`. -/
theorem getCode_insert (tx : TransactionState) (k : Hash32) (v : ByteArray) (hash : Hash32) :
    ({ tx with codeWrites := tx.codeWrites.insert k v } : TransactionState).getCode hash =
      if hash = State.EMPTY_CODE_HASH then .ok .empty else if hash = k then .ok v
      else tx.getCode hash := by
  unfold TransactionState.getCode
  by_cases he : hash = State.EMPTY_CODE_HASH
  · simp [he]
  · by_cases hk : hash = k
    · subst hk
      simp [he]
    · simp [he, hk, Std.ExtTreeMap.getElem?_insert, Ne.symm hk]

/-- Setting the code `code` keeps the code under every other hash. -/
theorem getCode_setCode_of_ne {tx tx' : TransactionState} {address : Address} {code : ByteArray}
    (h : tx.setCode fork address code = .ok tx') {hash : Hash32} (hne : hash ≠ hashOf code) :
    tx'.getCode hash = tx.getCode hash := by
  dsimp only [TransactionState.setCode] at h
  split at h
  · exact getCode_modifyState h hash
  · rw [getCode_modifyState h hash]
    refine (getCode_insert tx (hashOf code) code hash).trans ?_
    simp only [hne, ↓reduceIte]
    unfold TransactionState.getCode
    split <;> rfl

/-- Setting the code `code` keeps it under its hash, when that is not the empty code hash. -/
theorem getCode_setCode_self {tx tx' : TransactionState} {address : Address} {code : ByteArray}
    (h : tx.setCode fork address code = .ok tx') (hk : hashOf code ≠ State.EMPTY_CODE_HASH) :
    tx'.getCode (hashOf code) = .ok code := by
  dsimp only [TransactionState.setCode] at h
  split at h
  · exact absurd ‹_› hk
  · rw [getCode_modifyState h]
    refine (getCode_insert tx (hashOf code) code (hashOf code)).trans ?_
    simp only [hk, ↓reduceIte]

/-! ## One authorization -/

/-- The delegations with the read and the access of the authority `a`. -/
abbrev seen (done : Delegations Meter) (a : Address) : Delegations Meter :=
  { done with state := done.state.recordAccountRead a, accessed := done.accessed.insert a }

/-- The refund of `delegate`: 12500 before Glamsterdam for an authority with an account, else 0. -/
def delegateRefund (fork : Fork) (state : TransactionState) (a : Address) : Nat :=
  if fork < .glamsterdam ∧ state.accountExists a then
    GasCosts.AUTH_PER_EMPTY_ACCOUNT - GasCosts.REFUND_AUTH_PER_EXISTING_ACCOUNT else 0

/-- **`delegate` never fails.** See the module doc. -/
theorem delegate_ok (fork : Fork) (state : TransactionState) (a : Address) (auth : Authorization) :
    ∃ st, delegate fork state a auth = .ok (st, delegateRefund fork state a) ∧
      st.getAccount a = { state.getAccount a with
        codeHash := hashOf (delegationCode auth)
        nonce := (state.getAccount a).nonce + 1 } ∧
      SameOutside [a] state st ∧
      (∀ hash : Hash32, hash ≠ hashOf (delegationCode auth) →
        st.getCode hash = state.getCode hash) ∧
      (hashOf (delegationCode auth) ≠ State.EMPTY_CODE_HASH →
        st.getCode (hashOf (delegationCode auth)) = .ok (delegationCode auth)) := by
  obtain ⟨s1, h1⟩ := TransactionState.setCode_isOk fork state a (delegationCode auth)
  obtain ⟨s2, h2⟩ := TransactionState.incrementNonce_isOk fork s1 a
  refine ⟨s2, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [delegate, h1, h2, bind, Except.bind, pure, Except.pure, delegateRefund]
  · rw [(TransactionState.getAccount_incrementNonce h2).1,
      (TransactionState.getAccount_setCode h1).1]
  · exact ((TransactionState.sameOutside_setCode h1).trans
      (TransactionState.sameOutside_incrementNonce h2)).mono (by simp)
  · intro hash hne
    rw [getCode_modifyState h2, getCode_setCode_of_ne h1 hne]
  · intro hk
    rw [getCode_modifyState h2, getCode_setCode_self h1 hk]

/-- Before Glamsterdam, `payAuthorization` keeps the delegations. -/
theorem pay_pre (hf : fork < .glamsterdam) (done : Delegations Meter) (a : Address)
    (auth : Authorization) : payAuthorization fork done a auth = .ok done := by
  simp only [payAuthorization, show ¬fork ≥ .glamsterdam from fun h => Nat.lt_irrefl _
    (Nat.lt_of_lt_of_le hf h), ite_false]

/-- From Glamsterdam, `payAuthorization` sets the meter that `chargeAuthorization` leaves, records
the paid write and the delegation, and keeps the rest. -/
theorem pay_glam (hf : fork ≥ .glamsterdam) {done : Delegations Meter} {a : Address}
    {auth : Authorization} {m : Meter} (hc : chargeAuthorization done a auth = .ok m) :
    payAuthorization fork done a auth = .ok { done with
      meter := m
      paidWrites := done.paidWrites.insert a
      delegated := if auth.address ≠ NULL_ADDRESS then done.delegated.insert a
        else done.delegated } := by
  simp only [payAuthorization, hf, ite_true, hc, bind, Except.bind, pure, Except.pure]

/-- `payAuthorization` keeps the state, the accesses and the refund. -/
theorem pay_keeps {done d : Delegations Meter} {a : Address} {auth : Authorization}
    (h : payAuthorization fork done a auth = .ok d) :
    d.state = done.state ∧ d.accessed = done.accessed ∧ d.refund = done.refund := by
  unfold payAuthorization at h
  split at h
  · cases hc : chargeAuthorization done a auth with
    | error e => simp [hc, bind, Except.bind] at h
    | ok m =>
      simp only [hc, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
      subst h
      exact ⟨rfl, rfl, rfl⟩
  · cases h
    exact ⟨rfl, rfl, rfl⟩

/-- An authorization out of scope keeps the delegations. -/
theorem apply_out (chainId : Nat) (done : Delegations Meter) {auth : Authorization}
    (hs : authorizationInScope chainId auth = false) :
    applyAuthorization fork chainId done auth = .ok done := by
  simp only [applyAuthorization, hs, Bool.false_eq_true, ite_false]

/-- An authorization with no recovered authority keeps the delegations. -/
theorem apply_none (chainId : Nat) (done : Delegations Meter) {auth : Authorization}
    (hr : recoverAuthority auth = none) :
    applyAuthorization fork chainId done auth = .ok done := by
  unfold applyAuthorization
  split <;> simp only [hr]

/-- An authority that `authorityAccepts` refuses: the delegations with its read and access. -/
theorem apply_refused (chainId : Nat) (done : Delegations Meter) {auth : Authorization}
    {a : Address} (hs : authorizationInScope chainId auth = true)
    (hr : recoverAuthority auth = some a)
    (hacc : authorityAccepts (done.state.recordAccountRead a) a auth = .ok false) :
    applyAuthorization fork chainId done auth = .ok (seen done a) := by
  simp only [applyAuthorization, hs, ite_true, hr, hacc, Except.mapError, bind, Except.bind,
    Bool.false_eq_true, ite_false, pure, Except.pure]

/-- An authority that `authorityAccepts` accepts: `payAuthorization`, then `delegate`. -/
theorem apply_accepted (chainId : Nat) (done : Delegations Meter) {auth : Authorization}
    {a : Address} (hs : authorizationInScope chainId auth = true)
    (hr : recoverAuthority auth = some a)
    (hacc : authorityAccepts (done.state.recordAccountRead a) a auth = .ok true)
    {d : Delegations Meter} (hpay : payAuthorization fork (seen done a) a auth = .ok d)
    {st : State.TransactionState} {r : Nat} (hdel : delegate fork d.state a auth = .ok (st, r)) :
    applyAuthorization fork chainId done auth = .ok { d with state := st, refund := d.refund + r } := by
  simp only [applyAuthorization, hs, ite_true, hr, hacc, Except.mapError, bind, Except.bind,
    ite_true, hpay, hdel, pure, Except.pure]

/-- Every successful `applyAuthorization` keeps the delegations, refuses a recovered authority,
or accepts it through `payAuthorization` and `delegate`. -/
theorem apply_cases {chainId : Nat} {done d' : Delegations Meter} {auth : Authorization}
    (h : applyAuthorization fork chainId done auth = .ok d') :
    d' = done ∨ ∃ a, authorizationInScope chainId auth = true ∧ recoverAuthority auth = some a ∧
      ((authorityAccepts (done.state.recordAccountRead a) a auth = .ok false ∧ d' = seen done a) ∨
       (authorityAccepts (done.state.recordAccountRead a) a auth = .ok true ∧
        ∃ d st r, payAuthorization fork (seen done a) a auth = .ok d ∧
          delegate fork d.state a auth = .ok (st, r) ∧
          d' = { d with state := st, refund := d.refund + r })) := by
  cases hs : authorizationInScope chainId auth
  · rw [apply_out chainId done hs] at h
    exact .inl (Except.ok.inj h).symm
  cases hr : recoverAuthority auth with
  | none =>
    rw [apply_none chainId done hr] at h
    exact .inl (Except.ok.inj h).symm
  | some a =>
    refine .inr ⟨a, rfl, rfl, ?_⟩
    cases hacc : authorityAccepts (done.state.recordAccountRead a) a auth with
    | error e =>
      simp [applyAuthorization, hs, hr, hacc, Except.mapError, bind, Except.bind] at h
    | ok b =>
      cases b
      · rw [apply_refused chainId done hs hr hacc] at h
        exact .inl ⟨rfl, (Except.ok.inj h).symm⟩
      · refine .inr ⟨rfl, ?_⟩
        cases hp : payAuthorization fork (seen done a) a auth with
        | error e =>
          simp [applyAuthorization, hs, hr, hacc, hp, Except.mapError, bind, Except.bind] at h
        | ok d =>
          obtain ⟨st, hdel, -⟩ := delegate_ok fork d.state a auth
          rw [apply_accepted chainId done hs hr hacc hp hdel] at h
          exact ⟨d, st, _, rfl, hdel, (Except.ok.inj h).symm⟩

/-- `authorityAccepts` refuses an authority whose code is not empty and no delegation indicator. -/
theorem accepts_code {state : TransactionState} {a : Address} (auth : Authorization)
    {c : ByteArray} (hcode : state.getCode (state.getAccount a).codeHash = .ok c)
    (hc : (c.size = 0 || isValidDelegation c) = false) :
    authorityAccepts (state.recordAccountRead a) a auth = .ok false := by
  have hcode' : (state.recordAccountRead a).getCode
      ((state.recordAccountRead a).getAccount a).codeHash = .ok c := hcode
  simp only [authorityAccepts, hcode', bind, Except.bind, pure, Except.pure, hc, Bool.false_and]

/-- An authority whose code is not empty and no delegation indicator is refused. -/
theorem apply_code (chainId : Nat) (done : Delegations Meter) {auth : Authorization}
    {a : Address} (hs : authorizationInScope chainId auth = true)
    (hr : recoverAuthority auth = some a) {c : ByteArray}
    (hcode : done.state.getCode (done.state.getAccount a).codeHash = .ok c)
    (hc : (c.size = 0 || isValidDelegation c) = false) :
    applyAuthorization fork chainId done auth = .ok (seen done a) :=
  apply_refused chainId done hs hr (accepts_code auth hcode hc)

/-- One authorization keeps an address `X` whose code `c` is not empty and no delegation
indicator, when it sets no code with the hash of `c`: its account, its storage and its code. -/
theorem apply_keeps {chainId : Nat} {done d' : Delegations Meter} {auth : Authorization}
    (h : applyAuthorization fork chainId done auth = .ok d') {X : Address} {c : ByteArray}
    (hcode : done.state.getCode (done.state.getAccount X).codeHash = .ok c)
    (hc : (c.size = 0 || isValidDelegation c) = false)
    (hk : hashOf (delegationCode auth) ≠ (done.state.getAccount X).codeHash) :
    d'.state.getAccountOptional X = done.state.getAccountOptional X ∧
      (∀ key, d'.state.getStorage X key = done.state.getStorage X key) ∧
      d'.state.getCode (done.state.getAccount X).codeHash = .ok c := by
  rcases apply_cases h with rfl | ⟨a, -, -, ⟨-, rfl⟩ | ⟨hacc, d, st, r, hp, hdel, rfl⟩⟩
  · exact ⟨rfl, fun _ => rfl, hcode⟩
  · exact ⟨rfl, fun _ => rfl, hcode⟩
  · have hne : X ≠ a := by
      rintro rfl
      rw [accepts_code auth hcode hc] at hacc
      cases hacc
    obtain ⟨hst, -, -⟩ := pay_keeps hp
    obtain ⟨st', hdel', -, hsame, hcodes, -⟩ := delegate_ok fork d.state a auth
    rw [hdel] at hdel'
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Except.ok.inj hdel')
    obtain ⟨hacc', hstor, -⟩ := hsame X (by simpa using hne)
    refine ⟨?_, fun key => ?_, ?_⟩
    · rw [hacc', hst]; rfl
    · rw [hstor key, hst]; rfl
    · rw [hcodes _ (Ne.symm hk), hst]; exact hcode

/-- **The authorizations keep an address whose code is not empty and no delegation indicator.**
See the module doc. -/
theorem fold_keeps {chainId : Nat} {X : Address} {c : ByteArray}
    (hc : (c.size = 0 || isValidDelegation c) = false) :
    ∀ (auths : List Authorization) (d0 d : Delegations Meter),
      d0.state.getCode (d0.state.getAccount X).codeHash = .ok c →
      (∀ auth ∈ auths, hashOf (delegationCode auth) ≠ (d0.state.getAccount X).codeHash) →
      auths.foldlM (applyAuthorization fork chainId) d0 = .ok d →
      d.state.getAccountOptional X = d0.state.getAccountOptional X ∧
        (∀ key, d.state.getStorage X key = d0.state.getStorage X key) ∧
        d.state.getCode (d0.state.getAccount X).codeHash = .ok c
  | [], d0, d, hcode, _, h => by
    cases h
    exact ⟨rfl, fun _ => rfl, hcode⟩
  | auth :: rest, d0, d, hcode, hk, h => by
    simp only [List.foldlM_cons, bind, Except.bind] at h
    cases h1 : applyAuthorization fork chainId d0 auth with
    | error e => rw [h1] at h; cases h
    | ok d1 =>
      rw [h1] at h
      obtain ⟨ha1, hs1, hc1⟩ := apply_keeps h1 hcode hc (hk auth (List.mem_cons_self ..))
      have hX1 : d1.state.getAccount X = d0.state.getAccount X := by
        unfold TransactionState.getAccount; rw [ha1]
      rw [← hX1] at hc1
      obtain ⟨ha, hs, hc'⟩ := fold_keeps hc rest d1 d hc1
        (fun a ha => hX1 ▸ hk a (List.mem_cons_of_mem _ ha)) h
      exact ⟨ha.trans ha1, fun key => (hs key).trans (hs1 key), hX1 ▸ hc'⟩

/-- Before Glamsterdam, one authorization keeps the meter. -/
theorem apply_meter_pre (hf : fork < .glamsterdam) {chainId : Nat} {done d' : Delegations Meter}
    {auth : Authorization} (h : applyAuthorization fork chainId done auth = .ok d') :
    d'.meter = done.meter := by
  rcases apply_cases h with rfl | ⟨a, -, -, ⟨-, rfl⟩ | ⟨-, d, st, r, hp, -, rfl⟩⟩
  · rfl
  · rfl
  · rw [pay_pre hf] at hp
    cases hp
    rfl

/-- Before Glamsterdam, the authorizations keep the meter. -/
theorem fold_meter_pre (hf : fork < .glamsterdam) {chainId : Nat} :
    ∀ (auths : List Authorization) (d0 d : Delegations Meter),
      auths.foldlM (applyAuthorization fork chainId) d0 = .ok d → d.meter = d0.meter
  | [], d0, d, h => by cases h; rfl
  | auth :: rest, d0, d, h => by
    simp only [List.foldlM_cons, bind, Except.bind] at h
    cases h1 : applyAuthorization fork chainId d0 auth with
    | error e => rw [h1] at h; cases h
    | ok d1 =>
      rw [h1] at h
      exact (fold_meter_pre hf rest d1 d h).trans (apply_meter_pre hf h1)

/-! ## The first frame -/

/-- **The first frame of a call with no value, after its authorizations.** See the module doc. -/
theorem prepareFirstFrame_auths (chainId : Nat) (message : Message fork) (state : TransactionState)
    (substate : Substate) (auths : List Authorization) (paidWrites : Std.ExtTreeSet Address)
    {C : Address} (ht : message.target = some C) (hv : message.value = 0)
    {done : Delegations Meter}
    (hdone : applyAuthorizations fork chainId state substate.accessedAddresses
      (GasMeter.start message.gas message.reservoir) paidWrites auths = .ok done)
    {c : ByteArray} (hc : done.state.getCode (done.state.getAccount C).codeHash = .ok c)
    (hd : fork ≥ .pectra → delegatedAddress c = none) :
    prepareFirstFrame (Meter := Meter) chainId message state substate auths paidWrites =
      .ok (FirstFrame.ofMeter { message with code := c } (done.state.recordAccountRead C)
        { substate with accessedAddresses := done.accessed } done.refund
        (GasMeter.commit done.meter)) := by
  have hc' : (done.state.recordAccountRead C).getCode
      ((done.state.recordAccountRead C).getAccount C).codeHash = .ok c := hc
  have hdel : (if fork ≥ .pectra then delegatedAddress c else none) = none := by
    split
    · exact hd ‹_›
    · rfl
  simp only [prepareFirstFrame, ht, hdone, hv, bind, Except.bind, pure, Except.pure,
    Except.mapError]
  simp only [ne_eq, not_true_eq_false, false_and, and_false, ↓reduceIte]
  simp only [hc', hdel]

/-- An error of the authorizations of a call is the error of its first frame. -/
theorem prepareFirstFrame_auths_error (chainId : Nat) (message : Message fork)
    (state : TransactionState) (substate : Substate) (auths : List Authorization)
    (paidWrites : Std.ExtTreeSet Address) {C : Address} (ht : message.target = some C)
    {e : EvmError × TransactionState}
    (herr : applyAuthorizations fork chainId state substate.accessedAddresses
      (GasMeter.start (Meter := Meter) message.gas message.reservoir) paidWrites auths = .error e) :
    prepareFirstFrame (Meter := Meter) chainId message state substate auths paidWrites =
      .error e := by
  simp only [prepareFirstFrame, ht, herr, bind, Except.bind]

end UsdtVerify.Auth
