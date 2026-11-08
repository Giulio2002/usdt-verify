import UsdtVerify.Usdt.Security.Blacklist

/-!
# Allowances: transferFrom stays within the allowance; only approve and transferFrom change one

The allowance of `spender` over the tokens of `owner` is the slot `allowed[owner][spender]`,
`keccak(spender ++ keccak(owner ++ 5))`. For transferFrom(f, t, v) the code reads
`allowed[f][caller]` (`allowFrom message f`).

- `transferFrom_bound`: every successful transferFrom (not deprecated; any call data below 2^256
  bytes, any value, any gas, static or not), with `A` the allowance `allowed[f][caller]` at the
  start: `A = MAX_UINT` or `v ≤ A`; `balances[f]` falls by at most `v`; when `A ≠ MAX_UINT` the
  allowance at the end is `A - v` (so `balances[f]` falls by at most what the allowance falls),
  and when `A = MAX_UINT` the allowance is still `MAX_UINT`. Under `SepOn` of the call's keys.
- `Effect.allowKept` / `allowKept_call`: a successful call (not deprecated) whose selector is
  neither approve nor transferFrom keeps the slot of `allowed` keyed by `y` and `z`, for any words
  `y`, `z`, under `SecSep` of the call's keys and `y`, `z` (round 29: one slot at a time; through
  round 28 every slot at once, under `KeccakSep` and `AllowSep`).
- `allowKept_seq`: along a finite sequence of such calls (each not deprecated, slots 7 and 8 of
  `StrForm`, `SecSep` of its keys and `y`, `z`, at its own start state) and of `Untouched` steps,
  that slot keeps its word.

Deprecated or not (round 23): `allowKept_call_all` and `allowKept_seq_all`, when deprecated with
the runner assumption `KeepsAllow` (a call to the upgraded address keeps every slot of `allowed`
of `C`). transferFrom and approve forward when deprecated, so `transferFrom_bound` has no
deprecated form.
-/

namespace UsdtVerify.Security

open EthLib.Base (Fork U256 Address)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open Deprecated
open Invariant Complete Owner Approve Transfer TransferOk TransferFee TransferFrom

/-- Every slot of `allowed` keeps its word (the form of the runner assumption `KeepsAllow`). -/
def AllowKept (C : Address) (S S' : State.TransactionState) : Prop :=
  ∀ y z : U256, storageAt S' C (mapSlot y (mapSlot z 5)) = storageAt S C (mapSlot y (mapSlot z 5))

/-- The slot of `allowed` keyed by `y` and `z` keeps its word (round 29: the conclusions are stated
for one given slot, under `SecSep` of the call's keys and `y`, `z`; through round 28 they were
stated for every slot at once under the global `KeccakSep` and `AllowSep`). -/
def AllowKeptAt (y z : U256) (C : Address) (S S' : State.TransactionState) : Prop :=
  storageAt S' C (mapSlot y (mapSlot z 5)) = storageAt S C (mapSlot y (mapSlot z 5))

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate} {bound : Nat} {runChild : MessageRunner fork Nat bound}
  {evm s : Evm fork Nat} {gas : Nat}

theorem SecSep.allowYZ {y z : U256} {A : List U256} (K : SecSep (y :: z :: A)) :
    NotBal (mapSlot y (mapSlot z 5)) ∧ NotFixed (mapSlot y (mapSlot z 5)) ∧
      NotList (mapSlot y (mapSlot z 5)) :=
  ⟨(K.allow y (by simp) z (by simp)).1, (K.allow y (by simp) z (by simp)).2,
    K.allowList y (by simp) z (by simp)⟩

theorem not_balOrOne {n : U256} (hb : NotBal n) (hf : NotFixed n) : ¬ BalOrOne n := by
  rintro (⟨x, hx, e⟩ | e)
  · exact hb x hx e
  · exact hf.ne_one e

/-- A successful call that is neither approve nor transferFrom keeps the allowance of `y` and `z`,
under `SecSep` of the call's keys and `y`, `z`. -/
theorem Effect.allowKept {y z : U256} {S S' : State.TransactionState}
    (K : SecSep (y :: z :: callKeys message S)) (h : Effect message S S')
    (hsel : selector message.data ≠ 0x095ea7b3 ∧ selector message.data ≠ 0x23b872dd) :
    AllowKeptAt y z message.currentTarget S S' := by
  obtain ⟨hnb, hnf, hnl⟩ := K.allowYZ
  have hb : ¬ BalSlot (mapSlot y (mapSlot z 5)) := fun ⟨x, hx, e⟩ => hnb x hx e
  have hbo : ¬ BalOrOne (mapSlot y (mapSlot z 5)) := not_balOrOne hnb hnf
  unfold AllowKeptAt
  cases h with
  | same h => exact h _
  | transferOk _ hacc _ _ _ _ hst => rw [hst]; exact writes_credited hacc _ _ _ hb
  | transferFee _ hacc _ _ _ _ _ _ hst => rw [hst]; exact writes_feeState hacc _ _ _ hb
  | fromOk hs => exact absurd hs hsel.2
  | fromFee hs => exact absurd hs hsel.2
  | approve hs => exact absurd hs hsel.1
  | ownerW _ hw => exact hw _ (not_ownW hnf hnl)
  | issue _ _ hacc _ _ hst => rw [hst]; exact writes_issue hacc _ hbo
  | redeem _ _ hacc _ _ hst => rw [hst]; exact writes_redeem hacc _ hbo
  | destroy _ _ hacc _ hst => rw [hst]; exact writes_destroy hacc _ hbo

/-- **Allowances, one call.** From Berlin (Glamsterdam included), a fresh frame of `CODE` at pc
0, static or not, any call data below 2^256 bytes, any value, any gas, any gas bound and any
message runner; not deprecated, slots 7 and 8 of `StrForm`; for words `y`, `z`, under `SecSep` of
the call's keys and `y`, `z`: if the selector is neither approve nor transferFrom and the run ends
with no error, the slot of `allowed` keyed by `y` and `z` keeps its word. -/
theorem allowKept_call {y z : U256} (K : SecSep (y :: z :: callKeys message state)) (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    (h7 : StrForm (storageAt state message.currentTarget 7))
    (h8 : StrForm (storageAt state message.currentTarget 8))
    (hsel : selector message.data ≠ 0x095ea7b3 ∧ selector message.data ≠ 0x23b872dd)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) : AllowKeptAt y z message.currentTarget state s.state :=
  (effect_call hfork hsize' hdep h7 h8 start within hrun hok).allowKept K hsel

/-- **transferFrom stays within the allowance.** From Berlin (Glamsterdam included), a fresh frame
of `CODE` at pc 0, static or not, any call data below 2^256 bytes, any value, any gas, any gas
bound and any message runner; not deprecated; under `SepOn` of the call's keys. For `transferFrom(f, t, v)`
(`f = fromArg`, `v = valArg`), with `A = allowed[f][caller]` at the start, every run that ends
with no error has: `A = MAX_UINT` or `v ≤ A`; `balances[f]` at the start is at most
`balances[f]` at the end plus `v`; when `A ≠ MAX_UINT` the allowance at the end plus `v` is `A`;
when `A = MAX_UINT` the allowance at the end is `MAX_UINT`. -/
theorem transferFrom_bound (K : SepOn (callKeys message state)) (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x23b872dd)
    (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) :
    (storageAt state message.currentTarget (allowFrom message (fromArg message)) = MAX_UINT ∨
      (valArg message).toNat ≤
        (storageAt state message.currentTarget (allowFrom message (fromArg message))).toNat) ∧
    (storageAt state message.currentTarget (recipientSlot (fromArg message))).toNat ≤
      (storageAt s.state message.currentTarget (recipientSlot (fromArg message))).toNat +
        (valArg message).toNat ∧
    (storageAt state message.currentTarget (allowFrom message (fromArg message)) ≠ MAX_UINT →
      (storageAt s.state message.currentTarget (allowFrom message (fromArg message))).toNat +
        (valArg message).toNat =
      (storageAt state message.currentTarget (allowFrom message (fromArg message))).toNat) ∧
    (storageAt state message.currentTarget (allowFrom message (fromArg message)) = MAX_UINT →
      storageAt s.state message.currentTarget (allowFrom message (fromArg message)) = MAX_UINT) := by
  obtain ⟨-, hacc, -, -, -, -, hallow, -, hbal, hto, -, h⟩ := ok_transferFrom hfork hsize' hsel
    hdep rfl rfl rfl rfl rfl rfl rfl rfl rfl start (Gas.Ends.run hrun) hok
  have hA : allowOf (checkState state message) message (fromArg message) =
      storageAt state message.currentTarget (allowFrom message (fromArg message)) := by
    simp only [storageAt_readSlot]
  have hacc' : hasAccount (allowedF (checkState state message) message (valArg message)
      (fromArg message)) message.currentTarget := by wchain
  have hbf : balFrom (checkState state message) message (valArg message) (fromArg message) =
      storageAt state message.currentTarget (recipientSlot (fromArg message)) := by
    simp only [balFrom, allowedF]
    rw [Summary.storageAt_allowState_of_ne (by wchain)
      (fun e => K.allowFromArg.1 _ (mask_lt _) e.symm)]
    simp only [storageAt_readSlot]
  have hdeb : storageAt (debitedF (checkState state message) message (valArg message)
      (fromArg message)) message.currentTarget (recipientSlot (fromArg message)) =
      sub (balFrom (checkState state message) message (valArg message) (fromArg message))
        (valArg message) := storageAt_writeSlot_self (hasAccount_readSlot hacc')
  have hal : storageAt (allowedF (checkState state message) message (valArg message)
      (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) =
      if storageAt state message.currentTarget (allowFrom message (fromArg message)) = MAX_UINT
      then storageAt state message.currentTarget (allowFrom message (fromArg message))
      else sub (storageAt state message.currentTarget (allowFrom message (fromArg message)))
        (valArg message) := by
    simp only [allowedF, allowState, hA]
    split
    · simp only [storageAt_readSlot]
    · exact storageAt_writeSlot_self (by wchain)
  rw [hA] at hallow
  have finish : ∀ {S' : State.TransactionState},
      Writes message.currentTarget BalSlot (allowedF (checkState state message) message
        (valArg message) (fromArg message)) S' →
      NoDec message.currentTarget (recipientSlot (fromArg message))
        (debitedF (checkState state message) message (valArg message) (fromArg message)) S' →
      s.state = S' →
      (storageAt state message.currentTarget (allowFrom message (fromArg message)) = MAX_UINT ∨
        (valArg message).toNat ≤
          (storageAt state message.currentTarget (allowFrom message (fromArg message))).toNat) ∧
      (storageAt state message.currentTarget (recipientSlot (fromArg message))).toNat ≤
        (storageAt s.state message.currentTarget (recipientSlot (fromArg message))).toNat +
          (valArg message).toNat ∧
      (storageAt state message.currentTarget (allowFrom message (fromArg message)) ≠ MAX_UINT →
        (storageAt s.state message.currentTarget (allowFrom message (fromArg message))).toNat +
          (valArg message).toNat =
        (storageAt state message.currentTarget (allowFrom message (fromArg message))).toNat) ∧
      (storageAt state message.currentTarget (allowFrom message (fromArg message)) = MAX_UINT →
        storageAt s.state message.currentTarget (allowFrom message (fromArg message)) =
          MAX_UINT) := by
    intro S' hW hN hst
    have hkeep := hW (allowFrom message (fromArg message))
      (fun ⟨x, hx, e⟩ => K.allowFromArg.1 x hx e)
    rw [hst]
    refine ⟨hallow, ?_, fun hne => ?_, fun he => ?_⟩
    · unfold NoDec at hN
      rw [hdeb, IssueSpec.toNat_sub' hbal] at hN
      rw [hbf] at hN hbal
      omega
    · rw [hkeep, hal, ite_eq_right hne]
      have hv : (valArg message).toNat ≤
          (storageAt state message.currentTarget (allowFrom message (fromArg message))).toNat := by
        rcases hallow with e | hv
        · exact absurd e hne
        · exact hv
      rw [IssueSpec.toNat_sub' hv]
      omega
    · rw [hkeep, hal, ite_eq_left he, he]
  have hacc'' : hasAccount (debitedF (checkState state message) message (valArg message)
      (fromArg message)) message.currentTarget := by wchain
  rcases h with ⟨hfee, -, hst, -⟩ | ⟨-, hown, -, hst, -⟩
  · rw [sendOf_zero hfee] at hto
    refine finish ?_ ?_ hst
    · wchain
    · ndchain
  · refine finish ?_ ?_ hst
    · wchain
    · ndchain

/-- The predicate of `allowKept_seq` on each call: neither approve nor transferFrom, and, at its
start state, not deprecated with slots 7 and 8 of `StrForm`, and `SecSep` of the call's keys and
`y`, `z`. -/
def NoAllowFn (y z : U256) {fork : Fork} (message : Message fork) (S : State.TransactionState) :
    Prop :=
  selector message.data ≠ 0x095ea7b3 ∧ selector message.data ≠ 0x23b872dd ∧
    Plain message.currentTarget S ∧ SecSep (y :: z :: callKeys message S)

/-- **Allowances over a sequence.** Along a finite sequence of successful calls to `C` that are
neither approve nor transferFrom (each not deprecated, with slots 7 and 8 of `StrForm`, and with
`SecSep` of its keys and `y`, `z`, at its start state) and of `Untouched` steps, the slot of
`allowed` keyed by `y` and `z` keeps its word. Callers may be the owner. -/
theorem allowKept_seq {y z : U256} {C : Address} {S S' : State.TransactionState}
    (h : Seq C (@NoAllowFn y z) S S') : AllowKeptAt y z C S S' := by
  refine seq_lift (I := fun _ => True) (R := AllowKeptAt y z C) (fun _ => rfl)
    (fun h1 h2 => h2.trans h1) (fun hu _ => ⟨hu _, trivial⟩) ?_ h trivial
  intro S S' fork message hr hq _
  obtain ⟨ha, hf, ⟨hdep, h7, h8⟩, K⟩ := hq
  have hC : message.currentTarget = C := by obtain ⟨_, _, _, _, _, _, _, hC, -⟩ := hr; exact hC
  subst hC
  obtain ⟨-, he⟩ := hr.effect hdep h7 h8
  exact ⟨he.allowKept K ⟨ha, hf⟩, trivial⟩

/-! ## Deprecated or not -/

/-- The two writes of deprecated destroyBlackFunds after its call (`balances[a]`, slot 1) write
only a slot of `balances` and slot 1. -/
theorem writes_tail {C : Address} {Y : State.TransactionState} (hacc : hasAccount Y C)
    {a : U256} (ha : BalSlot (mapSlot a 2)) (d : U256) :
    Writes C BalOrOne Y (DeprecatedDestroy.tailState Y C a d) :=
  Writes.wr (Writes.wr (Writes.refl _ _ _) hacc (.inl ha) 0) (hasAccount_writeSlot hacc)
    (.inr rfl) _

/-- The runner assumption of the allowance property when deprecated: every call from `C` to
the upgraded address that the code of `C` makes from `S` (`SentVia`, round 29: the caller state has the view of `S`, the message runs the code the upgraded address holds in `S`; through round 28 every message from `C` to `ua`), and that the runner ends with no error keeps every slot of `allowed` of `C`. -/
def KeepsAllow {fork : Fork} {bound : Nat} (runChild : MessageRunner fork Nat bound)
    (message : Message fork) (S : State.TransactionState) : Prop :=
  KeepsAt runChild message S (upAddr S message) (AllowKept message.currentTarget)

theorem EffectD.allowKept {y z : U256} {S S' : State.TransactionState}
    (K : SecSep (y :: z :: callKeys message S)) (h : EffectD runChild message S S')
    (hsel : selector message.data ≠ 0x095ea7b3 ∧ selector message.data ≠ 0x23b872dd)
    (hk : byte20 (storageAt S message.currentTarget 10) ≠ 0 →
      KeepsAllow runChild message S) :
    AllowKeptAt y z message.currentTarget S S' := by
  cases h with
  | loc h => exact h.allowKept K hsel
  | fwd hdep _ _ _ X hX hf => exact ((hk hdep).fwd hf y z).trans (hX _)
  | dfwd hdep _ _ _ X Y d hX hf hacc hst =>
    have hbo : ¬ BalOrOne (mapSlot y (mapSlot z 5)) := not_balOrOne K.allowYZ.1 K.allowYZ.2.1
    unfold AllowKeptAt
    rw [hst, writes_tail hacc (bal_arg _ _) d _ hbo, (hk hdep).fwd hf y z, hX]

/-- **Allowances, one call, deprecated or not.** As `allowKept_call` without `hdep`: when
deprecated, the runner meets `KeepsAllow` for the calls to the upgraded address (`hkeeps`). If
the selector is neither approve nor transferFrom and the run ends with no error, then under
`SecSep` of the call's keys and `y`, `z`, the slot of `allowed` keyed by `y` and `z` keeps its
word. -/
theorem allowKept_call_all {y z : U256} (K : SecSep (y :: z :: callKeys message state)) (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (h7 : StrForm (storageAt state message.currentTarget 7))
    (h8 : StrForm (storageAt state message.currentTarget 8))
    (hsel : selector message.data ≠ 0x095ea7b3 ∧ selector message.data ≠ 0x23b872dd)
    (hkeeps : byte20 (storageAt state message.currentTarget 10) ≠ 0 →
      KeepsAllow runChild message state)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) : AllowKeptAt y z message.currentTarget state s.state :=
  (effect_all hfork hsize' h7 h8 start within hrun hok).allowKept K hsel hkeeps

/-- The predicate of `allowKept_seq_all` on each call: neither approve nor transferFrom, slots 7
and 8 of `StrForm`, and `SecSep` of the call's keys and `y`, `z`, at its start state. -/
def NoAllowFnS (y z : U256) {fork : Fork} (message : Message fork) (S : State.TransactionState) :
    Prop :=
  selector message.data ≠ 0x095ea7b3 ∧ selector message.data ≠ 0x23b872dd ∧ Strs message S ∧
    SecSep (y :: z :: callKeys message S)

/-- **Allowances over a sequence, deprecated or not.** Along a finite sequence of successful calls
to `C` that are neither approve nor transferFrom (with slots 7 and 8 of `StrForm` at each call's
start state), whose runner meets `KeepsAllow` when `C` is deprecated at that state, and of
`Untouched` steps, each call with `SecSep` of its keys and `y`, `z`: the slot of `allowed` keyed by
`y` and `z` keeps its word. Callers may be the owner. -/
theorem allowKept_seq_all {y z : U256} {C : Address}
    {S S' : State.TransactionState} (h : SeqR C (AllowKept C) (@NoAllowFnS y z) S S') :
    AllowKeptAt y z C S S' := by
  refine seqR_lift (I := fun _ => True) (R := AllowKeptAt y z C) (fun _ => rfl)
    (fun h1 h2 => h2.trans h1) (fun hu _ => ⟨hu _, trivial⟩) ?_ h trivial
  intro S S' fork message hr hq _
  obtain ⟨ha, hf, ⟨h7, h8⟩, K⟩ := hq
  have hC : message.currentTarget = C := by obtain ⟨_, _, _, _, _, _, _, hC, -⟩ := hr; exact hC
  subst hC
  obtain ⟨-, bound, runChild, he, hk⟩ := hr.effect h7 h8
  exact ⟨he.allowKept K ⟨ha, hf⟩ hk, trivial⟩

end UsdtVerify.Security
