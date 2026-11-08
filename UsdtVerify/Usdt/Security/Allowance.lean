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
  and when `A = MAX_UINT` the allowance is still `MAX_UINT`. Under `KeccakSep`.
- `Effect.allowKept` / `allowKept_call`: a successful call (not deprecated) whose selector is
  neither approve nor transferFrom keeps every slot of `allowed`. Under `KeccakSep` and
  `AllowSep`.
- `allowKept_seq`: along a finite sequence of such calls (each not deprecated, slots 7 and 8 of
  `StrForm`, at its own start state) and of `Untouched` steps, every slot of `allowed` keeps its
  word.

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

/-- Every slot of `allowed` keeps its word. -/
def AllowKept (C : Address) (S S' : State.TransactionState) : Prop :=
  ∀ y z : U256, storageAt S' C (mapSlot y (mapSlot z 5)) = storageAt S C (mapSlot y (mapSlot z 5))

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate} {bound : Nat} {runChild : MessageRunner fork Nat bound}
  {evm s : Evm fork Nat} {gas : Nat}

/-- A successful call that is neither approve nor transferFrom keeps every allowance. -/
theorem Effect.allowKept (K : KeccakSep) (A : AllowSep) {S S' : State.TransactionState}
    (h : Effect message S S')
    (hsel : selector message.data ≠ 0x095ea7b3 ∧ selector message.data ≠ 0x23b872dd) :
    AllowKept message.currentTarget S S' := by
  intro y z
  have hb : ¬ BalSlot (mapSlot y (mapSlot z 5)) := fun hb => bal_not_allow K hb (allow_mk y z)
  have hbo : ¬ BalOrOne (mapSlot y (mapSlot z 5)) := by
    rintro (hb' | e)
    · exact hb hb'
    · exact K.one_allow y z e
  cases h with
  | same h => exact h _
  | transferOk _ hacc _ _ _ _ hst => rw [hst]; exact writes_credited hacc _ _ _ hb
  | transferFee _ hacc _ _ _ _ _ _ hst => rw [hst]; exact writes_feeState hacc _ _ _ hb
  | fromOk hs => exact absurd hs hsel.2
  | fromFee hs => exact absurd hs hsel.2
  | approve hs => exact absurd hs hsel.1
  | ownerW _ hw => exact hw _ (allow_not_ownW A (allow_mk y z))
  | issue _ _ hacc _ _ hst => rw [hst]; exact writes_issue hacc _ hbo
  | redeem _ _ hacc _ _ hst => rw [hst]; exact writes_redeem hacc _ hbo
  | destroy _ _ hacc _ hst => rw [hst]; exact writes_destroy hacc _ hbo

/-- **Allowances, one call.** From Berlin (Glamsterdam included), a fresh frame of `CODE` at pc
0, static or not, any call data below 2^256 bytes, any value, any gas, any gas bound and any
message runner; not deprecated, slots 7 and 8 of `StrForm`, under `KeccakSep` and `AllowSep`: if
the selector is neither approve nor transferFrom and the run ends with no error, every slot of
`allowed` keeps its word. -/
theorem allowKept_call (K : KeccakSep) (A : AllowSep) (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    (h7 : StrForm (storageAt state message.currentTarget 7))
    (h8 : StrForm (storageAt state message.currentTarget 8))
    (hsel : selector message.data ≠ 0x095ea7b3 ∧ selector message.data ≠ 0x23b872dd)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) : AllowKept message.currentTarget state s.state :=
  (effect_call hfork hsize' hdep h7 h8 start within hrun hok).allowKept K A hsel

/-- **transferFrom stays within the allowance.** From Berlin (Glamsterdam included), a fresh frame
of `CODE` at pc 0, static or not, any call data below 2^256 bytes, any value, any gas, any gas
bound and any message runner; not deprecated; under `KeccakSep`. For `transferFrom(f, t, v)`
(`f = fromArg`, `v = valArg`), with `A = allowed[f][caller]` at the start, every run that ends
with no error has: `A = MAX_UINT` or `v ≤ A`; `balances[f]` at the start is at most
`balances[f]` at the end plus `v`; when `A ≠ MAX_UINT` the allowance at the end plus `v` is `A`;
when `A = MAX_UINT` the allowance at the end is `MAX_UINT`. -/
theorem transferFrom_bound (K : KeccakSep) (hfork : .berlin ≤ fork)
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
    hdep rfl rfl rfl rfl rfl rfl rfl rfl rfl start within hrun hok
  have hA : allowOf (checkState state message) message (fromArg message) =
      storageAt state message.currentTarget (allowFrom message (fromArg message)) := by
    simp only [storageAt_readSlot]
  have hacc' : hasAccount (allowedF (checkState state message) message (valArg message)
      (fromArg message)) message.currentTarget := by wchain
  have hbf : balFrom (checkState state message) message (valArg message) (fromArg message) =
      storageAt state message.currentTarget (recipientSlot (fromArg message)) := by
    simp only [balFrom, allowedF]
    rw [Summary.storageAt_allowState_of_ne (by wchain) (K.allow _ _ _)]
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
      (fun hb => bal_not_allow K hb (allow_mk _ _))
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
start state, not deprecated with slots 7 and 8 of `StrForm`. -/
def NoAllowFn {fork : Fork} (message : Message fork) (S : State.TransactionState) : Prop :=
  selector message.data ≠ 0x095ea7b3 ∧ selector message.data ≠ 0x23b872dd ∧
    Plain message.currentTarget S

/-- **Allowances over a sequence.** Along a finite sequence of successful calls to `C` that are
neither approve nor transferFrom (each not deprecated, with slots 7 and 8 of `StrForm`, at its
start state) and of `Untouched` steps: under `KeccakSep` and `AllowSep`, every slot of `allowed`
keeps its word. Callers may be the owner. -/
theorem allowKept_seq (K : KeccakSep) (A : AllowSep) {C : Address} {S S' : State.TransactionState}
    (h : Seq C NoAllowFn S S') : AllowKept C S S' := by
  refine seq_lift (I := fun _ => True) (R := AllowKept C) (fun _ _ _ => rfl)
    (fun h1 h2 y z => (h2 y z).trans (h1 y z)) (fun hu _ => ⟨fun _ _ => hu _, trivial⟩) ?_ h
    trivial
  intro S S' fork message hr hq _
  obtain ⟨ha, hf, hdep, h7, h8⟩ := hq
  have hC : message.currentTarget = C := by obtain ⟨_, _, _, _, _, _, _, hC, -⟩ := hr; exact hC
  subst hC
  obtain ⟨-, he⟩ := hr.effect hdep h7 h8
  exact ⟨he.allowKept K A ⟨ha, hf⟩, trivial⟩

/-! ## Deprecated or not -/

/-- The two writes of deprecated destroyBlackFunds after its call (`balances[a]`, slot 1) write
only a slot of `balances` and slot 1. -/
theorem writes_tail {C : Address} {Y : State.TransactionState} (hacc : hasAccount Y C)
    {a : U256} (ha : BalSlot (mapSlot a 2)) (d : U256) :
    Writes C BalOrOne Y (DeprecatedDestroy.tailState Y C a d) :=
  Writes.wr (Writes.wr (Writes.refl _ _ _) hacc (.inl ha) 0) (hasAccount_writeSlot hacc)
    (.inr rfl) _

/-- The runner assumption of the allowance property when deprecated: every call from `C` to
`ua` that the runner ends with no error keeps every slot of `allowed` of `C`. -/
def KeepsAllow {fork : Fork} {bound : Nat} (runChild : MessageRunner fork Nat bound)
    (C ua : Address) : Prop :=
  Keeps runChild C ua (AllowKept C)

theorem EffectD.allowKept (K : KeccakSep) (A : AllowSep) {S S' : State.TransactionState}
    (h : EffectD runChild message S S')
    (hsel : selector message.data ≠ 0x095ea7b3 ∧ selector message.data ≠ 0x23b872dd)
    (hk : byte20 (storageAt S message.currentTarget 10) ≠ 0 →
      KeepsAllow runChild message.currentTarget (upAddr S message)) :
    AllowKept message.currentTarget S S' := by
  cases h with
  | loc h => exact h.allowKept K A hsel
  | fwd hdep _ _ _ X hX hf => exact fun y z => ((hk hdep).fwd hf y z).trans (hX _)
  | dfwd hdep _ _ _ X Y d hX hf hacc hst =>
    intro y z
    have hbo : ¬ BalOrOne (mapSlot y (mapSlot z 5)) := by
      rintro (hb | e)
      · exact bal_not_allow K hb (allow_mk y z)
      · exact K.one_allow y z e
    rw [hst, writes_tail hacc (bal_arg _ _) d _ hbo, (hk hdep).fwd hf y z, hX]

/-- **Allowances, one call, deprecated or not.** As `allowKept_call` without `hdep`: when
deprecated, the runner meets `KeepsAllow` for the calls to the upgraded address (`hkeeps`). If
the selector is neither approve nor transferFrom and the run ends with no error, every slot of
`allowed` keeps its word. -/
theorem allowKept_call_all (K : KeccakSep) (A : AllowSep) (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (h7 : StrForm (storageAt state message.currentTarget 7))
    (h8 : StrForm (storageAt state message.currentTarget 8))
    (hsel : selector message.data ≠ 0x095ea7b3 ∧ selector message.data ≠ 0x23b872dd)
    (hkeeps : byte20 (storageAt state message.currentTarget 10) ≠ 0 →
      KeepsAllow runChild message.currentTarget (upAddr state message))
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) : AllowKept message.currentTarget state s.state :=
  (effect_all hfork hsize' h7 h8 start within hrun hok).allowKept K A hsel hkeeps

/-- The predicate of `allowKept_seq_all` on each call: neither approve nor transferFrom, and slots
7 and 8 of `StrForm` at its start state. -/
def NoAllowFnS {fork : Fork} (message : Message fork) (S : State.TransactionState) : Prop :=
  selector message.data ≠ 0x095ea7b3 ∧ selector message.data ≠ 0x23b872dd ∧ Strs message S

/-- **Allowances over a sequence, deprecated or not.** Along a finite sequence of successful calls
to `C` that are neither approve nor transferFrom (with slots 7 and 8 of `StrForm` at each call's
start state), whose runner meets `KeepsAllow` when `C` is deprecated at that state, and of
`Untouched` steps: under `KeccakSep` and `AllowSep`, every slot of `allowed` keeps its word.
Callers may be the owner. -/
theorem allowKept_seq_all (K : KeccakSep) (A : AllowSep) {C : Address}
    {S S' : State.TransactionState} (h : SeqR C (AllowKept C) NoAllowFnS S S') :
    AllowKept C S S' := by
  refine seqR_lift (I := fun _ => True) (R := AllowKept C) (fun _ _ _ => rfl)
    (fun h1 h2 y z => (h2 y z).trans (h1 y z)) (fun hu _ => ⟨fun _ _ => hu _, trivial⟩) ?_ h
    trivial
  intro S S' fork message hr hq _
  obtain ⟨ha, hf, h7, h8⟩ := hq
  have hC : message.currentTarget = C := by obtain ⟨_, _, _, _, _, _, _, hC, -⟩ := hr; exact hC
  subst hC
  obtain ⟨-, bound, runChild, he, hk⟩ := hr.effect h7 h8
  exact ⟨he.allowKept K A ⟨ha, hf⟩ hk, trivial⟩

end UsdtVerify.Security
