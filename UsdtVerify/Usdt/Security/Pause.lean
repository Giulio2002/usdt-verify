import UsdtVerify.Usdt.Security.Access

/-!
# Pause: no balance moves while paused, except by issue, redeem and destroyBlackFunds

`paused` is byte 20 of slot 0. `BalKept C S S'`: every slot of `balances` (of an address word
below 2^160) holds the same word in `S'` as in `S`.

- `Effect.paused`: under `SepOn` of the call's keys, a successful call (not deprecated) from a paused state
  keeps every balance, or it is a call by the owner of issue, redeem or destroyBlackFunds.
  (transfer and transferFrom revert when paused: their effects state "not paused"; approve
  writes a slot of `allowed`; the other owner functions write slots 0, 3, 4, 10 and the slot of
  `isBlackListed` of their address argument.)
- `paused_call`: that for every successful call (any call data below 2^256 bytes, any value, any
  gas, static or not), not deprecated, slots 7 and 8 of `StrForm`.
- `paused_seq`: along a finite sequence of successful calls by callers other than the owner and
  of `Untouched` steps, from a paused state, not deprecated, slots 7 and 8 of `StrForm`, each call
  under `SecSep` of its keys: every balance keeps its word (the flags stay as they are by
  `nonOwner_seq`).

Deprecated or not (round 23):
- `transfer_checks_all`, `transferFrom_checks_all` (no runner assumption): every successful
  transfer starts not paused with the caller not blacklisted, and every successful transferFrom
  not paused with `_from` not blacklisted (the code checks both before the `deprecated` flag).
- `paused_call_all`: `paused_call` without `hdep`; when deprecated the runner meets `KeepsBal`
  (a call to the upgraded address keeps every balance of `C`).
- `paused_seq_all`: over a `SeqR` sequence of non-owner calls, with `KeepsSlots` and `KeepsBal`.
-/

namespace UsdtVerify.Security

open EthLib.Base (Fork U256 Address)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open Invariant Complete Owner Approve Deprecated

/-- Every slot of `balances` keeps its word. -/
def BalKept (C : Address) (S S' : State.TransactionState) : Prop :=
  ∀ x : U256, x.toNat < 2 ^ 160 → storageAt S' C (mapSlot x 2) = storageAt S C (mapSlot x 2)

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate} {bound : Nat} {runChild : MessageRunner fork Nat bound}
  {evm s : Evm fork Nat} {gas : Nat}

/-- From a paused state, a successful call keeps every balance, or it is the owner's issue,
redeem or destroyBlackFunds. -/
theorem Effect.paused {S S' : State.TransactionState} (K : SepOn (callKeys message S))
    (h : Effect message S S')
    (hp : byte20 (storageAt S message.currentTarget 0) ≠ 0) :
    BalKept message.currentTarget S S' ∨
      (callerWord message = ownerOf S message.currentTarget ∧
        (selector message.data = 0xcc872b66 ∨ selector message.data = 0xdb006a75 ∨
          selector message.data = 0xf3bdc228)) := by
  cases h with
  | same h => exact .inl fun x _ => h _
  | transferOk _ _ hpause => exact absurd hpause hp
  | transferFee _ _ hpause => exact absurd hpause hp
  | fromOk _ _ hpause => exact absurd hpause hp
  | fromFee _ _ hpause => exact absurd hpause hp
  | approve _ hw => exact .inl fun x hx => hw _ fun e => K.allowArg.1 x hx e.symm
  | ownerW _ hw => exact .inl fun x hx => hw _ fun ho => ownW_notBal K ho x hx rfl
  | issue hsel howner => exact .inr ⟨howner, .inl hsel⟩
  | redeem hsel howner => exact .inr ⟨howner, .inr (.inl hsel)⟩
  | destroy hsel howner => exact .inr ⟨howner, .inr (.inr hsel)⟩

/-- **Pause, one call.** From Berlin (Glamsterdam included), a fresh frame of `CODE` at pc 0,
static or not, any call data below 2^256 bytes, any value, any gas, any gas bound and any message
runner; not deprecated, paused (`hpaused`: byte 20 of slot 0 not 0), slots 7 and 8 of `StrForm`,
under `SepOn` of the call's keys: if the run ends with no error, every balance keeps its word, or
the caller is the owner and the function is issue, redeem or destroyBlackFunds. -/
theorem paused_call (K : SepOn (callKeys message state)) (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    (hpaused : byte20 (storageAt state message.currentTarget 0) ≠ 0)
    (h7 : StrForm (storageAt state message.currentTarget 7))
    (h8 : StrForm (storageAt state message.currentTarget 8))
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) :
    BalKept message.currentTarget state s.state ∨
      (callerWord message = ownerOf state message.currentTarget ∧
        (selector message.data = 0xcc872b66 ∨ selector message.data = 0xdb006a75 ∨
          selector message.data = 0xf3bdc228)) :=
  (effect_call hfork hsize' hdep h7 h8 start within hrun hok).paused K hpaused

/-- **Pause over a sequence.** Along a finite sequence of successful calls to `C` by callers other
than the owner (of each call's start state) and of `Untouched` steps, from a state where `C` is
paused, not deprecated, with slots 7 and 8 of `StrForm`, each call with `SecSep` of its keys at
its start state: every balance keeps its word. -/
theorem paused_seq {C : Address} {S S' : State.TransactionState}
    (h : Seq C NotOwnerK S S') (hdep : byte20 (storageAt S C 10) = 0)
    (hpaused : byte20 (storageAt S C 0) ≠ 0)
    (h7 : StrForm (storageAt S C 7)) (h8 : StrForm (storageAt S C 8)) : BalKept C S S' := by
  refine seq_lift (I := fun X => Plain C X ∧ byte20 (storageAt X C 0) ≠ 0) (R := BalKept C)
    (fun _ _ _ => rfl) (fun h1 h2 x hx => (h2 x hx).trans (h1 x hx))
    (fun hu hI => ⟨fun _ _ => hu _, plain_of_untouched hu hI.1, by rw [hu]; exact hI.2⟩) ?_ h
    ⟨⟨hdep, h7, h8⟩, hpaused⟩
  intro S S' fork message hr hq hI
  obtain ⟨hno, K⟩ := hq
  obtain ⟨⟨hdep, h7, h8⟩, hp⟩ := hI
  obtain ⟨hC, he⟩ := hr.effect hdep h7 h8
  subst hC
  have hw := he.nonOwnerK K.toSepOn hno
  refine ⟨?_, plain_of_writes K.toSepOn hw ⟨hdep, h7, h8⟩, ?_⟩
  · rcases he.paused K.toSepOn hp with hk | ⟨howner, -⟩
    · exact hk
    · exact absurd howner hno
  · rw [hw 0 (fixed_not_kba K.toSepOn (k := 0) (by decide))]; exact hp

/-! ## Deprecated or not -/

/-- **transfer checks the pause flag and the sender, deprecated or not.** From Berlin
(Glamsterdam included), a fresh frame of `CODE` at pc 0, static or not, any call data below 2^256
bytes, any value, any gas, any gas bound and any message runner, no assumption on the runner:
every run of transfer that ends with no error starts from a state where `C` is not paused and the
caller is not blacklisted (the code checks both before it reads the `deprecated` flag). -/
theorem transfer_checks_all (hfork : .berlin ≤ fork) (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0xa9059cbb)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) :
    byte20 (storageAt state message.currentTarget 0) = 0 ∧
      (storageAt state message.currentTarget (Transfer.blackSlot message)).toNat % 256 = 0 := by
  by_cases hdep : byte20 (storageAt state message.currentTarget 10) = 0
  · obtain ⟨-, -, -, hpause, hblack, -⟩ := ok_transfer hfork hsize' hsel hdep rfl rfl rfl rfl rfl
      rfl rfl rfl start within hrun hok
    exact ⟨hpause, hblack⟩
  · obtain ⟨_, _, -, -, hpause, hblack, -⟩ :=
      dep_transfer_complete hfork hsize' hsel hdep rfl rfl rfl rfl start within hrun hok
    exact ⟨hpause, hblack⟩

/-- **transferFrom checks the pause flag and `_from`, deprecated or not.** As
`transfer_checks_all`, for transferFrom: not paused, and `_from` (`fromArg`) not blacklisted. -/
theorem transferFrom_checks_all (hfork : .berlin ≤ fork) (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x23b872dd)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) :
    byte20 (storageAt state message.currentTarget 0) = 0 ∧
      (storageAt state message.currentTarget
        (TransferFrom.blackFrom (TransferFrom.fromArg message))).toNat % 256 = 0 := by
  by_cases hdep : byte20 (storageAt state message.currentTarget 10) = 0
  · obtain ⟨-, -, -, hpause, hblack, -⟩ := ok_transferFrom hfork hsize' hsel hdep rfl rfl rfl rfl
      rfl rfl rfl rfl rfl start within hrun hok
    exact ⟨hpause, hblack⟩
  · obtain ⟨_, _, -, -, hpause, hblack, -⟩ :=
      dep_transferFrom_complete hfork hsize' hsel hdep rfl rfl rfl rfl start within hrun hok
    exact ⟨hpause, hblack⟩

/-- The runner assumption of the pause property when deprecated: every call from `C` to the upgraded address that the code of `C` makes from `S` (`SentVia`, round 29: the caller state has the view of `S`, the message runs the code the upgraded address holds in `S`; through round 28 every message from `C` to `ua`), and
that the runner ends with no error keeps every balance of `C`. -/
def KeepsBal {fork : Fork} {bound : Nat} (runChild : MessageRunner fork Nat bound)
    (message : Message fork) (S : State.TransactionState) : Prop :=
  KeepsAt runChild message S (upAddr S message) (BalKept message.currentTarget)

theorem EffectD.paused {S S' : State.TransactionState} (K : SepOn (callKeys message S))
    (h : EffectD runChild message S S')
    (hp : byte20 (storageAt S message.currentTarget 0) ≠ 0)
    (hk : byte20 (storageAt S message.currentTarget 10) ≠ 0 →
      KeepsBal runChild message S) :
    BalKept message.currentTarget S S' ∨
      (callerWord message = ownerOf S message.currentTarget ∧
        (selector message.data = 0xcc872b66 ∨ selector message.data = 0xdb006a75 ∨
          selector message.data = 0xf3bdc228)) := by
  cases h with
  | loc h => exact h.paused K hp
  | fwd hdep _ hT hF X hX hf =>
    by_cases e1 : selector message.data = 0xa9059cbb
    · exact absurd (hT e1).1 hp
    by_cases e2 : selector message.data = 0x23b872dd
    · exact absurd (hF e2).1 hp
    exact .inl fun x hx => ((hk hdep).fwd hf x hx).trans (hX _)
  | dfwd _ hsel howner => exact .inr ⟨howner, .inr (.inr hsel)⟩

/-- **Pause, one call, deprecated or not.** As `paused_call` without `hdep`: when deprecated, the
runner meets `KeepsBal` for the calls to the upgraded address (`hkeeps`; used for the forwarded
approve, totalSupply, balanceOf and allowance only: transfer and transferFrom have no successful
run while paused, `transfer_checks_all`, `transferFrom_checks_all`). From a paused state, if the
run ends with no error, every balance keeps its word, or the caller is the owner and the function
is issue, redeem or destroyBlackFunds. -/
theorem paused_call_all (K : SepOn (callKeys message state)) (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (hpaused : byte20 (storageAt state message.currentTarget 0) ≠ 0)
    (h7 : StrForm (storageAt state message.currentTarget 7))
    (h8 : StrForm (storageAt state message.currentTarget 8))
    (hkeeps : byte20 (storageAt state message.currentTarget 10) ≠ 0 →
      KeepsBal runChild message state)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) :
    BalKept message.currentTarget state s.state ∨
      (callerWord message = ownerOf state message.currentTarget ∧
        (selector message.data = 0xcc872b66 ∨ selector message.data = 0xdb006a75 ∨
          selector message.data = 0xf3bdc228)) :=
  (effect_all hfork hsize' h7 h8 start within hrun hok).paused K hpaused hkeeps

/-- **Pause over a sequence, deprecated or not.** Along a finite sequence of successful calls to
`C` by callers other than the owner (of each call's start state, with slots 7 and 8 of `StrForm`
there), whose runner, when `C` is deprecated at that state, meets `Keeps` for both `ProtKept C`
and `BalKept C` (that is, `KeepsSlots` and `KeepsBal`), and of `Untouched` steps, from a state
where `C` is paused, each call with `SecSep` of its keys: every balance keeps its word. -/
theorem paused_seq_all {C : Address}
    {S S' : State.TransactionState}
    (h : SeqR C (fun X Y => ProtKept C X Y ∧ BalKept C X Y) NotOwnerS S S')
    (hpaused : byte20 (storageAt S C 0) ≠ 0) : BalKept C S S' := by
  refine seqR_lift (I := fun X => byte20 (storageAt X C 0) ≠ 0) (R := BalKept C)
    (fun _ _ _ => rfl) (fun h1 h2 x hx => (h2 x hx).trans (h1 x hx))
    (fun hu hI => ⟨fun _ _ => hu _, by rw [hu]; exact hI⟩) ?_ h hpaused
  intro S S' fork message hr hq hp
  obtain ⟨hno, ⟨h7, h8⟩, K⟩ := hq
  have hC : message.currentTarget = C := by obtain ⟨_, _, _, _, _, _, _, hC, -⟩ := hr; exact hC
  subst hC
  obtain ⟨-, bound, runChild, he, hk⟩ := hr.effect h7 h8
  have hprot := he.protKept K hno (fun hd => (hk hd).mono fun _ _ h => h.1)
  refine ⟨?_, by rw [hprot 0 (.inl rfl)]; exact hp⟩
  rcases he.paused K.toSepOn hp (fun hd => (hk hd).mono fun _ _ h => h.2) with hb | ⟨howner, -⟩
  · exact hb
  · exact absurd howner hno

end UsdtVerify.Security
