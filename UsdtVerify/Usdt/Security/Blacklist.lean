import UsdtVerify.Usdt.Security.Pause

/-!
# Blacklist: a blacklisted address cannot lower its own balance

`Listed C S a`: the low byte of `isBlackListed[a]` (slot `keccak(a ++ 6)`) is not 0, as the code
tests it. The balance of `a` is the slot `keccak(a ++ 2)`.

- `Effect.listed`: under `SepOn` of the call's keys, for an address word `a < 2^160` blacklisted at the start,
  a successful call (not deprecated) does not lower the word of `balances[a]`, unless it is the
  owner's redeem or destroyBlackFunds. transfer checks the sender and transferFrom checks `_from`
  against the blacklist (so neither debits `a`); every other write to a balance adds to it
  without wrap (the recipient, the owner's fee, issue).
- `listed_call`: that for every successful call (any call data below 2^256 bytes, any value, any
  gas, static or not), not deprecated, slots 7 and 8 of `StrForm`. In particular through transfer
  and through transferFrom with `a` as `_from`.
- `listed_seq`: along a finite sequence of successful calls by callers other than the owner and of
  `Untouched` steps, from a state where `a` is blacklisted, not deprecated, slots 7 and 8 of
  `StrForm`, each call under `SecSep` of its keys: `balances[a]` never ends lower than it started (and
  `a` stays blacklisted, by `nonOwner_seq`).

Deprecated or not (round 23): `listed_call_all` (when deprecated the runner meets `KeepsListed`:
a call to the upgraded address lowers the balance of no address blacklisted in its caller state)
and `listed_seq_all` (with `KeepsSlots` and `KeepsListed`).

Over the EIP-8037 meter (round 37), not deprecated, any reservoir, refills allowed:
`listed_call_any`, `listed_seqS`. The `_seqS` forms take a `SeqS` (calls over `Nat` or
`StateGasMeter`); the `Seq` forms are proved from them.
-/

namespace UsdtVerify.Security

open EthLib.Base (Fork U256 Address)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open Deprecated
open Invariant Complete Owner Approve Transfer TransferOk TransferFee TransferFrom Issue IssueSpec

/-- `isBlackListed[a]`: the low byte of the slot `keccak(a ++ 6)` is not 0. -/
def Listed (C : Address) (S : State.TransactionState) (a : U256) : Prop :=
  (storageAt S C (mapSlot a 6)).toNat % 256 ≠ 0

theorem NoDec.allow {C : Address} {k : U256} {S X : State.TransactionState} (h : NoDec C k S X)
    (hacc : hasAccount X C) {n : U256} (hne : k ≠ n) (A v : U256) :
    NoDec C k S (allowState X C n A v) := by
  unfold allowState; split
  · exact h
  · exact h.wr_ne hacc hne _

/-- Builds a `NoDec` chain over reads, writes of other slots and writes of `old + d`. -/
macro "ndchain" : tactic => `(tactic| repeat (first
  | with_reducible assumption
  | with_reducible exact NoDec.refl _ _ _
  | with_reducible refine NoDec.rd ?_ _ _
  | with_reducible refine NoDec.wr_add ?_ ?_ (by first
      | (simp only [storageAt_readSlot]; done) | (simp only [storageAt_readSlot]; rfl) | rfl) ?_
  | with_reducible refine NoDec.wr_ne ?_ ?_ ?_ _
  | with_reducible refine NoDec.allow ?_ ?_ ?_ _ _
  | with_reducible apply hasAccount_readSlot
  | with_reducible apply hasAccount_writeSlot
  | with_reducible apply UsdtVerify.TransferFrom.hasAccount_allowState))

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate} {bound : Nat} {runChild : MessageRunner fork Nat bound}
  {evm s : Evm fork Nat} {gas : Nat}

theorem bal_ne_of_unlisted {S : State.TransactionState} {C : Address} {a x : U256}
    (hu : UniqBal (bitwiseAnd ADDR_MASK x)) (ha : a.toNat < 2 ^ 160) (hl : Listed C S a)
    (hx : (storageAt S C (mapSlot (bitwiseAnd ADDR_MASK x) 6)).toNat % 256 = 0) :
    mapSlot a 2 ≠ mapSlot (bitwiseAnd ADDR_MASK x) 2 := by
  intro e
  apply hl
  rw [hu a ha e]
  exact hx

/-- A blacklisted address word `a` keeps at least its balance over a successful call that is not
the owner's redeem or destroyBlackFunds. -/
theorem Effect.listed {S S' : State.TransactionState} (K : SepOn (callKeys message S))
    (h : Effect message S S')
    {a : U256} (ha : a.toNat < 2 ^ 160) (hl : Listed message.currentTarget S a)
    (hsel : (selector message.data ≠ 0xdb006a75 ∧ selector message.data ≠ 0xf3bdc228) ∨
      callerWord message ≠ ownerOf S message.currentTarget) :
    NoDec message.currentTarget (mapSlot a 2) S S' := by
  have h1 : mapSlot a 2 ≠ 1 := bal_ne_one K.fixed ha
  cases h with
  | same h => unfold NoDec; rw [h]; exact Nat.le_refl _
  | transferOk _ hacc _ hblack _ hto hst =>
    have hne : mapSlot a 2 ≠ senderSlot message := bal_ne_of_unlisted K.uniqCaller ha hl hblack
    rw [hst]; ndchain
  | transferFee _ hacc _ hblack _ _ hto hown hst =>
    have hne : mapSlot a 2 ≠ senderSlot message := bal_ne_of_unlisted K.uniqCaller ha hl hblack
    rw [hst]; ndchain
  | fromOk _ hacc _ hblack _ _ hto hst =>
    have hne : mapSlot a 2 ≠ recipientSlot (fromArg message) :=
      bal_ne_of_unlisted (K.uniqArg (.inl rfl)) ha hl hblack
    have hneA : mapSlot a 2 ≠ allowFrom message (fromArg message) :=
      fun e => K.allowFromArg.1 a ha e.symm
    rw [hst]; ndchain
  | fromFee _ hacc _ hblack _ _ _ hto hown hst =>
    have hne : mapSlot a 2 ≠ recipientSlot (fromArg message) :=
      bal_ne_of_unlisted (K.uniqArg (.inl rfl)) ha hl hblack
    have hneA : mapSlot a 2 ≠ allowFrom message (fromArg message) :=
      fun e => K.allowFromArg.1 a ha e.symm
    rw [hst]; ndchain
  | approve _ hw => exact NoDec.of_writes hw fun e => K.allowArg.1 a ha e.symm
  | ownerW _ hw => exact NoDec.of_writes hw fun ho => ownW_notBal K ho a ha rfl
  | issue _ _ hacc hT hB hst =>
    have hT' : (storageAt (issueState1 S message) message.currentTarget 1).toNat +
        (wordArg message.data 0).toNat < 2 ^ 256 := by
      rw [storageAt_writeSlot_of_ne (by acc) (Ne.symm (bal_ne_one K.fixed (mask_lt _)))]
      simp only [storageAt_readSlot]; exact hT
    rw [hst]; ndchain
  | redeem hsel' howner =>
    rcases hsel with ⟨hr, -⟩ | hno
    · exact absurd hsel' hr
    · exact absurd howner hno
  | destroy hsel' howner =>
    rcases hsel with ⟨-, hd⟩ | hno
    · exact absurd hsel' hd
    · exact absurd howner hno

/-- **Blacklist, one call.** From Berlin (Glamsterdam included), a fresh frame of `CODE` at pc 0,
static or not, any call data below 2^256 bytes, any value, any gas, any gas bound and any message
runner; not deprecated, slots 7 and 8 of `StrForm`, under `SepOn` of the call's keys: for an
address word
`a < 2^160` blacklisted at the start, if the run ends with no error and it is not the owner's
redeem or destroyBlackFunds (`hsel`), `balances[a]` is not lower at the end. -/
theorem listed_call (K : SepOn (callKeys message state)) (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    (h7 : StrForm (storageAt state message.currentTarget 7))
    (h8 : StrForm (storageAt state message.currentTarget 8))
    {a : U256} (ha : a.toNat < 2 ^ 160) (hl : Listed message.currentTarget state a)
    (hsel : (selector message.data ≠ 0xdb006a75 ∧ selector message.data ≠ 0xf3bdc228) ∨
      callerWord message ≠ ownerOf state message.currentTarget)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) : NoDec message.currentTarget (mapSlot a 2) state s.state :=
  (effect_call hfork hsize' hdep h7 h8 start within hrun hok).listed K ha hl hsel

/-- `listed_call` over the EIP-8037 meter (round 37): for a run of the loop over
`StateGasMeter`, any gas bound and message runner, from a frame `m` whose `toNat` is the fresh
frame of `CODE`. No hypothesis on the reservoir, on refills or on the gas limit. -/
theorem listed_call_any (K : SepOn (callKeys message state)) (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    (h7 : StrForm (storageAt state message.currentTarget 7))
    (h8 : StrForm (storageAt state message.currentTarget 8))
    {a : U256} (ha : a.toNat < 2 ^ 160) (hl : Listed message.currentTarget state a)
    (hsel : (selector message.data ≠ 0xdb006a75 ∧ selector message.data ≠ 0xf3bdc228) ∨
      callerWord message ≠ ownerOf state message.currentTarget)
    {runS : MessageRunner fork StateGasMeter bound} {m t : Evm fork StateGasMeter}
    (start : At CODE message 0 [] .empty gas state substate (Meter.toNat m))
    {within : GasMeter.gasHeld m.gas ≤ bound}
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runS m within = .ok t)
    (hok : t.error = none) : NoDec message.currentTarget (mapSlot a 2) state t.state :=
  (effect_any hfork hsize' hdep h7 h8 start hrun hok).listed K ha hl hsel

/-- **Blacklist over a sequence.** Along a finite sequence of successful calls to `C` (over the
meter `Nat` or over `StateGasMeter`, `SeqS`, round 37) by callers other than the owner (of each
call's start state) and of `Untouched` steps, from a state where `C` is not deprecated, slots 7 and
8 are of `StrForm`, and the address word `a < 2^160` is blacklisted, each call with `SecSep` of its
keys: `balances[a]` is not lower at the end. -/
theorem listed_seqS {C : Address} {S S' : State.TransactionState}
    (h : SeqS C NotOwnerK S S') (hdep : byte20 (storageAt S C 10) = 0)
    (h7 : StrForm (storageAt S C 7)) (h8 : StrForm (storageAt S C 8))
    {a : U256} (ha : a.toNat < 2 ^ 160) (hl : Listed C S a) : NoDec C (mapSlot a 2) S S' := by
  refine seqS_lift (I := fun X => Plain C X ∧ Listed C X a) (R := NoDec C (mapSlot a 2))
    (fun _ => NoDec.refl _ _ _) (fun h1 h2 => h1.trans h2)
    (fun hu hI => ⟨NoDec.of_writes (W := fun _ => False) (.of_same hu) id,
      plain_of_untouched hu hI.1, by unfold Listed; rw [hu]; exact hI.2⟩) ?_ h
    ⟨⟨hdep, h7, h8⟩, hl⟩
  intro S S' fork message hr hq hI
  obtain ⟨hno, K⟩ := hq
  obtain ⟨⟨hdep, h7, h8⟩, hl⟩ := hI
  obtain ⟨hC, he⟩ := hr.effect hdep h7 h8
  subst hC
  have hw := he.nonOwnerK K.toSepOn hno
  refine ⟨he.listed K.toSepOn ha hl (.inr hno), plain_of_writes K.toSepOn hw ⟨hdep, h7, h8⟩, ?_⟩
  unfold Listed
  rw [hw _ (protected_not_kba K (.inr (.inr (.inr (.inr (.inr ⟨a, ha, rfl⟩))))))]
  exact hl

/-- `listed_seqS` for a `Seq` (calls over the meter `Nat`). -/
theorem listed_seq {C : Address} {S S' : State.TransactionState}
    (h : Seq C NotOwnerK S S') (hdep : byte20 (storageAt S C 10) = 0)
    (h7 : StrForm (storageAt S C 7)) (h8 : StrForm (storageAt S C 8))
    {a : U256} (ha : a.toNat < 2 ^ 160) (hl : Listed C S a) : NoDec C (mapSlot a 2) S S' :=
  listed_seqS h.toS hdep h7 h8 ha hl

/-! ## Deprecated or not -/

/-- From `S` to `S'`: every address word `a < 2^160` blacklisted in `S` has a balance in `S'` not
lower than in `S`. -/
def ListedNoDec (C : Address) (S S' : State.TransactionState) : Prop :=
  ∀ a : U256, a.toNat < 2 ^ 160 → Listed C S a → NoDec C (mapSlot a 2) S S'

/-- The runner assumption of the blacklist property when deprecated: every call from `C` to the upgraded address that the code of `C` makes from `S` (`SentVia`, round 29: the caller state has the view of `S`, the message runs the code the upgraded address holds in `S`; through round 28 every message from `C` to `ua`), and
that the runner ends with no error lowers the balance of no address blacklisted in the caller
state. -/
def KeepsListed {fork : Fork} {bound : Nat} (runChild : MessageRunner fork Nat bound)
    (message : Message fork) (S : State.TransactionState) : Prop :=
  KeepsAt runChild message S (upAddr S message) (ListedNoDec message.currentTarget)

theorem EffectD.listed {S S' : State.TransactionState} (K : SepOn (callKeys message S))
    (h : EffectD runChild message S S')
    {a : U256} (ha : a.toNat < 2 ^ 160) (hl : Listed message.currentTarget S a)
    (hsel : (selector message.data ≠ 0xdb006a75 ∧ selector message.data ≠ 0xf3bdc228) ∨
      callerWord message ≠ ownerOf S message.currentTarget)
    (hk : byte20 (storageAt S message.currentTarget 10) ≠ 0 →
      KeepsListed runChild message S) :
    NoDec message.currentTarget (mapSlot a 2) S S' := by
  cases h with
  | loc h => exact h.listed K ha hl hsel
  | fwd hdep _ _ _ X hX hf =>
    exact NoDec.congr_left hX ((hk hdep).fwd hf a ha (by unfold Listed; rw [hX]; exact hl))
  | dfwd _ hs howner =>
    rcases hsel with ⟨-, hd⟩ | hno
    · exact absurd hs hd
    · exact absurd howner hno

/-- **Blacklist, one call, deprecated or not.** As `listed_call` without `hdep`: when deprecated,
the runner meets `KeepsListed` for the calls to the upgraded address (`hkeeps`). For an address
word `a < 2^160` blacklisted at the start, if the run ends with no error and it is not the owner's
redeem or destroyBlackFunds, `balances[a]` is not lower at the end. (transfer from a blacklisted
caller, and transferFrom with a blacklisted `_from`, have no successful run, deprecated or not:
`transfer_checks_all`, `transferFrom_checks_all`.) -/
theorem listed_call_all (K : SepOn (callKeys message state)) (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (h7 : StrForm (storageAt state message.currentTarget 7))
    (h8 : StrForm (storageAt state message.currentTarget 8))
    {a : U256} (ha : a.toNat < 2 ^ 160) (hl : Listed message.currentTarget state a)
    (hsel : (selector message.data ≠ 0xdb006a75 ∧ selector message.data ≠ 0xf3bdc228) ∨
      callerWord message ≠ ownerOf state message.currentTarget)
    (hkeeps : byte20 (storageAt state message.currentTarget 10) ≠ 0 →
      KeepsListed runChild message state)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) : NoDec message.currentTarget (mapSlot a 2) state s.state :=
  (effect_all hfork hsize' h7 h8 start within hrun hok).listed K ha hl hsel hkeeps

/-- **Blacklist over a sequence, deprecated or not.** Along a finite sequence of successful calls
to `C` by callers other than the owner (of each call's start state, with slots 7 and 8 of
`StrForm` there), whose runner, when `C` is deprecated at that state, meets `Keeps` for both
`ProtKept C` and `ListedNoDec C` (that is, `KeepsSlots` and `KeepsListed`), and of `Untouched`
steps, from a state where the address word `a < 2^160` is blacklisted, each call with `SecSep` of
its keys: `balances[a]` is not lower at the end. -/
theorem listed_seq_all {C : Address}
    {S S' : State.TransactionState}
    (h : SeqR C (fun X Y => ProtKept C X Y ∧ ListedNoDec C X Y) NotOwnerS S S')
    {a : U256} (ha : a.toNat < 2 ^ 160) (hl : Listed C S a) : NoDec C (mapSlot a 2) S S' := by
  refine seqR_lift (I := fun X => Listed C X a) (R := NoDec C (mapSlot a 2))
    (fun _ => NoDec.refl _ _ _) (fun h1 h2 => h1.trans h2)
    (fun hu hI => ⟨NoDec.of_writes (W := fun _ => False) (.of_same hu) id,
      by unfold Listed; rw [hu]; exact hI⟩) ?_ h hl
  intro S S' fork message hr hq hl
  obtain ⟨hno, ⟨h7, h8⟩, K⟩ := hq
  have hC : message.currentTarget = C := by obtain ⟨_, _, _, _, _, _, _, hC, -⟩ := hr; exact hC
  subst hC
  obtain ⟨-, bound, runChild, he, hk⟩ := hr.effect h7 h8
  have hprot := he.protKept K hno (fun hd => (hk hd).mono fun _ _ h => h.1)
  refine ⟨he.listed K.toSepOn ha hl (.inr hno) (fun hd => (hk hd).mono fun _ _ h => h.2), ?_⟩
  unfold Listed
  rw [hprot _ (.inr (.inr (.inr (.inr (.inr ⟨a, ha, rfl⟩)))))]
  exact hl

end UsdtVerify.Security
