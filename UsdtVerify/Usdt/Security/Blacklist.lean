import UsdtVerify.Usdt.Security.Pause

/-!
# Blacklist: a blacklisted address cannot lower its own balance

`Listed C S a`: the low byte of `isBlackListed[a]` (slot `keccak(a ++ 6)`) is not 0, as the code
tests it. The balance of `a` is the slot `keccak(a ++ 2)`.

- `Effect.listed`: under `KeccakSep`, for an address word `a < 2^160` blacklisted at the start,
  a successful call (not deprecated) does not lower the word of `balances[a]`, unless it is the
  owner's redeem or destroyBlackFunds. transfer checks the sender and transferFrom checks `_from`
  against the blacklist (so neither debits `a`); every other write to a balance adds to it
  without wrap (the recipient, the owner's fee, issue).
- `listed_call`: that for every successful call (any call data below 2^256 bytes, any value, any
  gas, static or not), not deprecated, slots 7 and 8 of `StrForm`. In particular through transfer
  and through transferFrom with `a` as `_from`.
- `listed_seq`: along a finite sequence of successful calls by callers other than the owner and of
  `Untouched` steps, from a state where `a` is blacklisted, not deprecated, slots 7 and 8 of
  `StrForm`: under `KeccakSep` and `AllowSep`, `balances[a]` never ends lower than it started (and
  `a` stays blacklisted, by `nonOwner_seq`).
-/

namespace UsdtVerify.Security

open EthLib.Base (Fork U256 Address)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
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

theorem bal_ne_of_unlisted (K : KeccakSep) {S : State.TransactionState} {C : Address} {a x : U256}
    (ha : a.toNat < 2 ^ 160) (hl : Listed C S a)
    (hx : (storageAt S C (mapSlot (bitwiseAnd ADDR_MASK x) 6)).toNat % 256 = 0) :
    mapSlot a 2 ≠ mapSlot (bitwiseAnd ADDR_MASK x) 2 := by
  intro e
  apply hl
  rw [K.inj _ _ ha (mask_lt _) e]
  exact hx

/-- A blacklisted address word `a` keeps at least its balance over a successful call that is not
the owner's redeem or destroyBlackFunds. -/
theorem Effect.listed (K : KeccakSep) {S S' : State.TransactionState} (h : Effect message S S')
    {a : U256} (ha : a.toNat < 2 ^ 160) (hl : Listed message.currentTarget S a)
    (hsel : (selector message.data ≠ 0xdb006a75 ∧ selector message.data ≠ 0xf3bdc228) ∨
      callerWord message ≠ ownerOf S message.currentTarget) :
    NoDec message.currentTarget (mapSlot a 2) S S' := by
  have h1 : mapSlot a 2 ≠ 1 := bal_ne_one K a
  cases h with
  | same h => unfold NoDec; rw [h]; exact Nat.le_refl _
  | transferOk _ hacc _ hblack _ hto hst =>
    have hne : mapSlot a 2 ≠ senderSlot message := bal_ne_of_unlisted K ha hl hblack
    rw [hst]; ndchain
  | transferFee _ hacc _ hblack _ _ hto hown hst =>
    have hne : mapSlot a 2 ≠ senderSlot message := bal_ne_of_unlisted K ha hl hblack
    rw [hst]; ndchain
  | fromOk _ hacc _ hblack _ _ hto hst =>
    have hne : mapSlot a 2 ≠ recipientSlot (fromArg message) := bal_ne_of_unlisted K ha hl hblack
    have hneA : mapSlot a 2 ≠ allowFrom message (fromArg message) := K.allow a _ _
    rw [hst]; ndchain
  | fromFee _ hacc _ hblack _ _ _ hto hown hst =>
    have hne : mapSlot a 2 ≠ recipientSlot (fromArg message) := bal_ne_of_unlisted K ha hl hblack
    have hneA : mapSlot a 2 ≠ allowFrom message (fromArg message) := K.allow a _ _
    rw [hst]; ndchain
  | approve _ hw => exact NoDec.of_writes hw fun e => K.allow a _ _ e
  | ownerW _ hw => exact NoDec.of_writes hw (bal_not_ownW K ⟨a, ha, rfl⟩)
  | issue _ _ hacc hT hB hst =>
    have hT' : (storageAt (issueState1 S message) message.currentTarget 1).toNat +
        (wordArg message.data 0).toNat < 2 ^ 256 := by
      rw [storageAt_writeSlot_of_ne (by acc) (Ne.symm (bal_ne_one K _))]
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
runner; not deprecated, slots 7 and 8 of `StrForm`, under `KeccakSep`: for an address word
`a < 2^160` blacklisted at the start, if the run ends with no error and it is not the owner's
redeem or destroyBlackFunds (`hsel`), `balances[a]` is not lower at the end. -/
theorem listed_call (K : KeccakSep) (hfork : .berlin ≤ fork)
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

/-- **Blacklist over a sequence.** Along a finite sequence of successful calls to `C` by callers
other than the owner (of each call's start state) and of `Untouched` steps, from a state where
`C` is not deprecated, slots 7 and 8 are of `StrForm`, and the address word `a < 2^160` is
blacklisted: under `KeccakSep` and `AllowSep`, `balances[a]` is not lower at the end. -/
theorem listed_seq (K : KeccakSep) (A : AllowSep) {C : Address} {S S' : State.TransactionState}
    (h : Seq C NotOwner S S') (hdep : byte20 (storageAt S C 10) = 0)
    (h7 : StrForm (storageAt S C 7)) (h8 : StrForm (storageAt S C 8))
    {a : U256} (ha : a.toNat < 2 ^ 160) (hl : Listed C S a) : NoDec C (mapSlot a 2) S S' := by
  refine seq_lift (I := fun X => Plain C X ∧ Listed C X a) (R := NoDec C (mapSlot a 2))
    (fun _ => NoDec.refl _ _ _) (fun h1 h2 => h1.trans h2)
    (fun hu hI => ⟨NoDec.of_writes (W := fun _ => False) (.of_same hu) id,
      plain_of_untouched hu hI.1, by unfold Listed; rw [hu]; exact hI.2⟩) ?_ h
    ⟨⟨hdep, h7, h8⟩, hl⟩
  intro S S' fork message hr hq hI
  obtain ⟨⟨hdep, h7, h8⟩, hl⟩ := hI
  obtain ⟨hC, he⟩ := hr.effect hdep h7 h8
  subst hC
  have hw := he.nonOwner hq
  refine ⟨he.listed K ha hl (.inr hq), plain_of_writes K A hw ⟨hdep, h7, h8⟩, ?_⟩
  unfold Listed
  rw [hw _ (protected_not_ba K A (.inr (.inr (.inr (.inr (.inr ⟨a, rfl⟩))))))]
  exact hl

end UsdtVerify.Security
