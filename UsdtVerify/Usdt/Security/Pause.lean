import UsdtVerify.Usdt.Security.Access

/-!
# Pause: no balance moves while paused, except by issue, redeem and destroyBlackFunds

`paused` is byte 20 of slot 0. `BalKept C S S'`: every slot of `balances` (of an address word
below 2^160) holds the same word in `S'` as in `S`.

- `Effect.paused`: under `KeccakSep`, a successful call (not deprecated) from a paused state
  keeps every balance, or it is a call by the owner of issue, redeem or destroyBlackFunds.
  (transfer and transferFrom revert when paused: their effects state "not paused"; approve
  writes a slot of `allowed`; the other owner functions write slots 0, 3, 4, 10 and slots of
  `isBlackListed`.)
- `paused_call`: that for every successful call (any call data below 2^256 bytes, any value, any
  gas, static or not), not deprecated, slots 7 and 8 of `StrForm`.
- `paused_seq`: along a finite sequence of successful calls by callers other than the owner and
  of `Untouched` steps, from a paused state, not deprecated, slots 7 and 8 of `StrForm`: under
  `KeccakSep` and `AllowSep`, every balance keeps its word (the flags stay as they are by
  `nonOwner_seq`).
-/

namespace UsdtVerify.Security

open EthLib.Base (Fork U256 Address)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open Invariant Complete Owner Approve

/-- Every slot of `balances` keeps its word. -/
def BalKept (C : Address) (S S' : State.TransactionState) : Prop :=
  ∀ x : U256, x.toNat < 2 ^ 160 → storageAt S' C (mapSlot x 2) = storageAt S C (mapSlot x 2)

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate} {bound : Nat} {runChild : MessageRunner fork Nat bound}
  {evm s : Evm fork Nat} {gas : Nat}

/-- From a paused state, a successful call keeps every balance, or it is the owner's issue,
redeem or destroyBlackFunds. -/
theorem Effect.paused (K : KeccakSep) {S S' : State.TransactionState} (h : Effect message S S')
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
  | approve _ hw => exact .inl fun x _ => hw _ fun e => K.allow x _ _ e
  | ownerW _ hw => exact .inl fun x hx => hw _ (bal_not_ownW K ⟨x, hx, rfl⟩)
  | issue hsel howner => exact .inr ⟨howner, .inl hsel⟩
  | redeem hsel howner => exact .inr ⟨howner, .inr (.inl hsel)⟩
  | destroy hsel howner => exact .inr ⟨howner, .inr (.inr hsel)⟩

/-- **Pause, one call.** From Berlin (Glamsterdam included), a fresh frame of `CODE` at pc 0,
static or not, any call data below 2^256 bytes, any value, any gas, any gas bound and any message
runner; not deprecated, paused (`hpaused`: byte 20 of slot 0 not 0), slots 7 and 8 of `StrForm`,
under `KeccakSep`: if the run ends with no error, every balance keeps its word, or the caller is
the owner and the function is issue, redeem or destroyBlackFunds. -/
theorem paused_call (K : KeccakSep) (hfork : .berlin ≤ fork)
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
paused, not deprecated, with slots 7 and 8 of `StrForm`: under `KeccakSep` and `AllowSep`, every
balance keeps its word. -/
theorem paused_seq (K : KeccakSep) (A : AllowSep) {C : Address} {S S' : State.TransactionState}
    (h : Seq C NotOwner S S') (hdep : byte20 (storageAt S C 10) = 0)
    (hpaused : byte20 (storageAt S C 0) ≠ 0)
    (h7 : StrForm (storageAt S C 7)) (h8 : StrForm (storageAt S C 8)) : BalKept C S S' := by
  refine seq_lift (I := fun X => Plain C X ∧ byte20 (storageAt X C 0) ≠ 0) (R := BalKept C)
    (fun _ _ _ => rfl) (fun h1 h2 x hx => (h2 x hx).trans (h1 x hx))
    (fun hu hI => ⟨fun _ _ => hu _, plain_of_untouched hu hI.1, by rw [hu]; exact hI.2⟩) ?_ h
    ⟨⟨hdep, h7, h8⟩, hpaused⟩
  intro S S' fork message hr hq hI
  obtain ⟨⟨hdep, h7, h8⟩, hp⟩ := hI
  obtain ⟨hC, he⟩ := hr.effect hdep h7 h8
  subst hC
  have hw := he.nonOwner hq
  refine ⟨?_, plain_of_writes K A hw ⟨hdep, h7, h8⟩, ?_⟩
  · rcases he.paused K hp with hk | ⟨howner, -⟩
    · exact hk
    · exact absurd howner hq
  · rw [hw 0 (fixed_not_ba K A (k := 0) (by decide))]; exact hp

end UsdtVerify.Security
