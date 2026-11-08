import UsdtVerify.Usdt.Security.Effect

/-!
# Access control: what a caller other than the owner can change

The owner is the low 160 bits of slot 0 (`ownerOf`); the caller is compared with it as the code
does (`callerWord`, the caller masked to 160 bits).

- `Effect.nonOwner`: a successful call by a caller other than the owner (not deprecated) writes
  only slots of `balances` and of `allowed` (`BalOrAllow`): every other slot of the contract holds
  the same word at the end as at the start. No keccak hypothesis.
- `nonOwner_call`: so, over every successful call by such a caller (any call data below 2^256
  bytes, any value, any gas, static or not), and under `KeccakSep` and `AllowSep`, the
  `Protected` slots keep their words: slot 0 (owner and the `paused` flag, byte 20), slot 1
  (`_totalSupply`), slots 3 and 4 (`basisPointsRate`, `maximumFee`), slot 10 (`upgradedAddress`
  and the `deprecated` flag, byte 20), and every slot of `isBlackListed`.
- `nonOwner_seq`: the same over a finite sequence (`Seq`) of successful calls, each by a caller
  other than the owner of its start state, and of `Untouched` steps, when the contract is not
  deprecated and slots 7 and 8 are of `StrForm` at the start (both kept along the sequence, as is
  the owner).

Hypotheses by name: `K : KeccakSep`, `A : AllowSep` (keccak, not proved), `hdep` (not deprecated:
byte 20 of slot 10 is 0; deprecated paths call the upgraded contract), `h7`, `h8` (`StrForm`, for
name() and symbol()), `hno` (the caller is not the owner).
-/

namespace UsdtVerify.Security

open EthLib.Base (Fork U256 Address)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open Invariant Complete Owner Approve

/-- Slots 0, 1, 3, 4, 10 and the slots of `isBlackListed`. -/
def Protected (n : U256) : Prop := n = 0 ∨ n = 1 ∨ n = 3 ∨ n = 4 ∨ n = 10 ∨ ListSlot n

theorem fixed_not_ba (K : KeccakSep) (A : AllowSep) {k : Nat} (hk : k < 11) :
    ¬ BalOrAllow (BitVec.ofNat 256 k) := by
  rintro (hb | ⟨y, z, e⟩)
  · exact bal_not_fixed K hb hk rfl
  · exact A.fixed y z k hk e.symm

theorem protected_not_ba (K : KeccakSep) (A : AllowSep) {n : U256} (h : Protected n) :
    ¬ BalOrAllow n := by
  rcases h with rfl | rfl | rfl | rfl | rfl | ⟨w, rfl⟩
  · exact fixed_not_ba K A (k := 0) (by decide)
  · exact fixed_not_ba K A (k := 1) (by decide)
  · exact fixed_not_ba K A (k := 3) (by decide)
  · exact fixed_not_ba K A (k := 4) (by decide)
  · exact fixed_not_ba K A (k := 10) (by decide)
  · rintro (hb | ⟨y, z, e⟩)
    · exact bal_not_list K hb ⟨w, rfl⟩
    · exact A.list y z w e.symm

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate} {bound : Nat} {runChild : MessageRunner fork Nat bound}
  {evm s : Evm fork Nat} {gas : Nat}

/-- A successful call by a caller other than the owner writes only slots of `balances` and of
`allowed`. -/
theorem Effect.nonOwner {S S' : State.TransactionState} (h : Effect message S S')
    (hno : callerWord message ≠ ownerOf S message.currentTarget) :
    Writes message.currentTarget BalOrAllow S S' := by
  cases h with
  | same h => exact .of_same h
  | transferOk _ hacc _ _ _ _ hst => rw [hst]; exact (writes_credited hacc _ _).mono fun _ h => .inl h
  | transferFee _ hacc _ _ _ _ _ _ hst =>
    rw [hst]; exact (writes_feeState hacc _ _).mono fun _ h => .inl h
  | fromOk _ hacc _ _ _ _ _ hst => rw [hst]; exact writes_creditedF hacc _ _ _
  | fromFee _ hacc _ _ _ _ _ _ _ hst => rw [hst]; exact writes_feeStateF hacc _ _ _
  | approve _ hw => exact hw.mono fun _ e => by subst e; exact .inr (allow_mk _ _)
  | ownerW howner _ => exact absurd howner hno
  | issue _ howner => exact absurd howner hno
  | redeem _ howner => exact absurd howner hno
  | destroy _ howner => exact absurd howner hno

/-- **Access control, one call.** From Berlin (Glamsterdam included), a fresh frame of `CODE` at
pc 0, static or not, any call data below 2^256 bytes, any value, any gas, any gas bound and any
message runner, not deprecated, slots 7 and 8 of `StrForm`: if the caller is not the owner and
the run ends with no error, only slots of `balances` and `allowed` change, and under `KeccakSep`
and `AllowSep` every `Protected` slot keeps its word. -/
theorem nonOwner_call (K : KeccakSep) (A : AllowSep) (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    (h7 : StrForm (storageAt state message.currentTarget 7))
    (h8 : StrForm (storageAt state message.currentTarget 8))
    (hno : callerWord message ≠ ownerOf state message.currentTarget)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) :
    Writes message.currentTarget BalOrAllow state s.state ∧
      ∀ n, Protected n → storageAt s.state message.currentTarget n =
        storageAt state message.currentTarget n := by
  have hw := (effect_call hfork hsize' hdep h7 h8 start within hrun hok).nonOwner hno
  exact ⟨hw, fun n hn => hw n (protected_not_ba K A hn)⟩

/-- The predicate of `nonOwner_seq` on each call: its caller is not the owner of its start
state. -/
def NotOwner {fork : Fork} (message : Message fork) (S : State.TransactionState) : Prop :=
  callerWord message ≠ ownerOf S message.currentTarget

/-- What `nonOwner_seq` keeps along the sequence: not deprecated, slots 7 and 8 of `StrForm`. -/
def Plain (C : Address) (S : State.TransactionState) : Prop :=
  byte20 (storageAt S C 10) = 0 ∧ StrForm (storageAt S C 7) ∧ StrForm (storageAt S C 8)

theorem plain_of_writes (K : KeccakSep) (A : AllowSep) {C : Address} {S S' : State.TransactionState}
    (hw : Writes C BalOrAllow S S') (hP : Plain C S) : Plain C S' := by
  obtain ⟨hdep, h7, h8⟩ := hP
  refine ⟨?_, ?_, ?_⟩
  · rw [hw 10 (fixed_not_ba K A (k := 10) (by decide))]; exact hdep
  · rw [hw 7 (fixed_not_ba K A (k := 7) (by decide))]; exact h7
  · rw [hw 8 (fixed_not_ba K A (k := 8) (by decide))]; exact h8

theorem plain_of_untouched {C : Address} {S S' : State.TransactionState} (hu : Untouched C S S')
    (hP : Plain C S) : Plain C S' := by
  obtain ⟨hdep, h7, h8⟩ := hP
  exact ⟨by rw [hu]; exact hdep, by rw [hu]; exact h7, by rw [hu]; exact h8⟩

/-- **Access control over a sequence.** Along a finite sequence of successful calls to `C`, each
by a caller other than the owner of its start state, and of `Untouched` steps, from a state where
`C` is not deprecated and slots 7 and 8 are of `StrForm`: under `KeccakSep` and `AllowSep`, only
slots of `balances` and `allowed` change, so every `Protected` slot (the owner, the `paused` and
`deprecated` flags, `_totalSupply`, slots 3 and 4, `upgradedAddress`, every blacklist flag) keeps
its word. -/
theorem nonOwner_seq (K : KeccakSep) (A : AllowSep) {C : Address} {S S' : State.TransactionState}
    (h : Seq C NotOwner S S') (hdep : byte20 (storageAt S C 10) = 0)
    (h7 : StrForm (storageAt S C 7)) (h8 : StrForm (storageAt S C 8)) :
    Writes C BalOrAllow S S' ∧ ∀ n, Protected n → storageAt S' C n = storageAt S C n := by
  have hw : Writes C BalOrAllow S S' := by
    refine seq_lift (I := Plain C) (R := Writes C BalOrAllow) (fun S => Writes.refl _ _ S)
      (fun h1 h2 => h1.trans h2) (fun hu hP => ⟨.of_same hu, plain_of_untouched hu hP⟩) ?_ h
      ⟨hdep, h7, h8⟩
    intro S S' fork message hr hq hP
    obtain ⟨hdep, h7, h8⟩ := hP
    obtain ⟨hC, he⟩ := hr.effect hdep h7 h8
    subst hC
    have hw := he.nonOwner hq
    exact ⟨hw, plain_of_writes K A hw ⟨hdep, h7, h8⟩⟩
  exact ⟨hw, fun n hn => hw n (protected_not_ba K A hn)⟩

end UsdtVerify.Security
