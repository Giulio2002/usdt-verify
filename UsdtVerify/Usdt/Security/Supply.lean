import UsdtVerify.Usdt.Security.Allowance

/-!
# Supply: `_totalSupply` changes only through issue, redeem and destroyBlackFunds

`_totalSupply` is slot 1. With `v` the argument word 0 and `a` the argument word 0 masked to 160
bits:

- `Effect.supply` / `supply_call`: under `KeccakSep`, every successful call (not deprecated; any
  call data below 2^256 bytes, any value, any gas, static or not; slots 7 and 8 of `StrForm`)
  keeps slot 1, or it is a call by the owner of
  - issue(v): slot 1 becomes `T + v` (as numbers; the code's `require` rules out a wrap),
  - redeem(v): slot 1 becomes `T - v` (as numbers; `v ≤ T` by the code's `require`),
  - destroyBlackFunds(a): slot 1 becomes `T - balances[a]` as a 256-bit subtraction (the code's
    subtraction is unchecked; under the supply invariant `Inv` it does not wrap, see
    `Invariant.destroy_inv`),
  with `T` slot 1 and `balances[a]` at the start.
- `supply_seq`: along a finite sequence of successful calls that are none of issue, redeem and
  destroyBlackFunds (each not deprecated, with slots 7 and 8 of `StrForm`, at its start state),
  and of `Untouched` steps, slot 1 keeps its word.
-/

namespace UsdtVerify.Security

open EthLib.Base (Fork U256 Address)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open Invariant Complete Owner Approve Issue IssueSpec DestroySpec

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate} {bound : Nat} {runChild : MessageRunner fork Nat bound}
  {evm s : Evm fork Nat} {gas : Nat}

/-- The changes of slot 1 that a successful call can make. -/
def SupplyStep {fork : Fork} (message : Message fork) (S S' : State.TransactionState) : Prop :=
  storageAt S' message.currentTarget 1 = storageAt S message.currentTarget 1 ∨
  (selector message.data = 0xcc872b66 ∧ callerWord message = ownerOf S message.currentTarget ∧
    (storageAt S' message.currentTarget 1).toNat =
      (storageAt S message.currentTarget 1).toNat + (wordArg message.data 0).toNat) ∨
  (selector message.data = 0xdb006a75 ∧ callerWord message = ownerOf S message.currentTarget ∧
    (storageAt S' message.currentTarget 1).toNat + (wordArg message.data 0).toNat =
      (storageAt S message.currentTarget 1).toNat) ∨
  (selector message.data = 0xf3bdc228 ∧ callerWord message = ownerOf S message.currentTarget ∧
    storageAt S' message.currentTarget 1 =
      sub (storageAt S message.currentTarget 1)
        (storageAt S message.currentTarget (mapSlot (addrArg message.data 0) 2)))

theorem Effect.supply (K : KeccakSep) {S S' : State.TransactionState} (h : Effect message S S') :
    SupplyStep message S S' := by
  have hb1 : ¬ BalSlot 1 := fun hb => bal_not_fixed K hb (m := 1) (by decide) rfl
  cases h with
  | same h => exact .inl (h 1)
  | transferOk _ hacc _ _ _ _ hst => rw [hst]; exact .inl (writes_credited hacc _ _ 1 hb1)
  | transferFee _ hacc _ _ _ _ _ _ hst => rw [hst]; exact .inl (writes_feeState hacc _ _ 1 hb1)
  | fromOk _ hacc _ _ _ _ _ hst =>
    rw [hst]
    exact .inl (writes_creditedF hacc _ _ _ 1 (fun h => h.elim hb1 (fun ha => allow_ne_one K ha rfl)))
  | fromFee _ hacc _ _ _ _ _ _ _ hst =>
    rw [hst]
    exact .inl (writes_feeStateF hacc _ _ _ 1 (fun h => h.elim hb1 (fun ha => allow_ne_one K ha rfl)))
  | approve _ hw => exact .inl (hw 1 fun e => K.one_allow _ _ e.symm)
  | ownerW _ hw => exact .inl (hw 1 fun h => ownW_ne_one K h rfl)
  | issue hsel howner hacc hT _ hst =>
    refine .inr (.inl ⟨hsel, howner, ?_⟩)
    rw [hst]
    simp only [issueState]
    rw [storageAt_writeSlot_self (by acc), storageAt_writeSlot_of_ne (by acc)
      (Ne.symm (bal_ne_one K _))]
    simp only [storageAt_readSlot]
    exact Summary.toNat_add_of_lt' hT
  | redeem hsel howner hacc hT _ hst =>
    refine .inr (.inr (.inl ⟨hsel, howner, ?_⟩))
    rw [hst]
    simp only [redeemState]
    rw [storageAt_writeSlot_of_ne (by acc) (Ne.symm (bal_ne_one K _)), storageAt_readSlot,
      redeemState1, storageAt_writeSlot_self (by acc), toNat_sub' hT]
    omega
  | destroy hsel howner hacc _ hst =>
    refine .inr (.inr (.inr ⟨hsel, howner, ?_⟩))
    rw [hst]
    simp only [destroyState]
    rw [storageAt_writeSlot_self (by acc), state1, storageAt_writeSlot_of_ne (by acc)
      (Ne.symm (bal_ne_one K _))]
    simp only [storageAt_readSlot, dirty, balSlot]

/-- **Supply, one call.** From Berlin (Glamsterdam included), a fresh frame of `CODE` at pc 0,
static or not, any call data below 2^256 bytes, any value, any gas, any gas bound and any message
runner; not deprecated, slots 7 and 8 of `StrForm`, under `KeccakSep`: if the run ends with no
error, `_totalSupply` (slot 1) keeps its word, or the owner called issue (`+ v`), redeem
(`- v`) or destroyBlackFunds (`- balances[a]`, unchecked), as `SupplyStep` states. -/
theorem supply_call (K : KeccakSep) (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    (h7 : StrForm (storageAt state message.currentTarget 7))
    (h8 : StrForm (storageAt state message.currentTarget 8))
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) : SupplyStep message state s.state :=
  (effect_call hfork hsize' hdep h7 h8 start within hrun hok).supply K

/-- The predicate of `supply_seq` on each call: none of issue, redeem and destroyBlackFunds, and,
at its start state, not deprecated with slots 7 and 8 of `StrForm`. -/
def NoSupplyFn {fork : Fork} (message : Message fork) (S : State.TransactionState) : Prop :=
  selector message.data ≠ 0xcc872b66 ∧ selector message.data ≠ 0xdb006a75 ∧
    selector message.data ≠ 0xf3bdc228 ∧ Plain message.currentTarget S

/-- **Supply over a sequence.** Along a finite sequence of successful calls to `C` that are none
of issue, redeem and destroyBlackFunds (each not deprecated, with slots 7 and 8 of `StrForm`, at
its start state) and of `Untouched` steps: under `KeccakSep`, `_totalSupply` (slot 1) keeps its
word. Callers may be the owner. -/
theorem supply_seq (K : KeccakSep) {C : Address} {S S' : State.TransactionState}
    (h : Seq C NoSupplyFn S S') : storageAt S' C 1 = storageAt S C 1 := by
  refine seq_lift (I := fun _ => True) (R := fun X Y => storageAt Y C 1 = storageAt X C 1)
    (fun _ => rfl) (fun h1 h2 => h2.trans h1) (fun hu _ => ⟨hu 1, trivial⟩) ?_ h trivial
  intro S S' fork message hr hq _
  obtain ⟨hi, hr', hd, hdep, h7, h8⟩ := hq
  have hC : message.currentTarget = C := by obtain ⟨_, _, _, _, _, _, _, hC, -⟩ := hr; exact hC
  subst hC
  obtain ⟨-, he⟩ := hr.effect hdep h7 h8
  refine ⟨?_, trivial⟩
  rcases he.supply K with h1 | ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩
  · exact h1
  · exact absurd e hi
  · exact absurd e hr'
  · exact absurd e hd

end UsdtVerify.Security
