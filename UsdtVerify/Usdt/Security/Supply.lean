import UsdtVerify.Usdt.Security.Allowance

/-!
# Supply: `_totalSupply` changes only through issue, redeem and destroyBlackFunds

`_totalSupply` is slot 1. With `v` the argument word 0 and `a` the argument word 0 masked to 160
bits:

- `Effect.supply` / `supply_call`: under `SepOn` of the call's keys, every successful call (not deprecated; any
  call data below 2^256 bytes, any value, any gas, static or not; slots 7 and 8 of `StrForm`)
  keeps slot 1, or it is a call by the owner of
  - issue(v): slot 1 becomes `T + v` (as numbers; the code's `require` rules out a wrap),
  - redeem(v): slot 1 becomes `T - v` (as numbers; `v ≤ T` by the code's `require`),
  - destroyBlackFunds(a): slot 1 becomes `T - balances[a]` as a 256-bit subtraction (the code's
    subtraction is unchecked; under the supply invariant `Inv` it does not wrap, see
    `Invariant.destroy_inv`),
  with `T` slot 1 and `balances[a]` at the start.
- `supply_seq`: along a finite sequence of successful calls that are none of issue, redeem and
  destroyBlackFunds (each not deprecated, with slots 7 and 8 of `StrForm` and `SepOn` of its keys,
  at its start state),
  and of `Untouched` steps, slot 1 keeps its word.

Deprecated or not (round 23): `supply_call_all` (`SupplyStepD`: `SupplyStep`, or the owner's
deprecated destroyBlackFunds, slot 1 becomes `T - d` for some word `d`) and
`supply_seq_all`, when deprecated with the runner assumption `KeepsSupply` (a call to the
upgraded address keeps slot 1 of `C`). issue and redeem do not branch on the flag: when deprecated
they are covered by `SupplyStep` with no runner assumption.

Over the EIP-8037 meter (round 37), not deprecated, any reservoir, refills allowed:
`supply_call_any`, `supply_seqS`. The `_seqS` forms take a `SeqS` (calls over `Nat` or
`StateGasMeter`); the `Seq` forms are proved from them.
-/

namespace UsdtVerify.Security

open EthLib.Base (Fork U256 Address)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open Deprecated
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

theorem Effect.supply {S S' : State.TransactionState} (K : SepOn (callKeys message S))
    (h : Effect message S S') : SupplyStep message S S' := by
  have hb1 : ¬ BalSlot 1 := fun ⟨x, hx, e⟩ => K.fixed 1 (by decide) x hx e
  cases h with
  | same h => exact .inl (h 1)
  | transferOk _ hacc _ _ _ _ hst => rw [hst]; exact .inl (writes_credited hacc _ _ 1 hb1)
  | transferFee _ hacc _ _ _ _ _ _ hst => rw [hst]; exact .inl (writes_feeState hacc _ _ 1 hb1)
  | fromOk _ hacc _ _ _ _ _ hst =>
    rw [hst]
    exact .inl (writes_creditedFK hacc 1 (fixed_not_kba K (k := 1) (by decide)))
  | fromFee _ hacc _ _ _ _ _ _ _ hst =>
    rw [hst]
    exact .inl (writes_feeStateFK K hacc 1 (fixed_not_kba K (k := 1) (by decide)))
  | approve _ hw => exact .inl (hw 1 fun e => K.allowArg.2.ne_one e.symm)
  | ownerW _ hw => exact .inl (hw 1 fun h => ownW_ne_one K h rfl)
  | issue hsel howner hacc hT _ hst =>
    refine .inr (.inl ⟨hsel, howner, ?_⟩)
    rw [hst]
    simp only [issueState]
    rw [storageAt_writeSlot_self (by acc), storageAt_writeSlot_of_ne (by acc)
      (Ne.symm (bal_ne_one K.fixed (mask_lt _)))]
    simp only [storageAt_readSlot]
    exact Summary.toNat_add_of_lt' hT
  | redeem hsel howner hacc hT _ hst =>
    refine .inr (.inr (.inl ⟨hsel, howner, ?_⟩))
    rw [hst]
    simp only [redeemState]
    rw [storageAt_writeSlot_of_ne (by acc) (Ne.symm (bal_ne_one K.fixed (mask_lt _))),
      storageAt_readSlot,
      redeemState1, storageAt_writeSlot_self (by acc), toNat_sub' hT]
    omega
  | destroy hsel howner hacc _ hst =>
    refine .inr (.inr (.inr ⟨hsel, howner, ?_⟩))
    rw [hst]
    simp only [destroyState]
    rw [storageAt_writeSlot_self (by acc), state1, storageAt_writeSlot_of_ne (by acc)
      (Ne.symm (bal_ne_one K.fixed (addrArg_lt _ _)))]
    simp only [storageAt_readSlot, dirty, balSlot]

/-- **Supply, one call.** From Berlin (Glamsterdam included), a fresh frame of `CODE` at pc 0,
static or not, any call data below 2^256 bytes, any value, any gas, any gas bound and any message
runner; not deprecated, slots 7 and 8 of `StrForm`, under `SepOn` of the call's keys: if the run
ends with no error, `_totalSupply` (slot 1) keeps its word, or the owner called issue (`+ v`), redeem
(`- v`) or destroyBlackFunds (`- balances[a]`, unchecked), as `SupplyStep` states. -/
theorem supply_call (K : SepOn (callKeys message state)) (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    (h7 : StrForm (storageAt state message.currentTarget 7))
    (h8 : StrForm (storageAt state message.currentTarget 8))
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) : SupplyStep message state s.state :=
  (effect_call hfork hsize' hdep h7 h8 start within hrun hok).supply K

/-- `supply_call` over the EIP-8037 meter (round 37): for a run of the loop over
`StateGasMeter`, any gas bound and message runner, from a frame `m` whose `toNat` is the fresh
frame of `CODE`. No hypothesis on the reservoir, on refills or on the gas limit. -/
theorem supply_call_any (K : SepOn (callKeys message state)) (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    (h7 : StrForm (storageAt state message.currentTarget 7))
    (h8 : StrForm (storageAt state message.currentTarget 8))
    {runS : MessageRunner fork StateGasMeter bound} {m t : Evm fork StateGasMeter}
    (start : At CODE message 0 [] .empty gas state substate (Meter.toNat m))
    {within : GasMeter.gasHeld m.gas ≤ bound}
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runS m within = .ok t)
    (hok : t.error = none) : SupplyStep message state t.state :=
  (effect_any hfork hsize' hdep h7 h8 start hrun hok).supply K

/-- The predicate of `supply_seq` on each call: none of issue, redeem and destroyBlackFunds, and,
at its start state, not deprecated with slots 7 and 8 of `StrForm`, and `SepOn` of its keys. -/
def NoSupplyFn {fork : Fork} (message : Message fork) (S : State.TransactionState) : Prop :=
  selector message.data ≠ 0xcc872b66 ∧ selector message.data ≠ 0xdb006a75 ∧
    selector message.data ≠ 0xf3bdc228 ∧ Plain message.currentTarget S ∧
    SepOn (callKeys message S)

/-- **Supply over a sequence.** Along a finite sequence of successful calls to `C` (over the meter
`Nat` or over `StateGasMeter`, `SeqS`, round 37) that are none of issue, redeem and
destroyBlackFunds (each not deprecated, with slots 7 and 8 of `StrForm`, at its start state, with
`SepOn` of its keys there) and of `Untouched` steps: `_totalSupply` (slot 1) keeps its word. Callers
may be the owner. -/
theorem supply_seqS {C : Address} {S S' : State.TransactionState}
    (h : SeqS C NoSupplyFn S S') : storageAt S' C 1 = storageAt S C 1 := by
  refine seqS_lift (I := fun _ => True) (R := fun X Y => storageAt Y C 1 = storageAt X C 1)
    (fun _ => rfl) (fun h1 h2 => h2.trans h1) (fun hu _ => ⟨hu 1, trivial⟩) ?_ h trivial
  intro S S' fork message hr hq _
  obtain ⟨hi, hr', hd, ⟨hdep, h7, h8⟩, K⟩ := hq
  have hC : message.currentTarget = C := hr.1
  subst hC
  obtain ⟨-, he⟩ := hr.effect hdep h7 h8
  refine ⟨?_, trivial⟩
  rcases he.supply K with h1 | ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩
  · exact h1
  · exact absurd e hi
  · exact absurd e hr'
  · exact absurd e hd

/-- `supply_seqS` for a `Seq` (calls over the meter `Nat`). -/
theorem supply_seq {C : Address} {S S' : State.TransactionState}
    (h : Seq C NoSupplyFn S S') : storageAt S' C 1 = storageAt S C 1 :=
  supply_seqS h.toS

/-! ## Deprecated or not -/

/-- Slot 1 keeps its word from `S` to `S'`. -/
def SupplyKept (C : Address) (S S' : State.TransactionState) : Prop :=
  storageAt S' C 1 = storageAt S C 1

/-- The runner assumption of the supply property when deprecated: every call from `C` to the upgraded address that the code of `C` makes from `S` (`SentVia`, round 29: the caller state has the view of `S`, the message runs the code the upgraded address holds in `S`; through round 28 every message from `C` to `ua`), and
that the runner ends with no error keeps slot 1 of `C`. -/
def KeepsSupply {fork : Fork} {bound : Nat} (runChild : MessageRunner fork Nat bound)
    (message : Message fork) (S : State.TransactionState) : Prop :=
  KeepsAt runChild message S (upAddr S message) (SupplyKept message.currentTarget)

/-- `SupplyStep`, or the owner's destroyBlackFunds when deprecated: slot 1 becomes `T - d` (a
256-bit subtraction), `T` slot 1 at the start and `d` some word (the answer of the forwarded
`balanceOf(a)`). -/
def SupplyStepD {fork : Fork} (message : Message fork) (S S' : State.TransactionState) : Prop :=
  SupplyStep message S S' ∨
  (selector message.data = 0xf3bdc228 ∧ callerWord message = ownerOf S message.currentTarget ∧
    ∃ d : U256, storageAt S' message.currentTarget 1 = sub (storageAt S message.currentTarget 1) d)

theorem EffectD.supply {S S' : State.TransactionState} (K : SepOn (callKeys message S))
    (h : EffectD runChild message S S')
    (hk : byte20 (storageAt S message.currentTarget 10) ≠ 0 →
      KeepsSupply runChild message S) :
    SupplyStepD message S S' := by
  cases h with
  | loc h => exact .inl (h.supply K)
  | fwd hdep _ _ _ X hX hf => exact .inl (.inl (((hk hdep).fwd hf).trans (hX 1)))
  | dfwd hdep hsel howner _ X Y d hX hf hacc hst =>
    refine .inr ⟨hsel, howner, d, ?_⟩
    rw [hst]
    simp only [DeprecatedDestroy.tailState]
    rw [storageAt_writeSlot_self (hasAccount_writeSlot hacc),
      storageAt_writeSlot_of_ne hacc (Ne.symm (bal_ne_one K.fixed (addrArg_lt _ _))), (hk hdep).fwd hf,
      hX]

/-- **Supply, one call, deprecated or not.** As `supply_call` without `hdep`: when deprecated, the
runner meets `KeepsSupply` for the calls to the upgraded address (`hkeeps`). If the run ends with
no error, `SupplyStepD` holds: slot 1 keeps its word, or the owner called issue, redeem or
destroyBlackFunds as in `SupplyStep`, or (deprecated) the owner called destroyBlackFunds and
slot 1 became `T - d` for some word `d`. -/
theorem supply_call_all (K : SepOn (callKeys message state)) (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (h7 : StrForm (storageAt state message.currentTarget 7))
    (h8 : StrForm (storageAt state message.currentTarget 8))
    (hkeeps : byte20 (storageAt state message.currentTarget 10) ≠ 0 →
      KeepsSupply runChild message state)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) : SupplyStepD message state s.state :=
  (effect_all hfork hsize' h7 h8 start within hrun hok).supply K hkeeps

/-- The predicate of `supply_seq_all` on each call: none of issue, redeem and destroyBlackFunds,
and slots 7 and 8 of `StrForm` and `SepOn` of its keys at its start state. -/
def NoSupplyFnS {fork : Fork} (message : Message fork) (S : State.TransactionState) : Prop :=
  selector message.data ≠ 0xcc872b66 ∧ selector message.data ≠ 0xdb006a75 ∧
    selector message.data ≠ 0xf3bdc228 ∧ Strs message S ∧ SepOn (callKeys message S)

/-- **Supply over a sequence, deprecated or not.** Along a finite sequence of successful calls to
`C` that are none of issue, redeem and destroyBlackFunds (with slots 7 and 8 of `StrForm` at each
call's start state), whose runner meets `KeepsSupply` when `C` is deprecated at that state, and
of `Untouched` steps, each call with `SepOn` of its keys: slot 1 keeps its word. Callers may be
the owner. -/
theorem supply_seq_all {C : Address} {S S' : State.TransactionState}
    (h : SeqR C (SupplyKept C) NoSupplyFnS S S') : storageAt S' C 1 = storageAt S C 1 := by
  refine seqR_lift (I := fun _ => True) (R := fun X Y => storageAt Y C 1 = storageAt X C 1)
    (fun _ => rfl) (fun h1 h2 => h2.trans h1) (fun hu _ => ⟨hu 1, trivial⟩) ?_ h trivial
  intro S S' fork message hr hq _
  obtain ⟨hi, hr', hd, ⟨h7, h8⟩, K⟩ := hq
  have hC : message.currentTarget = C := by obtain ⟨_, _, _, _, _, _, _, hC, -⟩ := hr; exact hC
  subst hC
  obtain ⟨-, bound, runChild, he, hk⟩ := hr.effect h7 h8
  refine ⟨?_, trivial⟩
  rcases he.supply K hk with (h1 | ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩) | ⟨e, -⟩
  · exact h1
  · exact absurd e hi
  · exact absurd e hr'
  · exact absurd e hd
  · exact absurd e hd

end UsdtVerify.Security
