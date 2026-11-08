import UsdtVerify.Usdt.Sanity.Calls

/-!
# Sanity: the hypotheses of the security theorems and of `inv_call_all` hold together

`OkRun M S ss`: some gas and a fresh frame of `CODE` for the message `M` in the state `S` (`At`)
from which the interpreter loop, with the interpreter's own runner `processRunner`, ends with no
error. It gives the hypotheses `start`, `within`, `hrun`, `hok` of every theorem below.

Three witnesses, at every fork from Berlin, for every block, transaction, contract address `C`
and substate, list the other hypotheses that are not about keccak:

- `transfer_witness`: `transfer(to, 1)` by `CALLER_A` from `sT` (Transfer.lean). Not deprecated,
  slots 7 and 8 of `StrForm`, the caller is not the owner, the selector is transfer's.
- `paused_witness`: `approve(s, 0)` by any caller, slot 0 holding `2^160` (paused, owner 0).
  Paused, not deprecated, slots 7 and 8 of `StrForm`.
- `listed_witness`: `approve(s, 0)` by any caller, `isBlackListed[a]` holding 2, for any
  `a < 2^160`. `Listed C S a`, not deprecated, slots 7 and 8 of `StrForm`.
- `inv_witness`: `approve(s, 1)` by any caller, every slot 0. `Inv C S`, not deprecated, not
  static, slots 7 and 8 of `StrForm`.

The `_applies` theorems apply each security theorem (`nonOwner_call`, `paused_call`,
`listed_call`, `allowKept_call`, `supply_call`, and their `_call_all` forms) and `inv_call_all` to
a witness: they take `KeccakSep` (and `AllowSep` where the theorem does) as hypotheses, and
discharge every other hypothesis. `KeccakSep` and `AllowSep` are statements about keccak; they
are not proved here.

The runs are not deprecated, so the runner assumptions of the `_call_all` forms and of
`inv_call_all` (taken only when deprecated) hold there with nothing to show; Runner.lean shows
that each of them holds for some runner. No run here is deprecated.
-/

namespace UsdtVerify.Sanity

open EthLib.Base (Fork U256 Address)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open Complete Security Invariant Owner Transfer TransferOk BlackList

variable {fork : Fork}

/-- A run of a fresh frame of `CODE` for `M` from `S` that ends with no error, with some gas,
under `processRunner`. -/
def OkRun (M : Message fork) (S : State.TransactionState) (ss : Substate) : Prop :=
  ∃ gas evm, At CODE M 0 [] .empty gas S ss evm ∧
    ∃ (within : GasMeter.gasHeld evm.gas ≤ gas) (s : Evm fork Nat),
      runFrame (step fork) (step_decreases fork) gas (processRunner fork gas) evm within =
        .ok s ∧ s.error = none

theorem strForm_zero : StrForm 0 := Or.inl rfl

theorem strForm_of {w : U256} (h : w = 256 ∨ w = 0) : StrForm w := Or.inl (low_256_or_0 h)

/-! ## transfer -/

/-- **Witness**: `transfer(to, 1)` by `CALLER_A` from `sT`. -/
theorem transfer_witness (hfork : .berlin ≤ fork) (b : BlockEnvironment fork)
    (t : TransactionEnvironment fork) (C : Address) (to : U256) (ss : Substate) :
    OkRun (mT b t C CALLER_A to) (sT b t C CALLER_A to) ss ∧
      (mT b t C CALLER_A to).data.size < 2 ^ 256 ∧
      byte20 (storageAt (sT b t C CALLER_A to) C 10) = 0 ∧
      StrForm (storageAt (sT b t C CALLER_A to) C 7) ∧
      StrForm (storageAt (sT b t C CALLER_A to) C 8) ∧
      callerWord (mT b t C CALLER_A to) ≠ ownerOf (sT b t C CALLER_A to) C ∧
      selector (mT b t C CALLER_A to).data = 0xa9059cbb := by
  have hw : ∀ n, storageAt (sT b t C CALLER_A to) C n = 256 ∨
      storageAt (sT b t C CALLER_A to) C n = 0 :=
    word_or_zero C (senderSlot (mT b t C CALLER_A to)) 256
  obtain ⟨g, s, w, hr, he⟩ := transfer_ok_sat hfork b t C CALLER_A to ss
  refine ⟨⟨g, _, at_sFrame _ rfl _ _ _, w, s, hr, he⟩, ?_, byte20_256_or_0 (hw 10),
    strForm_of (hw 7), strForm_of (hw 8), ?_, selector_dataT to 1⟩
  · rw [show (mT b t C CALLER_A to).data = dataT to 1 from rfl, size_dataT]; decide
  · show bitwiseAnd ADDR_MASK CALLER_A.toU256 ≠ bitwiseAnd ADDR_MASK _
    rw [word_A]
    rcases hw 0 with h | h <;> rw [h] <;> decide

/-! ## approve(s, 0) from a state where slot 10 is not deprecated -/

/-- The message of `approve(s, 0)` from `caller` to `C`. -/
abbrev mA0 (b : BlockEnvironment fork) (t : TransactionEnvironment fork) (C caller : Address)
    (sp : U256) : Message fork :=
  sMsg b t C caller CODE (data2 SEL_A sp 0)

/-- The gas of `approve_zero_run`. -/
abbrev gA0 (b : BlockEnvironment fork) (t : TransactionEnvironment fork) (C caller : Address)
    (sp : U256) (ss : Substate) (kvs : List (U256 × U256)) : Nat :=
  10000 + Gas.writeCost fork (originalAt (sState C kvs) C (Approve.allowArg (mA0 b t C caller sp)))
    (storageAt (sState C kvs) C (Approve.allowArg (mA0 b t C caller sp))) 0
    (coldIn (accessSlot ss C 10) C (Approve.allowArg (mA0 b t C caller sp)))

theorem approve_zero_run (hfork : .berlin ≤ fork) (b : BlockEnvironment fork)
    (t : TransactionEnvironment fork) (C caller : Address) (sp : U256) (ss : Substate)
    (kvs : List (U256 × U256)) (hdep : byte20 (storageAt (sState C kvs) C 10) = 0) :
    OkRun (mA0 b t C caller sp) (sState C kvs) ss := by
  have hct : (mA0 b t C caller sp).currentTarget = C := rfl
  obtain ⟨s, hrun, hH⟩ := Approve.runFrame_zero (fork := fork) (message := mA0 b t C caller sp)
    (state := sState C kvs) (substate := ss) hfork rfl (hasAccount_sState C _)
    (by rw [show (mA0 b t C caller sp).data = data2 SEL_A sp 0 from rfl, size_data2 size_SEL_A]
        exact Nat.le_refl _)
    (by rw [show (mA0 b t C caller sp).data = data2 SEL_A sp 0 from rfl, size_data2 size_SEL_A]
        decide)
    (by rw [show (mA0 b t C caller sp).data = data2 SEL_A sp 0 from rfl,
          selector_data2 size_SEL_A]; decide)
    rfl hdep (wordArg_data2_1 size_SEL_A sp 0) rfl rfl
    (gas := gA0 b t C caller sp ss kvs)
    (by have := slotCost_le (coldIn ss C 10); simp only [gA0, hct]; omega)
    (by have := slotCost_le (coldIn ss C 10); simp only [gA0, hct]; omega)
    (bound := gA0 b t C caller sp ss kvs) (runChild := processRunner fork _)
    (evm := sFrame (mA0 b t C caller sp) (sState C kvs) ss (gA0 b t C caller sp ss kvs))
    (at_sFrame _ rfl _ _ _) (Nat.le_refl _)
  exact ⟨gA0 b t C caller sp ss kvs, sFrame (mA0 b t C caller sp) (sState C kvs) ss
    (gA0 b t C caller sp ss kvs), at_sFrame _ rfl _ _ _, Nat.le_refl _, s, hrun,
    by obtain ⟨-, he, -⟩ := hH; simpa using he⟩

/-- The paused state: slot 0 holds `2^160` (byte 20 is 1, the owner is 0). -/
abbrev sP (C : Address) : State.TransactionState := sState C [(0, BitVec.ofNat 256 (2 ^ 160))]

/-- **Witness**: `approve(s, 0)` by any caller while paused. -/
theorem paused_witness (hfork : .berlin ≤ fork) (b : BlockEnvironment fork)
    (t : TransactionEnvironment fork) (C caller : Address) (sp : U256) (ss : Substate) :
    OkRun (mA0 b t C caller sp) (sP C) ss ∧ (mA0 b t C caller sp).data.size < 2 ^ 256 ∧
      byte20 (storageAt (sP C) C 0) ≠ 0 ∧ byte20 (storageAt (sP C) C 10) = 0 ∧
      StrForm (storageAt (sP C) C 7) ∧ StrForm (storageAt (sP C) C 8) := by
  have hz : ∀ k : U256, (0 : U256) ≠ k → storageAt (sP C) C k = 0 := by
    intro k hk
    rw [storageAt_sState_cons, storageAt_sState_nil, ite_eq_right_of_eq_false _ _ (eq_false hk)]
  have h10 := hz 10 (by decide)
  refine ⟨approve_zero_run hfork b t C caller sp ss _ (by rw [h10]; decide), ?_, ?_,
    by rw [h10]; decide, by rw [hz 7 (by decide)]; exact strForm_zero,
    by rw [hz 8 (by decide)]; exact strForm_zero⟩
  · rw [show (mA0 b t C caller sp).data = data2 SEL_A sp 0 from rfl, size_data2 size_SEL_A]
    decide
  · simp only [storageAt_sState_cons, ite_true]; decide

/-- The state of `listed_witness`: `isBlackListed[a]` holds 2. -/
abbrev sL (C : Address) (a : U256) : State.TransactionState := sState C [(mapSlot a 6, 2)]

theorem word_2_or_0 {w : U256} (h : w = 2 ∨ w = 0) : byte20 w = 0 ∧ StrForm w := by
  rcases h with h | h <;> subst h
  · exact ⟨by decide, Or.inr (Or.inl ⟨1, by decide, by decide, by decide⟩)⟩
  · exact ⟨by decide, strForm_zero⟩

/-- **Witness**: `approve(s, 0)` by any caller, with the address word `a` blacklisted. -/
theorem listed_witness (hfork : .berlin ≤ fork) (b : BlockEnvironment fork)
    (t : TransactionEnvironment fork) (C caller : Address) (sp a : U256) (ss : Substate) :
    OkRun (mA0 b t C caller sp) (sL C a) ss ∧ (mA0 b t C caller sp).data.size < 2 ^ 256 ∧
      Listed C (sL C a) a ∧ byte20 (storageAt (sL C a) C 10) = 0 ∧
      StrForm (storageAt (sL C a) C 7) ∧ StrForm (storageAt (sL C a) C 8) ∧
      selector (mA0 b t C caller sp).data = 0x095ea7b3 := by
  have hw : ∀ n, storageAt (sL C a) C n = 2 ∨ storageAt (sL C a) C n = 0 :=
    word_or_zero C (mapSlot a 6) 2
  refine ⟨approve_zero_run hfork b t C caller sp ss _ (word_2_or_0 (hw 10)).1, ?_, ?_,
    (word_2_or_0 (hw 10)).1, (word_2_or_0 (hw 7)).2, (word_2_or_0 (hw 8)).2, ?_⟩
  · rw [show (mA0 b t C caller sp).data = data2 SEL_A sp 0 from rfl, size_data2 size_SEL_A]
    decide
  · show (storageAt (sL C a) C (mapSlot a 6)).toNat % 256 ≠ 0
    simp only [storageAt_sState_cons, ite_true]; decide
  · rw [show (mA0 b t C caller sp).data = data2 SEL_A sp 0 from rfl, selector_data2 size_SEL_A]
    decide

/-! ## The invariant -/

theorem sumTo_zero (n : Nat) : sumTo (fun _ => 0) n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [sumTo, ih]

/-- `Inv` holds in the state with every slot 0. -/
theorem inv_empty (C : Address) : Invariant.Inv C (sState C []) := by
  unfold Invariant.Inv sumBal tot
  rw [sumTo_congr (g := fun _ => 0) _ (fun i _ => by simp [bal, storageAt_sState_nil]),
    sumTo_zero, storageAt_sState_nil]
  rfl

/-- **Witness**: `approve(s, 1)` by any caller from the state with every slot 0, where `Inv`
holds. -/
theorem inv_witness (hfork : .berlin ≤ fork) (b : BlockEnvironment fork)
    (t : TransactionEnvironment fork) (C caller : Address) (sp : U256) (ss : Substate) :
    OkRun (mA b t C caller sp) (sState C []) ss ∧ (mA b t C caller sp).data.size < 2 ^ 256 ∧
      (mA b t C caller sp).isStatic = false ∧ Invariant.Inv C (sState C []) ∧
      byte20 (storageAt (sState C []) C 10) = 0 ∧
      StrForm (storageAt (sState C []) C 7) ∧ StrForm (storageAt (sState C []) C 8) := by
  obtain ⟨g, s, w, hr, he⟩ := approve_set_sat hfork b t C caller sp ss
  refine ⟨⟨g, _, at_sFrame _ rfl _ _ _, w, s, hr, he⟩, ?_, rfl, inv_empty C,
    by rw [storageAt_sState_nil]; decide, by rw [storageAt_sState_nil]; exact strForm_zero,
    by rw [storageAt_sState_nil]; exact strForm_zero⟩
  rw [show (mA b t C caller sp).data = data2 SEL_A sp 1 from rfl, size_data2 size_SEL_A]
  decide

/-! ## The theorems applied -/

/-- `nonOwner_call` and `nonOwner_call_all` apply to `transfer_witness`. -/
theorem nonOwner_applies (K : KeccakSep) (A : AllowSep) (hfork : .berlin ≤ fork)
    (b : BlockEnvironment fork) (t : TransactionEnvironment fork) (C : Address) (to : U256)
    (ss : Substate) :
    ∃ s : Evm fork Nat, s.error = none ∧
      (Writes C BalOrAllow (sT b t C CALLER_A to) s.state ∧
        ∀ n, Protected n → storageAt s.state C n = storageAt (sT b t C CALLER_A to) C n) ∧
      ProtKept C (sT b t C CALLER_A to) s.state := by
  obtain ⟨⟨g, evm, hat, w, s, hr, he⟩, hsz, hdep, h7, h8, hno, -⟩ :=
    transfer_witness hfork b t C to ss
  exact ⟨s, he, nonOwner_call K A hfork hsz hdep h7 h8 hno hat w hr he,
    nonOwner_call_all K A hfork hsz h7 h8 hno (fun h => absurd hdep h) hat w hr he⟩

/-- `allowKept_call`, `allowKept_call_all`, `supply_call`, `supply_call_all` apply to
`transfer_witness`. -/
theorem allowKept_supply_applies (K : KeccakSep) (A : AllowSep) (hfork : .berlin ≤ fork)
    (b : BlockEnvironment fork) (t : TransactionEnvironment fork) (C : Address) (to : U256)
    (ss : Substate) :
    ∃ s : Evm fork Nat, s.error = none ∧
      AllowKept C (sT b t C CALLER_A to) s.state ∧
      SupplyStep (mT b t C CALLER_A to) (sT b t C CALLER_A to) s.state ∧
      SupplyStepD (mT b t C CALLER_A to) (sT b t C CALLER_A to) s.state := by
  obtain ⟨⟨g, evm, hat, w, s, hr, he⟩, hsz, hdep, h7, h8, -, hsel⟩ :=
    transfer_witness hfork b t C to ss
  have hsel' : selector (mT b t C CALLER_A to).data ≠ 0x095ea7b3 ∧
      selector (mT b t C CALLER_A to).data ≠ 0x23b872dd := by
    rw [hsel]; decide
  have := allowKept_call_all K A hfork hsz h7 h8 hsel' (fun h => absurd hdep h) hat w hr he
  exact ⟨s, he, allowKept_call K A hfork hsz hdep h7 h8 hsel' hat w hr he,
    supply_call K hfork hsz hdep h7 h8 hat w hr he,
    supply_call_all K hfork hsz h7 h8 (fun h => absurd hdep h) hat w hr he⟩

/-- `paused_call` and `paused_call_all` apply to `paused_witness`. -/
theorem paused_applies (K : KeccakSep) (hfork : .berlin ≤ fork) (b : BlockEnvironment fork)
    (t : TransactionEnvironment fork) (C caller : Address) (sp : U256) (ss : Substate) :
    ∃ s : Evm fork Nat, s.error = none ∧
      (BalKept C (sP C) s.state ∨
        (callerWord (mA0 b t C caller sp) = ownerOf (sP C) C ∧
          (selector (mA0 b t C caller sp).data = 0xcc872b66 ∨
            selector (mA0 b t C caller sp).data = 0xdb006a75 ∨
            selector (mA0 b t C caller sp).data = 0xf3bdc228))) := by
  obtain ⟨⟨g, evm, hat, w, s, hr, he⟩, hsz, hp, hdep, h7, h8⟩ :=
    paused_witness hfork b t C caller sp ss
  have := paused_call_all K hfork hsz hp h7 h8 (fun h => absurd hdep h) hat w hr he
  exact ⟨s, he, paused_call K hfork hsz hdep hp h7 h8 hat w hr he⟩

/-- `listed_call` and `listed_call_all` apply to `listed_witness`. -/
theorem listed_applies (K : KeccakSep) (hfork : .berlin ≤ fork) (b : BlockEnvironment fork)
    (t : TransactionEnvironment fork) (C caller : Address) (sp a : U256) (ha : a.toNat < 2 ^ 160)
    (ss : Substate) :
    ∃ s : Evm fork Nat, s.error = none ∧ NoDec C (mapSlot a 2) (sL C a) s.state := by
  obtain ⟨⟨g, evm, hat, w, s, hr, he⟩, hsz, hl, hdep, h7, h8, hsel⟩ :=
    listed_witness hfork b t C caller sp a ss
  have hsel' : (selector (mA0 b t C caller sp).data ≠ 0xdb006a75 ∧
      selector (mA0 b t C caller sp).data ≠ 0xf3bdc228) ∨
      callerWord (mA0 b t C caller sp) ≠ ownerOf (sL C a) C := by
    left; rw [hsel]; decide
  have := listed_call_all K hfork hsz h7 h8 ha hl hsel' (fun h => absurd hdep h) hat w hr he
  exact ⟨s, he, listed_call K hfork hsz hdep h7 h8 ha hl hsel' hat w hr he⟩

/-- `inv_call_all` (and `inv_call_ns`) apply to `inv_witness`. -/
theorem inv_applies (K : KeccakSep) (hfork : .berlin ≤ fork) (b : BlockEnvironment fork)
    (t : TransactionEnvironment fork) (C caller : Address) (sp : U256) (ss : Substate) :
    ∃ s : Evm fork Nat, s.error = none ∧ Invariant.Inv C s.state := by
  obtain ⟨⟨g, evm, hat, w, s, hr, he⟩, hsz, hst, hI, hdep, h7, h8⟩ :=
    inv_witness hfork b t C caller sp ss
  have := inv_call_ns (message := mA b t C caller sp) (state := sState C []) K hfork hsz h7 h8
    (fun h => absurd hdep h) (fun h => absurd hdep h) hI hat w hr he
  exact ⟨s, he, inv_call_all (message := mA b t C caller sp) (state := sState C []) K hfork
    (fun h => by rw [hst] at h; cases h) hsz h7 h8
    (fun h => absurd hdep h) (fun h => absurd hdep h) hI hat w hr he⟩

end UsdtVerify.Sanity
