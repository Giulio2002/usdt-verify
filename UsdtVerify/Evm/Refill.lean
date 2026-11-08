import UsdtVerify.Evm.Meter

/-!
# Where an SSTORE refills state gas

From Glamsterdam, SSTORE refills state gas (`sstoreStateRefill`) when it writes 0 over a word
that is not 0 in a slot that was 0 at the start of the transaction.
This file proves, over the meter `Nat`, that no SSTORE along a stretch of a run refills, from
facts about the two ends of the stretch only.

- `NoRefillN`, `NoRefillAtN`: `Meter.NoRefill` and `Meter.NoRefillAt` for a frame of the meter
  `Nat`.
- `sstoreStep_cases`: an SSTORE that gives a frame keeps the words before the transaction, and
  either halts with the storage as it was, or writes its word, changes no other word, and pays at
  least its state gas.
- `step_store`: a step from a `SimAt` frame keeps the words before the transaction and does not
  raise the gas, and a word of storage that it changes is the word of its SSTORE.
- `create_gas`: along `StepG`, a run that turns a word that was 0 at the start of the transaction
  and is 0 at the first frame into a word that is not 0 pays at least `STORAGE_SET_STATE_GAS`
  (97,920), from Glamsterdam.
- `noRefill_cheap`: a frame that a `StepG` chain passes, between two frames with the same
  storage, with less than 97,920 gas paid between them and no error at the end, refills nothing.
  `noRefill_cheapE` (round 39): the same when the end has an error but gas left (a revert).
- `StepI`, `HoareI`: steps over `StepG` from frames that refill nothing, and their triples.
  `HoareG.toI` and `SpecG.toI` make a triple over `StepG` one over `StepI` when its two ends
  meet the conditions of `noRefill_cheap` (`HoareG.toIE`: of `noRefill_cheapE`). `At.ruleI` and `sstoreWI` are `At.ruleG` and
  `Gas.sstoreWG` over `StepI`; `sstoreWI` asks that the write refill nothing.
- `noRefill_low`, `noRefill_run`: from a `StepI` chain to a stopped frame, from `sh k lo`, every
  running frame that the run from `lo` reaches along `Step` refills nothing.
- `ends_of_sgmN`: `Meter.ends_of_sgm` with its hypothesis on refills stated for the run of the
  meter `Nat` from `toNat m`.
- `sgm_of_reaches`: a `StepG` chain from `toNat m` to a stopped frame `z`, from reservoir 0 with no
  refill on the run from `toNat m`, gives a run of the loop over `StateGasMeter` from `m`, for any
  gas bound and message runner, that ends in a frame whose `toNat` is `z`.
-/

namespace UsdtVerify.Refill

open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open UsdtVerify.Gas
open UsdtVerify.Meter
open GasCosts

variable {fork : Fork}

/-- An SSTORE from `x` refills no state gas: for the key and the new word on top of the stack,
the refill of `sstoreStateRefill` is 0. -/
def NoRefillN (x : Evm fork Nat) : Prop :=
  ∀ key new rest, x.stack.val = key :: new :: rest →
    sstoreStateRefill fork (x.state.getStorageOriginal x.message.currentTarget key.toBeBytes)
      (x.state.getStorage x.message.currentTarget key.toBeBytes) new = 0

/-- An SSTORE at the program counter of `x`, if there is one, refills nothing. -/
def NoRefillAtN (x : Evm fork Nat) : Prop :=
  ∀ h : x.pc < x.code.size, Op.ofByte fork x.code[x.pc] = some .sstore → NoRefillN x

theorem noRefillAt_iff (m : Evm fork StateGasMeter) : NoRefillAt m ↔ NoRefillAtN (toNat m) :=
  Iff.rfl

/-- `NoRefillAtN` reads no gas. -/
theorem noRefillAtN_sh {x : Evm fork Nat} (k : Nat) (h : NoRefillAtN (sh k x)) : NoRefillAtN x :=
  h

/-- Before Glamsterdam no SSTORE refills. -/
theorem noRefillAtN_of_lt (h : fork < .glamsterdam) (x : Evm fork Nat) : NoRefillAtN x := by
  intro _ _ key new rest _
  simp only [sstoreStateRefill]
  split
  · rename_i hc
    exact absurd hc.1 (Nat.not_le_of_lt h)
  · rfl

/-! ## One step -/

theorem accessStorageKey_fields (n : Evm fork Nat) (a : EthLib.Base.Address)
    (k : EthLib.Base.Bytes32) :
    (accessStorageKey n a k).2.state = n.state ∧ (accessStorageKey n a k).2.gas = n.gas ∧
      (accessStorageKey n a k).2.running = n.running ∧
      (accessStorageKey n a k).2.message = n.message := by
  simp only [accessStorageKey]
  split <;> exact ⟨rfl, rfl, rfl, rfl⟩

theorem mapError_ok {α : Type} {r : Except EthLib.Execution.State.StateError α} {v : α}
    (h : r.mapError EvmError.state = .ok v) : r = .ok v := by
  cases r <;> simp_all [Except.mapError]

theorem chargeGas_nat {n b : Evm fork Nat} {c : Nat} (h : chargeGas n c = .ok b) :
    b = { n with gas := n.gas - c } ∧ c ≤ n.gas := by
  by_cases hl : n.gas < c
  · simp [chargeGas, GasMeter.charge, hl, bind, Except.bind] at h
  · simp [chargeGas, GasMeter.charge, hl, bind, Except.bind, pure, Except.pure] at h
    exact ⟨h.symm, by omega⟩

theorem chargeStateGas_nat {n b : Evm fork Nat} {c : Nat} (h : chargeStateGas n c = .ok b) :
    b = { n with gas := n.gas - c } ∧ c ≤ n.gas := by
  by_cases hl : n.gas < c
  · simp [chargeStateGas, GasMeter.chargeState, hl, bind, Except.bind] at h
  · simp [chargeStateGas, GasMeter.chargeState, hl, bind, Except.bind, pure, Except.pure] at h
    exact ⟨h.symm, by omega⟩

theorem popWord_with {n a : Evm fork Nat} {x : U256} (h : popWord n = .ok (x, a)) :
    ∃ st, a = { n with stack := st } := by
  obtain ⟨⟨y, st⟩, -, h⟩ := EthLib.Base.bind_ok_iff.mp h
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  exact ⟨st, h.2.symm⟩

/-- An SSTORE that gives a frame keeps the words of storage before the transaction. It either
halts with an error, no gas and the storage as it was, or it writes `new` at its key, changes no
other word and pays at least the state gas of its write. -/
theorem sstoreStep_cases {x y : Evm fork Nat} (h : sstoreStep x = .ok y) {key new : U256}
    {rest : List U256} (hs : x.stack.val = key :: new :: rest) :
    (∀ a k, y.state.getStorageOriginal a k = x.state.getStorageOriginal a k) ∧
    ((y.running = false ∧ y.error ≠ none ∧ y.gas = 0 ∧
        ∀ a k, y.state.getStorage a k = x.state.getStorage a k) ∨
      (y.running = x.running ∧
        y.state.getStorage x.message.currentTarget key.toBeBytes = new ∧
        (∀ a k, (a ≠ x.message.currentTarget ∨ k ≠ key.toBeBytes) →
          y.state.getStorage a k = x.state.getStorage a k) ∧
        y.gas + sstoreStateGas fork
          (x.state.getStorageOriginal x.message.currentTarget key.toBeBytes)
          (x.state.getStorage x.message.currentTarget key.toBeBytes) new ≤ x.gas)) := by
  unfold sstoreStep at h
  split at h
  · simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  obtain ⟨⟨w1, e1⟩, h1, h⟩ := EthLib.Base.bind_ok_iff.mp h
  obtain ⟨⟨w2, e2⟩, h2, h⟩ := EthLib.Base.bind_ok_iff.mp h
  obtain ⟨st1, rfl⟩ := popWord_with h1
  obtain ⟨st2, rfl⟩ := popWord_with h2
  have hw : w1 = key ∧ w2 = new := by
    have a1 := (EthLib.Execution.Evm.popWord_eq_ok h1).1
    have a2 := (EthLib.Execution.Evm.popWord_eq_ok h2).1
    rw [hs] at a1
    simp only [List.cons.injEq] at a1
    obtain ⟨rfl, a1⟩ := a1
    rw [← a1] at a2
    simp only [List.cons.injEq] at a2
    exact ⟨rfl, a2.1.symm⟩
  obtain ⟨rfl, rfl⟩ := hw
  dsimp only at h
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h
  rcases hacc : accessStorageKey { x with stack := st2 } x.message.currentTarget
    w1.toBeBytes with ⟨cold, e3⟩
  rw [hacc] at h
  dsimp only at h
  have hst3 : e3.state = x.state ∧ e3.gas = x.gas ∧ e3.running = x.running ∧
      e3.message = x.message := by
    have := accessStorageKey_fields { x with stack := st2 } x.message.currentTarget w1.toBeBytes
    rw [hacc] at this
    exact this
  rcases keepReads_eq_ok h with h | ⟨e, rfl⟩
  · obtain ⟨e4, h4, h⟩ := EthLib.Base.bind_ok_iff.mp h
    obtain ⟨e5, h5, h⟩ := EthLib.Base.bind_ok_iff.mp h
    obtain ⟨rfl, hc4⟩ := chargeGas_nat h4
    obtain ⟨rfl, hc5⟩ := chargeStateGas_nat h5
    split at h
    · simp [throw, throwThe, MonadExceptOf.throw] at h
    obtain ⟨st, hset, h⟩ := EthLib.Base.bind_ok_iff.mp h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    have hset' : (x.state.recordStorageRead x.message.currentTarget w1.toBeBytes).setStorage
        x.message.currentTarget w1.toBeBytes w2 = .ok st := by
      have := mapError_ok hset
      simp only [recordStorageRead, hst3.1] at this
      exact this
    refine ⟨fun a k => ?_, .inr ⟨?_, ?_, fun a k hne => ?_, ?_⟩⟩
    · show st.getStorageOriginal a k = _
      rw [EthLib.Execution.State.TransactionState.getStorageOriginal_setStorage hset']
      rfl
    · show e3.running = x.running
      exact hst3.2.2.1
    · exact EthLib.Execution.State.TransactionState.getStorage_setStorage_self hset'
    · show st.getStorage a k = _
      rw [EthLib.Execution.State.TransactionState.getStorage_setStorage_of_ne hset' hne]
      rfl
    · show e3.gas - _ - _ + _ ≤ x.gas
      simp only [refillStateGas, GasMeter.refill, recordStorageRead] at hc4 hc5 ⊢
      rw [hst3.2.1] at hc4 hc5 ⊢
      omega
  · refine ⟨fun a k => ?_, .inl ⟨rfl, by simp [exceptionalHalt], rfl, fun a k => ?_⟩⟩
    · simp only [id, exceptionalHalt, recordStorageRead, hst3.1]
      rfl
    · simp only [id, exceptionalHalt, recordStorageRead, hst3.1]
      rfl

/-- Two frames whose storage reads the same, now and before the transaction. -/
def SameStore (x y : Evm fork Nat) : Prop :=
  (∀ a k, y.state.getStorage a k = x.state.getStorage a k) ∧
    ∀ a k, y.state.getStorageOriginal a k = x.state.getStorageOriginal a k

theorem SameStore.of_state {x y : Evm fork Nat} (h : y.state = x.state) : SameStore x y := by
  rw [SameStore, h]
  exact ⟨fun _ _ => rfl, fun _ _ => rfl⟩

theorem sloadStep_same {x y : Evm fork Nat} (h : sloadStep x = .ok y) : SameStore x y := by
  obtain ⟨⟨w, e1⟩, h1, h⟩ := EthLib.Base.bind_ok_iff.mp h
  dsimp only at h
  rcases hacc : accessStorageKey e1 e1.message.currentTarget (U256.toBeBytes w) with ⟨cold, e2⟩
  simp only [hacc] at h
  obtain ⟨e3, h3, h⟩ := EthLib.Base.bind_ok_iff.mp h
  obtain ⟨e4, h4, h⟩ := EthLib.Base.bind_ok_iff.mp h
  cases h
  have s2 : e2.state = e1.state := by
    have := (accessStorageKey_fields e1 e1.message.currentTarget (U256.toBeBytes w)).1
    rwa [hacc] at this
  have s4 : e4.state = (e3.state.recordStorageRead e1.message.currentTarget w.toBeBytes) :=
    (EthLib.Execution.Evm.pushWord_sameContext h4).state
  have s3 : e3.state = e2.state := (EthLib.Execution.Evm.chargeGas_sameContext h3).state
  have s1 : e1.state = x.state := (EthLib.Execution.Evm.popWord_sameContext h1).state
  refine ⟨fun a k => ?_, fun a k => ?_⟩
  · show e4.state.getStorage a k = _
    rw [s4, ← s1, ← s2, ← s3]
    rfl
  · show e4.state.getStorageOriginal a k = _
    rw [s4, ← s1, ← s2, ← s3]
    rfl

/-- The instruction of an opcode of `simulated` other than SSTORE keeps the storage, now and
before the transaction. -/
theorem instr_same {op : Op} {run : Evm fork Nat → Except EvmError (Evm fork Nat)}
    (hs : simulated op = true) (hne : op ≠ .sstore) (hrun : instruction fork op = some run)
    {x y : Evm fork Nat} (h : run x = .ok y) : SameStore x y := by
  unfold instruction at hrun
  rcases orElse_eq_some hrun with hf | hrun
  · exact .of_state (stackOnlyStep_sameContext hf h).state
  rcases orElse_eq_some hrun with hf | hrun
  · exact .of_state (controlFlowStep_sameContext hf h).state
  rcases orElse_eq_some hrun with hf | hrun
  · exact .of_state (memoryDataStep_sameContext hf h).state
  rcases orElse_eq_some hrun with hf | hrun
  · cases op <;> simp only [returnOpStep, Option.some.injEq, reduceCtorEq] at hf
    case «return» => subst hf; exact .of_state (returnStep_sameContext h).state
    case revert =>
      split at hf
      · cases hf; exact .of_state (revertStep_sameContext h).state
      · cases hf
  rcases orElse_eq_some hrun with hf | hrun
  · exact .of_state (environmentStep_sameContext hf h).state
  rcases orElse_eq_some hrun with hf | hrun
  · cases op <;> simp only [accountStep, reduceCtorEq] at hf <;>
      simp only [simulated, Bool.false_eq_true] at hs
  rcases orElse_eq_some hrun with hf | hrun
  · cases op <;> simp only [storageStep, Option.some.injEq, reduceCtorEq] at hf
    case sload => subst hf; exact sloadStep_same h
    case sstore => exact absurd rfl hne
  rcases orElse_eq_some hrun with hf | hrun
  · cases op <;> simp only [transientStorageStep, reduceCtorEq] at hf <;>
      simp only [simulated, Bool.false_eq_true] at hs
  rcases orElse_eq_some hrun with hf | hf
  · cases op <;> simp only [logOpStep, Option.some.injEq, reduceCtorEq] at hf
    subst hf
    obtain ⟨-, -, -, -, hst, -⟩ := logStep_eq_ok h
    exact .of_state hst
  · cases op <;> simp only [selfdestructOpStep, reduceCtorEq] at hf <;>
      simp only [simulated, Bool.false_eq_true] at hs

theorem sstoreStep_stack {x y : Evm fork Nat} (h : sstoreStep x = .ok y) :
    ∃ key new rest, x.stack.val = key :: new :: rest := by
  unfold sstoreStep at h
  split at h
  · simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  obtain ⟨⟨w1, e1⟩, h1, h⟩ := EthLib.Base.bind_ok_iff.mp h
  obtain ⟨⟨w2, e2⟩, h2, -⟩ := EthLib.Base.bind_ok_iff.mp h
  have a1 := (EthLib.Execution.Evm.popWord_eq_ok h1).1
  have a2 := (EthLib.Execution.Evm.popWord_eq_ok h2).1
  exact ⟨w1, w2, e2.stack.val, by rw [a1, a2]⟩

theorem gas_le_of_next {x y : Evm fork Nat} (hr : x.running = true)
    (h : step fork x = .ok (.next y)) : y.gas ≤ x.gas := by
  have := step_decreases fork hr h
  simp only [StepResult.Decreases, EthLib.Execution.Evm.measure] at this
  change 2 * y.gas + _ < 2 * x.gas + _ at this
  rw [hr, Bool.toNat_true] at this
  omega

/-- A step from a `SimAt` frame does not raise the gas and keeps the words of storage before the
transaction. A word of storage that it changes is the word at the key of the SSTORE at its
program counter, which it sets to the new word of that SSTORE, and the step then pays at least the
state gas of that write. -/
theorem step_store {x y : Evm fork Nat} (h : Step fork x y) (hp : SimAt x) :
    y.gas ≤ x.gas ∧ (∀ a k, y.state.getStorageOriginal a k = x.state.getStorageOriginal a k) ∧
    ∀ a k, y.state.getStorage a k ≠ x.state.getStorage a k →
      ∃ key new rest, x.stack.val = key :: new :: rest ∧ a = x.message.currentTarget ∧
        k = key.toBeBytes ∧ y.state.getStorage a k = new ∧
        y.gas + sstoreStateGas fork (x.state.getStorageOriginal a k) (x.state.getStorage a k) new ≤
          x.gas := by
  cases h with
  | halt hr hs hab =>
    exact ⟨Nat.zero_le _, fun _ _ => rfl, fun _ _ hne => absurd rfl hne⟩
  | next hr hs =>
    refine ⟨gas_le_of_next hr hs, ?_⟩
    by_cases hlt : x.pc < x.code.size
    · rcases hop : Op.ofByte fork x.code[x.pc] with _ | op
      · rw [step_of_ofByte_eq_none hlt hop] at hs
        cases hs
      · obtain ⟨hsim, hi⟩ := hp hlt op hop
        obtain ⟨run, hrun⟩ := Option.isSome_iff_exists.mp hi
        rw [step_of_instruction hlt hop hrun] at hs
        rcases hx : run x with e | b
        · rw [hx] at hs; cases hs
        rw [hx] at hs
        cases hs
        by_cases hop' : op = .sstore
        · subst hop'
          rw [instruction_sstore] at hrun
          cases hrun
          obtain ⟨key, new, rest, hst⟩ := sstoreStep_stack hx
          obtain ⟨ho, hc⟩ := sstoreStep_cases hx hst
          refine ⟨ho, fun a k hne => ?_⟩
          rcases hc with ⟨-, -, -, hsame⟩ | ⟨-, hw, hother, hgas⟩
          · exact absurd (hsame a k) hne
          · by_cases hk : a = x.message.currentTarget ∧ k = key.toBeBytes
            · obtain ⟨rfl, rfl⟩ := hk
              exact ⟨key, new, rest, hst, rfl, rfl, hw, hgas⟩
            · refine absurd (hother a k ?_) hne
              by_cases ha : a = x.message.currentTarget
              · exact .inr fun hk' => hk ⟨ha, hk'⟩
              · exact .inl ha
        · have := instr_same hsim hop' hrun hx
          exact ⟨this.2, fun a k hne => absurd (this.1 a k) hne⟩
    · rw [step_of_size_le (by omega)] at hs
      cases hs
      exact ⟨fun _ _ => rfl, fun _ _ hne => absurd rfl hne⟩

/-- An SSTORE step from a `SimAt` frame either halts with an error and no gas or writes its new
word. -/
theorem step_sstore {x y : Evm fork Nat} (h : Step fork x y) (hlt : x.pc < x.code.size)
    (hop : Op.ofByte fork x.code[x.pc] = some .sstore) {key new : U256} {rest : List U256}
    (hs : x.stack.val = key :: new :: rest) :
    (y.running = false ∧ y.error ≠ none ∧ y.gas = 0) ∨
      y.state.getStorage x.message.currentTarget key.toBeBytes = new := by
  cases h with
  | halt hr hst hab => exact .inl ⟨rfl, by simp [exceptionalHalt], rfl⟩
  | next hr hst =>
    rw [step_of_instruction hlt hop instruction_sstore] at hst
    rcases hx : sstoreStep x with e | b
    · rw [hx] at hst; cases hst
    rw [hx] at hst
    cases hst
    rcases (sstoreStep_cases hx hs).2 with ⟨h1, h2, h3, -⟩ | ⟨-, hw, -⟩
    · exact .inl ⟨h1, h2, h3⟩
    · exact .inr hw

/-! ## Along a chain -/

/-- Along `StepG`, the gas does not rise and the words before the transaction stay. -/
theorem chain_store {c y : Evm fork Nat} (h : Reaches (StepG fork) c y) :
    y.gas ≤ c.gas ∧ ∀ a k, y.state.getStorageOriginal a k = c.state.getStorageOriginal a k := by
  induction h with
  | refl => exact ⟨Nat.le_refl _, fun _ _ => rfl⟩
  | step hs _ ih =>
    obtain ⟨g1, o1, -⟩ := step_store hs.1 hs.2.1
    exact ⟨Nat.le_trans ih.1 g1, fun a k => (ih.2 a k).trans (o1 a k)⟩

/-- From Glamsterdam, along `StepG`, turning a word that was 0 before the transaction and is 0 at
the first frame into a word that is not 0 pays at least `STORAGE_SET_STATE_GAS`. -/
theorem create_gas (hg : fork ≥ .glamsterdam) {c y : Evm fork Nat}
    (h : Reaches (StepG fork) c y) {a : EthLib.Base.Address} {k : EthLib.Base.Bytes32}
    (ho : c.state.getStorageOriginal a k = 0) (hc : c.state.getStorage a k = 0)
    (hy : y.state.getStorage a k ≠ 0) : y.gas + STORAGE_SET_STATE_GAS ≤ c.gas := by
  revert ho hc
  induction h with
  | refl => intro _ hc; exact absurd hc hy
  | step hs hr ih =>
    rename_i c c1 y
    intro ho hc
    obtain ⟨g1, o1, ch⟩ := step_store hs.1 hs.2.1
    have gy := (chain_store hr).1
    by_cases hc1 : c1.state.getStorage a k = 0
    · have := ih hy (by rw [o1]; exact ho) hc1
      omega
    · obtain ⟨key, new, rest, -, rfl, rfl, hw, hgas⟩ := ch _ _ (by rw [hc]; exact hc1)
      rw [ho, hc] at hgas
      have hs : sstoreStateGas fork 0 0 new = STORAGE_SET_STATE_GAS := by
        unfold sstoreStateGas
        exact ite_eq_left_iff.mpr fun hn => absurd ⟨hg, rfl, rfl, by rw [← hw]; exact hc1⟩ hn
      omega

/-- **No refill along a cheap stretch.** A frame `y` that a `StepG` chain passes from `c` to `e`,
with a step to `y1` from which the chain goes on to `e`, refills nothing at an SSTORE, when the
storage at `e` reads as at `c`, `e` has no error, and less than `STORAGE_SET_STATE_GAS` is paid
from `c` to `e`. -/
theorem noRefill_cheap {c y y1 e : Evm fork Nat} (hcy : Reaches (StepG fork) c y)
    (hy : StepG fork y y1) (hye : Reaches (StepG fork) y1 e) (herr : e.error = none)
    (hgas : c.gas < e.gas + STORAGE_SET_STATE_GAS)
    (hsame : ∀ a k, e.state.getStorage a k = c.state.getStorage a k) : NoRefillAtN y := by
  intro hlt hop key new rest hst
  apply Classical.byContradiction
  intro hR
  obtain ⟨hglam, ho, hcur, hnew⟩ := sstoreStateRefill_ne_zero hR
  obtain ⟨gcy, ocy⟩ := chain_store hcy
  obtain ⟨gye, oye⟩ := chain_store hye
  obtain ⟨gy1, oy1, -⟩ := step_store hy.1 hy.2.1
  have hoc : c.state.getStorageOriginal y.message.currentTarget key.toBeBytes = 0 := by
    rw [← ocy]; exact ho
  by_cases hc0 : c.state.getStorage y.message.currentTarget key.toBeBytes = 0
  · have := create_gas hglam hcy hoc hc0 hcur
    omega
  · rcases step_sstore hy.1 hlt hop hst with ⟨hr1, he1, -⟩ | hw
    · have := reaches_stopped (reaches_toStep hye) hr1
      rw [this] at herr
      exact he1 herr
    · rw [hnew] at hw
      have := create_gas hglam hye (by rw [oy1]; exact ho) hw (by rw [hsame]; exact hc0)
      omega

/-- `noRefill_cheap` for an end `e` that has no error or has gas left (round 39): an SSTORE
that halts leaves no gas, so the end may be a revert with gas left. -/
theorem noRefill_cheapE {c y y1 e : Evm fork Nat} (hcy : Reaches (StepG fork) c y)
    (hy : StepG fork y y1) (hye : Reaches (StepG fork) y1 e) (herr : e.error = none ∨ 0 < e.gas)
    (hgas : c.gas < e.gas + STORAGE_SET_STATE_GAS)
    (hsame : ∀ a k, e.state.getStorage a k = c.state.getStorage a k) : NoRefillAtN y := by
  intro hlt hop key new rest hst
  apply Classical.byContradiction
  intro hR
  obtain ⟨hglam, ho, hcur, hnew⟩ := sstoreStateRefill_ne_zero hR
  obtain ⟨gcy, ocy⟩ := chain_store hcy
  obtain ⟨gye, oye⟩ := chain_store hye
  obtain ⟨gy1, oy1, -⟩ := step_store hy.1 hy.2.1
  have hoc : c.state.getStorageOriginal y.message.currentTarget key.toBeBytes = 0 := by
    rw [← ocy]; exact ho
  by_cases hc0 : c.state.getStorage y.message.currentTarget key.toBeBytes = 0
  · have := create_gas hglam hcy hoc hc0 hcur
    omega
  · rcases step_sstore hy.1 hlt hop hst with ⟨hr1, he1, hg1⟩ | hw
    · have := reaches_stopped (reaches_toStep hye) hr1
      rw [this] at herr
      rcases herr with h | h
      · exact he1 h
      · rw [hg1] at h
        exact absurd h (Nat.lt_irrefl 0)
    · rw [hnew] at hw
      have := create_gas hglam hye (by rw [oy1]; exact ho) hw (by rw [hsame]; exact hc0)
      omega

/-- From Glamsterdam, a step from a `SimAt` frame that turns a word that was 0 before the
transaction and is 0 into a word that is not 0 pays at least `STORAGE_SET_STATE_GAS`, and changes
no other word. -/
theorem step_create (hg : fork ≥ .glamsterdam) {x y : Evm fork Nat} (h : Step fork x y)
    (hp : SimAt x) {a : EthLib.Base.Address} {k : EthLib.Base.Bytes32}
    (ho : x.state.getStorageOriginal a k = 0) (hc : x.state.getStorage a k = 0)
    (hy : y.state.getStorage a k ≠ 0) :
    y.gas + STORAGE_SET_STATE_GAS ≤ x.gas ∧
      ∀ b j, (b ≠ a ∨ j ≠ k) → y.state.getStorage b j = x.state.getStorage b j := by
  obtain ⟨-, -, ch⟩ := step_store h hp
  obtain ⟨key, new, rest, hst, rfl, rfl, hw, hgas⟩ := ch _ _ (by rw [hc]; exact hy)
  refine ⟨?_, fun b j hne => ?_⟩
  · rw [ho, hc] at hgas
    have hs : sstoreStateGas fork 0 0 new = STORAGE_SET_STATE_GAS := by
      unfold sstoreStateGas
      exact ite_eq_left_iff.mpr fun hn => absurd ⟨hg, rfl, rfl, by rw [← hw]; exact hy⟩ hn
    omega
  · apply Classical.byContradiction
    intro hn
    obtain ⟨key', _, _, hst', rfl, rfl, -, -⟩ := ch _ _ hn
    rw [hst] at hst'
    simp only [List.cons.injEq] at hst'
    rw [hst'.1] at hne
    rcases hne with h | h <;> exact h rfl

/-- From Glamsterdam, along `StepG`, turning two different words that were 0 before the
transaction and are 0 at the first frame into words that are not 0 pays at least twice
`STORAGE_SET_STATE_GAS`: one step writes one word. -/
theorem create2_gas (hg : fork ≥ .glamsterdam) {c y : Evm fork Nat}
    (h : Reaches (StepG fork) c y) {a a' : EthLib.Base.Address} {k k' : EthLib.Base.Bytes32}
    (hne : a ≠ a' ∨ k ≠ k')
    (ho : c.state.getStorageOriginal a k = 0) (ho' : c.state.getStorageOriginal a' k' = 0)
    (hc : c.state.getStorage a k = 0) (hc' : c.state.getStorage a' k' = 0)
    (hy : y.state.getStorage a k ≠ 0) (hy' : y.state.getStorage a' k' ≠ 0) :
    y.gas + 2 * STORAGE_SET_STATE_GAS ≤ c.gas := by
  revert ho ho' hc hc'
  induction h with
  | refl => intro _ _ hc _; exact absurd hc hy
  | step hs hr ih =>
    rename_i c c1 y
    intro ho ho' hc hc'
    obtain ⟨g1, o1, -⟩ := step_store hs.1 hs.2.1
    by_cases h1 : c1.state.getStorage a k = 0
    · by_cases h2 : c1.state.getStorage a' k' = 0
      · have := ih hy hy' (by rw [o1]; exact ho) (by rw [o1]; exact ho') h1 h2
        omega
      · obtain ⟨gs, hu⟩ := step_create hg hs.1 hs.2.1 ho' hc' h2
        have := create_gas hg hr (by rw [o1]; exact ho) h1 hy
        omega
    · obtain ⟨gs, hu⟩ := step_create hg hs.1 hs.2.1 ho hc h1
      have h2 : c1.state.getStorage a' k' = 0 := by
        rw [hu a' k' (by rcases hne with h | h; exact .inl (Ne.symm h); exact .inr (Ne.symm h))]
        exact hc'
      have := create_gas hg hr (by rw [o1]; exact ho') h2 hy'
      omega

/-- **No refill along a stretch with one write.** A frame `y` that a `StepG` chain passes from
`c` to `e`, with a step to `y1` from which the chain goes on to `e`, refills nothing at an SSTORE,
from Glamsterdam, when: the storage at `e` reads as at `c` except at the word `(T, K)`; that word
does not go from a word that is not 0 at `c` to 0 at `e` while it was 0 before the transaction;
`e` has no error; and less than `STORAGE_SET_STATE_GAS` is paid from `c` to `e`, or less than
twice that when the word goes from 0 at `c` to a word that is not 0 at `e` while it was 0 before
the transaction. -/
theorem noRefill_one (hglam : fork ≥ .glamsterdam) {c y y1 e : Evm fork Nat}
    (hcy : Reaches (StepG fork) c y) (hy : StepG fork y y1) (hye : Reaches (StepG fork) y1 e)
    (herr : e.error = none) {T : EthLib.Base.Address} {K : EthLib.Base.Bytes32}
    (hsame : ∀ a k, (a ≠ T ∨ k ≠ K) → e.state.getStorage a k = c.state.getStorage a k)
    (hA : ¬(c.state.getStorageOriginal T K = 0 ∧ c.state.getStorage T K ≠ 0 ∧
      e.state.getStorage T K = 0))
    (hgas2 : c.gas < e.gas + 2 * STORAGE_SET_STATE_GAS)
    (hgas1 : ¬(c.state.getStorageOriginal T K = 0 ∧ c.state.getStorage T K = 0 ∧
      e.state.getStorage T K ≠ 0) → c.gas < e.gas + STORAGE_SET_STATE_GAS) :
    NoRefillAtN y := by
  intro hlt hop key new rest hst
  apply Classical.byContradiction
  intro hR
  obtain ⟨-, ho, hcur, hnew⟩ := sstoreStateRefill_ne_zero hR
  obtain ⟨gcy, ocy⟩ := chain_store hcy
  obtain ⟨gye, oye⟩ := chain_store hye
  obtain ⟨gy1, oy1, chy⟩ := step_store hy.1 hy.2.1
  generalize hP : y.message.currentTarget = a at ho hcur hst
  generalize hK : key.toBeBytes = k at ho hcur
  have hoc : c.state.getStorageOriginal a k = 0 := by rw [← ocy]; exact ho
  have hy1 : y1.state.getStorage a k = 0 := by
    rcases step_sstore hy.1 hlt hop hst with ⟨hr1, he1, -⟩ | hw
    · have := reaches_stopped (reaches_toStep hye) hr1
      rw [this] at herr
      exact absurd herr he1
    · rw [← hP, ← hK, hw, hnew]
  have hoy1 : y1.state.getStorageOriginal a k = 0 := by rw [oy1]; exact ho
  have hS := Nat.zero_lt_succ 0
  by_cases hPT : a = T ∧ k = K
  · obtain ⟨rfl, rfl⟩ := hPT
    by_cases hc0 : c.state.getStorage a k = 0
    · have h1 := create_gas hglam hcy hoc hc0 hcur
      by_cases he0 : e.state.getStorage a k = 0
      · have := hgas1 fun h => h.2.2 he0
        omega
      · have h2 := create_gas hglam hye hoy1 hy1 he0
        omega
    · by_cases he0 : e.state.getStorage a k = 0
      · exact hA ⟨hoc, hc0, he0⟩
      · have h2 := create_gas hglam hye hoy1 hy1 he0
        have := hgas1 fun h => hc0 h.2.1
        omega
  · have hne : a ≠ T ∨ k ≠ K := by
      by_cases ha : a = T
      · exact .inr fun hk => hPT ⟨ha, hk⟩
      · exact .inl ha
    have hek := hsame a k hne
    by_cases hcr : c.state.getStorageOriginal T K = 0 ∧ c.state.getStorage T K = 0 ∧
        e.state.getStorage T K ≠ 0
    · obtain ⟨hoQ, hcQ, heQ⟩ := hcr
      have hy1Q : y1.state.getStorage T K = y.state.getStorage T K := by
        apply Classical.byContradiction
        intro hn
        obtain ⟨key', _, _, hst', rfl, rfl, -, -⟩ := chy _ _ hn
        rw [hst] at hst'
        simp only [List.cons.injEq] at hst'
        rw [← hst'.1, hK] at hPT
        exact hPT ⟨hP.symm, rfl⟩
      by_cases hyQ : y.state.getStorage T K = 0
      · have hQ := create_gas hglam hye (by rw [oy1, ocy]; exact hoQ) (by rw [hy1Q]; exact hyQ) heQ
        by_cases hc0 : c.state.getStorage a k = 0
        · have := create_gas hglam hcy hoc hc0 hcur
          omega
        · have := create2_gas hglam hye hne hoy1 (by rw [oy1, ocy]; exact hoQ) hy1
            (by rw [hy1Q]; exact hyQ) (by rw [hek]; exact hc0) heQ
          omega
      · by_cases hc0 : c.state.getStorage a k = 0
        · have := create2_gas hglam hcy hne hoc hoQ hc0 hcQ hcur hyQ
          omega
        · have h1 := create_gas hglam hcy hoQ hcQ hyQ
          have h2 := create_gas hglam hye hoy1 hy1 (by rw [hek]; exact hc0)
          omega
    · have := hgas1 hcr
      by_cases hc0 : c.state.getStorage a k = 0
      · have := create_gas hglam hcy hoc hc0 hcur
        omega
      · have := create_gas hglam hye hoy1 hy1 (by rw [hek]; exact hc0)
        omega

/-! ## Triples whose steps refill nothing -/

/-- A step over `StepG` from a frame where an SSTORE refills nothing. -/
def StepI (fork : Fork) (x y : Evm fork Nat) : Prop := StepG fork x y ∧ NoRefillAtN x

/-- A triple over the steps of `StepI`. -/
abbrev HoareI (fork : Fork) (P Q : Evm fork Nat → Prop) : Prop := Triple (StepI fork) P Q

instance : StepLift (StepI fork) (StepG fork) := ⟨And.left⟩

theorem reaches_liftI {c e : Evm fork Nat} (h : Reaches (StepG fork) c e)
    (hI : ∀ y y1, Reaches (StepG fork) c y → StepG fork y y1 → Reaches (StepG fork) y1 e →
      NoRefillAtN y) : Reaches (StepI fork) c e := by
  induction h with
  | refl => exact .refl _
  | step hs hr ih =>
    exact .step ⟨hs, hI _ _ (.refl _) hs hr⟩
      (ih fun y y1 hcy hy hye => hI y y1 (.step hs hcy) hy hye)

/-- **A cheap stretch.** A triple over `StepG` is one over `StepI` when, from each frame of the
precondition to each frame of the postcondition, the storage reads the same, less than
`STORAGE_SET_STATE_GAS` is paid, and the end has no error. -/
theorem HoareG.toI {P Q : Evm fork Nat → Prop} (h : HoareG fork P Q)
    (hc : ∀ c e, P c → Q e → c.gas < e.gas + STORAGE_SET_STATE_GAS ∧ e.error = none ∧
      ∀ a k, e.state.getStorage a k = c.state.getStorage a k) : HoareI fork P Q := by
  intro c hp
  obtain ⟨e, hr, hq⟩ := h c hp
  obtain ⟨hg, herr, hs⟩ := hc c e hp hq
  exact ⟨e, reaches_liftI hr fun y y1 hcy hy hye => noRefill_cheap hcy hy hye herr hg hs, hq⟩

/-- `HoareG.toI` for ends that have no error or have gas left (round 39), such as a revert. -/
theorem HoareG.toIE {P Q : Evm fork Nat → Prop} (h : HoareG fork P Q)
    (hc : ∀ c e, P c → Q e → c.gas < e.gas + STORAGE_SET_STATE_GAS ∧
      (e.error = none ∨ 0 < e.gas) ∧
      ∀ a k, e.state.getStorage a k = c.state.getStorage a k) : HoareI fork P Q := by
  intro c hp
  obtain ⟨e, hr, hq⟩ := h c hp
  obtain ⟨hg, herr, hs⟩ := hc c e hp hq
  exact ⟨e, reaches_liftI hr fun y y1 hcy hy hye => noRefill_cheapE hcy hy hye herr hg hs, hq⟩

/-- `HoareG.toI` for a specification. -/
theorem SpecG.toI {P Q : Evm fork Nat → Prop} (h : SpecG fork P Q)
    (hc : ∀ c e, P c → Q e → c.gas < e.gas + STORAGE_SET_STATE_GAS ∧ e.error = none ∧
      ∀ a k, e.state.getStorage a k = c.state.getStorage a k) :
    HoareI fork P fun evm => evm.running = false ∧ Q evm :=
  HoareG.toI h fun c e hp hq => hc c e hp hq.2

/-- A record of a read keeps every word of storage. -/
theorem getStorage_readSlot (st : State.TransactionState) (t : EthLib.Base.Address) (n : U256)
    (a : EthLib.Base.Address) (k : EthLib.Base.Bytes32) :
    (readSlot st t n).getStorage a k = st.getStorage a k := rfl

/-- `HoareG.toI` between two `At` frames: the storage of the second state reads as that of the
first, and less than 97,920 gas is paid. -/
theorem HoareG.toIA {code code' : ByteArray} {message message' : Message fork} {pc pc' : Nat}
    {stack stack' : List U256} {memory memory' : ByteArray} {g g' : Nat}
    {st st' : State.TransactionState} {ss ss' : Substate}
    (h : HoareG fork (At code message pc stack memory g st ss)
      (At code' message' pc' stack' memory' g' st' ss'))
    (hg : g < g' + 97920) (hs : ∀ a k, st'.getStorage a k = st.getStorage a k) :
    HoareI fork (At code message pc stack memory g st ss)
      (At code' message' pc' stack' memory' g' st' ss') :=
  HoareG.toI h fun c e hc he => by
    rw [hc.2.2.2.2.2.2.1, he.2.2.2.2.2.2.1, he.2.2.2.2.2.2.2.2.1, he.2.2.2.2.2.2.2.2.2.2.1,
      hc.2.2.2.2.2.2.2.2.2.2.1]
    exact ⟨hg, rfl, hs⟩

/-- `SpecG.toI` from an `At` frame to a normal halt. -/
theorem SpecG.toIA {code : ByteArray} {message : Message fork} {pc : Nat}
    {stack : List U256} {memory out : ByteArray} {g g' : Nat}
    {st st' : State.TransactionState} {ss ss' : Substate}
    (h : SpecG fork (At code message pc stack memory g st ss) (Halted false out g' st' ss'))
    (hg : g < g' + 97920) (hs : ∀ a k, st'.getStorage a k = st.getStorage a k) :
    HoareI fork (At code message pc stack memory g st ss)
      (fun evm => evm.running = false ∧ Halted false out g' st' ss' evm) :=
  SpecG.toI h fun c e hc he => by
    rw [hc.2.2.2.2.2.2.1, he.2.2.2.1, he.2.2.2.2.1, he.2.1, hc.2.2.2.2.2.2.2.2.2.2.1]
    exact ⟨hg, rfl, hs⟩

theorem if_pos' {p : Prop} [Decidable p] {α : Type} {a b : α} (h : p) :
    (if p then a else b) = a := by simp [h]

/-- Before Glamsterdam, every triple over `StepG` is one over `StepI`. -/
theorem HoareG.toI_lt (hlt : fork < .glamsterdam) {P Q : Evm fork Nat → Prop}
    (h : HoareG fork P Q) : HoareI fork P Q := fun c hp =>
  let ⟨e, hr, hq⟩ := h c hp
  ⟨e, reaches_liftI hr fun y _ _ _ _ => noRefillAtN_of_lt hlt y, hq⟩

/-- From Glamsterdam, the price of a write is at most 12,100 and its state gas. -/
theorem writeCost_le_glam (hg : fork ≥ .glamsterdam) (o c w : U256) (cold : Bool) :
    writeCost fork o c w cold ≤ 12100 + sstoreStateGas fork o c w := by
  simp only [writeCost, sstoreCost, hg, ↓reduceIte, COLD_STORAGE_ACCESS, WARM_ACCESS,
    STORAGE_WRITE]
  cases cold <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> split <;> omega

/-- **A stretch with one write over a state that reads the same.** A triple over `StepG` between
two `At` frames, whose second state is `st₁` with slot `n` of `T` written to `w`, where `st₁` reads
as the first state `st` (now: `getStorage`), is one over `StepI` when the write refills nothing,
`T` has an account in `st₁`, and the stretch pays the price of the write and at most 80,000
more. -/
theorem HoareG.toIW' {code code' : ByteArray} {message message' : Message fork} {pc pc' : Nat}
    {stack stack' : List U256} {memory memory' : ByteArray} {g d : Nat}
    {st st₁ : State.TransactionState} {ss ss' : Substate} {T : EthLib.Base.Address} {n w : U256}
    {cold : Bool}
    (h : HoareG fork (At code message pc stack memory g st ss)
      (At code' message' pc' stack' memory'
        (g - (d + writeCost fork (originalAt st T n) (storageAt st T n) w cold))
        (writeSlot st₁ T n w) ss'))
    (hS : ∀ a k, st₁.getStorage a k = st.getStorage a k)
    (hd : d ≤ 80000) (hacc : hasAccount st₁ T)
    (hle : d + writeCost fork (originalAt st T n) (storageAt st T n) w cold ≤ g)
    (hnr : sstoreStateRefill fork (originalAt st T n) (storageAt st T n) w = 0) :
    HoareI fork (At code message pc stack memory g st ss)
      (At code' message' pc' stack' memory'
        (g - (d + writeCost fork (originalAt st T n) (storageAt st T n) w cold))
        (writeSlot st₁ T n w) ss') := by
  by_cases hglam : fork ≥ .glamsterdam
  · intro c hp
    obtain ⟨e, hr, hq⟩ := h c hp
    have hcs := hp.2.2.2.2.2.2.2.2.2.2.1
    have hcg := hp.2.2.2.2.2.2.1
    have hes := hq.2.2.2.2.2.2.2.2.2.2.1
    have heg := hq.2.2.2.2.2.2.1
    have herr := hq.2.2.2.2.2.2.2.2.1
    have hw : e.state.getStorage T (U256.toBeBytes n) = w := by
      rw [hes]; exact storageAt_writeSlot_self hacc
    have hsame : ∀ a k, (a ≠ T ∨ k ≠ U256.toBeBytes n) →
        e.state.getStorage a k = c.state.getStorage a k := by
      intro a k hne
      rw [hes, hcs, State.TransactionState.getStorage_setStorage_of_ne (setStorage_writeSlot hacc)
        hne, ← hS a k]
      rfl
    have hwc := writeCost_le_glam hglam (originalAt st T n) (storageAt st T n) w cold
    have hS' : STORAGE_SET_STATE_GAS = 97920 := rfl
    have hsg : sstoreStateGas fork (originalAt st T n) (storageAt st T n) w ≤ 97920 := by
      unfold sstoreStateGas; split <;> simp [STORAGE_SET_STATE_GAS, STATE_BYTES_PER_STORAGE_SET, CPSB]
    refine ⟨e, reaches_liftI hr fun y y1 hcy hy hye =>
      noRefill_one hglam hcy hy hye herr hsame ?_ ?_ ?_, hq⟩
    · rw [hcs, hw]
      rintro ⟨h1, h2, h3⟩
      have : sstoreStateRefill fork (originalAt st T n) (storageAt st T n) w ≠ 0 := by
        unfold sstoreStateRefill
        rw [if_pos' ⟨hglam, h1, h2, h3⟩]
        decide
      exact this hnr
    · rw [hcg, heg]; omega
    · rw [hcs, hw, hcg, heg]
      intro hn
      have : sstoreStateGas fork (originalAt st T n) (storageAt st T n) w = 0 := by
        unfold sstoreStateGas
        exact ite_eq_right_iff.mpr fun h => absurd ⟨h.2.1, h.2.2.1, h.2.2.2⟩ hn
      omega
  · exact HoareG.toI_lt (Nat.lt_of_not_le hglam) h

/-- **A stretch with one write.** A triple over `StepG` between two `At` frames, whose second
state is the first one with slot `n` of `T` written to `w`, is one over `StepI` when the write
refills nothing, `T` has an account, and the stretch pays the price of the write and at most
80,000 more. -/
theorem HoareG.toIW {code code' : ByteArray} {message message' : Message fork} {pc pc' : Nat}
    {stack stack' : List U256} {memory memory' : ByteArray} {g d : Nat}
    {st : State.TransactionState} {ss ss' : Substate} {T : EthLib.Base.Address} {n w : U256}
    {cold : Bool}
    (h : HoareG fork (At code message pc stack memory g st ss)
      (At code' message' pc' stack' memory'
        (g - (d + writeCost fork (originalAt st T n) (storageAt st T n) w cold))
        (writeSlot st T n w) ss'))
    (hd : d ≤ 80000) (hacc : hasAccount st T)
    (hle : d + writeCost fork (originalAt st T n) (storageAt st T n) w cold ≤ g)
    (hnr : sstoreStateRefill fork (originalAt st T n) (storageAt st T n) w = 0) :
    HoareI fork (At code message pc stack memory g st ss)
      (At code' message' pc' stack' memory'
        (g - (d + writeCost fork (originalAt st T n) (storageAt st T n) w cold))
        (writeSlot st T n w) ss') :=
  HoareG.toIW' h (fun _ _ => rfl) hd hacc hle hnr

/-- **A stretch with one written word, from Glamsterdam.** A triple over `StepG` is one over `StepI`
when, from each frame `c` of the precondition to each frame `e` of the postcondition: `e` has no
error; the storage at `e` reads as at `c` except at the word `(T, K)`; that word does not go from
a word that is not 0 at `c` to 0 at `e` while it was 0 before the transaction; less than twice
`STORAGE_SET_STATE_GAS` is paid, and less than once unless the word goes from 0 at `c` to a word
that is not 0 at `e` while it was 0 before the transaction. -/
theorem HoareG.toI1 (hglam : fork ≥ .glamsterdam) {P Q : Evm fork Nat → Prop}
    (h : HoareG fork P Q) {T : EthLib.Base.Address} {K : EthLib.Base.Bytes32}
    (hc : ∀ c e, P c → Q e → e.error = none ∧
      (∀ a k, (a ≠ T ∨ k ≠ K) → e.state.getStorage a k = c.state.getStorage a k) ∧
      ¬(c.state.getStorageOriginal T K = 0 ∧ c.state.getStorage T K ≠ 0 ∧
        e.state.getStorage T K = 0) ∧
      c.gas < e.gas + 2 * STORAGE_SET_STATE_GAS ∧
      (¬(c.state.getStorageOriginal T K = 0 ∧ c.state.getStorage T K = 0 ∧
        e.state.getStorage T K ≠ 0) → c.gas < e.gas + STORAGE_SET_STATE_GAS)) :
    HoareI fork P Q := by
  intro c hp
  obtain ⟨e, hr, hq⟩ := h c hp
  obtain ⟨herr, hsame, hA, hg2, hg1⟩ := hc c e hp hq
  exact ⟨e, reaches_liftI hr fun y y1 hcy hy hye =>
    noRefill_one hglam hcy hy hye herr hsame hA hg2 hg1, hq⟩

/-- **A path to a halt with one write.** `HoareG.toIW'` for a specification from an `At` frame to
a normal halt: the state at the halt is `st₁` with slot `n` of `T` written to `w`, where `st₁`
reads as the first state `st`. -/
theorem SpecG.toIW' {code : ByteArray} {message : Message fork} {pc : Nat}
    {stack : List U256} {memory out : ByteArray} {g d : Nat}
    {st st₁ : State.TransactionState} {ss ss' : Substate} {T : EthLib.Base.Address} {n w : U256}
    {cold : Bool}
    (h : SpecG fork (At code message pc stack memory g st ss)
      (Halted false out (g - (d + writeCost fork (originalAt st T n) (storageAt st T n) w cold))
        (writeSlot st₁ T n w) ss'))
    (hS : ∀ a k, st₁.getStorage a k = st.getStorage a k)
    (hd : d ≤ 80000) (hacc : hasAccount st₁ T)
    (hle : d + writeCost fork (originalAt st T n) (storageAt st T n) w cold ≤ g)
    (hnr : sstoreStateRefill fork (originalAt st T n) (storageAt st T n) w = 0) :
    HoareI fork (At code message pc stack memory g st ss)
      (fun evm => evm.running = false ∧ Halted false out
        (g - (d + writeCost fork (originalAt st T n) (storageAt st T n) w cold))
        (writeSlot st₁ T n w) ss' evm) := by
  by_cases hglam : fork ≥ .glamsterdam
  · refine HoareG.toI1 hglam h (T := T) (K := U256.toBeBytes n) fun c e hp hq => ?_
    have hcs := hp.2.2.2.2.2.2.2.2.2.2.1
    have hcg := hp.2.2.2.2.2.2.1
    have hes := hq.2.2.2.2.2.1
    have heg := hq.2.2.2.2.1
    have herr := hq.2.2.1
    have hw : e.state.getStorage T (U256.toBeBytes n) = w := by
      rw [hes]; exact storageAt_writeSlot_self hacc
    have hwc := writeCost_le_glam hglam (originalAt st T n) (storageAt st T n) w cold
    have hS' : STORAGE_SET_STATE_GAS = 97920 := rfl
    have hsg : sstoreStateGas fork (originalAt st T n) (storageAt st T n) w ≤ 97920 := by
      unfold sstoreStateGas; split <;> simp [STORAGE_SET_STATE_GAS, STATE_BYTES_PER_STORAGE_SET, CPSB]
    refine ⟨by rw [herr]; rfl, fun a k hne => ?_, ?_, ?_, ?_⟩
    · rw [hes, hcs, State.TransactionState.getStorage_setStorage_of_ne (setStorage_writeSlot hacc)
        hne, ← hS a k]
      rfl
    · rw [hcs, hw]
      rintro ⟨h1, h2, h3⟩
      have : sstoreStateRefill fork (originalAt st T n) (storageAt st T n) w ≠ 0 := by
        unfold sstoreStateRefill
        rw [if_pos' ⟨hglam, h1, h2, h3⟩]
        decide
      exact this hnr
    · rw [hcg, heg]; omega
    · rw [hcs, hw, hcg, heg]
      intro hn
      have : sstoreStateGas fork (originalAt st T n) (storageAt st T n) w = 0 := by
        unfold sstoreStateGas
        exact ite_eq_right_iff.mpr fun h => absurd ⟨h.2.1, h.2.2.1, h.2.2.2⟩ hn
      omega
  · exact HoareG.toI_lt (Nat.lt_of_not_le hglam) h

/-- A write leaves every other word as it reads. -/
theorem getStorage_writeSlot_ne {st : State.TransactionState} {T : EthLib.Base.Address}
    {n w : U256} (hacc : hasAccount st T) {a : EthLib.Base.Address} {k : EthLib.Base.Bytes32}
    (hne : a ≠ T ∨ k ≠ U256.toBeBytes n) :
    (writeSlot st T n w).getStorage a k = st.getStorage a k := by
  rw [State.TransactionState.getStorage_setStorage_of_ne (setStorage_writeSlot hacc) hne]
  rfl

/-- **A path to a halt that changes one word.** A specification over `StepG` from an `At` frame
with state `st` to a normal halt with state `st'` is one over `StepI` when `st'` reads as `st`
except at slot `n` of `T` and, from Glamsterdam: that slot does not go from a word that is not 0
to 0 while it was 0 before the transaction; the path pays less than twice
`STORAGE_SET_STATE_GAS`, and less than once unless that slot goes from 0 to a word that is not 0
while it was 0 before the transaction. -/
theorem SpecG.toIS {code : ByteArray} {message : Message fork} {pc : Nat}
    {stack : List U256} {memory out : ByteArray} {g g' : Nat}
    {st st' : State.TransactionState} {ss ss' : Substate} {T : EthLib.Base.Address} {n : U256}
    (h : SpecG fork (At code message pc stack memory g st ss) (Halted false out g' st' ss'))
    (hsame : ∀ a k, (a ≠ T ∨ k ≠ U256.toBeBytes n) → st'.getStorage a k = st.getStorage a k)
    (hA : fork ≥ .glamsterdam →
      ¬(originalAt st T n = 0 ∧ storageAt st T n ≠ 0 ∧ storageAt st' T n = 0))
    (hg2 : fork ≥ .glamsterdam → g < g' + 2 * STORAGE_SET_STATE_GAS)
    (hg1 : fork ≥ .glamsterdam →
      ¬(originalAt st T n = 0 ∧ storageAt st T n = 0 ∧ storageAt st' T n ≠ 0) →
      g < g' + STORAGE_SET_STATE_GAS) :
    HoareI fork (At code message pc stack memory g st ss)
      (fun evm => evm.running = false ∧ Halted false out g' st' ss' evm) := by
  by_cases hglam : fork ≥ .glamsterdam
  · refine HoareG.toI1 hglam h (T := T) (K := U256.toBeBytes n) fun c e hp hq => ?_
    have hcs := hp.2.2.2.2.2.2.2.2.2.2.1
    have hcg := hp.2.2.2.2.2.2.1
    have hes := hq.2.2.2.2.2.1
    have heg := hq.2.2.2.2.1
    have herr := hq.2.2.1
    refine ⟨by rw [herr]; rfl, fun a k hne => ?_, ?_, ?_, ?_⟩
    · rw [hes, hcs]; exact hsame a k hne
    · rw [hcs, hes]; exact hA hglam
    · rw [hcg, heg]; exact hg2 hglam
    · rw [hcs, hes, hcg, heg]; exact hg1 hglam
  · exact HoareG.toI_lt (Nat.lt_of_not_le hglam) h

/-- From Glamsterdam, a write whose state gas is 0 costs at most 22,100. -/
theorem writeCost_le_of_no_create (hg : fork ≥ .glamsterdam) (o c w : U256) (cold : Bool)
    (h : ¬(o = 0 ∧ c = 0 ∧ w ≠ 0)) : writeCost fork o c w cold ≤ 22100 := by
  have hs : sstoreStateGas fork o c w = 0 := by
    unfold sstoreStateGas
    exact ite_eq_right_iff.mpr fun h' => absurd ⟨h'.2.1, h'.2.2.1, h'.2.2.2⟩ h
  have := writeCost_le_glam hg o c w cold
  omega

/-- From Glamsterdam, a write costs at most 110,020: 12,100 and `STORAGE_SET_STATE_GAS`. -/
theorem writeCost_le_max (hg : fork ≥ .glamsterdam) (o c w : U256) (cold : Bool) :
    writeCost fork o c w cold ≤ 12100 + STORAGE_SET_STATE_GAS := by
  have := writeCost_le_glam hg o c w cold
  have hsg : sstoreStateGas fork o c w ≤ STORAGE_SET_STATE_GAS := by
    unfold sstoreStateGas; split <;> simp [STORAGE_SET_STATE_GAS, STATE_BYTES_PER_STORAGE_SET, CPSB]
  omega

/-- The exponent of a word has at most 32 bytes. -/
theorem exponentBytes_le (x : U256) : exponentBytes x ≤ 32 := by
  unfold exponentBytes bitLength
  split
  · omega
  · have := (Nat.log2_lt (by assumption)).mpr x.isLt
    omega

/-- **The frames of a run that refill nothing.** If a `StepI` chain goes from `sh k lo` to a
stopped frame, then every running frame that `lo` reaches along `Step` refills nothing. The run
from `lo` has `k` less gas: up to where it fails, it follows the chain. -/
theorem noRefill_low {k : Nat} {lo z : Evm fork Nat} (h : Reaches (StepI fork) (sh k lo) z)
    (hz : z.running = false) :
    ∀ y, Reaches (Step fork) lo y → y.running = true → NoRefillAtN y := by
  intro y hy
  induction hy generalizing z with
  | refl =>
    intro hr
    cases h with
    | refl => rw [running_sh] at hz; rw [hz] at hr; cases hr
    | step hs _ => exact noRefillAtN_sh k hs.2
  | step hs1 hr1 ih =>
    rename_i lo lo1 y
    intro hyr
    have hlo : lo.running = true := hs1.running
    cases h with
    | refl => rw [running_sh, hlo] at hz; cases hz
    | step hs hr =>
      rename_i hi1
      rcases hs.1.2.2 k lo rfl with ⟨e, he⟩ | ⟨b, hb, hbr, -⟩ | ⟨b, hb, hhi⟩
      · cases hs1 with
        | next _ hn => rw [he] at hn; cases hn
        | halt _ _ _ =>
          rw [reaches_stopped hr1 rfl] at hyr
          cases hyr
      · have := Step.deterministic hs1 (.next hlo hb)
        subst this
        rw [reaches_stopped hr1 hbr, hbr] at hyr
        cases hyr
      · have e1 := Step.deterministic hs1 (.next hlo hb)
        have e2 := Step.deterministic hs.1.1 (.next (by rw [running_sh]; exact hlo) hhi)
        subst e1 e2
        exact ih hr hz hyr

/-- `noRefill_low` with no gas less. -/
theorem noRefill_run {lo z : Evm fork Nat} (h : Reaches (StepI fork) lo z)
    (hz : z.running = false) :
    ∀ y, Reaches (Step fork) lo y → y.running = true → NoRefillAtN y :=
  noRefill_low (k := 0) h hz

/-! ## Rules over `StepI` -/

section Rules

variable {code : ByteArray} {message : Message fork} {pc : Nat} {stack : List U256}
  {memory : ByteArray} {gas : Nat} {state : State.TransactionState} {substate : Substate}

/-- `At.ruleG` over `StepI`, for a precondition whose frames refill nothing. -/
theorem At.ruleI {byte : UInt8} {op : Op}
    {run : Evm fork Nat → Except EvmError (Evm fork Nat)} {post : Evm fork Nat → Prop}
    (hlt : pc < code.size) (hbyte : code[pc] = byte) (decoded : Op.ofByte fork byte = some op)
    (hrun : instruction fork op = some run) (hm : RunMono run)
    (h : ∀ evm, At code message pc stack memory gas state substate evm →
      ∃ after, run evm = .ok after ∧ post after)
    (hI : ∀ evm, At code message pc stack memory gas state substate evm → NoRefillAtN evm)
    (hsim : simulated op = true := by first | decide | rfl) :
    HoareI fork (At code message pc stack memory gas state substate) post := by
  apply Triple.of_step
  intro evm hp
  obtain ⟨after, ok, hpost⟩ := h evm hp
  refine ⟨after, ⟨⟨Step.of_code hp.2.2.2.2.2.2.2.1 hp.1 hp.2.2.2.1 hlt hbyte decoded hrun ok, ?_⟩,
    hI evm hp⟩, hpost⟩
  obtain ⟨hcode, -, -, hpc, -⟩ := hp
  subst hcode hpc
  exact gasMono_of_run hlt (by rw [hbyte]; exact decoded) hrun hm hsim

/-- `Gas.sstoreWG` over `StepI`, for a write that refills nothing. -/
theorem sstoreWI (hfork : .berlin ≤ fork) {key new : U256}
    {rest : List U256} {cold : Bool} (hlt : pc < code.size) (hbyte : code[pc] = 0x55)
    (hstatic : message.isStatic = false) (hacc : hasAccount state message.currentTarget)
    (hcold : coldIn substate message.currentTarget key = cold) (hstipend : 2300 < gas)
    (hgas : writeCost fork (originalAt state message.currentTarget key)
      (storageAt state message.currentTarget key) new cold ≤ gas)
    (hnr : sstoreStateRefill fork (originalAt state message.currentTarget key)
      (storageAt state message.currentTarget key) new = 0) :
    HoareI fork (At code message pc (key :: new :: rest) memory gas state substate)
      (At code message (pc + 1) rest memory
        (gas - writeCost fork (originalAt state message.currentTarget key)
          (storageAt state message.currentTarget key) new cold)
        (writeSlot state message.currentTarget key new)
        (storeSub fork substate message.currentTarget key
          (originalAt state message.currentTarget key)
          (storageAt state message.currentTarget key) new)) := by
  apply At.ruleI hlt hbyte (ofByte_of_decode (op := .sstore) rfl (Fork.frontier_le _))
    instruction_sstore runMono_sstore
  · rintro evm ⟨hcode, hj, hm, hpc, hst, hmem, hg, hrun, herr, hout, hs, hss⟩
    subst hm hg hs hss hcold
    obtain ⟨after, h, a1, a2, a3, a4, a5, a6, a7, a8, a9, ao, a10, a11⟩ :=
      sstoreStep_eq_any hfork hst hstatic (by simp only [CALL_STIPEND]; omega) hgas
        (setStorage_writeSlot hacc)
    exact ⟨after, h, by rw [a1, hcode], by rw [a2, hj], a3, by rw [a4, hpc], a5, by rw [a6, hmem],
      a7, by rw [a8, hrun], by rw [a9, herr], by rw [ao, hout], a10, a11⟩
  · rintro evm ⟨-, -, hm, -, hst, -, -, -, -, -, hs, -⟩ _ _ key' new' rest' hst'
    rw [hst] at hst'
    simp only [List.cons.injEq] at hst'
    obtain ⟨rfl, rfl, -⟩ := hst'
    rw [hm, hs]
    exact hnr

end Rules

end UsdtVerify.Refill

namespace UsdtVerify.Refill

open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open UsdtVerify.Gas
open UsdtVerify.Meter

variable {fork : Fork}

/-! ## Runs over the meter `StateGasMeter` -/

/-- `Meter.ends_of_sgm` with its hypothesis on refills stated for the run of the meter `Nat` from
`toNat m`: no running frame that this run reaches refills at an SSTORE. -/
theorem ends_of_sgmN {bound : Nat} {runChild : MessageRunner fork StateGasMeter bound}
    {m s : Evm fork StateGasMeter} {within : GasMeter.gasHeld m.gas ≤ bound}
    (h : Evm.runFrame (step fork) (step_decreases fork) bound runChild m within = .ok s)
    (hr : m.gas.reservoir = 0)
    (hnr : ∀ y, Reaches (Step fork) (toNat m) y → y.running = true → NoRefillAtN y) :
    Ends fork (toNat m) (toNat s) := by
  by_cases hrun : m.running = true
  · by_cases hp : SimAt (toNat m)
    · have hc := step_sim hr hp (hnr (toNat m) (.refl _) hrun)
      rcases hstep : step fork m with e | (b | ⟨c, msg, res⟩)
      · rw [hstep] at hc
        rcases hc with ⟨e', he, hN⟩ | ⟨_, he, _⟩
        · cases he
          by_cases ab : e.aborts = true
          · rw [runFrame_of_step_eq_abort hrun hstep ab] at h
            cases h
          · rw [runFrame_of_step_eq_error hrun hstep (by simpa using ab)] at h
            cases h
            exact .inl ⟨.single (.halt hrun hN (by simpa using ab)), rfl⟩
        · cases he
      · rw [hstep] at hc
        rcases hc with ⟨_, he, _⟩ | ⟨b', he, hN, hb⟩
        · cases he
        · cases he
          rw [runFrame_of_step_eq_next hrun hstep] at h
          have hs1 : Step fork (toNat m) (toNat b) := .next hrun hN
          rcases hb with hb | hb
          · have hlt : measure b < measure m := step_decreases fork hrun hstep
            rcases ends_of_sgmN h hb (fun y hy => hnr y (.step hs1 hy)) with
              ⟨hrc, hs⟩ | ⟨x, hrc, hx, hnp⟩
            · exact .inl ⟨.step hs1 hrc, hs⟩
            · exact .inr ⟨x, .step hs1 hrc, hx, hnp⟩
          · rw [runFrame_of_running_eq_false hb] at h
            cases h
            exact .inl ⟨.single hs1, hb⟩
      · rw [hstep] at hc
        rcases hc with ⟨_, he, _⟩ | ⟨_, he, _⟩ <;> cases he
    · exact .inr ⟨toNat m, .refl _, hrun, hp⟩
  · have hl : m.running = false := by simpa using hrun
    rw [runFrame_of_running_eq_false hl] at h
    cases h
    exact .inl ⟨.refl _, hl⟩
termination_by measure m

/-- **A run of the meter `Nat` carried to `StateGasMeter`.** If a `StepG` chain goes from
`toNat m` to a stopped frame `z`, the reservoir of `m` is 0 (or `m` is stopped), and no running
frame that the run from `toNat m` reaches refills at an SSTORE, then the loop of the interpreter
over `StateGasMeter` from `m`, for any gas bound and message runner, ends in a frame whose `toNat`
is `z`. -/
theorem sgm_of_reaches {bound : Nat} {runChild : MessageRunner fork StateGasMeter bound}
    {x z : Evm fork Nat} (hc : Reaches (StepG fork) x z) (hz : z.running = false) :
    ∀ (m : Evm fork StateGasMeter), toNat m = x → (m.gas.reservoir = 0 ∨ m.running = false) →
      (∀ y, Reaches (Step fork) x y → y.running = true → NoRefillAtN y) →
      ∀ (within : GasMeter.gasHeld m.gas ≤ bound),
      ∃ s, Evm.runFrame (step fork) (step_decreases fork) bound runChild m within = .ok s ∧
        toNat s = z := by
  induction hc with
  | refl =>
    intro m hm _ _ within
    subst hm
    exact ⟨m, runFrame_of_running_eq_false hz, rfl⟩
  | step hs hr ih =>
    rename_i x x1 z
    intro m hm hres hnr within
    subst hm
    have hrun : m.running = true := hs.1.running
    have hres' : m.gas.reservoir = 0 := by
      rcases hres with h | h
      · exact h
      · rw [h] at hrun; cases hrun
    have hcs := step_sim hres' hs.2.1 (hnr (toNat m) (.refl _) hrun)
    cases hs1 : hs.1 with
    | next _ hN =>
      rcases hcs with ⟨e, -, he⟩ | ⟨m', hS, hN', hb⟩
      · rw [hN] at he; cases he
      · rw [hN] at hN'
        cases hN'
        rw [runFrame_of_step_eq_next hrun hS]
        exact ih hz m' rfl hb (fun y hy => hnr y (.step hs.1 hy)) _
    | halt _ hN hab =>
      rcases hcs with ⟨e', hS, he⟩ | ⟨m', -, hN', -⟩
      · rw [hN] at he
        cases he
        rw [runFrame_of_step_eq_error hrun hS hab]
        refine ⟨_, rfl, ?_⟩
        rw [reaches_stopped (reaches_toStep hr) rfl]
        rfl
      · rw [hN] at hN'; cases hN'

end UsdtVerify.Refill
