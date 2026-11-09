import UsdtVerify.Evm.Refill

/-!
# A run of the meter `StateGasMeter` followed by a run of the meter `Nat` with more gas

The meter `StateGasMeter` may have a reservoir, and SSTORE may refill it. Its run then does not
match the run of the meter `Nat` from the same gas. This file shows that it matches the run of
the meter `Nat` from more gas, in every field but the gas, as long as it does not fail.

- `budget m`: the gas left of `m`, its reservoir, and 97,920 (the state gas of one refill) for
  each unit of the measure of `m`. A step lowers the measure, so the run has fewer refills than the
  measure.
- `SstoreOk`, `sstoreAfter`: the conditions under which SSTORE completes, and the frame it gives.
  `sstoreOk_of_step` and `sstoreStep_of_ok` relate them to `sstoreStep`, for any meter, from
  Berlin.
- `runMono_of_simulated`, `lifts_of_simulated`: each opcode of `simulated` has an instruction that
  is `RunMono`; for the opcodes other than SSTORE, the instruction over `StateGasMeter` is
  `Lifts` of it.
- `shadow_step`: a step over `StateGasMeter` from a running frame at a `SimAt` opcode, to a
  running frame or one with no error, is followed by the step over `Nat` from a frame with the
  same fields and at least `budget` gas, which keeps that relation.
- `shadow_run`: if the loop over `StateGasMeter` from `m`, for any gas bound and message runner,
  ends in `s` with no error, then `Ends` holds from every frame of the meter `Nat` with the fields
  of `m` and at least `budget m` gas to a frame with the fields of `s`. No hypothesis on the
  reservoir or on refills.
-/

namespace UsdtVerify.Shadow

open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic hiding HoareG StepG
open UsdtVerify.Gas
open UsdtVerify.Meter
open GasCosts

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-- The frame that a successful SSTORE gives, for the meter `g` after its charges. -/
def sstoreAfter (evm : Evm fork Meter) (key new : U256) (st2 : Stack) (g : Meter)
    (st : State.TransactionState) : Evm fork Meter :=
  advance { evm with
    stack := st2, gas := g, state := st,
    substate := { evm.substate with
      accessedStorageKeys := evm.substate.accessedStorageKeys.insert evm.message.currentTarget
        ((evm.substate.accessedStorageKeys.getD evm.message.currentTarget ∅).insert
          (U256.toBeBytes key))
      refundCounter := evm.substate.refundCounter + sstoreRefund fork
        (evm.state.getStorageOriginal evm.message.currentTarget (U256.toBeBytes key))
        (evm.state.getStorage evm.message.currentTarget (U256.toBeBytes key)) new } }

/-- The conditions under which an SSTORE completes, with the meters `g2` after its charge of
execution gas and `g3` after its charge of state gas. -/
structure SstoreOk (evm : Evm fork Meter) (key new : U256) (st2 : Stack) (g2 g3 : Meter)
    (st : State.TransactionState) : Prop where
  stack : evm.stack.val = key :: new :: st2.val
  stipend : ¬(fork ≥ .istanbul ∧ GasMeter.gasLeft evm.gas ≤ CALL_STIPEND)
  charge : GasMeter.charge (GasMeter.refill evm.gas (sstoreStateRefill fork
      (evm.state.getStorageOriginal evm.message.currentTarget (U256.toBeBytes key))
      (evm.state.getStorage evm.message.currentTarget (U256.toBeBytes key)) new))
    (sstoreCost fork
      (evm.state.getStorageOriginal evm.message.currentTarget (U256.toBeBytes key))
      (evm.state.getStorage evm.message.currentTarget (U256.toBeBytes key)) new
      (decide (U256.toBeBytes key ∉
        evm.substate.accessedStorageKeys.getD evm.message.currentTarget ∅))) = .ok g2
  chargeState : GasMeter.chargeState g2 (sstoreStateGas fork
      (evm.state.getStorageOriginal evm.message.currentTarget (U256.toBeBytes key))
      (evm.state.getStorage evm.message.currentTarget (U256.toBeBytes key)) new) = .ok g3
  static : evm.message.isStatic = false
  set : (evm.state.recordStorageRead evm.message.currentTarget (U256.toBeBytes key)).setStorage
      evm.message.currentTarget (U256.toBeBytes key) new = .ok st

/-- An SSTORE whose conditions hold gives `sstoreAfter`, from Berlin. -/
theorem sstoreStep_of_ok (hfork : .berlin ≤ fork) {evm : Evm fork Meter} {key new : U256}
    {st2 : Stack} {g2 g3 : Meter} {st : State.TransactionState}
    (h : SstoreOk evm key new st2 g2 g3 st) :
    sstoreStep evm = .ok (sstoreAfter evm key new st2 g3 st) := by
  obtain ⟨hst, hstip, hc, hcs, hstatic, hset⟩ := h
  rcases evm with ⟨pc, ⟨l, hl⟩, memory, code, valid, gas, running, message, output, returnData,
    state, substate, error⟩
  simp only at hst hstip hc hcs hstatic hset ⊢
  subst hst
  simp only [decide_not] at hc
  simp [sstoreStep, popWord, Stack.pop, bind, Except.bind, pure, Except.pure, hstip,
    accessStorageKey, hfork, recordStorageRead, keepReads, refillStateGas, chargeGas, hc,
    chargeStateGas, hcs, hstatic, hset, Except.mapError, sstoreAfter, advance]

omit [GasMeter Meter] in
theorem popWord_withM {n a : Evm fork Meter} {x : U256} (h : popWord n = .ok (x, a)) :
    ∃ st, a = { n with stack := st } := by
  obtain ⟨⟨y, st⟩, -, h⟩ := EthLib.Base.bind_ok_iff.mp h
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  exact ⟨st, h.2.symm⟩

theorem chargeGas_withM {n b : Evm fork Meter} {c : Nat} (h : chargeGas n c = .ok b) :
    ∃ g, GasMeter.charge n.gas c = .ok g ∧ b = { n with gas := g } := by
  obtain ⟨g, hg, h⟩ := EthLib.Base.bind_ok_iff.mp h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  exact ⟨g, hg, h.symm⟩

theorem chargeStateGas_withM {n b : Evm fork Meter} {c : Nat} (h : chargeStateGas n c = .ok b) :
    ∃ g, GasMeter.chargeState n.gas c = .ok g ∧ b = { n with gas := g } := by
  obtain ⟨g, hg, h⟩ := EthLib.Base.bind_ok_iff.mp h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  exact ⟨g, hg, h.symm⟩

/-- An SSTORE that gives a running frame, from Berlin: its conditions hold, and the frame is
`sstoreAfter`. -/
theorem sstoreOk_of_step (hfork : .berlin ≤ fork) {evm after : Evm fork Meter}
    (h : sstoreStep evm = .ok after) (hr : after.running = true ∨ after.error = none) :
    ∃ key new st2 g2 g3 st, SstoreOk evm key new st2 g2 g3 st ∧
      after = sstoreAfter evm key new st2 g3 st := by
  unfold sstoreStep at h
  split at h
  · simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  obtain ⟨⟨w1, e1⟩, h1, h⟩ := EthLib.Base.bind_ok_iff.mp h
  obtain ⟨⟨w2, e2⟩, h2, h⟩ := EthLib.Base.bind_ok_iff.mp h
  have a1 := (EthLib.Execution.Evm.popWord_eq_ok h1).1
  have a2 := (EthLib.Execution.Evm.popWord_eq_ok h2).1
  obtain ⟨st1, rfl⟩ := popWord_withM h1
  obtain ⟨st2, rfl⟩ := popWord_withM h2
  dsimp only at h a2
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h
  rename_i hstip
  simp only [accessStorageKey, hfork, ↓reduceIte] at h
  rcases keepReads_eq_ok h with h | ⟨e, rfl⟩
  · obtain ⟨e4, h4, h⟩ := EthLib.Base.bind_ok_iff.mp h
    obtain ⟨e5, h5, h⟩ := EthLib.Base.bind_ok_iff.mp h
    obtain ⟨g2, hg2, rfl⟩ := chargeGas_withM h4
    obtain ⟨g3, hg3, rfl⟩ := chargeStateGas_withM h5
    split at h
    · simp [throw, throwThe, MonadExceptOf.throw] at h
    rename_i hstatic
    obtain ⟨st, hset, h⟩ := EthLib.Base.bind_ok_iff.mp h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    refine ⟨w1, w2, st2, g2, g3, st, ⟨by rw [a1, a2], hstip, hg2, hg3,
      by simpa [refillStateGas, recordStorageRead] using hstatic,
      Refill.mapError_ok hset⟩, rfl⟩
  · simp [exceptionalHalt] at hr

/-! ## The opcodes of `simulated` -/

theorem runMono_of_simulated {op : Op} (hs : simulated op = true)
    {runN : Evm fork Nat → Except EvmError (Evm fork Nat)}
    (hN : instruction (Meter := Nat) fork op = some runN) : RunMono runN := by
  cases op <;> simp only [simulated, Bool.false_eq_true] at hs
  all_goals simp only [instruction, stackOnlyStep, controlFlowStep, memoryDataStep, returnOpStep,
    environmentStep, accountStep, storageStep, transientStorageStep, logOpStep, selfdestructOpStep,
    HOrElse.hOrElse, OrElse.orElse, Option.orElse, Option.some.injEq] at hN
  case revert =>
    by_cases hb : Fork.byzantium ≤ fork
    · simp only [hb, ↓reduceIte, Option.some.injEq] at hN
      subst hN
      exact runMono_revert
    · simp only [hb, ↓reduceIte, reduceCtorEq] at hN
  all_goals subst hN
  all_goals first
    | with_reducible exact runMono_binaryOp _ _
    | with_reducible exact runMono_unaryOp _ _
    | with_reducible exact runMono_exp
    | with_reducible exact runMono_keccak256
    | with_reducible exact runMono_readFrame _ _ (fun _ _ => rfl)
    | with_reducible exact runMono_calldataload
    | with_reducible exact runMono_pop
    | with_reducible exact runMono_mload
    | with_reducible exact runMono_mstore
    | with_reducible exact runMono_sload
    | with_reducible exact runMono_sstore
    | with_reducible exact runMono_jump
    | with_reducible exact runMono_jumpi
    | with_reducible exact runMono_jumpdest
    | with_reducible exact runMono_stop
    | with_reducible exact runMono_return
    | with_reducible exact runMono_pushN _
    | with_reducible exact runMono_dupN _
    | with_reducible exact runMono_swapN _
    | with_reducible exact runMono_log _

theorem lifts_of_simulated {op : Op} (hs : simulated op = true) (hne : op ≠ .sstore)
    {runN : Evm fork Nat → Except EvmError (Evm fork Nat)}
    (hN : instruction (Meter := Nat) fork op = some runN) :
    ∃ runS, instruction (Meter := StateGasMeter) fork op = some runS ∧ Lifts runS runN := by
  cases op <;> simp only [simulated, Bool.false_eq_true] at hs
  all_goals simp only [instruction, stackOnlyStep, controlFlowStep, memoryDataStep, returnOpStep,
    environmentStep, accountStep, storageStep, transientStorageStep, logOpStep, selfdestructOpStep,
    HOrElse.hOrElse, OrElse.orElse, Option.orElse, Option.some.injEq] at hN ⊢
  case revert =>
    by_cases hb : Fork.byzantium ≤ fork
    · simp only [hb, ↓reduceIte, Option.some.injEq] at hN ⊢
      subst hN
      exact ⟨_, rfl, lifts_revertStep⟩
    · simp only [hb, ↓reduceIte, reduceCtorEq] at hN
  case sstore => exact absurd rfl hne
  all_goals subst hN
  all_goals refine ⟨_, rfl, ?_⟩
  all_goals first
    | with_reducible exact lifts_binaryOp _ _
    | with_reducible exact lifts_unaryOp _ _
    | with_reducible exact lifts_expStep
    | with_reducible exact lifts_keccak256Step
    | with_reducible exact lifts_readFrame _ _ _ (fun _ _ => rfl)
    | with_reducible exact lifts_calldataloadStep
    | with_reducible exact lifts_popStep
    | with_reducible exact lifts_mloadStep
    | with_reducible exact lifts_mstoreStep
    | with_reducible exact lifts_sloadStep
    | with_reducible exact lifts_jumpStep
    | with_reducible exact lifts_jumpiStep
    | with_reducible exact lifts_jumpdestStep
    | with_reducible exact lifts_stopStep
    | with_reducible exact lifts_returnStep
    | with_reducible exact lifts_pushN _
    | with_reducible exact lifts_dupN _
    | with_reducible exact lifts_swapN _
    | with_reducible exact lifts_logStep _

theorem instruction_sstoreM : instruction (Meter := Meter) fork .sstore = some sstoreStep := by
  simp [instruction, stackOnlyStep, controlFlowStep, memoryDataStep, returnOpStep,
    environmentStep, accountStep, storageStep, HOrElse.hOrElse, OrElse.orElse, Option.orElse]

/-! ## One step -/

/-- The gas of a frame of the meter `StateGasMeter` that a frame of the meter `Nat` must have
more of, for the run of the meter `Nat` to follow its run: the gas left, the reservoir, and the
state gas of one refill for each unit of the measure. -/
def budget (m : Evm fork StateGasMeter) : Nat :=
  m.gas.gasLeft + m.gas.reservoir + STORAGE_SET_STATE_GAS * measure m

theorem refill_le (o c v : U256) : sstoreStateRefill fork o c v ≤ STORAGE_SET_STATE_GAS := by
  unfold sstoreStateRefill
  split <;> omega

theorem sgm_charges {g g2 g3 : StateGasMeter} {r c s : Nat}
    (hc : GasMeter.charge (GasMeter.refill g r) c = .ok g2)
    (hs : GasMeter.chargeState g2 s = .ok g3) :
    c ≤ g.gasLeft + r ∧ c + s ≤ g.gasLeft + g.reservoir + r ∧
      g3.gasLeft + g3.reservoir + c + s = g.gasLeft + g.reservoir + r := by
  simp only [GasMeter.charge, StateGasMeter.charge, GasMeter.refill, StateGasMeter.refill] at hc
  by_cases hlt : g.gasLeft + min r g.spill < c
  · simp [hlt] at hc
  simp only [hlt, ↓reduceIte, Except.ok.injEq] at hc
  subst hc
  simp only [GasMeter.chargeState, StateGasMeter.chargeState] at hs
  split at hs
  · cases hs
    simp only at *
    omega
  · split at hs
    · cases hs
      simp only at *
      omega
    · cases hs

theorem nat_charge {x c : Nat} (h : c ≤ x) (r : Nat) :
    GasMeter.charge (GasMeter.refill (Meter := Nat) x r) c = .ok (x - c) := by
  simp only [GasMeter.charge, GasMeter.refill]
  exact ite_eq_right_iff.mpr fun h' => absurd h' (by omega)

theorem nat_chargeState {x c : Nat} (h : c ≤ x) :
    GasMeter.chargeState (Meter := Nat) x c = .ok (x - c) := by
  simp only [GasMeter.chargeState]
  exact ite_eq_right_iff.mpr fun h' => absurd h' (by omega)

/-- **One step followed with more gas.** A step of the meter `StateGasMeter` from a running frame
`m` at a `SimAt` opcode, to a running frame or one with no error, is followed by the step of the
meter `Nat` from a frame `n` with the fields of `m` and at least `budget m` gas: it gives a frame
with the fields of the next frame and at least its `budget`. -/
theorem shadow_step (hfork : .berlin ≤ fork) {m m' : Evm fork StateGasMeter} {n : Evm fork Nat}
    (hrun : m.running = true) (hp : SimAt (toNat m)) (hs : step fork m = .ok (.next m'))
    (hm' : m'.running = true ∨ m'.error = none) (hn : n = { toNat m with gas := n.gas })
    (hb : budget m ≤ n.gas) :
    ∃ n', step fork n = .ok (.next n') ∧ n' = { toNat m' with gas := n'.gas } ∧
      budget m' ≤ n'.gas ∧
      n'.gas + (m.gas.gasLeft + m.gas.reservoir) ≤ n.gas + (m'.gas.gasLeft + m'.gas.reservoir) ∧
      (UsdtVerify.Refill.NoRefillAtN (toNat m) →
        n'.gas + (m.gas.gasLeft + m.gas.reservoir) = n.gas + (m'.gas.gasLeft + m'.gas.reservoir)) := by
  have hdec : measure m' < measure m := step_decreases fork hrun hs
  unfold budget at hb ⊢
  generalize hG : n.gas = G at hn hb ⊢
  subst hn
  by_cases hlt : m.pc < m.code.size
  · rcases hop : Op.ofByte fork m.code[m.pc] with _ | op
    · rw [step_of_ofByte_eq_none hlt hop] at hs; cases hs
    obtain ⟨hsim, hi⟩ := hp hlt op hop
    obtain ⟨runN, hN⟩ := Option.isSome_iff_exists.mp hi
    by_cases hss : op = .sstore
    · subst hss
      rw [step_of_instruction hlt hop instruction_sstoreM] at hs
      rcases hx : sstoreStep m with e | b
      · rw [hx] at hs; cases hs
      rw [hx] at hs
      cases hs
      obtain ⟨key, new, st2, g2, g3, st, hok, rfl⟩ := sstoreOk_of_step hfork hx hm'
      have hr := refill_le (fork := fork)
        (m.state.getStorageOriginal m.message.currentTarget (U256.toBeBytes key))
        (m.state.getStorage m.message.currentTarget (U256.toBeBytes key)) new
      obtain ⟨c1, c2, c3⟩ := sgm_charges hok.charge hok.chargeState
      have hm1 : 1 ≤ measure m := by omega
      have hS : STORAGE_SET_STATE_GAS = 97920 := rfl
      have hmul : STORAGE_SET_STATE_GAS ≤ STORAGE_SET_STATE_GAS * measure m :=
        Nat.le_mul_of_pos_right _ hm1
      have hmul2 : STORAGE_SET_STATE_GAS * measure (sstoreAfter m key new st2 g3 st) +
          STORAGE_SET_STATE_GAS ≤ STORAGE_SET_STATE_GAS * measure m := by
        rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hdec
      generalize hC : sstoreCost fork
        (m.state.getStorageOriginal m.message.currentTarget (U256.toBeBytes key))
        (m.state.getStorage m.message.currentTarget (U256.toBeBytes key)) new
        (decide (U256.toBeBytes key ∉
          m.substate.accessedStorageKeys.getD m.message.currentTarget ∅)) = C at c1 c2 c3
      generalize hSG : sstoreStateGas fork
        (m.state.getStorageOriginal m.message.currentTarget (U256.toBeBytes key))
        (m.state.getStorage m.message.currentTarget (U256.toBeBytes key)) new = SG at c2 c3
      have hcG : C ≤ G := by omega
      have hsG : SG ≤ G - C := by omega
      have hnok : SstoreOk ({ toNat m with gas := G } : Evm fork Nat) key new st2
          (G - C) (G - C - SG) st := by
        refine ⟨hok.stack, fun h => hok.stipend ⟨h.1, ?_⟩, ?_, ?_, hok.static, hok.set⟩
        · have := h.2
          change G ≤ CALL_STIPEND at this
          change m.gas.gasLeft ≤ CALL_STIPEND
          omega
        · rw [← hC]; exact nat_charge (hC ▸ hcG) _
        · rw [← hSG]; exact nat_chargeState (hSG ▸ hsG)
      refine ⟨sstoreAfter ({ toNat m with gas := G } : Evm fork Nat) key new st2 (G - C - SG) st,
        ?_, rfl, ?_, ?_, fun hnr => ?_⟩
      · rw [step_of_instruction (evm := ({ toNat m with gas := G } : Evm fork Nat)) hlt hop
          instruction_sstoreM, sstoreStep_of_ok hfork hnok]
        rfl
      · show g3.gasLeft + g3.reservoir + _ ≤ G - _ - _
        omega
      · show G - C - SG + _ ≤ G + (g3.gasLeft + g3.reservoir)
        omega
      · have h0 := hnr hlt hop key new st2.val hok.stack
        show G - C - SG + _ = G + (g3.gasLeft + g3.reservoir)
        change sstoreStateRefill fork
          (m.state.getStorageOriginal m.message.currentTarget (U256.toBeBytes key))
          (m.state.getStorage m.message.currentTarget (U256.toBeBytes key)) new = 0 at h0
        omega
    · obtain ⟨runS, hS, hL⟩ := lifts_of_simulated hsim hss hN
      rw [step_of_instruction hlt hop hS] at hs
      have e := hL m.gas (toNat m)
      rw [lift_toNat] at e
      rw [e] at hs
      rcases hb' : runN (toNat m) with err | b
      · rw [hb'] at hs; cases hs
      rw [hb'] at hs
      cases hs
      have hk : ({ toNat m with gas := G } : Evm fork Nat) = addGas (G - m.gas.gasLeft) (toNat m) := by
        simp only [addGas, toNat]
        congr 1
        omega
      rcases runMono_of_simulated hsim hN (toNat m) (G - m.gas.gasLeft) with
        (⟨err, he⟩ | ⟨b', he, hbr, hbe⟩) | ⟨b', he, hhi⟩
      · rw [hb'] at he; cases he
      · rw [hb'] at he
        cases he
        rcases hm' with h | h
        · exact absurd h (by simp [lift, hbr])
        · exact absurd h hbe
      · rw [hb'] at he
        cases he
        refine ⟨addGas (G - m.gas.gasLeft) b, ?_, rfl, ?_, ?_, fun _ => ?_⟩
        · rw [step_of_instruction (evm := ({ toNat m with gas := G } : Evm fork Nat)) hlt hop hN,
            hk, hhi]
          rfl
        · have hmul2 : STORAGE_SET_STATE_GAS * measure (lift m.gas b) +
              STORAGE_SET_STATE_GAS ≤ STORAGE_SET_STATE_GAS * measure m := by
            rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hdec
          show b.gas + m.gas.reservoir + _ ≤ b.gas + (G - m.gas.gasLeft)
          omega
        · show b.gas + (G - m.gas.gasLeft) + _ ≤ G + (b.gas + m.gas.reservoir)
          omega
        · show b.gas + (G - m.gas.gasLeft) + _ = G + (b.gas + m.gas.reservoir)
          omega
  · rw [step_of_size_le (by omega)] at hs
    cases hs
    refine ⟨_, step_of_size_le (evm := ({ toNat m with gas := G } : Evm fork Nat))
      (by simp only [toNat]; omega), rfl, ?_, Nat.le_of_eq rfl, fun _ => rfl⟩
    have hmul2 : STORAGE_SET_STATE_GAS * measure (advance { m with running := false }) ≤
        STORAGE_SET_STATE_GAS * measure m := Nat.mul_le_mul_left _ (Nat.le_of_lt hdec)
    show m.gas.gasLeft + m.gas.reservoir + _ ≤ G
    omega

/-! ## A run -/

theorem Ends.cons {l b s : Evm fork Nat} (h : Step fork l b) (he : Ends fork b s) :
    Ends fork l s := by
  rcases he with ⟨hr, hs⟩ | ⟨x, hr, hx, hnp⟩
  · exact .inl ⟨.step h hr, hs⟩
  · exact .inr ⟨x, .step h hr, hx, hnp⟩

/-- A step of the meter `StateGasMeter` from a frame whose `toNat` is `SimAt` sends no message. -/
theorem not_child_sgm {m : Evm fork StateGasMeter} (hp : SimAt (toNat m))
    {c : Evm fork StateGasMeter} {msg : Message fork}
    {r : Evm fork StateGasMeter → Except EvmError (Evm fork StateGasMeter)} :
    step fork m ≠ .ok (.child c msg r) := by
  intro h
  by_cases hlt : m.pc < m.code.size
  · rcases hop : Op.ofByte fork m.code[m.pc] with _ | op
    · rw [step_of_ofByte_eq_none hlt hop] at h
      cases h
    · obtain ⟨hsim, hi⟩ := hp hlt op hop
      obtain ⟨runN, hN⟩ := Option.isSome_iff_exists.mp hi
      have : ∃ runS, instruction (Meter := StateGasMeter) fork op = some runS := by
        by_cases hss : op = .sstore
        · subst hss; exact ⟨_, instruction_sstoreM⟩
        · obtain ⟨runS, hS, -⟩ := lifts_of_simulated hsim hss hN
          exact ⟨runS, hS⟩
      obtain ⟨runS, hS⟩ := this
      rw [step_of_instruction hlt hop hS] at h
      rcases hr : runS m with e | b <;> simp [hr, Functor.map, Except.map] at h
  · rw [step_of_size_le (by omega)] at h
    cases h

/-- **A run followed with more gas.** If the loop of the interpreter over `StateGasMeter` from
`m`, for any gas bound and message runner, ends in `s` with no error, then from every frame `n` of
the meter `Nat` with the fields of `m` and at least `budget m` gas, `Ends` holds from `n` to a frame
with the fields of `s` and some gas. The reservoir of `m` may be any, and SSTORE may refill. -/
theorem shadow_run (hfork : .berlin ≤ fork) {bound : Nat}
    {runChild : MessageRunner fork StateGasMeter bound} {m s : Evm fork StateGasMeter}
    {within : GasMeter.gasHeld m.gas ≤ bound}
    (h : Evm.runFrame (step fork) (step_decreases fork) bound runChild m within = .ok s)
    (hok : s.error = none) {n : Evm fork Nat} (hn : n = { toNat m with gas := n.gas })
    (hb : budget m ≤ n.gas) : ∃ G, Ends fork n { toNat s with gas := G } := by
  by_cases hrun : m.running = true
  · have hrn : n.running = true := by rw [hn]; exact hrun
    by_cases hp : SimAt (toNat m)
    · rcases hstep : step fork m with e | (b | ⟨c, msg, res⟩)
      · by_cases ab : e.aborts = true
        · rw [runFrame_of_step_eq_abort hrun hstep ab] at h
          cases h
        · rw [runFrame_of_step_eq_error hrun hstep (by simpa using ab)] at h
          cases h
          simp [exceptionalHalt] at hok
      · rw [runFrame_of_step_eq_next hrun hstep] at h
        have hb' : b.running = true ∨ b.error = none := by
          by_cases hbr : b.running = true
          · exact .inl hbr
          · rw [runFrame_of_running_eq_false (by simpa using hbr)] at h
            cases h
            exact .inr hok
        obtain ⟨n', hs', hn', hbud, -, -⟩ := shadow_step hfork hrun hp hstep hb' hn hb
        have hlt : measure b < measure m := step_decreases fork hrun hstep
        obtain ⟨G, hE⟩ := shadow_run hfork h hok hn' hbud
        exact ⟨G, Ends.cons (.next hrn hs') hE⟩
      · exact absurd hstep (not_child_sgm hp)
    · refine ⟨0, .inr ⟨n, .refl _, hrn, ?_⟩⟩
      rw [hn]
      exact hp
  · have hl : m.running = false := by simpa using hrun
    rw [runFrame_of_running_eq_false hl] at h
    cases h
    refine ⟨n.gas, .inl ⟨?_, ?_⟩⟩
    · rw [← hn]; exact .refl _
    · exact hl
termination_by measure m

/-- **A run followed with more gas, with the gas counted.** `shadow_run`, and the gas `G` of the
end frame of the meter `Nat` meets `G + Q m ≤ n.gas + Q s`, where `Q` is the execution gas left
plus the reservoir; with equality when no running frame that `n` reaches along `Step` refills at
an SSTORE. The reservoir of `m` may be any. -/
theorem shadow_runQ (hfork : .berlin ≤ fork) {bound : Nat}
    {runChild : MessageRunner fork StateGasMeter bound} {m s : Evm fork StateGasMeter}
    {within : GasMeter.gasHeld m.gas ≤ bound}
    (h : Evm.runFrame (step fork) (step_decreases fork) bound runChild m within = .ok s)
    (hok : s.error = none) {n : Evm fork Nat} (hn : n = { toNat m with gas := n.gas })
    (hb : budget m ≤ n.gas) : ∃ G, Ends fork n { toNat s with gas := G } ∧
      G + (m.gas.gasLeft + m.gas.reservoir) ≤ n.gas + (s.gas.gasLeft + s.gas.reservoir) ∧
      ((∀ y, Reaches (Step fork) n y → y.running = true → UsdtVerify.Refill.NoRefillAtN y) →
        G + (m.gas.gasLeft + m.gas.reservoir) = n.gas + (s.gas.gasLeft + s.gas.reservoir)) := by
  have hQ : m.gas.gasLeft + m.gas.reservoir ≤ n.gas := by unfold budget at hb; omega
  by_cases hrun : m.running = true
  · have hrn : n.running = true := by rw [hn]; exact hrun
    by_cases hp : SimAt (toNat m)
    · rcases hstep : step fork m with e | (b | ⟨c, msg, res⟩)
      · by_cases ab : e.aborts = true
        · rw [runFrame_of_step_eq_abort hrun hstep ab] at h
          cases h
        · rw [runFrame_of_step_eq_error hrun hstep (by simpa using ab)] at h
          cases h
          simp [exceptionalHalt] at hok
      · rw [runFrame_of_step_eq_next hrun hstep] at h
        have hb' : b.running = true ∨ b.error = none := by
          by_cases hbr : b.running = true
          · exact .inl hbr
          · rw [runFrame_of_running_eq_false (by simpa using hbr)] at h
            cases h
            exact .inr hok
        obtain ⟨n', hs', hn', hbud, hle, heq⟩ := shadow_step hfork hrun hp hstep hb' hn hb
        have hlt : measure b < measure m := step_decreases fork hrun hstep
        obtain ⟨G, hE, hG1, hG2⟩ := shadow_runQ hfork h hok hn' hbud
        refine ⟨G, Ends.cons (.next hrn hs') hE, by omega, fun hnr => ?_⟩
        have h1 := heq (by
          have := hnr n (.refl _) hrn
          rw [hn] at this
          exact this)
        have h2 := hG2 fun y hy hyr => hnr y (.step (.next hrn hs') hy) hyr
        omega
      · exact absurd hstep (not_child_sgm hp)
    · refine ⟨n.gas + (s.gas.gasLeft + s.gas.reservoir) - (m.gas.gasLeft + m.gas.reservoir),
        .inr ⟨n, .refl _, hrn, ?_⟩, by omega, fun _ => by omega⟩
      rw [hn]
      exact hp
  · have hl : m.running = false := by simpa using hrun
    rw [runFrame_of_running_eq_false hl] at h
    cases h
    refine ⟨n.gas, .inl ⟨?_, ?_⟩, Nat.le_refl _, fun _ => rfl⟩
    · rw [← hn]; exact .refl _
    · exact hl
termination_by measure m

end UsdtVerify.Shadow

namespace UsdtVerify.Shadow

open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic hiding HoareG StepG
open UsdtVerify.Gas
open UsdtVerify.Meter
open UsdtVerify.Refill

variable {fork : Fork} {bound : Nat} {runChild : MessageRunner fork StateGasMeter bound}

/-! ## Forms for the specifications -/

/-- The loop of the interpreter over `StateGasMeter`, run from `m` with gas bound `bound` and
message runner `runChild`, ends in a frame with no error. -/
def RunsOkS (fork : Fork) (bound : Nat) (runChild : MessageRunner fork StateGasMeter bound)
    (m : Evm fork StateGasMeter) (within : GasMeter.gasHeld m.gas ≤ bound) : Prop :=
  ∃ s, Evm.runFrame (step fork) (step_decreases fork) bound runChild m within = .ok s ∧
    s.error = none

/-- `shadow_run` from the frame `addGas (budget m) (toNat m)`. -/
theorem shadow_ends (hfork : .berlin ≤ fork) {m s : Evm fork StateGasMeter}
    {within : GasMeter.gasHeld m.gas ≤ bound}
    (h : Evm.runFrame (step fork) (step_decreases fork) bound runChild m within = .ok s)
    (hok : s.error = none) : ∃ G, Ends fork (addGas (budget m) (toNat m)) { toNat s with gas := G } :=
  shadow_run hfork h hok rfl (by simp only [gas_addGas]; exact Nat.le_add_left _ _)

/-- **A specification over `StepI` run over `StateGasMeter`.** From a frame with reservoir 0
whose `toNat` meets the precondition of a triple over `StepI` to stopped frames that meet `Q`, the
loop over `StateGasMeter`, for any gas bound and message runner, ends in a frame whose `toNat`
meets `Q`. -/
theorem runFrame_of_specI {P Q : Evm fork Nat → Prop}
    (h : HoareI fork P fun e => e.running = false ∧ Q e) {m : Evm fork StateGasMeter}
    (hp : P (toNat m)) (hres : m.gas.reservoir = 0) (within : GasMeter.gasHeld m.gas ≤ bound) :
    ∃ s, Evm.runFrame (step fork) (step_decreases fork) bound runChild m within = .ok s ∧
      Q (toNat s) := by
  obtain ⟨z, hr, hz, hq⟩ := h (toNat m) hp
  obtain ⟨s, hs, hts⟩ := sgm_of_reaches (hr.mono fun h => h.1) hz m rfl (.inl hres)
    (noRefill_run hr hz) within
  exact ⟨s, hs, hts ▸ hq⟩

/-- **`Ends` from a specification over `StepI` with more gas.** If a triple over `StepI` to
stopped frames holds from `addGas k (toNat m)`, `m` has reservoir 0, and the loop over
`StateGasMeter` from `m` ends in `s`, then `Ends` holds from `toNat m` to `toNat s`. -/
theorem ends_of_specI {P Q : Evm fork Nat → Prop}
    (h : HoareI fork P fun e => e.running = false ∧ Q e) {m s : Evm fork StateGasMeter} {k : Nat}
    (hp : P (addGas k (toNat m))) (hres : m.gas.reservoir = 0)
    {within : GasMeter.gasHeld m.gas ≤ bound}
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild m within = .ok s) :
    Ends fork (toNat m) (toNat s) := by
  obtain ⟨z, hr, hz, -⟩ := h _ hp
  exact ends_of_sgmN hrun hres (noRefill_low hr hz)

/-! ## A run over `StateGasMeter` gives a run of the meter `Nat` -/

/-- **The frames of a run are `SimAt`.** If a `StepG` chain goes from `addGas k lo` to a stopped
frame, then every running frame that `lo` reaches along `Step` is `SimAt`. -/
theorem simAt_low {k : Nat} {lo z : Evm fork Nat} (h : Reaches (StepG fork) (addGas k lo) z)
    (hz : z.running = false) :
    ∀ y, Reaches (Step fork) lo y → y.running = true → SimAt y := by
  intro y hy
  induction hy generalizing z with
  | refl =>
    intro hr
    cases h with
    | refl => rw [running_addGas] at hz; rw [hz] at hr; cases hr
    | step hs _ => exact hs.2.1
  | step hs1 hr1 ih =>
    rename_i lo lo1 y
    intro hyr
    have hlo : lo.running = true := hs1.running
    cases h with
    | refl => rw [running_addGas, hlo] at hz; cases hz
    | step hs hr =>
      rename_i hi1
      rcases hs.2.2 k lo rfl with (⟨e, he⟩ | ⟨b, hb, hbr, -⟩) | ⟨b, hb, hhi⟩
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
        have e2 := Step.deterministic hs.1 (.next (by rw [running_addGas]; exact hlo) hhi)
        subst e1 e2
        exact ih hr hz hyr

/-- The loop of the interpreter over the meter `Nat` follows a `Step` chain to a stopped frame,
for any gas bound and message runner. -/
theorem runFrame_of_reachesN {bound : Nat} {runChild : MessageRunner fork Nat bound}
    {l s : Evm fork Nat} (h : Reaches (Step fork) l s) (hs : s.running = false)
    (within : GasMeter.gasHeld l.gas ≤ bound) :
    Evm.runFrame (step fork) (step_decreases fork) bound runChild l within = .ok s := by
  induction h with
  | refl => exact runFrame_of_running_eq_false hs
  | step h1 _ ih =>
    cases h1 with
    | next hr hn => rw [runFrame_of_step_eq_next hr hn]; exact ih hs _
    | halt hr hn hab =>
      rw [runFrame_of_step_eq_error hr hn hab]
      rename_i hrest
      rw [reaches_stopped hrest rfl]

/-- **A run of the meter `Nat` from a run over `StateGasMeter`.** If a triple over `StepI` to
stopped frames holds from `addGas k (toNat m)`, `m` has reservoir 0, and the loop over
`StateGasMeter` from `m` ends with no error, then the loop over the meter `Nat` from `toNat m`
ends with no error, for any gas bound and message runner. -/
theorem runsOk_of_specI {P Q : Evm fork Nat → Prop}
    (h : HoareI fork P fun e => e.running = false ∧ Q e) {m s : Evm fork StateGasMeter} {k : Nat}
    (hp : P (addGas k (toNat m))) (hres : m.gas.reservoir = 0)
    {within : GasMeter.gasHeld m.gas ≤ bound}
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild m within = .ok s)
    (hok : s.error = none) {bound' : Nat} (runChild' : MessageRunner fork Nat bound')
    (within' : GasMeter.gasHeld (toNat m).gas ≤ bound') :
    ∃ s', Evm.runFrame (step fork) (step_decreases fork) bound' runChild' (toNat m) within' =
      .ok s' ∧ s'.error = none := by
  obtain ⟨z, hr, hz, -⟩ := h _ hp
  rcases ends_of_sgmN hrun hres (noRefill_low hr hz) with ⟨hc, hs⟩ | ⟨x, hx, hxr, hnp⟩
  · exact ⟨toNat s, runFrame_of_reachesN hc hs within', hok⟩
  · exact absurd (simAt_low (hr.mono fun h => h.1) hz x hx hxr) hnp

/-! ## The gas at any reservoir -/

theorem sh_zero (e : Evm fork Nat) : addGas 0 e = e := rfl

/-- **The gas of a run at any reservoir, a lower bound.** If, from every gas `g` from `B` on, a
triple over `StepG` takes the fresh frame `At ... g` to stopped frames with `g - cost` gas
(`cost ≤ B`), then a run of the loop over `StateGasMeter` from `m` (any reservoir, refills
allowed) whose `toNat` is that frame with `gas` gas, and that ends with no error, ends with at
least `gas + reservoir - cost` in the execution gas left and the reservoir together. -/
theorem gas_ge_any (hfork : .berlin ≤ fork) {code : ByteArray} {message : Message fork}
    {pc : Nat} {stack : List U256} {memory : ByteArray} {st : State.TransactionState}
    {ss : Substate} {B cost : Nat} (hcB : cost ≤ B)
    (hspec : ∀ g, B ≤ g → HoareG fork (At code message pc stack memory g st ss)
      (fun e => e.running = false ∧ e.gas = g - cost))
    {m s : Evm fork StateGasMeter} {gas : Nat}
    (start : At code message pc stack memory gas st ss (toNat m))
    {within : GasMeter.gasHeld m.gas ≤ bound}
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild m within = .ok s)
    (hok : s.error = none) :
    gas + m.gas.reservoir ≤ s.gas.gasLeft + s.gas.reservoir + cost := by
  have hg0 : (toNat m).gas = gas := start.2.2.2.2.2.2.1
  have hg1 : m.gas.gasLeft = gas := hg0
  obtain ⟨G, hE, hle, -⟩ := shadow_runQ hfork hrun hok (n := addGas (budget m + B) (toNat m)) rfl
    (by simp only [gas_addGas, budget] at *; omega)
  obtain ⟨z, hr, hz, hzg⟩ := hspec (gas + (budget m + B)) (by omega) _ (at_addGas start _)
  have hzs := low_of_reachesE hr hz 0 _ (sh_zero _).symm hE hok
  rw [hzs] at hzg
  simp only [gas_addGas, hg0] at hzg hle
  omega

/-- **The gas of a run at any reservoir.** `gas_ge_any` for a triple over `StepI` (no SSTORE of
the path refills): the execution gas left and the reservoir at the end add up to exactly
`gas + reservoir - cost`. -/
theorem gas_eq_any (hfork : .berlin ≤ fork) {code : ByteArray} {message : Message fork}
    {pc : Nat} {stack : List U256} {memory : ByteArray} {st : State.TransactionState}
    {ss : Substate} {B cost : Nat} (hcB : cost ≤ B)
    (hspec : ∀ g, B ≤ g → HoareI fork (At code message pc stack memory g st ss)
      (fun e => e.running = false ∧ e.gas = g - cost))
    {m s : Evm fork StateGasMeter} {gas : Nat}
    (start : At code message pc stack memory gas st ss (toNat m))
    {within : GasMeter.gasHeld m.gas ≤ bound}
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild m within = .ok s)
    (hok : s.error = none) :
    s.gas.gasLeft + s.gas.reservoir + cost = gas + m.gas.reservoir := by
  have hg0 : (toNat m).gas = gas := start.2.2.2.2.2.2.1
  have hg1 : m.gas.gasLeft = gas := hg0
  obtain ⟨G, hE, -, heq⟩ := shadow_runQ hfork hrun hok (n := addGas (budget m + B) (toNat m)) rfl
    (by simp only [gas_addGas, budget] at *; omega)
  obtain ⟨z, hr, hz, hzg⟩ := hspec (gas + (budget m + B)) (by omega) _ (at_addGas start _)
  have hzs := low_of_reachesE (hr.mono fun h => h.1) hz 0 _ (sh_zero _).symm hE hok
  have hq := heq (noRefill_low (k := 0) hr hz)
  rw [hzs] at hzg
  simp only [gas_addGas, hg0] at hzg hq
  omega

end UsdtVerify.Shadow
