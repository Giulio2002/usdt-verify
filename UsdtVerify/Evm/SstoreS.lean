import UsdtVerify.Evm.SgmSplit

/-!
# SSTORE over the EIP-8037 meter, exactly, at any reservoir (round 42)

Over `StateGasMeter` an SSTORE first refills `A` (`sstoreStateRefill`): the execution gas gets
back up to the spill of the frame, `b = min A spill`, and the reservoir the rest. Then it charges
`c` execution gas (`sstoreCost`), then `S` state gas (`sstoreStateGas`), from the reservoir first.
So the step is the step of the meter `Nat` from the same frame with `sstoreBump g A S` more gas,
`b + min S (reservoir + A - b)`: the execution gas that the refill gives back plus the state gas
that the reservoir pays (`sstoreS_of_cond`, `cond_of_sstoreS`). The 2300 check reads the
execution gas left before the refill.

- `sstoreBump`, `sstoreMeter`: the bump and the meter after the SSTORE.
- `sgm_sstore_charges`, `sgm_sstore_charges_inv`: the two charges of an SSTORE over
  `StateGasMeter` succeed exactly when `c + S` is at most the execution gas left plus the bump,
  and give `sstoreMeter`.
- `sstoreS_of_cond`, `cond_of_sstoreS`: the SSTORE step over `StateGasMeter` and the SSTORE step
  of the meter `Nat` from the frame with the bump added.
-/

namespace UsdtVerify.Complete

open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open UsdtVerify.Gas
open UsdtVerify.Meter
open UsdtVerify.Shadow (SstoreOk sstoreAfter sstoreOk_of_step sstoreStep_of_ok)
open GasCosts

variable {fork : Fork}

/-- The execution gas an SSTORE over `StateGasMeter` gains against the meter `Nat`: the part of
the refill `A` that goes back to execution gas (up to the spill), and the part of the state gas
`S` that the reservoir, refilled, pays. -/
def sstoreBump (g : StateGasMeter) (A S : Nat) : Nat :=
  min A g.spill + min S (g.reservoir + (A - min A g.spill))

/-- The meter after an SSTORE that refills `A`, charges `c` execution gas and `S` state gas. -/
def sstoreMeter (g : StateGasMeter) (A c S : Nat) : StateGasMeter :=
  { g with
    gasLeft := g.gasLeft + sstoreBump g A S - c - S
    reservoir := g.reservoir + (A - min A g.spill) - min S (g.reservoir + (A - min A g.spill))
    spill := g.spill - min A g.spill + (S - min S (g.reservoir + (A - min A g.spill))) }

/-- The charges of an SSTORE over `StateGasMeter` succeed when `c + S` is at most the execution
gas left plus the bump, and give `sstoreMeter`. -/
theorem sgm_sstore_charges {g : StateGasMeter} {A c S : Nat}
    (h : c + S ≤ g.gasLeft + sstoreBump g A S) :
    ∃ g2, GasMeter.charge (GasMeter.refill g A) c = .ok g2 ∧
      GasMeter.chargeState g2 S = .ok (sstoreMeter g A c S) := by
  rcases g with ⟨gl, res, base, sp, com, gr⟩
  simp only [sstoreBump] at h
  simp only [GasMeter.charge, StateGasMeter.charge, GasMeter.refill, StateGasMeter.refill,
    GasMeter.chargeState, StateGasMeter.chargeState, sstoreMeter, sstoreBump]
  by_cases h1 : S ≤ res + (A - min A sp)
  · have hm : min S (res + (A - min A sp)) = S := Nat.min_eq_left h1
    rw [hm] at h ⊢
    have h2 : ¬ gl + min A sp < c := by omega
    simp only [h2, ↓reduceIte, Except.ok.injEq, exists_eq_left', h1]
    congr 1 <;> omega
  · have hm : min S (res + (A - min A sp)) = res + (A - min A sp) := Nat.min_eq_right (by omega)
    rw [hm] at h ⊢
    have h2 : ¬ gl + min A sp < c := by omega
    have h3 : S ≤ res + (A - min A sp) + (gl + min A sp - c) := by omega
    simp only [h2, ↓reduceIte, Except.ok.injEq, exists_eq_left', h1, h3]
    congr 1 <;> omega

/-- The converse of `sgm_sstore_charges`. -/
theorem sgm_sstore_charges_inv {g g2 g3 : StateGasMeter} {A c S : Nat}
    (hc : GasMeter.charge (GasMeter.refill g A) c = .ok g2)
    (hs : GasMeter.chargeState g2 S = .ok g3) :
    c + S ≤ g.gasLeft + sstoreBump g A S ∧ g3 = sstoreMeter g A c S := by
  rcases g with ⟨gl, res, base, sp, com, gr⟩
  simp only [GasMeter.charge, StateGasMeter.charge, GasMeter.refill, StateGasMeter.refill] at hc
  by_cases h2 : gl + min A sp < c
  · simp [h2] at hc
  simp only [h2, ↓reduceIte, Except.ok.injEq] at hc
  subst hc
  simp only [GasMeter.chargeState, StateGasMeter.chargeState] at hs
  simp only [sstoreMeter, sstoreBump]
  split at hs
  · cases hs
    rename_i h1
    have hm : min S (res + (A - min A sp)) = S := Nat.min_eq_left h1
    rw [hm]
    refine ⟨by omega, ?_⟩
    congr 1 <;> omega
  · split at hs
    · cases hs
      rename_i h1 h3
      have hm : min S (res + (A - min A sp)) = res + (A - min A sp) :=
        Nat.min_eq_right (by omega)
      rw [hm]
      refine ⟨by omega, ?_⟩
      congr 1 <;> omega
    · cases hs

/-- The three words an SSTORE from `m` reads: the original word, the current word, and the cold
flag of the key. -/
abbrev origOf (m : Evm fork StateGasMeter) (key : U256) : U256 :=
  m.state.getStorageOriginal m.message.currentTarget (U256.toBeBytes key)
abbrev curOf (m : Evm fork StateGasMeter) (key : U256) : U256 :=
  m.state.getStorage m.message.currentTarget (U256.toBeBytes key)
abbrev coldOf (m : Evm fork StateGasMeter) (key : U256) : Bool :=
  decide (U256.toBeBytes key ∉ m.substate.accessedStorageKeys.getD m.message.currentTarget ∅)

/-- **SSTORE over `StateGasMeter`, forward.** From Berlin, an SSTORE from `m` (any meter) with
more than 2300 execution gas left, whose write costs at most the execution gas left plus the bump,
in a frame that is not static and whose write of the state succeeds: the step gives a frame `m'`
with `sstoreMeter`, and the SSTORE of the meter `Nat` from `toNat m` with the bump added gives
`toNat m'`. -/
theorem sstoreS_of_cond (hfork : .berlin ≤ fork) {m : Evm fork StateGasMeter} {key new : U256}
    {rest : List U256} {st : State.TransactionState}
    (hst : m.stack.val = key :: new :: rest) (hstatic : m.message.isStatic = false)
    (hstip : CALL_STIPEND < m.gas.gasLeft)
    (hgas : writeCost fork (origOf m key) (curOf m key) new (coldOf m key) ≤
      m.gas.gasLeft + sstoreBump m.gas (sstoreStateRefill fork (origOf m key) (curOf m key) new)
        (sstoreStateGas fork (origOf m key) (curOf m key) new))
    (hset : (m.state.recordStorageRead m.message.currentTarget (U256.toBeBytes key)).setStorage
      m.message.currentTarget (U256.toBeBytes key) new = .ok st) :
    ∃ m', sstoreStep m = .ok m' ∧
      m'.gas = sstoreMeter m.gas (sstoreStateRefill fork (origOf m key) (curOf m key) new)
        (sstoreCost fork (origOf m key) (curOf m key) new (coldOf m key))
        (sstoreStateGas fork (origOf m key) (curOf m key) new) ∧
      sstoreStep ({ toNat m with gas := (m.gas.gasLeft + sstoreBump m.gas
        (sstoreStateRefill fork (origOf m key) (curOf m key) new)
        (sstoreStateGas fork (origOf m key) (curOf m key) new)) } : Evm fork Nat) =
        .ok (toNat m') := by
  generalize hA : sstoreStateRefill fork (origOf m key) (curOf m key) new = A at hgas ⊢
  generalize hS : sstoreStateGas fork (origOf m key) (curOf m key) new = S at hgas ⊢
  have hw : writeCost fork (origOf m key) (curOf m key) new (coldOf m key) =
      sstoreCost fork (origOf m key) (curOf m key) new (coldOf m key) + S := by
    rw [writeCost, hS]
  rw [hw] at hgas
  generalize hC : sstoreCost fork (origOf m key) (curOf m key) new (coldOf m key) = C at hgas ⊢
  have hlen : rest.length ≤ STACK_LIMIT := by
    have := m.stack.property
    rw [hst] at this
    simp at this
    omega
  let st2 : Stack := ⟨rest, hlen⟩
  obtain ⟨g2, hc2, hc3⟩ := sgm_sstore_charges (g := m.gas) (A := A) (c := C) (S := S) hgas
  have hokS : SstoreOk m key new st2 g2 (sstoreMeter m.gas A C S) st := by
    refine ⟨hst, fun h => ?_, ?_, ?_, hstatic, hset⟩
    · have := h.2
      change m.gas.gasLeft ≤ CALL_STIPEND at this
      omega
    · rw [hA, hC]; exact hc2
    · rw [hS]; exact hc3
  have hokN : SstoreOk ({ toNat m with gas := m.gas.gasLeft + sstoreBump m.gas A S } :
      Evm fork Nat) key new st2 (m.gas.gasLeft + sstoreBump m.gas A S - C)
      (m.gas.gasLeft + sstoreBump m.gas A S - C - S) st := by
    refine ⟨hst, fun h => ?_, ?_, ?_, hstatic, hset⟩
    · have := h.2
      change m.gas.gasLeft + sstoreBump m.gas A S ≤ CALL_STIPEND at this
      omega
    · change GasMeter.charge (GasMeter.refill (m.gas.gasLeft + sstoreBump m.gas A S)
        (sstoreStateRefill fork (origOf m key) (curOf m key) new))
        (sstoreCost fork (origOf m key) (curOf m key) new (coldOf m key)) = _
      rw [hC]
      exact Shadow.nat_charge (by omega) _
    · change GasMeter.chargeState (m.gas.gasLeft + sstoreBump m.gas A S - C)
        (sstoreStateGas fork (origOf m key) (curOf m key) new) = _
      rw [hS]
      exact Shadow.nat_chargeState (by omega)
  refine ⟨_, sstoreStep_of_ok hfork hokS, rfl, ?_⟩
  rw [sstoreStep_of_ok hfork hokN]
  rfl

/-- **SSTORE over `StateGasMeter`, backward.** From Berlin, an SSTORE step from `m` (any meter)
that gives a frame that runs or has no error met the conditions of `sstoreS_of_cond`, and its
frame is the one there. -/
theorem cond_of_sstoreS (hfork : .berlin ≤ fork) {m m' : Evm fork StateGasMeter}
    (h : sstoreStep m = .ok m') (hm' : m'.running = true ∨ m'.error = none) :
    ∃ key new rest st, m.stack.val = key :: new :: rest ∧ m.message.isStatic = false ∧
      CALL_STIPEND < m.gas.gasLeft ∧
      writeCost fork (origOf m key) (curOf m key) new (coldOf m key) ≤
        m.gas.gasLeft + sstoreBump m.gas (sstoreStateRefill fork (origOf m key) (curOf m key) new)
          (sstoreStateGas fork (origOf m key) (curOf m key) new) ∧
      (m.state.recordStorageRead m.message.currentTarget (U256.toBeBytes key)).setStorage
        m.message.currentTarget (U256.toBeBytes key) new = .ok st ∧
      m'.gas = sstoreMeter m.gas (sstoreStateRefill fork (origOf m key) (curOf m key) new)
        (sstoreCost fork (origOf m key) (curOf m key) new (coldOf m key))
        (sstoreStateGas fork (origOf m key) (curOf m key) new) ∧
      sstoreStep ({ toNat m with gas := (m.gas.gasLeft + sstoreBump m.gas
        (sstoreStateRefill fork (origOf m key) (curOf m key) new)
        (sstoreStateGas fork (origOf m key) (curOf m key) new)) } : Evm fork Nat) =
        .ok (toNat m') := by
  obtain ⟨key, new, st2, g2, g3, st, hok, rfl⟩ := sstoreOk_of_step hfork h hm'
  have hist : Fork.istanbul ≤ fork := Nat.le_trans (by decide) hfork
  obtain ⟨hle, -⟩ := sgm_sstore_charges_inv hok.charge hok.chargeState
  have hstip : CALL_STIPEND < m.gas.gasLeft := by
    have := hok.stipend
    apply Nat.lt_of_not_le
    intro hc
    exact this ⟨hist, hc⟩
  have hw : writeCost fork (origOf m key) (curOf m key) new (coldOf m key) ≤
      m.gas.gasLeft + sstoreBump m.gas (sstoreStateRefill fork (origOf m key) (curOf m key) new)
        (sstoreStateGas fork (origOf m key) (curOf m key) new) := by
    rw [writeCost]; exact hle
  obtain ⟨m'', h1, h2, h3⟩ := sstoreS_of_cond hfork (rest := st2.val) hok.stack hok.static hstip hw
    hok.set
  rw [h1] at h
  cases h
  exact ⟨key, new, st2.val, st, hok.stack, hok.static, hstip, hw, hok.set, h2, h3⟩

end UsdtVerify.Complete
