import UsdtVerify.Evm.OneWrite

/-!
# A path with a chain of writes over the EIP-8037 meter: the exact threshold and gas (round 43)

`ExactS fork code message pc stack memory state substate Ok End` says: from every frame `m` over
`StateGasMeter` whose `toNat` is the `At` frame with `m.gas.gasLeft` execution gas, for every gas
bound and message runner, the run ends with no error if and only if `Ok m.gas`, and every run that
ends with no error meets `End m.gas`.

- `exactS_halt`: a cheap stretch to a normal halt (`T` gas, below 97,920, no write) has
  `Ok g := T ≤ g.gasLeft` and ends with the meter `g` less `T` execution gas.
- `exactS_write`: a cheap stretch of `P` gas (below 97,920, the storage as at its start) to an
  SSTORE, followed by a path with `ExactS … Ok End` from the frame after the SSTORE, has
  `Ok g := wOk fork g P o c n cold ∧ Ok (wMeter fork g P o c n cold)`, and `End` read at
  `wMeter fork g P o c n cold`. Here `o`, `c`, `n`, `cold` are the original word, the current
  word, the new word and the cold flag of the write. `wOk` is `P + 2301 ≤ gasLeft` (more than
  2300 execution gas at the SSTORE) and `P + writeCost ≤ gasLeft + sstoreBump`. `wMeter` is
  the meter after the SSTORE (`sstoreMeter`), so the refill of a write goes to the reservoir
  and the spill of the meter that the next write reads.

Applied once per write, this gives the exact success condition and the exact meter at the end
of a path with any number of writes, from any meter: a refill of one write can pay the state
gas of a later one. No hypothesis on refills or on the reservoir.

Status (round 43): READY for the statements of this file and of the `X_sgm` theorems of
Usdt/Refill/ (OwnerS, ChainOwner, ChainTransfer, ChainFee, TransferFromS, ApproveS): clean rebuild
and independent review recorded in docs/AUDIT.md (T1, round 43). The trust assumptions of
docs/RESULTS.md ("What is trusted") apply.
-/

namespace UsdtVerify.Complete

open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open UsdtVerify.Gas
open UsdtVerify.Meter
open UsdtVerify.Refill (StepJ HoareJ)
open GasCosts

variable {fork : Fork}

/-- The exact success condition and end of the runs over `StateGasMeter` from an `At` frame. See
the module doc. -/
def ExactS (fork : Fork) (code : ByteArray) (message : Message fork) (pc : Nat)
    (stack : List U256) (memory : ByteArray) (state : State.TransactionState)
    (substate : Substate) (Ok : StateGasMeter → Prop)
    (End : StateGasMeter → Evm fork StateGasMeter → Prop) : Prop :=
  ∀ (m : Evm fork StateGasMeter),
    At code message pc stack memory m.gas.gasLeft state substate (toNat m) →
    ∀ {bound : Nat} (runChild : MessageRunner fork StateGasMeter bound)
      (within : GasMeter.gasHeld m.gas ≤ bound),
      (Shadow.RunsOkS fork bound runChild m within ↔ Ok m.gas) ∧
      ∀ s, Evm.runFrame (step fork) (step_decreases fork) bound runChild m within = .ok s →
        s.error = none → End m.gas s

/-- The execution gas a write of `n` over the current word `c` (original word `o`) gains over
`StateGasMeter` from the meter `g` against the meter `Nat` (`sstoreBump`). -/
abbrev wBump (fork : Fork) (g : StateGasMeter) (o c n : U256) : Nat :=
  sstoreBump g (sstoreStateRefill fork o c n) (sstoreStateGas fork o c n)

/-- The meter after that write from the meter `g` (`sstoreMeter`). -/
abbrev wSgm (fork : Fork) (g : StateGasMeter) (o c n : U256) (cold : Bool) : StateGasMeter :=
  sstoreMeter g (sstoreStateRefill fork o c n) (sstoreCost fork o c n cold)
    (sstoreStateGas fork o c n)

/-- The condition of a cheap stretch of `P` gas and a write of `n` over the current word `c`
(original word `o`, cold flag `cold`), from the meter `g`. -/
def wOk (fork : Fork) (g : StateGasMeter) (P : Nat) (o c n : U256) (cold : Bool) : Prop :=
  P + 2301 ≤ g.gasLeft ∧
    P + writeCost fork o c n cold ≤
      g.gasLeft + sstoreBump g (sstoreStateRefill fork o c n) (sstoreStateGas fork o c n)

/-- The meter after a cheap stretch of `P` gas and the write, from the meter `g`. -/
def wMeter (fork : Fork) (g : StateGasMeter) (P : Nat) (o c n : U256) (cold : Bool) :
    StateGasMeter :=
  sstoreMeter { g with gasLeft := g.gasLeft - P } (sstoreStateRefill fork o c n)
    (sstoreCost fork o c n cold) (sstoreStateGas fork o c n)

/-- The execution gas left after the stretch and the write, when `wOk` holds. -/
theorem wMeter_gasLeft {g : StateGasMeter} {P : Nat} {o c n : U256} {cold : Bool}
    (h : wOk fork g P o c n cold) :
    (wMeter fork g P o c n cold).gasLeft + P + writeCost fork o c n cold =
      g.gasLeft + sstoreBump g (sstoreStateRefill fork o c n) (sstoreStateGas fork o c n) := by
  obtain ⟨h1, h2⟩ := h
  simp only [writeCost] at h2 ⊢
  change g.gasLeft - P + sstoreBump g _ _ - _ - _ + P + _ = _
  omega

/-- Reading a slot leaves every word of the storage as it is (`getStorage` form). -/
theorem getStorage_readSlot (st : State.TransactionState) (t a : EthLib.Base.Address) (n : U256)
    (k : EthLib.Base.Bytes32) : (readSlot st t n).getStorage a k = st.getStorage a k :=
  (State.TransactionState.recordStorageRead_reads st t a _ k default).2.1

/-- `ExactS` at a frame `m` given with its execution gas `gas`. -/
theorem ExactS.run {code : ByteArray} {message : Message fork} {pc : Nat} {stack : List U256}
    {memory : ByteArray} {state : State.TransactionState} {substate : Substate}
    {Ok : StateGasMeter → Prop} {End : StateGasMeter → Evm fork StateGasMeter → Prop}
    (h : ExactS fork code message pc stack memory state substate Ok End) {gas : Nat}
    {m : Evm fork StateGasMeter} (start : At code message pc stack memory gas state substate (toNat m))
    {bound : Nat} {runChild : MessageRunner fork StateGasMeter bound}
    (within : GasMeter.gasHeld m.gas ≤ bound) :
    m.gas.gasLeft = gas ∧ (Shadow.RunsOkS fork bound runChild m within ↔ Ok m.gas) ∧
      ∀ s, Evm.runFrame (step fork) (step_decreases fork) bound runChild m within = .ok s →
        s.error = none → End m.gas s := by
  have hg : m.gas.gasLeft = gas := start.2.2.2.2.2.2.1
  subst hg
  exact ⟨rfl, h m start runChild within⟩

/-- **A cheap stretch to a normal halt over `StateGasMeter`.** -/
theorem exactS_halt {code : ByteArray} {message : Message fork} {pc : Nat} {stack : List U256}
    {memory out : ByteArray} {state state' : State.TransactionState}
    {substate substate' : Substate} {T : Nat}
    (hpost : ∀ g, T ≤ g → SpecG fork (At code message pc stack memory g state substate)
      (Halted false out (g - T) state' substate'))
    (hT : T < 97920) (hst : ∀ a k, state'.getStorage a k = state.getStorage a k) :
    ExactS fork code message pc stack memory state substate (fun g => T ≤ g.gasLeft)
      (fun g s => s.running = false ∧ s.output = out ∧ s.state = state' ∧
        s.substate = substate' ∧ s.gas = { g with gasLeft := g.gasLeft - T }) := by
  intro m start bound runChild within
  refine ⟨⟨fun ⟨s, hrun, hok⟩ => ?_, fun hg => ?_⟩, fun s hrun hok => ?_⟩
  · exact (ok_exactS (Nat.le_refl T) hpost hT hst start hrun hok).1
  · obtain ⟨z, hr, hzr, hz⟩ := Refill.SpecG.toJA (hpost _ hg) (by omega) hst _ start
    obtain ⟨m3, hm3z, -, hrun3⟩ := fwd_reachesJ hr (.inr hz.2.1) m rfl
    obtain ⟨w3, e3⟩ := hrun3 within
    have hr3 : m3.running = false := by
      have : (toNat m3).running = false := by rw [hm3z]; exact hzr
      exact this
    refine ⟨m3, ?_, ?_⟩
    · rw [e3, runFrame_of_running_eq_false hr3]
    · have : (toNat m3).error = none := by rw [hm3z]; exact hz.2.1
      exact this
  · obtain ⟨-, hr, ho, hgs, hgm, hs, hss⟩ :=
      ok_exactS (Nat.le_refl T) hpost hT hst start hrun hok
    refine ⟨hr, ho, hs, hss, ?_⟩
    rw [hgm, hgs]

/-- **A cheap stretch, a write, and the rest of the path, over `StateGasMeter`.** -/
theorem exactS_write (hfork : .berlin ≤ fork) {code : ByteArray} {message : Message fork}
    {pc0 pcS : Nat} {stk0 : List U256} {mem0 memS : ByteArray}
    {state0 st : State.TransactionState} {substate0 ss : Substate} {key new : U256}
    {rest : List U256} {cold : Bool} {P : Nat}
    {Ok : StateGasMeter → Prop} {End : StateGasMeter → Evm fork StateGasMeter → Prop}
    (hpre : ∀ g, P ≤ g → HoareG fork (At code message pc0 stk0 mem0 g state0 substate0)
      (At code message pcS (key :: new :: rest) memS (g - P) st ss))
    (hP : P < 97920) (hst0 : ∀ a k, st.getStorage a k = state0.getStorage a k)
    (hlt : pcS < code.size) (hbyte : code[pcS] = 0x55) (hstatic : message.isStatic = false)
    (hacc : hasAccount st message.currentTarget) (hcold : coldIn ss message.currentTarget key = cold)
    (hnext : ExactS fork code message (pcS + 1) rest memS
      (writeSlot st message.currentTarget key new)
      (storeSub fork ss message.currentTarget key (originalAt st message.currentTarget key)
        (storageAt st message.currentTarget key) new) Ok End) :
    ExactS fork code message pc0 stk0 mem0 state0 substate0
      (fun g => wOk fork g P (originalAt st message.currentTarget key)
          (storageAt st message.currentTarget key) new cold ∧
        Ok (wMeter fork g P (originalAt st message.currentTarget key)
          (storageAt st message.currentTarget key) new cold))
      (fun g s => End (wMeter fork g P (originalAt st message.currentTarget key)
          (storageAt st message.currentTarget key) new cold) s) := by
  intro m start bound runChild within
  generalize hgas : m.gas.gasLeft = gas at start
  generalize hA : sstoreStateRefill fork (originalAt st message.currentTarget key)
    (storageAt st message.currentTarget key) new = A
  generalize hS : sstoreStateGas fork (originalAt st message.currentTarget key)
    (storageAt st message.currentTarget key) new = S
  generalize hC : sstoreCost fork (originalAt st message.currentTarget key)
    (storageAt st message.currentTarget key) new cold = C
  have hW : writeCost fork (originalAt st message.currentTarget key)
      (storageAt st message.currentTarget key) new cold = C + S := by rw [writeCost, hC, hS]
  have h2300 : CALL_STIPEND = 2300 := rfl
  have hwm : ∀ g : StateGasMeter, wMeter fork g P (originalAt st message.currentTarget key)
      (storageAt st message.currentTarget key) new cold =
        sstoreMeter { g with gasLeft := g.gasLeft - P } A C S := by
    intro g; rw [wMeter, hA, hC, hS]
  have hwo : ∀ g : StateGasMeter, wOk fork g P (originalAt st message.currentTarget key)
      (storageAt st message.currentTarget key) new cold ↔
        (P + 2301 ≤ g.gasLeft ∧ P + (C + S) ≤ g.gasLeft + sstoreBump g A S) := by
    intro g; rw [wOk, hA, hS, hW]
  simp only [hwm, hwo]
  -- The frame after the SSTORE, from the frame at the SSTORE (both directions use it).
  have post : ∀ (m1 : Evm fork StateGasMeter),
      At code message pcS (key :: new :: rest) memS (gas - P) st ss (toNat m1) →
      m1.gas = { m.gas with gasLeft := m1.gas.gasLeft } →
      CALL_STIPEND < gas - P → C + S ≤ gas - P + sstoreBump m.gas A S →
      ∃ m2, step fork m1 = .ok (.next m2) ∧
        m2.gas = sstoreMeter { m.gas with gasLeft := gas - P } A C S ∧
        At code message (pcS + 1) rest memS m2.gas.gasLeft
          (writeSlot st message.currentTarget key new)
          (storeSub fork ss message.currentTarget key (originalAt st message.currentTarget key)
            (storageAt st message.currentTarget key) new) (toNat m2) := by
    intro m1 h1 hg1 hstip hw0
    obtain ⟨ho1, hcu1, hcd1, hstep1, hb1, hk1, hmsg1, hs1, hgl1, hrn1⟩ :=
      one_write_at (A := A) (S := S) hlt hbyte hcold h1 hg1
    have hset : (m1.state.recordStorageRead m1.message.currentTarget
        (U256.toBeBytes key)).setStorage m1.message.currentTarget (U256.toBeBytes key) new =
          .ok (writeSlot st message.currentTarget key new) := by
      rw [hs1, hmsg1]; exact setStorage_writeSlot hacc
    have hw : writeCost fork (origOf m1 key) (curOf m1 key) new (coldOf m1 key) ≤
        m1.gas.gasLeft + sstoreBump m1.gas (sstoreStateRefill fork (origOf m1 key)
          (curOf m1 key) new) (sstoreStateGas fork (origOf m1 key) (curOf m1 key) new) := by
      rw [ho1, hcu1, hcd1, hA, hS, hb1, hgl1, hW]; exact hw0
    obtain ⟨m2, hss, hg2, hN⟩ := sstoreS_of_cond hfork hk1 (by rw [hmsg1]; exact hstatic)
      (by rw [hgl1]; exact hstip) hw hset
    rw [ho1, hcu1, hA, hS, hb1] at hN
    rw [ho1, hcu1, hcd1, hA, hS, hC, hg1, sstoreMeter_gasLeft, hgl1] at hg2
    have hat2 := sstore_post_at (n := sh (sstoreBump m.gas A S) (toNat m1)) hfork hstatic hacc
      hcold (at_sh h1 _) (by omega) (by rw [hW]; omega) (by exact hN)
    rw [hW] at hat2
    refine ⟨m2, by rw [hstep1, hss]; rfl, by rw [hg2]; rfl, ?_⟩
    have hgl2 : m2.gas.gasLeft = gas - P + sstoreBump m.gas A S - (C + S) := by
      rw [hg2]; change gas - P + sstoreBump m.gas A S - C - S = _; omega
    rw [hgl2]; exact hat2
  constructor
  · constructor
    · rintro ⟨s, hrun, hok⟩
      obtain ⟨hP', m1, h1, hg1, w1, hr1⟩ := ok_splitSA (Nat.le_refl P) hpre hP hst0 start hrun hok
      obtain ⟨ho1, hcu1, hcd1, hstep1, hb1, hk1, hmsg1, hs1, hgl1, hrun1⟩ :=
        one_write_at (A := A) (S := S) hlt hbyte hcold h1 hg1
      rcases hss : sstoreStep m1 with e | m2
      · rw [hss] at hstep1
        exact absurd hok (sgm_step_error hrun1 hstep1 hr1)
      rw [hss] at hstep1
      rw [runFrame_of_step_eq_next hrun1 hstep1] at hr1
      have hm2 : m2.running = true ∨ m2.error = none := by
        by_cases hr2 : m2.running = true
        · exact .inl hr2
        · rw [runFrame_of_running_eq_false (by simpa using hr2)] at hr1
          cases hr1
          exact .inr hok
      obtain ⟨key', new', rest', st0, hk, -, hstip, hw, -, -, -⟩ := cond_of_sstoreS hfork hss hm2
      rw [hk1] at hk
      simp only [List.cons.injEq] at hk
      obtain ⟨rfl, rfl, rfl⟩ := hk
      rw [ho1, hcu1, hcd1, hA, hS, hb1, writeCost, hC, hS, hgl1] at hw
      rw [hgl1] at hstip
      obtain ⟨m2', hst2, hg2, hat2⟩ := post m1 h1 hg1 hstip hw
      rw [hstep1] at hst2
      change Except.ok (StepResult.next m2) = _ at hst2
      cases hst2
      refine ⟨⟨by omega, by rw [hgas]; omega⟩, ?_⟩
      have := ((hnext m2 hat2 runChild _).1).mp ⟨s, hr1, hok⟩
      rw [hg2] at this
      rw [hgas]; exact this
    · rintro ⟨⟨hstip, hw⟩, hok⟩
      rw [hgas] at hstip hw hok
      obtain ⟨z1, hr1, hz1⟩ := Refill.HoareG.toJA (hpre gas (by omega)) (by omega) hst0 _ start
      obtain ⟨m1, hm1z, hg1, hrun1⟩ := fwd_reachesJ hr1 (.inl hz1.2.2.2.2.2.2.2.1) m rfl
      rw [← hm1z] at hz1
      have hrn1 : m1.running = true := hz1.2.2.2.2.2.2.2.1
      obtain ⟨m2, hst1, hg2, hat2⟩ := post m1 hz1 hg1 (by show 2300 < _; omega) (by omega)
      obtain ⟨w1, e1⟩ := hrun1 within
      have w2 : GasMeter.gasHeld m2.gas ≤ bound :=
        Nat.le_trans (gasHeld_le_of_measure_lt (step_decreases fork hrn1 hst1)) w1
      rw [← hg2] at hok
      obtain ⟨s, hs, hsok⟩ := ((hnext m2 hat2 runChild w2).1).mpr hok
      refine ⟨s, ?_, hsok⟩
      rw [e1, runFrame_of_step_eq_next hrn1 hst1]
      exact hs
  · intro s hrun hok
    obtain ⟨hP', m1, h1, hg1, w1, hr1⟩ := ok_splitSA (Nat.le_refl P) hpre hP hst0 start hrun hok
    obtain ⟨ho1, hcu1, hcd1, hstep1, hb1, hk1, hmsg1, hs1, hgl1, hrun1⟩ :=
      one_write_at (A := A) (S := S) hlt hbyte hcold h1 hg1
    rcases hss : sstoreStep m1 with e | m2
    · rw [hss] at hstep1
      exact absurd hok (sgm_step_error hrun1 hstep1 hr1)
    rw [hss] at hstep1
    rw [runFrame_of_step_eq_next hrun1 hstep1] at hr1
    have hm2 : m2.running = true ∨ m2.error = none := by
      by_cases hr2 : m2.running = true
      · exact .inl hr2
      · rw [runFrame_of_running_eq_false (by simpa using hr2)] at hr1
        cases hr1
        exact .inr hok
    obtain ⟨key', new', rest', st0, hk, -, hstip, hw, -, -, -⟩ := cond_of_sstoreS hfork hss hm2
    rw [hk1] at hk
    simp only [List.cons.injEq] at hk
    obtain ⟨rfl, rfl, rfl⟩ := hk
    rw [ho1, hcu1, hcd1, hA, hS, hb1, writeCost, hC, hS, hgl1] at hw
    rw [hgl1] at hstip
    obtain ⟨m2', hst2, hg2, hat2⟩ := post m1 h1 hg1 hstip hw
    rw [hstep1] at hst2
    change Except.ok (StepResult.next m2) = _ at hst2
    cases hst2
    have := (hnext m2 hat2 runChild _).2 s hr1 hok
    rw [hg2] at this
    rw [hgas]; exact this

end UsdtVerify.Complete
