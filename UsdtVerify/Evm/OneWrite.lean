import UsdtVerify.Evm.SstoreS

/-!
# A path with one write over the EIP-8037 meter: the exact threshold and gas (round 42)

A path of the meter `Nat` made of a cheap stretch to an SSTORE (no write, less than 97,920 gas,
the storage as at the start), the SSTORE, and a cheap stretch to a normal halt. Over
`StateGasMeter`, from a frame `m` with any meter whose `toNat` is the first frame with `gas`
execution gas:

- `ok_exactS`: a run over `StateGasMeter` along a cheap specification to a normal halt ends with
  the exact execution gas left and the meter of the first frame for the rest.
- `one_write_sgm`: the run ends with no error if and only if `P + 2301 ≤ gas` (more than 2300 at
  the SSTORE) and `P + W + T ≤ gas + bump`, where `P` is the gas of the first stretch, `W` the
  price of the write (`writeCost`), `T` the gas of the second stretch, and `bump` is
  `sstoreBump m.gas A S` with `A` the refill and `S` the state gas of the write. Every run that ends
  with no error ends as the specification says, with `gasLeft + P + W + T = gas + bump` and the
  meter `sstoreMeter m.gas A c S` for the rest (reservoir and spill).

No hypothesis on refills or on the reservoir.
-/

namespace UsdtVerify.Complete

open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic hiding HoareG SpecG StepG
open UsdtVerify.Gas
open UsdtVerify.Meter
open UsdtVerify.Refill (StepJ HoareJ)
open GasCosts

variable {fork : Fork}

/-- **The end of a cheap path over `StateGasMeter`.** A run over `StateGasMeter` that ends with no
error, from a frame whose `toNat` is an `At` frame with `gas` from which, for every gas from
`B ≥ c` on, a specification over `StepG` reaches a normal halt with `c` less (`c` below 97,920, the
storage as at the start): `c ≤ gas`, and the end is that halt, with `gas - c` execution gas left and
the meter of the first frame for the rest. -/
theorem ok_exactS {code : ByteArray} {message : Message fork} {pc : Nat} {stack : List U256}
    {memory out : ByteArray} {state state' : State.TransactionState}
    {substate substate' : Substate} {B c : Nat} (hB : c ≤ B)
    (h : ∀ g, B ≤ g → SpecG fork (At code message pc stack memory g state substate)
      (Halted false out (g - c) state' substate'))
    (hc : c < 97920) (hst : ∀ a k, state'.getStorage a k = state.getStorage a k)
    {gas : Nat} {m s : Evm fork StateGasMeter}
    (start : At code message pc stack memory gas state substate (toNat m))
    {bound : Nat} {runChild : MessageRunner fork StateGasMeter bound}
    {within : GasMeter.gasHeld m.gas ≤ bound}
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild m within = .ok s)
    (hok : s.error = none) :
    c ≤ gas ∧ s.running = false ∧ s.output = out ∧ s.gas.gasLeft = gas - c ∧
      s.gas = { m.gas with gasLeft := s.gas.gasLeft } ∧ s.state = state' ∧
      s.substate = substate' := by
  obtain ⟨z, hr, hz, hh⟩ := Refill.SpecG.toJA (h (gas + B) (by omega)) (by omega) hst _
    (at_addGas start B)
  obtain ⟨m3, rfl, hg, w3, h3⟩ := low_to_runningS hr B m rfl hrun hok
  have hr3 : m3.running = false := hz
  rw [runFrame_of_running_eq_false hr3] at h3
  cases h3
  obtain ⟨-, -, ho, hgas, hs, hss⟩ := hh
  simp only [gas_addGas] at hgas
  have hgl : s.gas.gasLeft + B = gas + B - c := hgas
  exact ⟨by omega, hr3, ho, by omega, hg, hs, hss⟩

section OneWrite

variable {code : ByteArray} {message : Message fork} {pc0 pcS : Nat} {stk0 : List U256}
  {mem0 memS out : ByteArray} {state0 st st' : State.TransactionState}
  {substate0 ss ss' : Substate} {key new : U256} {rest : List U256} {cold : Bool} {P T : Nat}

/-- The frame after the SSTORE of the meter `Nat`, as an `At` frame. -/
theorem sstore_post_at (hfork : .berlin ≤ fork) (hstatic : message.isStatic = false)
    (hacc : hasAccount st message.currentTarget) (hcold : coldIn ss message.currentTarget key = cold)
    {X : Nat} {n y : Evm fork Nat}
    (hn : At code message pcS (key :: new :: rest) memS X st ss n)
    (hstip : CALL_STIPEND < X)
    (hgas : writeCost fork (originalAt st message.currentTarget key)
      (storageAt st message.currentTarget key) new cold ≤ X)
    (hy : sstoreStep n = .ok y) :
    At code message (pcS + 1) rest memS
      (X - writeCost fork (originalAt st message.currentTarget key)
        (storageAt st message.currentTarget key) new cold)
      (writeSlot st message.currentTarget key new)
      (storeSub fork ss message.currentTarget key (originalAt st message.currentTarget key)
        (storageAt st message.currentTarget key) new) y := by
  obtain ⟨hcode, hj, hm, hpc, hst, hmem, hg, hrun, herr, hout, hs, hss⟩ := hn
  subst hm hg hs hss hcold
  obtain ⟨after, h, a1, a2, a3, a4, a5, a6, a7, a8, a9, ao, a10, a11⟩ :=
    sstoreStep_eq_any hfork hst hstatic hstip hgas (setStorage_writeSlot hacc)
  rw [h] at hy
  cases hy
  exact ⟨by rw [a1, hcode], by rw [a2, hj], a3, by rw [a4, hpc], a5, by rw [a6, hmem],
    a7, by rw [a8, hrun], by rw [a9, herr], by rw [ao, hout], a10, a11⟩

/-- `sstoreMeter` reads the execution gas left only for its own. -/
theorem sstoreMeter_gasLeft (g : StateGasMeter) (x A c S : Nat) :
    sstoreMeter { g with gasLeft := x } A c S =
      { sstoreMeter g A c S with gasLeft := x + sstoreBump g A S - c - S } := rfl

/-- The facts at the SSTORE frame of the path, over `StateGasMeter`. -/
theorem one_write_at (hlt : pcS < code.size) (hbyte : code[pcS] = 0x55)
    (hcold : coldIn ss message.currentTarget key = cold) {g0 : StateGasMeter} {A S X : Nat}
    {m1 : Evm fork StateGasMeter}
    (h1 : At code message pcS (key :: new :: rest) memS X st ss (toNat m1))
    (hg1 : m1.gas = { g0 with gasLeft := m1.gas.gasLeft }) :
    origOf m1 key = originalAt st message.currentTarget key ∧
      curOf m1 key = storageAt st message.currentTarget key ∧ coldOf m1 key = cold ∧
      step fork m1 = .next <$> sstoreStep m1 ∧ sstoreBump m1.gas A S = sstoreBump g0 A S ∧
      m1.stack.val = key :: new :: rest ∧ m1.message = message ∧ m1.state = st ∧
      m1.gas.gasLeft = X ∧ m1.running = true := by
  obtain ⟨hc1, -, hm1, hpc1, hk1, -, hgl, hr1, -, -, hs1, hss1⟩ := h1
  have hlt1 : m1.pc < m1.code.size := by
    change (toNat m1).pc < (toNat m1).code.size
    rw [hc1, hpc1]; exact hlt
  have hop1 : Op.ofByte fork m1.code[m1.pc] = some .sstore := by
    change Op.ofByte fork (toNat m1).code[(toNat m1).pc] = some .sstore
    simp only [hc1, hpc1, hbyte]
    exact ofByte_of_decode (op := .sstore) rfl (Fork.frontier_le _)
  refine ⟨?_, ?_, ?_, ?_, ?_, hk1, hm1, hs1, hgl, hr1⟩
  · show (toNat m1).state.getStorageOriginal (toNat m1).message.currentTarget _ = _
    rw [hs1, hm1]
  · show (toNat m1).state.getStorage (toNat m1).message.currentTarget _ = _
    rw [hs1, hm1]
  · show decide (_ ∉ (toNat m1).substate.accessedStorageKeys.getD
      (toNat m1).message.currentTarget ∅) = _
    rw [hss1, hm1, ← hcold]
  · rw [step_of_instruction hlt1 hop1 Shadow.instruction_sstoreM] <;> rfl
  · rw [hg1] <;> rfl

/-- **A path with one write over `StateGasMeter`: every run that ends with no error.** -/
theorem one_write_end (hfork : .berlin ≤ fork)
    (hpre : ∀ g, P ≤ g → HoareG fork (At code message pc0 stk0 mem0 g state0 substate0)
      (At code message pcS (key :: new :: rest) memS (g - P) st ss))
    (hP : P < 97920) (hst0 : ∀ a k, st.getStorage a k = state0.getStorage a k)
    (hlt : pcS < code.size) (hbyte : code[pcS] = 0x55) (hstatic : message.isStatic = false)
    (hacc : hasAccount st message.currentTarget) (hcold : coldIn ss message.currentTarget key = cold)
    (hpost : ∀ g, T ≤ g → SpecG fork (At code message (pcS + 1) rest memS g
        (writeSlot st message.currentTarget key new)
        (storeSub fork ss message.currentTarget key (originalAt st message.currentTarget key)
          (storageAt st message.currentTarget key) new))
      (Halted false out (g - T) st' ss'))
    (hT : T < 97920)
    (hst' : ∀ a k, st'.getStorage a k = (writeSlot st message.currentTarget key new).getStorage a k)
    {gas : Nat} {m : Evm fork StateGasMeter}
    (start : At code message pc0 stk0 mem0 gas state0 substate0 (toNat m))
    {bound : Nat} {runChild : MessageRunner fork StateGasMeter bound}
    {within : GasMeter.gasHeld m.gas ≤ bound} {s : Evm fork StateGasMeter}
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild m within = .ok s)
    (hok : s.error = none) :
    P + 2301 ≤ gas ∧
    P + writeCost fork (originalAt st message.currentTarget key)
        (storageAt st message.currentTarget key) new cold + T ≤
      gas + sstoreBump m.gas (sstoreStateRefill fork (originalAt st message.currentTarget key)
            (storageAt st message.currentTarget key) new) (sstoreStateGas fork (originalAt st message.currentTarget key)
            (storageAt st message.currentTarget key) new) ∧
    s.running = false ∧ s.output = out ∧ s.state = st' ∧ s.substate = ss' ∧
    s.gas.gasLeft + P + writeCost fork (originalAt st message.currentTarget key)
        (storageAt st message.currentTarget key) new cold + T =
      gas + sstoreBump m.gas (sstoreStateRefill fork (originalAt st message.currentTarget key)
            (storageAt st message.currentTarget key) new) (sstoreStateGas fork (originalAt st message.currentTarget key)
            (storageAt st message.currentTarget key) new) ∧
    s.gas = { sstoreMeter m.gas (sstoreStateRefill fork (originalAt st message.currentTarget key)
            (storageAt st message.currentTarget key) new) (sstoreCost fork (originalAt st message.currentTarget key)
            (storageAt st message.currentTarget key) new cold) (sstoreStateGas fork (originalAt st message.currentTarget key)
            (storageAt st message.currentTarget key) new) with gasLeft := s.gas.gasLeft } := by
  generalize hA : sstoreStateRefill fork (originalAt st message.currentTarget key) (storageAt st message.currentTarget key) new = A
  generalize hS : sstoreStateGas fork (originalAt st message.currentTarget key) (storageAt st message.currentTarget key) new = S
  generalize hC : sstoreCost fork (originalAt st message.currentTarget key) (storageAt st message.currentTarget key) new cold = C
  have hW : writeCost fork (originalAt st message.currentTarget key)
        (storageAt st message.currentTarget key) new cold = C + S := by rw [writeCost, hC, hS]
  have h2300 : CALL_STIPEND = 2300 := rfl
  rw [hW]
  obtain ⟨hP', m1, h1, hg1, w1, hr1⟩ := ok_splitSA (Nat.le_refl P) hpre hP hst0 start hrun hok
  obtain ⟨ho1, hcu1, hcd1, hstep1, hb1, hk1, hm1, hs1, hgl1, hrun1⟩ :=
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
  obtain ⟨key', new', rest', st0, hk, -, hstip, hw, -, hg2, hN⟩ := cond_of_sstoreS hfork hss hm2
  rw [hk1] at hk
  simp only [List.cons.injEq] at hk
  obtain ⟨rfl, rfl, rfl⟩ := hk
  rw [ho1, hcu1, hcd1, hA, hS, hb1, writeCost, hC, hS] at hw
  rw [ho1, hcu1, hA, hS, hb1] at hN
  rw [ho1, hcu1, hcd1, hA, hS, hC, hg1, sstoreMeter_gasLeft] at hg2
  rw [hgl1] at hstip hw hg2
  have hat2 := sstore_post_at (n := addGas (sstoreBump m.gas A S) (toNat m1)) hfork hstatic hacc hcold
    (at_addGas h1 _) (by omega) (by rw [hW]; exact hw) (by exact hN)
  rw [hW] at hat2
  obtain ⟨hT', hr, ho, hgs, hgm, hs, hsss⟩ := ok_exactS (Nat.le_refl T) hpost hT hst' hat2 hr1 hok
  refine ⟨by omega, by omega, hr, ho, hs, hsss, by omega, ?_⟩
  rw [hgm, hg2]

/-- **A path with one write over `StateGasMeter`: the run, given the gas.** -/
theorem one_write_run (hfork : .berlin ≤ fork)
    (hpre : ∀ g, P ≤ g → HoareG fork (At code message pc0 stk0 mem0 g state0 substate0)
      (At code message pcS (key :: new :: rest) memS (g - P) st ss))
    (hP : P < 97920) (hst0 : ∀ a k, st.getStorage a k = state0.getStorage a k)
    (hlt : pcS < code.size) (hbyte : code[pcS] = 0x55) (hstatic : message.isStatic = false)
    (hacc : hasAccount st message.currentTarget) (hcold : coldIn ss message.currentTarget key = cold)
    (hpost : ∀ g, T ≤ g → SpecG fork (At code message (pcS + 1) rest memS g
        (writeSlot st message.currentTarget key new)
        (storeSub fork ss message.currentTarget key (originalAt st message.currentTarget key)
          (storageAt st message.currentTarget key) new))
      (Halted false out (g - T) st' ss'))
    (hT : T < 97920)
    (hst' : ∀ a k, st'.getStorage a k = (writeSlot st message.currentTarget key new).getStorage a k)
    {gas : Nat} {m : Evm fork StateGasMeter}
    (start : At code message pc0 stk0 mem0 gas state0 substate0 (toNat m))
    (hstip : P + 2301 ≤ gas)
    (hgas : P + writeCost fork (originalAt st message.currentTarget key)
        (storageAt st message.currentTarget key) new cold + T ≤
      gas + sstoreBump m.gas (sstoreStateRefill fork (originalAt st message.currentTarget key)
            (storageAt st message.currentTarget key) new) (sstoreStateGas fork (originalAt st message.currentTarget key)
            (storageAt st message.currentTarget key) new))
    {bound : Nat} {runChild : MessageRunner fork StateGasMeter bound}
    (within : GasMeter.gasHeld m.gas ≤ bound) :
    Shadow.RunsOkS fork bound runChild m within := by
  generalize hA : sstoreStateRefill fork (originalAt st message.currentTarget key) (storageAt st message.currentTarget key) new = A at hgas
  generalize hS : sstoreStateGas fork (originalAt st message.currentTarget key) (storageAt st message.currentTarget key) new = S at hgas
  generalize hC : sstoreCost fork (originalAt st message.currentTarget key) (storageAt st message.currentTarget key) new cold = C
  have hW : writeCost fork (originalAt st message.currentTarget key)
        (storageAt st message.currentTarget key) new cold = C + S := by rw [writeCost, hC, hS]
  have h2300 : CALL_STIPEND = 2300 := rfl
  rw [hW] at hgas
  obtain ⟨z1, hr1, hz1⟩ := Refill.HoareG.toJA (hpre gas (by omega)) (by omega) hst0 _ start
  obtain ⟨m1, hm1z, hg1, hrun1⟩ := fwd_reachesJ hr1 (.inl hz1.2.2.2.2.2.2.2.1) m rfl
  rw [← hm1z] at hz1
  obtain ⟨ho1, hcu1, hcd1, hstep1, hb1, hk1, hmsg1, hs1, hgl1, hrn1⟩ :=
    one_write_at (A := A) (S := S) hlt hbyte hcold hz1 hg1
  have hset : (m1.state.recordStorageRead m1.message.currentTarget (U256.toBeBytes key)).setStorage
      m1.message.currentTarget (U256.toBeBytes key) new =
        .ok (writeSlot st message.currentTarget key new) := by
    rw [hs1, hmsg1]; exact setStorage_writeSlot hacc
  have hw : writeCost fork (origOf m1 key) (curOf m1 key) new (coldOf m1 key) ≤
      m1.gas.gasLeft + sstoreBump m1.gas (sstoreStateRefill fork (origOf m1 key) (curOf m1 key) new)
        (sstoreStateGas fork (origOf m1 key) (curOf m1 key) new) := by
    rw [ho1, hcu1, hcd1, hA, hS, hb1, hgl1, hW]; omega
  obtain ⟨m2, hss, -, hN⟩ := sstoreS_of_cond hfork hk1 (by rw [hmsg1]; exact hstatic)
    (by rw [hgl1]; show 2300 < _; omega) hw hset
  rw [ho1, hcu1, hA, hS, hb1] at hN
  have hat2 := sstore_post_at (n := addGas (sstoreBump m.gas A S) (toNat m1)) hfork hstatic hacc hcold
    (at_addGas hz1 _) (by omega) (by rw [hW]; omega) (by exact hN)
  rw [hW] at hat2
  obtain ⟨z, hr, hzr, hz⟩ := Refill.SpecG.toJA (hpost _ (by omega)) (by omega) hst' _ hat2
  obtain ⟨m3, hm3z, -, hrun3⟩ := fwd_reachesJ hr (.inr hz.2.1) m2 rfl
  have hst1 : step fork m1 = .ok (.next m2) := by rw [hstep1, hss]; rfl
  obtain ⟨w1, e1⟩ := hrun1 within
  obtain ⟨w3, e3⟩ := hrun3 (Nat.le_trans (gasHeld_le_of_measure_lt
    (step_decreases fork hrn1 hst1)) w1)
  have hr3 : m3.running = false := by
    have : (toNat m3).running = false := by rw [hm3z]; exact hzr
    exact this
  refine ⟨m3, ?_, ?_⟩
  · rw [e1, runFrame_of_step_eq_next hrn1 hst1, e3, runFrame_of_running_eq_false hr3]
  · have : (toNat m3).error = none := by rw [hm3z]; exact hz.2.1
    exact this

/-- **A path with one write over `StateGasMeter`, exactly.** See the module doc. -/
theorem one_write_sgm (hfork : .berlin ≤ fork)
    (hpre : ∀ g, P ≤ g → HoareG fork (At code message pc0 stk0 mem0 g state0 substate0)
      (At code message pcS (key :: new :: rest) memS (g - P) st ss))
    (hP : P < 97920) (hst0 : ∀ a k, st.getStorage a k = state0.getStorage a k)
    (hlt : pcS < code.size) (hbyte : code[pcS] = 0x55) (hstatic : message.isStatic = false)
    (hacc : hasAccount st message.currentTarget) (hcold : coldIn ss message.currentTarget key = cold)
    (hpost : ∀ g, T ≤ g → SpecG fork (At code message (pcS + 1) rest memS g
        (writeSlot st message.currentTarget key new)
        (storeSub fork ss message.currentTarget key (originalAt st message.currentTarget key)
          (storageAt st message.currentTarget key) new))
      (Halted false out (g - T) st' ss'))
    (hT : T < 97920)
    (hst' : ∀ a k, st'.getStorage a k = (writeSlot st message.currentTarget key new).getStorage a k)
    {gas : Nat} {m : Evm fork StateGasMeter}
    (start : At code message pc0 stk0 mem0 gas state0 substate0 (toNat m))
    {bound : Nat} {runChild : MessageRunner fork StateGasMeter bound}
    (within : GasMeter.gasHeld m.gas ≤ bound) :
    Shadow.RunsOkS fork bound runChild m within ↔
      P + 2301 ≤ gas ∧
      P + writeCost fork (originalAt st message.currentTarget key)
        (storageAt st message.currentTarget key) new cold + T ≤
        gas + sstoreBump m.gas (sstoreStateRefill fork (originalAt st message.currentTarget key)
            (storageAt st message.currentTarget key) new) (sstoreStateGas fork (originalAt st message.currentTarget key)
            (storageAt st message.currentTarget key) new) := by
  constructor
  · rintro ⟨s, hrun, hok⟩
    obtain ⟨h1, h2, -⟩ := one_write_end hfork hpre hP hst0 hlt hbyte hstatic hacc hcold hpost hT
      hst' start hrun hok
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact one_write_run hfork hpre hP hst0 hlt hbyte hstatic hacc hcold hpost hT hst' start h1 h2
      within

end OneWrite

end UsdtVerify.Complete
