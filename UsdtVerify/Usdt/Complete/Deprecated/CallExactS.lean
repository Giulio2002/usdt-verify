import UsdtVerify.Usdt.Complete.Deprecated.CallS
import UsdtVerify.Usdt.Complete.Deprecated.Meter
import UsdtVerify.Evm.OneWrite

/-!
# A deprecated forward over the EIP-8037 meter from EXTCODESIZE to the end, exactly (round 45)

The six deprecated paths other than destroyBlackFunds end, after the CALL, with a tail that
writes no storage: it reads the answer of the child (or reverts when the child failed) and halts.
Here that end is followed over `StateGasMeter` from the EXTCODESIZE of the upgraded address.

- `resumeG`: the frame after a CALL at `q` whose output goes to `(o, osz)` in a memory it does not
  extend: the `toNat` of the resumed frame is the frame at `q + 1` with the flag of the child, the
  start of its output written at `o`, its state, the substate of the resume and the execution gas
  left of the frame.
- `dep_call_exactS`: from a frame at EXTCODESIZE at any of the six sites (`fromExtSG`), with a
  tail at `q + 1` given as a specification over `StepG` from `T` gas on (`T` below 97,920) to a
  normal halt with `T` less, that keeps the state and the substate, for any output of the child:
  every run over `StateGasMeter` that ends with no error went through the CALL with a caller and
  message that have the meters, state, substate and `SendsVia` facts of `fromExtSG`, and a child
  with no error, `T` execution gas was left after the
  CALL, and the end is the halt of the tail with the meter after the CALL
  (`GasMeter.absorb caller.gas child.gas true`) less `T` execution gas.
-/

namespace UsdtVerify.Complete

open EthLib.Base (Fork U256 toAddressMasked Address)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic hiding SpecG StepG
open UsdtVerify.Gas
open UsdtVerify.Meter
open GasCosts
open Deprecated

variable {fork : Fork} {message : Message fork}

/-- The frame after a CALL at `q` over `StateGasMeter`, with output `(o, osz)`: the `toNat` of the
resumed frame is the frame at `q + 1` with the flag of the child, the start of its output written
at `o`, its state and the substate of the resume, with its execution gas left. -/
theorem resumeG {caller ch y : Evm fork StateGasMeter} {q : Nat} {rest : List U256}
    {M : ByteArray} {o osz : U256} (hlen : rest.length ≤ 10)
    (c1 : caller.code = CODE) (c2 : caller.validJumpDestinations = validJumpDestinations CODE)
    (c3 : caller.message = message) (c4 : caller.pc = q) (c5 : caller.stack.val = rest)
    (c6 : caller.memory = M) (c8 : caller.running = true) (c9 : caller.error = none)
    (co : caller.output = .empty)
    (hy : resumeCall fork caller 0 o osz ch = .ok y) :
    At CODE message (q + 1) ((if ch.error.isNone then 1 else 0) :: rest)
      (memoryWrite (memoryExtend M 0) o.toNat (ch.output.extract 0 (min osz.toNat ch.output.size)))
      y.gas.gasLeft (incorporateChild fork caller ch).state
      (incorporateChild fork caller ch).substate (toNat y) := by
  obtain ⟨y', hy', hty, -, -⟩ := resumeCall_sgm hy
  have hlenN : (toNat caller).stack.val.length < STACK_LIMIT := by
    show caller.stack.val.length < STACK_LIMIT
    rw [c5]; simp only [STACK_LIMIT]; omega
  obtain ⟨after, ha, a1, a2, a3, a4, a5, a6, -, a8, a9, ao, a10, a11, -⟩ :=
    resumeCall_eq (child := toNat ch) (o := o) (osz := osz) hlenN
  rw [hy'] at ha
  cases ha
  obtain ⟨i1, i2⟩ := incorporateChild_toNat caller ch (toNat ch) rfl rfl rfl rfl
  rw [hty]
  refine ⟨a1.trans c1, a2.trans c2, a3.trans c3, by rw [a4]; exact congrArg (· + 1) c4,
    by rw [a5]; exact congrArg _ c5, ?_, rfl, a8.trans c8, a9.trans c9, ao.trans co,
    a10.trans i1, a11.trans i2⟩
  rw [a6]
  show memoryWrite caller.memory _ _ = _
  rw [c6, memoryExtend_zero]
  rfl

/-- **A deprecated forward over the EIP-8037 meter from EXTCODESIZE to the end, exactly.** See the
module doc. The hypotheses up to `start` are those of `fromExtSG`. -/
theorem dep_call_exactS (hfork : .berlin ≤ fork) {p q : Nat}
    (hp : (p = 3719 ∧ q = 3736) ∨ (p = 4874 ∧ q = 4891) ∨ (p = 5739 ∧ q = 5756) ∨
      (p = 3213 ∧ q = 3230) ∨ (p = 4200 ∧ q = 4217) ∨ (p = 7186 ∧ q = 7203))
    {U i isz o osz : U256} {rest : List U256} (hrest : rest.length ≤ 10)
    {M : ByteArray} (hM : extendMemory M.size [(i, isz), (o, osz)] = ⟨0, 0⟩)
    {st : State.TransactionState} {ss : Substate} {c : ByteArray} {r : Route}
    (hcode : st.getCode (st.getAccount (toAddressMasked U)).codeHash = .ok c)
    (hw : BitVec.ofNat 256 c.size ≠ 0) (hroute : Routes fork st c r)
    (hdepth : message.depth + 1 ≤ STACK_DEPTH_LIMIT)
    {A R : Nat} (hA : extCost fork (decide (toAddressMasked U ∉ ss.accessedAddresses)) = A)
    (hR : routeCost fork (ss.accessedAddresses.insert (toAddressMasked U)) r = R)
    {G : Nat} (hg : A + 128 + R ≤ G)
    {T : Nat} (hT : T < 97920) {out : ByteArray → ByteArray}
    (htail : ∀ (ob : ByteArray) (S : State.TransactionState) (sb : Substate) (g : Nat), T ≤ g →
      SpecG fork (At CODE message (q + 1) (1 :: rest)
        (memoryWrite (memoryExtend M 0) o.toNat (ob.extract 0 (min osz.toNat ob.size))) g S sb)
        (Halted false (out ob) (g - T) S sb))
    {m s : Evm fork StateGasMeter}
    (start : At CODE message p (U :: U :: 0 :: i :: isz :: o :: osz :: rest) M G st ss
      (toNat m))
    {bound : Nat} {runChild : MessageRunner fork StateGasMeter bound}
    {within : GasMeter.gasHeld m.gas ≤ bound}
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild m within = .ok s)
    (hok : s.error = none) :
    ∃ caller msg lt child, runChild caller msg lt = .ok child ∧ child.1.error = none ∧
      caller.gas = { m.gas with reservoir := 0, gasLeft := G - (A + 28) -
        (depCallGas fork (asked (G - (A + 25))) (G - (A + 28)) R).cost } ∧
      msg.reservoir = m.gas.reservoir ∧
      msg.gas = (depCallGas fork (asked (G - (A + 25))) (G - (A + 28)) R).subCall ∧
      SendsVia message (toAddressMasked U) c r (memoryReadBytes M i.toNat isz.toNat) msg ∧
      caller.state = (routeState ((st.recordAccountRead (toAddressMasked U)).recordAccountRead
        (toAddressMasked U)) r).recordAccountRead message.currentTarget ∧
      caller.substate = routeSub { ss with
        accessedAddresses := (ss.accessedAddresses.insert (toAddressMasked U)).insert
          (toAddressMasked U) } r ∧
      (GasMeter.absorb caller.gas child.1.gas true).gasLeft +
          (GasMeter.absorb caller.gas child.1.gas true).reservoir =
        caller.gas.gasLeft + child.1.gas.gasLeft + child.1.gas.reservoir ∧
      T ≤ (GasMeter.absorb caller.gas child.1.gas true).gasLeft ∧
      s.running = false ∧ s.output = out child.1.output ∧
      s.state = (incorporateChild fork caller child.1).state ∧
      s.substate = (incorporateChild fork caller child.1).substate ∧
      s.gas = { GasMeter.absorb caller.gas child.1.gas true with
        gasLeft := (GasMeter.absorb caller.gas child.1.gas true).gasLeft - T } := by
  have hf : (q + 1 = 3737 ∨ q + 1 = 4892 ∨ q + 1 = 5757 ∨ q + 1 = 3231 ∨ q + 1 = 4218) ∨
      q + 1 = 7204 := by
    rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
  obtain ⟨mC, caller, msg, -, hrC, hrunC, hstepC, k1, k2, k3, k4, k5, k6, k7, k8, k9, ko, k10,
      k11, m0, mg, mcl, mct, mtg, mca, mcode, mdp, md, mv, mdep, mst, mbe, mte, msh⟩ :=
    fromExtSG hfork hp hrest hM hcode hw hroute hdepth hA hR hg start
  -- through the runner and the resume
  obtain ⟨wC, eC⟩ := hrunC within
  rw [eC] at hrun
  obtain ⟨lt, chS, y, hch, hy, wy, hrunY⟩ := runFrame_childS hrC hstepC hrun hok
  have hat := resumeG hrest k1 k2 k3 k4 k5 k6 k8 k9 ko hy
  obtain ⟨Gs, hEnds⟩ := Shadow.shadow_ends hfork hrunY hok
  have hatS := at_addGas hat (Shadow.budget y)
  -- the child ended with no error
  have he : chS.1.error = none := by
    refine Classical.byContradiction fun hne => ?_
    have hz : chS.1.error.isNone = false := by
      cases h : chS.1.error
      · exact absurd h hne
      · rfl
    rw [hz] at hatS
    rcases hf with hf | hf
    · exact no_okE (fun g hg => failTail hfork hf (by omega) hg)
        (fun g e h => by rw [h.2.1]; simp) hatS hEnds hok
    · rw [hf] at hatS
      exact no_okE (fun g hg => DeprecatedAllowance.failTailA hfork (by omega) hg)
        (fun g e h => by rw [h.2.1]; simp) hatS hEnds hok
  simp only [he, Option.isNone_none, ↓reduceIte] at hat
  -- the meter after the CALL
  have hlenC : caller.stack.val.length < STACK_LIMIT := by
    rw [k5]; simp only [STACK_LIMIT]; omega
  obtain ⟨y2, hy2, -, -, -, -, -, -, hgy, -⟩ := resumeCall_okS (o := o) (osz := osz) hlenC he
  rw [hy] at hy2
  cases hy2
  -- the tail
  obtain ⟨hTg, hr, ho, hgl, hgs, hst, hss⟩ := ok_exactS (Nat.le_refl T)
    (htail chS.1.output _ _) hT (fun _ _ => rfl) hat hrunY hok
  rw [hgy] at hTg hgl hgs
  have hr0 : caller.gas.reservoir = 0 := by rw [k7]
  refine ⟨caller, msg, lt, chS, hch, he, k7, m0, mg,
    ⟨mcl, mct, mtg, mca, mcode, mdp, md, mv, mdep, mst, mbe, mte, msh⟩, k10, k11, ?_, hTg, hr, ho, hst, hss, ?_⟩
  · rw [absorb_sum, hr0, Nat.add_zero]
  · rw [hgs, hgl]

end UsdtVerify.Complete
