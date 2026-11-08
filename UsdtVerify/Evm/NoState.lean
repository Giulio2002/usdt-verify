import UsdtVerify.Evm.Refill

/-!
# Where an SSTORE charges no state gas (round 42)

From Glamsterdam, SSTORE charges state gas (`sstoreStateGas`, 97,920) when it writes a word that
is not 0 into a slot that is 0 and was 0 at the start of the transaction. Over `StateGasMeter`
that charge comes from the reservoir first, so with a reservoir above 0 the execution gas left no
longer follows the gas of the meter `Nat`. This file proves, over the meter `Nat`, that no SSTORE
along a cheap stretch of a run charges state gas or refills.

- `NoStateN`, `NoStateAtN`: an SSTORE at the program counter, if there is one, charges no state
  gas.
- `noState_cheapE`: a frame that a `StepG` chain passes, with less than 97,920 gas paid from the
  first frame to the end, and an end with no error or with gas left, charges no state gas at an
  SSTORE. No fact on the storage is needed: the charge alone is 97,920.
- `StepJ`, `HoareJ`: steps over `StepG` from frames that neither refill nor charge state gas at an
  SSTORE, and their triples. `HoareG.toJE` and `HoareG.toJA` are `HoareG.toIE` and
  `HoareG.toIA` over `StepJ`.
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

/-- An SSTORE from `x` charges no state gas: for the key and the new word on top of the stack,
the charge of `sstoreStateGas` is 0. -/
def NoStateN (x : Evm fork Nat) : Prop :=
  ∀ key new rest, x.stack.val = key :: new :: rest →
    sstoreStateGas fork (x.state.getStorageOriginal x.message.currentTarget key.toBeBytes)
      (x.state.getStorage x.message.currentTarget key.toBeBytes) new = 0

/-- An SSTORE at the program counter of `x`, if there is one, charges no state gas. -/
def NoStateAtN (x : Evm fork Nat) : Prop :=
  ∀ h : x.pc < x.code.size, Op.ofByte fork x.code[x.pc] = some .sstore → NoStateN x

/-- `NoStateAtN` reads no gas. -/
theorem noStateAtN_sh {x : Evm fork Nat} (k : Nat) (h : NoStateAtN (sh k x)) : NoStateAtN x :=
  h

/-- **No state gas along a cheap stretch.** A frame `y` that a `StepG` chain passes from `c` to
`e`, with a step to `y1` from which the chain goes on to `e`, charges no state gas at an SSTORE,
when less than `STORAGE_SET_STATE_GAS` is paid from `c` to `e` and `e` has no error or has gas
left. -/
theorem noState_cheapE {c y y1 e : Evm fork Nat} (hcy : Reaches (StepG fork) c y)
    (hy : StepG fork y y1) (hye : Reaches (StepG fork) y1 e) (herr : e.error = none ∨ 0 < e.gas)
    (hgas : c.gas < e.gas + STORAGE_SET_STATE_GAS) : NoStateAtN y := by
  intro hlt hop key new rest hst
  apply Classical.byContradiction
  intro hS
  obtain ⟨-, -, hcur, hnew⟩ := sstoreStateGas_ne_zero hS
  have hval : sstoreStateGas fork
      (y.state.getStorageOriginal y.message.currentTarget key.toBeBytes)
      (y.state.getStorage y.message.currentTarget key.toBeBytes) new = STORAGE_SET_STATE_GAS := by
    unfold sstoreStateGas at hS ⊢
    split at hS
    · exact ite_eq_left ‹_›
    · exact absurd rfl hS
  obtain ⟨gcy, -⟩ := chain_store hcy
  obtain ⟨gye, -⟩ := chain_store hye
  obtain ⟨-, -, ch⟩ := step_store hy.1 hy.2.1
  rcases step_sstore hy.1 hlt hop hst with ⟨hr1, he1, hg1⟩ | hw
  · have := reaches_stopped (reaches_toStep hye) hr1
    rw [this] at herr
    rcases herr with h | h
    · exact he1 h
    · rw [hg1] at h
      exact absurd h (Nat.lt_irrefl 0)
  · obtain ⟨key', new', rest', hst', -, hk, hw', hg⟩ :=
      ch y.message.currentTarget key.toBeBytes (by rw [hw, hcur]; exact hnew)
    rw [hst] at hst'
    simp only [List.cons.injEq] at hst'
    obtain ⟨rfl, rfl, -⟩ := hst'
    rw [hval] at hg
    omega

/-! ## Triples whose steps neither refill nor charge state gas -/

/-- A step over `StepG` from a frame where an SSTORE neither refills nor charges state gas. -/
def StepJ (fork : Fork) (x y : Evm fork Nat) : Prop :=
  StepG fork x y ∧ NoRefillAtN x ∧ NoStateAtN x

/-- A triple over the steps of `StepJ`. -/
abbrev HoareJ (fork : Fork) (P Q : Evm fork Nat → Prop) : Prop := Triple (StepJ fork) P Q

instance : StepLift (StepJ fork) (StepG fork) := ⟨And.left⟩

theorem reaches_liftJ {c e : Evm fork Nat} (h : Reaches (StepG fork) c e)
    (hJ : ∀ y y1, Reaches (StepG fork) c y → StepG fork y y1 → Reaches (StepG fork) y1 e →
      NoRefillAtN y ∧ NoStateAtN y) : Reaches (StepJ fork) c e := by
  induction h with
  | refl => exact .refl _
  | step hs hr ih =>
    exact .step ⟨hs, hJ _ _ (.refl _) hs hr⟩
      (ih fun y y1 hcy hy hye => hJ y y1 (.step hs hcy) hy hye)

/-- **A cheap stretch over `StepJ`.** `HoareG.toIE` over `StepJ`: a triple over `StepG` whose two
ends read the same storage, with less than `STORAGE_SET_STATE_GAS` paid and an end with no error or
with gas left, is one over `StepJ`. -/
theorem HoareG.toJE {P Q : Evm fork Nat → Prop} (h : HoareG fork P Q)
    (hc : ∀ c e, P c → Q e → c.gas < e.gas + STORAGE_SET_STATE_GAS ∧
      (e.error = none ∨ 0 < e.gas) ∧
      ∀ a k, e.state.getStorage a k = c.state.getStorage a k) : HoareJ fork P Q := by
  intro c hp
  obtain ⟨e, hr, hq⟩ := h c hp
  obtain ⟨hg, herr, hs⟩ := hc c e hp hq
  exact ⟨e, reaches_liftJ hr fun y y1 hcy hy hye =>
    ⟨noRefill_cheapE hcy hy hye herr hg hs, noState_cheapE hcy hy hye herr hg⟩, hq⟩

/-- `HoareG.toJE` between two `At` frames: the storage of the second state reads as that of the
first, and less than 97,920 gas is paid (`HoareG.toIA` over `StepJ`). -/
theorem HoareG.toJA {code code' : ByteArray} {message message' : Message fork} {pc pc' : Nat}
    {stack stack' : List U256} {memory memory' : ByteArray} {g g' : Nat}
    {st st' : State.TransactionState} {ss ss' : Substate}
    (h : HoareG fork (At code message pc stack memory g st ss)
      (At code' message' pc' stack' memory' g' st' ss'))
    (hg : g < g' + 97920) (hs : ∀ a k, st'.getStorage a k = st.getStorage a k) :
    HoareJ fork (At code message pc stack memory g st ss)
      (At code' message' pc' stack' memory' g' st' ss') :=
  HoareG.toJE h fun c e hc he => by
    rw [hc.2.2.2.2.2.2.1, he.2.2.2.2.2.2.1, he.2.2.2.2.2.2.2.2.1, he.2.2.2.2.2.2.2.2.2.2.1,
      hc.2.2.2.2.2.2.2.2.2.2.1]
    exact ⟨hg, .inl rfl, hs⟩

/-- `SpecG.toIA` over `StepJ`: a specification from an `At` frame to a normal halt that keeps the
storage and pays less than 97,920. -/
theorem SpecG.toJA {code : ByteArray} {message : Message fork} {pc : Nat}
    {stack : List U256} {memory out : ByteArray} {g g' : Nat}
    {st st' : State.TransactionState} {ss ss' : Substate}
    (h : SpecG fork (At code message pc stack memory g st ss) (Halted false out g' st' ss'))
    (hg : g < g' + 97920) (hs : ∀ a k, st'.getStorage a k = st.getStorage a k) :
    HoareJ fork (At code message pc stack memory g st ss)
      (fun evm => evm.running = false ∧ Halted false out g' st' ss' evm) :=
  HoareG.toJE h fun c e hc ⟨_, he⟩ => by
    rw [hc.2.2.2.2.2.2.1, he.2.2.2.1, he.2.2.2.2.1, he.2.1, hc.2.2.2.2.2.2.2.2.2.2.1]
    exact ⟨hg, .inl rfl, hs⟩

/-- A `StepJ` chain is a `StepI` chain. -/
theorem reaches_JI {c e : Evm fork Nat} (h : Reaches (StepJ fork) c e) : Reaches (StepI fork) c e :=
  h.mono fun hs => ⟨hs.1, hs.2.1⟩

end UsdtVerify.Refill
