import UsdtVerify.Evm.GasRules
import EthLib.Execution.Transactions.Settlement

/-!
# The EIP-8037 meter and the one-counter meter

EthLib runs Glamsterdam transactions with the meter `StateGasMeter` and earlier forks with the
meter `Nat`. Every opcode rule of this repository is about `Nat`. This file relates the two.

- `toNat m`: the frame of the meter `Nat` with the fields of `m`, and as gas the execution gas
  left of `m`. `lift g n`: the frame of the meter `StateGasMeter` with the fields of `n`, and the
  meter `g` with the gas of `n` as its execution gas left.
- `Lifts runS runN`: on `lift g n`, the instruction `runS` gives the result of `runN` on `n`,
  mapped by `lift g`. It holds for the instructions of the opcodes of `simulated` other than
  SSTORE (`lifts_*`): they charge execution gas only.
- `sim_sstoreStep`: SSTORE, from a frame with reservoir 0 where the refill of
  `sstoreStateRefill` is 0 (`NoRefill`), gives the same error or the `toNat` of its result.
- `step_sim`: one step from a frame with reservoir 0, `SimAt` (an opcode of `simulated`, or no
  opcode) and no refill at an SSTORE: the same error, or the next frame and its `toNat`, with
  reservoir 0 or stopped.
- `ends_of_sgm`: a run of the interpreter loop over `StateGasMeter`, for any gas bound and
  message runner, from a frame with reservoir 0 where no SSTORE that the steps reach refills:
  `Ends` holds from `toNat` of the start to `toNat` of the end. The completeness and invariant
  theorems that take `Ends` then apply to it.
-/

namespace UsdtVerify.Meter

open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open UsdtVerify.Gas
open GasCosts

variable {fork : Fork}

/-- The frame of the meter `StateGasMeter` with the fields of `n`, and as meter `g` with the
execution gas left of `n`. -/
def lift (g : StateGasMeter) (n : Evm fork Nat) : Evm fork StateGasMeter :=
  { pc := n.pc, stack := n.stack, memory := n.memory, code := n.code,
    validJumpDestinations := n.validJumpDestinations, gas := { g with gasLeft := n.gas },
    running := n.running, message := n.message, output := n.output, returnData := n.returnData,
    state := n.state, substate := n.substate, error := n.error }

/-- The frame of the meter `Nat` with the fields of `m`, and as gas its execution gas left. -/
def toNat (m : Evm fork StateGasMeter) : Evm fork Nat :=
  { pc := m.pc, stack := m.stack, memory := m.memory, code := m.code,
    validJumpDestinations := m.validJumpDestinations, gas := m.gas.gasLeft,
    running := m.running, message := m.message, output := m.output, returnData := m.returnData,
    state := m.state, substate := m.substate, error := m.error }

theorem lift_toNat (m : Evm fork StateGasMeter) : lift m.gas (toNat m) = m := rfl

theorem popWord_lift (g : StateGasMeter) (n : Evm fork Nat) :
    popWord (lift g n) = (popWord n).map (fun p => (p.1, lift g p.2)) := by
  rcases n with ⟨pc, ⟨_ | ⟨x, rest⟩, hp⟩⟩ <;> rfl

theorem pushWord_lift (g : StateGasMeter) (n : Evm fork Nat) (x : U256) :
    pushWord (lift g n) x = (pushWord n x).map (lift g) := by
  by_cases h : n.stack.val.length = STACK_LIMIT <;>
    simp [pushWord, Stack.push, h, bind, Except.bind, Except.map, pure, Except.pure, lift]

theorem chargeGas_lift (g : StateGasMeter) (n : Evm fork Nat) (c : Nat) :
    chargeGas (lift g n) c = (chargeGas n c).map (lift g) := by
  by_cases h : n.gas < c <;>
    simp [chargeGas, GasMeter.charge, StateGasMeter.charge, lift, h, bind, Except.bind,
      Except.map, pure, Except.pure]

theorem binaryOp_lift (cost : Nat) (f : U256 → U256 → U256) (g : StateGasMeter) (n : Evm fork Nat) :
    binaryOp cost f (lift g n) = (binaryOp cost f n).map (lift g) := by
  unfold binaryOp
  rw [popWord_lift]
  rcases popWord n with e | ⟨x, a⟩
  · rfl
  simp only [Except.map, bind, Except.bind]
  rw [popWord_lift]
  rcases popWord a with e | ⟨y, b⟩
  · rfl
  simp only [Except.map]
  rw [chargeGas_lift]
  rcases chargeGas b cost with e | c
  · rfl
  simp only [Except.map]
  rw [pushWord_lift]
  rcases pushWord c (f x y) with e | d
  · rfl
  rfl

theorem chargeGasAndMemory_lift (g : StateGasMeter) (n : Evm fork Nat) (c : Nat)
    (r : List (U256 × U256)) :
    chargeGasAndMemory (lift g n) c r = (chargeGasAndMemory n c r).map (lift g) := by
  unfold chargeGasAndMemory
  dsimp only
  rw [show (lift g n).memory = n.memory from rfl, chargeGas_lift]
  rcases chargeGas n _ with e | c
  · rfl
  rfl

/-- The instruction `runS` of the meter `StateGasMeter` on a frame with meter `g` is the
instruction `runN` of the meter `Nat` on that frame with its execution gas, with `g` for the rest
of the meter. -/
def Lifts (runS : Evm fork StateGasMeter → Except EvmError (Evm fork StateGasMeter))
    (runN : Evm fork Nat → Except EvmError (Evm fork Nat)) : Prop :=
  ∀ g n, runS (lift g n) = (runN n).map (lift g)

theorem lifts_unaryOp (cost : Nat) (f : U256 → U256) : Lifts (fork := fork) (unaryOp cost f)
    (unaryOp cost f) := by
  intro g n
  unfold unaryOp
  rw [popWord_lift]
  rcases popWord n with e | ⟨x, a⟩
  · rfl
  simp only [Except.map, bind, Except.bind]
  rw [chargeGas_lift]
  rcases chargeGas a cost with e | c
  · rfl
  simp only [Except.map]
  rw [pushWord_lift]
  rcases pushWord c (f x) with e | d
  · rfl
  rfl

theorem lifts_binaryOp (cost : Nat) (f : U256 → U256 → U256) :
    Lifts (fork := fork) (binaryOp cost f) (binaryOp cost f) := binaryOp_lift cost f

theorem lifts_expStep : Lifts (fork := fork) (expStep fork) (expStep fork) := by
  intro g n
  unfold expStep
  rw [popWord_lift]
  rcases popWord n with e | ⟨x, a⟩
  · rfl
  simp only [Except.map, bind, Except.bind]
  rw [popWord_lift]
  rcases popWord a with e | ⟨y, b⟩
  · rfl
  simp only [Except.map]
  rw [chargeGas_lift]
  rcases chargeGas b _ with e | c
  · rfl
  simp only [Except.map]
  rw [pushWord_lift]
  rcases pushWord c _ with e | d
  · rfl
  rfl

theorem lifts_keccak256Step : Lifts (fork := fork) keccak256Step keccak256Step := by
  intro g n
  unfold keccak256Step
  rw [popWord_lift]
  rcases popWord n with e | ⟨x, a⟩
  · rfl
  simp only [Except.map, bind, Except.bind]
  rw [popWord_lift]
  rcases popWord a with e | ⟨y, b⟩
  · rfl
  simp only [Except.map]
  rw [chargeGasAndMemory_lift]
  rcases chargeGasAndMemory b _ _ with e | c
  · rfl
  simp only [Except.map]
  rw [show (lift g c).memory = c.memory from rfl, pushWord_lift]
  rcases pushWord c _ with e | d
  · rfl
  rfl

theorem lifts_popStep : Lifts (fork := fork) popStep popStep := by
  intro g n
  unfold popStep
  rw [popWord_lift]
  rcases popWord n with e | ⟨x, a⟩
  · rfl
  simp only [Except.map, bind, Except.bind]
  rw [chargeGas_lift]
  rcases chargeGas a _ with e | c
  · rfl
  rfl

theorem lifts_pushN (k : Fin 33) : Lifts (fork := fork) (pushN k) (pushN k) := by
  intro g n
  unfold pushN
  rw [chargeGas_lift]
  rcases chargeGas n _ with e | c
  · rfl
  simp only [Except.map, bind, Except.bind]
  rw [show (lift g c).code = c.code from rfl, show (lift g c).pc = c.pc from rfl, pushWord_lift]
  rcases pushWord c _ with e | d
  · rfl
  rfl

theorem lifts_dupN (k : Fin 16) : Lifts (fork := fork) (dupN k) (dupN k) := by
  intro g n
  unfold dupN
  rw [chargeGas_lift]
  rcases chargeGas n _ with e | c
  · rfl
  simp only [Except.map, bind, Except.bind]
  rw [show (lift g c).stack = c.stack from rfl]
  rcases c.stack.val[k.val]? with _ | x
  · rfl
  simp only []
  rw [pushWord_lift]
  rcases pushWord c x with e | d
  · rfl
  rfl

theorem lifts_swapN (k : Fin 16) : Lifts (fork := fork) (swapN k) (swapN k) := by
  intro g n
  unfold swapN
  rw [chargeGas_lift]
  rcases chargeGas n _ with e | c
  · rfl
  simp only [Except.map, bind, Except.bind]
  rw [show (lift g c).stack = c.stack from rfl]
  rcases hs : c.stack with ⟨_ | ⟨top, rest⟩, hp⟩
  · rfl
  simp only []
  rcases rest[k.val]? with _ | x
  · rfl
  rfl

theorem lifts_calldataloadStep : Lifts (fork := fork) calldataloadStep calldataloadStep := by
  intro g n
  unfold calldataloadStep
  rw [popWord_lift]
  rcases popWord n with e | ⟨x, a⟩
  · rfl
  simp only [Except.map, bind, Except.bind]
  rw [chargeGas_lift]
  rcases chargeGas a _ with e | c
  · rfl
  simp only [Except.map]
  rw [show (lift g c).message = c.message from rfl, pushWord_lift]
  rcases pushWord c _ with e | d
  · rfl
  rfl

theorem lifts_readFrame (cost : Nat) (vS : Evm fork StateGasMeter → U256)
    (vN : Evm fork Nat → U256) (hv : ∀ g n, vS (lift g n) = vN n) :
    Lifts (readFrame cost vS) (readFrame cost vN) := by
  intro g n
  unfold readFrame
  rw [chargeGas_lift]
  rcases chargeGas n _ with e | c
  · rfl
  simp only [Except.map, bind, Except.bind]
  rw [hv, pushWord_lift]
  rcases pushWord c _ with e | d
  · rfl
  rfl

theorem lifts_mloadStep : Lifts (fork := fork) mloadStep mloadStep := by
  intro g n
  unfold mloadStep
  rw [popWord_lift]
  rcases popWord n with e | ⟨x, a⟩
  · rfl
  simp only [Except.map, bind, Except.bind]
  rw [chargeGasAndMemory_lift]
  rcases chargeGasAndMemory a _ _ with e | c
  · rfl
  simp only [Except.map]
  rw [show (lift g c).memory = c.memory from rfl, pushWord_lift]
  rcases pushWord c _ with e | d
  · rfl
  rfl

theorem lifts_mstoreStep : Lifts (fork := fork) mstoreStep mstoreStep := by
  intro g n
  unfold mstoreStep
  rw [popWord_lift]
  rcases popWord n with e | ⟨x, a⟩
  · rfl
  simp only [Except.map, bind, Except.bind]
  rw [popWord_lift]
  rcases popWord a with e | ⟨y, b⟩
  · rfl
  simp only [Except.map]
  rw [chargeGasAndMemory_lift]
  rcases chargeGasAndMemory b _ _ with e | c
  · rfl
  rfl

theorem lifts_jumpStep : Lifts (fork := fork) jumpStep jumpStep := by
  intro g n
  unfold jumpStep
  rw [popWord_lift]
  rcases popWord n with e | ⟨x, a⟩
  · rfl
  simp only [Except.map, bind, Except.bind]
  rw [chargeGas_lift]
  rcases chargeGas a _ with e | c
  · rfl
  simp only [Except.map]
  rw [show (lift g c).validJumpDestinations = c.validJumpDestinations from rfl]
  split <;> rfl

theorem lifts_jumpiStep : Lifts (fork := fork) jumpiStep jumpiStep := by
  intro g n
  unfold jumpiStep
  rw [popWord_lift]
  rcases popWord n with e | ⟨x, a⟩
  · rfl
  simp only [Except.map, bind, Except.bind]
  rw [popWord_lift]
  rcases popWord a with e | ⟨y, b⟩
  · rfl
  simp only [Except.map]
  rw [chargeGas_lift]
  rcases chargeGas b _ with e | c
  · rfl
  simp only [Except.map]
  rw [show (lift g c).validJumpDestinations = c.validJumpDestinations from rfl]
  split
  · rfl
  split <;> rfl

theorem lifts_jumpdestStep : Lifts (fork := fork) jumpdestStep jumpdestStep := by
  intro g n
  unfold jumpdestStep
  rw [chargeGas_lift]
  rcases chargeGas n _ with e | c
  · rfl
  rfl

theorem lifts_stopStep : Lifts (fork := fork) stopStep stopStep := fun _ _ => rfl

theorem lifts_returnStep : Lifts (fork := fork) returnStep returnStep := by
  intro g n
  unfold returnStep haltWithOutput
  rw [popWord_lift]
  rcases popWord n with e | ⟨x, a⟩
  · rfl
  simp only [Except.map, bind, Except.bind]
  rw [popWord_lift]
  rcases popWord a with e | ⟨y, b⟩
  · rfl
  simp only [Except.map]
  rw [chargeGasAndMemory_lift]
  rcases chargeGasAndMemory b _ _ with e | c
  · rfl
  rfl

theorem lifts_revertStep : Lifts (fork := fork) revertStep revertStep := by
  intro g n
  rw [revertStep_eq, revertStep_eq, lifts_returnStep g n]
  rcases returnStep n with e | c <;> rfl

theorem popTopics_lift (g : StateGasMeter) : ∀ (k : Nat) (n : Evm fork Nat),
    popTopics (lift g n) k = (popTopics n k).map (fun p => (p.1, lift g p.2))
  | 0, _ => rfl
  | k + 1, n => by
    simp only [popTopics]
    rw [popWord_lift]
    rcases popWord n with e | ⟨w, b⟩
    · rfl
    simp only [Except.map, bind, Except.bind]
    rw [popTopics_lift g k b]
    rcases popTopics b k with e | ⟨t, c⟩ <;> rfl

theorem lifts_logStep (k : Nat) : Lifts (fork := fork) (logStep k) (logStep k) := by
  intro g n
  unfold logStep
  rw [popWord_lift]
  rcases popWord n with e | ⟨x, a⟩
  · rfl
  simp only [Except.map, bind, Except.bind]
  rw [popWord_lift]
  rcases popWord a with e | ⟨y, b⟩
  · rfl
  simp only [Except.map]
  rw [popTopics_lift]
  rcases popTopics b k with e | ⟨t, c⟩
  · rfl
  simp only [Except.map]
  rw [chargeGasAndMemory_lift]
  rcases chargeGasAndMemory c _ _ with e | d
  · rfl
  simp only [Except.map]
  rw [show (lift g d).message = d.message from rfl]
  split <;> rfl

theorem accessStorageKey_lift (g : StateGasMeter) (n : Evm fork Nat) (a : EthLib.Base.Address)
    (k : EthLib.Base.Bytes32) :
    accessStorageKey (lift g n) a k =
      ((accessStorageKey n a k).1, lift g (accessStorageKey n a k).2) := by
  simp only [accessStorageKey]
  split <;> rfl

theorem lifts_sloadStep : Lifts (fork := fork) sloadStep sloadStep := by
  intro g n
  unfold sloadStep
  rw [popWord_lift]
  rcases popWord n with e | ⟨x, a⟩
  · rfl
  simp only [Except.map, bind, Except.bind]
  rw [show (lift g a).message = a.message from rfl, accessStorageKey_lift]
  generalize accessStorageKey a _ _ = p
  rcases p with ⟨cold, b⟩
  simp only []
  rw [chargeGas_lift]
  rcases chargeGas b _ with e | c
  · rfl
  simp only [Except.map]
  rw [show recordStorageRead (lift g c) a.message.currentTarget x.toBeBytes =
    lift g (recordStorageRead c a.message.currentTarget x.toBeBytes) from rfl,
    show (lift g (recordStorageRead c a.message.currentTarget x.toBeBytes)).state =
      (recordStorageRead c a.message.currentTarget x.toBeBytes).state from rfl, pushWord_lift]
  rcases pushWord _ _ with e | d
  · rfl
  rfl

/-! ## Corresponding results -/

/-- A result of the meter `StateGasMeter` and a result of the meter `Nat` that correspond: the
same error, or a frame and its `toNat`, whose reservoir is 0 or which is stopped. -/
def Corr (rS : Except EvmError (Evm fork StateGasMeter)) (rN : Except EvmError (Evm fork Nat)) :
    Prop :=
  (∃ e, rS = .error e ∧ rN = .error e) ∨
    ∃ m, rS = .ok m ∧ rN = .ok (toNat m) ∧ (m.gas.reservoir = 0 ∨ m.running = false)

/-- An SSTORE from `m` refills no state gas: for the key and the new word on top of the stack,
the refill of `sstoreStateRefill` is 0. -/
def NoRefill (m : Evm fork StateGasMeter) : Prop :=
  ∀ key new rest, m.stack.val = key :: new :: rest →
    sstoreStateRefill fork (m.state.getStorageOriginal m.message.currentTarget key.toBeBytes)
      (m.state.getStorage m.message.currentTarget key.toBeBytes) new = 0

/-- From every frame with reservoir 0 whose SSTORE refills nothing, the instructions `runS` and
`runN` give corresponding results. -/
def SimRun (runS : Evm fork StateGasMeter → Except EvmError (Evm fork StateGasMeter))
    (runN : Evm fork Nat → Except EvmError (Evm fork Nat)) : Prop :=
  ∀ m, m.gas.reservoir = 0 → NoRefill m → Corr (runS m) (runN (toNat m))

theorem Lifts.corr {runS : Evm fork StateGasMeter → Except EvmError (Evm fork StateGasMeter)}
    {runN : Evm fork Nat → Except EvmError (Evm fork Nat)} (h : Lifts runS runN)
    {m : Evm fork StateGasMeter} (hr : m.gas.reservoir = 0) : Corr (runS m) (runN (toNat m)) := by
  have e := h m.gas (toNat m)
  rw [lift_toNat] at e
  rw [e]
  rcases runN (toNat m) with e | n
  · exact .inl ⟨e, rfl, rfl⟩
  · exact .inr ⟨lift m.gas n, rfl, rfl, .inl hr⟩

/-! ## SSTORE -/

theorem popWord_ok {n a : Evm fork Nat} {x : U256} (h : popWord n = .ok (x, a)) :
    n.stack.val = x :: a.stack.val ∧ a.state = n.state ∧ a.message = n.message := by
  rcases n with ⟨pc, ⟨_ | ⟨y, rest⟩, hp⟩⟩
  · cases h
  · simp only [popWord, Stack.pop, bind, Except.bind, pure, Except.pure, Except.ok.injEq,
      Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, rfl, rfl⟩

theorem refill_zero (meter : StateGasMeter) : StateGasMeter.refill meter 0 = meter := by
  simp [StateGasMeter.refill]

theorem chargeStateGas_lift {g : StateGasMeter} (hr : g.reservoir = 0) (n : Evm fork Nat)
    (d : Nat) :
    chargeStateGas (lift g n) d = (chargeStateGas n d).map (lift { g with spill := g.spill + d }) := by
  rcases g with ⟨gl, res, base, sp, com, gr⟩
  simp only at hr
  subst hr
  by_cases h0 : d = 0
  · subst h0
    simp [chargeStateGas, GasMeter.chargeState, StateGasMeter.chargeState, lift, bind,
      Except.bind, Except.map, pure, Except.pure]
  · by_cases h : n.gas < d
    · have h1 : ¬ d ≤ 0 := by omega
      have h3 : ¬ d ≤ n.gas := by omega
      simp [chargeStateGas, GasMeter.chargeState, StateGasMeter.chargeState, lift, bind,
        Except.bind, Except.map, h, h1, h3]
    · have h1 : ¬ d ≤ 0 := by omega
      have h3 : d ≤ n.gas := by omega
      simp [chargeStateGas, GasMeter.chargeState, StateGasMeter.chargeState, lift, bind,
        Except.bind, Except.map, pure, Except.pure, h, h1, h3]

theorem keepReads_corr {g g' : StateGasMeter} (hr : g'.reservoir = 0) {b : Evm fork Nat}
    {rS : Except EvmError (Evm fork StateGasMeter)} {rN : Except EvmError (Evm fork Nat)}
    (h : rS = rN.map (lift g')) : Corr (keepReads (lift g b) id rS) (keepReads b id rN) := by
  subst h
  rcases rN with e | r
  · simp only [keepReads, Except.map]
    split
    · exact .inl ⟨e, rfl, rfl⟩
    · exact .inr ⟨_, rfl, rfl, .inr rfl⟩
  · exact .inr ⟨lift g' r, rfl, rfl, .inl hr⟩

theorem sim_sstoreStep : SimRun (fork := fork) sstoreStep sstoreStep := by
  intro m hr hnr
  obtain ⟨g, n, rfl⟩ : ∃ g n, m = lift g n := ⟨m.gas, toNat m, rfl⟩
  change g.reservoir = 0 at hr
  show Corr (sstoreStep (lift g n)) (sstoreStep n)
  unfold sstoreStep
  rw [show (lift g n).message = n.message from rfl]
  split
  · exact .inl ⟨_, rfl, rfl⟩
  simp only [bind, Except.bind]
  rw [popWord_lift]
  rcases h1 : popWord n with e | ⟨word, a1⟩
  · exact .inl ⟨e, rfl, rfl⟩
  simp only [Except.map]
  rw [popWord_lift]
  rcases h2 : popWord a1 with e | ⟨new, a2⟩
  · exact .inl ⟨e, rfl, rfl⟩
  simp only [Except.map]
  obtain ⟨s1, t1, m1⟩ := popWord_ok h1
  obtain ⟨s2, t2, m2⟩ := popWord_ok h2
  have hR := hnr word new a2.stack.val (by show n.stack.val = _; rw [s1, s2])
  change sstoreStateRefill fork (n.state.getStorageOriginal n.message.currentTarget _)
    (n.state.getStorage n.message.currentTarget _) new = 0 at hR
  rw [← t1, ← t2, ← m1, ← m2] at hR
  rw [show GasMeter.gasLeft (lift g a2).gas = GasMeter.gasLeft a2.gas from rfl]
  split
  · exact .inl ⟨_, rfl, rfl⟩
  rw [show (lift g a2).state = a2.state from rfl, show (lift g a2).message = a2.message from rfl,
    accessStorageKey_lift]
  generalize accessStorageKey a2 a2.message.currentTarget word.toBeBytes = p
  rcases p with ⟨cold, b0⟩
  simp only []
  rw [show recordStorageRead (lift g b0) a2.message.currentTarget word.toBeBytes =
    lift g (recordStorageRead b0 a2.message.currentTarget word.toBeBytes) from rfl]
  generalize recordStorageRead b0 a2.message.currentTarget word.toBeBytes = b
  rw [hR]
  have hz : refillStateGas (lift g b) 0 = lift g b := by
    simp only [refillStateGas, GasMeter.refill, refill_zero]
  rw [hz]
  have hz' : refillStateGas b 0 = b := rfl
  rw [hz', chargeGas_lift]
  rcases chargeGas b _ with e | c1
  · exact keepReads_corr hr rfl
  simp only [Except.map]
  rw [chargeStateGas_lift hr]
  rcases chargeStateGas c1 _ with e | c2
  · exact keepReads_corr hr rfl
  simp only [Except.map]
  generalize hg' : ({ g with spill := g.spill + _ } : StateGasMeter) = g'
  have hr' : g'.reservoir = 0 := by rw [← hg']; exact hr
  rw [show (lift g' c2).message = c2.message from rfl, show (lift g' c2).state = c2.state from rfl]
  split
  · exact keepReads_corr hr rfl
  rcases (c2.state.setStorage a2.message.currentTarget word.toBeBytes new).mapError EvmError.state
    with e | st
  · exact keepReads_corr hr rfl
  · exact keepReads_corr hr' rfl


/-! ## The opcodes of `simulated` -/

/-- The instruction of a `simulated` opcode gives, over the two meters, corresponding results from
every frame with reservoir 0, provided an SSTORE refills nothing. -/
theorem sim_of_simulated {op : Op} (hs : simulated op = true)
    {runN : Evm fork Nat → Except EvmError (Evm fork Nat)}
    (hN : instruction (Meter := Nat) fork op = some runN) :
    ∃ runS, instruction (Meter := StateGasMeter) fork op = some runS ∧
      ∀ m : Evm fork StateGasMeter, m.gas.reservoir = 0 → (op = .sstore → NoRefill m) →
        Corr (runS m) (runN (toNat m)) := by
  cases op <;> simp only [simulated, Bool.false_eq_true] at hs
  all_goals simp only [instruction, stackOnlyStep, controlFlowStep, memoryDataStep, returnOpStep,
    environmentStep, accountStep, storageStep, transientStorageStep, logOpStep, selfdestructOpStep,
    HOrElse.hOrElse, OrElse.orElse, Option.orElse, Option.some.injEq] at hN ⊢
  case revert =>
    by_cases hb : Fork.byzantium ≤ fork
    · simp only [hb, ↓reduceIte, Option.some.injEq] at hN ⊢
      subst hN
      exact ⟨_, rfl, fun m hr _ => lifts_revertStep.corr hr⟩
    · simp only [hb, ↓reduceIte, reduceCtorEq] at hN
  case sstore =>
    subst hN
    exact ⟨_, rfl, fun m hr hn => sim_sstoreStep m hr (hn trivial)⟩
  all_goals subst hN
  all_goals refine ⟨_, rfl, fun m hr _ => ?_⟩
  all_goals first
    | with_reducible exact (lifts_binaryOp _ _).corr hr
    | with_reducible exact (lifts_unaryOp _ _).corr hr
    | with_reducible exact lifts_expStep.corr hr
    | with_reducible exact lifts_keccak256Step.corr hr
    | with_reducible exact (lifts_readFrame _ _ _ (fun _ _ => rfl)).corr hr
    | with_reducible exact lifts_calldataloadStep.corr hr
    | with_reducible exact lifts_popStep.corr hr
    | with_reducible exact lifts_mloadStep.corr hr
    | with_reducible exact lifts_mstoreStep.corr hr
    | with_reducible exact lifts_sloadStep.corr hr
    | with_reducible exact lifts_jumpStep.corr hr
    | with_reducible exact lifts_jumpiStep.corr hr
    | with_reducible exact lifts_jumpdestStep.corr hr
    | with_reducible exact lifts_stopStep.corr hr
    | with_reducible exact lifts_returnStep.corr hr
    | with_reducible exact (lifts_pushN _).corr hr
    | with_reducible exact (lifts_dupN _).corr hr
    | with_reducible exact (lifts_swapN _).corr hr
    | with_reducible exact (lifts_logStep _).corr hr

/-! ## One step -/

/-- An SSTORE at the program counter of `m`, if there is one, refills nothing (`NoRefill`). -/
def NoRefillAt (m : Evm fork StateGasMeter) : Prop :=
  ∀ h : m.pc < m.code.size, Op.ofByte fork m.code[m.pc] = some .sstore → NoRefill m

/-- Results of a step over the two meters that correspond: the same error, or a next frame and
its `toNat`, whose reservoir is 0 or which is stopped. -/
def CorrS (rS : Except EvmError (StepResult fork StateGasMeter))
    (rN : Except EvmError (StepResult fork Nat)) : Prop :=
  (∃ e, rS = .error e ∧ rN = .error e) ∨
    ∃ m, rS = .ok (.next m) ∧ rN = .ok (.next (toNat m)) ∧
      (m.gas.reservoir = 0 ∨ m.running = false)

theorem corrS_map {rS : Except EvmError (Evm fork StateGasMeter)}
    {rN : Except EvmError (Evm fork Nat)} (h : Corr rS rN) :
    CorrS (.next <$> rS) (.next <$> rN) := by
  rcases h with ⟨e, rfl, rfl⟩ | ⟨m, rfl, rfl, hm⟩
  · exact .inl ⟨e, rfl, rfl⟩
  · exact .inr ⟨m, rfl, rfl, hm⟩

/-- **One step.** From a frame of the meter `StateGasMeter` with reservoir 0, whose `toNat` is
`SimAt`, and where an SSTORE refills nothing, the step and the step of the meter `Nat` from its
`toNat` give the same error, or a next frame and its `toNat`, with reservoir 0 or stopped. -/
theorem step_sim {m : Evm fork StateGasMeter} (hr : m.gas.reservoir = 0)
    (hp : SimAt (toNat m)) (hnr : NoRefillAt m) :
    CorrS (step fork m) (step fork (toNat m)) := by
  by_cases hlt : m.pc < m.code.size
  · have hlt' : (toNat m).pc < (toNat m).code.size := hlt
    rcases hop : Op.ofByte fork m.code[m.pc] with _ | op
    · rw [step_of_ofByte_eq_none hlt hop, step_of_ofByte_eq_none hlt' hop]
      exact .inl ⟨_, rfl, rfl⟩
    · obtain ⟨hs, hi⟩ := hp hlt' op hop
      obtain ⟨runN, hN⟩ := Option.isSome_iff_exists.mp hi
      obtain ⟨runS, hS, hsim⟩ := sim_of_simulated hs hN
      rw [step_of_instruction hlt hop hS, step_of_instruction hlt' hop hN]
      exact corrS_map (hsim m hr (fun h => hnr hlt (h ▸ hop)))
  · rw [step_of_size_le (by omega), step_of_size_le (evm := toNat m) (by simp only [toNat]; omega)]
    exact .inr ⟨_, rfl, rfl, .inr rfl⟩

/-! ## A run -/

/-- **A run.** The loop of the interpreter over the meter `StateGasMeter`, for any gas bound and
message runner, from a frame with reservoir 0, where no SSTORE that the steps reach refills state
gas: if it ends in `s`, then `Ends` holds from `toNat m` to `toNat s`. -/
theorem ends_of_sgm {bound : Nat} {runChild : MessageRunner fork StateGasMeter bound}
    {m s : Evm fork StateGasMeter} {within : GasMeter.gasHeld m.gas ≤ bound}
    (h : Evm.runFrame (step fork) (step_decreases fork) bound runChild m within = .ok s)
    (hr : m.gas.reservoir = 0) (hnr : ∀ x, Reaches (Step fork) m x → NoRefillAt x) :
    Ends fork (toNat m) (toNat s) := by
  by_cases hrun : m.running = true
  · by_cases hp : SimAt (toNat m)
    · have hc := step_sim hr hp (hnr m (.refl _))
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
            rcases ends_of_sgm h hb (fun x hx => hnr x (.step (.next hrun hstep) hx)) with
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

/-! ## The reservoir of a transaction -/

/-- A transaction whose gas limit is at most `TX_MAX_GAS_LIMIT` (2^24) gives its first frame a
reservoir of 0, at every fork, by EthLib's `allocateGas`. -/
theorem allocateGas_reservoir (fork : Fork) (tx : EthLib.Execution.Transactions.Transaction)
    (intrinsic : Nat) (h : tx.gas.toNat ≤ TX_MAX_GAS_LIMIT) :
    (EthLib.Execution.Transactions.allocateGas fork tx intrinsic).reservoir = 0 := by
  simp only [EthLib.Execution.Transactions.allocateGas]
  split
  · simp only
    omega
  · rfl

/-- The frame at the start of a message over `StateGasMeter` with the meter `meter`, seen through
`toNat`, is the fresh frame of its code with the execution gas left of `meter` (moved here from
Evm/ProcessMeter.lean in round 47). -/
theorem at_startFrameS {code : ByteArray} {message : Message fork} (hcode : message.code = code)
    (state : State.TransactionState) (substate : Substate) (meter : StateGasMeter) :
    At code message 0 [] .empty (GasMeter.gasLeft meter) state substate
      (toNat (startFrame message state substate meter)) := by
  subst hcode
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end UsdtVerify.Meter
