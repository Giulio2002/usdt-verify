import UsdtVerify.Complete.Static

/-!
# The invariant over a finite sequence of calls

`inv_call_all` is about one run of the code. Here it is lifted to a finite sequence of steps
between states, each of which is:

- `GoodCall C S S'`: a successful run of a fresh frame of `CODE` for a message to `C`, from the
  state `S`, that ends in `S'`, with the hypotheses of `inv_call_all` for that run (its own fork
  in Berlin ≤ fork < Glamsterdam, message, gas, gas bound, runner, and the named assumptions
  `StrForm`, `hstat`/`hacc`, `KeepsInv`, `HonestBalance`, each at the state `S` of that call);
- or `Untouched C S S'`: any change that keeps every storage word of `C`. This is where the
  model puts what happens between the top-level calls to `C` and is not a run of `C`'s code: a
  failed call rolled back by the message layer, transactions to other accounts, fees. That such a
  step keeps the storage of `C` is the assumption of this step, not proved here.

`inv_calls`: under `KeccakSep`, `Inv C` at the start of a `Calls` sequence gives `Inv C` at its
end. `goodCall_process`: from Paris, a top-level message to `C` with no value and no precompile,
run by EthLib's `processMessage`, that ends with no error, is a `GoodCall` from its start state
to its end state, under the same named assumptions for the interpreter's runner
(`StaticKeeps` is then proved, `staticKeeps_process`).
-/

namespace UsdtVerify.Complete

open EthLib.Base (Fork U256 Address)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open Invariant Deprecated

/-- One successful run of `CODE` for a message to `C`, from `S` to `S'`, under the hypotheses of
`inv_call_all`. -/
def GoodCall (C : Address) (S S' : State.TransactionState) : Prop :=
  ∃ (fork : Fork) (message : Message fork) (substate : Substate) (gas bound : Nat)
    (runChild : MessageRunner fork Nat bound) (evm s : Evm fork Nat)
    (within : GasMeter.gasHeld evm.gas ≤ bound),
    message.currentTarget = C ∧ .berlin ≤ fork ∧ fork < .glamsterdam ∧
    (message.isStatic = true →
      message.code = CODE ∧ StaticCode S message ∧ StaticKeeps runChild) ∧
    (message.isStatic = false → hasAccount S C) ∧
    message.data.size < 2 ^ 256 ∧
    StrForm (storageAt S C 7) ∧ StrForm (storageAt S C 8) ∧
    (byte20 (storageAt S C 10) ≠ 0 → KeepsInv runChild C (upAddr S message)) ∧
    (byte20 (storageAt S C 10) ≠ 0 → selector message.data = 0xf3bdc228 →
      HonestBalance runChild message S) ∧
    At CODE message 0 [] .empty gas S substate evm ∧
    Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s ∧
    s.error = none ∧ S' = s.state

/-- A change of state that keeps every storage word of `C`. -/
def Untouched (C : Address) (S S' : State.TransactionState) : Prop :=
  ∀ n, storageAt S' C n = storageAt S C n

/-- A finite sequence of successful calls to `C` and of changes that keep the storage of `C`. -/
inductive Calls (C : Address) : State.TransactionState → State.TransactionState → Prop
  | nil (S : State.TransactionState) : Calls C S S
  | call {S S' S'' : State.TransactionState} : GoodCall C S S' → Calls C S' S'' → Calls C S S''
  | other {S S' S'' : State.TransactionState} : Untouched C S S' → Calls C S' S'' →
      Calls C S S''

/-- One successful call keeps `Inv C`. -/
theorem inv_goodCall (K : KeccakSep) {C : Address} {S S' : State.TransactionState}
    (h : GoodCall C S S') (hI : Inv C S) : Inv C S' := by
  obtain ⟨fork, message, substate, gas, bound, runChild, evm, s, within, hC, hfork, hglam, hstat,
    hacc, hsize, h7, h8, hkeeps, hhonest, start, hrun, hok, rfl⟩ := h
  subst hC
  exact inv_call_all K hfork hglam hstat hacc hsize h7 h8 hkeeps hhonest hI start within hrun hok

/-- `Inv C` along every finite sequence of successful calls to `C` and of changes that keep the
storage of `C`, under `KeccakSep`. -/
theorem inv_calls (K : KeccakSep) {C : Address} {S S' : State.TransactionState}
    (h : Calls C S S') (hI : Inv C S) : Inv C S' := by
  induction h with
  | nil => exact hI
  | call hg _ ih => exact ih (inv_goodCall K hg hI)
  | other hu _ ih => exact ih ((DepInv.inv_congr hu).mpr hI)

/-- From Paris, a top-level message to `C` (code `CODE`, no value, no precompile), run by EthLib's
`processMessage`, that ends with no error, is a `GoodCall` from its start state to its end state,
under the named assumptions for the interpreter's runner. The static case needs only
`StaticCode`: `StaticKeeps` holds for this runner (`staticKeeps_process`). -/
theorem goodCall_process {fork : Fork} (hparis : .paris ≤ fork) (hglam : fork < .glamsterdam)
    {message : Message fork} {state : State.TransactionState} {substate : Substate}
    (hmc : message.code = CODE)
    (noValue : ¬(message.shouldTransferValue = true ∧ message.value ≠ 0))
    (noPrecompile : precompileAddress fork message = none)
    (hstat : message.isStatic = true → StaticCode state message)
    (hacc : message.isStatic = false → hasAccount state message.currentTarget)
    (hsize : message.data.size < 2 ^ 256)
    (h7 : StrForm (storageAt state message.currentTarget 7))
    (h8 : StrForm (storageAt state message.currentTarget 8))
    (hkeeps : byte20 (storageAt state message.currentTarget 10) ≠ 0 →
      KeepsInv (processRunner fork message.gas) message.currentTarget (upAddr state message))
    (hhonest : byte20 (storageAt state message.currentTarget 10) ≠ 0 →
      selector message.data = 0xf3bdc228 →
        HonestBalance (processRunner fork message.gas) message state)
    {ended : { evm : Evm fork Nat // GasMeter.gasHeld evm.gas ≤ message.gas }}
    (hproc : processMessage fork message state substate = .ok ended)
    (hok : ended.val.error = none) :
    GoodCall message.currentTarget state ended.val.state := by
  have hst : startState fork message state = state := by
    simp only [startState, show ¬fork < Fork.paris from Nat.not_lt.mpr hparis, ite_false]
  have hberlin : Fork.berlin ≤ fork := Nat.le_trans (by decide) hparis
  generalize hres : runFrame (step fork) (step_decreases fork) message.gas
    (processRunner fork message.gas)
    (startFrame message (startState fork message state) substate
      (GasMeter.start message.gas message.reservoir)) (Nat.le_refl _) = result
  have hmap := processMessage_map_val noValue noPrecompile hres
  rw [hproc] at hmap
  rcases result with e | s
  · cases hmap
  · simp only [Except.map, Except.ok.injEq] at hmap
    have hse : s.error = none := by
      rw [← hok, hmap]
      unfold rollbackOnError
      split <;> rfl
    have hend : ended.val = s := by
      rw [hmap]
      unfold rollbackOnError
      simp [hse]
    have start := at_startFrame hmc (startState fork message state) substate
    rw [hst] at start hres
    refine ⟨fork, message, substate, message.gas, message.gas, processRunner fork message.gas, _, s,
      Nat.le_refl _, rfl, hberlin, hglam, fun h => ⟨hmc, hstat h, staticKeeps_process hparis⟩,
      hacc, hsize, h7, h8, hkeeps, hhonest, start, hres, hse, by rw [hend]⟩

end UsdtVerify.Complete
