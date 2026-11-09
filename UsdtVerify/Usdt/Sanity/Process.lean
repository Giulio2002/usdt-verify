import UsdtVerify.Usdt.Sanity.Runner
import UsdtVerify.Usdt.Exact.Deprecated

/-!
# Sanity: EthLib's `processRunner` meets the restated runner assumptions (round 29)

docs/AUDIT.md, finding 2: `KeepsInv` and the `Keeps*` assumptions of rounds 15 to 28 quantified
over every caller frame and every message from `C` to the upgraded address, including its code,
so EthLib's own runner `processRunner` met them for no upgraded address. Since round 29 the
theorems take the `At` forms (`KeepsInvAt`, `KeepsSlots`, `KeepsBal`, `KeepsListed`, `KeepsAllow`,
`KeepsSupply`, all `KeepsAt`): only the calls that the code of `C` makes from the start state `S`
(`SentVia`: the caller state has the storage and code of `S`, the message runs the code that the
upgraded address holds in `S` along its route, no value; any data, any gas).

Here the upgraded address holds the one byte STOP (`STOP_CODE`), a real contract, and is no
precompile. Then:

- `processRunner_stop_keepsAt`: from Paris, `processRunner` at any bound meets `KeepsAt … R` for
  every reflexive relation `R`: each such call ends with the caller state, unchanged.
- `processRunner_stop_keepsAll`: so it meets all six (`KeepsAll`), and in particular `KeepsInvAt`,
  the assumption that `goodCall_process` and `process_step` take for `processRunner`.

Not shown: `HonestBalanceAt` for `processRunner` with a real upgraded code (STOP answers no word).

docs/AUDIT.md, finding 3: the deprecated exact theorems under `processRunner` are in
Sanity/ProcessExact.lean.
-/

namespace UsdtVerify.Sanity

open EthLib.Base (Fork U256 Address)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open Complete Security Invariant Deprecated

variable {fork : Fork}

/-- The code of one byte, STOP. -/
def STOP_CODE : ByteArray := ⟨#[0x00]⟩

theorem delegatedAddress_stop : delegatedAddress STOP_CODE = none := by decide

/-- From Paris, a message that runs `STOP_CODE` at a target with no value and no precompile, run
by `processRunner`, ends with no error in the state it starts from. -/
theorem process_stop (hparis : .paris ≤ fork) {bound : Nat} (caller : Evm fork Nat)
    {msg : Message fork} (lt : msg.gas < bound) (hcode : msg.code = STOP_CODE)
    {ua : Address} (ht : msg.target = some ua) (hv : msg.value = 0)
    (hpre : precompileAddress fork msg = none)
    {child : { evm : Evm fork Nat // GasMeter.gasHeld evm.gas ≤ msg.gas }}
    (hch : processRunner fork bound caller msg lt = .ok child) :
    child.1.error = none ∧ child.1.state = caller.state := by
  have hst : startState fork msg caller.state = caller.state := by
    simp only [startState, show ¬fork < Fork.paris from Nat.not_lt.mpr hparis, ite_false]
  have hp : processRunner fork bound caller msg lt =
      processMessage fork msg caller.state caller.substate.child := by
    simp only [processRunner, ht]
  have hspec := stop (fork := fork) (code := STOP_CODE) (message := msg) (pc := 0)
    (stack := []) (memory := .empty) (gas := msg.gas) (state := caller.state)
    (substate := caller.substate.child) (returnData := .empty) (by decide) rfl
  obtain ⟨stopped, hq, hmap⟩ := processMessage_of_spec (message := msg) (state := caller.state)
    (substate := caller.substate.child) hspec (fun h => h.2 hv) hpre
    (by rw [hst]; exact Logic.at_startFrame hcode _ _)
  obtain ⟨-, herr, -, -, hs, -⟩ := hq
  have herr' : stopped.error = none := by simpa using herr
  rw [rollbackOnError_of_error_eq_none herr', ← hp, hch] at hmap
  have hc : child.1 = stopped := by simpa [Except.map] using hmap
  rw [hc]
  exact ⟨herr', hs⟩

/-- **`processRunner` meets the restated assumptions.** From Paris, when the upgraded address of
`message` in `S` holds `STOP_CODE` and is no precompile, `processRunner` at any bound meets
`KeepsAt … R` for every reflexive `R`. -/
theorem processRunner_stop_keepsAt (hparis : .paris ≤ fork) {bound : Nat}
    {message : Message fork} {S : State.TransactionState}
    (hcode : S.getCode (S.getAccount (upAddr S message)).codeHash = .ok STOP_CODE)
    (hnp : Precompiles.isPrecompile fork (upAddr S message).toU256.toNat = false)
    {R : State.TransactionState → State.TransactionState → Prop} (hR : ∀ X, R X X) :
    KeepsAt (processRunner fork bound) message S (upAddr S message) R := by
  intro caller msg lt child ⟨c, r, hc, hroute, hsv, _⟩ hch _
  rw [hcode] at hc
  cases hc
  obtain ⟨-, -, htg, hca, hmc, -, -, hval, -, -⟩ := hsv
  rcases r with _ | ⟨d, c'⟩
  · have hpre : precompileAddress fork msg = none := by
      simp only [precompileAddress, hca, routeAddr, hnp]; rfl
    rw [(process_stop hparis caller lt hmc htg hval hpre hch).2]
    exact hR _
  · exact absurd hroute.2.1 (by rw [delegatedAddress_stop]; exact fun h => by cases h)

/-- So `processRunner` meets all six runner assumptions of the deprecated theorems, in their `At`
forms, in particular `KeepsInvAt`. -/
theorem processRunner_stop_keepsAll (hparis : .paris ≤ fork) {bound : Nat}
    {message : Message fork} {S : State.TransactionState}
    (hcode : S.getCode (S.getAccount (upAddr S message)).codeHash = .ok STOP_CODE)
    (hnp : Precompiles.isPrecompile fork (upAddr S message).toU256.toNat = false) :
    KeepsAll (processRunner fork bound) message S :=
  ⟨processRunner_stop_keepsAt hparis hcode hnp fun _ _ _ => rfl,
    processRunner_stop_keepsAt hparis hcode hnp fun _ _ _ => rfl,
    processRunner_stop_keepsAt hparis hcode hnp fun _ _ _ _ => by unfold NoDec; exact Nat.le_refl _,
    processRunner_stop_keepsAt hparis hcode hnp fun _ _ _ => rfl,
    processRunner_stop_keepsAt hparis hcode hnp fun _ => rfl,
    processRunner_stop_keepsAt hparis hcode hnp fun _ h => h⟩

/-- The deprecated-path hypothesis `hkeeps` of `goodCall_process` and `process_step` (round 29),
for `processRunner fork message.gas`, holds when the upgraded address holds STOP and is no
precompile, from Paris. -/
theorem keepsInvAt_process_stop (hparis : .paris ≤ fork) {message : Message fork}
    {S : State.TransactionState}
    (hcode : S.getCode (S.getAccount (upAddr S message)).codeHash = .ok STOP_CODE)
    (hnp : Precompiles.isPrecompile fork (upAddr S message).toU256.toNat = false) :
    KeepsInvAt (processRunner fork message.gas) message S :=
  (processRunner_stop_keepsAll hparis hcode hnp).2.2.2.2.2

end UsdtVerify.Sanity
