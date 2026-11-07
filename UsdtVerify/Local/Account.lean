import UsdtVerify.Local.Rules
import EthLib.Execution.Proofs.Evm.Logic.Call
import EthLib.Execution.Proofs.Evm.Instructions.EnvironmentData

/-!
# LOCAL: rules for EXTCODESIZE and GAS

GENERIC GAP. EthLib's program logic at the pinned commit has no rule for EXTCODESIZE (0x3b) or
GAS (0x5a). Nothing here is specific to USDT; each rule holds for every code.

- `extcodesize`: from Berlin to before Glamsterdam, EXTCODESIZE pushes the size of the code of the
  account at an address, pays 2600 for a cold address and 100 for a warm one (EIP-2929), adds the
  address to the accessed addresses and records the read of the account.
- `gas`: GAS pushes the gas left after its own price of 2.
-/

namespace UsdtVerify.Local

open EthLib.Base (Fork U256 toAddressMasked)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts

variable {fork : Fork}

theorem instruction_extcodesize {Meter : Type} [GasMeter Meter] :
    instruction (Meter := Meter) fork .extcodesize = some extcodesizeStep := by
  simp [instruction, stackOnlyStep, controlFlowStep, memoryDataStep, returnOpStep,
    environmentStep, accountStep, HOrElse.hOrElse, OrElse.orElse, Option.orElse]

theorem instruction_gas {Meter : Type} [GasMeter Meter] :
    instruction (Meter := Meter) fork .gas =
      some (readFrame OPCODE_GAS fun evm => BitVec.ofNat 256 (GasMeter.gasLeft evm.gas)) := by
  simp [instruction, stackOnlyStep, controlFlowStep, HOrElse.hOrElse, OrElse.orElse,
    Option.orElse]

/-- From Berlin to before Glamsterdam, a read of another account pays 2600 cold, 100 warm. -/
theorem externalBaseCost_of_berlin (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    (cold : Bool) : externalBaseCost fork cold = if cold then 2600 else 100 := by
  have hng : ¬fork ≥ .glamsterdam := Nat.not_le_of_lt hglam
  simp [externalBaseCost, hfork, accountAccessCost, gasSchedule, hng, WARM_ACCESS]

variable {code : ByteArray} {message : Message fork} {pc : Nat} {stack : List U256}
  {memory : ByteArray} {gas : Nat} {state : State.TransactionState} {substate : Substate}

/-- EXTCODESIZE of the address `a`, whose account holds the code `c` in the state. -/
theorem extcodesize (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam) {a : U256}
    {rest : List U256} {cold : Bool} {c : ByteArray} (hlt : pc < code.size)
    (hbyte : code[pc] = 0x3b)
    (hcode : state.getCode (state.getAccount (toAddressMasked a)).codeHash = .ok c)
    (hcold : decide (toAddressMasked a ∉ substate.accessedAddresses) = cold)
    (hgas : (if cold then 2600 else 100) ≤ gas) :
    Hoare fork (At code message pc (a :: rest) memory gas state substate)
      (At code message (pc + 1) (BitVec.ofNat 256 c.size :: rest) memory
        (gas - if cold then 2600 else 100)
        (state.recordAccountRead (toAddressMasked a))
        { substate with
          accessedAddresses := substate.accessedAddresses.insert (toAddressMasked a) }) := by
  apply At.rule hlt hbyte (ofByte_of_decode (op := .extcodesize) rfl (Fork.frontier_le _))
    instruction_extcodesize
  rintro ⟨pc', ⟨l, hl⟩, memory', code', valid, gas', running, message', output, returnData,
    state', substate', error⟩ ⟨hc, hj, hm, hpc, hst, hmem, hg, hrun, herr, hs, hss⟩
  simp only at hc hj hm hpc hst hmem hg hrun herr hs hss
  subst hst hg hs hss hm hc hj hpc hmem hrun herr
  have hlen : rest.length < STACK_LIMIT := by simp at hl; omega
  have hne : rest.length ≠ STACK_LIMIT := Nat.ne_of_lt hlen
  have hgc : ∀ (tx : State.TransactionState) (x : EthLib.Base.Address) h,
      (tx.recordAccountRead x).getCode h = tx.getCode h := fun _ _ _ => rfl
  have hga : ∀ (tx : State.TransactionState) (x y : EthLib.Base.Address),
      (tx.recordAccountRead x).getAccount y = tx.getAccount y := fun _ _ _ => rfl
  rcases cold with _ | _ <;> simp only [Bool.false_eq_true, ↓reduceIte, decide_eq_true_eq,
    decide_eq_false_iff_not, Classical.not_not] at hcold hgas ⊢ <;>
  simp [extcodesizeStep, popWord, Stack.pop, accessAddress, hfork, chargeGas, GasMeter.charge,
    externalBaseCost_of_berlin hfork hglam, recordAccountRead, accountCode, hgc, hga, hcode,
    Except.mapError, pushWord, Stack.push, hne, advance, bind, Except.bind, pure, Except.pure,
    hcold, Nat.not_lt.mpr hgas, At]

/-- GAS pushes the gas left after its own price of 2. -/
theorem gasOp (hlt : pc < code.size) (hbyte : code[pc] = 0x5a) (hgas : 2 ≤ gas)
    (hstack : stack.length < STACK_LIMIT) :
    Hoare fork (At code message pc stack memory gas state substate)
      (At code message (pc + 1) (BitVec.ofNat 256 (gas - 2) :: stack) memory (gas - 2) state
        substate) := by
  apply At.rule hlt hbyte (ofByte_of_decode (op := .gas) rfl (Fork.frontier_le _)) instruction_gas
  rintro evm ⟨hcode, hj, hm, hpc, hst, hmem, hg, hrun, herr, hs, hss⟩
  have hc : (OPCODE_GAS : Nat) = 2 := rfl
  rw [readFrame_of_length_lt (by rw [hst]; exact hstack),
    charge_nat (by rw [hg, hc]; exact hgas)]
  refine ⟨_, rfl, hcode, hj, hm, by simp [hpc], ?_, hmem, by simp [hg, hc], hrun, herr, hs, hss⟩
  simp [hst, hg, hc, GasMeter.gasLeft]

end UsdtVerify.Local
