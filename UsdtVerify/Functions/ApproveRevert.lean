import UsdtVerify.Functions.ApproveSpec

/-!
# approve(address,uint256): the revert over a nonzero allowance

StandardToken's `approve` has
`require(!((_value != 0) && (allowed[msg.sender][_spender] != 0)))`.
With `_value ≠ 0` and a nonzero allowance the JUMPI at 8379 falls through to
`PUSH1 0 DUP1 REVERT` at 8380: the run reverts with no output.
-/

namespace UsdtVerify.Approve

open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts
open Transfer TransferOk

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate}

/-- At 8230, with `_value ≠ 0` and `allowed[msg.sender][_spender] ≠ 0`, the code reverts. -/
theorem checkRevert (hfork : .berlin ≤ fork) {v s : U256} (hv0 : v ≠ 0) {rest : List U256}
    (hrest : rest.length ≤ 800) {cA : Bool}
    (hcA : coldIn substate message.currentTarget (allowSlot message s) = cA)
    (hnz : storageAt state message.currentTarget (allowSlot message s) ≠ 0) {gas : Nat}
    (hg : 254 + slotCost cA ≤ gas) {M : ByteArray} (hM : M.size = 96) :
    Gas.SpecG fork (At CODE message 8230 (0x40 :: v :: s :: rest) M gas state substate)
      (Halted true .empty (gas - (254 + slotCost cA))
        (readSlot state message.currentTarget (allowSlot message s))
        (accessSlot substate message.currentTarget (allowSlot message s))) := by
  have hM2 := size_mapMem (size_mapMem hM (mkey message.caller.toU256) 5) (mkey s)
    (mapSlot (mkey message.caller.toU256) 5)
  have hz : extendMemory (mapMem (mapMem M (mkey message.caller.toU256) 5) (mkey s)
      (mapSlot (mkey message.caller.toU256) 5)).size [((0 : U256), (0 : U256))] = ⟨0, 0⟩ := by
    rw [hM2]; decide
  step jumpdestR
  step pushR 1 (0 : U256)
  step dupR 2
  step binR 0x14 instruction_eq
  step unR 0x15 instruction_iszero
  step dupR 0
  step unR 0x15 instruction_iszero
  step pushR 2 (0x20b4 : U256)
  step jumpi0R (by simp [equal, isZero]; exact hv0)
  step popR
  step pushR 1 (0 : U256)
  step pushR 1 (0x05 : U256)
  step pushR 1 (0 : U256)
  step Gas.callerG (by code_fact) (by code_fact) (by gas_ok) (by stk_ok)
  at_pc 8250
  step hashTail (by decide) (by simp; omega) hM (by gas_ok)
  at_pc 8308
  step pushR 1 (0 : U256)
  step dupR 5
  at_pc 8311
  step hashTail (by decide) (by simp; omega) (size_mapMem hM _ _) (by gas_ok)
  at_pc 8369
  step Gas.sloadG hfork (cold := cA) (by code_fact) (by code_fact) hcA (by gas_ok)
  step binR 0x14 instruction_eq
  step unR 0x15 instruction_iszero
  step jumpdestR
  step unR 0x15 instruction_iszero
  step unR 0x15 instruction_iszero
  step unR 0x15 instruction_iszero
  step pushR 2 (0x20c0 : U256)
  step jumpi0R (by
    have h : storageAt state message.currentTarget (allowSlot message s) ≠ 0 := hnz
    simp only [storageAt, allowSlot, mkey] at h
    simp [equal, isZero]; exact h)
  step pushR 1 (0 : U256)
  step dupR 0
  refine (Gas.revertG (Nat.le_trans (by decide) hfork) (by code_fact) (by code_fact)
    (by simp only [mkey] at hz; rw [hz]; gas_ok)).consequence (fun _ h => h) ?_
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  refine ⟨hr, he, ?_, ?_, hs, hss⟩
  · rw [ho]; simp [memoryReadBytes]
  · rw [hgas]; simp only [mkey] at hz; rw [hz]; gas_ok

/-- The specification of `approve(spender, v)` for `v ≠ 0` when the allowance is not 0.

Hypotheses: call data of 68 to 2^256 - 1 bytes with selector 0x095ea7b3 and argument word 1
(`v`) not 0; no value; not deprecated (byte 20 of slot 10 is 0); `allowed[msg.sender][spender]`
(slot `keccak(spender ++ keccak(caller ++ 5))`) not 0.

Then the run reverts with no output, after reading slot 10 and the allowance slot; gas left
`gas - (703 + price(slot 10) + price(allowance))`, the allowance's coldness taken after slot 10
was accessed. -/
theorem spec_revert (hfork : .berlin ≤ fork)
    (hlong : 68 ≤ message.data.size) (hsz : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x095ea7b3) (hv : message.value = 0)
    (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    (hnz : wordArg message.data 1 ≠ 0)
    (hallow : storageAt state message.currentTarget (allowArg message) ≠ 0)
    {c10 cA : Bool} (hc10 : coldIn substate message.currentTarget 10 = c10)
    (hcA : coldIn (accessSlot substate message.currentTarget 10) message.currentTarget
      (allowArg message) = cA) {gas : Nat}
    (hg : 703 + slotCost c10 + slotCost cA ≤ gas) :
    Gas.SpecG fork (At CODE message 0 [] .empty gas state substate)
      (Halted true .empty (gas - (703 + slotCost c10 + slotCost cA))
        (readSlot (readSlot state message.currentTarget 10) message.currentTarget
          (allowArg message))
        (accessSlot (accessSlot substate message.currentTarget 10) message.currentTarget
          (allowArg message))) := by
  simp only [allowArg] at hcA hallow ⊢
  step prefixA hfork hlong hsz hsel hv hdep hc10 (by gas_ok)
  refine (checkRevert hfork hnz (by simp) hcA (by rw [storageAt_readSlot]; exact hallow)
    (by gas_ok) size_MEM0).consequence (fun _ h => h) ?_
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  exact ⟨hr, he, ho, by rw [hgas]; gas_ok, hs, hss⟩

/-- The loop of the interpreter runs `approve(spender, v)` over a nonzero allowance to a revert.
It holds for every bound on the gas of messages and every runner of messages. -/
theorem runFrame_revert (hfork : .berlin ≤ fork)
    (hlong : 68 ≤ message.data.size) (hsz : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x095ea7b3) (hv : message.value = 0)
    (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    (hnz : wordArg message.data 1 ≠ 0)
    (hallow : storageAt state message.currentTarget (allowArg message) ≠ 0)
    {c10 cA : Bool} (hc10 : coldIn substate message.currentTarget 10 = c10)
    (hcA : coldIn (accessSlot substate message.currentTarget 10) message.currentTarget
      (allowArg message) = cA) {gas : Nat}
    (hg : 703 + slotCost c10 + slotCost cA ≤ gas) {bound : Nat}
    {runChild : MessageRunner fork Nat bound} {evm : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    ∃ stopped, runFrame (step fork) (step_decreases fork) bound runChild evm within =
      .ok stopped ∧
      Halted true .empty (gas - (703 + slotCost c10 + slotCost cA))
        (readSlot (readSlot state message.currentTarget 10) message.currentTarget
          (allowArg message))
        (accessSlot (accessSlot substate message.currentTarget 10) message.currentTarget
          (allowArg message)) stopped :=
  (spec_revert hfork hlong hsz hsel hv hdep hnz hallow hc10 hcA hg).runFrame start within

end UsdtVerify.Approve
