import UsdtVerify.Evm.Exact
import UsdtVerify.Usdt.Complete.Dispatch
import UsdtVerify.Usdt.Spec.Transfer

/-!
# Completeness of transfer(address to, uint256 v), not deprecated

Every run of a `transfer` call (selector 0xa9059cbb) that ends with no error, for any gas, gas
bound and message runner, with the contract not deprecated, is one of the two success paths:
`TransferOk.spec_ok` (fee 0) or `TransferFee.spec_fee` (fee > 0), with the exact output, gas,
state and substate. The checks that the run passed are part of the conclusion: call data of at
least 68 bytes, not paused, the caller not blacklisted, no overflow of `v * rate`, `fee ≤ v`,
`v ≤ balances[caller]`, no overflow at the recipient, and for fee > 0 no overflow at the owner.

Each other case is excluded by a specification over `StepG` that ends with an error: the
reverts (`spec_paused`, `spec_blacklisted`, `spec_short`) and the INVALID paths (`spec_mulOv`,
`spec_feeGt`, `spec_low`, `spec_toOv`, `spec_ownerOv`).

Hypotheses beyond the call: Berlin ≤ fork (Glamsterdam included). A static frame, or a contract
with no account, is excluded once the checks up to `spec_low` pass: every remaining path reaches
the SSTORE of the sender's balance, which is then `Gas.Stuck` (`TransferOk.bad_transfer`, with
`Gas.no_ok_stuckE`); so the conclusion states `message.isStatic = false` and an account of the
contract.
-/

namespace UsdtVerify.Complete

open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open UsdtVerify.Gas
open Transfer TransferOk TransferFee SafeMath

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate} {bound : Nat} {runChild : MessageRunner fork Nat bound}
  {evm s : Evm fork Nat} {gas : Nat}

theorem sendOf_zero {S : State.TransactionState} {v : U256} (h : feeOf S message v = 0) :
    sendOf S message v = v := by
  simp [sendOf, h, sub]

/-- Every successful `transfer(a, v)` call, not deprecated, is the fee-0 or the fee path.
The conclusion states that the frame is not static and the contract has an account: otherwise
the SSTORE of the sender's balance is `Gas.Stuck` (`bad_transfer`). -/
theorem ok_transfer (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xa9059cbb)
    (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    {c0 cB c10 c3 c4 cS cT cO : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hcB : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget
      (blackSlot message) = cB)
    (hc10 : coldIn (accessSlot (accessSlot substate message.currentTarget 0) message.currentTarget
      (blackSlot message)) message.currentTarget 10 = c10)
    (hc3 : coldIn (shortSubstate substate message) message.currentTarget 3 = c3)
    (hc4 : coldIn (accessSlot (shortSubstate substate message) message.currentTarget 3)
      message.currentTarget 4 = c4)
    (hcS : coldIn (accessSlot (accessSlot (shortSubstate substate message) message.currentTarget 3)
      message.currentTarget 4) message.currentTarget (senderSlot message) = cS)
    (hcT : coldIn (access3 (shortSubstate substate message) message) message.currentTarget
      (recipientSlot (addrArg message.data 0)) = cT)
    (hcO : coldIn (creditedSubFee fork (shortSubstate substate message) (shortState state message)
      message (wordArg message.data 1) (addrArg message.data 0)) message.currentTarget
      (ownerSlot (ownerWord (shortState state message) message (wordArg message.data 1)
        (addrArg message.data 0))) = cO)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (hrun : Ends fork evm s)
    (hok : s.error = none) :
    message.isStatic = false ∧ hasAccount state message.currentTarget ∧
    68 ≤ message.data.size ∧ byte20 (storageAt state message.currentTarget 0) = 0 ∧
      (storageAt state message.currentTarget (blackSlot message)).toNat % 256 = 0 ∧
      (wordArg message.data 1).toNat *
        (storageAt (shortState state message) message.currentTarget 3).toNat < 2 ^ 256 ∧
      (feeOf (shortState state message) message (wordArg message.data 1)).toNat ≤
        (wordArg message.data 1).toNat ∧
      (wordArg message.data 1).toNat ≤ (balS (shortState state message) message).toNat ∧
      (balT (shortState state message) message (wordArg message.data 1)
        (addrArg message.data 0)).toNat +
        (sendOf (shortState state message) message (wordArg message.data 1)).toNat < 2 ^ 256 ∧
      s.output = .empty ∧
      ((feeOf (shortState state message) message (wordArg message.data 1) = 0 ∧
        (okCost fork state message c0 cB c10 c3 c4 cS cT ≤ gas ∧
          s.gas = gas - okCost fork state message c0 cB c10 c3 c4 cS cT) ∧
        s.state = credited (shortState state message) message (wordArg message.data 1)
          (addrArg message.data 0) ∧
        s.substate = loggedSub fork (shortSubstate substate message) (shortState state message)
          message (wordArg message.data 1) (addrArg message.data 0)) ∨
      (feeOf (shortState state message) message (wordArg message.data 1) ≠ 0 ∧
        (balO (shortState state message) message (wordArg message.data 1)
          (addrArg message.data 0)).toNat +
          (feeOf (shortState state message) message (wordArg message.data 1)).toNat < 2 ^ 256 ∧
        (feeCost fork state message c0 cB c10 c3 c4 cS cT cO ≤ gas ∧
          s.gas = gas - feeCost fork state message c0 cB c10 c3 c4 cS cT cO) ∧
        s.state = feeState (shortState state message) message (wordArg message.data 1)
          (addrArg message.data 0) ∧
        s.substate = feeSub fork (shortSubstate substate message) (shortState state message)
          message (wordArg message.data 1) (addrArg message.data 0))) := by
  obtain ⟨h4, hv, -⟩ := ends_ok_dispatch hfork hsize' start hrun hok
  by_cases hp : byte20 (storageAt state message.currentTarget 0) ≠ 0
  · exact (no_okE (fun g hg => spec_paused hfork h4 hsize' hsel hv hp hc0 hg)
      (fun _ e h => halted_true_error e h) start hrun hok).elim
  have hp : byte20 (storageAt state message.currentTarget 0) = 0 := by omega
  by_cases hb : (storageAt state message.currentTarget (blackSlot message)).toNat % 256 ≠ 0
  · exact (no_okE (fun g hg => spec_blacklisted hfork h4 hsize' hsel hv hp hb hc0 hcB hg)
      (fun _ e h => halted_true_error e h) start hrun hok).elim
  have hb : (storageAt state message.currentTarget (blackSlot message)).toNat % 256 = 0 := by
    omega
  by_cases hl : message.data.size < 68
  · exact (no_okE (fun g hg => spec_short hfork h4 hl hsel hv hp hb hdep hc0 hcB hc10 hg)
      (fun _ e h => halted_true_error e h) start hrun hok).elim
  have hl : 68 ≤ message.data.size := by omega
  by_cases hov : 2 ^ 256 ≤ (wordArg message.data 1).toNat *
      (storageAt (shortState state message) message.currentTarget 3).toNat
  · exact (no_okE (fun g hg => spec_mulOv hfork hl hsize' hsel hv hp hb hdep hov hc0 hcB hc10 hc3 hg)
      (fun _ e h => faulted_error e h) start hrun hok).elim
  have hov := Nat.lt_of_not_le hov
  by_cases hgt : (wordArg message.data 1).toNat <
      (feeOf (shortState state message) message (wordArg message.data 1)).toNat
  · exact (no_okE (fun g hg => spec_feeGt hfork hl hsize' hsel hv hp hb hdep hov hgt hc0 hcB hc10
      hc3 hc4 hg) (fun _ e h => faulted_error e h) start hrun hok).elim
  have hfv := Nat.le_of_not_lt hgt
  by_cases hlow : (balS (shortState state message) message).toNat < (wordArg message.data 1).toNat
  · exact (no_okE (fun g hg => spec_low hfork hl hsize' hsel hv hp hb hdep hov hfv hlow hc0 hcB
      hc10 hc3 hc4 hcS hg) (fun _ e h => faulted_error e h) start hrun hok).elim
  have hbal := Nat.le_of_not_lt hlow
  by_cases hgood : ¬(message.isStatic = false ∧ hasAccount state message.currentTarget)
  · exact (Gas.no_ok_stuckE (fun g hg => bad_transfer hfork hl hsize' hsel
      hv hp hb hdep hov hfv hbal hc0 hcB hc10 hc3 hc4 hcS (.of_bad (Gas.bad_of_not hgood)) hg) start hrun hok).elim
  obtain ⟨hstatic, hacc⟩ := Classical.not_not.mp hgood
  by_cases hto : 2 ^ 256 ≤ (balT (shortState state message) message (wordArg message.data 1)
      (addrArg message.data 0)).toNat +
      (sendOf (shortState state message) message (wordArg message.data 1)).toNat
  · refine (no_okE (B := preCost c0 cB c10 + (530 + slotCost c3 + slotCost c4 + slotCost cS +
        mulCost (wordArg message.data 1) +
        capCost (rawFee (shortState state message) message (wordArg message.data 1))
          (storageAt (shortState state message) message.currentTarget 4) + 2400) +
        (preCost c0 cB c10 + (808 + readCost c3 c4 cS cT + mulCost (wordArg message.data 1) +
        capCost (rawFee (shortState state message) message (wordArg message.data 1))
          (storageAt (shortState state message) message.currentTarget 4) +
        debitCost fork (shortState state message) message (wordArg message.data 1))))
      (fun g hg => spec_toOv hfork hstatic hacc hl hsize' hsel hv hp hb hdep hov hfv hbal hto
        hc0 hcB hc10 hc3 hc4 hcS hcT (le_l hg) (le_r hg))
      (fun _ e h => faulted_error e h) start hrun hok).elim
  have hto := Nat.lt_of_not_le hto
  refine ⟨hstatic, hacc, hl, hp, hb, hov, hfv, hbal, hto, ?_⟩
  by_cases hfee : feeOf (shortState state message) message (wordArg message.data 1) = 0
  · have hto' := hto
    rw [sendOf_zero hfee] at hto'
    obtain ⟨hcg, -, ho, hg, hst, hss⟩ := ok_exactE (Nat.le_add_right _ _)
      (B := okCost fork state message c0 cB c10 c3 c4 cS cT +
        (PRE_COST + slotCost c0 + slotCost cB + slotCost c10 + (530 + slotCost c3 +
        slotCost c4 + slotCost cS + mulCost (wordArg message.data 1) +
        capCost (rawFee (shortState state message) message (wordArg message.data 1))
          (storageAt (shortState state message) message.currentTarget 4) + 2400) +
        (PRE_COST + slotCost c0 + slotCost cB + slotCost c10 + (837 + readCost c3 c4 cS cT +
        mulCost (wordArg message.data 1) +
        capCost (rawFee (shortState state message) message (wordArg message.data 1))
          (storageAt (shortState state message) message.currentTarget 4) +
        debitCost fork (shortState state message) message (wordArg message.data 1) + 2401))))
      (fun g hg => spec_ok hfork hstatic hacc hl hsize' hsel hv hp hb hdep hov hfee hbal
        hto' hc0 hcB hc10 hc3 hc4 hcS hcT (le_l (le_r hg)) (le_r (le_r hg)) (le_l hg))
      start hrun hok
    exact ⟨ho, .inl ⟨hfee, ⟨hcg, hg⟩, hst, hss⟩⟩
  by_cases hown : 2 ^ 256 ≤ (balO (shortState state message) message (wordArg message.data 1)
      (addrArg message.data 0)).toNat +
      (feeOf (shortState state message) message (wordArg message.data 1)).toNat
  · refine (no_okE (B := preCost c0 cB c10 + (964 + readCost c3 c4 cS cT +
        mulCost (wordArg message.data 1) +
        capCost (rawFee (shortState state message) message (wordArg message.data 1))
          (storageAt (shortState state message) message.currentTarget 4) +
        debitCost fork (shortState state message) message (wordArg message.data 1) +
        creditCostFee fork (shortState state message) message (wordArg message.data 1)
          (addrArg message.data 0) + 2401) +
        (preCost c0 cB c10 + (964 + readCost c3 c4 cS cT + mulCost (wordArg message.data 1) +
        capCost (rawFee (shortState state message) message (wordArg message.data 1))
          (storageAt (shortState state message) message.currentTarget 4) +
        debitCost fork (shortState state message) message (wordArg message.data 1) +
        creditCostFee fork (shortState state message) message (wordArg message.data 1)
          (addrArg message.data 0) + 313 + slotCost cO)))
      (fun g hg => spec_ownerOv hfork hstatic hacc hl hsize' hsel hv hp hb hdep hov hfee hfv
        hbal hto hown hc0 hcB hc10 hc3 hc4 hcS hcT hcO (le_l hg) (le_r hg))
      (fun _ e h => faulted_error e h) start hrun hok).elim
  have hown := Nat.lt_of_not_le hown
  obtain ⟨hcg, -, ho, hg, hst, hss⟩ := ok_exactE (Nat.le_refl _)
    (fun g hg => spec_fee hfork hstatic hacc hl hsize' hsel hv hp hb hdep hov hfee hfv hbal
      hto hown hc0 hcB hc10 hc3 hc4 hcS hcT hcO hg)
    start hrun hok
  exact ⟨ho, .inr ⟨hfee, hown, ⟨hcg, hg⟩, hst, hss⟩⟩

end UsdtVerify.Complete
