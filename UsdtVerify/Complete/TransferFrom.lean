import UsdtVerify.Complete.Exact
import UsdtVerify.Complete.Transfer
import UsdtVerify.Functions.TransferFromSpec
import UsdtVerify.Functions.TransferFromFault
import UsdtVerify.Functions.TransferFromFault2
import UsdtVerify.Functions.TransferFromFeeSpec

/-!
# Completeness of transferFrom(address f, address t, uint256 v), not deprecated

Every run of a `transferFrom` call (selector 0x23b872dd) that ends with no error, for any gas,
gas bound and message runner, with the contract not deprecated, is one of the two success paths:
`TransferFrom.spec_ok` (fee 0) or `TransferFrom.spec_feeF` (fee > 0), with the exact output, gas,
state and substate. The checks that the run passed are part of the conclusion: call data of at
least 100 bytes, not paused, `f` not blacklisted, no overflow of `v * rate`, the allowance is
MAX_UINT or at least `v`, `fee ≤ v`, `v ≤ balances[f]`, no overflow at `t`, and for fee > 0 no
overflow at the owner.

Each other case is excluded by a specification over `StepG` that ends with an error: the
reverts (`spec_paused`, `spec_blacklisted`, `spec_short`) and the INVALID paths (`spec_mulOv`,
`spec_allowLow`, `spec_feeGtF`, `spec_balLow`, `spec_toOvF`, `spec_ownerOvF`).

Hypotheses beyond the call: Berlin ≤ fork (Glamsterdam included), the frame is not static (`hstatic`),
and the contract has an account (`hacc`).
-/

namespace UsdtVerify.Complete

open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open UsdtVerify.Gas
open Transfer TransferOk TransferFee SafeMath TransferFrom

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate} {bound : Nat} {runChild : MessageRunner fork Nat bound}
  {evm s : Evm fork Nat} {gas : Nat}

/-- Every successful `transferFrom(f, t, v)` call, not deprecated, is the fee-0 or the fee
path. -/
theorem ok_transferFrom (hfork : .berlin ≤ fork)
    (hstatic : message.isStatic = false) (hacc : hasAccount state message.currentTarget)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x23b872dd)
    (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    {c0 cB c10 cA c3 c4 cF cT cO : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hcB : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget
      (blackFrom (fromArg message)) = cB)
    (hc10 : coldIn (accessSlot (accessSlot substate message.currentTarget 0) message.currentTarget
      (blackFrom (fromArg message))) message.currentTarget 10 = c10)
    (hcA : coldIn (checkSub substate message) message.currentTarget
      (allowFrom message (fromArg message)) = cA)
    (hc3 : coldIn (accessSlot (checkSub substate message) message.currentTarget
      (allowFrom message (fromArg message))) message.currentTarget 3 = c3)
    (hc4 : coldIn (accessSlot (accessSlot (checkSub substate message) message.currentTarget
      (allowFrom message (fromArg message))) message.currentTarget 3) message.currentTarget 4 = c4)
    (hcF : coldIn (allowedSubF fork (checkSub substate message) (checkState state message) message
      (valArg message) (fromArg message)) message.currentTarget (recipientSlot (fromArg message)) =
        cF)
    (hcT : coldIn (accessSlot (allowedSubF fork (checkSub substate message)
      (checkState state message) message (valArg message) (fromArg message)) message.currentTarget
      (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (toArg message)) = cT)
    (hcO : coldIn (creditedSubFeeF fork (checkSub substate message) (checkState state message)
      message (valArg message) (toArg message) (fromArg message)) message.currentTarget
      (ownerSlot (ownerWordF (checkState state message) message (valArg message) (toArg message)
        (fromArg message))) = cO)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) :
    100 ≤ message.data.size ∧ byte20 (storageAt state message.currentTarget 0) = 0 ∧
      (storageAt state message.currentTarget (blackFrom (fromArg message))).toNat % 256 = 0 ∧
      (valArg message).toNat *
        (storageAt (checkState state message) message.currentTarget 3).toNat < 2 ^ 256 ∧
      (allowOf (checkState state message) message (fromArg message) = MAX_UINT ∨
        (valArg message).toNat ≤
          (allowOf (checkState state message) message (fromArg message)).toNat) ∧
      (feeOf (checkState state message) message (valArg message)).toNat ≤
        (valArg message).toNat ∧
      (valArg message).toNat ≤
        (balFrom (checkState state message) message (valArg message) (fromArg message)).toNat ∧
      (balTo (checkState state message) message (valArg message) (toArg message)
        (fromArg message)).toNat +
        (sendOf (checkState state message) message (valArg message)).toNat < 2 ^ 256 ∧
      s.output = .empty ∧
      ((feeOf (checkState state message) message (valArg message) = 0 ∧
        s.gas = gas - okCostF fork state message c0 cB c10 cA c3 c4 cF cT ∧
        s.state = creditedF (checkState state message) message (valArg message) (toArg message)
          (fromArg message) ∧
        s.substate = loggedSubF fork (checkSub substate message) (checkState state message)
          message (valArg message) (toArg message) (fromArg message)) ∨
      (feeOf (checkState state message) message (valArg message) ≠ 0 ∧
        (balOF (checkState state message) message (valArg message) (toArg message)
          (fromArg message)).toNat +
          (feeOf (checkState state message) message (valArg message)).toNat < 2 ^ 256 ∧
        s.gas = gas - feeCostF fork state message c0 cB c10 cA c3 c4 cF cT cO ∧
        s.state = feeStateF (checkState state message) message (valArg message) (toArg message)
          (fromArg message) ∧
        s.substate = feeSubF fork (checkSub substate message) (checkState state message) message
          (valArg message) (toArg message) (fromArg message))) := by
  obtain ⟨h4, hv, -⟩ := runFrame_ok_dispatch hfork hsize' start within hrun hok
  by_cases hp : byte20 (storageAt state message.currentTarget 0) ≠ 0
  · exact (no_ok (fun g hg => spec_paused hfork h4 hsize' hsel hv hp hc0 hg)
      (fun _ e h => halted_true_error e h) start within hrun hok).elim
  have hp : byte20 (storageAt state message.currentTarget 0) = 0 := by omega
  by_cases hb : (storageAt state message.currentTarget (blackFrom (fromArg message))).toNat %
      256 ≠ 0
  · exact (no_ok (fun g hg => spec_blacklisted hfork h4 hsize' hsel hv hp hb hc0 hcB hg)
      (fun _ e h => halted_true_error e h) start within hrun hok).elim
  have hb : (storageAt state message.currentTarget (blackFrom (fromArg message))).toNat % 256 =
      0 := by omega
  by_cases hl : message.data.size < 100
  · exact (no_ok (fun g hg => spec_short hfork h4 hl hsel hv hp hb hdep hc0 hcB hc10 hg)
      (fun _ e h => halted_true_error e h) start within hrun hok).elim
  have hl : 100 ≤ message.data.size := by omega
  by_cases hov : 2 ^ 256 ≤ (valArg message).toNat *
      (storageAt (checkState state message) message.currentTarget 3).toNat
  · exact (no_ok (fun g hg => spec_mulOv hfork hl hsize' hsel hv hp hb hdep hov hc0 hcB hc10 hcA
      hc3 hg) (fun _ e h => faulted_error e h) start within hrun hok).elim
  have hov := Nat.lt_of_not_le hov
  by_cases hlt : (allowOf (checkState state message) message (fromArg message)).toNat <
      (valArg message).toNat
  · exact (no_ok (fun g hg => spec_allowLow hfork hl hsize' hsel hv hp hb hdep hov hlt hc0 hcB
      hc10 hcA hc3 hc4 hg) (fun _ e h => faulted_error e h) start within hrun hok).elim
  have hallow : allowOf (checkState state message) message (fromArg message) = MAX_UINT ∨
      (valArg message).toNat ≤
        (allowOf (checkState state message) message (fromArg message)).toNat :=
    .inr (Nat.le_of_not_lt hlt)
  by_cases hgt : (valArg message).toNat <
      (feeOf (checkState state message) message (valArg message)).toNat
  · exact (no_ok (fun g hg => spec_feeGtF hfork hstatic hacc hl hsize' hsel hv hp hb hdep
      hov hallow hgt hc0 hcB hc10 hcA hc3 hc4 hg)
      (fun _ e h => faulted_error e h) start within hrun hok).elim
  have hfv := Nat.le_of_not_lt hgt
  by_cases hlow : (balFrom (checkState state message) message (valArg message)
      (fromArg message)).toNat < (valArg message).toNat
  · exact (no_ok2 (fun g h1 h2 => spec_balLow hfork hstatic hacc hl hsize' hsel hv hp hb
      hdep hov hfv hallow hlow hc0 hcB hc10 hcA hc3 hc4 hcF h1 h2)
      (fun _ e h => faulted_error e h) start within hrun hok).elim
  have hbal := Nat.le_of_not_lt hlow
  by_cases hto : 2 ^ 256 ≤ (balTo (checkState state message) message (valArg message)
      (toArg message) (fromArg message)).toNat +
      (sendOf (checkState state message) message (valArg message)).toNat
  · exact (no_ok2 (fun g h1 h2 => spec_toOvF hfork hstatic hacc hl hsize' hsel hv hp hb
      hdep hov hallow hfv hbal hto hc0 hcB hc10 hcA hc3 hc4 hcF hcT h1 h2)
      (fun _ e h => faulted_error e h) start within hrun hok).elim
  have hto := Nat.lt_of_not_le hto
  refine ⟨hl, hp, hb, hov, hallow, hfv, hbal, hto, ?_⟩
  by_cases hfee : feeOf (checkState state message) message (valArg message) = 0
  · have hto' := hto
    rw [sendOf_zero hfee] at hto'
    obtain ⟨-, -, ho, hg, hst, hss⟩ := ok_exact2
      (fun g h1 h2 => spec_ok hfork hstatic hacc hl hsize' hsel hv hp hb hdep hov hfee
        hallow hbal hto' hc0 hcB hc10 hcA hc3 hc4 hcF hcT h1 h2)
      start within hrun hok
    exact ⟨ho, .inl ⟨hfee, hg, hst, hss⟩⟩
  by_cases hown : 2 ^ 256 ≤ (balOF (checkState state message) message (valArg message)
      (toArg message) (fromArg message)).toNat +
      (feeOf (checkState state message) message (valArg message)).toNat
  · exact (no_ok2 (fun g h1 h2 => spec_ownerOvF hfork hstatic hacc hl hsize' hsel hv hp hb
      hdep hov hallow hfee hfv hbal hto hown hc0 hcB hc10 hcA hc3 hc4 hcF hcT hcO h1 h2)
      (fun _ e h => faulted_error e h) start within hrun hok).elim
  have hown := Nat.lt_of_not_le hown
  obtain ⟨-, -, ho, hg, hst, hss⟩ := ok_exact (Nat.le_refl _)
    (fun g hg => spec_feeF hfork hstatic hacc hl hsize' hsel hv hp hb hdep hov hfee hfv
      hallow hbal hto hown hc0 hcB hc10 hcA hc3 hc4 hcF hcT hcO hg)
    start within hrun hok
  exact ⟨ho, .inr ⟨hfee, hown, hg, hst, hss⟩⟩

end UsdtVerify.Complete
