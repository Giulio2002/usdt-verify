import UsdtVerify.Evm.Exact
import UsdtVerify.Usdt.Complete.Dispatch
import UsdtVerify.Usdt.Complete.Transfer
import UsdtVerify.Usdt.Spec.TransferFrom

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

Hypotheses beyond the call: Berlin ≤ fork (Glamsterdam included). A static frame, or a contract
with no account, is excluded by `Gas.no_ok_stuckE`: with an allowance `A ≠ MAX_UINT` (and
`v ≤ A`) the SSTORE of the allowance is `Gas.Stuck` (`bad_allowF`); with `A = MAX_UINT` nothing
is written there, the INVALIDs of `spec_feeGtF` and `spec_balLow` are excluded as before (their
hypothesis `hgood` asks for a non-static frame and an account only when `A ≠ MAX_UINT`), and the
SSTORE of `balances[f]` is `Gas.Stuck` (`bad_transferFrom`). So the conclusion states
`message.isStatic = false` and an account of the contract.
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
path. The conclusion states that the frame is not static and the contract has an account:
otherwise the first SSTORE of the path (of the allowance, or of `balances[f]` when the allowance
is `MAX_UINT`) is `Gas.Stuck` (`bad_allowF`, `bad_transferFrom`). -/
theorem ok_transferFrom (hfork : .berlin ≤ fork)
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
    (hrun : Ends fork evm s)
    (hok : s.error = none) :
    message.isStatic = false ∧ hasAccount state message.currentTarget ∧
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
        (okCostF fork state message c0 cB c10 cA c3 c4 cF cT ≤ gas ∧
          s.gas = gas - okCostF fork state message c0 cB c10 cA c3 c4 cF cT) ∧
        s.state = creditedF (checkState state message) message (valArg message) (toArg message)
          (fromArg message) ∧
        s.substate = loggedSubF fork (checkSub substate message) (checkState state message)
          message (valArg message) (toArg message) (fromArg message)) ∨
      (feeOf (checkState state message) message (valArg message) ≠ 0 ∧
        (balOF (checkState state message) message (valArg message) (toArg message)
          (fromArg message)).toNat +
          (feeOf (checkState state message) message (valArg message)).toNat < 2 ^ 256 ∧
        (feeCostF fork state message c0 cB c10 cA c3 c4 cF cT cO ≤ gas ∧
          s.gas = gas - feeCostF fork state message c0 cB c10 cA c3 c4 cF cT cO) ∧
        s.state = feeStateF (checkState state message) message (valArg message) (toArg message)
          (fromArg message) ∧
        s.substate = feeSubF fork (checkSub substate message) (checkState state message) message
          (valArg message) (toArg message) (fromArg message))) := by
  obtain ⟨h4, hv, -⟩ := ends_ok_dispatch hfork hsize' start hrun hok
  by_cases hp : byte20 (storageAt state message.currentTarget 0) ≠ 0
  · exact (no_okE (fun g hg => spec_paused hfork h4 hsize' hsel hv hp hc0 hg)
      (fun _ e h => halted_true_error e h) start hrun hok).elim
  have hp : byte20 (storageAt state message.currentTarget 0) = 0 := by omega
  by_cases hb : (storageAt state message.currentTarget (blackFrom (fromArg message))).toNat %
      256 ≠ 0
  · exact (no_okE (fun g hg => spec_blacklisted hfork h4 hsize' hsel hv hp hb hc0 hcB hg)
      (fun _ e h => halted_true_error e h) start hrun hok).elim
  have hb : (storageAt state message.currentTarget (blackFrom (fromArg message))).toNat % 256 =
      0 := by omega
  by_cases hl : message.data.size < 100
  · exact (no_okE (fun g hg => spec_short hfork h4 hl hsel hv hp hb hdep hc0 hcB hc10 hg)
      (fun _ e h => halted_true_error e h) start hrun hok).elim
  have hl : 100 ≤ message.data.size := by omega
  by_cases hov : 2 ^ 256 ≤ (valArg message).toNat *
      (storageAt (checkState state message) message.currentTarget 3).toNat
  · exact (no_okE (fun g hg => spec_mulOv hfork hl hsize' hsel hv hp hb hdep hov hc0 hcB hc10 hcA
      hc3 hg) (fun _ e h => faulted_error e h) start hrun hok).elim
  have hov := Nat.lt_of_not_le hov
  by_cases hlt : (allowOf (checkState state message) message (fromArg message)).toNat <
      (valArg message).toNat
  · exact (no_okE (fun g hg => spec_allowLow hfork hl hsize' hsel hv hp hb hdep hov hlt hc0 hcB
      hc10 hcA hc3 hc4 hg) (fun _ e h => faulted_error e h) start hrun hok).elim
  have hallow : allowOf (checkState state message) message (fromArg message) = MAX_UINT ∨
      (valArg message).toNat ≤
        (allowOf (checkState state message) message (fromArg message)).toNat :=
    .inr (Nat.le_of_not_lt hlt)
  by_cases hA : allowOf (checkState state message) message (fromArg message) ≠ MAX_UINT ∧
      ¬(message.isStatic = false ∧ hasAccount state message.currentTarget)
  · exact (Gas.no_ok_stuckE (fun g hg => bad_allowF hfork (Gas.bad_of_not hA.2) hl hsize' hsel hv
      hp hb hdep hov hA.1 (Nat.le_of_not_lt hlt) hc0 hcB hc10 hcA hc3 hc4 hg) start hrun
      hok).elim
  have hw : allowOf (checkState state message) message (fromArg message) ≠ MAX_UINT →
      message.isStatic = false ∧ hasAccount state message.currentTarget :=
    fun h => Classical.not_not.mp fun h' => hA ⟨h, h'⟩
  by_cases hgt : (valArg message).toNat <
      (feeOf (checkState state message) message (valArg message)).toNat
  · exact (no_okE (fun g hg => spec_feeGtF hfork hl hsize' hsel hv hp hb hdep
      hov hallow hw hgt hc0 hcB hc10 hcA hc3 hc4 hg)
      (fun _ e h => faulted_error e h) start hrun hok).elim
  have hfv := Nat.le_of_not_lt hgt
  by_cases hlow : (balFrom (checkState state message) message (valArg message)
      (fromArg message)).toNat < (valArg message).toNat
  · exact (no_ok2E (fun g h1 h2 => spec_balLow hfork hl hsize' hsel hv hp hb
      hdep hov hfv hallow hw hlow hc0 hcB hc10 hcA hc3 hc4 hcF h1 h2)
      (fun _ e h => faulted_error e h) start hrun hok).elim
  have hbal := Nat.le_of_not_lt hlow
  by_cases hgood : ¬(message.isStatic = false ∧ hasAccount state message.currentTarget)
  · have hmax : allowOf (checkState state message) message (fromArg message) = MAX_UINT :=
      Classical.byContradiction fun h => hgood (hw h)
    exact (Gas.no_ok_stuckE (fun g hg => bad_transferFrom hfork (Gas.bad_of_not hgood) hl hsize'
      hsel hv hp hb hdep hov hfv hmax hbal hc0 hcB hc10 hcA hc3 hc4 hcF hg) start hrun
      hok).elim
  obtain ⟨hstatic, hacc⟩ := Classical.not_not.mp hgood
  by_cases hto : 2 ^ 256 ≤ (balTo (checkState state message) message (valArg message)
      (toArg message) (fromArg message)).toNat +
      (sendOf (checkState state message) message (valArg message)).toNat
  · exact (no_ok2E (fun g h1 h2 => spec_toOvF hfork hstatic hacc hl hsize' hsel hv hp hb
      hdep hov hallow hfv hbal hto hc0 hcB hc10 hcA hc3 hc4 hcF hcT h1 h2)
      (fun _ e h => faulted_error e h) start hrun hok).elim
  have hto := Nat.lt_of_not_le hto
  refine ⟨hstatic, hacc, hl, hp, hb, hov, hallow, hfv, hbal, hto, ?_⟩
  by_cases hfee : feeOf (checkState state message) message (valArg message) = 0
  · have hto' := hto
    rw [sendOf_zero hfee] at hto'
    obtain ⟨hcg, -, ho, hg, hst, hss⟩ := ok_exact2E
      (fun g h1 h2 => spec_ok hfork hstatic hacc hl hsize' hsel hv hp hb hdep hov hfee
        hallow hbal hto' hc0 hcB hc10 hcA hc3 hc4 hcF hcT h1 h2)
      start hrun hok
    exact ⟨ho, .inl ⟨hfee, ⟨hcg, hg⟩, hst, hss⟩⟩
  by_cases hown : 2 ^ 256 ≤ (balOF (checkState state message) message (valArg message)
      (toArg message) (fromArg message)).toNat +
      (feeOf (checkState state message) message (valArg message)).toNat
  · exact (no_ok2E (fun g h1 h2 => spec_ownerOvF hfork hstatic hacc hl hsize' hsel hv hp hb
      hdep hov hallow hfee hfv hbal hto hown hc0 hcB hc10 hcA hc3 hc4 hcF hcT hcO h1 h2)
      (fun _ e h => faulted_error e h) start hrun hok).elim
  have hown := Nat.lt_of_not_le hown
  obtain ⟨hcg, -, ho, hg, hst, hss⟩ := ok_exactE (Nat.le_refl _)
    (fun g hg => spec_feeF hfork hstatic hacc hl hsize' hsel hv hp hb hdep hov hfee hfv
      hallow hbal hto hown hc0 hcB hc10 hcA hc3 hc4 hcF hcT hcO hg)
    start hrun hok
  exact ⟨ho, .inr ⟨hfee, hown, ⟨hcg, hg⟩, hst, hss⟩⟩

end UsdtVerify.Complete
