import UsdtVerify.Usdt.Exact.Getters
import UsdtVerify.Usdt.Complete.Transfer

/-!
# Exact success condition of transfer, not deprecated

From Berlin, a fresh frame of `CODE` at pc 0 with call data below `2^256` bytes, the selector
0xa9059cbb and byte 20 of slot 10 equal to 0 (`hdep`), any gas bound and any message runner.

- `transfer_ok_iff`: with the gas of the success path (`transferCost`; with a fee of 0 also the
  two bounds `transferStip1`, `transferStip2` of more than 2300 gas left at the two SSTOREs), the
  run ends with no error if and only if `TransferGuard` holds.
- `transfer_low`: with less gas than `transferCost`, no run ends with no error.
  A gas between `transferCost` and a stipend bound is not covered.
-/

namespace UsdtVerify.Exact

open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open UsdtVerify.Gas
open Complete Transfer TransferOk TransferFee SafeMath

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate} {bound : Nat} {runChild : MessageRunner fork Nat bound}
  {evm : Evm fork Nat} {gas : Nat}

/-- The cost of the success path of `transfer(a, v)`: `okCost` with a fee of 0, `feeCost`
otherwise. -/
abbrev transferCost (fork : Fork) (state : State.TransactionState) (message : Message fork)
    (c0 cB c10 c3 c4 cS cT cO : Bool) : Nat :=
  if feeOf (shortState state message) message (wordArg message.data 1) = 0 then
    okCost fork state message c0 cB c10 c3 c4 cS cT
  else feeCost fork state message c0 cB c10 c3 c4 cS cT cO

/-- The gas that the path with a fee of 0 needs so that more than 2300 is left at the SSTORE of
the sender's balance. -/
abbrev transferStip1 (state : State.TransactionState) (message : Message fork)
    (c0 cB c10 c3 c4 cS : Bool) : Nat :=
  PRE_COST + slotCost c0 + slotCost cB + slotCost c10 + (530 + slotCost c3 +
    slotCost c4 + slotCost cS + mulCost (wordArg message.data 1) +
    capCost (rawFee (shortState state message) message (wordArg message.data 1))
      (storageAt (shortState state message) message.currentTarget 4) + 2400)

/-- The gas that the path with a fee of 0 needs so that more than 2300 is left at the SSTORE of
the recipient's balance. -/
abbrev transferStip2 (fork : Fork) (state : State.TransactionState) (message : Message fork)
    (c0 cB c10 c3 c4 cS cT : Bool) : Nat :=
  PRE_COST + slotCost c0 + slotCost cB + slotCost c10 + (837 + readCost c3 c4 cS cT +
    mulCost (wordArg message.data 1) +
    capCost (rawFee (shortState state message) message (wordArg message.data 1))
      (storageAt (shortState state message) message.currentTarget 4) +
    debitCost fork (shortState state message) message (wordArg message.data 1) + 2401)

section

variable (hfork : .berlin ≤ fork) (hsize' : message.data.size < 2 ^ 256)
  (start : At CODE message 0 [] .empty gas state substate evm)
  (within : GasMeter.gasHeld evm.gas ≤ bound)
  (hsel : selector message.data = 0xa9059cbb)
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
include hfork hsize' start hsel hdep hc0 hcB hc10 hc3 hc4 hcS hcT hcO

theorem transfer_comp (s : Evm fork Nat)
    (hs : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) : TransferGuard state message := by
  obtain ⟨hst, hacc, hl, hp, hb, hov, hfv, hbal, hto, -, h⟩ :=
    ok_transfer hfork hsize' hsel hdep hc0 hcB hc10 hc3 hc4 hcS hcT hcO start within hs hok
  refine ⟨callOk_of_run hfork hsize' start within s hs hok, ⟨hst, hacc⟩, hl, hp, hb, hov, hfv,
    hbal, hto, fun hfee => ?_⟩
  rcases h with ⟨h0, -⟩ | ⟨-, hown, -⟩
  · exact absurd h0 hfee
  · exact hown

/-- `transfer(a, v)`, not deprecated, succeeds exactly when `TransferGuard` holds, with the gas of
its success path. -/
theorem transfer_ok_iff
    (hstip : feeOf (shortState state message) message (wordArg message.data 1) = 0 →
      transferStip1 state message c0 cB c10 c3 c4 cS ≤ gas ∧
        transferStip2 fork state message c0 cB c10 c3 c4 cS cT ≤ gas)
    (hg : transferCost fork state message c0 cB c10 c3 c4 cS cT cO ≤ gas) :
    RunsOk fork bound runChild evm within ↔ TransferGuard state message := by
  refine runsOk_iff (Q := fun e => e.error = none)
    (fun ⟨⟨h4, hv⟩, ⟨hst, hacc⟩, hl, hp, hb, hov, hfv, hbal, hto, hown⟩ => ?_)
    (fun _ h => h) start within
    (transfer_comp hfork hsize' start within hsel hdep hc0 hcB hc10 hc3 hc4 hcS hcT hcO)
  by_cases hfee : feeOf (shortState state message) message (wordArg message.data 1) = 0
  · simp only [transferCost, hfee, ↓reduceIte] at hg
    obtain ⟨h1, h2⟩ := hstip hfee
    rw [sendOf_zero hfee] at hto
    exact (spec_ok hfork hst hacc hl hsize' hsel hv hp hb hdep hov hfee hbal hto hc0 hcB hc10
      hc3 hc4 hcS hcT h1 h2 hg).consequence (fun _ h => h) halted_false_ok
  · simp only [transferCost, hfee, ↓reduceIte] at hg
    exact (spec_fee hfork hst hacc hl hsize' hsel hv hp hb hdep hov hfee hfv hbal hto (hown hfee)
      hc0 hcB hc10 hc3 hc4 hcS hcT hcO hg).consequence (fun _ h => h) halted_false_ok

theorem transfer_low (hg : gas < transferCost fork state message c0 cB c10 c3 c4 cS cT cO) :
    ¬ RunsOk fork bound runChild evm within := by
  have hcomp := transfer_comp (runChild := runChild) hfork hsize' start within hsel hdep hc0 hcB hc10 hc3 hc4 hcS hcT hcO
  by_cases hfee : feeOf (shortState state message) message (wordArg message.data 1) = 0
  · simp only [transferCost, hfee, ↓reduceIte] at hg
    exact not_runsOk_low3 hg
      (fun ⟨⟨h4, hv⟩, ⟨hst, hacc⟩, hl, hp, hb, hov, hfv, hbal, hto, hown⟩ _ =>
        spec_ok hfork hst hacc hl hsize' hsel hv hp hb hdep hov hfee hbal
          (by rw [sendOf_zero hfee] at hto; exact hto) hc0 hcB hc10 hc3 hc4 hcS hcT)
      start within hcomp
  · simp only [transferCost, hfee, ↓reduceIte] at hg
    exact not_runsOk_low (Nat.le_refl _) hg
      (fun ⟨⟨h4, hv⟩, ⟨hst, hacc⟩, hl, hp, hb, hov, hfv, hbal, hto, hown⟩ _ =>
        spec_fee hfork hst hacc hl hsize' hsel hv hp hb hdep hov hfee hfv hbal hto (hown hfee)
          hc0 hcB hc10 hc3 hc4 hcS hcT hcO)
      start within hcomp

end

end UsdtVerify.Exact
