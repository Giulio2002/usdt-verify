import UsdtVerify.Usdt.Refill.Approve
import UsdtVerify.Usdt.Exact.Approve
import UsdtVerify.Evm.Shadow
import UsdtVerify.Usdt.Refill.Transfer
import UsdtVerify.Usdt.Refill.Fee
import UsdtVerify.Usdt.Refill.TransferFrom
import UsdtVerify.Usdt.Exact.Transfer
import UsdtVerify.Usdt.Exact.TransferFrom

/-!
# Exact success conditions over EthLib's EIP-8037 meter

EthLib runs Glamsterdam transactions with the meter `StateGasMeter`. The theorems here are about
the loop of the interpreter over that meter, for any gas bound and message runner, from a frame
`m` whose `toNat` (its fields, with its execution gas left as the gas) is the fresh frame of `CODE`
with `gas` gas.

- `ok_approve_any`: a run of `approve` that ends with no error meets `ApproveGuard`, and its
  output, state and substate are those of `ok_approve`. Any reservoir; SSTORE may refill.
- `approve_iff_gas_sgm`: with reservoir 0, and when the write of the allowance refills nothing
  (`hnr`), the run ends with no error if and only if `ApproveGuard` holds and the gas is at least
  the larger of `approveCost` and `approveStip`.
- `approve_ok_sgm`: in that case, the execution gas left is `gas - approveCost`.
- `ok_transfer_any`, `ok_transferFrom_any`: as `ok_approve_any`, for `transfer` and
  `transferFrom`, with `TransferGuard` and `TransferFromGuard`.
- `transfer_iff_gas_sgm`, `transfer_ok_sgm`: as for `approve`, for `transfer` (fee 0 or above
  0), when the write of the sender's balance refills nothing (`hnrD`). The writes of the
  recipient's and the owner's balances add to them without overflow, so they never refill.
- `transferFrom_iff_gas_sgm`, `transferFrom_ok_sgm`: as for `approve`, for `transferFrom` (fee 0
  or above 0), when the write of the allowance (only made when `A ≠ MAX_UINT`, `hnrA`) and the
  write of `balances[_from]` (`hnrD`) refill nothing.

The write of `approve(s, v)` refills, from Glamsterdam, exactly when `v = 0`, the allowance slot
was 0 at the start of the transaction, and it is not 0 at the call (`sstoreStateRefill`). The
write of the sender's balance in `transfer(a, v)` refills exactly when that slot was 0 at the start
of the transaction, is not 0 at the call, and `v` is the whole balance. In `transferFrom(f, t, v)`
the allowance write refills when `A ≠ MAX_UINT`, its slot was 0 at the start of the transaction,
`A ≠ 0` and `v = A`; the write of `balances[f]` as the sender's in `transfer`, with the balance
read after the allowance step.
-/

namespace UsdtVerify.Exact

open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open UsdtVerify.Gas
open UsdtVerify.Meter
open UsdtVerify.Refill
open UsdtVerify.Shadow
open Complete Approve

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate} {bound : Nat} {runChild : MessageRunner fork StateGasMeter bound}
  {m s : Evm fork StateGasMeter} {gas : Nat}

/-- **approve over the EIP-8037 meter, any reservoir.** A run of the loop over `StateGasMeter`
from `m`, for any gas bound and message runner, that ends with no error meets `ApproveGuard`;
its output is empty, and its state and substate are those of the path of `ok_approve`. -/
theorem ok_approve_any (hfork : .berlin ≤ fork) (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x095ea7b3)
    (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    (start : At CODE message 0 [] .empty gas state substate (toNat m))
    {within : GasMeter.gasHeld m.gas ≤ bound}
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild m within = .ok s)
    (hok : s.error = none) :
    ApproveGuard state message ∧ s.output = .empty ∧
      ((wordArg message.data 1 = 0 ∧
        s.state = writeSlot (readSlot state message.currentTarget 10) message.currentTarget
          (allowArg message) 0 ∧
        s.substate = { storeSub fork (accessSlot substate message.currentTarget 10)
            message.currentTarget (allowArg message)
            (originalAt state message.currentTarget (allowArg message))
            (storageAt state message.currentTarget (allowArg message)) 0 with
          logs := substate.logs.push (approvalLog message.currentTarget
            (bitwiseAnd ADDR_MASK message.caller.toU256)
            (bitwiseAnd ADDR_MASK (addrArg message.data 0)) 0) }) ∨
      (wordArg message.data 1 ≠ 0 ∧
        s.state = writeSlot (readSlot (readSlot state message.currentTarget 10)
          message.currentTarget (allowArg message)) message.currentTarget (allowArg message)
          (wordArg message.data 1) ∧
        s.substate = { storeSub fork (accessSlot (accessSlot substate message.currentTarget 10)
              message.currentTarget (allowArg message)) message.currentTarget
            (allowArg message) (originalAt state message.currentTarget (allowArg message)) 0
            (wordArg message.data 1) with
          logs := substate.logs.push (approvalLog message.currentTarget
            (bitwiseAnd ADDR_MASK message.caller.toU256)
            (bitwiseAnd ADDR_MASK (addrArg message.data 0)) (wordArg message.data 1)) })) := by
  obtain ⟨G, hE⟩ := shadow_ends hfork hrun hok
  have st' := at_sh start (budget m)
  obtain ⟨h4, hv, -⟩ := ends_ok_dispatch hfork hsize' st' hE hok
  obtain ⟨hst, hacc, hl, ho, h⟩ := ok_approve hfork hsize' hsel hdep rfl rfl st' hE hok
  refine ⟨⟨⟨h4, hv⟩, ⟨hst, hacc⟩, hl, fun hz => ?_⟩, ho, ?_⟩
  · rcases h with ⟨h0, -⟩ | ⟨-, ha, -⟩
    · exact absurd h0 hz
    · exact ha
  · rcases h with ⟨h0, -, hs, hss⟩ | ⟨h0, -, -, hs, hss⟩
    · exact .inl ⟨h0, hs, hss⟩
    · exact .inr ⟨h0, hs, hss⟩

section

variable (hfork : .berlin ≤ fork) (hsize' : message.data.size < 2 ^ 256)
  (hsel : selector message.data = 0x095ea7b3)
  (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
  {c10 cA : Bool} (hc10 : coldIn substate message.currentTarget 10 = c10)
  (hcA : coldIn (accessSlot substate message.currentTarget 10) message.currentTarget
    (allowArg message) = cA)
  (start : At CODE message 0 [] .empty gas state substate (toNat m))
  (hres : m.gas.reservoir = 0)
  (hnr : sstoreStateRefill fork (originalAt state message.currentTarget (allowArg message))
    (storageAt state message.currentTarget (allowArg message)) (wordArg message.data 1) = 0)
include hfork hsize' hsel hdep hc10 hcA start hres hnr

omit start hres in
/-- The success path of `approve` over `StepI`, under `ApproveGuard`, with at least the larger of
`approveCost` and `approveStip` gas. -/
theorem approve_specI (hG : ApproveGuard state message) {g : Nat}
    (hm : max (approveCost fork state message c10 cA) (approveStip message c10 cA) ≤ g) :
    HoareI fork (At CODE message 0 [] .empty g state substate)
      (fun e => e.running = false ∧
        Halted false .empty (g - approveCost fork state message c10 cA)
          e.state e.substate e) := by
  obtain ⟨⟨h4, hv⟩, ⟨hst, hacc⟩, hl, ha⟩ := hG
  obtain ⟨hc, hs⟩ := Nat.max_le.mp hm
  by_cases hz : wordArg message.data 1 = 0
  · simp only [approveCost, approveStip, hz, ↓reduceIte] at hc hs
    refine (spec_zeroI hfork hst hacc hl hsize' hsel hv hdep hz hc10 hcA hs hc
      (by rw [hz] at hnr; exact hnr)).consequence (fun _ h => h) ?_
    rintro e ⟨hr, h1, h2, h3, h4, -, -⟩
    simp only [approveCost, hz, ↓reduceIte]
    exact ⟨hr, h1, h2, h3, h4, rfl, rfl⟩
  · simp only [approveCost, approveStip, hz, ↓reduceIte] at hc hs
    refine (spec_setI hfork hst hacc hl hsize' hsel hv hdep hz (ha hz) hc10 hcA hs
      hc).consequence (fun _ h => h) ?_
    rintro e ⟨hr, h1, h2, h3, h4, -, -⟩
    simp only [approveCost, hz, ↓reduceIte]
    exact ⟨hr, h1, h2, h3, h4, rfl, rfl⟩

/-- **approve over the EIP-8037 meter, with enough gas.** From reservoir 0, when the write of
the allowance refills nothing, under `ApproveGuard` and with at least the larger of `approveCost`
and `approveStip` gas, the loop over `StateGasMeter`, for any gas bound and message runner, ends
with no error and `gas - approveCost` execution gas left. -/
theorem approve_ok_sgm (hG : ApproveGuard state message)
    (hm : max (approveCost fork state message c10 cA) (approveStip message c10 cA) ≤ gas)
    (within : GasMeter.gasHeld m.gas ≤ bound) :
    ∃ s, Evm.runFrame (step fork) (step_decreases fork) bound runChild m within = .ok s ∧
      s.error = none ∧ s.gas.gasLeft = gas - approveCost fork state message c10 cA := by
  obtain ⟨s, hs, -, he, -, hg, -⟩ := runFrame_of_specI
    (approve_specI hfork hsize' hsel hdep hc10 hcA hnr hG hm) start hres within
  exact ⟨s, hs, he, hg⟩

/-- **approve over the EIP-8037 meter: the exact success condition.** From reservoir 0, when the
write of the allowance refills nothing (`hnr`), the loop over `StateGasMeter`, for any gas bound
and message runner, ends with no error if and only if `ApproveGuard` holds and the gas is at least
the larger of `approveCost` and `approveStip`. -/
theorem approve_iff_gas_sgm (within : GasMeter.gasHeld m.gas ≤ bound) :
    RunsOkS fork bound runChild m within ↔ ApproveGuard state message ∧
      max (approveCost fork state message c10 cA) (approveStip message c10 cA) ≤ gas := by
  constructor
  · rintro ⟨s, hs, hok⟩
    have hG := (ok_approve_any hfork hsize' hsel hdep start hs hok).1
    have hE : Ends fork (toNat m) (toNat s) :=
      ends_of_specI (approve_specI hfork hsize' hsel hdep hc10 hcA hnr hG
        (g := gas + max (approveCost fork state message c10 cA) (approveStip message c10 cA))
        (Nat.le_add_left _ _)) (at_sh start _) hres hs
    refine ⟨hG, Nat.max_le.mpr ⟨?_, ?_⟩⟩
    · obtain ⟨-, -, -, -, h⟩ := ok_approve hfork hsize' hsel hdep hc10 hcA start hE hok
      by_cases hz : wordArg message.data 1 = 0
      · simp only [approveCost, hz, ↓reduceIte]
        rcases h with ⟨-, ⟨hc, -⟩, -⟩ | ⟨h0, -⟩
        · exact hc
        · exact absurd hz h0
      · simp only [approveCost, hz, ↓reduceIte]
        rcases h with ⟨h0, -⟩ | ⟨-, -, ⟨hc, -⟩, -⟩
        · exact absurd h0 hz
        · exact hc
    · obtain ⟨⟨h4, hv⟩, -, hl, ha⟩ := hG
      refine Nat.le_of_not_lt fun hlt => ?_
      by_cases hz : wordArg message.data 1 = 0
      · simp only [approveStip, hz, ↓reduceIte] at hlt
        by_cases hlo : 696 + slotCost c10 ≤ gas
        · exact no_ok_stuck_atE (bad_zero hfork hl hsize' hsel hv hdep hz hc10
            (.of_low hfork (by omega)) hlo) start hE hok
        · obtain ⟨-, -, -, -, h⟩ := ok_approve hfork hsize' hsel hdep hc10 hcA start hE hok
          rcases h with ⟨-, ⟨hc, -⟩, -⟩ | ⟨h0, -⟩
          · omega
          · exact h0 hz
      · simp only [approveStip, hz, ↓reduceIte] at hlt
        by_cases hlo : 889 + slotCost c10 + slotCost cA ≤ gas
        · exact no_ok_stuck_atE (bad_set hfork hl hsize' hsel hv hdep hz (ha hz) hc10 hcA
            (.of_low hfork (by omega)) hlo) start hE hok
        · obtain ⟨-, -, -, -, h⟩ := ok_approve hfork hsize' hsel hdep hc10 hcA start hE hok
          rcases h with ⟨h0, -⟩ | ⟨-, -, ⟨hc, -⟩, -⟩
          · exact hz h0
          · omega
  · rintro ⟨hG, hm⟩
    obtain ⟨s, hs, he, -⟩ := approve_ok_sgm hfork hsize' hsel hdep hc10 hcA start hres hnr hG hm
      within
    exact ⟨s, hs, he⟩

end


section Transfer

open Transfer TransferOk TransferFee SafeMath

/-- **transfer over the EIP-8037 meter, any reservoir.** A run of the loop over `StateGasMeter`
from `m`, for any gas bound and message runner, that ends with no error meets `TransferGuard`;
its output is empty, and its state and substate are those of the path of `ok_transfer`. -/
theorem ok_transfer_any (hfork : .berlin ≤ fork) (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0xa9059cbb)
    (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    (start : At CODE message 0 [] .empty gas state substate (toNat m))
    {within : GasMeter.gasHeld m.gas ≤ bound}
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild m within = .ok s)
    (hok : s.error = none) :
    TransferGuard state message ∧ s.output = .empty ∧
      ((feeOf (shortState state message) message (wordArg message.data 1) = 0 ∧
        s.state = credited (shortState state message) message (wordArg message.data 1)
          (addrArg message.data 0) ∧
        s.substate = loggedSub fork (shortSubstate substate message) (shortState state message)
          message (wordArg message.data 1) (addrArg message.data 0)) ∨
      (feeOf (shortState state message) message (wordArg message.data 1) ≠ 0 ∧
        s.state = feeState (shortState state message) message (wordArg message.data 1)
          (addrArg message.data 0) ∧
        s.substate = feeSub fork (shortSubstate substate message) (shortState state message)
          message (wordArg message.data 1) (addrArg message.data 0))) := by
  obtain ⟨G, hE⟩ := shadow_ends hfork hrun hok
  have st' := at_sh start (budget m)
  obtain ⟨h4, hv, -⟩ := ends_ok_dispatch hfork hsize' st' hE hok
  obtain ⟨hst, hacc, hl, hp, hb, hov, hfv, hbal, hto, ho, h⟩ :=
    ok_transfer hfork hsize' hsel hdep rfl rfl rfl rfl rfl rfl rfl rfl st' hE hok
  refine ⟨⟨⟨h4, hv⟩, ⟨hst, hacc⟩, hl, hp, hb, hov, hfv, hbal, hto, fun hfee => ?_⟩, ho, ?_⟩
  · rcases h with ⟨h0, -⟩ | ⟨-, hown, -⟩
    · exact absurd h0 hfee
    · exact hown
  · rcases h with ⟨h0, -, hs, hss⟩ | ⟨h0, -, -, hs, hss⟩
    · exact .inl ⟨h0, hs, hss⟩
    · exact .inr ⟨h0, hs, hss⟩

theorem stip1_le_stip2 (fork : Fork) (state : State.TransactionState) (message : Message fork)
    (c0 cB c10 c3 c4 cS cT : Bool) :
    transferStip1 state message c0 cB c10 c3 c4 cS ≤
      transferStip2 fork state message c0 cB c10 c3 c4 cS cT := by
  simp only [transferStip1, transferStip2, readCost]
  omega

section

variable (hfork : .berlin ≤ fork) (hsize' : message.data.size < 2 ^ 256)
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
  (start : At CODE message 0 [] .empty gas state substate (toNat m))
  (hres : m.gas.reservoir = 0)
  (hnrD : sstoreStateRefill fork (originalAt state message.currentTarget (senderSlot message))
    (balS (shortState state message) message)
    (sub (balS (shortState state message) message) (wordArg message.data 1)) = 0)
include hfork hsize' hsel hdep hc0 hcB hc10 hc3 hc4 hcS hcT hcO start hres hnrD

omit start hres in
/-- The success path of `transfer` over `StepI`, under `TransferGuard`, with at least the larger
of `transferCost` and `transferStip` gas. -/
theorem transfer_specI (hG : TransferGuard state message) {g : Nat}
    (hm : max (transferCost fork state message c0 cB c10 c3 c4 cS cT cO)
      (transferStip fork state message c0 cB c10 c3 c4 cS cT) ≤ g) :
    HoareI fork (At CODE message 0 [] .empty g state substate)
      (fun e => e.running = false ∧
        Halted false .empty (g - transferCost fork state message c0 cB c10 c3 c4 cS cT cO)
          e.state e.substate e) := by
  obtain ⟨⟨h4, hv⟩, ⟨hst, hacc⟩, hl, hp, hb, hov, hfv, hbal, hto, hown⟩ := hG
  obtain ⟨hc, hs⟩ := Nat.max_le.mp hm
  by_cases hfee : feeOf (shortState state message) message (wordArg message.data 1) = 0
  · simp only [transferCost, transferStip, hfee, ↓reduceIte] at hc hs
    have h1 : transferStip1 state message c0 cB c10 c3 c4 cS ≤ g :=
      Nat.le_trans (stip1_le_stip2 fork state message c0 cB c10 c3 c4 cS cT) hs
    rw [sendOf_zero hfee] at hto
    refine (spec_okI hfork hst hacc hl hsize' hsel hv hp hb hdep hov hfee hbal hto hc0 hcB hc10
      hc3 hc4 hcS hcT hnrD h1 hs hc).consequence (fun _ h => h) ?_
    rintro e ⟨hr, h1, h2, h3, h4, -, -⟩
    simp only [transferCost, hfee, ↓reduceIte]
    exact ⟨hr, h1, h2, h3, h4, rfl, rfl⟩
  · simp only [transferCost, hfee, ↓reduceIte] at hc
    refine (spec_feeI hfork hst hacc hl hsize' hsel hv hp hb hdep hov hfee hfv hbal hto
      (hown hfee) hc0 hcB hc10 hc3 hc4 hcS hcT hcO hnrD hc).consequence (fun _ h => h) ?_
    rintro e ⟨hr, h1, h2, h3, h4, -, -⟩
    simp only [transferCost, hfee, ↓reduceIte]
    exact ⟨hr, h1, h2, h3, h4, rfl, rfl⟩

/-- **transfer over the EIP-8037 meter, with enough gas.** From reservoir 0, when the write of the
sender's balance refills nothing (`hnrD`), under `TransferGuard` and with at least the larger of
`transferCost` and `transferStip` gas, the loop over `StateGasMeter`, for any gas bound and
message runner, ends with no error and `gas - transferCost` execution gas left. -/
theorem transfer_ok_sgm (hG : TransferGuard state message)
    (hm : max (transferCost fork state message c0 cB c10 c3 c4 cS cT cO)
      (transferStip fork state message c0 cB c10 c3 c4 cS cT) ≤ gas)
    (within : GasMeter.gasHeld m.gas ≤ bound) :
    ∃ s, Evm.runFrame (step fork) (step_decreases fork) bound runChild m within = .ok s ∧
      s.error = none ∧
      s.gas.gasLeft = gas - transferCost fork state message c0 cB c10 c3 c4 cS cT cO := by
  obtain ⟨s, hs, -, he, -, hg, -⟩ := runFrame_of_specI
    (transfer_specI hfork hsize' hsel hdep hc0 hcB hc10 hc3 hc4 hcS hcT hcO hnrD hG hm)
    start hres within
  exact ⟨s, hs, he, hg⟩

/-- **transfer over the EIP-8037 meter: the exact success condition.** From reservoir 0, when the
write of the sender's balance refills nothing (`hnrD`), the loop over `StateGasMeter`, for any gas
bound and message runner, ends with no error if and only if `TransferGuard` holds and the gas is
at least the larger of `transferCost` and `transferStip`. -/
theorem transfer_iff_gas_sgm (within : GasMeter.gasHeld m.gas ≤ bound) :
    RunsOkS fork bound runChild m within ↔ TransferGuard state message ∧
      max (transferCost fork state message c0 cB c10 c3 c4 cS cT cO)
        (transferStip fork state message c0 cB c10 c3 c4 cS cT) ≤ gas := by
  constructor
  · rintro ⟨s, hs, hok⟩
    have hG := (ok_transfer_any hfork hsize' hsel hdep start hs hok).1
    have hE : Ends fork (toNat m) (toNat s) :=
      ends_of_specI (transfer_specI hfork hsize' hsel hdep hc0 hcB hc10 hc3 hc4 hcS hcT hcO
        hnrD hG (g := gas + max (transferCost fork state message c0 cB c10 c3 c4 cS cT cO)
          (transferStip fork state message c0 cB c10 c3 c4 cS cT)) (Nat.le_add_left _ _))
        (at_sh start _) hres hs
    obtain ⟨-, -, -, -, -, -, -, -, -, -, h⟩ :=
      ok_transfer hfork hsize' hsel hdep hc0 hcB hc10 hc3 hc4 hcS hcT hcO start hE hok
    obtain ⟨⟨h4, hv⟩, ⟨hst, hacc⟩, hl, hp, hb, hov, hfv, hbal, hto, -⟩ := id hG
    by_cases hfee : feeOf (shortState state message) message (wordArg message.data 1) = 0
    · have hc : okCost fork state message c0 cB c10 c3 c4 cS cT ≤ gas := by
        rcases h with ⟨-, ⟨hc, -⟩, -⟩ | ⟨h0, -⟩
        · exact hc
        · exact absurd hfee h0
      refine ⟨hG, Nat.max_le.mpr ⟨?_, ?_⟩⟩
      · simp only [transferCost, hfee, ↓reduceIte]
        exact hc
      · simp only [transferStip, hfee, ↓reduceIte]
        refine Nat.le_of_not_lt fun hlt => ?_
        simp only [transferStip2, okCost, readCost] at hlt hc
        by_cases h1 : gas < transferStip1 state message c0 cB c10 c3 c4 cS
        · simp only [transferStip1] at h1
          exact no_ok_stuck_atE (bad_transfer hfork hl hsize' hsel hv hp hb hdep hov hfv hbal hc0
            hcB hc10 hc3 hc4 hcS (.of_low hfork (by omega)) (by omega)) start hE hok
        · simp only [transferStip1] at h1
          rw [sendOf_zero hfee] at hto
          exact no_ok_stuck_atE (low_transfer2 hfork hst hacc hl hsize' hsel hv hp hb hdep hov
            hfee hbal hto hc0 hcB hc10 hc3 hc4 hcS hcT (by omega) (by simp only [readCost]; omega)
            (by simp only [readCost]; omega)) start hE hok
    · have hc : feeCost fork state message c0 cB c10 c3 c4 cS cT cO ≤ gas := by
        rcases h with ⟨h0, -⟩ | ⟨-, -, ⟨hc, -⟩, -⟩
        · exact absurd h0 hfee
        · exact hc
      refine ⟨hG, Nat.max_le.mpr ⟨?_, ?_⟩⟩
      · simp only [transferCost, hfee, ↓reduceIte]
        exact hc
      · simp only [transferStip, hfee, ↓reduceIte]
        exact Nat.zero_le _
  · rintro ⟨hG, hm⟩
    obtain ⟨s, hs, he, -⟩ := transfer_ok_sgm hfork hsize' hsel hdep hc0 hcB hc10 hc3 hc4 hcS hcT
      hcO start hres hnrD hG hm within
    exact ⟨s, hs, he⟩

end

end Transfer

section TransferFrom

open Transfer TransferOk TransferFee SafeMath TransferFrom

/-- **transferFrom over the EIP-8037 meter, any reservoir.** A run of the loop over
`StateGasMeter` from `m`, for any gas bound and message runner, that ends with no error meets
`TransferFromGuard`; its output is empty, and its state and substate are those of the path of
`ok_transferFrom`. -/
theorem ok_transferFrom_any (hfork : .berlin ≤ fork) (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x23b872dd)
    (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    (start : At CODE message 0 [] .empty gas state substate (toNat m))
    {within : GasMeter.gasHeld m.gas ≤ bound}
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild m within = .ok s)
    (hok : s.error = none) :
    TransferFromGuard state message ∧ s.output = .empty ∧
      ((feeOf (checkState state message) message (valArg message) = 0 ∧
        s.state = creditedF (checkState state message) message (valArg message) (toArg message)
          (fromArg message) ∧
        s.substate = loggedSubF fork (checkSub substate message) (checkState state message)
          message (valArg message) (toArg message) (fromArg message)) ∨
      (feeOf (checkState state message) message (valArg message) ≠ 0 ∧
        s.state = feeStateF (checkState state message) message (valArg message) (toArg message)
          (fromArg message) ∧
        s.substate = feeSubF fork (checkSub substate message) (checkState state message) message
          (valArg message) (toArg message) (fromArg message))) := by
  obtain ⟨G, hE⟩ := shadow_ends hfork hrun hok
  have st' := at_sh start (budget m)
  obtain ⟨h4, hv, -⟩ := ends_ok_dispatch hfork hsize' st' hE hok
  obtain ⟨hst, hacc, hl, hp, hb, hov, hallow, hfv, hbal, hto, ho, h⟩ :=
    ok_transferFrom hfork hsize' hsel hdep rfl rfl rfl rfl rfl rfl rfl rfl rfl st' hE hok
  refine ⟨⟨⟨h4, hv⟩, ⟨hst, hacc⟩, hl, hp, hb, hov, hallow, hfv, hbal, hto, fun hfee => ?_⟩, ho,
    ?_⟩
  · rcases h with ⟨h0, -⟩ | ⟨-, hown, -⟩
    · exact absurd h0 hfee
    · exact hown
  · rcases h with ⟨h0, -, hs, hss⟩ | ⟨h0, -, -, hs, hss⟩
    · exact .inl ⟨h0, hs, hss⟩
    · exact .inr ⟨h0, hs, hss⟩

section

variable (hfork : .berlin ≤ fork) (hsize' : message.data.size < 2 ^ 256)
  (hsel : selector message.data = 0x23b872dd)
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
  (start : At CODE message 0 [] .empty gas state substate (toNat m))
  (hres : m.gas.reservoir = 0)
  (hnrA : allowOf (checkState state message) message (fromArg message) ≠ MAX_UINT →
    sstoreStateRefill fork
      (originalAt state message.currentTarget (allowFrom message (fromArg message)))
      (allowOf (checkState state message) message (fromArg message))
      (sub (allowOf (checkState state message) message (fromArg message)) (valArg message)) = 0)
  (hnrD : sstoreStateRefill fork
    (originalAt state message.currentTarget (recipientSlot (fromArg message)))
    (balFrom (checkState state message) message (valArg message) (fromArg message))
    (sub (balFrom (checkState state message) message (valArg message) (fromArg message))
      (valArg message)) = 0)
include hfork hsize' hsel hdep hc0 hcB hc10 hcA hc3 hc4 hcF hcT hcO start hres hnrA hnrD

omit start hres in
/-- The success path of `transferFrom` over `StepI`, under `TransferFromGuard`, with at least the
larger of `transferFromCost` and `transferFromStip` gas. -/
theorem transferFrom_specI (hG : TransferFromGuard state message) {g : Nat}
    (hm : max (transferFromCost fork state message c0 cB c10 cA c3 c4 cF cT cO)
      (transferFromStip fork state message c0 cB c10 cA c3 c4 cF cT) ≤ g) :
    HoareI fork (At CODE message 0 [] .empty g state substate)
      (fun e => e.running = false ∧
        Halted false .empty (g - transferFromCost fork state message c0 cB c10 cA c3 c4 cF cT cO)
          e.state e.substate e) := by
  obtain ⟨⟨h4, hv⟩, ⟨hst, hacc⟩, hl, hp, hb, hov, hallow, hfv, hbal, hto, hown⟩ := hG
  obtain ⟨hc, hs⟩ := Nat.max_le.mp hm
  by_cases hfee : feeOf (checkState state message) message (valArg message) = 0
  · simp only [transferFromCost, transferFromStip, hfee, ↓reduceIte] at hc hs
    rw [sendOf_zero hfee] at hto
    refine (spec_okFI hfork hst hacc hl hsize' hsel hv hp hb hdep hov hfee hallow hbal hto hc0
      hcB hc10 hcA hc3 hc4 hcF hcT hnrA hnrD hs hc).consequence (fun _ h => h) ?_
    rintro e ⟨hr, h1, h2, h3, h4, -, -⟩
    simp only [transferFromCost, hfee, ↓reduceIte]
    exact ⟨hr, h1, h2, h3, h4, rfl, rfl⟩
  · simp only [transferFromCost, hfee, ↓reduceIte] at hc
    refine (spec_feeFI hfork hst hacc hl hsize' hsel hv hp hb hdep hov hfee hfv hallow hbal hto
      (hown hfee) hc0 hcB hc10 hcA hc3 hc4 hcF hcT hcO hnrA hnrD hc).consequence
      (fun _ h => h) ?_
    rintro e ⟨hr, h1, h2, h3, h4, -, -⟩
    simp only [transferFromCost, hfee, ↓reduceIte]
    exact ⟨hr, h1, h2, h3, h4, rfl, rfl⟩

/-- **transferFrom over the EIP-8037 meter, with enough gas.** From reservoir 0, when the write of
the allowance (if `A ≠ MAX_UINT`, `hnrA`) and the write of `balances[_from]` (`hnrD`) refill
nothing, under `TransferFromGuard` and with at least the larger of `transferFromCost` and
`transferFromStip` gas, the loop over `StateGasMeter`, for any gas bound and message runner,
ends with no error and `gas - transferFromCost` execution gas left. -/
theorem transferFrom_ok_sgm (hG : TransferFromGuard state message)
    (hm : max (transferFromCost fork state message c0 cB c10 cA c3 c4 cF cT cO)
      (transferFromStip fork state message c0 cB c10 cA c3 c4 cF cT) ≤ gas)
    (within : GasMeter.gasHeld m.gas ≤ bound) :
    ∃ s, Evm.runFrame (step fork) (step_decreases fork) bound runChild m within = .ok s ∧
      s.error = none ∧
      s.gas.gasLeft = gas - transferFromCost fork state message c0 cB c10 cA c3 c4 cF cT cO := by
  obtain ⟨s, hs, -, he, -, hg, -⟩ := runFrame_of_specI
    (transferFrom_specI hfork hsize' hsel hdep hc0 hcB hc10 hcA hc3 hc4 hcF hcT hcO hnrA hnrD hG
      hm) start hres within
  exact ⟨s, hs, he, hg⟩

/-- **transferFrom over the EIP-8037 meter: the exact success condition.** From reservoir 0, when
the write of the allowance (if `A ≠ MAX_UINT`, `hnrA`) and the write of `balances[_from]`
(`hnrD`) refill nothing, the loop over `StateGasMeter`, for any gas bound and message runner, ends
with no error if and only if `TransferFromGuard` holds and the gas is at least the larger of
`transferFromCost` and `transferFromStip`. -/
theorem transferFrom_iff_gas_sgm (within : GasMeter.gasHeld m.gas ≤ bound) :
    RunsOkS fork bound runChild m within ↔ TransferFromGuard state message ∧
      max (transferFromCost fork state message c0 cB c10 cA c3 c4 cF cT cO)
        (transferFromStip fork state message c0 cB c10 cA c3 c4 cF cT) ≤ gas := by
  constructor
  · rintro ⟨s, hs, hok⟩
    have hG := (ok_transferFrom_any hfork hsize' hsel hdep start hs hok).1
    have hE : Ends fork (toNat m) (toNat s) :=
      ends_of_specI (transferFrom_specI hfork hsize' hsel hdep hc0 hcB hc10 hcA hc3 hc4 hcF hcT
        hcO hnrA hnrD hG
        (g := gas + max (transferFromCost fork state message c0 cB c10 cA c3 c4 cF cT cO)
          (transferFromStip fork state message c0 cB c10 cA c3 c4 cF cT)) (Nat.le_add_left _ _))
        (at_sh start _) hres hs
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, h⟩ :=
      ok_transferFrom hfork hsize' hsel hdep hc0 hcB hc10 hcA hc3 hc4 hcF hcT hcO start hE hok
    obtain ⟨⟨h4, hv⟩, ⟨hst, hacc⟩, hl, hp, hb, hov, hallow, hfv, hbal, hto, -⟩ := id hG
    by_cases hfee : feeOf (checkState state message) message (valArg message) = 0
    · have hc : okCostF fork state message c0 cB c10 cA c3 c4 cF cT ≤ gas := by
        rcases h with ⟨-, ⟨hc, -⟩, -⟩ | ⟨h0, -⟩
        · exact hc
        · exact absurd hfee h0
      refine ⟨hG, Nat.max_le.mpr ⟨?_, ?_⟩⟩
      · simp only [transferFromCost, hfee, ↓reduceIte]
        exact hc
      · simp only [transferFromStip, hfee, ↓reduceIte]
        refine Nat.le_of_not_lt fun hlt => ?_
        rw [sendOf_zero hfee] at hto
        exact no_ok_stuck_atE (low_transferFrom2 hfork hst hacc hl hsize' hsel hv hp hb hdep hov
          hfee hallow hbal hto hc0 hcB hc10 hcA hc3 hc4 hcF hcT hc hlt) start hE hok
    · have hc : feeCostF fork state message c0 cB c10 cA c3 c4 cF cT cO ≤ gas := by
        rcases h with ⟨h0, -⟩ | ⟨-, -, ⟨hc, -⟩, -⟩
        · exact absurd h0 hfee
        · exact hc
      refine ⟨hG, Nat.max_le.mpr ⟨?_, ?_⟩⟩
      · simp only [transferFromCost, hfee, ↓reduceIte]
        exact hc
      · simp only [transferFromStip, hfee, ↓reduceIte]
        exact Nat.zero_le _
  · rintro ⟨hG, hm⟩
    obtain ⟨s, hs, he, -⟩ := transferFrom_ok_sgm hfork hsize' hsel hdep hc0 hcB hc10 hcA hc3 hc4
      hcF hcT hcO start hres hnrA hnrD hG hm within
    exact ⟨s, hs, he⟩

end

end TransferFrom

end UsdtVerify.Exact
