import UsdtVerify.Usdt.Exact.Getters
import UsdtVerify.Evm.Dom
import UsdtVerify.Usdt.Complete.TransferFrom

/-!
# Exact success condition of transferFrom, not deprecated

From Berlin, a fresh frame of `CODE` at pc 0 with call data below `2^256` bytes, the selector
0x23b872dd and byte 20 of slot 10 equal to 0 (`hdep`), any gas bound and any message runner.

- `transferFrom_ok_iff`: with the gas of the success path (`transferFromCost`; with a fee of 0
  also `stipCostF`, more than 2300 gas left at the SSTORE of `balances[t]`), the run ends with no
  error if and only if `TransferFromGuard` holds.
- `transferFrom_low`: with less gas than `transferFromCost`, no run ends with no error.
- `transferFrom_mid` (round 26): with at least `transferFromCost` but less than
  `transferFromStip` gas, no run ends with no error: with a fee of 0, the SSTORE of `balances[t]`
  is reached with at most 2300 gas left (EIP-2200).
- `transferFrom_iff_gas` (round 26): for every gas, the run ends with no error if and only if
  `TransferFromGuard` holds and the gas is at least the larger of `transferFromCost` and
  `transferFromStip`.
-/

namespace UsdtVerify.Exact

open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic hiding SpecG
open UsdtVerify.Gas
open Complete Transfer TransferOk TransferFee SafeMath TransferFrom

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate} {bound : Nat} {runChild : MessageRunner fork Nat bound}
  {evm : Evm fork Nat} {gas : Nat}

/-- The cost of the success path of `transferFrom(f, t, v)`: `okCostF` with a fee of 0,
`feeCostF` otherwise. -/
abbrev transferFromCost (fork : Fork) (state : State.TransactionState) (message : Message fork)
    (c0 cB c10 cA c3 c4 cF cT cO : Bool) : Nat :=
  if feeOf (checkState state message) message (valArg message) = 0 then
    okCostF fork state message c0 cB c10 cA c3 c4 cF cT
  else feeCostF fork state message c0 cB c10 cA c3 c4 cF cT cO

/-- The stipend bound of the success path of `transferFrom(f, t, v)`: `stipCostF` with a fee of 0,
none otherwise (the logs after the SSTOREs of the fee path cost more than 2300). -/
abbrev transferFromStip (fork : Fork) (state : State.TransactionState) (message : Message fork)
    (c0 cB c10 cA c3 c4 cF cT : Bool) : Nat :=
  if feeOf (checkState state message) message (valArg message) = 0 then
    stipCostF fork state message c0 cB c10 cA c3 c4 cF cT
  else 0

section

variable (hfork : .berlin ≤ fork) (hsize' : message.data.size < 2 ^ 256)
  (start : At CODE message 0 [] .empty gas state substate evm)
  (within : GasMeter.gasHeld evm.gas ≤ bound)
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
include hfork hsize' start hsel hdep hc0 hcB hc10 hcA hc3 hc4 hcF hcT hcO

theorem transferFrom_comp (s : Evm fork Nat)
    (hs : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) : TransferFromGuard state message := by
  obtain ⟨hst, hacc, hl, hp, hb, hov, hallow, hfv, hbal, hto, -, h⟩ :=
    ok_transferFrom hfork hsize' hsel hdep hc0 hcB hc10 hcA hc3 hc4 hcF hcT hcO start (Ends.run hs)
      hok
  refine ⟨callOk_of_run hfork hsize' start within s hs hok, ⟨hst, hacc⟩, hl, hp, hb, hov, hallow,
    hfv, hbal, hto, fun hfee => ?_⟩
  rcases h with ⟨h0, -⟩ | ⟨-, hown, -⟩
  · exact absurd h0 hfee
  · exact hown

/-- `transferFrom(f, t, v)`, not deprecated, succeeds exactly when `TransferFromGuard` holds, with
the gas of its success path. -/
theorem transferFrom_ok_iff
    (hstip : feeOf (checkState state message) message (valArg message) = 0 →
      stipCostF fork state message c0 cB c10 cA c3 c4 cF cT ≤ gas)
    (hg : transferFromCost fork state message c0 cB c10 cA c3 c4 cF cT cO ≤ gas) :
    RunsOk fork bound runChild evm within ↔ TransferFromGuard state message := by
  refine runsOk_iff (Q := fun e => e.error = none)
    (fun ⟨⟨h4, hv⟩, ⟨hst, hacc⟩, hl, hp, hb, hov, hallow, hfv, hbal, hto, hown⟩ => ?_)
    (fun _ h => h) start within
    (transferFrom_comp hfork hsize' start within hsel hdep hc0 hcB hc10 hcA hc3 hc4 hcF hcT hcO)
  by_cases hfee : feeOf (checkState state message) message (valArg message) = 0
  · simp only [transferFromCost, hfee, ↓reduceIte] at hg
    rw [sendOf_zero hfee] at hto
    exact (spec_ok hfork hst hacc hl hsize' hsel hv hp hb hdep hov hfee hallow hbal hto hc0 hcB
      hc10 hcA hc3 hc4 hcF hcT (hstip hfee) hg).consequence (fun _ h => h) halted_false_ok
  · simp only [transferFromCost, hfee, ↓reduceIte] at hg
    exact (spec_feeF hfork hst hacc hl hsize' hsel hv hp hb hdep hov hfee hfv hallow hbal hto
      (hown hfee) hc0 hcB hc10 hcA hc3 hc4 hcF hcT hcO hg).consequence (fun _ h => h)
      halted_false_ok

/-- `transferFrom` over the EIP-8037 meter at any reservoir, with refills allowed (round 42): under
`TransferFromGuard` and the gas of `transferFrom_ok_iff`, the loop over `StateGasMeter` from a frame `m` whose
`toNat` is the fresh frame, for any gas bound and message runner, ends with no error. -/
theorem transferFrom_ok_dom
    (hstip : feeOf (checkState state message) message (valArg message) = 0 →
      stipCostF fork state message c0 cB c10 cA c3 c4 cF cT ≤ gas)
    (hg : transferFromCost fork state message c0 cB c10 cA c3 c4 cF cT cO ≤ gas)
    {m : Evm fork StateGasMeter} (hm : evm = Meter.toNat m) {boundS : Nat}
    {runS : MessageRunner fork StateGasMeter boundS} (withinS : GasMeter.gasHeld m.gas ≤ boundS)
    (hG : TransferFromGuard state message) : Shadow.RunsOkS fork boundS runS m withinS := by
  have key : ∃ Q : Evm fork Nat → Prop,
      SpecG fork (At CODE message 0 [] .empty gas state substate) Q ∧
        ∀ e, Q e → e.error = none := by
    obtain ⟨⟨h4, hv⟩, ⟨hst, hacc⟩, hl, hp, hb, hov, hallow, hfv, hbal, hto, hown⟩ := hG
    refine ⟨fun e => e.error = none, ?_, fun _ h => h⟩
    by_cases hfee : feeOf (checkState state message) message (valArg message) = 0
    · simp only [transferFromCost, hfee, ↓reduceIte] at hg
      rw [sendOf_zero hfee] at hto
      exact (spec_ok hfork hst hacc hl hsize' hsel hv hp hb hdep hov hfee hallow hbal hto hc0 hcB
        hc10 hcA hc3 hc4 hcF hcT (hstip hfee) hg).consequence (fun _ h => h) halted_false_ok
    · simp only [transferFromCost, hfee, ↓reduceIte] at hg
      exact (spec_feeF hfork hst hacc hl hsize' hsel hv hp hb hdep hov hfee hfv hallow hbal hto
        (hown hfee) hc0 hcB hc10 hcA hc3 hc4 hcF hcT hcO hg).consequence (fun _ h => h)
        halted_false_ok
  obtain ⟨Q, h, hQ⟩ := key
  exact Shadow.runsOkS_of_specG hfork h hQ (hm ▸ start) withinS


theorem transferFrom_low
    (hg : gas < transferFromCost fork state message c0 cB c10 cA c3 c4 cF cT cO) :
    ¬ RunsOk fork bound runChild evm within := by
  have hcomp := transferFrom_comp (runChild := runChild) hfork hsize' start within hsel hdep hc0
    hcB hc10 hcA hc3 hc4 hcF hcT hcO
  by_cases hfee : feeOf (checkState state message) message (valArg message) = 0
  · simp only [transferFromCost, hfee, ↓reduceIte] at hg
    exact not_runsOk_low2 hg
      (fun ⟨⟨h4, hv⟩, ⟨hst, hacc⟩, hl, hp, hb, hov, hallow, hfv, hbal, hto, hown⟩ _ =>
        spec_ok hfork hst hacc hl hsize' hsel hv hp hb hdep hov hfee hallow hbal
          (by rw [sendOf_zero hfee] at hto; exact hto) hc0 hcB hc10 hcA hc3 hc4 hcF hcT)
      start within hcomp
  · simp only [transferFromCost, hfee, ↓reduceIte] at hg
    exact not_runsOk_low (Nat.le_refl _) hg
      (fun ⟨⟨h4, hv⟩, ⟨hst, hacc⟩, hl, hp, hb, hov, hallow, hfv, hbal, hto, hown⟩ _ =>
        spec_feeF hfork hst hacc hl hsize' hsel hv hp hb hdep hov hfee hfv hallow hbal hto
          (hown hfee) hc0 hcB hc10 hcA hc3 hc4 hcF hcT hcO)
      start within hcomp

theorem transferFrom_mid
    (hg : transferFromCost fork state message c0 cB c10 cA c3 c4 cF cT cO ≤ gas)
    (hlt : gas < transferFromStip fork state message c0 cB c10 cA c3 c4 cF cT) :
    ¬ RunsOk fork bound runChild evm within := by
  refine not_runsOk_stuck
    (fun ⟨⟨h4, hv⟩, ⟨hst, hacc⟩, hl, hp, hb, hov, hallow, hfv, hbal, hto, hown⟩ => ?_) start
    within
    (transferFrom_comp hfork hsize' start within hsel hdep hc0 hcB hc10 hcA hc3 hc4 hcF hcT hcO)
  by_cases hfee : feeOf (checkState state message) message (valArg message) = 0
  · simp only [transferFromCost, transferFromStip, hfee, ↓reduceIte] at hg hlt
    rw [sendOf_zero hfee] at hto
    exact low_transferFrom2 hfork hst hacc hl hsize' hsel hv hp hb hdep hov hfee hallow hbal hto
      hc0 hcB hc10 hcA hc3 hc4 hcF hcT hg hlt
  · simp only [transferFromStip, hfee, ↓reduceIte] at hlt
    omega

/-- `transferFrom(f, t, v)`, not deprecated, succeeds exactly when `TransferFromGuard` holds and
the gas is at least the larger of `transferFromCost` and `transferFromStip`. -/
theorem transferFrom_iff_gas :
    RunsOk fork bound runChild evm within ↔ TransferFromGuard state message ∧
      max (transferFromCost fork state message c0 cB c10 cA c3 c4 cF cT cO)
        (transferFromStip fork state message c0 cB c10 cA c3 c4 cF cT) ≤ gas :=
  iff_max (fun hg hs => transferFrom_ok_iff hfork hsize' start within hsel hdep hc0 hcB hc10 hcA
      hc3 hc4 hcF hcT hcO
      (fun hfee => by simpa only [transferFromStip, hfee, ↓reduceIte] using hs) hg)
    (transferFrom_low hfork hsize' start within hsel hdep hc0 hcB hc10 hcA hc3 hc4 hcF hcT hcO)
    (transferFrom_mid hfork hsize' start within hsel hdep hc0 hcB hc10 hcA hc3 hc4 hcF hcT hcO)
    (fun h => of_runsOk h (transferFrom_comp hfork hsize' start within hsel hdep hc0 hcB hc10 hcA
      hc3 hc4 hcF hcT hcO))

end

end UsdtVerify.Exact
