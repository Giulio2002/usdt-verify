import UsdtVerify.Functions.TransferSuccess
import EthLib.Execution.Proofs.Evm.Logic.Fault

/-!
# SafeMath asserts that fail, and `transfer` with an insufficient balance

SafeMath's `assert` compiles to `JUMPI` over `INVALID` (0xfe). With EthLib's rule for INVALID
(#1250, `invalid_fe`), a failed assert halts the frame exceptionally: `Faulted`, with the error
`invalidOpcode 0xfe`, no output, no gas left, and the state and substate it had (the caller
discards them).

- `subFault`: `sub(a, b)` at 10976 with `a < b`.
- `addFault`: `add(a, b)` at 11001 with `a + b ≥ 2^256`.
- `spec_low`: `transfer(to, v)` with `balances[msg.sender] < v`.
-/

namespace UsdtVerify.SafeMath

open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate}

/-- `sub(a, b)` at 10976 with `a < b` fails its assert: INVALID at 10989, after 35 gas. -/
theorem subFault {a b ret : U256} {rest : List U256} (hrest : rest.length ≤ 20)
    (hlt : a.toNat < b.toNat) {gas : Nat} (hg : 35 ≤ gas) {M : ByteArray} :
    Gas.SpecG fork (At CODE message 10976 (b :: a :: ret :: rest) M gas state substate)
      (Faulted (.invalidOpcode 0xfe) state substate) := by
  have hgt : greaterThan b a = 1 := by simp [greaterThan, hlt]
  step jumpdestR
  step pushR 1 (0 : U256)
  step dupR 2
  step dupR 2
  step binR 0x11 Local.instruction_gt
  step unR 0x15 instruction_iszero
  step unR 0x15 instruction_iszero
  step unR 0x15 instruction_iszero
  step pushR 2 (0x2aee : U256)
  step jumpi0R (by rw [hgt]; decide)
  exact Gas.invalid_feG (by code_fact) (by code_fact)

/-- `add(a, b)` at 11001 with `a + b ≥ 2^256` fails its assert: INVALID at 11020, after 52 gas. -/
theorem addFault {a b ret : U256} {rest : List U256} (hrest : rest.length ≤ 20)
    (hov : 2 ^ 256 ≤ a.toNat + b.toNat) {gas : Nat} (hg : 52 ≤ gas) {M : ByteArray} :
    Gas.SpecG fork (At CODE message 11001 (b :: a :: ret :: rest) M gas state substate)
      (Faulted (.invalidOpcode 0xfe) state substate) := by
  have hlt : lessThan (add a b) a = 1 := by
    have h1 := a.isLt
    have h2 := b.isLt
    have : (add a b).toNat = a.toNat + b.toNat - 2 ^ 256 := by
      simp only [add, BitVec.toNat_add]
      rw [Nat.mod_eq_sub_mod hov, Nat.mod_eq_of_lt (by omega)]
    simp only [lessThan, this]
    rw [if_pos (by omega)]
  step jumpdestR
  step pushR 1 (0 : U256)
  step dupR 0
  step dupR 2
  step dupR 4
  step binR 0x01 instruction_add
  step swapR 0
  norm
  step popR
  step dupR 3
  step dupR 1
  step binR 0x10 Local.instruction_lt
  step unR 0x15 instruction_iszero
  step unR 0x15 instruction_iszero
  step unR 0x15 instruction_iszero
  step pushR 2 (0x2b0d : U256)
  step jumpi0R (by rw [hlt]; decide)
  exact Gas.invalid_feG (by code_fact) (by code_fact)

end UsdtVerify.SafeMath

namespace UsdtVerify.TransferOk

open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts
open Transfer SafeMath

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate}

/-- From 9883, a `transfer` whose sender's balance is below `v` faults at the `sub` of the debit
(after the fee and `sendAmount = v - fee`, which need no overflow and `fee ≤ v`). -/
theorem bodyLow (hfork : .berlin ≤ fork) (hlong : 68 ≤ message.data.size)
    (hsz : message.data.size < 2 ^ 256)
    {v a sel : U256} {M : ByteArray} (hM : M.size = 96)
    (hov : v.toNat * (storageAt state message.currentTarget 3).toNat < 2 ^ 256)
    (hfv : (feeOf state message v).toNat ≤ v.toNat)
    (hlow : (balS state message).toNat < v.toNat)
    {c3 c4 cS : Bool} (hc3 : coldIn substate message.currentTarget 3 = c3)
    (hc4 : coldIn (accessSlot substate message.currentTarget 3) message.currentTarget 4 = c4)
    (hcS : coldIn (accessSlot (accessSlot substate message.currentTarget 3) message.currentTarget 4)
      message.currentTarget (senderSlot message) = cS)
    {gas : Nat}
    (hg : 497 + slotCost c3 + slotCost c4 + slotCost cS + mulCost v +
      capCost (rawFee state message v) (storageAt state message.currentTarget 4) ≤ gas) :
    Gas.SpecG fork (At CODE message 9883 [v, a, 0x1699, v, a, 0x078a, sel] M gas state substate)
      (Faulted (.invalidOpcode 0xfe) (reads3 state message) (access3 substate message)) := by
  simp only [rawFee, feeOf, balS, reads3, access3] at hg hfv hlow ⊢
  step payloadOk hlong hsz (by simp) (by gas_ok)
  step feeCall hfork (by simp) hc3 (by gas_ok)
  step mulBlock (by simp) (by valid_dest) hov (by gas_ok)
  at_pc 9937
  step divCall (by simp) (by gas_ok)
  step divBlock (by simp) (by valid_dest) (by decide) (by gas_ok)
  at_pc 9951
  step capBlock hfork (by simp) hc4 (by simp only [storageAt_readSlot]; gas_ok)
  simp only [storageAt_readSlot]
  step sendCall (by simp) (by gas_ok)
  step subBlock (by simp) (by valid_dest) hfv (by gas_ok)
  at_pc 9988
  step debitCall hfork (by simp) hcS (by gas_ok) hM
  simp only [storageAt_readSlot]
  exact subFault (by simp) hlow (by gas_ok)

/-- The gas a `transfer` with an insufficient balance needs to reach its INVALID. -/
abbrev lowCost (state : State.TransactionState) (message : Message fork)
    (c0 cB c10 c3 c4 cS : Bool) : Nat :=
  PRE_COST + slotCost c0 + slotCost cB + slotCost c10 + (497 + slotCost c3 + slotCost c4 +
    slotCost cS + mulCost (wordArg message.data 1) +
    capCost (rawFee (shortState state message) message (wordArg message.data 1))
      (storageAt (shortState state message) message.currentTarget 4))

/-- The specification of `transfer(to, v)` when the sender's balance is below `v`.

Hypotheses: as for `spec_ok` up to the fee: call data of 68 to 2^256 - 1 bytes with selector
0xa9059cbb, no value, not paused, caller not blacklisted, not deprecated, `v * basisPointsRate`
does not overflow, the fee is at most `v`; then `balances[msg.sender] < v`, and enough gas to reach
the assert (`lowCost ≤ gas`; with less, the frame runs out of gas instead).

Then the frame halts exceptionally with INVALID (error `invalidOpcode 0xfe`), no output, no gas
left, in the state after the reads of slots 0, the blacklist slot, 10, 3, 4 and the sender's
balance (nothing written). The caller discards that state. -/
theorem spec_low (hfork : .berlin ≤ fork)
    (hlong : 68 ≤ message.data.size) (hsz : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0xa9059cbb) (hv : message.value = 0)
    (hnp : byte20 (storageAt state message.currentTarget 0) = 0)
    (hnb : (storageAt state message.currentTarget (blackSlot message)).toNat % 256 = 0)
    (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    (hov : (wordArg message.data 1).toNat *
      (storageAt (shortState state message) message.currentTarget 3).toNat < 2 ^ 256)
    (hfv : (feeOf (shortState state message) message (wordArg message.data 1)).toNat ≤
      (wordArg message.data 1).toNat)
    (hlow : (balS (shortState state message) message).toNat < (wordArg message.data 1).toNat)
    {c0 cB c10 c3 c4 cS : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hcB : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget
      (blackSlot message) = cB)
    (hc10 : coldIn (accessSlot (accessSlot substate message.currentTarget 0) message.currentTarget
      (blackSlot message)) message.currentTarget 10 = c10)
    (hc3 : coldIn (shortSubstate substate message) message.currentTarget 3 = c3)
    (hc4 : coldIn (accessSlot (shortSubstate substate message) message.currentTarget 3)
      message.currentTarget 4 = c4)
    (hcS : coldIn (accessSlot (accessSlot (shortSubstate substate message) message.currentTarget 3)
      message.currentTarget 4) message.currentTarget (senderSlot message) = cS)
    {gas : Nat} (hg : lowCost state message c0 cB c10 c3 c4 cS ≤ gas) :
    Gas.SpecG fork (At CODE message 0 [] .empty gas state substate)
      (Faulted (.invalidOpcode 0xfe) (reads3 (shortState state message) message)
        (access3 (shortSubstate substate message) message)) := by
  have hB := bodyLow (state := shortState state message) (substate := shortSubstate substate message)
    (sel := BitVec.ofNat 256 (selector message.data)) (a := addrArg message.data 0)
    (gas := gas - (PRE_COST + slotCost c0 + slotCost cB + slotCost c10))
    hfork hlong hsz (size_MEMK (callerKey message) 6) hov hfv hlow hc3 hc4 hcS
    (Nat.le_sub_of_add_le (by rw [Nat.add_comm]; exact hg))
  have hpre : PRE_COST + slotCost c0 + slotCost cB + slotCost c10 ≤ gas :=
    Nat.le_trans (Nat.le_add_right _ _) hg
  clear hov hfv hlow hg
  simp only [PRE_COST] at hpre hB
  have ht : tested (BitVec.ofNat 256 (selector message.data)) ENTRIES = 22 := by
    rw [hsel]; decide
  have hb : branch (BitVec.ofNat 256 (selector message.data)) 54 (entrySize 4 2) ENTRIES =
      1866 := by
    rw [hsel]; decide
  have h1 := dispatch (state := state) (substate := substate) (by omega) hsz (gas := gas)
    (by rw [ht]; gas_ok)
  rw [ht, hb] at h1
  refine Gas.SpecG.seq h1 ?_
  step entry hv (by gas_ok)
  step notPaused hfork (by simp) hnp hc0 (by gas_ok)
  step blackLookup hfork (by simp) hcB (by gas_ok)
  step jumpiR (blackTest_ne (by rw [storageAt_readSlot]; exact hnb))
  step repc (pc' := 5481) (by decide)
  step depInline hfork (by simp) (by rw [storageAt_readSlot, storageAt_readSlot]; exact hdep) hc10
    (by gas_ok)
  step toBasic (by gas_ok)
  step Gas.reshapeG (g' := gas - (1034 + slotCost c0 + slotCost cB + slotCost c10)) rfl rfl (by gas_ok)
  exact hB

/-- The loop of the interpreter runs a `transfer` call whose sender's balance is below `v` to the
fault of `spec_low` (INVALID, no output, no gas left). It holds for every bound on the gas of
messages and every runner of messages. -/
theorem runFrame_low (hfork : .berlin ≤ fork)
    (hlong : 68 ≤ message.data.size) (hsz : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0xa9059cbb) (hv : message.value = 0)
    (hnp : byte20 (storageAt state message.currentTarget 0) = 0)
    (hnb : (storageAt state message.currentTarget (blackSlot message)).toNat % 256 = 0)
    (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    (hov : (wordArg message.data 1).toNat *
      (storageAt (shortState state message) message.currentTarget 3).toNat < 2 ^ 256)
    (hfv : (feeOf (shortState state message) message (wordArg message.data 1)).toNat ≤
      (wordArg message.data 1).toNat)
    (hlow : (balS (shortState state message) message).toNat < (wordArg message.data 1).toNat)
    {c0 cB c10 c3 c4 cS : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hcB : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget
      (blackSlot message) = cB)
    (hc10 : coldIn (accessSlot (accessSlot substate message.currentTarget 0) message.currentTarget
      (blackSlot message)) message.currentTarget 10 = c10)
    (hc3 : coldIn (shortSubstate substate message) message.currentTarget 3 = c3)
    (hc4 : coldIn (accessSlot (shortSubstate substate message) message.currentTarget 3)
      message.currentTarget 4 = c4)
    (hcS : coldIn (accessSlot (accessSlot (shortSubstate substate message) message.currentTarget 3)
      message.currentTarget 4) message.currentTarget (senderSlot message) = cS)
    {gas : Nat} (hg : lowCost state message c0 cB c10 c3 c4 cS ≤ gas) {bound : Nat}
    {runChild : MessageRunner fork Nat bound} {evm : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    ∃ stopped, runFrame (step fork) (step_decreases fork) bound runChild evm within =
      .ok stopped ∧
      Faulted (.invalidOpcode 0xfe) (reads3 (shortState state message) message)
        (access3 (shortSubstate substate message) message) stopped :=
  (spec_low hfork hlong hsz hsel hv hnp hnb hdep hov hfv hlow hc0 hcB hc10 hc3 hc4 hcS hg).runFrame
    start within

end UsdtVerify.TransferOk
