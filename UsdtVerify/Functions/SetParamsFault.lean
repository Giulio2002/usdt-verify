import UsdtVerify.Functions.SetParamsSpec
import UsdtVerify.Functions.TransferFaults

/-!
# setParams(uint256, uint256): the overflow of `m * 10^d`

Write `m` for argument word 1 and `d` for slot 9 (`decimals`). When `m * 10^d ≥ 2^256` (as
numbers; `10^d` is the EVM word `exp 10 d`), SafeMath's `mul` fails its assert: INVALID at
10802 (`SafeMath.mulFault`), after slot 3 was written (the frame is reverted by the fault).

- `mulCallFault`: from 5919, the read of slot 9, `10 ** d`, and the call of `mul` to INVALID.
- `spec_mulOv`: from pc 0, the owner's `setParams(b, m)` with `b < 20`, `m < 50` and the overflow
  ends in `Faulted (.invalidOpcode 0xfe)`.
-/

namespace UsdtVerify.SetParamsSpec

open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts
open Transfer TransferOk Owner Admin Issue SafeMath SetParams

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate}

/-- At 5919, with `m * 10^d ≥ 2^256`: the read of slot 9, `10 ** d`, and `mul`'s INVALID. -/
theorem mulCallFault (hfork : .berlin ≤ fork) {b m x : U256} {c9 : Bool}
    (hc9 : coldIn substate message.currentTarget 9 = c9)
    (hov : 2 ^ 256 ≤ m.toNat * (exp (0x0a : U256) (storageAt state message.currentTarget 9)).toNat)
    {M : ByteArray} {gas : Nat}
    (hg : 156 + slotCost c9 + 50 * exponentBytes (storageAt state message.currentTarget 9) ≤ gas) :
    Gas.SpecG fork (At CODE message 5919 [m, b, 0x07b6, x] M gas state substate)
      (Faulted (.invalidOpcode 0xfe) (readSlot state message.currentTarget 9)
        (accessSlot substate message.currentTarget 9)) := by
  step pushR 2 (0x1736 : U256)
  step pushR 1 (0x09 : U256)
  step Gas.sloadG hfork (cold := c9) (by code_fact) (by code_fact) hc9 (by gas_ok)
  rw [getStorage_eq]
  step pushR 1 (0x0a : U256)
  step Gas.expLG (Nat.le_trans (by decide) hfork) (by code_fact) (by code_fact) (by gas_ok)
  step dupR 2
  step pushR 2 (0x2a03 : U256)
  step swapR 0
  norm
  step swapR 1
  norm
  step swapR 0
  norm
  step pushR 4 (0xffffffff : U256)
  step binR 0x16 Local.instruction_and
  step jumpR
  at_pc 10755
  exact mulFault (by simp) hov (by gas_ok)

/-- The specification of `setParams(b, m)` by the owner when `m * 10^d` overflows.

Hypotheses: Berlin ≤ fork (Glamsterdam included); a frame that may write, of an existing account `C`;
call data of 4 to 2^256 - 1 bytes with selector 0xc0324c77; no value; the caller is the owner;
`b < 20`, `m < 50`, `m * 10^d ≥ 2^256` (as numbers, `10^d` the EVM word); more than 2300 gas left
at the SSTORE of slot 3, and enough gas.

Then the run ends in INVALID (`Faulted (.invalidOpcode 0xfe)`): the error of the frame is set,
all its gas is consumed, and its state is the one it had before the write of slot 3 was undone
by the caller of the frame. -/
theorem spec_mulOv (hfork : .berlin ≤ fork)
    (hstatic : message.isStatic = false) (hacc : hasAccount state message.currentTarget)
    (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xc0324c77)
    (hv : message.value = 0) (hown : callerWord message = ownerOf state message.currentTarget)
    (hb : (wordArg message.data 0).toNat < 20) (hm : (wordArg message.data 1).toNat < 50)
    (hov : 2 ^ 256 ≤ (wordArg message.data 1).toNat *
      (exp (0x0a : U256) (storageAt state message.currentTarget 9)).toNat)
    {c0 c3 c9 : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hc3 : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget 3 = c3)
    (hc9 : coldIn (accessSlot (accessSlot substate message.currentTarget 0) message.currentTarget 3)
      message.currentTarget 9 = c9)
    {gas : Nat}
    (hstip : 3168 + slotCost c0 + Gas.writeCost fork (originalAt state message.currentTarget 3)
      (storageAt state message.currentTarget 3) (wordArg message.data 0) c3 + slotCost c9 +
      50 * exponentBytes (storageAt state message.currentTarget 9) ≤ gas) :
    Gas.SpecG fork (At CODE message 0 [] .empty gas state substate)
      (Faulted (.invalidOpcode 0xfe)
        (readSlot (writeSlot (readSlot state message.currentTarget 0) message.currentTarget 3
          (wordArg message.data 0)) message.currentTarget 9)
        (accessSlot (storeSub fork (accessSlot substate message.currentTarget 0)
          message.currentTarget 3 (originalAt state message.currentTarget 3)
          (storageAt state message.currentTarget 3) (wordArg message.data 0))
          message.currentTarget 9)) := by
  have hacc0 := hasAccount_readSlot (n := 0) (other := message.currentTarget) hacc
  have h9 : storageAt (writeSlot (readSlot state message.currentTarget 0) message.currentTarget 3
      (wordArg message.data 0)) message.currentTarget 9 = storageAt state message.currentTarget 9 := by
    rw [storageAt_writeSlot_of_ne hacc0 (by decide), storageAt_readSlot]
  have hc9' : coldIn (storeSub fork (accessSlot substate message.currentTarget 0)
      message.currentTarget 3 (originalAt state message.currentTarget 3)
      (storageAt state message.currentTarget 3) (wordArg message.data 0)) message.currentTarget 9 =
      c9 := hc9
  refine Gas.SpecG.seq (toBody hsize hsize' hsel hv (by omega)) ?_
  step ownerOk hfork (mem_CHECKS (by decide)) (by simp) hc0 hown (by gas_ok)
  at_pc 5881
  step test1 (by simp) (by gas_ok)
  step pass (Or.inl ⟨rfl, rfl⟩) (lt_ne (by simpa using hb)) (by simp) (by gas_ok)
  step test2 (by simp) (by gas_ok)
  step pass (Or.inr ⟨rfl, rfl⟩) (lt_ne (by simpa using hm)) (by simp) (by gas_ok)
  step write3 hfork (by simp) hstatic hacc0 hc3 (by gas_ok)
    (by rw [originalAt_readSlot, storageAt_readSlot]; gas_ok)
  rw [originalAt_readSlot, storageAt_readSlot]
  refine mulCallFault hfork hc9' ?_ ?_
  · rw [h9]; exact hov
  · rw [h9]; gas_ok

end UsdtVerify.SetParamsSpec
