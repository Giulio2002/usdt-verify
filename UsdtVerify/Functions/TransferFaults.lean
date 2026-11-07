import UsdtVerify.Functions.TransferFault
import UsdtVerify.Functions.TransferFeeBody

/-!
# transfer(address,uint256): the failed SafeMath asserts (INVALID)

Each SafeMath assert compiles to `JUMPI` over INVALID (0xfe); a failed one halts the frame with
EthLib's `Faulted (.invalidOpcode 0xfe)`: no output, no gas left, and the state and substate
it had (the caller discards them). Besides `spec_low` (TransferFault.lean), the asserts of
`transfer` that can fail are:

- `spec_mulOv`: `mul(v, basisPointsRate)` overflows (INVALID at 10802, `mulFault`);
- `spec_feeGt`: the fee is above `v` (`sub(v, fee)`, INVALID at 10989);
- `spec_toOv`: the recipient's balance plus `sendAmount` overflows (`add`, INVALID at 11020);
  for every fee, after the sender's write;
- `spec_ownerOv`: with a fee above 0, the owner's balance plus the fee overflows (`add`), after
  the recipient's write.

`pre` is the common prefix from pc 0 to BasicToken's `transfer` at 9883.
-/

namespace UsdtVerify.SafeMath

open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate}

/-- With an overflow, the product divided by the first factor is not the second. -/
theorem div_mul_ne {a b : U256} (hov : 2 ^ 256 ≤ a.toNat * b.toNat) : div (mul a b) a ≠ b := by
  have ha : a ≠ 0 := by
    intro h
    subst h
    simp at hov
  intro h
  have h2 := congrArg BitVec.toNat h
  simp only [div, ha, ite_false, mul, BitVec.toNat_mul] at h2
  have h3 := Nat.div_mul_le_self (a.toNat * b.toNat % 2 ^ 256) a.toNat
  have h4 := Nat.mod_lt (a.toNat * b.toNat) (show 0 < 2 ^ 256 by decide)
  have h5 : a.toNat * b.toNat % 2 ^ 256 / a.toNat < 2 ^ 256 :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) h4
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h5] at h2
  rw [h2] at h3
  have h6 : b.toNat * a.toNat = a.toNat * b.toNat := Nat.mul_comm _ _
  omega

/-- `mul(a, b)` at 10755 with `a * b ≥ 2^256` fails its assert: INVALID at 10802, after 108 gas. -/
theorem mulFault {a b ret : U256} {rest : List U256} (hrest : rest.length ≤ 20)
    (hov : 2 ^ 256 ≤ a.toNat * b.toNat) {gas : Nat} (hg : 108 ≤ gas) {M : ByteArray} :
    Spec fork (At CODE message 10755 (b :: a :: ret :: rest) M gas state substate)
      (Faulted (.invalidOpcode 0xfe) state substate) := by
  have ha : a ≠ 0 := by
    intro h
    subst h
    simp at hov
  have hq := div_mul_ne hov
  step jumpdestR
  step pushR 1 (0 : U256)
  step dupR 0
  step pushR 1 (0 : U256)
  step dupR 4
  step binR 0x14 instruction_eq
  step unR 0x15 instruction_iszero
  step pushR 2 (0x2a18 : U256)
  step jumpiR (by simp [equal, isZero]; exact ha)
  at_pc 10776
  step jumpdestR
  step dupR 2
  step dupR 4
  step binR 0x02 Local.instruction_mul
  step swapR 0
  norm
  step popR
  step dupR 2
  step dupR 4
  step dupR 2
  step dupR 1
  step unR 0x15 instruction_iszero
  step unR 0x15 instruction_iszero
  step pushR 2 (0x2a29 : U256)
  step jumpiR (by simp [isZero]; exact ha)
  at_pc 10793
  step jumpdestR
  step binR 0x04 Local.instruction_div
  step binR 0x14 instruction_eq
  step unR 0x15 instruction_iszero
  step unR 0x15 instruction_iszero
  step pushR 2 (0x2a33 : U256)
  step jumpi0R (by simp [hq, equal, isZero])
  exact invalid_fe (by code_fact) (by code_fact)

end UsdtVerify.SafeMath

namespace UsdtVerify.TransferOk

open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts
open Transfer SafeMath TransferFee TransferFrom

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate}

/-- The stack at 9883 for `transfer(to, v)`. -/
abbrev bodyStack (message : Message fork) : List U256 :=
  [wordArg message.data 1, addrArg message.data 0, 0x1699, wordArg message.data 1,
    addrArg message.data 0, 0x078a, BitVec.ofNat 256 (selector message.data)]

/-- From pc 0, a `transfer` call that passes the checks (no value, not paused, caller not
blacklisted, not deprecated) reaches BasicToken's `transfer` at 9883. -/
theorem pre (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsz : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0xa9059cbb) (hv : message.value = 0)
    (hnp : byte20 (storageAt state message.currentTarget 0) = 0)
    (hnb : (storageAt state message.currentTarget (blackSlot message)).toNat % 256 = 0)
    (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    {c0 cB c10 : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hcB : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget
      (blackSlot message) = cB)
    (hc10 : coldIn (accessSlot (accessSlot substate message.currentTarget 0) message.currentTarget
      (blackSlot message)) message.currentTarget 10 = c10)
    {gas : Nat} (hg : PRE_COST + slotCost c0 + slotCost cB + slotCost c10 ≤ gas) :
    Hoare fork (At CODE message 0 [] .empty gas state substate)
      (At CODE message 9883 (bodyStack message) (MEMK (callerKey message) 6)
        (gas - (PRE_COST + slotCost c0 + slotCost cB + slotCost c10))
        (shortState state message) (shortSubstate substate message)) := by
  simp only [PRE_COST] at hg ⊢
  have ht : tested (BitVec.ofNat 256 (selector message.data)) ENTRIES = 22 := by
    rw [hsel]; decide
  have hb : branch (BitVec.ofNat 256 (selector message.data)) 54 (entrySize 4 2) ENTRIES =
      1866 := by
    rw [hsel]; decide
  have h1 := dispatch (state := state) (substate := substate) hsize hsz (gas := gas)
    (by rw [ht]; gas_ok)
  rw [ht, hb] at h1
  refine Triple.seq h1 ?_
  step entry hv (by gas_ok)
  step notPaused hfork (by simp) hnp hc0 (by gas_ok)
  step blackLookup hfork (by simp) hcB (by gas_ok)
  step jumpiR (blackTest_ne (by rw [storageAt_readSlot]; exact hnb))
  step repc (pc' := 5481) (by decide)
  step depInline hfork (by simp) (by rw [storageAt_readSlot, storageAt_readSlot]; exact hdep) hc10
    (by gas_ok)
  step toBasic (by gas_ok)
  exact reshape rfl rfl (by gas_ok)

/-- From 9883, `mul(v, basisPointsRate)` overflows: INVALID after the read of slot 3. -/
theorem bodyMulOv (hlong : 68 ≤ message.data.size) (hsz : message.data.size < 2 ^ 256)
    (hfork : .berlin ≤ fork) {v a sel : U256} {M : ByteArray}
    (hov : 2 ^ 256 ≤ v.toNat * (storageAt state message.currentTarget 3).toNat)
    {c3 : Bool} (hc3 : coldIn substate message.currentTarget 3 = c3)
    {gas : Nat} (hg : 204 + slotCost c3 ≤ gas) :
    Spec fork (At CODE message 9883 [v, a, 0x1699, v, a, 0x078a, sel] M gas state substate)
      (Faulted (.invalidOpcode 0xfe) (readSlot state message.currentTarget 3)
        (accessSlot substate message.currentTarget 3)) := by
  step payloadOk hlong hsz (by simp) (by gas_ok)
  step feeCall hfork (by simp) hc3 (by gas_ok)
  exact mulFault (by simp) hov (by gas_ok)

/-- From 9883, a fee above `v`: INVALID at the `sub(v, fee)` of `sendAmount`. -/
theorem bodyFeeGt (hlong : 68 ≤ message.data.size) (hsz : message.data.size < 2 ^ 256)
    (hfork : .berlin ≤ fork) {v a sel : U256} {M : ByteArray}
    (hov : v.toNat * (storageAt state message.currentTarget 3).toNat < 2 ^ 256)
    (hgt : v.toNat < (feeOf state message v).toNat)
    {c3 c4 : Bool} (hc3 : coldIn substate message.currentTarget 3 = c3)
    (hc4 : coldIn (accessSlot substate message.currentTarget 3) message.currentTarget 4 = c4)
    {gas : Nat}
    (hg : 299 + slotCost c3 + slotCost c4 + mulCost v +
      capCost (rawFee state message v) (storageAt state message.currentTarget 4) ≤ gas) :
    Spec fork (At CODE message 9883 [v, a, 0x1699, v, a, 0x078a, sel] M gas state substate)
      (Faulted (.invalidOpcode 0xfe)
        (readSlot (readSlot state message.currentTarget 3) message.currentTarget 4)
        (accessSlot (accessSlot substate message.currentTarget 3) message.currentTarget 4)) := by
  simp only [rawFee, feeOf] at hg hgt ⊢
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
  exact subFault (by simp) hgt (by gas_ok)

/-- The state at the recipient's `add`: the sender written, the recipient's slot read. -/
abbrev toOvState (state : State.TransactionState) (message : Message fork) (v a : U256) :
    State.TransactionState :=
  readSlot (debited state message v) message.currentTarget (recipientSlot a)

/-- The substate at the recipient's `add`. -/
abbrev toOvSub (fork : Fork) (substate : Substate) (state : State.TransactionState)
    (message : Message fork) (v a : U256) : Substate :=
  accessSlot (debitedSub fork substate state message v) message.currentTarget (recipientSlot a)

/-- From 9883, for any fee `≤ v`, the recipient's balance (read after the sender's write) plus
`sendAmount = v - fee` overflows: INVALID at the `add`, after the sender's write. -/
theorem bodyToOv (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    (hlong : 68 ≤ message.data.size) (hsz : message.data.size < 2 ^ 256)
    (hstatic : message.isStatic = false) (hacc : hasAccount state message.currentTarget)
    {v a sel : U256} {M : ByteArray} (hM : M.size = 96)
    (hov : v.toNat * (storageAt state message.currentTarget 3).toNat < 2 ^ 256)
    (hfv : (feeOf state message v).toNat ≤ v.toNat)
    (hbal : v.toNat ≤ (balS state message).toNat)
    (hto : 2 ^ 256 ≤ (balT state message v a).toNat + (sendOf state message v).toNat)
    {c3 c4 cS cT : Bool} (hc3 : coldIn substate message.currentTarget 3 = c3)
    (hc4 : coldIn (accessSlot substate message.currentTarget 3) message.currentTarget 4 = c4)
    (hcS : coldIn (accessSlot (accessSlot substate message.currentTarget 3) message.currentTarget 4)
      message.currentTarget (senderSlot message) = cS)
    (hcT : coldIn (access3 substate message) message.currentTarget (recipientSlot a) = cT)
    {gas : Nat}
    (hstip : 530 + slotCost c3 + slotCost c4 + slotCost cS + mulCost v +
      capCost (rawFee state message v) (storageAt state message.currentTarget 4) + 2400 ≤ gas)
    (hg : 808 + readCost c3 c4 cS cT + mulCost v +
      capCost (rawFee state message v) (storageAt state message.currentTarget 4) +
      debitCost fork state message v ≤ gas) :
    Spec fork (At CODE message 9883 [v, a, 0x1699, v, a, 0x078a, sel] M gas state substate)
      (Faulted (.invalidOpcode 0xfe) (toOvState state message v a)
        (toOvSub fork substate state message v a)) := by
  have hacc3 : hasAccount (reads3 state message) message.currentTarget :=
    hasAccount_readSlot (hasAccount_readSlot (hasAccount_readSlot hacc))
  simp only [readCost, debitCost, rawFee, feeOf, balS, balT, debited, reads3, sendOf, toOvState,
    toOvSub, debitedSub, access3] at hstip hg hfv hbal hto hcT hacc3 ⊢
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
  step subBlock (by simp) (by valid_dest) hbal (by gas_ok)
  at_pc 10072
  step debitStore hfork hglam (by simp) hstatic hacc3 (coldIn_accessSlot_self _ _ _) (by gas_ok)
    (by simp only [storageAt_readSlot, originalAt_readSlot]; gas_ok) (size_mapMem hM _ _)
  simp only [storageAt_readSlot, originalAt_readSlot]
  step creditCall hfork (by simp) (cT := cT) (by rw [coldIn_storeSub]; exact hcT) (by gas_ok)
    (size_mapMem (size_mapMem hM _ _) _ _)
  exact addFault (by simp) hto (by gas_ok)

/-- The state at the owner's `add`: after the recipient's write, slot 0 and the owner's slot read. -/
abbrev ownerOvState (state : State.TransactionState) (message : Message fork) (v a : U256) :
    State.TransactionState :=
  readSlot (readSlot (creditedFee state message v a) message.currentTarget 0)
    message.currentTarget (ownerSlot (ownerWord state message v a))

/-- The substate at the owner's `add`. -/
abbrev ownerOvSub (fork : Fork) (substate : Substate) (state : State.TransactionState)
    (message : Message fork) (v a : U256) : Substate :=
  accessSlot (accessSlot (creditedSubFee fork substate state message v a) message.currentTarget 0)
    message.currentTarget (ownerSlot (ownerWord state message v a))

/-- From 9883, with a fee above 0 and the transfer to `_to` done, the owner's balance (read after
the recipient's write) plus the fee overflows: INVALID at the `add` of the owner's credit. -/
theorem bodyOwnerOv (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    (hlong : 68 ≤ message.data.size) (hsz : message.data.size < 2 ^ 256)
    (hstatic : message.isStatic = false) (hacc : hasAccount state message.currentTarget)
    {v a sel : U256} {M : ByteArray} (hM : M.size = 96)
    (hov : v.toNat * (storageAt state message.currentTarget 3).toNat < 2 ^ 256)
    (hfee : feeOf state message v ≠ 0)
    (hfv : (feeOf state message v).toNat ≤ v.toNat)
    (hbal : v.toNat ≤ (balS state message).toNat)
    (hto : (balT state message v a).toNat + (sendOf state message v).toNat < 2 ^ 256)
    (hown : 2 ^ 256 ≤ (balO state message v a).toNat + (feeOf state message v).toNat)
    (hc0 : coldIn substate message.currentTarget 0 = false)
    {c3 c4 cS cT cO : Bool} (hc3 : coldIn substate message.currentTarget 3 = c3)
    (hc4 : coldIn (accessSlot substate message.currentTarget 3) message.currentTarget 4 = c4)
    (hcS : coldIn (accessSlot (accessSlot substate message.currentTarget 3) message.currentTarget 4)
      message.currentTarget (senderSlot message) = cS)
    (hcT : coldIn (access3 substate message) message.currentTarget (recipientSlot a) = cT)
    (hcO : coldIn (creditedSubFee fork substate state message v a) message.currentTarget
      (ownerSlot (ownerWord state message v a)) = cO)
    {gas : Nat}
    (hstip : 964 + readCost c3 c4 cS cT + mulCost v +
      capCost (rawFee state message v) (storageAt state message.currentTarget 4) +
      debitCost fork state message v + creditCostFee fork state message v a + 2401 ≤ gas)
    (hg : 964 + readCost c3 c4 cS cT + mulCost v +
      capCost (rawFee state message v) (storageAt state message.currentTarget 4) +
      debitCost fork state message v + creditCostFee fork state message v a + 313 +
      slotCost cO ≤ gas) :
    Spec fork (At CODE message 9883 [v, a, 0x1699, v, a, 0x078a, sel] M gas state substate)
      (Faulted (.invalidOpcode 0xfe) (ownerOvState state message v a)
        (ownerOvSub fork substate state message v a)) := by
  have hw : coldIn (creditedSubFee fork substate state message v a) message.currentTarget 0 =
      false :=
    coldIn_storeSub_false (coldIn_accessSlot_false (coldIn_storeSub_false
      (coldIn_accessSlot_false (coldIn_accessSlot_false (coldIn_accessSlot_false hc0)))))
  have hA := feeHead (sel := sel) hfork hglam hlong hsz hstatic hacc hM hov hfee hfv hbal hto hc3
    hc4 hcS hcT (gas := gas) hstip
  refine Triple.seq hA ?_
  have hO := ownerCall (message := message) (state := creditedFee state message v a)
    (substate := creditedSubFee fork substate state message v a) (cO := cO) hfork rfl
    (send := sendOf state message v) (fee := feeOf state message v) (v := v) (a := a)
    (rest := [0x1699, v, a, 0x078a, sel]) (by simp) hw
    (by rw [coldIn_accessSlot_of_warm hw]; exact hcO)
    (gas := gas - (964 + readCost c3 c4 cS cT + mulCost v +
          capCost (rawFee state message v) (storageAt state message.currentTarget 4) +
          debitCost fork state message v + creditCostFee fork state message v a))
    (Nat.le_sub_of_add_le (by omega)) (M := memA M message a)
    (size_mapMem (size_mapMem (size_mapMem (size_mapMem hM _ _) _ _) _ _) _ _)
  refine Triple.seq hO ?_
  exact addFault (by simp) hown (by omega)

/-- The gas of `transfer` up to 9883 and the reads of slots 0, the blacklist slot and 10. -/
abbrev preCost (c0 cB c10 : Bool) : Nat := PRE_COST + slotCost c0 + slotCost cB + slotCost c10

/-- The specification of `transfer(to, v)` when `v * basisPointsRate` overflows.

Hypotheses: call data of 68 to 2^256 - 1 bytes with selector 0xa9059cbb; no value; not paused;
the caller not blacklisted; not deprecated; `v * rate ≥ 2^256` (`rate` = slot 3, read in `S`,
the state after the reads of the checks); enough gas to reach the assert.

Then the frame halts exceptionally with INVALID (`invalidOpcode 0xfe`), no output, no gas left,
in `S` with slot 3 recorded read (nothing written). -/
theorem spec_mulOv (hfork : .berlin ≤ fork)
    (hlong : 68 ≤ message.data.size) (hsz : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0xa9059cbb) (hv : message.value = 0)
    (hnp : byte20 (storageAt state message.currentTarget 0) = 0)
    (hnb : (storageAt state message.currentTarget (blackSlot message)).toNat % 256 = 0)
    (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    (hov : 2 ^ 256 ≤ (wordArg message.data 1).toNat *
      (storageAt (shortState state message) message.currentTarget 3).toNat)
    {c0 cB c10 c3 : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hcB : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget
      (blackSlot message) = cB)
    (hc10 : coldIn (accessSlot (accessSlot substate message.currentTarget 0) message.currentTarget
      (blackSlot message)) message.currentTarget 10 = c10)
    (hc3 : coldIn (shortSubstate substate message) message.currentTarget 3 = c3)
    {gas : Nat} (hg : preCost c0 cB c10 + (204 + slotCost c3) ≤ gas) :
    Spec fork (At CODE message 0 [] .empty gas state substate)
      (Faulted (.invalidOpcode 0xfe) (readSlot (shortState state message) message.currentTarget 3)
        (accessSlot (shortSubstate substate message) message.currentTarget 3)) :=
  Triple.seq (pre hfork (by omega) hsz hsel hv hnp hnb hdep hc0 hcB hc10
      (Nat.le_trans (Nat.le_add_right _ _) hg))
    (bodyMulOv hlong hsz hfork hov hc3 (Nat.le_sub_of_add_le (by rw [Nat.add_comm]; exact hg)))

/-- The specification of `transfer(to, v)` when the fee is above `v`.

Hypotheses: as `spec_mulOv` up to the checks; `v * rate < 2^256`; `v < fee`, the fee as the
bytecode computes it (`feeOf`, from slots 3 and 4 in `S`); enough gas.

Then INVALID at the `sub(v, fee)` of `sendAmount`: no output, no gas left, state `S` with slots 3
and 4 recorded read (nothing written). -/
theorem spec_feeGt (hfork : .berlin ≤ fork)
    (hlong : 68 ≤ message.data.size) (hsz : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0xa9059cbb) (hv : message.value = 0)
    (hnp : byte20 (storageAt state message.currentTarget 0) = 0)
    (hnb : (storageAt state message.currentTarget (blackSlot message)).toNat % 256 = 0)
    (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    (hov : (wordArg message.data 1).toNat *
      (storageAt (shortState state message) message.currentTarget 3).toNat < 2 ^ 256)
    (hgt : (wordArg message.data 1).toNat <
      (feeOf (shortState state message) message (wordArg message.data 1)).toNat)
    {c0 cB c10 c3 c4 : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hcB : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget
      (blackSlot message) = cB)
    (hc10 : coldIn (accessSlot (accessSlot substate message.currentTarget 0) message.currentTarget
      (blackSlot message)) message.currentTarget 10 = c10)
    (hc3 : coldIn (shortSubstate substate message) message.currentTarget 3 = c3)
    (hc4 : coldIn (accessSlot (shortSubstate substate message) message.currentTarget 3)
      message.currentTarget 4 = c4)
    {gas : Nat} (hg : preCost c0 cB c10 + (299 + slotCost c3 + slotCost c4 +
      mulCost (wordArg message.data 1) +
      capCost (rawFee (shortState state message) message (wordArg message.data 1))
        (storageAt (shortState state message) message.currentTarget 4)) ≤ gas) :
    Spec fork (At CODE message 0 [] .empty gas state substate)
      (Faulted (.invalidOpcode 0xfe)
        (readSlot (readSlot (shortState state message) message.currentTarget 3)
          message.currentTarget 4)
        (accessSlot (accessSlot (shortSubstate substate message) message.currentTarget 3)
          message.currentTarget 4)) :=
  Triple.seq (pre hfork (by omega) hsz hsel hv hnp hnb hdep hc0 hcB hc10
      (Nat.le_trans (Nat.le_add_right _ _) hg))
    (bodyFeeGt hlong hsz hfork hov hgt hc3 hc4
      (Nat.le_sub_of_add_le (by rw [Nat.add_comm]; exact hg)))

/-- The specification of `transfer(to, v)` when the recipient's balance overflows.

Hypotheses: Berlin ≤ fork < Glamsterdam, not static, the contract has an account; the checks pass
as in `spec_ok`; `v * rate < 2^256`; `fee ≤ v` (any fee, 0 included); `v ≤ balances[caller]`;
`balances[to] + (v - fee) ≥ 2^256`, with `balances[to]` read after the sender's write (`balT`);
more than 2300 gas left at the sender's SSTORE (`hstip`), and enough gas to reach the assert.

Then INVALID at the recipient's `add`: no output, no gas left, in the state after the sender's
write `balances[caller] := balS - v` and the read of the recipient's slot (the caller discards
it). -/
theorem spec_toOv (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    (hstatic : message.isStatic = false) (hacc : hasAccount state message.currentTarget)
    (hlong : 68 ≤ message.data.size) (hsz : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0xa9059cbb) (hv : message.value = 0)
    (hnp : byte20 (storageAt state message.currentTarget 0) = 0)
    (hnb : (storageAt state message.currentTarget (blackSlot message)).toNat % 256 = 0)
    (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    (hov : (wordArg message.data 1).toNat *
      (storageAt (shortState state message) message.currentTarget 3).toNat < 2 ^ 256)
    (hfv : (feeOf (shortState state message) message (wordArg message.data 1)).toNat ≤
      (wordArg message.data 1).toNat)
    (hbal : (wordArg message.data 1).toNat ≤ (balS (shortState state message) message).toNat)
    (hto : 2 ^ 256 ≤ (balT (shortState state message) message (wordArg message.data 1)
      (addrArg message.data 0)).toNat +
      (sendOf (shortState state message) message (wordArg message.data 1)).toNat)
    {c0 cB c10 c3 c4 cS cT : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
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
    {gas : Nat}
    (hstip : preCost c0 cB c10 + (530 + slotCost c3 + slotCost c4 + slotCost cS +
      mulCost (wordArg message.data 1) +
      capCost (rawFee (shortState state message) message (wordArg message.data 1))
        (storageAt (shortState state message) message.currentTarget 4) + 2400) ≤ gas)
    (hg : preCost c0 cB c10 + (808 + readCost c3 c4 cS cT + mulCost (wordArg message.data 1) +
      capCost (rawFee (shortState state message) message (wordArg message.data 1))
        (storageAt (shortState state message) message.currentTarget 4) +
      debitCost fork (shortState state message) message (wordArg message.data 1)) ≤ gas) :
    Spec fork (At CODE message 0 [] .empty gas state substate)
      (Faulted (.invalidOpcode 0xfe)
        (toOvState (shortState state message) message (wordArg message.data 1)
          (addrArg message.data 0))
        (toOvSub fork (shortSubstate substate message) (shortState state message) message
          (wordArg message.data 1) (addrArg message.data 0))) :=
  Triple.seq (pre hfork (by omega) hsz hsel hv hnp hnb hdep hc0 hcB hc10
      (Nat.le_trans (Nat.le_add_right _ _) hg))
    (bodyToOv hfork hglam hlong hsz hstatic
      (hasAccount_readSlot (hasAccount_readSlot (hasAccount_readSlot hacc)))
      (size_MEMK (callerKey message) 6) hov hfv hbal hto hc3 hc4 hcS hcT
      (Nat.le_sub_of_add_le (by rw [Nat.add_comm]; exact hstip))
      (Nat.le_sub_of_add_le (by rw [Nat.add_comm]; exact hg)))

/-- The specification of `transfer(to, v)` with a fee above 0 when the owner's balance
overflows.

Hypotheses: as `spec_fee` (TransferFeeSpec.lean) up to the recipient: the checks pass,
`v * rate < 2^256`, `0 < fee ≤ v`, `v ≤ balances[caller]`, `balances[to] + (v - fee) < 2^256`;
then `balances[owner] + fee ≥ 2^256`, with `owner` the low 160 bits of slot 0 and both read after
the recipient's write (`balO`); more than 2300 gas left at the recipient's SSTORE (`hstip`; the
sender's follows), and enough gas to reach the assert.

Then INVALID at the owner's `add`: no output, no gas left, in the state after the sender's and
the recipient's writes and the reads of slot 0 and the owner's slot. -/
theorem spec_ownerOv (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    (hstatic : message.isStatic = false) (hacc : hasAccount state message.currentTarget)
    (hlong : 68 ≤ message.data.size) (hsz : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0xa9059cbb) (hv : message.value = 0)
    (hnp : byte20 (storageAt state message.currentTarget 0) = 0)
    (hnb : (storageAt state message.currentTarget (blackSlot message)).toNat % 256 = 0)
    (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    (hov : (wordArg message.data 1).toNat *
      (storageAt (shortState state message) message.currentTarget 3).toNat < 2 ^ 256)
    (hfee : feeOf (shortState state message) message (wordArg message.data 1) ≠ 0)
    (hfv : (feeOf (shortState state message) message (wordArg message.data 1)).toNat ≤
      (wordArg message.data 1).toNat)
    (hbal : (wordArg message.data 1).toNat ≤ (balS (shortState state message) message).toNat)
    (hto : (balT (shortState state message) message (wordArg message.data 1)
      (addrArg message.data 0)).toNat +
      (sendOf (shortState state message) message (wordArg message.data 1)).toNat < 2 ^ 256)
    (hown : 2 ^ 256 ≤ (balO (shortState state message) message (wordArg message.data 1)
      (addrArg message.data 0)).toNat +
      (feeOf (shortState state message) message (wordArg message.data 1)).toNat)
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
    {gas : Nat}
    (hstip : preCost c0 cB c10 + (964 + readCost c3 c4 cS cT + mulCost (wordArg message.data 1) +
      capCost (rawFee (shortState state message) message (wordArg message.data 1))
        (storageAt (shortState state message) message.currentTarget 4) +
      debitCost fork (shortState state message) message (wordArg message.data 1) +
      creditCostFee fork (shortState state message) message (wordArg message.data 1)
        (addrArg message.data 0) + 2401) ≤ gas)
    (hg : preCost c0 cB c10 + (964 + readCost c3 c4 cS cT + mulCost (wordArg message.data 1) +
      capCost (rawFee (shortState state message) message (wordArg message.data 1))
        (storageAt (shortState state message) message.currentTarget 4) +
      debitCost fork (shortState state message) message (wordArg message.data 1) +
      creditCostFee fork (shortState state message) message (wordArg message.data 1)
        (addrArg message.data 0) + 313 + slotCost cO) ≤ gas) :
    Spec fork (At CODE message 0 [] .empty gas state substate)
      (Faulted (.invalidOpcode 0xfe)
        (ownerOvState (shortState state message) message (wordArg message.data 1)
          (addrArg message.data 0))
        (ownerOvSub fork (shortSubstate substate message) (shortState state message) message
          (wordArg message.data 1) (addrArg message.data 0))) :=
  Triple.seq (pre hfork (by omega) hsz hsel hv hnp hnb hdep hc0 hcB hc10
      (Nat.le_trans (Nat.le_add_right _ _) hg))
    (bodyOwnerOv hfork hglam hlong hsz hstatic
      (hasAccount_readSlot (hasAccount_readSlot (hasAccount_readSlot hacc)))
      (size_MEMK (callerKey message) 6) hov hfee hfv hbal hto hown
      (coldIn_accessSlot_false (coldIn_accessSlot_false (coldIn_accessSlot_self _ _ _)))
      hc3 hc4 hcS hcT hcO
      (Nat.le_sub_of_add_le (by rw [Nat.add_comm]; exact hstip))
      (Nat.le_sub_of_add_le (by rw [Nat.add_comm]; exact hg)))

/-- The loop of the interpreter runs the case of `spec_mulOv` to its end condition. It holds for
every bound on the gas of messages and every runner of messages. -/
theorem runFrame_mulOv (hfork : .berlin ≤ fork)
    (hlong : 68 ≤ message.data.size) (hsz : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0xa9059cbb) (hv : message.value = 0)
    (hnp : byte20 (storageAt state message.currentTarget 0) = 0)
    (hnb : (storageAt state message.currentTarget (blackSlot message)).toNat % 256 = 0)
    (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    (hov : 2 ^ 256 ≤ (wordArg message.data 1).toNat *
      (storageAt (shortState state message) message.currentTarget 3).toNat)
    {c0 cB c10 c3 : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hcB : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget
      (blackSlot message) = cB)
    (hc10 : coldIn (accessSlot (accessSlot substate message.currentTarget 0) message.currentTarget
      (blackSlot message)) message.currentTarget 10 = c10)
    (hc3 : coldIn (shortSubstate substate message) message.currentTarget 3 = c3)
    {gas : Nat} (hg : preCost c0 cB c10 + (204 + slotCost c3) ≤ gas)
    {bound : Nat} {runChild : MessageRunner fork Nat bound} {evm : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    ∃ stopped, runFrame (step fork) (step_decreases fork) bound runChild evm within =
      .ok stopped ∧
      Faulted (.invalidOpcode 0xfe) (readSlot (shortState state message) message.currentTarget 3)
          (accessSlot (shortSubstate substate message) message.currentTarget 3) stopped :=
  (spec_mulOv hfork hlong hsz hsel hv hnp hnb hdep hov hc0 hcB hc10 hc3 hg).runFrame start within

/-- The loop of the interpreter runs the case of `spec_feeGt` to its end condition. It holds for
every bound on the gas of messages and every runner of messages. -/
theorem runFrame_feeGt (hfork : .berlin ≤ fork)
    (hlong : 68 ≤ message.data.size) (hsz : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0xa9059cbb) (hv : message.value = 0)
    (hnp : byte20 (storageAt state message.currentTarget 0) = 0)
    (hnb : (storageAt state message.currentTarget (blackSlot message)).toNat % 256 = 0)
    (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    (hov : (wordArg message.data 1).toNat *
      (storageAt (shortState state message) message.currentTarget 3).toNat < 2 ^ 256)
    (hgt : (wordArg message.data 1).toNat <
      (feeOf (shortState state message) message (wordArg message.data 1)).toNat)
    {c0 cB c10 c3 c4 : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hcB : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget
      (blackSlot message) = cB)
    (hc10 : coldIn (accessSlot (accessSlot substate message.currentTarget 0) message.currentTarget
      (blackSlot message)) message.currentTarget 10 = c10)
    (hc3 : coldIn (shortSubstate substate message) message.currentTarget 3 = c3)
    (hc4 : coldIn (accessSlot (shortSubstate substate message) message.currentTarget 3)
      message.currentTarget 4 = c4)
    {gas : Nat} (hg : preCost c0 cB c10 + (299 + slotCost c3 + slotCost c4 +
      mulCost (wordArg message.data 1) +
      capCost (rawFee (shortState state message) message (wordArg message.data 1))
        (storageAt (shortState state message) message.currentTarget 4)) ≤ gas)
    {bound : Nat} {runChild : MessageRunner fork Nat bound} {evm : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    ∃ stopped, runFrame (step fork) (step_decreases fork) bound runChild evm within =
      .ok stopped ∧
      Faulted (.invalidOpcode 0xfe)
          (readSlot (readSlot (shortState state message) message.currentTarget 3)
            message.currentTarget 4)
          (accessSlot (accessSlot (shortSubstate substate message) message.currentTarget 3)
            message.currentTarget 4) stopped :=
  (spec_feeGt hfork hlong hsz hsel hv hnp hnb hdep hov hgt hc0 hcB hc10 hc3 hc4 hg).runFrame start
    within

/-- The loop of the interpreter runs the case of `spec_toOv` to its end condition. It holds for
every bound on the gas of messages and every runner of messages. -/
theorem runFrame_toOv (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    (hstatic : message.isStatic = false) (hacc : hasAccount state message.currentTarget)
    (hlong : 68 ≤ message.data.size) (hsz : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0xa9059cbb) (hv : message.value = 0)
    (hnp : byte20 (storageAt state message.currentTarget 0) = 0)
    (hnb : (storageAt state message.currentTarget (blackSlot message)).toNat % 256 = 0)
    (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    (hov : (wordArg message.data 1).toNat *
      (storageAt (shortState state message) message.currentTarget 3).toNat < 2 ^ 256)
    (hfv : (feeOf (shortState state message) message (wordArg message.data 1)).toNat ≤
      (wordArg message.data 1).toNat)
    (hbal : (wordArg message.data 1).toNat ≤ (balS (shortState state message) message).toNat)
    (hto : 2 ^ 256 ≤ (balT (shortState state message) message (wordArg message.data 1)
      (addrArg message.data 0)).toNat +
      (sendOf (shortState state message) message (wordArg message.data 1)).toNat)
    {c0 cB c10 c3 c4 cS cT : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
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
    {gas : Nat}
    (hstip : preCost c0 cB c10 + (530 + slotCost c3 + slotCost c4 + slotCost cS +
      mulCost (wordArg message.data 1) +
      capCost (rawFee (shortState state message) message (wordArg message.data 1))
        (storageAt (shortState state message) message.currentTarget 4) + 2400) ≤ gas)
    (hg : preCost c0 cB c10 + (808 + readCost c3 c4 cS cT + mulCost (wordArg message.data 1) +
      capCost (rawFee (shortState state message) message (wordArg message.data 1))
        (storageAt (shortState state message) message.currentTarget 4) +
      debitCost fork (shortState state message) message (wordArg message.data 1)) ≤ gas)
    {bound : Nat} {runChild : MessageRunner fork Nat bound} {evm : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    ∃ stopped, runFrame (step fork) (step_decreases fork) bound runChild evm within =
      .ok stopped ∧
      Faulted (.invalidOpcode 0xfe)
          (toOvState (shortState state message) message (wordArg message.data 1)
            (addrArg message.data 0))
          (toOvSub fork (shortSubstate substate message) (shortState state message) message
            (wordArg message.data 1) (addrArg message.data 0)) stopped :=
  (spec_toOv hfork hglam hstatic hacc hlong hsz hsel hv hnp hnb hdep hov hfv hbal hto hc0 hcB hc10
    hc3 hc4 hcS hcT hstip hg).runFrame start within

/-- The loop of the interpreter runs the case of `spec_ownerOv` to its end condition. It holds for
every bound on the gas of messages and every runner of messages. -/
theorem runFrame_ownerOv (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    (hstatic : message.isStatic = false) (hacc : hasAccount state message.currentTarget)
    (hlong : 68 ≤ message.data.size) (hsz : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0xa9059cbb) (hv : message.value = 0)
    (hnp : byte20 (storageAt state message.currentTarget 0) = 0)
    (hnb : (storageAt state message.currentTarget (blackSlot message)).toNat % 256 = 0)
    (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    (hov : (wordArg message.data 1).toNat *
      (storageAt (shortState state message) message.currentTarget 3).toNat < 2 ^ 256)
    (hfee : feeOf (shortState state message) message (wordArg message.data 1) ≠ 0)
    (hfv : (feeOf (shortState state message) message (wordArg message.data 1)).toNat ≤
      (wordArg message.data 1).toNat)
    (hbal : (wordArg message.data 1).toNat ≤ (balS (shortState state message) message).toNat)
    (hto : (balT (shortState state message) message (wordArg message.data 1)
      (addrArg message.data 0)).toNat +
      (sendOf (shortState state message) message (wordArg message.data 1)).toNat < 2 ^ 256)
    (hown : 2 ^ 256 ≤ (balO (shortState state message) message (wordArg message.data 1)
      (addrArg message.data 0)).toNat +
      (feeOf (shortState state message) message (wordArg message.data 1)).toNat)
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
    {gas : Nat}
    (hstip : preCost c0 cB c10 + (964 + readCost c3 c4 cS cT + mulCost (wordArg message.data 1) +
      capCost (rawFee (shortState state message) message (wordArg message.data 1))
        (storageAt (shortState state message) message.currentTarget 4) +
      debitCost fork (shortState state message) message (wordArg message.data 1) +
      creditCostFee fork (shortState state message) message (wordArg message.data 1)
        (addrArg message.data 0) + 2401) ≤ gas)
    (hg : preCost c0 cB c10 + (964 + readCost c3 c4 cS cT + mulCost (wordArg message.data 1) +
      capCost (rawFee (shortState state message) message (wordArg message.data 1))
        (storageAt (shortState state message) message.currentTarget 4) +
      debitCost fork (shortState state message) message (wordArg message.data 1) +
      creditCostFee fork (shortState state message) message (wordArg message.data 1)
        (addrArg message.data 0) + 313 + slotCost cO) ≤ gas)
    {bound : Nat} {runChild : MessageRunner fork Nat bound} {evm : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    ∃ stopped, runFrame (step fork) (step_decreases fork) bound runChild evm within =
      .ok stopped ∧
      Faulted (.invalidOpcode 0xfe)
          (ownerOvState (shortState state message) message (wordArg message.data 1)
            (addrArg message.data 0))
          (ownerOvSub fork (shortSubstate substate message) (shortState state message) message
            (wordArg message.data 1) (addrArg message.data 0)) stopped :=
  (spec_ownerOv hfork hglam hstatic hacc hlong hsz hsel hv hnp hnb hdep hov hfee hfv hbal hto hown
    hc0 hcB hc10 hc3 hc4 hcS hcT hcO hstip hg).runFrame start within

end UsdtVerify.TransferOk
