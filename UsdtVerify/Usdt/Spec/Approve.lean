import UsdtVerify.Usdt.Proofs.Approve

/-!
# approve(address,uint256): the specifications from pc 0

The parts below keep their own headers:

- approve(address,uint256): the specifications
- approve(address,uint256): the revert over a nonzero allowance
-/

section

/-!
## approve(address,uint256): the specifications

`spec_zero`: `approve(s, 0)` sets `allowed[msg.sender][s]` to 0 without reading it.
`spec_set`: `approve(s, v)` with `v ≠ 0` and `allowed[msg.sender][s] = 0` sets it to `v`.
Both log `Approval(msg.sender, s, v)` and stop. (With `v ≠ 0` and a nonzero allowance the
bytecode reverts, `spec_revert`; call data below 68 bytes reverts, `spec_payload`; both in
the second part of this file.)
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

/-- From pc 0, an `approve` call that passes the checks reaches 8230. -/
theorem prefixA (hfork : .berlin ≤ fork) (hlong : 68 ≤ message.data.size)
    (hsz : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x095ea7b3)
    (hv : message.value = 0) (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    {c10 : Bool} (hc10 : coldIn substate message.currentTarget 10 = c10) {gas : Nat}
    (hg : 449 + slotCost c10 ≤ gas) :
    Gas.HoareG fork (At CODE message 0 [] .empty gas state substate)
      (At CODE message 8230 [0x40, wordArg message.data 1, addrArg message.data 0, 0x0cbb, 0x40,
        wordArg message.data 1, addrArg message.data 0, 0x02a2,
        BitVec.ofNat 256 (selector message.data)] MEM0 (gas - (449 + slotCost c10))
        (readSlot state message.currentTarget 10) (accessSlot substate message.currentTarget 10)) := by
  have ht : tested (BitVec.ofNat 256 (selector message.data)) ENTRIES = 3 := by
    rw [hsel]; decide
  have hb : branch (BitVec.ofNat 256 (selector message.data)) 54 (entrySize 4 2) ENTRIES =
      610 := by
    rw [hsel]; decide
  have h1 := dispatch (state := state) (substate := substate) (by omega) hsz (gas := gas)
    (by rw [ht]; gas_ok)
  rw [ht, hb] at h1
  refine Triple.seq h1 ?_
  step entry hv (by gas_ok)
  step payload (Or.inl ⟨rfl, rfl⟩) hlong hsz (by simp) (by gas_ok)
  step notDeprecated hfork (by simp) hdep hc10 (by gas_ok)
  step toStandard (by gas_ok)
  step payload (Or.inr ⟨rfl, rfl⟩) hlong hsz (by simp) (by gas_ok)
  exact Gas.reshapeG rfl rfl (by gas_ok)

/-- From 8384, the write, the log and the stop. -/
theorem suffixA (hfork : .berlin ≤ fork)
    (hstatic : message.isStatic = false) (hacc : hasAccount state message.currentTarget)
    {v s sel : U256} {cA : Bool}
    (hcA : coldIn substate message.currentTarget (allowSlot message s) = cA) {gas : Nat}
    (hstip : 2493 ≤ gas)
    (hg : 2056 + Gas.writeCost fork (originalAt state message.currentTarget (allowSlot message s))
      (storageAt state message.currentTarget (allowSlot message s)) v cA ≤ gas)
    {M : ByteArray} (hM : M.size = 96) (hptr : loadWord (memoryReadBytes M 64 32) 0 32 = 0x60) :
    Gas.SpecG fork (At CODE message 8384 [0x40, v, s, 0x0cbb, 0x40, v, s, 0x02a2, sel] M gas state
        substate)
      (Halted false .empty (gas - (2056 + Gas.writeCost fork
          (originalAt state message.currentTarget (allowSlot message s))
          (storageAt state message.currentTarget (allowSlot message s)) v cA))
        (writeSlot state message.currentTarget (allowSlot message s) v)
        { storeSub fork substate message.currentTarget (allowSlot message s)
            (originalAt state message.currentTarget (allowSlot message s))
            (storageAt state message.currentTarget (allowSlot message s)) v with
          logs := substate.logs.push (approvalLog message.currentTarget
            (bitwiseAnd ADDR_MASK message.caller.toU256) (bitwiseAnd ADDR_MASK s) v) }) := by
  step store hfork (by simp) hstatic hacc hcA hstip (by gas_ok) hM
  step logApproval (by simp) hstatic (by gas_ok) (size_mapMem (size_mapMem hM _ _) _ _)
    (ptr_mapMem (size_mapMem hM _ _) (ptr_mapMem hM hptr _ _) _ _)
  refine (stopA (by gas_ok)).consequence (fun _ h => h) ?_
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  exact ⟨hr, he, ho, by rw [hgas]; gas_ok, hs, hss⟩

/-- The slot of `allowed[msg.sender][spender]` for the spender in argument word 0. -/
abbrev allowArg (message : Message fork) : U256 := allowSlot message (addrArg message.data 0)

/-- The specification of `approve(spender, 0)`, from Berlin on (Glamsterdam included).

Hypotheses: a frame that may write, of an existing account `C`; call data of 68 to 2^256 - 1
bytes with selector 0x095ea7b3 and argument word 1 equal to 0; no value; not deprecated (byte 20
of slot 10 is 0); more than 2300 gas left at the SSTORE, and enough gas.

Then the run stops normally, with `allowed[msg.sender][spender]` (slot
`keccak(spender ++ keccak(caller ++ 5))`) set to 0, after reading slot 10, and the log
`Approval(caller, spender, 0)` appended; gas left `gas - (2560 + price(slot 10) + price(write))`,
the allowance slot's coldness taken after slot 10 was accessed. -/
theorem spec_zero (hfork : .berlin ≤ fork)
    (hstatic : message.isStatic = false) (hacc : hasAccount state message.currentTarget)
    (hlong : 68 ≤ message.data.size) (hsz : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x095ea7b3) (hv : message.value = 0)
    (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    (hzero : wordArg message.data 1 = 0)
    {c10 cA : Bool} (hc10 : coldIn substate message.currentTarget 10 = c10)
    (hcA : coldIn (accessSlot substate message.currentTarget 10) message.currentTarget
      (allowArg message) = cA) {gas : Nat}
    (hstip : 2997 + slotCost c10 ≤ gas)
    (hg : 2560 + slotCost c10 + Gas.writeCost fork
      (originalAt state message.currentTarget (allowArg message))
      (storageAt state message.currentTarget (allowArg message)) 0 cA ≤ gas) :
    Gas.SpecG fork (At CODE message 0 [] .empty gas state substate)
      (Halted false .empty (gas - (2560 + slotCost c10 + Gas.writeCost fork
          (originalAt state message.currentTarget (allowArg message))
          (storageAt state message.currentTarget (allowArg message)) 0 cA))
        (writeSlot (readSlot state message.currentTarget 10) message.currentTarget
          (allowArg message) 0)
        { storeSub fork (accessSlot substate message.currentTarget 10) message.currentTarget
            (allowArg message) (originalAt state message.currentTarget (allowArg message))
            (storageAt state message.currentTarget (allowArg message)) 0 with
          logs := substate.logs.push (approvalLog message.currentTarget
            (bitwiseAnd ADDR_MASK message.caller.toU256)
            (bitwiseAnd ADDR_MASK (addrArg message.data 0)) 0) }) := by
  simp only [allowArg] at hcA hg ⊢
  step prefixA hfork hlong hsz hsel hv hdep hc10 (by gas_ok)
  rw [hzero]
  step checkZero (by simp) (by gas_ok)
  refine (suffixA hfork hstatic (hasAccount_readSlot hacc) hcA (by gas_ok)
    (by simp only [storageAt_readSlot, originalAt_readSlot]; gas_ok) size_MEM0 mload_MEM0).consequence
    (fun _ h => h) ?_
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  exact ⟨hr, he, ho, by rw [hgas]; simp only [storageAt_readSlot, originalAt_readSlot]; gas_ok, hs, hss⟩

/-- The specification of `approve(spender, v)` for `v ≠ 0` when the allowance is 0.

Hypotheses as for `spec_zero`, with argument word 1 (`v`) not 0 and
`allowed[msg.sender][spender] = 0` (the `require` of StandardToken's `approve`).

Then the run stops normally, with the allowance slot set to `v`, after reading slot 10 and the
allowance slot, and the log `Approval(caller, spender, v)` appended; gas left
`gas - (2753 + price(slot 10) + price(allowance read) + price(write))`, the write warm. -/
theorem spec_set (hfork : .berlin ≤ fork)
    (hstatic : message.isStatic = false) (hacc : hasAccount state message.currentTarget)
    (hlong : 68 ≤ message.data.size) (hsz : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x095ea7b3) (hv : message.value = 0)
    (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    (hnz : wordArg message.data 1 ≠ 0)
    (hallow : storageAt state message.currentTarget (allowArg message) = 0)
    {c10 cA : Bool} (hc10 : coldIn substate message.currentTarget 10 = c10)
    (hcA : coldIn (accessSlot substate message.currentTarget 10) message.currentTarget
      (allowArg message) = cA) {gas : Nat}
    (hstip : 3190 + slotCost c10 + slotCost cA ≤ gas)
    (hg : 2753 + slotCost c10 + slotCost cA + Gas.writeCost fork
      (originalAt state message.currentTarget (allowArg message)) 0
      (wordArg message.data 1) false ≤ gas) :
    Gas.SpecG fork (At CODE message 0 [] .empty gas state substate)
      (Halted false .empty (gas - (2753 + slotCost c10 + slotCost cA + Gas.writeCost fork
          (originalAt state message.currentTarget (allowArg message)) 0
          (wordArg message.data 1) false))
        (writeSlot (readSlot (readSlot state message.currentTarget 10) message.currentTarget
          (allowArg message)) message.currentTarget (allowArg message) (wordArg message.data 1))
        { storeSub fork (accessSlot (accessSlot substate message.currentTarget 10)
              message.currentTarget (allowArg message)) message.currentTarget
            (allowArg message) (originalAt state message.currentTarget (allowArg message)) 0
            (wordArg message.data 1) with
          logs := substate.logs.push (approvalLog message.currentTarget
            (bitwiseAnd ADDR_MASK message.caller.toU256)
            (bitwiseAnd ADDR_MASK (addrArg message.data 0)) (wordArg message.data 1)) }) := by
  simp only [allowArg] at hcA hg hallow ⊢
  step prefixA hfork hlong hsz hsel hv hdep hc10 (by gas_ok)
  step checkNonzero hfork hnz (by simp) hcA (by rw [storageAt_readSlot]; exact hallow)
    (by gas_ok) size_MEM0
  refine (suffixA hfork hstatic (hasAccount_readSlot (hasAccount_readSlot hacc))
    (coldIn_accessSlot_self _ _ _) (by gas_ok)
    (by simp only [storageAt_readSlot, originalAt_readSlot, hallow]; gas_ok)
    (size_mapMem (size_mapMem size_MEM0 _ _) _ _)
    (ptr_mapMem (size_mapMem size_MEM0 _ _) (ptr_mapMem size_MEM0 mload_MEM0 _ _) _ _)).consequence
    (fun _ h => h) ?_
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  refine ⟨hr, he, ho, ?_, hs, ?_⟩
  · rw [hgas]; simp only [storageAt_readSlot, originalAt_readSlot, hallow]; gas_ok
  · rw [hss]; simp only [storageAt_readSlot, originalAt_readSlot, hallow]

/-- `approve(spender, 0)`, not deprecated, when the `SSTORE` of the allowance cannot complete
(`NoWrite`: a static frame, no account for `C`, or at most 2300 gas left there): the run reaches
it, and it is `Stuck`. -/
theorem bad_zero (hfork : .berlin ≤ fork)
    (hlong : 68 ≤ message.data.size) (hsz : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x095ea7b3) (hv : message.value = 0)
    (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    (hzero : wordArg message.data 1 = 0)
    {c10 : Bool} (hc10 : coldIn substate message.currentTarget 10 = c10) {gas : Nat}
    (hbad : Gas.NoWrite message state (gas - (696 + slotCost c10)))
    (hg : 696 + slotCost c10 ≤ gas) :
    Gas.HoareG fork (At CODE message 0 [] .empty gas state substate) Gas.Stuck := by
  step prefixA hfork hlong hsz hsel hv hdep hc10 (by gas_ok)
  rw [hzero]
  step checkZero (by simp) (by gas_ok)
  refine storeBad (state := readSlot state message.currentTarget 10) ?_ (hbad.le ?_) ?_ size_MEM0
  · simp
  · gas_ok
  · gas_ok

/-- `approve(spender, v)` with `v ≠ 0` and the allowance 0, not deprecated, when the `SSTORE` of
the allowance cannot complete (`NoWrite`): the run reaches it, and it is `Stuck`. -/
theorem bad_set (hfork : .berlin ≤ fork)
    (hlong : 68 ≤ message.data.size) (hsz : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x095ea7b3) (hv : message.value = 0)
    (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    (hnz : wordArg message.data 1 ≠ 0)
    (hallow : storageAt state message.currentTarget (allowArg message) = 0)
    {c10 cA : Bool} (hc10 : coldIn substate message.currentTarget 10 = c10)
    (hcA : coldIn (accessSlot substate message.currentTarget 10) message.currentTarget
      (allowArg message) = cA) {gas : Nat}
    (hbad : Gas.NoWrite message state (gas - (889 + slotCost c10 + slotCost cA)))
    (hg : 889 + slotCost c10 + slotCost cA ≤ gas) :
    Gas.HoareG fork (At CODE message 0 [] .empty gas state substate) Gas.Stuck := by
  simp only [allowArg] at hcA hallow
  step prefixA hfork hlong hsz hsel hv hdep hc10 (by gas_ok)
  step checkNonzero hfork hnz (by simp) hcA (by rw [storageAt_readSlot]; exact hallow)
    (by gas_ok) size_MEM0
  refine storeBad (state := readSlot (readSlot state message.currentTarget 10)
    message.currentTarget (allowSlot message (addrArg message.data 0))) ?_ (hbad.le ?_) ?_
    (size_mapMem (size_mapMem size_MEM0 _ _) _ _)
  · simp
  · gas_ok
  · gas_ok

/-- The loop of the interpreter runs the case of `spec_zero` to its end condition. It holds for
every bound on the gas of messages and every runner of messages. -/
theorem runFrame_zero (hfork : .berlin ≤ fork)
    (hstatic : message.isStatic = false) (hacc : hasAccount state message.currentTarget)
    (hlong : 68 ≤ message.data.size) (hsz : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x095ea7b3) (hv : message.value = 0)
    (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    (hzero : wordArg message.data 1 = 0)
    {c10 cA : Bool} (hc10 : coldIn substate message.currentTarget 10 = c10)
    (hcA : coldIn (accessSlot substate message.currentTarget 10) message.currentTarget
      (allowArg message) = cA) {gas : Nat}
    (hstip : 2997 + slotCost c10 ≤ gas)
    (hg : 2560 + slotCost c10 + Gas.writeCost fork
      (originalAt state message.currentTarget (allowArg message))
      (storageAt state message.currentTarget (allowArg message)) 0 cA ≤ gas)
    {bound : Nat} {runChild : MessageRunner fork Nat bound} {evm : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    ∃ stopped, runFrame (step fork) (step_decreases fork) bound runChild evm within =
      .ok stopped ∧
      Halted false .empty (gas - (2560 + slotCost c10 + Gas.writeCost fork
            (originalAt state message.currentTarget (allowArg message))
            (storageAt state message.currentTarget (allowArg message)) 0 cA))
          (writeSlot (readSlot state message.currentTarget 10) message.currentTarget
            (allowArg message) 0)
          { storeSub fork (accessSlot substate message.currentTarget 10) message.currentTarget
              (allowArg message) (originalAt state message.currentTarget (allowArg message))
              (storageAt state message.currentTarget (allowArg message)) 0 with
            logs := substate.logs.push (approvalLog message.currentTarget
              (bitwiseAnd ADDR_MASK message.caller.toU256)
              (bitwiseAnd ADDR_MASK (addrArg message.data 0)) 0) } stopped :=
  (spec_zero hfork hstatic hacc hlong hsz hsel hv hdep hzero hc10 hcA hstip hg).runFrame
    start within

/-- The loop of the interpreter runs the case of `spec_set` to its end condition. It holds for
every bound on the gas of messages and every runner of messages. -/
theorem runFrame_set (hfork : .berlin ≤ fork)
    (hstatic : message.isStatic = false) (hacc : hasAccount state message.currentTarget)
    (hlong : 68 ≤ message.data.size) (hsz : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x095ea7b3) (hv : message.value = 0)
    (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    (hnz : wordArg message.data 1 ≠ 0)
    (hallow : storageAt state message.currentTarget (allowArg message) = 0)
    {c10 cA : Bool} (hc10 : coldIn substate message.currentTarget 10 = c10)
    (hcA : coldIn (accessSlot substate message.currentTarget 10) message.currentTarget
      (allowArg message) = cA) {gas : Nat}
    (hstip : 3190 + slotCost c10 + slotCost cA ≤ gas)
    (hg : 2753 + slotCost c10 + slotCost cA + Gas.writeCost fork
      (originalAt state message.currentTarget (allowArg message)) 0
      (wordArg message.data 1) false ≤ gas)
    {bound : Nat} {runChild : MessageRunner fork Nat bound} {evm : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    ∃ stopped, runFrame (step fork) (step_decreases fork) bound runChild evm within =
      .ok stopped ∧
      Halted false .empty (gas - (2753 + slotCost c10 + slotCost cA + Gas.writeCost fork
            (originalAt state message.currentTarget (allowArg message)) 0
            (wordArg message.data 1) false))
          (writeSlot (readSlot (readSlot state message.currentTarget 10) message.currentTarget
            (allowArg message)) message.currentTarget (allowArg message) (wordArg message.data 1))
          { storeSub fork (accessSlot (accessSlot substate message.currentTarget 10)
                message.currentTarget (allowArg message)) message.currentTarget
              (allowArg message) (originalAt state message.currentTarget (allowArg message)) 0
              (wordArg message.data 1) with
            logs := substate.logs.push (approvalLog message.currentTarget
              (bitwiseAnd ADDR_MASK message.caller.toU256)
              (bitwiseAnd ADDR_MASK (addrArg message.data 0)) (wordArg message.data 1)) } stopped :=
  (spec_set hfork hstatic hacc hlong hsz hsel hv hdep hnz hallow hc10 hcA hstip hg).runFrame
    start within

end UsdtVerify.Approve

end

section

/-!
## approve(address,uint256): the revert over a nonzero allowance

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

/-- At 2931, call data of fewer than 68 bytes (two argument words) makes the code revert
(TetherToken's `onlyPayloadSize(2 * 32)`). -/
theorem payloadRevert (hfork : .berlin ≤ fork) {rest : List U256} (hrest : rest.length ≤ 16)
    (hshort : message.data.size < 68) {gas : Nat} (hg : 54 ≤ gas) {M : ByteArray}
    (hM : M.size = 96) :
    Gas.SpecG fork (At CODE message 2931 rest M gas state substate)
      (Halted true .empty (gas - 54) state substate) := by
  have hz : extendMemory M.size [((0 : U256), (0 : U256))] = ⟨0, 0⟩ := by rw [hM]; decide
  step jumpdestR
  step pushR 1 (0x40 : U256)
  step pushR 1 (0x04 : U256)
  step dupR 1
  step binR 0x01 instruction_add
  step pushR 1 (0 : U256)
  step Gas.calldatasizeG (by code_fact) (by code_fact) (by gas_ok) (by stk_ok)
  step swapR 0
  norm
  step popR
  step binR 0x10 Local.instruction_lt
  step unR 0x15 instruction_iszero
  step unR 0x15 instruction_iszero
  step unR 0x15 instruction_iszero
  step pushR 2 (0x0b8b : U256)
  refine Triple.seq (Gas.jumpi_of_eq_zeroG (by code_fact) (by code_fact) (by gas_ok) ?_) ?_
  · have h68 : (add (0x40 : U256) (0x04 : U256)).toNat = 68 := by decide
    have hlt : lessThan (BitVec.ofNat 256 message.data.size) (add (0x40 : U256) (0x04 : U256)) = 1 := by
      simp only [lessThan, h68, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show message.data.size < 2 ^ 256 by omega)]
      rw [if_pos hshort]
    rw [hlt]
    decide
  step pushR 1 (0 : U256)
  step dupR 0
  refine (Gas.revertG (Nat.le_trans (by decide) hfork) (by code_fact) (by code_fact)
    (by rw [hz]; gas_ok)).consequence (fun _ h => h) ?_
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  refine ⟨hr, he, ?_, ?_, hs, hss⟩
  · rw [ho]; simp [memoryReadBytes]
  · rw [hgas, hz]; gas_ok

/-- The gas of the short-payload path of `approve`. -/
abbrev SHORT_COST_A : Nat := 280

/-- The specification of an `approve(address,uint256)` call whose call data is too short.

The call data starts with the selector 0x095ea7b3 and has from 4 to 67 bytes, and the call has no
value. Then TetherToken's payload check of two argument words (at 2931, before the deprecation
check) fails and the run reverts with no output, state and substate unchanged, after 280 gas. -/
theorem spec_payload (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hshort : message.data.size < 68) (hsel : selector message.data = 0x095ea7b3)
    (hv : message.value = 0) {gas : Nat} (hg : SHORT_COST_A ≤ gas) :
    Gas.SpecG fork (At CODE message 0 [] .empty gas state substate)
      (Halted true .empty (gas - SHORT_COST_A) state substate) := by
  simp only [SHORT_COST_A] at hg ⊢
  have hsize' : message.data.size < 2 ^ 256 := by omega
  have ht : tested (BitVec.ofNat 256 (selector message.data)) ENTRIES = 3 := by
    rw [hsel]; decide
  have hb : branch (BitVec.ofNat 256 (selector message.data)) 54 (entrySize 4 2) ENTRIES =
      610 := by
    rw [hsel]; decide
  have h1 := dispatch (state := state) (substate := substate) hsize hsize' (gas := gas)
    (by rw [ht]; gas_ok)
  rw [ht, hb] at h1
  refine Gas.SpecG.seq h1 ?_
  step entry hv (by gas_ok)
  refine ((payloadRevert hfork (by simp) hshort (by gas_ok) size_MEM0)).consequence
    (fun _ h => h) ?_
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  exact ⟨hr, he, ho, by rw [hgas]; gas_ok, hs, hss⟩

end UsdtVerify.Approve

end
