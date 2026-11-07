import UsdtVerify.Functions.Approve

/-!
# approve(address,uint256): the specifications

`spec_zero`: `approve(s, 0)` sets `allowed[msg.sender][s]` to 0 without reading it.
`spec_set`: `approve(s, v)` with `v ≠ 0` and `allowed[msg.sender][s] = 0` sets it to `v`.
Both log `Approval(msg.sender, s, v)` and stop. (With `v ≠ 0` and a nonzero allowance the
bytecode reverts, `spec_revert`; call data below 68 bytes reverts, `spec_payload`; both in
ApproveRevert.lean.)
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

/-- `approve(spender, 0)`, not deprecated, in a static frame or with no account for `C`: the run
reaches the `SSTORE` of the allowance, which is `Stuck`. -/
theorem bad_zero (hfork : .berlin ≤ fork)
    (hbad : message.isStatic = true ∨ ¬hasAccount state message.currentTarget)
    (hlong : 68 ≤ message.data.size) (hsz : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x095ea7b3) (hv : message.value = 0)
    (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    (hzero : wordArg message.data 1 = 0)
    {c10 : Bool} (hc10 : coldIn substate message.currentTarget 10 = c10) {gas : Nat}
    (hg : 5000 + slotCost c10 ≤ gas) :
    Gas.HoareG fork (At CODE message 0 [] .empty gas state substate) Gas.Stuck := by
  step prefixA hfork hlong hsz hsel hv hdep hc10 (by gas_ok)
  rw [hzero]
  step checkZero (by simp) (by gas_ok)
  refine storeBad (state := readSlot state message.currentTarget 10) ?_ hbad ?_ size_MEM0
  · simp
  · gas_ok

/-- `approve(spender, v)` with `v ≠ 0` and the allowance 0, not deprecated, in a static frame or
with no account for `C`: the run reaches the `SSTORE` of the allowance, which is `Stuck`. -/
theorem bad_set (hfork : .berlin ≤ fork)
    (hbad : message.isStatic = true ∨ ¬hasAccount state message.currentTarget)
    (hlong : 68 ≤ message.data.size) (hsz : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x095ea7b3) (hv : message.value = 0)
    (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    (hnz : wordArg message.data 1 ≠ 0)
    (hallow : storageAt state message.currentTarget (allowArg message) = 0)
    {c10 cA : Bool} (hc10 : coldIn substate message.currentTarget 10 = c10)
    (hcA : coldIn (accessSlot substate message.currentTarget 10) message.currentTarget
      (allowArg message) = cA) {gas : Nat}
    (hg : 5000 + slotCost c10 + slotCost cA ≤ gas) :
    Gas.HoareG fork (At CODE message 0 [] .empty gas state substate) Gas.Stuck := by
  simp only [allowArg] at hcA hallow
  step prefixA hfork hlong hsz hsel hv hdep hc10 (by gas_ok)
  step checkNonzero hfork hnz (by simp) hcA (by rw [storageAt_readSlot]; exact hallow)
    (by gas_ok) size_MEM0
  refine storeBad (state := readSlot (readSlot state message.currentTarget 10)
    message.currentTarget (allowSlot message (addrArg message.data 0))) ?_ hbad ?_
    (size_mapMem (size_mapMem size_MEM0 _ _) _ _)
  · simp
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
