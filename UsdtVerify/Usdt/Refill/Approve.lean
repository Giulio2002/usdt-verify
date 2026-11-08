import UsdtVerify.Usdt.Spec.Approve
import UsdtVerify.Evm.Refill

/-!
# approve: the success paths over `StepI`

`spec_zero` and `spec_set` of `Usdt/Spec/Approve.lean` over `StepI`: no frame of these paths
refills state gas at an SSTORE. The one SSTORE of each path writes the allowance slot.

- `spec_zeroI`: `approve(s, 0)`, when the write of 0 over the allowance refills nothing
  (`hnr`). It refills when, from Glamsterdam, the allowance slot was 0 at the start of the
  transaction and is not 0 at the call.
- `spec_setI`: `approve(s, v)` with `v ≠ 0` over an allowance of 0. A write of a word other than 0
  never refills, so it takes no hypothesis on refills.
-/

namespace UsdtVerify.Approve

open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts
open Transfer TransferOk
open Refill

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate}

/-- A write of a word other than 0 refills nothing. -/
theorem refill_of_ne {o c v : U256} (hv : v ≠ 0) : sstoreStateRefill fork o c v = 0 := by
  unfold sstoreStateRefill
  exact ite_eq_right_iff.mpr fun h => absurd h.2.2.2 hv

/-- `store` over `StepI`, for a write that refills nothing. -/
theorem storeI (hfork : .berlin ≤ fork) {v s : U256}
    {rest : List U256} (hrest : rest.length ≤ 800) (hstatic : message.isStatic = false)
    (hacc : hasAccount state message.currentTarget) {cA : Bool}
    (hcA : coldIn substate message.currentTarget (allowSlot message s) = cA) {gas : Nat}
    (hstip : 2493 ≤ gas)
    (hg : 194 + Gas.writeCost fork (originalAt state message.currentTarget (allowSlot message s))
      (storageAt state message.currentTarget (allowSlot message s)) v cA ≤ gas)
    (hnr : sstoreStateRefill fork (originalAt state message.currentTarget (allowSlot message s))
      (storageAt state message.currentTarget (allowSlot message s)) v = 0)
    {M : ByteArray} (hM : M.size = 96) :
    HoareI fork (At CODE message 8384 (0x40 :: v :: s :: rest) M gas state substate)
      (At CODE message 8514 (0x40 :: v :: s :: rest)
        (mapMem (mapMem M (mkey message.caller.toU256) 5) (mkey s)
          (mapSlot (mkey message.caller.toU256) 5))
        (gas - (194 + Gas.writeCost fork (originalAt state message.currentTarget (allowSlot message s))
          (storageAt state message.currentTarget (allowSlot message s)) v cA))
        (writeSlot state message.currentTarget (allowSlot message s) v)
        (storeSub fork substate message.currentTarget (allowSlot message s)
          (originalAt state message.currentTarget (allowSlot message s))
          (storageAt state message.currentTarget (allowSlot message s)) v)) := by
  simp only [allowSlot, mkey] at hcA hg hnr ⊢
  have pre : Gas.HoareG fork (At CODE message 8384 (0x40 :: v :: s :: rest) M gas state substate)
      (At CODE message 8512
        (mapSlot (bitwiseAnd ADDR_MASK (bitwiseAnd ADDR_MASK s))
          (mapSlot (bitwiseAnd ADDR_MASK (bitwiseAnd ADDR_MASK message.caller.toU256)) 5) ::
          v :: v :: 64 :: v :: s :: rest)
        (mapMem (mapMem M (bitwiseAnd ADDR_MASK (bitwiseAnd ADDR_MASK message.caller.toU256)) 5)
          (bitwiseAnd ADDR_MASK (bitwiseAnd ADDR_MASK s))
          (mapSlot (bitwiseAnd ADDR_MASK (bitwiseAnd ADDR_MASK message.caller.toU256)) 5))
        (gas - 192) state substate) := by
    store_pre
    exact Triple.of_imp fun _ h => h
  refine Triple.seq (HoareG.toIA pre (by gas_ok) fun _ _ => rfl) ?_
  refine Triple.seq (sstoreWI hfork (by code_fact) (by code_fact) hstatic hacc hcA (by gas_ok)
    (by gas_ok) hnr) ?_
  refine HoareG.toIA (Gas.Triple.seqL popR (restate (by decide) rfl rfl (by gas_ok) rfl rfl))
    (by gas_ok) fun _ _ => rfl

/-- `suffixA` over `StepI`, for a write that refills nothing. -/
theorem suffixAI (hfork : .berlin ≤ fork)
    (hstatic : message.isStatic = false) (hacc : hasAccount state message.currentTarget)
    {v s sel : U256} {cA : Bool}
    (hcA : coldIn substate message.currentTarget (allowSlot message s) = cA) {gas : Nat}
    (hstip : 2493 ≤ gas)
    (hg : 2056 + Gas.writeCost fork (originalAt state message.currentTarget (allowSlot message s))
      (storageAt state message.currentTarget (allowSlot message s)) v cA ≤ gas)
    (hnr : sstoreStateRefill fork (originalAt state message.currentTarget (allowSlot message s))
      (storageAt state message.currentTarget (allowSlot message s)) v = 0)
    {M : ByteArray} (hM : M.size = 96) (hptr : loadWord (memoryReadBytes M 64 32) 0 32 = 0x60) :
    HoareI fork (At CODE message 8384 [0x40, v, s, 0x0cbb, 0x40, v, s, 0x02a2, sel] M gas state
        substate)
      (fun evm => evm.running = false ∧ Halted false .empty (gas - (2056 + Gas.writeCost fork
          (originalAt state message.currentTarget (allowSlot message s))
          (storageAt state message.currentTarget (allowSlot message s)) v cA))
        (writeSlot state message.currentTarget (allowSlot message s) v)
        { storeSub fork substate message.currentTarget (allowSlot message s)
            (originalAt state message.currentTarget (allowSlot message s))
            (storageAt state message.currentTarget (allowSlot message s)) v with
          logs := substate.logs.push (approvalLog message.currentTarget
            (bitwiseAnd ADDR_MASK message.caller.toU256) (bitwiseAnd ADDR_MASK s) v) } evm) := by
  refine Triple.seq (storeI hfork (by simp) hstatic hacc hcA hstip (by gas_ok) hnr hM) ?_
  refine Triple.seq (HoareG.toIA (logApproval (by simp) hstatic (by gas_ok)
    (size_mapMem (size_mapMem hM _ _) _ _)
    (ptr_mapMem (size_mapMem hM _ _) (ptr_mapMem hM hptr _ _) _ _)) (by gas_ok) fun _ _ => rfl) ?_
  refine (SpecG.toIA (stopA (by gas_ok)) (by gas_ok) fun _ _ => rfl).consequence
    (fun _ h => h) ?_
  rintro evm ⟨hr0, hr, he, ho, hgas, hs, hss⟩
  exact ⟨hr0, hr, he, ho, by rw [hgas]; gas_ok, hs, hss⟩

/-- `spec_zero` over `StepI`: `approve(s, 0)`, when the write of 0 over the allowance refills
nothing (`hnr`). -/
theorem spec_zeroI (hfork : .berlin ≤ fork)
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
    (hnr : sstoreStateRefill fork (originalAt state message.currentTarget (allowArg message))
      (storageAt state message.currentTarget (allowArg message)) 0 = 0) :
    HoareI fork (At CODE message 0 [] .empty gas state substate)
      (fun evm => evm.running = false ∧ Halted false .empty (gas - (2560 + slotCost c10 +
          Gas.writeCost fork
          (originalAt state message.currentTarget (allowArg message))
          (storageAt state message.currentTarget (allowArg message)) 0 cA))
        (writeSlot (readSlot state message.currentTarget 10) message.currentTarget
          (allowArg message) 0)
        { storeSub fork (accessSlot substate message.currentTarget 10) message.currentTarget
            (allowArg message) (originalAt state message.currentTarget (allowArg message))
            (storageAt state message.currentTarget (allowArg message)) 0 with
          logs := substate.logs.push (approvalLog message.currentTarget
            (bitwiseAnd ADDR_MASK message.caller.toU256)
            (bitwiseAnd ADDR_MASK (addrArg message.data 0)) 0) } evm) := by
  simp only [allowArg] at hcA hg hnr ⊢
  refine Triple.seq (HoareG.toIA (prefixA hfork hlong hsz hsel hv hdep hc10 (by gas_ok))
    (by cases c10 <;> gas_ok) fun _ _ => rfl) ?_
  rw [hzero]
  refine Triple.seq (HoareG.toIA (checkZero (by simp) (by gas_ok)) (by gas_ok)
    fun _ _ => rfl) ?_
  refine (suffixAI hfork hstatic (hasAccount_readSlot hacc) hcA (by gas_ok)
    (by simp only [storageAt_readSlot, originalAt_readSlot]; gas_ok)
    (by simp only [storageAt_readSlot, originalAt_readSlot]; exact hnr)
    size_MEM0 mload_MEM0).consequence (fun _ h => h) ?_
  rintro evm ⟨hr0, hr, he, ho, hgas, hs, hss⟩
  refine ⟨hr0, hr, he, ho, ?_, hs, hss⟩
  rw [hgas]; simp only [storageAt_readSlot, originalAt_readSlot]; gas_ok

/-- `spec_set` over `StepI`: `approve(s, v)` with `v ≠ 0` over an allowance of 0. -/
theorem spec_setI (hfork : .berlin ≤ fork)
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
    HoareI fork (At CODE message 0 [] .empty gas state substate)
      (fun evm => evm.running = false ∧ Halted false .empty (gas - (2753 + slotCost c10 +
          slotCost cA + Gas.writeCost fork
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
            (bitwiseAnd ADDR_MASK (addrArg message.data 0)) (wordArg message.data 1)) } evm) := by
  simp only [allowArg] at hcA hg hallow ⊢
  refine Triple.seq (HoareG.toIA (prefixA hfork hlong hsz hsel hv hdep hc10 (by gas_ok))
    (by cases c10 <;> gas_ok) fun _ _ => rfl) ?_
  refine Triple.seq (HoareG.toIA (checkNonzero hfork hnz (by simp) hcA
    (by rw [storageAt_readSlot]; exact hallow) (by gas_ok) size_MEM0) (by cases cA <;> gas_ok)
    (getStorage_readSlot _ _ _)) ?_
  refine (suffixAI hfork hstatic (hasAccount_readSlot (hasAccount_readSlot hacc))
    (coldIn_accessSlot_self _ _ _) (by gas_ok)
    (by simp only [storageAt_readSlot, originalAt_readSlot, hallow]; gas_ok)
    (refill_of_ne hnz)
    (size_mapMem (size_mapMem size_MEM0 _ _) _ _)
    (ptr_mapMem (size_mapMem size_MEM0 _ _) (ptr_mapMem size_MEM0 mload_MEM0 _ _) _ _)).consequence
    (fun _ h => h) ?_
  rintro evm ⟨hr0, hr, he, ho, hgas, hs, hss⟩
  refine ⟨hr0, hr, he, ho, ?_, hs, ?_⟩
  · rw [hgas]; simp only [storageAt_readSlot, originalAt_readSlot, hallow]; gas_ok
  · rw [hss]; simp only [storageAt_readSlot, originalAt_readSlot, hallow]

end UsdtVerify.Approve
