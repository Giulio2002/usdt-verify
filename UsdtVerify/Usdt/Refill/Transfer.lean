import UsdtVerify.Usdt.Spec.Transfer
import UsdtVerify.Evm.Refill

/-!
# transfer: the success paths over `StepI`

`body` and `TransferOk.spec_ok` of the transfer proofs over `StepI`: no frame of the success path
with a fee of 0 refills state gas at an SSTORE, when the write of the sender's balance refills
nothing (`hnrD`). The write of the recipient's balance adds to it without overflow, so it never
writes 0 over a word that is not 0, and refills nothing.

- `stepC`, `stepW`: a step of a proof over `StepG` lifted to `StepI` by `HoareG.toIA` (no write,
  less than 97,920 gas) or `HoareG.toIW` (one write).
- `refill_add`: a write of `add c v` over `c`, with `c + v < 2^256`, refills nothing.
-/

namespace UsdtVerify.Refill

open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm

/-- The goal of `HoareG.toIA` on the gas: the stretch pays less than 97,920. -/
macro "cheap" : tactic => `(tactic| first
  | omega
  | (simp only [UsdtVerify.slotCost, UsdtVerify.SafeMath.mulCost, UsdtVerify.TransferOk.capCost]; (repeat' split) <;> omega))

/-- The goal of `HoareG.toIA` on the storage: the same state, or the state after a read. -/
macro "same_store" : tactic => `(tactic| first
  | exact fun _ _ => (by with_reducible rfl)
  | exact UsdtVerify.Refill.getStorage_readSlot _ _ _
  | (intro _ _; simp only [UsdtVerify.Refill.getStorage_readSlot]; done)
  | exact fun _ _ => rfl)

/-- A step over `StepG` with no write, lifted to `StepI`. -/
macro "stepC " r:term : tactic =>
  `(tactic| refine EthLib.Execution.Evm.Logic.Triple.seq
    (UsdtVerify.Refill.HoareG.toIA $r (by cheap) (by same_store)) ?_)

/-- A write of `add c v` over `c`, with no overflow, refills nothing. -/
theorem refill_add {fork : Fork} {o c v : U256} (h : c.toNat + v.toNat < 2 ^ 256) :
    sstoreStateRefill fork o c (add c v) = 0 := by
  unfold sstoreStateRefill
  refine ite_eq_right_iff.mpr fun ⟨_, _, hc, ha⟩ => absurd ?_ hc
  have : (add c v).toNat = c.toNat + v.toNat := by
    simp [add, BitVec.toNat_add, Nat.mod_eq_of_lt h]
  rw [ha] at this
  apply BitVec.eq_of_toNat_eq
  show c.toNat = 0
  have h0 : (0 : U256).toNat = 0 := rfl
  omega

end UsdtVerify.Refill

namespace UsdtVerify.TransferOk

open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts
open Transfer SafeMath Refill

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate}

/-- `body` over `StepI`, when the write of the sender's balance refills nothing. -/
theorem bodyI (hfork : .berlin ≤ fork)
    (hlong : 68 ≤ message.data.size) (hsz : message.data.size < 2 ^ 256)
    (hstatic : message.isStatic = false) (hacc : hasAccount state message.currentTarget)
    {v a sel : U256} {M : ByteArray} (hM : M.size = 96)
    (hptr : loadWord (memoryReadBytes M 64 32) 0 32 = 0x60)
    (hov : v.toNat * (storageAt state message.currentTarget 3).toNat < 2 ^ 256)
    (hfee : feeOf state message v = 0)
    (hbal : v.toNat ≤ (balS state message).toNat)
    (hto : (balT state message v a).toNat + v.toNat < 2 ^ 256)
    {c3 c4 cS cT : Bool} (hc3 : coldIn substate message.currentTarget 3 = c3)
    (hc4 : coldIn (accessSlot substate message.currentTarget 3) message.currentTarget 4 = c4)
    (hcS : coldIn (accessSlot (accessSlot substate message.currentTarget 3) message.currentTarget 4)
      message.currentTarget (senderSlot message) = cS)
    (hcT : coldIn (access3 substate message) message.currentTarget (recipientSlot a) = cT)
    (hnrD : sstoreStateRefill fork (originalAt state message.currentTarget (senderSlot message))
      (balS state message) (sub (balS state message) v) = 0)
    {gas : Nat}
    (hstip1 : 530 + slotCost c3 + slotCost c4 + slotCost cS + mulCost v +
      capCost (rawFee state message v) (storageAt state message.currentTarget 4) + 2400 ≤ gas)
    (hstip2 : 837 + readCost c3 c4 cS cT + mulCost v +
      capCost (rawFee state message v) (storageAt state message.currentTarget 4) +
      debitCost fork state message v + 2401 ≤ gas)
    (hg : 2829 + readCost c3 c4 cS cT + mulCost v +
      capCost (rawFee state message v) (storageAt state message.currentTarget 4) +
      debitCost fork state message v + creditCost fork state message v a ≤ gas) :
    Refill.HoareI fork (At CODE message 9883 [v, a, 0x1699, v, a, 0x078a, sel] M gas state substate)
      (fun evm => evm.running = false ∧ Halted false .empty (gas - (2829 + readCost c3 c4 cS cT + mulCost v +
        capCost (rawFee state message v) (storageAt state message.currentTarget 4) +
        debitCost fork state message v + creditCost fork state message v a))
        (credited state message v a) (loggedSub fork substate state message v a) evm) := by
  simp only [readCost, debitCost, creditCost, rawFee, feeOf, balS, balT, debited, reads3] at hstip1 hstip2 hg hfee hbal hto hnrD ⊢
  have hacc3 : hasAccount (reads3 state message) message.currentTarget :=
    hasAccount_readSlot (hasAccount_readSlot (hasAccount_readSlot hacc))
  have hacc4 : hasAccount (readSlot (debited state message v) message.currentTarget
      (recipientSlot a)) message.currentTarget :=
    hasAccount_readSlot (hasAccount_writeSlot hacc3)
  simp only [debited, reads3, balS] at hacc3 hacc4
  stepC (payloadOk hlong hsz (by simp) (by gas_ok))
  stepC (feeCall hfork (by simp) hc3 (by gas_ok))
  stepC (mulBlock (by simp) (by valid_dest) hov (by gas_ok))
  stepC (repc (pc' := 9937) (by decide))
  stepC (divCall (by simp) (by gas_ok))
  stepC (divBlock (by simp) (by valid_dest) (by decide) (by gas_ok))
  stepC (repc (pc' := 9951) (by decide))
  stepC (capBlock hfork (by simp) hc4 (by simp only [storageAt_readSlot]; gas_ok))
  simp only [storageAt_readSlot]
  stepC (Gas.reshapeG (s' := (0x40 : U256) :: 0 :: 0 :: v :: a :: [0x1699, v, a, 0x078a, sel])
    (by rw [hfee]) rfl rfl)
  stepC (sendCall (by simp) (by gas_ok))
  stepC (subBlock (by simp) (by valid_dest) (by simp) (by gas_ok))
  stepC (repc (pc' := 9988) (by decide))
  stepC (Gas.reshapeG (s' := v :: (0x40 : U256) :: 0 :: 0 :: v :: a :: [0x1699, v, a, 0x078a, sel])
    (by simp [sub]) rfl rfl)
  stepC (debitCall hfork (by simp) hcS (by gas_ok) hM)
  simp only [storageAt_readSlot]
  stepC (subBlock (by simp) (by valid_dest) hbal (by gas_ok))
  stepC (repc (pc' := 10072) (by decide))
  refine Triple.seq (Refill.HoareG.toIW (debitStore hfork (by simp) hstatic hacc3
    (coldIn_accessSlot_self _ _ _) (by gas_ok)
    (by simp only [storageAt_readSlot, originalAt_readSlot]; gas_ok) (size_mapMem hM _ _))
    (by omega) hacc3 (by simp only [storageAt_readSlot, originalAt_readSlot]; gas_ok)
    (by simp only [storageAt_readSlot, originalAt_readSlot]; exact hnrD)) ?_
  simp only [storageAt_readSlot, originalAt_readSlot]
  stepC (creditCall hfork (by simp) (cT := cT) (by rw [coldIn_storeSub]; exact hcT) (by gas_ok)
    (size_mapMem (size_mapMem hM _ _) _ _))
  stepC (addBlock (by simp) (by valid_dest) hto (by gas_ok))
  stepC (repc (pc' := 10221) (by decide))
  refine Triple.seq (Refill.HoareG.toIW (creditStore hfork (by simp) hstatic hacc4
    (coldIn_accessSlot_self _ _ _) (by gas_ok)
    (by simp only [storageAt_readSlot, originalAt_readSlot, originalAt_writeSlot hacc3]; gas_ok)
    (size_mapMem (size_mapMem (size_mapMem hM _ _) _ _) _ _))
    (by omega) hacc4
    (by simp only [storageAt_readSlot, originalAt_readSlot, originalAt_writeSlot hacc3]; gas_ok)
    (by simp only [storageAt_readSlot]; exact Refill.refill_add hto)) ?_
  simp only [storageAt_readSlot, originalAt_readSlot, originalAt_writeSlot hacc3]
  stepC (logBlock (by simp) hstatic (by gas_ok)
    (size_mapMem (size_mapMem (size_mapMem (size_mapMem hM _ _) _ _) _ _) _ _)
    (ptr_mapMem (size_mapMem (size_mapMem (size_mapMem hM _ _) _ _) _ _)
      (ptr_mapMem (size_mapMem (size_mapMem hM _ _) _ _)
        (ptr_mapMem (size_mapMem hM _ _) (ptr_mapMem hM hptr _ _) _ _) _ _) _ _))
  refine (Refill.SpecG.toIA (endBlock (by gas_ok)) (by cheap) (by same_store)).consequence
    (fun _ h => h) ?_
  rintro evm ⟨hr0, hr, he, ho, hgas, hs, hss⟩
  exact ⟨hr0, hr, he, ho, by rw [hgas]; gas_ok, hs, hss⟩

open TransferFee in
/-- `spec_ok` over `StepI`, when the write of the sender's balance refills nothing (`hnrD`). -/
theorem spec_okI (hfork : .berlin ≤ fork)
    (hstatic : message.isStatic = false) (hacc : hasAccount state message.currentTarget)
    (hlong : 68 ≤ message.data.size) (hsz : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0xa9059cbb) (hv : message.value = 0)
    (hnp : byte20 (storageAt state message.currentTarget 0) = 0)
    (hnb : (storageAt state message.currentTarget (blackSlot message)).toNat % 256 = 0)
    (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    (hov : (wordArg message.data 1).toNat *
      (storageAt (shortState state message) message.currentTarget 3).toNat < 2 ^ 256)
    (hfee : feeOf (shortState state message) message (wordArg message.data 1) = 0)
    (hbal : (wordArg message.data 1).toNat ≤ (balS (shortState state message) message).toNat)
    (hto : (balT (shortState state message) message (wordArg message.data 1)
      (addrArg message.data 0)).toNat + (wordArg message.data 1).toNat < 2 ^ 256)
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
    (hnrD : sstoreStateRefill fork (originalAt state message.currentTarget (senderSlot message))
      (balS (shortState state message) message)
      (sub (balS (shortState state message) message) (wordArg message.data 1)) = 0)
    {gas : Nat}
    (hstip1 : PRE_COST + slotCost c0 + slotCost cB + slotCost c10 + (530 + slotCost c3 +
      slotCost c4 + slotCost cS + mulCost (wordArg message.data 1) +
      capCost (rawFee (shortState state message) message (wordArg message.data 1))
        (storageAt (shortState state message) message.currentTarget 4) + 2400) ≤ gas)
    (hstip2 : PRE_COST + slotCost c0 + slotCost cB + slotCost c10 + (837 + readCost c3 c4 cS cT +
      mulCost (wordArg message.data 1) +
      capCost (rawFee (shortState state message) message (wordArg message.data 1))
        (storageAt (shortState state message) message.currentTarget 4) +
      debitCost fork (shortState state message) message (wordArg message.data 1) + 2401) ≤ gas)
    (hg : okCost fork state message c0 cB c10 c3 c4 cS cT ≤ gas) :
    HoareI fork (At CODE message 0 [] .empty gas state substate)
      (fun evm => evm.running = false ∧ Halted false .empty (gas - okCost fork state message c0 cB c10 c3 c4 cS cT)
        (credited (shortState state message) message (wordArg message.data 1)
          (addrArg message.data 0))
        (loggedSub fork (shortSubstate substate message) (shortState state message) message
          (wordArg message.data 1) (addrArg message.data 0)) evm) := by
  have hB := bodyI (state := shortState state message) (substate := shortSubstate substate message)
    (sel := BitVec.ofNat 256 (selector message.data))
    (gas := gas - (PRE_COST + slotCost c0 + slotCost cB + slotCost c10))
    hfork hlong hsz hstatic
    (hasAccount_readSlot (hasAccount_readSlot (hasAccount_readSlot hacc)))
    (size_MEMK (callerKey message) 6) (ptr_MEMK _ _) hov hfee hbal hto hc3 hc4 hcS hcT
    (by simp only [originalAt_readSlot]; exact hnrD)
    (Nat.le_sub_of_add_le (by rw [Nat.add_comm]; exact hstip1))
    (Nat.le_sub_of_add_le (by rw [Nat.add_comm]; exact hstip2))
    (Nat.le_sub_of_add_le (by rw [Nat.add_comm]; exact hg))
  have hpre : PRE_COST + slotCost c0 + slotCost cB + slotCost c10 ≤ gas :=
    Nat.le_trans (Nat.le_add_right _ _) hg
  refine Triple.seq (HoareG.toIA (pre hfork (by omega) hsz hsel hv hnp hnb hdep hc0 hcB hc10 hpre)
    (by simp only [PRE_COST]; cheap) (by same_store)) ?_
  refine hB.consequence (fun _ h => h) ?_
  rintro evm ⟨hr0, hr, he, ho, hgas, hs, hss⟩
  exact ⟨hr0, hr, he, ho, by rw [hgas, Nat.sub_sub], hs, hss⟩

end UsdtVerify.TransferOk
