import UsdtVerify.Functions.TransferFrom

/-!
# transferFrom(address,address,uint256): the success path from 8648, with a fee of 0

`body` composes the blocks of `TransferFrom` from 8648 (after the payload check) to the STOP at
915. The states and substates along the path are named below. Each word is read in the state
where the code reads it: `balances[_from]` after the allowance step, `balances[_to]` after the
write of `_from`.
-/

namespace UsdtVerify.TransferFrom

open EthLib.Base (Fork U256 Address)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts
open Transfer SafeMath TransferOk

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate}

/-- A slot accessed stays accessed when another slot is accessed. -/
theorem coldIn_accessSlot_false {ss : Substate} {target : Address} {n m : U256}
    (h : coldIn ss target m = false) : coldIn (accessSlot ss target n) target m = false := by
  simp only [coldIn, decide_eq_false_iff_not, Decidable.not_not] at h ⊢
  simp only [Std.ExtTreeMap.getD_insert_self, Std.ExtTreeSet.mem_insert]
  exact Or.inr h

theorem slotCost_ge (c : Bool) : 100 ≤ slotCost c := by cases c <;> decide

/-- `_allowance`: the word of `allowed[_from][msg.sender]`. -/
abbrev allowOf (state : State.TransactionState) (message : Message fork) (f : U256) : U256 :=
  storageAt state message.currentTarget (allowFrom message f)

/-- The state after the reads of the allowance, slot 3 and slot 4. -/
abbrev readsF (state : State.TransactionState) (message : Message fork) (f : U256) :
    State.TransactionState :=
  readSlot (readSlot (readSlot state message.currentTarget (allowFrom message f))
    message.currentTarget 3) message.currentTarget 4

/-- The substate after the accesses of the allowance, slot 3 and slot 4. -/
abbrev accessF (substate : Substate) (message : Message fork) (f : U256) : Substate :=
  accessSlot (accessSlot (accessSlot substate message.currentTarget (allowFrom message f))
    message.currentTarget 3) message.currentTarget 4

/-- The state after the allowance step. -/
abbrev allowedF (state : State.TransactionState) (message : Message fork) (v f : U256) :
    State.TransactionState :=
  allowState (readsF state message f) message.currentTarget (allowFrom message f)
    (allowOf state message f) v

/-- The substate after the allowance step. -/
abbrev allowedSubF (fork : Fork) (substate : Substate) (state : State.TransactionState)
    (message : Message fork) (v f : U256) : Substate :=
  allowSub fork (accessF substate message f) message.currentTarget (allowFrom message f)
    (originalAt state message.currentTarget (allowFrom message f)) (allowOf state message f) v

/-- `balances[_from]`, read after the allowance step. -/
abbrev balFrom (state : State.TransactionState) (message : Message fork) (v f : U256) : U256 :=
  storageAt (allowedF state message v f) message.currentTarget (recipientSlot f)

/-- The state after the write of `balances[_from] = balFrom - v`. -/
abbrev debitedF (state : State.TransactionState) (message : Message fork) (v f : U256) :
    State.TransactionState :=
  writeSlot (readSlot (allowedF state message v f) message.currentTarget (recipientSlot f))
    message.currentTarget (recipientSlot f) (sub (balFrom state message v f) v)

/-- The substate after that write. -/
abbrev debitedSubF (fork : Fork) (substate : Substate) (state : State.TransactionState)
    (message : Message fork) (v f : U256) : Substate :=
  storeSub fork (accessSlot (allowedSubF fork substate state message v f) message.currentTarget
      (recipientSlot f)) message.currentTarget (recipientSlot f)
    (originalAt state message.currentTarget (recipientSlot f)) (balFrom state message v f)
    (sub (balFrom state message v f) v)

/-- `balances[_to]`, read after the write of `_from`. -/
abbrev balTo (state : State.TransactionState) (message : Message fork) (v t f : U256) : U256 :=
  storageAt (debitedF state message v f) message.currentTarget (recipientSlot t)

/-- The state at the end: `balances[_to] = balTo + v`. -/
abbrev creditedF (state : State.TransactionState) (message : Message fork) (v t f : U256) :
    State.TransactionState :=
  writeSlot (readSlot (debitedF state message v f) message.currentTarget (recipientSlot t))
    message.currentTarget (recipientSlot t) (add (balTo state message v t f) v)

/-- The substate after the write of `_to`. -/
abbrev creditedSubF (fork : Fork) (substate : Substate) (state : State.TransactionState)
    (message : Message fork) (v t f : U256) : Substate :=
  storeSub fork (accessSlot (debitedSubF fork substate state message v f) message.currentTarget
      (recipientSlot t)) message.currentTarget (recipientSlot t)
    (originalAt state message.currentTarget (recipientSlot t)) (balTo state message v t f)
    (add (balTo state message v t f) v)

/-- The substate at the end: the log `Transfer(_from, _to, v)` appended. -/
abbrev loggedSubF (fork : Fork) (substate : Substate) (state : State.TransactionState)
    (message : Message fork) (v t f : U256) : Substate :=
  { creditedSubF fork substate state message v t f with
    logs := (creditedSubF fork substate state message v t f).logs.push
      (transferLog message.currentTarget (bitwiseAnd ADDR_MASK f) (bitwiseAnd ADDR_MASK t) v) }

/-- The price of the allowance step. -/
abbrev allowCostF (fork : Fork) (state : State.TransactionState) (message : Message fork)
    (v f : U256) : Nat :=
  allowCost fork (originalAt state message.currentTarget (allowFrom message f))
    (allowOf state message f) v

/-- The price of the write of `_from` (warm). -/
abbrev debitCostF (fork : Fork) (state : State.TransactionState) (message : Message fork)
    (v f : U256) : Nat :=
  Gas.writeCost fork (originalAt state message.currentTarget (recipientSlot f))
    (balFrom state message v f) (sub (balFrom state message v f) v) false

/-- The price of the write of `_to` (warm). -/
abbrev creditCostF (fork : Fork) (state : State.TransactionState) (message : Message fork)
    (v t f : U256) : Nat :=
  Gas.writeCost fork (originalAt state message.currentTarget (recipientSlot t))
    (balTo state message v t f) (add (balTo state message v t f) v) false

/-- From 8648, with a fee of 0, the success path of StandardToken's `transferFrom` up to the STOP
at 915. -/
theorem body (hfork : .berlin ≤ fork)
    (hstatic : message.isStatic = false) (hacc : hasAccount state message.currentTarget)
    {v t f sel : U256} {M : ByteArray} (hM : M.size = 96)
    (hptr : loadWord (memoryReadBytes M 64 32) 0 32 = 0x60)
    (hov : v.toNat * (storageAt state message.currentTarget 3).toNat < 2 ^ 256)
    (hfee : feeOf state message v = 0)
    (hallow : allowOf state message f = MAX_UINT ∨ v.toNat ≤ (allowOf state message f).toNat)
    (hbal : v.toNat ≤ (balFrom state message v f).toNat)
    (hto : (balTo state message v t f).toNat + v.toNat < 2 ^ 256)
    {cA c3 c4 cF cT : Bool}
    (hcA : coldIn substate message.currentTarget (allowFrom message f) = cA)
    (hc3 : coldIn (accessSlot substate message.currentTarget (allowFrom message f))
      message.currentTarget 3 = c3)
    (hc4 : coldIn (accessSlot (accessSlot substate message.currentTarget (allowFrom message f))
      message.currentTarget 3) message.currentTarget 4 = c4)
    (hcF : coldIn (allowedSubF fork substate state message v f) message.currentTarget
      (recipientSlot f) = cF)
    (hcT : coldIn (accessSlot (allowedSubF fork substate state message v f) message.currentTarget
      (recipientSlot f)) message.currentTarget (recipientSlot t) = cT)
    {gas : Nat}
    (hstip : 972 + slotCost cA + slotCost c3 + slotCost c4 + slotCost cF + slotCost cT +
      mulCost v + capCost (rawFee state message v) (storageAt state message.currentTarget 4) +
      allowCostF fork state message v f + debitCostF fork state message v f + 2401 ≤ gas)
    (hg : 2971 + slotCost cA + slotCost c3 + slotCost c4 + slotCost cF + slotCost cT +
      mulCost v + capCost (rawFee state message v) (storageAt state message.currentTarget 4) +
      allowCostF fork state message v f + debitCostF fork state message v f +
      creditCostF fork state message v t f ≤ gas) :
    Gas.SpecG fork (At CODE message 8648 [0x60, 0, 0, 0, v, t, f, 0x1097, v, t, f, 0x0392, sel] M gas
        state substate)
      (Halted false .empty (gas - (2971 + slotCost cA + slotCost c3 + slotCost c4 + slotCost cF +
        slotCost cT + mulCost v +
        capCost (rawFee state message v) (storageAt state message.currentTarget 4) +
        allowCostF fork state message v f + debitCostF fork state message v f +
        creditCostF fork state message v t f))
        (creditedF state message v t f) (loggedSubF fork substate state message v t f)) := by
  have hacc3 : hasAccount (readsF state message f) message.currentTarget :=
    hasAccount_readSlot (hasAccount_readSlot (hasAccount_readSlot hacc))
  have hacc4 : hasAccount (readSlot (allowedF state message v f) message.currentTarget
      (recipientSlot f)) message.currentTarget :=
    hasAccount_readSlot (hasAccount_allowState hacc3)
  have hacc5 : hasAccount (readSlot (debitedF state message v f) message.currentTarget
      (recipientSlot t)) message.currentTarget :=
    hasAccount_readSlot (hasAccount_writeSlot hacc4)
  have horig : ∀ m, originalAt (allowedF state message v f) message.currentTarget m =
      originalAt state message.currentTarget m := by
    intro m
    rw [originalAt_allowState hacc3]
    simp only [originalAt_readSlot]
  have horig2 : ∀ m, originalAt (debitedF state message v f) message.currentTarget m =
      originalAt state message.currentTarget m := by
    intro m
    rw [originalAt_writeSlot hacc4, originalAt_readSlot, horig]
  have hT := slotCost_ge cT
  simp only [allowCostF, debitCostF, creditCostF, rawFee, feeOf, allowOf, balFrom, balTo,
    creditedF, debitedF, allowedF, readsF, loggedSubF, creditedSubF, debitedSubF, allowedSubF,
    accessF] at hstip hg hfee hbal hto hallow hcF hcT hacc4 hacc5 horig horig2 ⊢
  step allowRead hfork (by simp) hcA (by gas_ok) hM
  step feeCall hfork (by simp) hc3 (by gas_ok)
  step mulBlock (by simp) (by valid_dest) (by simpa only [storageAt_readSlot] using hov)
    (by gas_ok)
  at_pc 8802
  step divCall (by simp) (by gas_ok)
  step divBlock (by simp) (by valid_dest) (by decide) (by gas_ok)
  at_pc 8816
  step capBlock hfork (by simp) hc4 (by simp only [storageAt_readSlot]; gas_ok)
  simp only [storageAt_readSlot]
  step Gas.reshapeG (s' := (0x60 : U256) :: 0 :: 0 ::
      storageAt state message.currentTarget (allowFrom message f) :: v :: t :: f ::
      [0x1097, v, t, f, 0x0392, sel]) (by rw [hfee]) rfl rfl
  step allowStep hfork (by simp) (by simp only [storageAt_readSlot]) hallow
    (fun _ => ⟨hstatic, hacc3⟩)
    (coldIn_accessSlot_false (coldIn_accessSlot_false (coldIn_accessSlot_self _ _ _)))
    (by simp only [originalAt_readSlot]; gas_ok)
    (size_allowMem hM f)
  simp only [originalAt_readSlot]
  have hMa : (allowMem message M f).size = 96 := size_allowMem hM f
  have hMb := size_allowMem2 (message := message) hMa (storageAt state message.currentTarget
    (allowFrom message f)) f
  have hPb := ptr_allowMem2 (message := message) hMa (ptr_allowMem hM hptr f)
    (storageAt state message.currentTarget (allowFrom message f)) f
  step sendCall (by simp) (by gas_ok)
  step subBlock (by simp) (by valid_dest) (by simp) (by gas_ok)
  at_pc 9041
  step Gas.reshapeG (s' := v :: (0x60 : U256) :: 0 :: 0 ::
      storageAt state message.currentTarget (allowFrom message f) :: v :: t :: f ::
      [0x1097, v, t, f, 0x0392, sel]) (by simp [sub]) rfl rfl
  step debitCall hfork (by simp) hcF (by gas_ok) hMb
  step subBlock (by simp) (by valid_dest) hbal (by gas_ok)
  at_pc 9125
  step debitStore hfork (by simp) hstatic hacc4 (coldIn_accessSlot_self _ _ _)
    (by simp only [storageAt_readSlot, originalAt_readSlot, horig]; gas_ok) (size_mapMem hMb _ _)
  simp only [storageAt_readSlot, originalAt_readSlot, horig]
  step creditCall hfork (by simp) (cT := cT) (by rw [coldIn_storeSub]; exact hcT) (by gas_ok)
    (size_mapMem (size_mapMem hMb _ _) _ _)
  step addBlock (by simp) (by valid_dest) hto (by gas_ok)
  at_pc 9274
  step creditStore hfork (by simp) hstatic hacc5 (coldIn_accessSlot_self _ _ _) (by gas_ok)
    (by simp only [storageAt_readSlot, originalAt_readSlot, horig2]; gas_ok)
    (size_mapMem (size_mapMem (size_mapMem hMb _ _) _ _) _ _)
  simp only [storageAt_readSlot, originalAt_readSlot, horig2]
  step logBlock (by simp) hstatic (by gas_ok)
    (size_mapMem (size_mapMem (size_mapMem (size_mapMem hMb _ _) _ _) _ _) _ _)
    (ptr_mapMem (size_mapMem (size_mapMem (size_mapMem hMb _ _) _ _) _ _)
      (ptr_mapMem (size_mapMem (size_mapMem hMb _ _) _ _)
        (ptr_mapMem (size_mapMem hMb _ _) (ptr_mapMem hMb hPb _ _) _ _) _ _) _ _)
  refine (endBlock (by gas_ok)).consequence (fun _ h => h) ?_
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  exact ⟨hr, he, ho, by rw [hgas]; gas_ok, hs, hss⟩

end UsdtVerify.TransferFrom
