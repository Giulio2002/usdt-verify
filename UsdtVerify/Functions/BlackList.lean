import UsdtVerify.Functions.Admin

/-!
# addBlackList(address) and removeBlackList(address)

`addBlackList(a) onlyOwner`: `isBlackListed[a] = true; AddedBlackList(a)`.
`removeBlackList(a) onlyOwner`: `isBlackListed[a] = false; RemovedBlackList(a)`.
`isBlackListed[a]` is the low byte of slot `keccak(a ++ 6)`.

The two bodies are the same code 4004 bytes apart, with the pushed flag (1 or 0) and the topic
as the only differences:
- addBlackList: entry 721, body 3284, check at 3288, write at 3375, log at 3464, back to 776.
- removeBlackList: entry 2276, body 7288, check at 7292, write at 7379, log at 7468, back to 2331.
-/

namespace UsdtVerify.BlackList

open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts
open Transfer TransferOk Owner Admin

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate}

/-- The slot of `isBlackListed[a]`. -/
abbrev listSlot (a : U256) : U256 := mapSlot (mkey a) 6

theorem exp0 : exp (0x0100 : U256) (0 : U256) = 1 := by decide +kernel

/-- At 3375 / 7379: the code writes `isBlackListed[a]` with its low byte set to `v`. -/
theorem listWrite (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam) {p : Nat} {v : U256}
    (hp : (p = 3375 ∧ v = 1) ∨ (p = 7379 ∧ v = 0)) {a : U256} {rest : List U256}
    (hrest : rest.length ≤ 16) (hstatic : message.isStatic = false)
    (hacc : hasAccount state message.currentTarget) {cB : Bool}
    (hcB : coldIn substate message.currentTarget (listSlot a) = cB) {M : ByteArray}
    (hM : M.size = 96) {gas : Nat} (hstip : 2457 + slotCost cB ≤ gas)
    (hg : 158 + slotCost cB + sstoreCost fork (originalAt state message.currentTarget (listSlot a))
      (storageAt state message.currentTarget (listSlot a))
      (setLow (storageAt state message.currentTarget (listSlot a)) v) false ≤ gas) :
    Hoare fork (At CODE message p (a :: rest) M gas state substate)
      (At CODE message (p + 89) (a :: rest) (mapMem M (mkey a) 6)
        (gas - (158 + slotCost cB + sstoreCost fork
          (originalAt state message.currentTarget (listSlot a))
          (storageAt state message.currentTarget (listSlot a))
          (setLow (storageAt state message.currentTarget (listSlot a)) v) false))
        (writeSlot state message.currentTarget (listSlot a)
          (setLow (storageAt state message.currentTarget (listSlot a)) v))
        (storeSub fork (accessSlot substate message.currentTarget (listSlot a))
          message.currentTarget (listSlot a)
          (originalAt state message.currentTarget (listSlot a))
          (storageAt state message.currentTarget (listSlot a))
          (setLow (storageAt state message.currentTarget (listSlot a)) v))) := by
  have hexp : exponentBytes (0 : U256) = 0 := by decide
  have hff : mul (0xff : U256) 1 = 0xff := by decide
  have hv' : mul (isZero (isZero v)) 1 = v := by
    rcases hp with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> decide
  unfold setLow at hg ⊢
  simp only [listSlot] at hcB hg ⊢
  rcases hp with ⟨rfl, hv⟩ | ⟨rfl, hv⟩
  all_goals
    step jumpdestR
    step push (n := 1) (word := v) (by decide) (by code_fact) (by code_fact)
      (decode_push 1 (by decide)) (by rw [hv, pushData_CODE]; decide) (by gas_ok) (by stk_ok)
    step pushR 1 (0x06 : U256)
    step pushR 1 (0 : U256)
    step dupR 3
    step hashTail7 (by decide) (by simp; omega) hM (by gas_ok)
    step pushR 1 (0 : U256)
    step pushR 2 (0x0100 : U256)
    step Local.exp (Nat.le_trans (by decide) hfork) (by code_fact) (by code_fact) (by gas_ok)
    rw [exp0]
    step dupR 1
    step sload hfork (cold := cB) (by code_fact) (by code_fact) hcB (by gas_ok)
    rw [show state.getStorage message.currentTarget (U256.toBeBytes (mapSlot (mkey a) 6)) =
      storageAt state message.currentTarget (mapSlot (mkey a) 6) from rfl]
    step dupR 1
    step pushR 1 (0xff : U256)
    step binR 0x02 Local.instruction_mul
    rw [hff]
    step unR 0x19 Local.instruction_not
    step binR 0x16 Local.instruction_and
    step swapR 0
    norm
    step dupR 3
    step unR 0x15 instruction_iszero
    step unR 0x15 instruction_iszero
    step binR 0x02 Local.instruction_mul
    rw [hv']
    step binR 0x17 Local.instruction_or
    step swapR 0
    norm
    step sstoreW hfork hglam (by code_fact) (by code_fact) hstatic (hasAccount_readSlot hacc)
      (coldIn_accessSlot_self _ _ _) (by gas_ok)
      (by rw [originalAt_readSlot, storageAt_readSlot]; gas_ok)
    rw [originalAt_readSlot, storageAt_readSlot, writeSlot_readSlot _ _ hacc]
    step popR
    exact restate (by decide) rfl rfl (by gas_ok) rfl rfl

/-- The topic of `AddedBlackList(address)`. -/
abbrev ADDED_TOPIC : U256 :=
  0x42e160154868087d6bfdc0ca23d96a1c1cfa32f1b72ba9ba27b69b98a0d819dc

/-- The topic of `RemovedBlackList(address)`. -/
abbrev REMOVED_TOPIC : U256 :=
  0xd7e9ec6e6ecd65492dce6bf513cd6867560d49544421d0783ddf06e76c24470c

/-- The topic of `Deprecate(address)`. -/
abbrev DEPRECATE_TOPIC : U256 :=
  0xcc358699805e9a8b7f77b522628c7cb9abd07d9efb86b6fb616af1609036a99e

/-- A log of the contract `c` with the one topic `t` and the data word `w`. -/
abbrev log1W (c : EthLib.Base.Address) (t w : U256) : Blocks.Log :=
  { address := c, topics := [t].map U256.toBeBytes, data := wordBytes w }

/-- At 3464 / 7468 / 2830 (addBlackList, removeBlackList, deprecate): the log of the masked
argument under the topic `t`, the jump back to `r`, and the STOP there. -/
theorem listLog {q : Nat} {t : U256} {r : Nat}
    (hq : (q = 3464 ∧ t = ADDED_TOPIC ∧ r = 0x0308) ∨ (q = 7468 ∧ t = REMOVED_TOPIC ∧ r = 0x091b) ∨
      (q = 2830 ∧ t = DEPRECATE_TOPIC ∧ r = 0x0260))
    {a x : U256} (hstatic : message.isStatic = false) {M : ByteArray} (hM : M.size = 96)
    (hptr : loadWord (memoryReadBytes M 64 32) 0 32 = 0x60) {gas : Nat} (hg : 1087 ≤ gas) :
    Spec fork (At CODE message q [a, BitVec.ofNat 256 r, x] M gas state substate)
      (Local.Stopped (gas - 1087) state
        { substate with logs := substate.logs.push (log1W message.currentTarget t (mkey a)) }) := by
  have hext0 : extendMemory M.size [((0x40 : U256), (32 : U256))] = ⟨0, 0⟩ := by
    rw [hM]; decide
  have hext1 : extendMemory M.size [((0x60 : U256), (32 : U256))] = ⟨3, 32⟩ := by
    rw [hM]; decide
  have hsz : (M ++ wordBytes (mkey a)).size = 128 := by
    rw [ByteArray.size_append, hM, size_wordBytes]
  have hext2 : extendMemory (M ++ wordBytes (mkey a)).size [((0x40 : U256), (32 : U256))] =
      ⟨0, 0⟩ := by rw [hsz]; decide
  have hext3 : extendMemory (M ++ wordBytes (mkey a)).size [((0x60 : U256), (0x20 : U256))] =
      ⟨0, 0⟩ := by rw [hsz]; decide
  have hmem1 : memoryWrite (memoryExtend M 32) (0x60 : U256).toNat (wordBytes (mkey a)) =
      M ++ wordBytes (mkey a) := by
    have h := memoryWrite_extend_end (memory := M) (value := wordBytes (mkey a))
    rwa [size_wordBytes, hM] at h
  have hread2 : memoryReadBytes (M ++ wordBytes (mkey a)) 64 32 = memoryReadBytes M 64 32 := by
    simp only [memoryReadBytes, ByteArray.extract_append, hM]
    simp
  have hlog : logCost (1 : Fin 5).val (0x20 : U256) = 1006 := by decide
  rcases hq with ⟨rfl, ht, rfl⟩ | ⟨rfl, ht, rfl⟩ | ⟨rfl, ht, rfl⟩
  all_goals
    step push (n := 32) (word := t) (by decide) (by code_fact) (by code_fact)
      (decode_push 32 (by decide)) (by rw [ht, pushData_CODE]; decide) (by gas_ok) (by stk_ok)
    step dupR 1
    step pushR 1 (0x40 : U256)
    step mload (by code_fact) (by code_fact) (by rw [hext0]; gas_ok)
    step reshape (s' := (0x60 : U256) :: _) (m' := M)
      (by rw [hext0, memoryExtend_zero]; exact congrArg (· :: _) hptr)
      (by rw [hext0, memoryExtend_zero]) (by rw [hext0])
    step dupR 0
    step dupR 2
    step pushR 20 ADDR_MASK
    step binR 0x16 Local.instruction_and
    step pushR 20 ADDR_MASK
    step binR 0x16 Local.instruction_and
    step dupR 1
    step mstore (by code_fact) (by code_fact) (by rw [hext1]; gas_ok)
    step reshape (m' := M ++ wordBytes (mkey a)) rfl (by rw [hext1]; exact hmem1) (by rw [hext1])
    step pushR 1 (0x20 : U256)
    step binR 0x01 instruction_add
    step swapR 1
    norm
    step popR
    step popR
    step pushR 1 (0x40 : U256)
    step mload (by code_fact) (by code_fact) (by rw [hext2]; gas_ok)
    step reshape (s' := 0x60 :: 0x80 :: t :: a :: BitVec.ofNat 256 _ :: [x])
      (m' := M ++ wordBytes (mkey a))
      (by rw [hext2, memoryExtend_zero, show (0x40 : U256).toNat = 64 from rfl, hread2, hptr]; rfl)
      (by rw [hext2, memoryExtend_zero]) (by rw [hext2])
    step dupR 0
    step swapR 1
    norm
    step binR 0x03 Local.instruction_sub
    step swapR 0
    norm
    step reshape (s' := 0x60 :: 0x20 :: ([t] ++ [a, BitVec.ofNat 256 _, x])) rfl rfl rfl
    step Logic.log (n := 1) (byte := 0xa1) rfl (by code_fact) (by code_fact) rfl hstatic
      (by rw [hlog, hext3]; gas_ok)
    step reshape rfl (by rw [hext3, memoryExtend_zero]) (by rw [hlog, hext3])
    step popR
    step jumpR
    step jumpdestR
    refine (Local.stop (by code_fact) (by code_fact)).consequence (fun _ h => h) ?_
    rintro evm ⟨hr, he, hgas, hs, hss⟩
    refine ⟨hr, he, by rw [hgas]; gas_ok, hs, ?_⟩
    rw [hss, hext3, memoryExtend_zero, show (0x60 : U256).toNat = 96 from rfl,
      show (0x20 : U256).toNat = 32 from rfl, read_after hM _ (size_wordBytes (mkey a))]

end UsdtVerify.BlackList
