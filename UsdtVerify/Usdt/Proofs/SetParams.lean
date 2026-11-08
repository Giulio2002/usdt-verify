import UsdtVerify.Usdt.Proofs.Issue

/-!
# setParams(uint256 newBasisPoints, uint256 newMaxFee): the blocks

TetherToken:
```
function setParams(uint newBasisPoints, uint newMaxFee) public onlyOwner {
    require(newBasisPoints < 20);
    require(newMaxFee < 50);
    basisPointsRate = newBasisPoints;
    maximumFee = newMaxFee.mul(10**decimals);
    Params(basisPointsRate, maximumFee);
}
```
`basisPointsRate` is slot 3, `maximumFee` slot 4, `decimals` slot 9.

Entry 1932, body 5790, check at 5794, then 5881 (first require), 5896 (second), 5911 (write
of slot 3), 5919 (`10 ** decimals` and the call of SafeMath `mul` at 10755), 5942 (write of
slot 4), 5949 (the log), back to 1974 (STOP).
-/

namespace UsdtVerify.SetParams

open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts
open Transfer TransferOk Owner Admin Issue SafeMath

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate}

/-- The entry of setParams: the value check, argument words 0 and 1, the jump to 5790 with the
return address 1974. -/
theorem entry2 (hv : message.value = 0) {x : U256} {M : ByteArray} {gas : Nat} (hg : 92 ≤ gas) :
    Gas.HoareG fork (At CODE message 1932 [x] M gas state substate)
      (At CODE message 5790 [wordArg message.data 1, wordArg message.data 0, 0x07b6, x] M
        (gas - 92) state substate) := by
  step jumpdestR
  step Gas.callvalueG (by code_fact) (by code_fact) (by gas_ok) (by stk_ok)
  step unR 0x15 instruction_iszero
  step pushR 2 (0x0797 : U256)
  step jumpiR (by simp [hv, isZero])
  step jumpdestR
  step pushR 2 (0x07b6 : U256)
  step pushR 1 (0x04 : U256)
  step dupR 0
  step dupR 0
  step Gas.calldataloadG (by code_fact) (by code_fact) (by gas_ok)
  step swapR 0
  norm
  step pushR 1 (0x20 : U256)
  step binR 0x01 instruction_add
  step swapR 0
  norm
  step swapR 1
  norm
  step swapR 0
  norm
  step dupR 0
  step Gas.calldataloadG (by code_fact) (by code_fact) (by gas_ok)
  step swapR 0
  norm
  step pushR 1 (0x20 : U256)
  step binR 0x01 instruction_add
  step swapR 0
  norm
  step swapR 1
  norm
  step swapR 0
  norm
  step popR
  step popR
  step pushR 2 (0x169e : U256)
  step jumpR
  exact restate (by decide) rfl rfl (by gas_ok) rfl rfl

/-- The tests of the two `require`s: `x < k` as the code computes it (`ISZERO ISZERO LT`). -/
theorem lt_ne {x k : U256} (h : x.toNat < k.toNat) : isZero (isZero (lessThan x k)) ≠ 0 := by
  simp [lessThan, h, isZero]

theorem lt_eq {x k : U256} (h : ¬ x.toNat < k.toNat) : isZero (isZero (lessThan x k)) = 0 := by
  simp [lessThan, h, isZero]

/-- At 5881: `newBasisPoints < 20`, the test word before the JUMPI at 5888. -/
theorem test1 {b m : U256} {rest : List U256} (hrest : rest.length ≤ 16) {M : ByteArray}
    {gas : Nat} (hg : 16 ≤ gas) :
    Gas.HoareG fork (At CODE message 5881 (m :: b :: rest) M gas state substate)
      (At CODE message 5888 (isZero (isZero (lessThan b 0x14)) :: m :: b :: rest) M (gas - 16)
        state substate) := by
  step jumpdestR
  step pushR 1 (0x14 : U256)
  step dupR 2
  step binR 0x10 Local.instruction_lt
  step unR 0x15 instruction_iszero
  step unR 0x15 instruction_iszero
  exact restate (by decide) rfl rfl (by gas_ok) rfl rfl

/-- At 5896: `newMaxFee < 50`, the test word before the JUMPI at 5903. -/
theorem test2 {b m : U256} {rest : List U256} (hrest : rest.length ≤ 16) {M : ByteArray}
    {gas : Nat} (hg : 16 ≤ gas) :
    Gas.HoareG fork (At CODE message 5896 (m :: b :: rest) M gas state substate)
      (At CODE message 5903 (isZero (isZero (lessThan m 0x32)) :: m :: b :: rest) M (gas - 16)
        state substate) := by
  step jumpdestR
  step pushR 1 (0x32 : U256)
  step dupR 1
  step binR 0x10 Local.instruction_lt
  step unR 0x15 instruction_iszero
  step unR 0x15 instruction_iszero
  exact restate (by decide) rfl rfl (by gas_ok) rfl rfl

/-- The JUMPI of a `require` of setParams: nonzero goes on at `d`. -/
theorem pass {p d : Nat} (hp : (p = 5888 ∧ d = 5896) ∨ (p = 5903 ∧ d = 5911)) {w : U256}
    (hw : w ≠ 0) {rest : List U256} (hrest : rest.length ≤ 16) {M : ByteArray} {gas : Nat}
    (hg : 13 ≤ gas) :
    Gas.HoareG fork (At CODE message p (w :: rest) M gas state substate)
      (At CODE message d rest M (gas - 13) state substate) := by
  rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals
    step pushAnyR 2
    step jumpiR hw
    exact restate (by decide) rfl rfl (by gas_ok) rfl rfl

/-- The JUMPI of a `require` of setParams: zero reverts with no output. -/
theorem fail (hfork : .berlin ≤ fork) {p : Nat} (hp : p = 5888 ∨ p = 5903) {w : U256}
    (hw : w = 0) {rest : List U256} (hrest : rest.length ≤ 16) {M : ByteArray} (hM : M.size = 96)
    {gas : Nat} (hg : 19 ≤ gas) :
    Gas.SpecG fork (At CODE message p (w :: rest) M gas state substate)
      (Halted true .empty (gas - 19) state substate) := by
  have hz : extendMemory M.size [((0 : U256), (0 : U256))] = ⟨0, 0⟩ := by
    rw [hM]; decide
  rcases hp with rfl | rfl
  all_goals
    step pushAnyR 2
    step jumpi0R hw
    step pushR 1 (0 : U256)
    step dupR 0
    refine (Gas.revertG (Nat.le_trans (by decide) hfork) (by code_fact) (by code_fact)
      (by rw [hz]; gas_ok)).consequence (fun _ h => h) ?_
    rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
    refine ⟨hr, he, ?_, ?_, hs, hss⟩
    · rw [ho]; simp [memoryReadBytes]
    · rw [hgas, hz]; gas_ok

-- At 5911, from the `JUMPDEST` to the `SSTORE` of slot 3.
set_option hygiene false in
macro "write3_pre" : tactic => `(tactic| (
  step jumpdestR
  step dupR 1
  step pushR 1 (0x03 : U256)
  step dupR 1
  step swapR 0
  norm))

/-- At 5911: `basisPointsRate = newBasisPoints` (slot 3). -/
theorem write3 (hfork : .berlin ≤ fork) {b m : U256}
    {rest : List U256} (hrest : rest.length ≤ 16) (hstatic : message.isStatic = false)
    (hacc : hasAccount state message.currentTarget) {c3 : Bool}
    (hc3 : coldIn substate message.currentTarget 3 = c3) {M : ByteArray} {gas : Nat}
    (hstip : 2314 ≤ gas)
    (hg : 15 + Gas.writeCost fork (originalAt state message.currentTarget 3)
      (storageAt state message.currentTarget 3) b c3 ≤ gas) :
    Gas.HoareG fork (At CODE message 5911 (m :: b :: rest) M gas state substate)
      (At CODE message 5919 (m :: b :: rest) M
        (gas - (15 + Gas.writeCost fork (originalAt state message.currentTarget 3)
          (storageAt state message.currentTarget 3) b c3))
        (writeSlot state message.currentTarget 3 b)
        (storeSub fork substate message.currentTarget 3 (originalAt state message.currentTarget 3)
          (storageAt state message.currentTarget 3) b)) := by
  write3_pre
  step Gas.sstoreWG hfork (by code_fact) (by code_fact) hstatic hacc hc3 (by gas_ok) (by gas_ok)
  step popR
  exact restate (by decide) rfl rfl (by gas_ok) rfl rfl

/-- At 5911, in a static frame or with no account for `C`: the run reaches the `SSTORE` of
slot 3, which is `Stuck`. -/
theorem write3Bad {b m : U256} {rest : List U256} (hrest : rest.length ≤ 16)
    {M : ByteArray}
    {gas : Nat} (hbad : Gas.NoWrite message state (gas - 13))
    (hg : 13 ≤ gas) :
    Gas.HoareG fork (At CODE message 5911 (m :: b :: rest) M gas state substate) Gas.Stuck := by
  write3_pre
  exact Gas.sstoreNoWrite (by code_fact) (by code_fact) (hbad.le (by gas_ok))

/-- At 5919: reads `decimals` (slot 9), computes `10 ** decimals`, and calls `mul(newMaxFee,
10 ** decimals)`, which returns to 5942. -/
theorem mulCall (hfork : .berlin ≤ fork) {b m x : U256} {c9 : Bool}
    (hc9 : coldIn substate message.currentTarget 9 = c9)
    (hov : m.toNat * (exp (0x0a : U256) (storageAt state message.currentTarget 9)).toNat < 2 ^ 256)
    {M : ByteArray} {gas : Nat}
    (hg : 48 + slotCost c9 + 50 * exponentBytes (storageAt state message.currentTarget 9) +
      mulCost m ≤ gas) :
    Gas.HoareG fork (At CODE message 5919 [m, b, 0x07b6, x] M gas state substate)
      (At CODE message 5942 [mul m (exp (0x0a : U256) (storageAt state message.currentTarget 9)),
          m, b, 0x07b6, x] M
        (gas - (48 + slotCost c9 + 50 * exponentBytes (storageAt state message.currentTarget 9) +
          mulCost m))
        (readSlot state message.currentTarget 9) (accessSlot substate message.currentTarget 9)) := by
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
  step mulBlock (by simp) (by valid_dest) hov (by gas_ok)
  exact restate (by decide) rfl rfl (by gas_ok) rfl rfl

/-- At 5942: `maximumFee = ...` (slot 4). -/
theorem write4 (hfork : .berlin ≤ fork) {f b m : U256}
    {rest : List U256} (hrest : rest.length ≤ 16) (hstatic : message.isStatic = false)
    (hacc : hasAccount state message.currentTarget) {c4 : Bool}
    (hc4 : coldIn substate message.currentTarget 4 = c4) {M : ByteArray} {gas : Nat}
    (hstip : 2311 ≤ gas)
    (hg : 12 + Gas.writeCost fork (originalAt state message.currentTarget 4)
      (storageAt state message.currentTarget 4) f c4 ≤ gas) :
    Gas.HoareG fork (At CODE message 5942 (f :: m :: b :: rest) M gas state substate)
      (At CODE message 5949 (m :: b :: rest) M
        (gas - (12 + Gas.writeCost fork (originalAt state message.currentTarget 4)
          (storageAt state message.currentTarget 4) f c4))
        (writeSlot state message.currentTarget 4 f)
        (storeSub fork substate message.currentTarget 4 (originalAt state message.currentTarget 4)
          (storageAt state message.currentTarget 4) f)) := by
  step jumpdestR
  step pushR 1 (0x04 : U256)
  step dupR 1
  step swapR 0
  norm
  step Gas.sstoreWG hfork (by code_fact) (by code_fact) hstatic hacc hc4 (by gas_ok) (by gas_ok)
  step popR
  exact restate (by decide) rfl rfl (by gas_ok) rfl rfl

/-- At 5942, when the `SSTORE` of slot 4 cannot complete (`NoWrite`): the run reaches it, and it
is `Stuck`. -/
theorem write4Bad {f b m : U256} {rest : List U256} (hrest : rest.length ≤ 16) {M : ByteArray}
    {gas : Nat} (hbad : Gas.NoWrite message state (gas - 10)) (hg : 10 ≤ gas) :
    Gas.HoareG fork (At CODE message 5942 (f :: m :: b :: rest) M gas state substate)
      Gas.Stuck := by
  step jumpdestR
  step pushR 1 (0x04 : U256)
  step dupR 1
  step swapR 0
  norm
  exact Gas.sstoreNoWrite (by code_fact) (by code_fact) (hbad.le (by gas_ok))

/-- GENERIC: the 64 bytes after a memory `M` of 96 bytes in `M ++ a ++ b` are `a ++ b`. -/
theorem read_after64 {M : ByteArray} (hM : M.size = 96) (a b : ByteArray) (ha : a.size = 32)
    (hb : b.size = 32) : memoryReadBytes (M ++ a ++ b) 96 64 = a ++ b := by
  have hab : (a ++ b).size = 64 := by rw [ByteArray.size_append, ha, hb]
  rw [ByteArray.append_assoc]
  have h := ByteArray.extract_append_size_add' (a := M) (b := a ++ b) (i := 0) (j := 64) hM.symm
  simp only [memoryReadBytes, Nat.add_zero, show ¬ (64 = 0) from by decide, ite_false] at h ⊢
  rw [h, ← hab, ByteArray.extract_zero_size]

/-- The topic of `Params(uint256,uint256)`. -/
abbrev PARAMS_TOPIC : U256 :=
  0xb044a1e409eac5c48e5af22d4af52670dd1a99059537a78b31b48c6500a6354e

/-- The log `Params(r, f)` of the contract `c`: one topic, the two words as data. -/
abbrev paramsLog (c : EthLib.Base.Address) (r f : U256) : Blocks.Log :=
  { address := c, topics := [PARAMS_TOPIC].map U256.toBeBytes, data := wordBytes r ++ wordBytes f }

/-- At 5949: reads slots 3 and 4 (warm), logs `Params(slot 3, slot 4)`, returns to 1974 and
stops. -/
theorem paramsLogBlock {b m x : U256} (hstatic : message.isStatic = false)
    (hc3 : coldIn substate message.currentTarget 3 = false)
    (hc4 : coldIn substate message.currentTarget 4 = false) {M : ByteArray} (hM : M.size = 96)
    (hptr : loadWord (memoryReadBytes M 64 32) 0 32 = 0x60) (hfork : .berlin ≤ fork)
    {gas : Nat} (hg : 1556 ≤ gas) :
    Gas.SpecG fork (At CODE message 5949 [m, b, 0x07b6, x] M gas state substate)
      (Halted false .empty (gas - 1556)
        (readSlot (readSlot state message.currentTarget 3) message.currentTarget 4)
        { accessSlot (accessSlot substate message.currentTarget 3) message.currentTarget 4 with
          logs := substate.logs.push (paramsLog message.currentTarget
            (storageAt state message.currentTarget 3) (storageAt state message.currentTarget 4)) }) := by
  have hext0 : extendMemory M.size [((0x40 : U256), (32 : U256))] = ⟨0, 0⟩ := by
    rw [hM]; decide
  have hext1 : extendMemory M.size [((0x60 : U256), (32 : U256))] = ⟨3, 32⟩ := by
    rw [hM]; decide
  have hs1 : (M ++ wordBytes (storageAt state message.currentTarget 3)).size = 128 := by
    rw [ByteArray.size_append, hM, size_wordBytes]
  have hext2 : extendMemory (M ++ wordBytes (storageAt state message.currentTarget 3)).size
      [((0x80 : U256), (32 : U256))] = ⟨3, 32⟩ := by rw [hs1]; decide
  have hs2 : (M ++ wordBytes (storageAt state message.currentTarget 3) ++
      wordBytes (storageAt state message.currentTarget 4)).size = 160 := by
    rw [ByteArray.size_append, hs1, size_wordBytes]
  have hext3 : extendMemory (M ++ wordBytes (storageAt state message.currentTarget 3) ++
      wordBytes (storageAt state message.currentTarget 4)).size
      [((0x40 : U256), (32 : U256))] = ⟨0, 0⟩ := by rw [hs2]; decide
  have hext4 : extendMemory (M ++ wordBytes (storageAt state message.currentTarget 3) ++
      wordBytes (storageAt state message.currentTarget 4)).size
      [((0x60 : U256), (0x40 : U256))] = ⟨0, 0⟩ := by rw [hs2]; decide
  have hmem1 : memoryWrite (memoryExtend M 32) (0x60 : U256).toNat
      (wordBytes (storageAt state message.currentTarget 3)) =
      M ++ wordBytes (storageAt state message.currentTarget 3) := by
    have h := memoryWrite_extend_end (memory := M)
      (value := wordBytes (storageAt state message.currentTarget 3))
    rwa [size_wordBytes, hM] at h
  have hmem2 : memoryWrite (memoryExtend (M ++ wordBytes (storageAt state message.currentTarget 3))
      32) (0x80 : U256).toNat (wordBytes (storageAt state message.currentTarget 4)) =
      M ++ wordBytes (storageAt state message.currentTarget 3) ++
        wordBytes (storageAt state message.currentTarget 4) := by
    have h := memoryWrite_extend_end (memory := M ++ wordBytes (storageAt state message.currentTarget 3))
      (value := wordBytes (storageAt state message.currentTarget 4))
    rwa [size_wordBytes, hs1] at h
  have hread : memoryReadBytes (M ++ wordBytes (storageAt state message.currentTarget 3) ++
      wordBytes (storageAt state message.currentTarget 4)) 64 32 = memoryReadBytes M 64 32 := by
    simp only [memoryReadBytes, ByteArray.extract_append, ByteArray.size_append, hM, size_wordBytes]
    simp
  have hlog : logCost (1 : Fin 5).val (0x40 : U256) = 1262 := by decide
  have hsub : sub (0xa0 : U256) 0x60 = 0x40 := by decide
  step Gas.pushG (n := 32) (word := PARAMS_TOPIC) (by decide) (by code_fact) (by code_fact)
    (decode_push 32 (by decide)) (by rw [pushData_CODE]; decide) (by gas_ok) (by stk_ok)
  step pushR 1 (0x03 : U256)
  step Gas.sloadG hfork (cold := false) (by code_fact) (by code_fact) hc3 (by gas_ok)
  rw [getStorage_eq]
  step pushR 1 (0x04 : U256)
  step Gas.sloadG hfork (cold := false) (by code_fact) (by code_fact)
    (TransferFrom.coldIn_accessSlot_false hc4) (by gas_ok)
  rw [getStorage_eq, storageAt_readSlot]
  step pushR 1 (0x40 : U256)
  step Gas.mloadG (by code_fact) (by code_fact) (by rw [hext0]; gas_ok)
  step Gas.reshapeG (s' := (0x60 : U256) :: _) (m' := M)
    (by rw [hext0, memoryExtend_zero]; exact congrArg (· :: _) hptr)
    (by rw [hext0, memoryExtend_zero]) (by rw [hext0])
  step dupR 0
  step dupR 3
  step dupR 1
  step Gas.mstoreG (by code_fact) (by code_fact) (by rw [hext1]; gas_ok)
  step Gas.reshapeG (m' := M ++ wordBytes (storageAt state message.currentTarget 3)) rfl
    (by rw [hext1]; exact hmem1) (by rw [hext1])
  step pushR 1 (0x20 : U256)
  step binR 0x01 instruction_add
  step dupR 2
  step dupR 1
  step Gas.reshapeG (s' := (0x80 : U256) :: _ :: 0x80 :: _) rfl rfl rfl
  step Gas.mstoreG (by code_fact) (by code_fact) (by rw [hext2]; gas_ok)
  step Gas.reshapeG (m' := M ++ wordBytes (storageAt state message.currentTarget 3) ++
      wordBytes (storageAt state message.currentTarget 4)) rfl
    (by rw [hext2]; exact hmem2) (by rw [hext2])
  step pushR 1 (0x20 : U256)
  step binR 0x01 instruction_add
  step swapR 2
  norm
  step popR
  step popR
  step popR
  step pushR 1 (0x40 : U256)
  step Gas.mloadG (by code_fact) (by code_fact) (by rw [hext3]; gas_ok)
  step Gas.reshapeG (s' := (0x60 : U256) :: _) (m' := M ++ wordBytes (storageAt state message.currentTarget 3) ++
      wordBytes (storageAt state message.currentTarget 4))
    (by rw [hext3, memoryExtend_zero, show (0x40 : U256).toNat = 64 from rfl, hread, hptr])
    (by rw [hext3, memoryExtend_zero]) (by rw [hext3])
  step dupR 0
  step swapR 1
  norm
  step binR 0x03 Local.instruction_sub
  step swapR 0
  norm
  step Gas.reshapeG (s' := 0x60 :: 0x40 :: ([PARAMS_TOPIC] ++ [m, b, 0x07b6, x])) rfl rfl rfl
  step Gas.logG (n := 1) (byte := 0xa1) rfl (by code_fact) (by code_fact) rfl hstatic
    (by rw [hlog, hext4]; gas_ok)
  step Gas.reshapeG rfl (by rw [hext4, memoryExtend_zero]) (by rw [hlog, hext4])
  step popR
  step popR
  step jumpR
  step jumpdestR
  refine (Gas.stopG (by code_fact) (by code_fact)).consequence (fun _ h => h) ?_
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  refine ⟨hr, he, ho, by rw [hgas]; gas_ok, hs, ?_⟩
  rw [hss, hext4, memoryExtend_zero, show (0x60 : U256).toNat = 96 from rfl,
    show (0x40 : U256).toNat = 64 from rfl, read_after64 hM _ _ (size_wordBytes _) (size_wordBytes _)]

end UsdtVerify.SetParams
