import UsdtVerify.Usdt.Proofs.BlackList
import UsdtVerify.Usdt.Proofs.TransferFrom

/-!
# issue(uint256) and redeem(uint256): the blocks

TetherToken:
```
function issue(uint amount) public onlyOwner {
    require(_totalSupply + amount > _totalSupply);
    require(balances[owner] + amount > balances[owner]);
    balances[owner] += amount;
    _totalSupply += amount;
    Issue(amount);
}
function redeem(uint amount) public onlyOwner {
    require(_totalSupply >= amount);
    require(balances[owner] >= amount);
    _totalSupply -= amount;
    balances[owner] -= amount;
    Redeem(amount);
}
```
`_totalSupply` is slot 1, `balances[owner]` is slot `keccak(owner ++ 2)` (`ownerBal`). The sums
are unchecked EVM additions guarded by the `require`s.

- issue: entry 1976, body 6019, check at 6023, then 6110 (first require), 6130 (second), 6338
  (the writes), 6465 (the log), back to 2009 (STOP).
- redeem: entry 2011, body 6522, check at 6526, then 6613, 6630, 6741 (write of slot 1), 6758
  (write of `balances[owner]`), 6868 (the log), back to 2044 (STOP).
-/

namespace UsdtVerify.Issue

open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts
open Transfer TransferOk Owner Admin BlackList

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate}

/-- The slot of `balances[owner]`. -/
abbrev ownerBal (state : State.TransactionState) (c : EthLib.Base.Address) : U256 :=
  mapSlot (ownerOf state c) 2

theorem mkey_owner (w : U256) :
    mkey (bitwiseAnd ADDR_MASK (div w (exp (0x0100 : U256) (0 : U256)))) = bitwiseAnd ADDR_MASK w := by
  simp only [mkey, mask_mask]
  have := owner_expr w
  rw [mask_mask] at this
  exact this

/-- The lookup of `balances[owner]` at its five copies: slot 0 (warm) is read, the owner masked,
and the key words hashed; the slot is left on the stack. -/
theorem ownerLookup (hfork : .berlin ≤ fork) {p : Nat}
    (hp : p ∈ [6131, 6229, 6340, 6632, 6759]) {rest : List U256} (hrest : rest.length ≤ 900)
    {M : ByteArray} (hM : M.size = 96) (hc0 : coldIn substate message.currentTarget 0 = false)
    {gas : Nat} (hg : 229 ≤ gas) :
    Gas.HoareG fork (At CODE message p rest M gas state substate)
      (At CODE message (p + 96) (ownerBal state message.currentTarget :: rest)
        (mapMem M (ownerOf state message.currentTarget) 2) (gas - 229)
        (readSlot state message.currentTarget 0) (accessSlot substate message.currentTarget 0)) := by
  have hexp : exponentBytes (0 : U256) = 0 := by decide
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl
  all_goals
    step pushR 1 (0x02 : U256)
    step pushR 1 (0 : U256)
    step dupR 0
    step pushR 1 (0 : U256)
    step swapR 0
    norm
    step Gas.sloadG hfork (cold := false) (by code_fact) (by code_fact) hc0 (by gas_ok)
    rw [show state.getStorage message.currentTarget (U256.toBeBytes 0) =
      storageAt state message.currentTarget 0 from rfl]
    step swapR 0
    norm
    step pushR 2 (0x0100 : U256)
    step Gas.expLG (Nat.le_trans (by decide) hfork) (by code_fact) (by code_fact) (by gas_ok)
    step swapR 0
    norm
    step binR 0x04 Local.instruction_div
    step pushR 20 ADDR_MASK
    step binR 0x16 Local.instruction_and
    step hashTail7 (by decide) (by omega) hM (by gas_ok)
    rw [mkey_owner]
    exact restate rfl rfl rfl (by gas_ok) rfl rfl

/-- The topic of `Issue(uint256)`. -/
abbrev ISSUE_TOPIC : U256 :=
  0xcb8241adb0c3fdb35b70c24ce35c5eb0c17af7431c99f827d44a445ca624176a

/-- The topic of `Redeem(uint256)`. -/
abbrev REDEEM_TOPIC : U256 :=
  0x702d5967f45f6513a38ffc42d6ba9bf230bd40e8f53b16363c7eb4fd2deb9a44

/-- At 6465 / 6868: the log of the amount under the topic `t`, the jump back to `r`, and the
STOP there. -/
theorem amountLog {q : Nat} {t : U256} {r : Nat}
    (hq : (q = 6465 ∧ t = ISSUE_TOPIC ∧ r = 0x07d9) ∨ (q = 6868 ∧ t = REDEEM_TOPIC ∧ r = 0x07fc))
    {a x : U256} (hstatic : message.isStatic = false) {M : ByteArray} (hM : M.size = 96)
    (hptr : loadWord (memoryReadBytes M 64 32) 0 32 = 0x60) {gas : Nat} (hg : 1075 ≤ gas) :
    Gas.SpecG fork (At CODE message q [a, BitVec.ofNat 256 r, x] M gas state substate)
      (Halted false .empty (gas - 1075) state
        { substate with logs := substate.logs.push (log1W message.currentTarget t a) }) := by
  have hext0 : extendMemory M.size [((0x40 : U256), (32 : U256))] = ⟨0, 0⟩ := by
    rw [hM]; decide
  have hext1 : extendMemory M.size [((0x60 : U256), (32 : U256))] = ⟨3, 32⟩ := by
    rw [hM]; decide
  have hsz : (M ++ wordBytes a).size = 128 := by
    rw [ByteArray.size_append, hM, size_wordBytes]
  have hext2 : extendMemory (M ++ wordBytes a).size [((0x40 : U256), (32 : U256))] =
      ⟨0, 0⟩ := by rw [hsz]; decide
  have hext3 : extendMemory (M ++ wordBytes a).size [((0x60 : U256), (0x20 : U256))] =
      ⟨0, 0⟩ := by rw [hsz]; decide
  have hmem1 : memoryWrite (memoryExtend M 32) (0x60 : U256).toNat (wordBytes a) =
      M ++ wordBytes a := by
    have h := memoryWrite_extend_end (memory := M) (value := wordBytes a)
    rwa [size_wordBytes, hM] at h
  have hread2 : memoryReadBytes (M ++ wordBytes a) 64 32 = memoryReadBytes M 64 32 := by
    simp only [memoryReadBytes, ByteArray.extract_append, hM]
    simp
  have hlog : logCost (1 : Fin 5).val (0x20 : U256) = 1006 := by decide
  rcases hq with ⟨rfl, ht, rfl⟩ | ⟨rfl, ht, rfl⟩
  all_goals
    step Gas.pushG (n := 32) (word := t) (by decide) (by code_fact) (by code_fact)
      (decode_push 32 (by decide)) (by rw [ht, pushData_CODE]; decide) (by gas_ok) (by stk_ok)
    step dupR 1
    step pushR 1 (0x40 : U256)
    step Gas.mloadG (by code_fact) (by code_fact) (by rw [hext0]; gas_ok)
    step Gas.reshapeG (s' := (0x60 : U256) :: _) (m' := M)
      (by rw [hext0, memoryExtend_zero]; exact congrArg (· :: _) hptr)
      (by rw [hext0, memoryExtend_zero]) (by rw [hext0])
    step dupR 0
    step dupR 2
    step dupR 1
    step Gas.mstoreG (by code_fact) (by code_fact) (by rw [hext1]; gas_ok)
    step Gas.reshapeG (m' := M ++ wordBytes a) rfl (by rw [hext1]; exact hmem1) (by rw [hext1])
    step pushR 1 (0x20 : U256)
    step binR 0x01 instruction_add
    step swapR 1
    norm
    step popR
    step popR
    step pushR 1 (0x40 : U256)
    step Gas.mloadG (by code_fact) (by code_fact) (by rw [hext2]; gas_ok)
    step Gas.reshapeG (s' := 0x60 :: 0x80 :: t :: a :: BitVec.ofNat 256 _ :: [x])
      (m' := M ++ wordBytes a)
      (by rw [hext2, memoryExtend_zero, show (0x40 : U256).toNat = 64 from rfl, hread2, hptr]; rfl)
      (by rw [hext2, memoryExtend_zero]) (by rw [hext2])
    step dupR 0
    step swapR 1
    norm
    step binR 0x03 Local.instruction_sub
    step swapR 0
    norm
    step Gas.reshapeG (s' := 0x60 :: 0x20 :: ([t] ++ [a, BitVec.ofNat 256 _, x])) rfl rfl rfl
    step Gas.logG (n := 1) (byte := 0xa1) rfl (by code_fact) (by code_fact) rfl hstatic
      (by rw [hlog, hext3]; gas_ok)
    step Gas.reshapeG rfl (by rw [hext3, memoryExtend_zero]) (by rw [hlog, hext3])
    step popR
    step jumpR
    step jumpdestR
    refine (Gas.stopG (by code_fact) (by code_fact)).consequence (fun _ h => h) ?_
    rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
    refine ⟨hr, he, ho, by rw [hgas]; gas_ok, hs, ?_⟩
    rw [hss, hext3, memoryExtend_zero, show (0x60 : U256).toNat = 96 from rfl,
      show (0x20 : U256).toNat = 32 from rfl, read_after hM _ (size_wordBytes a)]

/-- GENERIC: recording two reads of slots of one account commutes. -/
theorem readSlot_comm (st : State.TransactionState) (t : EthLib.Base.Address) (n m : U256) :
    readSlot (readSlot st t n) t m = readSlot (readSlot st t m) t n := by
  simp only [readSlot, State.TransactionState.recordStorageRead]
  congr 1
  apply Std.ExtTreeMap.ext_getElem?
  intro k
  by_cases hk : k = t
  · subst hk
    simp only [Std.ExtTreeMap.getElem?_insert_self, Std.ExtTreeMap.getD_insert_self]
    congr 1
    ext x
    simp only [Std.ExtTreeSet.mem_insert]
    exact or_left_comm
  · simp [Std.ExtTreeMap.getElem?_insert, Ne.symm hk]

/-- GENERIC: accessing two slots of one account commutes. -/
theorem accessSlot_comm (ss : Substate) (t : EthLib.Base.Address) (n m : U256) :
    accessSlot (accessSlot ss t n) t m = accessSlot (accessSlot ss t m) t n := by
  simp only [accessSlot]
  congr 1
  apply Std.ExtTreeMap.ext_getElem?
  intro k
  by_cases hk : k = t
  · subst hk
    simp only [Std.ExtTreeMap.getElem?_insert_self, Std.ExtTreeMap.getD_insert_self]
    congr 1
    ext x
    simp only [Std.ExtTreeSet.mem_insert]
    exact or_left_comm
  · simp [Std.ExtTreeMap.getElem?_insert, Ne.symm hk]

/-- The JUMPI of a `require` after its test word: nonzero goes on at `d`. -/
theorem reqPass {p d : Nat}
    (hp : (p = 6122 ∧ d = 6130) ∨ (p = 6330 ∧ d = 6338) ∨ (p = 6622 ∧ d = 6630) ∨
      (p = 6733 ∧ d = 6741)) {w : U256} (hw : w ≠ 0) {rest : List U256}
    (hrest : rest.length ≤ 16) {M : ByteArray} {gas : Nat} (hg : 13 ≤ gas) :
    Gas.HoareG fork (At CODE message p (w :: rest) M gas state substate)
      (At CODE message d rest M (gas - 13) state substate) := by
  rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals
    step pushAnyR 2
    step jumpiR hw
    exact restate (by decide) rfl rfl (by gas_ok) rfl rfl

/-- The JUMPI of a `require` after its test word: zero reverts with no output. -/
theorem reqRevert (hfork : .berlin ≤ fork) {p : Nat}
    (hp : p = 6122 ∨ p = 6330 ∨ p = 6622 ∨ p = 6733) {w : U256} (hw : w = 0)
    {rest : List U256} (hrest : rest.length ≤ 16) {M : ByteArray} (hM : M.size = 96)
    {gas : Nat} (hg : 19 ≤ gas) :
    Gas.SpecG fork (At CODE message p (w :: rest) M gas state substate)
      (Halted true .empty (gas - 19) state substate) := by
  have hz : extendMemory M.size [((0 : U256), (0 : U256))] = ⟨0, 0⟩ := by
    rw [hM]; decide
  rcases hp with rfl | rfl | rfl | rfl
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

/-! ## issue -/

/-- At 6110, the first `require` of issue: `_totalSupply + amount > _totalSupply`. -/
theorem issueTest1 (hfork : .berlin ≤ fork) {a : U256} {rest : List U256}
    (hrest : rest.length ≤ 16) {M : ByteArray} {c1 : Bool}
    (hc1 : coldIn substate message.currentTarget 1 = c1) {gas : Nat}
    (hg : 122 + slotCost c1 ≤ gas) :
    Gas.HoareG fork (At CODE message 6110 (a :: rest) M gas state substate)
      (At CODE message 6122 (isZero (isZero (greaterThan
          (add (storageAt state message.currentTarget 1) a) (storageAt state message.currentTarget 1)))
          :: a :: rest) M (gas - (122 + slotCost c1))
        (readSlot state message.currentTarget 1) (accessSlot substate message.currentTarget 1)) := by
  step jumpdestR
  step pushR 1 (0x01 : U256)
  step Gas.sloadG hfork (cold := c1) (by code_fact) (by code_fact) hc1 (by gas_ok)
  step dupR 1
  step pushR 1 (0x01 : U256)
  step Gas.sloadG hfork (cold := false) (by code_fact) (by code_fact)
    (coldIn_accessSlot_self _ _ _) (by gas_ok)
  step binR 0x01 instruction_add
  step binR 0x11 Local.instruction_gt
  step unR 0x15 instruction_iszero
  step unR 0x15 instruction_iszero
  refine restate (by decide) ?_ rfl (by gas_ok) (readSlot_readSlot _ _ _)
    (accessSlot_accessSlot _ _ _)
  simp only [storageAt_readSlot]

/-- Reading slot 0 again after reading slot 0 and `n`: the state is as before. -/
theorem readSlot_0n0 (st : State.TransactionState) (t : EthLib.Base.Address) (n : U256) :
    readSlot (readSlot (readSlot st t 0) t n) t 0 = readSlot (readSlot st t 0) t n := by
  rw [readSlot_comm _ t n 0, readSlot_readSlot]

theorem accessSlot_0n0 (ss : Substate) (t : EthLib.Base.Address) (n : U256) :
    accessSlot (accessSlot (accessSlot ss t 0) t n) t 0 = accessSlot (accessSlot ss t 0) t n := by
  rw [accessSlot_comm _ t n 0, accessSlot_accessSlot]

/-- At 6130, the second `require` of issue: `balances[owner] + amount > balances[owner]`. -/
theorem issueTest2 (hfork : .berlin ≤ fork) {a : U256} {rest : List U256}
    (hrest : rest.length ≤ 16) {M : ByteArray} (hM : M.size = 96)
    (hc0 : coldIn substate message.currentTarget 0 = false) {cO : Bool}
    (hcO : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget
      (ownerBal state message.currentTarget) = cO) {gas : Nat}
    (hg : 574 + slotCost cO ≤ gas) :
    Gas.HoareG fork (At CODE message 6130 (a :: rest) M gas state substate)
      (At CODE message 6330 (isZero (isZero (greaterThan
          (add (storageAt state message.currentTarget (ownerBal state message.currentTarget)) a)
          (storageAt state message.currentTarget (ownerBal state message.currentTarget))))
          :: a :: rest)
        (mapMem (mapMem M (ownerOf state message.currentTarget) 2)
          (ownerOf state message.currentTarget) 2) (gas - (574 + slotCost cO))
        (readSlot (readSlot state message.currentTarget 0) message.currentTarget
          (ownerBal state message.currentTarget))
        (accessSlot (accessSlot substate message.currentTarget 0) message.currentTarget
          (ownerBal state message.currentTarget))) := by
  have hc0' : coldIn (accessSlot (accessSlot substate message.currentTarget 0)
      message.currentTarget (ownerBal state message.currentTarget)) message.currentTarget 0 =
      false := by
    rw [accessSlot_comm]; exact coldIn_accessSlot_self _ _ _
  step jumpdestR
  step ownerLookup hfork (by decide) (by simp; omega) hM hc0 (gas := gas - 1) (by gas_ok)
  step Gas.sloadG hfork (cold := cO) (by code_fact) (by code_fact) hcO (by gas_ok)
  rw [show (readSlot state message.currentTarget 0).getStorage message.currentTarget
      (U256.toBeBytes (ownerBal state message.currentTarget)) =
      storageAt state message.currentTarget (ownerBal state message.currentTarget) from
    storageAt_readSlot _ _ _ _ _]
  step dupR 1
  step ownerLookup hfork (by decide) (by simp; omega) (size_mapMem hM _ _) hc0'
    (gas := gas - 1 - 229 - slotCost cO - 3) (by gas_ok)
  simp only [readSlot_0n0, accessSlot_0n0]
  step Gas.sloadG hfork (cold := false) (by code_fact) (by code_fact)
    (coldIn_accessSlot_self _ _ _) (by gas_ok)
  step binR 0x01 instruction_add
  step binR 0x11 Local.instruction_gt
  step unR 0x15 instruction_iszero
  step unR 0x15 instruction_iszero
  refine restate (by decide) ?_ rfl (by gas_ok) (readSlot_readSlot _ _ _)
    (accessSlot_accessSlot _ _ _)
  simp only [ownerBal, ownerOf, storageAt_readSlot]

/-! ## The writes -/

theorem getStorage_eq (st : State.TransactionState) (t : EthLib.Base.Address) (n : U256) :
    st.getStorage t (U256.toBeBytes n) = storageAt st t n := rfl

-- The tail of a write of `slot op= a`, from `PUSH1 0 DUP3 DUP3` (slot and amount below) to the
-- `SSTORE`.
set_option hygiene false in
macro "op_pre " b:term:max i:term:max hcold:term:max : tactic => `(tactic| (
  step dupR 2
  step dupR 2
  step Gas.sloadG hfork (cold := false) (by code_fact) (by code_fact) $hcold (by gas_ok)
  rw [getStorage_eq]
  step binR $b $i
  step swapR 2
  norm
  step popR
  step popR
  step dupR 1
  step swapR 0
  norm))

-- The tail of a write of `slot op= a`, from `PUSH1 0 DUP3 DUP3` (slot and amount below) to the
-- `POP` after `SSTORE`.
set_option hygiene false in
macro "op_write " b:term:max i:term:max hcold:term:max : tactic => `(tactic| (
  op_pre $b $i $hcold
  step Gas.sstoreWG hfork (by code_fact) (by code_fact) hstatic (hasAccount_readSlot hacc)
    (coldIn_accessSlot_self _ _ _) (by gas_ok)
    (by rw [originalAt_readSlot, storageAt_readSlot]; gas_ok)
  rw [originalAt_readSlot, storageAt_readSlot, writeSlot_readSlot _ _ hacc, storeSub_accessSlot]
  step popR))

/-- At 6449 (issue): `_totalSupply += amount`. -/
theorem issueTotal (hfork : .berlin ≤ fork) {a : U256}
    {rest : List U256} (hrest : rest.length ≤ 800) (hstatic : message.isStatic = false)
    (hacc : hasAccount state message.currentTarget)
    (hc1 : coldIn substate message.currentTarget 1 = false) {M : ByteArray} {gas : Nat}
    (hstip : 2432 ≤ gas)
    (hg : 133 + Gas.writeCost fork (originalAt state message.currentTarget 1)
      (storageAt state message.currentTarget 1) (add (storageAt state message.currentTarget 1) a)
      false ≤ gas) :
    Gas.HoareG fork (At CODE message 6449 (a :: rest) M gas state substate)
      (At CODE message 6465 (a :: rest) M
        (gas - (133 + Gas.writeCost fork (originalAt state message.currentTarget 1)
          (storageAt state message.currentTarget 1)
          (add (storageAt state message.currentTarget 1) a) false))
        (writeSlot state message.currentTarget 1 (add (storageAt state message.currentTarget 1) a))
        (storeSub fork substate message.currentTarget 1 (originalAt state message.currentTarget 1)
          (storageAt state message.currentTarget 1)
          (add (storageAt state message.currentTarget 1) a))) := by
  step dupR 0
  step pushR 1 (0x01 : U256)
  step pushR 1 (0 : U256)
  op_write 0x01 instruction_add hc1
  exact restate (by decide) rfl rfl (by gas_ok) rfl rfl

/-- At 6741 (redeem): `_totalSupply -= amount`. -/
theorem redeemTotal (hfork : .berlin ≤ fork) {a : U256}
    {rest : List U256} (hrest : rest.length ≤ 800) (hstatic : message.isStatic = false)
    (hacc : hasAccount state message.currentTarget)
    (hc1 : coldIn substate message.currentTarget 1 = false) {M : ByteArray} {gas : Nat}
    (hstip : 2433 ≤ gas)
    (hg : 134 + Gas.writeCost fork (originalAt state message.currentTarget 1)
      (storageAt state message.currentTarget 1) (sub (storageAt state message.currentTarget 1) a)
      false ≤ gas) :
    Gas.HoareG fork (At CODE message 6741 (a :: rest) M gas state substate)
      (At CODE message 6758 (a :: rest) M
        (gas - (134 + Gas.writeCost fork (originalAt state message.currentTarget 1)
          (storageAt state message.currentTarget 1)
          (sub (storageAt state message.currentTarget 1) a) false))
        (writeSlot state message.currentTarget 1 (sub (storageAt state message.currentTarget 1) a))
        (storeSub fork substate message.currentTarget 1 (originalAt state message.currentTarget 1)
          (storageAt state message.currentTarget 1)
          (sub (storageAt state message.currentTarget 1) a))) := by
  step jumpdestR
  step dupR 0
  step pushR 1 (0x01 : U256)
  step pushR 1 (0 : U256)
  op_write 0x03 Local.instruction_sub hc1
  exact restate (by decide) rfl rfl (by gas_ok) rfl rfl

-- The write of `balances[owner] op= a` after the lookup of the slot (issue and redeem), from
-- `DUP3 DUP3` to the `SSTORE`.
set_option hygiene false in
macro "owner_pre " b:term:max i:term:max : tactic => `(tactic| (
  step dupR 2
  step dupR 2
  step Gas.sloadG hfork (cold := false) (by code_fact) (by code_fact) hcO' (by gas_ok)
  rw [getStorage_eq]
  step binR $b $i
  step swapR 2
  norm
  step popR
  step popR
  step dupR 1
  step swapR 0
  norm
  step restate (st' := readSlot (readSlot state message.currentTarget 0) message.currentTarget
      (ownerBal state message.currentTarget))
    (ss' := accessSlot (accessSlot substate message.currentTarget 0) message.currentTarget
      (ownerBal state message.currentTarget)) rfl rfl rfl rfl rfl rfl))

/-- At 6338 (issue): `balances[owner] += amount`. -/
theorem issueOwner (hfork : .berlin ≤ fork) {a : U256}
    {rest : List U256} (hrest : rest.length ≤ 800) (hstatic : message.isStatic = false)
    (hacc : hasAccount state message.currentTarget)
    (hc0 : coldIn substate message.currentTarget 0 = false)
    (hcO : coldIn substate message.currentTarget (ownerBal state message.currentTarget) = false)
    {M : ByteArray} (hM : M.size = 96) {gas : Nat} (hstip : 2659 ≤ gas)
    (hg : 360 + Gas.writeCost fork
      (originalAt state message.currentTarget (ownerBal state message.currentTarget))
      (storageAt state message.currentTarget (ownerBal state message.currentTarget))
      (add (storageAt state message.currentTarget (ownerBal state message.currentTarget)) a)
      false ≤ gas) :
    Gas.HoareG fork (At CODE message 6338 (a :: rest) M gas state substate)
      (At CODE message 6449 (a :: rest) (mapMem M (ownerOf state message.currentTarget) 2)
        (gas - (360 + Gas.writeCost fork
          (originalAt state message.currentTarget (ownerBal state message.currentTarget))
          (storageAt state message.currentTarget (ownerBal state message.currentTarget))
          (add (storageAt state message.currentTarget (ownerBal state message.currentTarget)) a)
          false))
        (writeSlot (readSlot state message.currentTarget 0) message.currentTarget
          (ownerBal state message.currentTarget)
          (add (storageAt state message.currentTarget (ownerBal state message.currentTarget)) a))
        (storeSub fork (accessSlot substate message.currentTarget 0) message.currentTarget
          (ownerBal state message.currentTarget)
          (originalAt state message.currentTarget (ownerBal state message.currentTarget))
          (storageAt state message.currentTarget (ownerBal state message.currentTarget))
          (add (storageAt state message.currentTarget (ownerBal state message.currentTarget)) a))) := by
  have hcO' := TransferFrom.coldIn_accessSlot_false (n := 0) hcO
  step jumpdestR
  step dupR 0
  step ownerLookup hfork (by decide) (by simp; omega) hM hc0 (gas := gas - 1 - 3) (by gas_ok)
  step pushR 1 (0 : U256)
  have hacc := hasAccount_readSlot (n := 0) (other := message.currentTarget) hacc
  owner_pre 0x01 instruction_add
  step Gas.sstoreWG hfork (by code_fact) (by code_fact) hstatic (hasAccount_readSlot hacc)
    (coldIn_accessSlot_self _ _ _) (by gas_ok)
    (by simp only [originalAt_readSlot, storageAt_readSlot]; gas_ok)
  simp only [originalAt_readSlot, storageAt_readSlot]
  rw [writeSlot_readSlot _ _ hacc, storeSub_accessSlot]
  step popR
  exact restate (by decide) rfl rfl (by gas_ok) rfl rfl

/-- At 6758 (redeem): `balances[owner] -= amount`. -/
theorem redeemOwner (hfork : .berlin ≤ fork) {a : U256}
    {rest : List U256} (hrest : rest.length ≤ 800) (hstatic : message.isStatic = false)
    (hacc : hasAccount state message.currentTarget)
    (hc0 : coldIn substate message.currentTarget 0 = false)
    (hcO : coldIn substate message.currentTarget (ownerBal state message.currentTarget) = false)
    {M : ByteArray} (hM : M.size = 96) {gas : Nat} (hstip : 2658 ≤ gas)
    (hg : 359 + Gas.writeCost fork
      (originalAt state message.currentTarget (ownerBal state message.currentTarget))
      (storageAt state message.currentTarget (ownerBal state message.currentTarget))
      (sub (storageAt state message.currentTarget (ownerBal state message.currentTarget)) a)
      false ≤ gas) :
    Gas.HoareG fork (At CODE message 6758 (a :: rest) M gas state substate)
      (At CODE message 6868 (a :: rest) (mapMem M (ownerOf state message.currentTarget) 2)
        (gas - (359 + Gas.writeCost fork
          (originalAt state message.currentTarget (ownerBal state message.currentTarget))
          (storageAt state message.currentTarget (ownerBal state message.currentTarget))
          (sub (storageAt state message.currentTarget (ownerBal state message.currentTarget)) a)
          false))
        (writeSlot (readSlot state message.currentTarget 0) message.currentTarget
          (ownerBal state message.currentTarget)
          (sub (storageAt state message.currentTarget (ownerBal state message.currentTarget)) a))
        (storeSub fork (accessSlot substate message.currentTarget 0) message.currentTarget
          (ownerBal state message.currentTarget)
          (originalAt state message.currentTarget (ownerBal state message.currentTarget))
          (storageAt state message.currentTarget (ownerBal state message.currentTarget))
          (sub (storageAt state message.currentTarget (ownerBal state message.currentTarget)) a))) := by
  have hcO' := TransferFrom.coldIn_accessSlot_false (n := 0) hcO
  step dupR 0
  step ownerLookup hfork (by decide) (by simp; omega) hM hc0 (gas := gas - 3) (by gas_ok)
  step pushR 1 (0 : U256)
  have hacc := hasAccount_readSlot (n := 0) (other := message.currentTarget) hacc
  owner_pre 0x03 Local.instruction_sub
  step Gas.sstoreWG hfork (by code_fact) (by code_fact) hstatic (hasAccount_readSlot hacc)
    (coldIn_accessSlot_self _ _ _) (by gas_ok)
    (by simp only [originalAt_readSlot, storageAt_readSlot]; gas_ok)
  simp only [originalAt_readSlot, storageAt_readSlot]
  rw [writeSlot_readSlot _ _ hacc, storeSub_accessSlot]
  step popR
  exact restate (by decide) rfl rfl (by gas_ok) rfl rfl

/-- At 6338 (issue), when the `SSTORE` cannot complete (`NoWrite`: a static frame, no account for
`C`, or at most 2300 gas left there): the run reaches the `SSTORE` of `balances[owner]` (`Stuck`).
-/
theorem issueOwnerBad (hfork : .berlin ≤ fork) {a : U256}
    {rest : List U256} (hrest : rest.length ≤ 800)
    (hc0 : coldIn substate message.currentTarget 0 = false)
    (hcO : coldIn substate message.currentTarget (ownerBal state message.currentTarget) = false)
    {M : ByteArray} (hM : M.size = 96) {gas : Nat} (hbad : Gas.NoWrite message state (gas - 358))
    (hg : 358 ≤ gas) :
    Gas.HoareG fork (At CODE message 6338 (a :: rest) M gas state substate) Gas.Stuck := by
  have hcO' := TransferFrom.coldIn_accessSlot_false (n := 0) hcO
  step jumpdestR
  step dupR 0
  step ownerLookup hfork (by decide) (by simp; omega) hM hc0 (gas := gas - 1 - 3) (by gas_ok)
  step pushR 1 (0 : U256)
  owner_pre 0x01 instruction_add
  exact Gas.sstoreNoWrite (by code_fact) (by code_fact) (hbad.le (by gas_ok))

/-- At 6741 (redeem), when the `SSTORE` cannot complete (`NoWrite`: a static frame, no account for
`C`, or at most 2300 gas left there): the run reaches the `SSTORE` of `_totalSupply` (`Stuck`). -/
theorem redeemTotalBad (hfork : .berlin ≤ fork) {a : U256}
    {rest : List U256} (hrest : rest.length ≤ 800)
    (hc1 : coldIn substate message.currentTarget 1 = false) {M : ByteArray} {gas : Nat}
    (hbad : Gas.NoWrite message state (gas - 132))
    (hg : 132 ≤ gas) :
    Gas.HoareG fork (At CODE message 6741 (a :: rest) M gas state substate) Gas.Stuck := by
  step jumpdestR
  step dupR 0
  step pushR 1 (0x01 : U256)
  step pushR 1 (0 : U256)
  op_pre 0x03 Local.instruction_sub hc1
  exact Gas.sstoreNoWrite (by code_fact) (by code_fact) (hbad.le (by gas_ok))

/-- At 6449 (issue), when the `SSTORE` of `_totalSupply` cannot complete (`NoWrite`): the run
reaches it, and it is `Stuck`. -/
theorem issueTotalBad (hfork : .berlin ≤ fork) {a : U256}
    {rest : List U256} (hrest : rest.length ≤ 800)
    (hc1 : coldIn substate message.currentTarget 1 = false) {M : ByteArray} {gas : Nat}
    (hbad : Gas.NoWrite message state (gas - 131)) (hg : 131 ≤ gas) :
    Gas.HoareG fork (At CODE message 6449 (a :: rest) M gas state substate) Gas.Stuck := by
  step dupR 0
  step pushR 1 (0x01 : U256)
  step pushR 1 (0 : U256)
  op_pre 0x01 instruction_add hc1
  exact Gas.sstoreNoWrite (by code_fact) (by code_fact) (hbad.le (by gas_ok))

/-- At 6758 (redeem), when the `SSTORE` of `balances[owner]` cannot complete (`NoWrite`): the run
reaches it, and it is `Stuck`. -/
theorem redeemOwnerBad (hfork : .berlin ≤ fork) {a : U256}
    {rest : List U256} (hrest : rest.length ≤ 800)
    (hc0 : coldIn substate message.currentTarget 0 = false)
    (hcO : coldIn substate message.currentTarget (ownerBal state message.currentTarget) = false)
    {M : ByteArray} (hM : M.size = 96) {gas : Nat}
    (hbad : Gas.NoWrite message state (gas - 357)) (hg : 357 ≤ gas) :
    Gas.HoareG fork (At CODE message 6758 (a :: rest) M gas state substate) Gas.Stuck := by
  have hcO' := TransferFrom.coldIn_accessSlot_false (n := 0) hcO
  step dupR 0
  step ownerLookup hfork (by decide) (by simp; omega) hM hc0 (gas := gas - 3) (by gas_ok)
  step pushR 1 (0 : U256)
  owner_pre 0x03 Local.instruction_sub
  exact Gas.sstoreNoWrite (by code_fact) (by code_fact) (hbad.le (by gas_ok))

/-! ## redeem's tests -/

/-- At 6613, the first `require` of redeem: `_totalSupply >= amount`. -/
theorem redeemTest1 (hfork : .berlin ≤ fork) {a : U256} {rest : List U256}
    (hrest : rest.length ≤ 16) {M : ByteArray} {c1 : Bool}
    (hc1 : coldIn substate message.currentTarget 1 = c1) {gas : Nat}
    (hg : 19 + slotCost c1 ≤ gas) :
    Gas.HoareG fork (At CODE message 6613 (a :: rest) M gas state substate)
      (At CODE message 6622 (isZero (isZero (isZero (lessThan
          (storageAt state message.currentTarget 1) a))) :: a :: rest) M (gas - (19 + slotCost c1))
        (readSlot state message.currentTarget 1) (accessSlot substate message.currentTarget 1)) := by
  step jumpdestR
  step dupR 0
  step pushR 1 (0x01 : U256)
  step Gas.sloadG hfork (cold := c1) (by code_fact) (by code_fact) hc1 (by gas_ok)
  step binR 0x10 Local.instruction_lt
  step unR 0x15 instruction_iszero
  step unR 0x15 instruction_iszero
  step unR 0x15 instruction_iszero
  exact restate (by decide) rfl rfl (by gas_ok) rfl rfl

/-- At 6630, the second `require` of redeem: `balances[owner] >= amount`. -/
theorem redeemTest2 (hfork : .berlin ≤ fork) {a : U256} {rest : List U256}
    (hrest : rest.length ≤ 16) {M : ByteArray} (hM : M.size = 96)
    (hc0 : coldIn substate message.currentTarget 0 = false) {cO : Bool}
    (hcO : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget
      (ownerBal state message.currentTarget) = cO) {gas : Nat}
    (hg : 245 + slotCost cO ≤ gas) :
    Gas.HoareG fork (At CODE message 6630 (a :: rest) M gas state substate)
      (At CODE message 6733 (isZero (isZero (isZero (lessThan
          (storageAt state message.currentTarget (ownerBal state message.currentTarget)) a))) ::
          a :: rest)
        (mapMem M (ownerOf state message.currentTarget) 2) (gas - (245 + slotCost cO))
        (readSlot (readSlot state message.currentTarget 0) message.currentTarget
          (ownerBal state message.currentTarget))
        (accessSlot (accessSlot substate message.currentTarget 0) message.currentTarget
          (ownerBal state message.currentTarget))) := by
  step jumpdestR
  step dupR 0
  step ownerLookup hfork (by decide) (by simp; omega) hM hc0 (gas := gas - 1 - 3) (by gas_ok)
  step Gas.sloadG hfork (cold := cO) (by code_fact) (by code_fact) hcO (by gas_ok)
  rw [getStorage_eq, storageAt_readSlot]
  step binR 0x10 Local.instruction_lt
  step unR 0x15 instruction_iszero
  step unR 0x15 instruction_iszero
  step unR 0x15 instruction_iszero
  exact restate (by decide) rfl rfl (by gas_ok) rfl rfl

end UsdtVerify.Issue
