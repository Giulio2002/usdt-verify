import UsdtVerify.Usdt.Proofs.Fee
import UsdtVerify.Usdt.Proofs.Issue

/-!
# issue(uint256) and redeem(uint256): the specifications from pc 0

Write `C` for the contract, `a` for argument word 0 (the amount), `T` for slot 1
(`_totalSupply`), `O = keccak(owner ++ 2)` for the slot of `balances[owner]` (`ownerBal`), `B`
for its word.

- `spec_issue_notOwner` / `spec_redeem_notOwner`: a caller other than the owner gets a revert.
- `spec_issue_req1`: `T + a ≤ T` as EVM words (`a = 0`, or `T + a ≥ 2^256`) ⇒ REVERT.
  `spec_issue_req2`: the first passes, `B + a ≤ B` as words ⇒ REVERT.
- `spec_redeem_req1`: `T < a` ⇒ REVERT. `spec_redeem_req2`: `T ≥ a`, `B < a` ⇒ REVERT.
- `spec_issue`: both pass ⇒ STOP; `O := B + a`, then `slot 1 := T' + a` (`T'` read after the
  first write); log `Issue(a)`. `spec_redeem`: both pass ⇒ STOP; `slot 1 := T - a`, then
  `O := B' - a` (`B'` read after the first write); log `Redeem(a)`. `issue_effects` /
  `redeem_effects`: with `O ≠ 1`, the new words are `B + a` and `T + a` (resp. `B - a`, `T - a`)
  as numbers, without wrap-around.
-/

namespace UsdtVerify.IssueSpec

open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts
open Transfer TransferOk Owner Admin BlackList Issue

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate}

/-- The entry of a function with one word argument (issue, redeem): the value check, then a
jump to the body `b` with argument word 0 and the return address `r`. -/
theorem entryW {e r b : Nat} (hp : (e = 1976 ∧ r = 0x07d9 ∧ b = 6019) ∨
      (e = 2011 ∧ r = 0x07fc ∧ b = 6522))
    (hv : message.value = 0) {x : U256} {M : ByteArray} {gas : Nat} (hg : 68 ≤ gas) :
    Gas.HoareG fork (At CODE message e [x] M gas state substate)
      (At CODE message b [wordArg message.data 0, BitVec.ofNat 256 r, x] M (gas - 68) state
        substate) := by
  rcases hp with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  all_goals
    step jumpdestR
    step Gas.callvalueG (by code_fact) (by code_fact) (by gas_ok) (by stk_ok)
    step unR 0x15 instruction_iszero
    step pushAnyR 2
    step jumpiR (by simp [hv, isZero])
    step jumpdestR
    step pushAnyR 2
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
    step popR
    step popR
    step pushAnyR 2
    step jumpR
    exact restate (by decide) (congrArg (wordArg message.data 0 :: · :: [x]) (by decide)) rfl
      (by gas_ok) rfl rfl

/-- From pc 0 to the owner check of issue (`i = 0`) or redeem (`i = 1`). -/
theorem toBodyW {sel e r b t : Nat}
    (hp : (sel = 0xcc872b66 ∧ e = 1976 ∧ r = 0x07d9 ∧ b = 6019 ∧ t = 24) ∨
      (sel = 0xdb006a75 ∧ e = 2011 ∧ r = 0x07fc ∧ b = 6522 ∧ t = 25))
    (hsize : 4 ≤ message.data.size) (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = sel) (hv : message.value = 0) {gas : Nat}
    (hg : 137 + 22 * t ≤ gas) :
    Gas.HoareG fork (At CODE message 0 [] .empty gas state substate)
      (At CODE message (b + 4) [0, 0, wordArg message.data 0, BitVec.ofNat 256 r,
          BitVec.ofNat 256 (selector message.data)]
        MEM0 (gas - (137 + 22 * t)) state substate) := by
  have ht : tested (BitVec.ofNat 256 (selector message.data)) ENTRIES = t ∧
      branch (BitVec.ofNat 256 (selector message.data)) 54 (entrySize 4 2) ENTRIES = e := by
    rw [hsel]
    rcases hp with ⟨rfl, rfl, -, -, rfl⟩ | ⟨rfl, rfl, -, -, rfl⟩ <;> decide
  have h1 := dispatch (state := state) (substate := substate) hsize hsize' (gas := gas)
    (by rw [ht.1]; omega)
  rw [ht.1, ht.2] at h1
  refine h1.seq ?_
  have hb : b ∈ BODIES := by
    rcases hp with ⟨-, -, -, rfl, -⟩ | ⟨-, -, -, rfl, -⟩ <;> decide
  have he : (e = 1976 ∧ r = 0x07d9 ∧ b = 6019) ∨ (e = 2011 ∧ r = 0x07fc ∧ b = 6522) := by
    rcases hp with ⟨-, h1, h2, h3, -⟩ | ⟨-, h1, h2, h3, -⟩
    · exact Or.inl ⟨h1, h2, h3⟩
    · exact Or.inr ⟨h1, h2, h3⟩
  refine (entryW he hv (by omega)).seq ?_
  refine (prefix9 hb (by simp) (by omega)).seq ?_
  exact restate rfl rfl rfl (by omega) rfl rfl

/-- `issue(a)` / `redeem(a)` from a caller other than the owner reverts with no output. -/
theorem spec_issue_notOwner (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xcc872b66)
    (hv : message.value = 0) (hown : callerWord message ≠ ownerOf state message.currentTarget)
    {c0 : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0) {gas : Nat}
    (hg : 740 + slotCost c0 ≤ gas) :
    Gas.SpecG fork (At CODE message 0 [] .empty gas state substate)
      (Halted true .empty (gas - (740 + slotCost c0)) (readSlot state message.currentTarget 0)
        (accessSlot substate message.currentTarget 0)) := by
  refine Gas.SpecG.seq (toBodyW (Or.inl ⟨rfl, rfl, rfl, rfl, rfl⟩) hsize hsize' hsel hv (by omega)) ?_
  refine (ownerRevert hfork (mem_CHECKS (by decide)) (by simp) size_MEM0 hc0 hown
    (by gas_ok)).consequence (fun _ h => h) ?_
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  exact ⟨hr, he, ho, by rw [hgas]; gas_ok, hs, hss⟩

theorem spec_redeem_notOwner (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xdb006a75)
    (hv : message.value = 0) (hown : callerWord message ≠ ownerOf state message.currentTarget)
    {c0 : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0) {gas : Nat}
    (hg : 762 + slotCost c0 ≤ gas) :
    Gas.SpecG fork (At CODE message 0 [] .empty gas state substate)
      (Halted true .empty (gas - (762 + slotCost c0)) (readSlot state message.currentTarget 0)
        (accessSlot substate message.currentTarget 0)) := by
  refine Gas.SpecG.seq (toBodyW (Or.inr ⟨rfl, rfl, rfl, rfl, rfl⟩) hsize hsize' hsel hv (by omega)) ?_
  refine (ownerRevert hfork (mem_CHECKS (by decide)) (by simp) size_MEM0 hc0 hown
    (by gas_ok)).consequence (fun _ h => h) ?_
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  exact ⟨hr, he, ho, by rw [hgas]; gas_ok, hs, hss⟩

/-- The test of `x + a > x` as EVM words is nonzero exactly when `0 < a` and `x + a < 2^256`. -/
theorem gtAdd_ne {x a : U256} (h : 0 < a.toNat ∧ x.toNat + a.toNat < 2 ^ 256) :
    isZero (isZero (greaterThan (add x a) x)) ≠ 0 := by
  have hadd : (add x a).toNat = x.toNat + a.toNat := by
    simp only [add, BitVec.toNat_add]; exact Nat.mod_eq_of_lt h.2
  have hgt : (add x a).toNat > x.toNat := by omega
  simp [greaterThan, hgt, isZero]

theorem gtAdd_eq {x a : U256} (h : ¬ (0 < a.toNat ∧ x.toNat + a.toNat < 2 ^ 256)) :
    isZero (isZero (greaterThan (add x a) x)) = 0 := by
  have hng : ¬ (add x a).toNat > x.toNat := by
    simp only [add, BitVec.toNat_add]
    have := x.isLt
    have := a.isLt
    by_cases hlt : x.toNat + a.toNat < 2 ^ 256
    · rw [Nat.mod_eq_of_lt hlt]; omega
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]; omega
  simp [greaterThan, hng, isZero]

/-- The test of `x >= a` (`!(x < a)`) as the code computes it. -/
theorem ge_ne {x a : U256} (h : a.toNat ≤ x.toNat) : isZero (isZero (isZero (lessThan x a))) ≠ 0 := by
  have : ¬ x.toNat < a.toNat := by omega
  simp [lessThan, this, isZero]

theorem ge_eq {x a : U256} (h : x.toNat < a.toNat) : isZero (isZero (isZero (lessThan x a))) = 0 := by
  simp [lessThan, h, isZero]

theorem ownerBal_readSlot (st : State.TransactionState) (t c : EthLib.Base.Address) (n : U256) :
    ownerBal (readSlot st t n) c = ownerBal st c := by
  simp only [ownerBal, ownerOf, storageAt_readSlot]

theorem ownerOf_readSlot (st : State.TransactionState) (t c : EthLib.Base.Address) (n : U256) :
    ownerOf (readSlot st t n) c = ownerOf st c := by
  simp only [ownerOf, storageAt_readSlot]

/-- `issue(a)` by the owner when `T + a > T` fails as EVM words (`a = 0` or `T + a ≥ 2^256`):
REVERT with no output, after reading slots 0 and 1. -/
theorem spec_issue_req1 (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xcc872b66)
    (hv : message.value = 0) (hown : callerWord message = ownerOf state message.currentTarget)
    (hT : ¬ (0 < (wordArg message.data 0).toNat ∧
      (storageAt state message.currentTarget 1).toNat + (wordArg message.data 0).toNat < 2 ^ 256))
    {c0 c1 : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hc1 : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget 1 = c1)
    {gas : Nat} (hg : 875 + slotCost c0 + slotCost c1 ≤ gas) :
    Gas.SpecG fork (At CODE message 0 [] .empty gas state substate)
      (Halted true .empty (gas - (875 + slotCost c0 + slotCost c1))
        (readSlot (readSlot state message.currentTarget 0) message.currentTarget 1)
        (accessSlot (accessSlot substate message.currentTarget 0) message.currentTarget 1)) := by
  refine Gas.SpecG.seq (toBodyW (Or.inl ⟨rfl, rfl, rfl, rfl, rfl⟩) hsize hsize' hsel hv (by omega)) ?_
  step ownerOk hfork (mem_CHECKS (by decide)) (by simp) hc0 hown (by gas_ok)
  at_pc 6110
  step issueTest1 hfork (by simp) hc1 (by gas_ok)
  rw [storageAt_readSlot]
  refine (reqRevert hfork (Or.inl rfl) (gtAdd_eq hT) (by simp) size_MEM0
    (by gas_ok)).consequence (fun _ h => h) ?_
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  exact ⟨hr, he, ho, by rw [hgas]; gas_ok, hs, hss⟩

/-- `redeem(a)` by the owner when `T < a`: REVERT with no output, after reading slots 0 and 1. -/
theorem spec_redeem_req1 (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xdb006a75)
    (hv : message.value = 0) (hown : callerWord message = ownerOf state message.currentTarget)
    (hT : (storageAt state message.currentTarget 1).toNat < (wordArg message.data 0).toNat)
    {c0 c1 : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hc1 : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget 1 = c1)
    {gas : Nat} (hg : 794 + slotCost c0 + slotCost c1 ≤ gas) :
    Gas.SpecG fork (At CODE message 0 [] .empty gas state substate)
      (Halted true .empty (gas - (794 + slotCost c0 + slotCost c1))
        (readSlot (readSlot state message.currentTarget 0) message.currentTarget 1)
        (accessSlot (accessSlot substate message.currentTarget 0) message.currentTarget 1)) := by
  refine Gas.SpecG.seq (toBodyW (Or.inr ⟨rfl, rfl, rfl, rfl, rfl⟩) hsize hsize' hsel hv (by omega)) ?_
  step ownerOk hfork (mem_CHECKS (by decide)) (by simp) hc0 hown (by gas_ok)
  at_pc 6613
  step redeemTest1 hfork (by simp) hc1 (by gas_ok)
  rw [storageAt_readSlot]
  refine (reqRevert hfork (Or.inr (Or.inr (Or.inl rfl))) (ge_eq hT) (by simp) size_MEM0
    (by gas_ok)).consequence (fun _ h => h) ?_
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  exact ⟨hr, he, ho, by rw [hgas]; gas_ok, hs, hss⟩

/-- The reads of the two `require`s of issue / redeem: slots 0, 1, 0 and `O`. -/
abbrev reqState (state : State.TransactionState) (c : EthLib.Base.Address) :
    State.TransactionState :=
  readSlot (readSlot (readSlot state c 0) c 1) c (ownerBal state c)

abbrev reqSub (substate : Substate) (state : State.TransactionState) (c : EthLib.Base.Address) :
    Substate :=
  accessSlot (accessSlot (accessSlot substate c 0) c 1) c (ownerBal state c)

/-- From pc 0 to 6338 (issue) or 6741 (redeem), with both `require`s passing, or to the JUMPI of
the second `require`. -/
theorem issuePre (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xcc872b66)
    (hv : message.value = 0) (hown : callerWord message = ownerOf state message.currentTarget)
    (hT : 0 < (wordArg message.data 0).toNat ∧
      (storageAt state message.currentTarget 1).toNat + (wordArg message.data 0).toNat < 2 ^ 256)
    {c0 c1 cO : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hc1 : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget 1 = c1)
    (hcO : coldIn (accessSlot (accessSlot substate message.currentTarget 0) message.currentTarget 1)
      message.currentTarget (ownerBal state message.currentTarget) = cO)
    {gas : Nat} (hg : 1443 + slotCost c0 + slotCost c1 + slotCost cO ≤ gas) :
    Gas.HoareG fork (At CODE message 0 [] .empty gas state substate)
      (At CODE message 6330 (isZero (isZero (greaterThan
          (add (storageAt state message.currentTarget (ownerBal state message.currentTarget))
            (wordArg message.data 0))
          (storageAt state message.currentTarget (ownerBal state message.currentTarget)))) ::
          wordArg message.data 0 :: [BitVec.ofNat 256 0x07d9,
            BitVec.ofNat 256 (selector message.data)])
        (mapMem (mapMem MEM0 (ownerOf state message.currentTarget) 2)
          (ownerOf state message.currentTarget) 2)
        (gas - (1443 + slotCost c0 + slotCost c1 + slotCost cO))
        (reqState state message.currentTarget) (reqSub substate state message.currentTarget)) := by
  refine (toBodyW (Or.inl ⟨rfl, rfl, rfl, rfl, rfl⟩) hsize hsize' hsel hv (by omega)).seq ?_
  step ownerOk hfork (mem_CHECKS (by decide)) (by simp) hc0 hown (by gas_ok)
  at_pc 6110
  step issueTest1 hfork (by simp) hc1 (by gas_ok)
  rw [storageAt_readSlot]
  step reqPass (Or.inl ⟨rfl, rfl⟩) (gtAdd_ne hT) (by simp) (by gas_ok)
  step issueTest2 hfork (cO := cO) (by simp) size_MEM0 (TransferFrom.coldIn_accessSlot_false
    (coldIn_accessSlot_self _ _ _)) (by rw [accessSlot_0n0, ownerBal_readSlot, ownerBal_readSlot]; exact hcO)
    (by gas_ok)
  simp only [ownerBal_readSlot, ownerOf_readSlot, storageAt_readSlot, readSlot_0n0, accessSlot_0n0]
  exact restate rfl rfl rfl (by gas_ok) rfl rfl

/-- `issue(a)` by the owner when the first `require` passes and `B + a > B` fails as EVM words:
REVERT with no output. -/
theorem spec_issue_req2 (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xcc872b66)
    (hv : message.value = 0) (hown : callerWord message = ownerOf state message.currentTarget)
    (hT : 0 < (wordArg message.data 0).toNat ∧
      (storageAt state message.currentTarget 1).toNat + (wordArg message.data 0).toNat < 2 ^ 256)
    (hB : ¬ (0 < (wordArg message.data 0).toNat ∧
      (storageAt state message.currentTarget (ownerBal state message.currentTarget)).toNat +
        (wordArg message.data 0).toNat < 2 ^ 256))
    {c0 c1 cO : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hc1 : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget 1 = c1)
    (hcO : coldIn (accessSlot (accessSlot substate message.currentTarget 0) message.currentTarget 1)
      message.currentTarget (ownerBal state message.currentTarget) = cO)
    {gas : Nat} (hg : 1462 + slotCost c0 + slotCost c1 + slotCost cO ≤ gas) :
    Gas.SpecG fork (At CODE message 0 [] .empty gas state substate)
      (Halted true .empty (gas - (1462 + slotCost c0 + slotCost c1 + slotCost cO))
        (reqState state message.currentTarget) (reqSub substate state message.currentTarget)) := by
  refine Gas.SpecG.seq (issuePre hfork hsize hsize' hsel hv hown hT hc0 hc1 hcO (by omega)) ?_
  refine (reqRevert hfork (Or.inr (Or.inl rfl)) (gtAdd_eq hB) (by simp)
    (size_mapMem (size_mapMem size_MEM0 _ _) _ _) (by gas_ok)).consequence (fun _ h => h) ?_
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  exact ⟨hr, he, ho, by rw [hgas]; gas_ok, hs, hss⟩

/-- The state after `balances[owner] += a` in issue. -/
abbrev issueState1 (state : State.TransactionState) (message : Message fork) :
    State.TransactionState :=
  writeSlot (readSlot (reqState state message.currentTarget) message.currentTarget 0)
    message.currentTarget (ownerBal state message.currentTarget)
    (add (storageAt state message.currentTarget (ownerBal state message.currentTarget))
      (wordArg message.data 0))

/-- The state at the end of issue: then `_totalSupply += a`, read after the first write. -/
abbrev issueState (state : State.TransactionState) (message : Message fork) :
    State.TransactionState :=
  writeSlot (issueState1 state message) message.currentTarget 1
    (add (storageAt (issueState1 state message) message.currentTarget 1) (wordArg message.data 0))

/-- The price of the write of `balances[owner]` in issue (the slot is warm). -/
abbrev issueCostO (fork : Fork) (state : State.TransactionState) (message : Message fork) : Nat :=
  Gas.writeCost fork (originalAt state message.currentTarget (ownerBal state message.currentTarget))
    (storageAt state message.currentTarget (ownerBal state message.currentTarget))
    (add (storageAt state message.currentTarget (ownerBal state message.currentTarget))
      (wordArg message.data 0)) false

/-- The price of the write of `_totalSupply` in issue (the slot is warm). -/
abbrev issueCostT (fork : Fork) (state : State.TransactionState) (message : Message fork) : Nat :=
  Gas.writeCost fork (originalAt state message.currentTarget 1)
    (storageAt (issueState1 state message) message.currentTarget 1)
    (add (storageAt (issueState1 state message) message.currentTarget 1) (wordArg message.data 0))
    false

/-- The substate at the end of issue: both writes (accesses, refunds) and the log `Issue(a)`. -/
abbrev issueSub (fork : Fork) (substate : Substate) (state : State.TransactionState)
    (message : Message fork) : Substate :=
  { storeSub fork (storeSub fork (accessSlot (reqSub substate state message.currentTarget)
        message.currentTarget 0) message.currentTarget (ownerBal state message.currentTarget)
        (originalAt state message.currentTarget (ownerBal state message.currentTarget))
        (storageAt state message.currentTarget (ownerBal state message.currentTarget))
        (add (storageAt state message.currentTarget (ownerBal state message.currentTarget))
          (wordArg message.data 0)))
      message.currentTarget 1 (originalAt state message.currentTarget 1)
      (storageAt (issueState1 state message) message.currentTarget 1)
      (add (storageAt (issueState1 state message) message.currentTarget 1)
        (wordArg message.data 0)) with
    logs := substate.logs.push (log1W message.currentTarget ISSUE_TOPIC (wordArg message.data 0)) }

/-- The specification of a successful `issue(a)`.

Hypotheses: Berlin ≤ fork (Glamsterdam included); a frame that may write, of an existing account `C`;
call data of 4 to 2^256 - 1 bytes with selector 0xcc872b66; no value; the caller is the owner;
`0 < a` and `T + a < 2^256`; `B + a < 2^256` (`B` the word of `balances[owner]`); enough gas,
and more than 2300 left at each SSTORE.

Then the run stops normally: `balances[owner] := B + a`, then `_totalSupply := T' + a` (`T'` read
after the first write; `T' = T` unless the two slots coincide, see `issue_effects`); one log
`Issue(a)` (topic 0xcb8241ad…, data the word `a`). Gas left:
`gas - (3024 + prices of the reads of slots 0, 1, O + prices of the two writes)`. -/
theorem spec_issue (hfork : .berlin ≤ fork)
    (hstatic : message.isStatic = false) (hacc : hasAccount state message.currentTarget)
    (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xcc872b66)
    (hv : message.value = 0) (hown : callerWord message = ownerOf state message.currentTarget)
    (hT : 0 < (wordArg message.data 0).toNat ∧
      (storageAt state message.currentTarget 1).toNat + (wordArg message.data 0).toNat < 2 ^ 256)
    (hB : (storageAt state message.currentTarget (ownerBal state message.currentTarget)).toNat +
        (wordArg message.data 0).toNat < 2 ^ 256)
    {c0 c1 cO : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hc1 : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget 1 = c1)
    (hcO : coldIn (accessSlot (accessSlot substate message.currentTarget 0) message.currentTarget 1)
      message.currentTarget (ownerBal state message.currentTarget) = cO)
    {gas : Nat}
    (hstip : 4248 + slotCost c0 + slotCost c1 + slotCost cO + issueCostO fork state message ≤ gas)
    (hg : 3024 + slotCost c0 + slotCost c1 + slotCost cO + issueCostO fork state message +
      issueCostT fork state message ≤ gas) :
    Gas.SpecG fork (At CODE message 0 [] .empty gas state substate)
      (Halted false .empty (gas - (3024 + slotCost c0 + slotCost c1 + slotCost cO +
          issueCostO fork state message + issueCostT fork state message))
        (issueState state message) (issueSub fork substate state message)) := by
  simp only [issueCostO, issueCostT, issueState1] at hstip hg ⊢
  have hacc1 : hasAccount (readSlot (reqState state message.currentTarget) message.currentTarget 0)
      message.currentTarget :=
    hasAccount_readSlot (hasAccount_readSlot (hasAccount_readSlot (hasAccount_readSlot hacc)))
  have hacc2 : hasAccount (reqState state message.currentTarget) message.currentTarget :=
    hasAccount_readSlot (hasAccount_readSlot (hasAccount_readSlot hacc))
  have hw0 : coldIn (reqSub substate state message.currentTarget) message.currentTarget 0 =
      false :=
    TransferFrom.coldIn_accessSlot_false (TransferFrom.coldIn_accessSlot_false
      (coldIn_accessSlot_self _ _ _))
  have hwO : coldIn (reqSub substate state message.currentTarget) message.currentTarget
      (ownerBal (reqState state message.currentTarget) message.currentTarget) = false := by
    rw [ownerBal_readSlot, ownerBal_readSlot, ownerBal_readSlot]
    exact coldIn_accessSlot_self _ _ _
  have hw1 : coldIn (storeSub fork (accessSlot (reqSub substate state message.currentTarget)
      message.currentTarget 0) message.currentTarget (ownerBal state message.currentTarget)
      (originalAt state message.currentTarget (ownerBal state message.currentTarget))
      (storageAt state message.currentTarget (ownerBal state message.currentTarget))
      (add (storageAt state message.currentTarget (ownerBal state message.currentTarget))
        (wordArg message.data 0))) message.currentTarget 1 = false :=
    TransferFee.coldIn_storeSub_false (TransferFrom.coldIn_accessSlot_false
      (TransferFrom.coldIn_accessSlot_false (coldIn_accessSlot_self _ _ _)))
  refine Gas.SpecG.seq (issuePre hfork hsize hsize' hsel hv hown hT hc0 hc1 hcO (by omega)) ?_
  step reqPass (Or.inr (Or.inl ⟨rfl, rfl⟩)) (gtAdd_ne ⟨hT.1, hB⟩) (by simp) (by gas_ok)
  step issueOwner hfork (by simp) hstatic hacc2 hw0 hwO
    (size_mapMem (size_mapMem size_MEM0 _ _) _ _) (by gas_ok)
    (by simp only [ownerBal_readSlot, storageAt_readSlot, originalAt_readSlot]; gas_ok)
  simp only [ownerBal_readSlot, ownerOf_readSlot, storageAt_readSlot, originalAt_readSlot]
  step issueTotal hfork (by simp) hstatic (hasAccount_writeSlot hacc1) hw1 (by gas_ok)
    (by rw [originalAt_writeSlot hacc1, originalAt_readSlot, originalAt_readSlot,
      originalAt_readSlot, originalAt_readSlot]; gas_ok)
  rw [originalAt_writeSlot hacc1, originalAt_readSlot, originalAt_readSlot,
      originalAt_readSlot, originalAt_readSlot]
  refine (amountLog (Or.inl ⟨rfl, rfl, rfl⟩) hstatic
    (size_mapMem (size_mapMem (size_mapMem size_MEM0 _ _) _ _) _ _)
    (ptr_mapMem (size_mapMem (size_mapMem size_MEM0 _ _) _ _)
      (ptr_mapMem (size_mapMem size_MEM0 _ _) (ptr_mapMem size_MEM0 mload_MEM0 _ _) _ _) _ _)
    (by gas_ok)).consequence (fun _ h => h) ?_
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  exact ⟨hr, he, ho, by rw [hgas]; gas_ok, hs, hss⟩

/-- `issue(a)` by the owner, with both `require`s passing, in a static frame or with no account
for `C`: the run reaches the `SSTORE` of `balances[owner]`, which is `Stuck`. -/
theorem bad_issue (hfork : .berlin ≤ fork)
    (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xcc872b66)
    (hv : message.value = 0) (hown : callerWord message = ownerOf state message.currentTarget)
    (hT : 0 < (wordArg message.data 0).toNat ∧
      (storageAt state message.currentTarget 1).toNat + (wordArg message.data 0).toNat < 2 ^ 256)
    (hB : (storageAt state message.currentTarget (ownerBal state message.currentTarget)).toNat +
        (wordArg message.data 0).toNat < 2 ^ 256)
    {c0 c1 cO : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hc1 : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget 1 = c1)
    (hcO : coldIn (accessSlot (accessSlot substate message.currentTarget 0) message.currentTarget 1)
      message.currentTarget (ownerBal state message.currentTarget) = cO)
    {gas : Nat} (hbad : Gas.NoWrite message state (gas - (1814 + slotCost c0 + slotCost c1 + slotCost cO)))
    (hg : 1814 + slotCost c0 + slotCost c1 + slotCost cO ≤ gas) :
    Gas.HoareG fork (At CODE message 0 [] .empty gas state substate) Gas.Stuck := by
  have hw0 : coldIn (reqSub substate state message.currentTarget) message.currentTarget 0 =
      false :=
    TransferFrom.coldIn_accessSlot_false (TransferFrom.coldIn_accessSlot_false
      (coldIn_accessSlot_self _ _ _))
  have hwO : coldIn (reqSub substate state message.currentTarget) message.currentTarget
      (ownerBal (reqState state message.currentTarget) message.currentTarget) = false := by
    rw [ownerBal_readSlot, ownerBal_readSlot, ownerBal_readSlot]
    exact coldIn_accessSlot_self _ _ _
  refine Triple.seq (issuePre hfork hsize hsize' hsel hv hown hT hc0 hc1 hcO (by omega)) ?_
  step reqPass (Or.inr (Or.inl ⟨rfl, rfl⟩)) (gtAdd_ne ⟨hT.1, hB⟩) (by simp) (by gas_ok)
  refine issueOwnerBad (state := reqState state message.currentTarget) hfork ?_ hw0 hwO
    (size_mapMem (size_mapMem size_MEM0 _ _) _ _) (hbad.le ?_) ?_
  · simp
  · gas_ok
  · gas_ok

/-- `issue(a)` by the owner, both `require`s passing, a frame that may write and an account for
`C`, with more than 2300 gas left at the `SSTORE` of `balances[owner]` but at most 2300 at the
`SSTORE` of `_totalSupply` (`hlow`): the run reaches the second one, which is `Stuck`. -/
theorem low_issue2 (hfork : .berlin ≤ fork)
    (hstatic : message.isStatic = false) (hacc : hasAccount state message.currentTarget)
    (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xcc872b66)
    (hv : message.value = 0) (hown : callerWord message = ownerOf state message.currentTarget)
    (hT : 0 < (wordArg message.data 0).toNat ∧
      (storageAt state message.currentTarget 1).toNat + (wordArg message.data 0).toNat < 2 ^ 256)
    (hB : (storageAt state message.currentTarget (ownerBal state message.currentTarget)).toNat +
        (wordArg message.data 0).toNat < 2 ^ 256)
    {c0 c1 cO : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hc1 : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget 1 = c1)
    (hcO : coldIn (accessSlot (accessSlot substate message.currentTarget 0) message.currentTarget 1)
      message.currentTarget (ownerBal state message.currentTarget) = cO)
    {gas : Nat} (hstip : 4115 + slotCost c0 + slotCost c1 + slotCost cO ≤ gas)
    (hg : 1947 + slotCost c0 + slotCost c1 + slotCost cO + issueCostO fork state message ≤ gas)
    (hlow : gas < 4248 + slotCost c0 + slotCost c1 + slotCost cO + issueCostO fork state message) :
    Gas.HoareG fork (At CODE message 0 [] .empty gas state substate) Gas.Stuck := by
  simp only [issueCostO] at hg hlow
  have hacc2 : hasAccount (reqState state message.currentTarget) message.currentTarget :=
    hasAccount_readSlot (hasAccount_readSlot (hasAccount_readSlot hacc))
  have hw0 : coldIn (reqSub substate state message.currentTarget) message.currentTarget 0 =
      false :=
    TransferFrom.coldIn_accessSlot_false (TransferFrom.coldIn_accessSlot_false
      (coldIn_accessSlot_self _ _ _))
  have hwO : coldIn (reqSub substate state message.currentTarget) message.currentTarget
      (ownerBal (reqState state message.currentTarget) message.currentTarget) = false := by
    rw [ownerBal_readSlot, ownerBal_readSlot, ownerBal_readSlot]
    exact coldIn_accessSlot_self _ _ _
  have hw1 : coldIn (storeSub fork (accessSlot (reqSub substate state message.currentTarget)
      message.currentTarget 0) message.currentTarget (ownerBal state message.currentTarget)
      (originalAt state message.currentTarget (ownerBal state message.currentTarget))
      (storageAt state message.currentTarget (ownerBal state message.currentTarget))
      (add (storageAt state message.currentTarget (ownerBal state message.currentTarget))
        (wordArg message.data 0))) message.currentTarget 1 = false :=
    TransferFee.coldIn_storeSub_false (TransferFrom.coldIn_accessSlot_false
      (TransferFrom.coldIn_accessSlot_false (coldIn_accessSlot_self _ _ _)))
  refine Triple.seq (issuePre hfork hsize hsize' hsel hv hown hT hc0 hc1 hcO (by omega)) ?_
  step reqPass (Or.inr (Or.inl ⟨rfl, rfl⟩)) (gtAdd_ne ⟨hT.1, hB⟩) (by simp) (by gas_ok)
  step issueOwner hfork (by simp) hstatic hacc2 hw0 hwO
    (size_mapMem (size_mapMem size_MEM0 _ _) _ _) (by gas_ok)
    (by simp only [ownerBal_readSlot, storageAt_readSlot, originalAt_readSlot]; gas_ok)
  simp only [ownerBal_readSlot, ownerOf_readSlot, storageAt_readSlot, originalAt_readSlot]
  refine issueTotalBad hfork (by simp) hw1 (.of_low hfork ?_) ?_
  · gas_ok
  · gas_ok

/-- From pc 0 to the JUMPI of redeem's second `require`. -/
theorem redeemPre (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xdb006a75)
    (hv : message.value = 0) (hown : callerWord message = ownerOf state message.currentTarget)
    (hT : (wordArg message.data 0).toNat ≤ (storageAt state message.currentTarget 1).toNat)
    {c0 c1 cO : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hc1 : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget 1 = c1)
    (hcO : coldIn (accessSlot (accessSlot substate message.currentTarget 0) message.currentTarget 1)
      message.currentTarget (ownerBal state message.currentTarget) = cO)
    {gas : Nat} (hg : 1033 + slotCost c0 + slotCost c1 + slotCost cO ≤ gas) :
    Gas.HoareG fork (At CODE message 0 [] .empty gas state substate)
      (At CODE message 6733 (isZero (isZero (isZero (lessThan
          (storageAt state message.currentTarget (ownerBal state message.currentTarget))
          (wordArg message.data 0)))) ::
          wordArg message.data 0 :: [BitVec.ofNat 256 0x07fc,
            BitVec.ofNat 256 (selector message.data)])
        (mapMem MEM0 (ownerOf state message.currentTarget) 2)
        (gas - (1033 + slotCost c0 + slotCost c1 + slotCost cO))
        (reqState state message.currentTarget) (reqSub substate state message.currentTarget)) := by
  refine (toBodyW (Or.inr ⟨rfl, rfl, rfl, rfl, rfl⟩) hsize hsize' hsel hv (by omega)).seq ?_
  step ownerOk hfork (mem_CHECKS (by decide)) (by simp) hc0 hown (by gas_ok)
  at_pc 6613
  step redeemTest1 hfork (by simp) hc1 (by gas_ok)
  rw [storageAt_readSlot]
  step reqPass (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))) (ge_ne hT) (by simp) (by gas_ok)
  step redeemTest2 hfork (cO := cO) (by simp) size_MEM0 (TransferFrom.coldIn_accessSlot_false
    (coldIn_accessSlot_self _ _ _))
    (by rw [accessSlot_0n0, ownerBal_readSlot, ownerBal_readSlot]; exact hcO) (by gas_ok)
  simp only [ownerBal_readSlot, ownerOf_readSlot, storageAt_readSlot, readSlot_0n0, accessSlot_0n0]
  exact restate rfl rfl rfl (by gas_ok) rfl rfl

/-- `redeem(a)` by the owner when `T ≥ a` and `B < a`: REVERT with no output. -/
theorem spec_redeem_req2 (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xdb006a75)
    (hv : message.value = 0) (hown : callerWord message = ownerOf state message.currentTarget)
    (hT : (wordArg message.data 0).toNat ≤ (storageAt state message.currentTarget 1).toNat)
    (hB : (storageAt state message.currentTarget (ownerBal state message.currentTarget)).toNat <
      (wordArg message.data 0).toNat)
    {c0 c1 cO : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hc1 : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget 1 = c1)
    (hcO : coldIn (accessSlot (accessSlot substate message.currentTarget 0) message.currentTarget 1)
      message.currentTarget (ownerBal state message.currentTarget) = cO)
    {gas : Nat} (hg : 1052 + slotCost c0 + slotCost c1 + slotCost cO ≤ gas) :
    Gas.SpecG fork (At CODE message 0 [] .empty gas state substate)
      (Halted true .empty (gas - (1052 + slotCost c0 + slotCost c1 + slotCost cO))
        (reqState state message.currentTarget) (reqSub substate state message.currentTarget)) := by
  refine Gas.SpecG.seq (redeemPre hfork hsize hsize' hsel hv hown hT hc0 hc1 hcO (by omega)) ?_
  refine (reqRevert hfork (Or.inr (Or.inr (Or.inr rfl))) (ge_eq hB) (by simp)
    (size_mapMem size_MEM0 _ _) (by gas_ok)).consequence (fun _ h => h) ?_
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  exact ⟨hr, he, ho, by rw [hgas]; gas_ok, hs, hss⟩

theorem ownerBal_writeSlot {st : State.TransactionState} {t : EthLib.Base.Address} {n v : U256}
    (h : hasAccount st t) (hn : (0 : U256) ≠ n) : ownerBal (writeSlot st t n v) t = ownerBal st t := by
  simp only [ownerBal, ownerOf, storageAt_writeSlot_of_ne h hn]

theorem ownerOf_writeSlot {st : State.TransactionState} {t : EthLib.Base.Address} {n v : U256}
    (h : hasAccount st t) (hn : (0 : U256) ≠ n) : ownerOf (writeSlot st t n v) t = ownerOf st t := by
  simp only [ownerOf, storageAt_writeSlot_of_ne h hn]

/-- The state after `_totalSupply -= a` in redeem. -/
abbrev redeemState1 (state : State.TransactionState) (message : Message fork) :
    State.TransactionState :=
  writeSlot (reqState state message.currentTarget) message.currentTarget 1
    (sub (storageAt state message.currentTarget 1) (wordArg message.data 0))

/-- The state at the end of redeem: then `balances[owner] -= a`, read after the first write. -/
abbrev redeemState (state : State.TransactionState) (message : Message fork) :
    State.TransactionState :=
  writeSlot (readSlot (redeemState1 state message) message.currentTarget 0) message.currentTarget
    (ownerBal state message.currentTarget)
    (sub (storageAt (redeemState1 state message) message.currentTarget
      (ownerBal state message.currentTarget)) (wordArg message.data 0))

abbrev redeemCostT (fork : Fork) (state : State.TransactionState) (message : Message fork) : Nat :=
  Gas.writeCost fork (originalAt state message.currentTarget 1)
    (storageAt state message.currentTarget 1)
    (sub (storageAt state message.currentTarget 1) (wordArg message.data 0)) false

abbrev redeemCostO (fork : Fork) (state : State.TransactionState) (message : Message fork) : Nat :=
  Gas.writeCost fork (originalAt state message.currentTarget (ownerBal state message.currentTarget))
    (storageAt (redeemState1 state message) message.currentTarget
      (ownerBal state message.currentTarget))
    (sub (storageAt (redeemState1 state message) message.currentTarget
      (ownerBal state message.currentTarget)) (wordArg message.data 0)) false

/-- The substate at the end of redeem: both writes and the log `Redeem(a)`. -/
abbrev redeemSub (fork : Fork) (substate : Substate) (state : State.TransactionState)
    (message : Message fork) : Substate :=
  { storeSub fork (accessSlot (storeSub fork (reqSub substate state message.currentTarget)
        message.currentTarget 1 (originalAt state message.currentTarget 1)
        (storageAt state message.currentTarget 1)
        (sub (storageAt state message.currentTarget 1) (wordArg message.data 0)))
        message.currentTarget 0)
      message.currentTarget (ownerBal state message.currentTarget)
      (originalAt state message.currentTarget (ownerBal state message.currentTarget))
      (storageAt (redeemState1 state message) message.currentTarget
        (ownerBal state message.currentTarget))
      (sub (storageAt (redeemState1 state message) message.currentTarget
        (ownerBal state message.currentTarget)) (wordArg message.data 0)) with
    logs := substate.logs.push (log1W message.currentTarget REDEEM_TOPIC (wordArg message.data 0)) }

/-- The specification of a successful `redeem(a)`: as `spec_issue`, with selector 0xdb006a75,
`a ≤ T` and `a ≤ B`; `_totalSupply := T - a` first, then `balances[owner] := B' - a` (`B'` read
after the first write); log `Redeem(a)` (topic 0x702d5967…); gas left
`gas - (2614 + prices of the reads of slots 0, 1, O + prices of the two writes)`. -/
theorem spec_redeem (hfork : .berlin ≤ fork)
    (hstatic : message.isStatic = false) (hacc : hasAccount state message.currentTarget)
    (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xdb006a75)
    (hv : message.value = 0) (hown : callerWord message = ownerOf state message.currentTarget)
    (hT : (wordArg message.data 0).toNat ≤ (storageAt state message.currentTarget 1).toNat)
    (hB : (wordArg message.data 0).toNat ≤
      (storageAt state message.currentTarget (ownerBal state message.currentTarget)).toNat)
    {c0 c1 cO : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hc1 : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget 1 = c1)
    (hcO : coldIn (accessSlot (accessSlot substate message.currentTarget 0) message.currentTarget 1)
      message.currentTarget (ownerBal state message.currentTarget) = cO)
    {gas : Nat}
    (hstip : 3838 + slotCost c0 + slotCost c1 + slotCost cO + redeemCostT fork state message ≤ gas)
    (hg : 2614 + slotCost c0 + slotCost c1 + slotCost cO + redeemCostT fork state message +
      redeemCostO fork state message ≤ gas) :
    Gas.SpecG fork (At CODE message 0 [] .empty gas state substate)
      (Halted false .empty (gas - (2614 + slotCost c0 + slotCost c1 + slotCost cO +
          redeemCostT fork state message + redeemCostO fork state message))
        (redeemState state message) (redeemSub fork substate state message)) := by
  simp only [redeemCostO, redeemCostT, redeemState1] at hstip hg ⊢
  have hacc2 : hasAccount (reqState state message.currentTarget) message.currentTarget :=
    hasAccount_readSlot (hasAccount_readSlot (hasAccount_readSlot hacc))
  have hacc3 := hasAccount_writeSlot (n := 1)
    (v := sub (storageAt state message.currentTarget 1) (wordArg message.data 0)) hacc2
  have hw1 : coldIn (reqSub substate state message.currentTarget) message.currentTarget 1 =
      false :=
    TransferFrom.coldIn_accessSlot_false (coldIn_accessSlot_self _ _ _)
  have hw0 : coldIn (storeSub fork (reqSub substate state message.currentTarget)
      message.currentTarget 1 (originalAt state message.currentTarget 1)
      (storageAt state message.currentTarget 1)
      (sub (storageAt state message.currentTarget 1) (wordArg message.data 0)))
      message.currentTarget 0 = false :=
    TransferFee.coldIn_storeSub_false (TransferFrom.coldIn_accessSlot_false
      (TransferFrom.coldIn_accessSlot_false (coldIn_accessSlot_self _ _ _)))
  have hwO : coldIn (storeSub fork (reqSub substate state message.currentTarget)
      message.currentTarget 1 (originalAt state message.currentTarget 1)
      (storageAt state message.currentTarget 1)
      (sub (storageAt state message.currentTarget 1) (wordArg message.data 0)))
      message.currentTarget (ownerBal (writeSlot (reqState state message.currentTarget)
        message.currentTarget 1
        (sub (storageAt state message.currentTarget 1) (wordArg message.data 0)))
        message.currentTarget) = false := by
    rw [ownerBal_writeSlot hacc2 (by decide), ownerBal_readSlot, ownerBal_readSlot,
      ownerBal_readSlot]
    exact TransferFee.coldIn_storeSub_false (coldIn_accessSlot_self _ _ _)
  refine Gas.SpecG.seq (redeemPre hfork hsize hsize' hsel hv hown hT hc0 hc1 hcO (by omega)) ?_
  step reqPass (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))) (ge_ne hB) (by simp) (by gas_ok)
  step redeemTotal hfork (by simp) hstatic hacc2 hw1 (by gas_ok)
    (by simp only [storageAt_readSlot, originalAt_readSlot]; gas_ok)
  simp only [storageAt_readSlot, originalAt_readSlot]
  step redeemOwner hfork (by simp) hstatic hacc3 hw0 hwO (size_mapMem size_MEM0 _ _)
    (by gas_ok)
    (by rw [ownerBal_writeSlot hacc2 (by decide), ownerBal_readSlot, ownerBal_readSlot,
      ownerBal_readSlot, originalAt_writeSlot hacc2, originalAt_readSlot, originalAt_readSlot,
      originalAt_readSlot]; gas_ok)
  rw [ownerBal_writeSlot hacc2 (by decide), ownerOf_writeSlot hacc2 (by decide)]
  simp only [ownerBal_readSlot, ownerOf_readSlot]
  rw [originalAt_writeSlot hacc2]
  simp only [originalAt_readSlot]
  refine (amountLog (Or.inr ⟨rfl, rfl, rfl⟩) hstatic
    (size_mapMem (size_mapMem size_MEM0 _ _) _ _)
    (ptr_mapMem (size_mapMem size_MEM0 _ _) (ptr_mapMem size_MEM0 mload_MEM0 _ _) _ _)
    (by gas_ok)).consequence (fun _ h => h) ?_
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  exact ⟨hr, he, ho, by rw [hgas]; gas_ok, hs, hss⟩

/-! ## The end states in plain terms -/

/-- `redeem(a)` by the owner, with both `require`s passing, in a static frame or with no
account for `C`: the run reaches the `SSTORE` of `_totalSupply`, which is `Stuck`. -/
theorem bad_redeem (hfork : .berlin ≤ fork)
    (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xdb006a75)
    (hv : message.value = 0) (hown : callerWord message = ownerOf state message.currentTarget)
    (hT : (wordArg message.data 0).toNat ≤ (storageAt state message.currentTarget 1).toNat)
    (hB : (wordArg message.data 0).toNat ≤
      (storageAt state message.currentTarget (ownerBal state message.currentTarget)).toNat)
    {c0 c1 cO : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hc1 : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget 1 = c1)
    (hcO : coldIn (accessSlot (accessSlot substate message.currentTarget 0) message.currentTarget 1)
      message.currentTarget (ownerBal state message.currentTarget) = cO)
    {gas : Nat} (hbad : Gas.NoWrite message state (gas - (1178 + slotCost c0 + slotCost c1 + slotCost cO)))
    (hg : 1178 + slotCost c0 + slotCost c1 + slotCost cO ≤ gas) :
    Gas.HoareG fork (At CODE message 0 [] .empty gas state substate) Gas.Stuck := by
  have hw1 : coldIn (reqSub substate state message.currentTarget) message.currentTarget 1 =
      false :=
    TransferFrom.coldIn_accessSlot_false (coldIn_accessSlot_self _ _ _)
  refine Triple.seq (redeemPre hfork hsize hsize' hsel hv hown hT hc0 hc1 hcO (by omega)) ?_
  step reqPass (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))) (ge_ne hB) (by simp) (by gas_ok)
  refine redeemTotalBad (state := reqState state message.currentTarget) hfork ?_ hw1 (hbad.le ?_) ?_
  · simp
  · gas_ok
  · gas_ok

/-- `redeem(a)` by the owner, both `require`s passing, a frame that may write and an account for
`C`, with more than 2300 gas left at the `SSTORE` of `_totalSupply` but at most 2300 at the
`SSTORE` of `balances[owner]` (`hlow`): the run reaches the second one, which is `Stuck`. -/
theorem low_redeem2 (hfork : .berlin ≤ fork)
    (hstatic : message.isStatic = false) (hacc : hasAccount state message.currentTarget)
    (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xdb006a75)
    (hv : message.value = 0) (hown : callerWord message = ownerOf state message.currentTarget)
    (hT : (wordArg message.data 0).toNat ≤ (storageAt state message.currentTarget 1).toNat)
    (hB : (wordArg message.data 0).toNat ≤
      (storageAt state message.currentTarget (ownerBal state message.currentTarget)).toNat)
    {c0 c1 cO : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hc1 : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget 1 = c1)
    (hcO : coldIn (accessSlot (accessSlot substate message.currentTarget 0) message.currentTarget 1)
      message.currentTarget (ownerBal state message.currentTarget) = cO)
    {gas : Nat} (hstip : 3479 + slotCost c0 + slotCost c1 + slotCost cO ≤ gas)
    (hg : 1537 + slotCost c0 + slotCost c1 + slotCost cO + redeemCostT fork state message ≤ gas)
    (hlow : gas < 3838 + slotCost c0 + slotCost c1 + slotCost cO + redeemCostT fork state message) :
    Gas.HoareG fork (At CODE message 0 [] .empty gas state substate) Gas.Stuck := by
  simp only [redeemCostT] at hg hlow
  have hacc2 : hasAccount (reqState state message.currentTarget) message.currentTarget :=
    hasAccount_readSlot (hasAccount_readSlot (hasAccount_readSlot hacc))
  have hw1 : coldIn (reqSub substate state message.currentTarget) message.currentTarget 1 =
      false :=
    TransferFrom.coldIn_accessSlot_false (coldIn_accessSlot_self _ _ _)
  have hw0 : coldIn (storeSub fork (reqSub substate state message.currentTarget)
      message.currentTarget 1 (originalAt state message.currentTarget 1)
      (storageAt state message.currentTarget 1)
      (sub (storageAt state message.currentTarget 1) (wordArg message.data 0)))
      message.currentTarget 0 = false :=
    TransferFee.coldIn_storeSub_false (TransferFrom.coldIn_accessSlot_false
      (TransferFrom.coldIn_accessSlot_false (coldIn_accessSlot_self _ _ _)))
  have hwO : coldIn (storeSub fork (reqSub substate state message.currentTarget)
      message.currentTarget 1 (originalAt state message.currentTarget 1)
      (storageAt state message.currentTarget 1)
      (sub (storageAt state message.currentTarget 1) (wordArg message.data 0)))
      message.currentTarget (ownerBal (writeSlot (reqState state message.currentTarget)
        message.currentTarget 1
        (sub (storageAt state message.currentTarget 1) (wordArg message.data 0)))
        message.currentTarget) = false := by
    rw [ownerBal_writeSlot hacc2 (by decide), ownerBal_readSlot, ownerBal_readSlot,
      ownerBal_readSlot]
    exact TransferFee.coldIn_storeSub_false (coldIn_accessSlot_self _ _ _)
  refine Triple.seq (redeemPre hfork hsize hsize' hsel hv hown hT hc0 hc1 hcO (by omega)) ?_
  step reqPass (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))) (ge_ne hB) (by simp) (by gas_ok)
  step redeemTotal hfork (by simp) hstatic hacc2 hw1 (by gas_ok)
    (by simp only [storageAt_readSlot, originalAt_readSlot]; gas_ok)
  simp only [storageAt_readSlot, originalAt_readSlot]
  refine redeemOwnerBad hfork (by simp) hw0 hwO (size_mapMem size_MEM0 _ _)
    (.of_low hfork ?_) ?_
  · gas_ok
  · gas_ok

theorem toNat_add' {x a : U256} (h : x.toNat + a.toNat < 2 ^ 256) : (add x a).toNat = x.toNat + a.toNat := by
  simp only [add, BitVec.toNat_add]; exact Nat.mod_eq_of_lt h

theorem toNat_sub' {x a : U256} (h : a.toNat ≤ x.toNat) : (sub x a).toNat = x.toNat - a.toNat := by
  simp only [sub, BitVec.toNat_sub]
  have := x.isLt
  rw [show 2 ^ 256 - a.toNat + x.toNat = (x.toNat - a.toNat) + 2 ^ 256 by omega,
    Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

/-- After `issue(a)`, when `O ≠ 1`: `balances[owner]` is `B + a` and `_totalSupply` is `T + a`
(as numbers: the `require`s exclude wrap-around), and every other slot is unchanged. -/
theorem issue_effects (hacc : hasAccount state message.currentTarget)
    (hO1 : ownerBal state message.currentTarget ≠ 1)
    (hT : (storageAt state message.currentTarget 1).toNat + (wordArg message.data 0).toNat < 2 ^ 256)
    (hB : (storageAt state message.currentTarget (ownerBal state message.currentTarget)).toNat +
        (wordArg message.data 0).toNat < 2 ^ 256) :
    (storageAt (issueState state message) message.currentTarget
        (ownerBal state message.currentTarget)).toNat =
      (storageAt state message.currentTarget (ownerBal state message.currentTarget)).toNat +
        (wordArg message.data 0).toNat ∧
    (storageAt (issueState state message) message.currentTarget 1).toNat =
      (storageAt state message.currentTarget 1).toNat + (wordArg message.data 0).toNat ∧
    ∀ n, n ≠ ownerBal state message.currentTarget → n ≠ 1 →
      storageAt (issueState state message) message.currentTarget n =
        storageAt state message.currentTarget n := by
  have hacc1 : hasAccount (readSlot (reqState state message.currentTarget) message.currentTarget 0)
      message.currentTarget :=
    hasAccount_readSlot (hasAccount_readSlot (hasAccount_readSlot (hasAccount_readSlot hacc)))
  have h1 : storageAt (issueState1 state message) message.currentTarget 1 =
      storageAt state message.currentTarget 1 := by
    rw [issueState1, storageAt_writeSlot_of_ne hacc1 (Ne.symm hO1)]
    simp only [storageAt_readSlot]
  refine ⟨?_, ?_, ?_⟩
  · rw [issueState, storageAt_writeSlot_of_ne (hasAccount_writeSlot hacc1) hO1,
      storageAt_writeSlot_self hacc1, toNat_add' hB]
  · rw [issueState, storageAt_writeSlot_self (hasAccount_writeSlot hacc1), h1, toNat_add' hT]
  · intro n hnO hn1
    rw [issueState, storageAt_writeSlot_of_ne (hasAccount_writeSlot hacc1) hn1,
      storageAt_writeSlot_of_ne hacc1 hnO]
    simp only [storageAt_readSlot]

/-- After `redeem(a)`, when `O ≠ 1`: `_totalSupply` is `T - a` and `balances[owner]` is `B - a`
(as numbers), and every other slot is unchanged. -/
theorem redeem_effects (hacc : hasAccount state message.currentTarget)
    (hO1 : ownerBal state message.currentTarget ≠ 1)
    (hT : (wordArg message.data 0).toNat ≤ (storageAt state message.currentTarget 1).toNat)
    (hB : (wordArg message.data 0).toNat ≤
      (storageAt state message.currentTarget (ownerBal state message.currentTarget)).toNat) :
    (storageAt (redeemState state message) message.currentTarget
        (ownerBal state message.currentTarget)).toNat =
      (storageAt state message.currentTarget (ownerBal state message.currentTarget)).toNat -
        (wordArg message.data 0).toNat ∧
    (storageAt (redeemState state message) message.currentTarget 1).toNat =
      (storageAt state message.currentTarget 1).toNat - (wordArg message.data 0).toNat ∧
    ∀ n, n ≠ ownerBal state message.currentTarget → n ≠ 1 →
      storageAt (redeemState state message) message.currentTarget n =
        storageAt state message.currentTarget n := by
  have hacc2 : hasAccount (reqState state message.currentTarget) message.currentTarget :=
    hasAccount_readSlot (hasAccount_readSlot (hasAccount_readSlot hacc))
  have hacc3 : hasAccount (readSlot (redeemState1 state message) message.currentTarget 0)
      message.currentTarget := hasAccount_readSlot (hasAccount_writeSlot hacc2)
  have hO : storageAt (redeemState1 state message) message.currentTarget
      (ownerBal state message.currentTarget) =
      storageAt state message.currentTarget (ownerBal state message.currentTarget) := by
    rw [redeemState1, storageAt_writeSlot_of_ne hacc2 hO1]
    simp only [storageAt_readSlot]
  refine ⟨?_, ?_, ?_⟩
  · rw [redeemState, storageAt_writeSlot_self hacc3, hO, toNat_sub' hB]
  · rw [redeemState, storageAt_writeSlot_of_ne hacc3 (Ne.symm hO1), storageAt_readSlot,
      redeemState1, storageAt_writeSlot_self hacc2, toNat_sub' hT]
  · intro n hnO hn1
    rw [redeemState, storageAt_writeSlot_of_ne hacc3 hnO, storageAt_readSlot, redeemState1,
      storageAt_writeSlot_of_ne hacc2 hn1]
    simp only [storageAt_readSlot]

end UsdtVerify.IssueSpec
