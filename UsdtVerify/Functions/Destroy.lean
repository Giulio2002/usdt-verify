import UsdtVerify.Functions.AddrWriteSpec

/-!
# destroyBlackFunds(address): the reverts

TetherToken:
```
function destroyBlackFunds(address _blackListedUser) public onlyOwner {
    require(isBlackListed[_blackListedUser]);
    uint dirtyFunds = balanceOf(_blackListedUser);
    balances[_blackListedUser] = 0;
    _totalSupply -= dirtyFunds;
    DestroyedBlackFunds(_blackListedUser, dirtyFunds);
}
```
Entry 2431, body 7818 (`JUMPDEST PUSH1 0 DUP1 PUSH1 0`: the local `dirtyFunds` first), check at
7824, then 7911 (the `require`).

- `spec_notOwner`: a caller other than the owner gets a revert.
- `spec_notListed`: the owner, `a` not blacklisted (low byte of `isBlackListed[a]` is 0) ⇒
  REVERT.

The success path (the call of TetherToken's `balanceOf`, with its own deprecation check, then
the writes and the log) is not covered yet.
-/

namespace UsdtVerify.Destroy

open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts
open Transfer TransferOk Owner Admin BlackList Issue

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate}

/-- From pc 0 to the owner check of destroyBlackFunds (entry 31 of the table). -/
theorem toBody (hsize : 4 ≤ message.data.size) (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0xf3bdc228) (hv : message.value = 0) {gas : Nat}
    (hg : 850 ≤ gas) :
    Gas.HoareG fork (At CODE message 0 [] .empty gas state substate)
      (At CODE message 7824 [0, 0, 0, addrArg message.data 0, 0x09b6,
          BitVec.ofNat 256 (selector message.data)]
        MEM0 (gas - 850) state substate) := by
  have ht : tested (BitVec.ofNat 256 (selector message.data)) ENTRIES = 32 ∧
      branch (BitVec.ofNat 256 (selector message.data)) 54 (entrySize 4 2) ENTRIES = 2431 := by
    rw [hsel]; decide
  have h1 := dispatch (state := state) (substate := substate) hsize hsize' (gas := gas)
    (by rw [ht.1]; omega)
  rw [ht.1, ht.2] at h1
  refine h1.seq ?_
  refine (entry1 (e := 2431) (r := 0x09b6) (b := 7818) (by decide) hv (by omega)).seq ?_
  step jumpdestR
  step pushR 1 (0 : U256)
  step dupR 0
  step pushR 1 (0 : U256)
  exact restate (by decide) rfl rfl (by gas_ok) rfl rfl

/-- `destroyBlackFunds(a)` from a caller other than the owner reverts with no output. -/
theorem spec_notOwner (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xf3bdc228)
    (hv : message.value = 0) (hown : callerWord message ≠ ownerOf state message.currentTarget)
    {c0 : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0) {gas : Nat}
    (hg : 925 + slotCost c0 ≤ gas) :
    Gas.SpecG fork (At CODE message 0 [] .empty gas state substate)
      (Halted true .empty (gas - (925 + slotCost c0)) (readSlot state message.currentTarget 0)
        (accessSlot substate message.currentTarget 0)) := by
  refine Gas.SpecG.seq (toBody hsize hsize' hsel hv (by omega)) ?_
  refine (ownerRevert hfork (by decide) (by simp) size_MEM0 hc0 hown
    (by gas_ok)).consequence (fun _ h => h) ?_
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  exact ⟨hr, he, ho, by rw [hgas]; gas_ok, hs, hss⟩

/-- The flag test of the code (`ISZERO ISZERO` of the low byte) is 0 for a low byte of 0. -/
theorem lowTest_eq {w : U256} (h : w.toNat % 256 = 0) :
    isZero (isZero (bitwiseAnd (0xff : U256) (div w (exp (0x0100 : U256) (0 : U256))))) = 0 := by
  have hd : div w (exp (0x0100 : U256) (0 : U256)) = w := by
    rw [exp0]; apply BitVec.eq_of_toNat_eq; simp [div]
  have hz : bitwiseAnd (0xff : U256) w = 0 := by
    apply BitVec.eq_of_toNat_eq
    simp only [bitwiseAnd, BitVec.toNat_and]
    rw [show BitVec.toNat (0xff : U256) = 2 ^ 8 - 1 by rfl, Nat.and_comm,
      Nat.and_two_pow_sub_one_eq_mod]
    simpa using h
  rw [hd, hz]; decide

/-- `destroyBlackFunds(a)` by the owner when `a` is not blacklisted (the low byte of
`isBlackListed[a]` is 0): REVERT with no output, after reading slot 0 and that slot. -/
theorem spec_notListed (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xf3bdc228)
    (hv : message.value = 0) (hown : callerWord message = ownerOf state message.currentTarget)
    (hnl : (storageAt state message.currentTarget (listSlot (addrArg message.data 0))).toNat % 256 = 0)
    {c0 cL : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hcL : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget
      (listSlot (addrArg message.data 0)) = cL) {gas : Nat}
    (hg : 1074 + slotCost c0 + slotCost cL ≤ gas) :
    Gas.SpecG fork (At CODE message 0 [] .empty gas state substate)
      (Halted true .empty (gas - (1074 + slotCost c0 + slotCost cL))
        (readSlot (readSlot state message.currentTarget 0) message.currentTarget
          (listSlot (addrArg message.data 0)))
        (accessSlot (accessSlot substate message.currentTarget 0) message.currentTarget
          (listSlot (addrArg message.data 0)))) := by
  have hexp : exponentBytes (0 : U256) = 0 := by decide
  have hz : extendMemory (mapMem MEM0 (mkey (addrArg message.data 0)) 6).size
      [((0 : U256), (0 : U256))] = ⟨0, 0⟩ := by
    rw [size_mapMem size_MEM0]; decide
  simp only [listSlot] at hnl hcL ⊢
  refine Gas.SpecG.seq (toBody hsize hsize' hsel hv (by omega)) ?_
  step ownerOk hfork (by decide) (by simp) hc0 hown (by gas_ok)
  at_pc 7911
  step jumpdestR
  step pushR 1 (0x06 : U256)
  step pushR 1 (0 : U256)
  step dupR 3
  step hashTail7 (by decide) (by simp) size_MEM0 (by gas_ok)
  step pushR 1 (0 : U256)
  step swapR 0
  norm
  step Gas.sloadG hfork (cold := cL) (by code_fact) (by code_fact) hcL (by gas_ok)
  rw [getStorage_eq, storageAt_readSlot]
  step swapR 0
  norm
  step pushR 2 (0x0100 : U256)
  step Gas.expLG (Nat.le_trans (by decide) hfork) (by code_fact) (by code_fact) (by gas_ok)
  step swapR 0
  norm
  step binR 0x04 Local.instruction_div
  step pushR 1 (0xff : U256)
  step binR 0x16 Local.instruction_and
  step unR 0x15 instruction_iszero
  step unR 0x15 instruction_iszero
  step pushR 2 (0x1f3f : U256)
  step jumpi0R (lowTest_eq hnl)
  step pushR 1 (0 : U256)
  step dupR 0
  refine (Gas.revertG (Nat.le_trans (by decide) hfork) (by code_fact) (by code_fact)
    (by rw [hz]; gas_ok)).consequence (fun _ h => h) ?_
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  refine ⟨hr, he, ?_, ?_, hs, hss⟩
  · rw [ho]; simp [memoryReadBytes]
  · rw [hgas, hz]; gas_ok

end UsdtVerify.Destroy
