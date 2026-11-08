import UsdtVerify.Usdt.Proofs.BlackList

/-!
# addBlackList(address) and removeBlackList(address): the specifications from pc 0

Write `C` for the contract, `a` for argument word 0 masked to 160 bits (`addrArg data 0`) and
`L = keccak(a ++ 6)` for the slot of `isBlackListed[a]` (`listSlot a`; `mkey a = a`).

- `spec_add_notOwner` / `spec_remove_notOwner`: a caller other than the owner gets a revert.
- `spec_add` / `spec_remove`: the owner's call stops after one write, of slot `L`, to
  `setLow w 1` / `setLow w 0` (`w` = the word of `L`; low byte set, the rest kept:
  `lowByte_setLow`, `bit_setLow`) and one log `AddedBlackList(a)` / `RemovedBlackList(a)`.
  Neither function reads the old flag: adding twice or removing an absent address succeeds.
-/

namespace UsdtVerify.BlackListSpec

open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts
open Transfer TransferOk Owner Admin BlackList

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate}

/-- From pc 0 to the owner check of a function with one address argument whose body starts with
`JUMPDEST PUSH1 0 DUP1`. -/
theorem toBody1 {e r b t : Nat} (hent : (e, r, b) ∈ ENTRY1) (hb : b ∈ BODIES)
    (htb : tested (BitVec.ofNat 256 (selector message.data)) ENTRIES = t ∧
      branch (BitVec.ofNat 256 (selector message.data)) 54 (entrySize 4 2) ENTRIES = e)
    (hsize : 4 ≤ message.data.size) (hsize' : message.data.size < 2 ^ 256)
    (hv : message.value = 0) {gas : Nat} (hg : 143 + 22 * t ≤ gas) :
    Gas.HoareG fork (At CODE message 0 [] .empty gas state substate)
      (At CODE message (b + 4) [0, 0, addrArg message.data 0, BitVec.ofNat 256 r,
          BitVec.ofNat 256 (selector message.data)]
        MEM0 (gas - (143 + 22 * t)) state substate) := by
  have h1 := dispatch (state := state) (substate := substate) hsize hsize' (gas := gas)
    (by rw [htb.1]; omega)
  rw [htb.1, htb.2] at h1
  refine h1.seq ?_
  refine (entry1 hent hv (by omega)).seq ?_
  refine (prefix9 hb (by simp) (by omega)).seq ?_
  exact restate rfl rfl rfl (by omega) rfl rfl

/-- `addBlackList(a)` from a caller other than the owner reverts with no output. -/
theorem spec_add_notOwner (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x0ecb93c0)
    (hv : message.value = 0) (hown : callerWord message ≠ ownerOf state message.currentTarget)
    {c0 : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0) {gas : Nat}
    (hg : 328 + slotCost c0 ≤ gas) :
    Gas.SpecG fork (At CODE message 0 [] .empty gas state substate)
      (Halted true .empty (gas - (328 + slotCost c0)) (readSlot state message.currentTarget 0)
        (accessSlot substate message.currentTarget 0)) := by
  refine Gas.SpecG.seq (toBody1 (e := 721) (r := 0x0308) (b := 3284) (t := 5) (by decide) (by decide)
    (by rw [hsel]; decide) hsize hsize' hv (by omega)) ?_
  refine (ownerRevert hfork (mem_CHECKS (by decide)) (by simp) size_MEM0 hc0 hown
    (by gas_ok)).consequence (fun _ h => h) ?_
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  exact ⟨hr, he, ho, by rw [hgas]; gas_ok, hs, hss⟩

/-- `removeBlackList(a)` from a caller other than the owner reverts with no output. -/
theorem spec_remove_notOwner (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xe4997dc5)
    (hv : message.value = 0) (hown : callerWord message ≠ ownerOf state message.currentTarget)
    {c0 : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0) {gas : Nat}
    (hg : 856 + slotCost c0 ≤ gas) :
    Gas.SpecG fork (At CODE message 0 [] .empty gas state substate)
      (Halted true .empty (gas - (856 + slotCost c0)) (readSlot state message.currentTarget 0)
        (accessSlot substate message.currentTarget 0)) := by
  refine Gas.SpecG.seq (toBody1 (e := 2276) (r := 0x091b) (b := 7288) (t := 29) (by decide)
    (by decide) (by rw [hsel]; decide) hsize hsize' hv (by omega)) ?_
  refine (ownerRevert hfork (mem_CHECKS (by decide)) (by simp) size_MEM0 hc0 hown
    (by gas_ok)).consequence (fun _ h => h) ?_
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  exact ⟨hr, he, ho, by rw [hgas]; gas_ok, hs, hss⟩

/-- The price of the write of `isBlackListed[a]` to `setLow w v`. -/
abbrev listCost (fork : Fork) (state : State.TransactionState) (message : Message fork)
    (v : U256) : Nat :=
  Gas.writeCost fork (originalAt state message.currentTarget (listSlot (addrArg message.data 0)))
    (storageAt state message.currentTarget (listSlot (addrArg message.data 0)))
    (setLow (storageAt state message.currentTarget (listSlot (addrArg message.data 0))) v) false

/-- The state after the write of `isBlackListed[a]` (slot 0 read by the owner check first). -/
abbrev listState (state : State.TransactionState) (message : Message fork) (v : U256) :
    State.TransactionState :=
  writeSlot (readSlot state message.currentTarget 0) message.currentTarget
    (listSlot (addrArg message.data 0))
    (setLow (storageAt state message.currentTarget (listSlot (addrArg message.data 0))) v)

/-- The substate after the write of `isBlackListed[a]` and the log `t(a)`. -/
abbrev listSub (fork : Fork) (substate : Substate) (state : State.TransactionState)
    (message : Message fork) (v t : U256) : Substate :=
  { storeSub fork (accessSlot substate message.currentTarget 0) message.currentTarget
      (listSlot (addrArg message.data 0))
      (originalAt state message.currentTarget (listSlot (addrArg message.data 0)))
      (storageAt state message.currentTarget (listSlot (addrArg message.data 0)))
      (setLow (storageAt state message.currentTarget (listSlot (addrArg message.data 0))) v) with
    logs := substate.logs.push (log1W message.currentTarget t (addrArg message.data 0)) }

/-- The two success paths, from the owner check on. -/
theorem listTail (hfork : .berlin ≤ fork) {s p q : Nat} {v t : U256}
    {r : Nat}
    (hp : (s = 3288 ∧ p = 3375 ∧ q = 3464 ∧ v = 1 ∧ t = ADDED_TOPIC ∧ r = 0x0308) ∨
      (s = 7292 ∧ p = 7379 ∧ q = 7468 ∧ v = 0 ∧ t = REMOVED_TOPIC ∧ r = 0x091b))
    (hstatic : message.isStatic = false) (hacc : hasAccount state message.currentTarget)
    (hown : callerWord message = ownerOf state message.currentTarget) {x : U256}
    {c0 cB : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hcB : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget
      (listSlot (addrArg message.data 0)) = cB) {gas : Nat}
    (hstip : 2526 + slotCost c0 + slotCost cB ≤ gas)
    (hg : 1314 + slotCost c0 + slotCost cB + listCost fork state message v ≤ gas) :
    Gas.SpecG fork (At CODE message s [0, 0, addrArg message.data 0, BitVec.ofNat 256 r, x] MEM0 gas
        state substate)
      (Halted false .empty (gas - (1314 + slotCost c0 + slotCost cB + listCost fork state message v))
        (listState state message v) (listSub fork substate state message v t)) := by
  have hm := mkey_addrArg0 message.data
  simp only [listCost] at hg ⊢
  have hsq : s + 87 = p := by rcases hp with ⟨rfl, rfl, -⟩ | ⟨rfl, rfl, -⟩ <;> rfl
  have hpq : p + 89 = q := by rcases hp with ⟨-, rfl, rfl, -⟩ | ⟨-, rfl, rfl, -⟩ <;> rfl
  have hs : s ∈ CHECKS := by rcases hp with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> decide
  step ownerOk hfork hs (by simp) hc0 hown (by gas_ok)
  rw [hsq]
  have hpv : (p = 3375 ∧ v = 1) ∨ (p = 7379 ∧ v = 0) := by
    rcases hp with ⟨-, h1, -, h2, -⟩ | ⟨-, h1, -, h2, -⟩
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h1, h2⟩
  step listWrite hfork hpv (by simp) hstatic (hasAccount_readSlot hacc) hcB size_MEM0
    (by gas_ok) (by rw [originalAt_readSlot, storageAt_readSlot]; gas_ok)
  rw [hpq, originalAt_readSlot, storageAt_readSlot, storeSub_accessSlot]
  have hqt : (q = 3464 ∧ t = ADDED_TOPIC ∧ r = 0x0308) ∨ (q = 7468 ∧ t = REMOVED_TOPIC ∧ r = 0x091b) ∨
      (q = 2830 ∧ t = DEPRECATE_TOPIC ∧ r = 0x0260) := by
    rcases hp with ⟨-, -, h1, -, h2, h3⟩ | ⟨-, -, h1, -, h2, h3⟩
    · exact Or.inl ⟨h1, h2, h3⟩
    · exact Or.inr (Or.inl ⟨h1, h2, h3⟩)
  refine (listLog hqt hstatic (size_mapMem size_MEM0 _ _) (ptr_mapMem size_MEM0 mload_MEM0 _ _)
    (by gas_ok)).consequence (fun _ h => h) ?_
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  refine ⟨hr, he, ho, by rw [hgas]; gas_ok, hs, ?_⟩
  rw [hss, hm]

/-- The specification of `addBlackList(a)` by the owner.

Hypotheses: Berlin ≤ fork (Glamsterdam included); a frame that may write, of an existing account `C`;
call data of 4 to 2^256 - 1 bytes with selector 0x0ecb93c0; no value; the caller (masked) is the
low 160 bits of slot 0; enough gas, and more than 2300 left at the SSTORE.

Then the run stops normally. Slot 0 is read, then slot `L = keccak(a ++ 6)` is written to
`setLow w 1` (`w` its word: low byte 1, the other bits kept); both slots accessed, the refund of
the write added; one log `AddedBlackList(a)` (topic 0x42e16015…, data the 32-byte word `a`).
Gas left: `gas - (1567 + price(slot 0) + price(L) + price(write))`. -/
theorem spec_add (hfork : .berlin ≤ fork)
    (hstatic : message.isStatic = false) (hacc : hasAccount state message.currentTarget)
    (hsize : 4 ≤ message.data.size) (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x0ecb93c0) (hv : message.value = 0)
    (hown : callerWord message = ownerOf state message.currentTarget)
    {c0 cB : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hcB : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget
      (listSlot (addrArg message.data 0)) = cB) {gas : Nat}
    (hstip : 2779 + slotCost c0 + slotCost cB ≤ gas)
    (hg : 1567 + slotCost c0 + slotCost cB + listCost fork state message 1 ≤ gas) :
    Gas.SpecG fork (At CODE message 0 [] .empty gas state substate)
      (Halted false .empty (gas - (1567 + slotCost c0 + slotCost cB + listCost fork state message 1))
        (listState state message 1) (listSub fork substate state message 1 ADDED_TOPIC)) := by
  refine Gas.SpecG.seq (toBody1 (e := 721) (r := 0x0308) (b := 3284) (t := 5) (by decide) (by decide)
    (by rw [hsel]; decide) hsize hsize' hv (by omega)) ?_
  refine (listTail hfork (Or.inl ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩) hstatic hacc hown hc0 hcB
    (by omega) (by omega)).consequence (fun _ h => h) ?_
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  exact ⟨hr, he, ho, by rw [hgas]; omega, hs, hss⟩

/-- The specification of `removeBlackList(a)` by the owner: as `spec_add`, with selector
0xe4997dc5, the word written `setLow w 0` (low byte 0), the log `RemovedBlackList(a)` (topic
0xd7e9ec6e…), and gas left `gas - (2095 + price(slot 0) + price(L) + price(write))`. -/
theorem spec_remove (hfork : .berlin ≤ fork)
    (hstatic : message.isStatic = false) (hacc : hasAccount state message.currentTarget)
    (hsize : 4 ≤ message.data.size) (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0xe4997dc5) (hv : message.value = 0)
    (hown : callerWord message = ownerOf state message.currentTarget)
    {c0 cB : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hcB : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget
      (listSlot (addrArg message.data 0)) = cB) {gas : Nat}
    (hstip : 3307 + slotCost c0 + slotCost cB ≤ gas)
    (hg : 2095 + slotCost c0 + slotCost cB + listCost fork state message 0 ≤ gas) :
    Gas.SpecG fork (At CODE message 0 [] .empty gas state substate)
      (Halted false .empty (gas - (2095 + slotCost c0 + slotCost cB + listCost fork state message 0))
        (listState state message 0) (listSub fork substate state message 0 REMOVED_TOPIC)) := by
  refine Gas.SpecG.seq (toBody1 (e := 2276) (r := 0x091b) (b := 7288) (t := 29) (by decide)
    (by decide) (by rw [hsel]; decide) hsize hsize' hv (by omega)) ?_
  refine (listTail hfork (Or.inr ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩) hstatic hacc hown hc0 hcB
    (by omega) (by omega)).consequence (fun _ h => h) ?_
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  exact ⟨hr, he, ho, by rw [hgas]; omega, hs, hss⟩

/-- The two writing paths from the owner check on, in a static frame or with no account for `C`:
the run reaches the `SSTORE` of `isBlackListed[a]`, which is `Stuck`. -/
theorem listTailBad (hfork : .berlin ≤ fork) {s p : Nat} {v : U256} {r : Nat}
    (hp : (s = 3288 ∧ p = 3375 ∧ v = 1 ∧ r = 0x0308) ∨ (s = 7292 ∧ p = 7379 ∧ v = 0 ∧ r = 0x091b))
    (hown : callerWord message = ownerOf state message.currentTarget) {x : U256}
    {c0 cB : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hcB : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget
      (listSlot (addrArg message.data 0)) = cB) {gas : Nat}
    (hbad : Gas.NoWrite message state (gas - (225 + slotCost c0 + slotCost cB)))
    (hg : 225 + slotCost c0 + slotCost cB ≤ gas) :
    Gas.HoareG fork (At CODE message s [0, 0, addrArg message.data 0, BitVec.ofNat 256 r, x] MEM0
        gas state substate) Gas.Stuck := by
  have hsq : s + 87 = p := by rcases hp with ⟨rfl, rfl, -⟩ | ⟨rfl, rfl, -⟩ <;> rfl
  have hs : s ∈ CHECKS := by rcases hp with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> decide
  step ownerOk hfork hs (by simp) hc0 hown (by gas_ok)
  rw [hsq]
  have hpv : (p = 3375 ∧ v = 1) ∨ (p = 7379 ∧ v = 0) := by
    rcases hp with ⟨-, h1, h2, -⟩ | ⟨-, h1, h2, -⟩
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h1, h2⟩
  refine listWriteBad (state := readSlot state message.currentTarget 0) hfork hpv ?_ hcB
    size_MEM0 (hbad.le ?_) ?_
  · simp
  · gas_ok
  · gas_ok

/-- `addBlackList(a)` by the owner, in a static frame or with no account for `C`: the run
reaches the `SSTORE` of `isBlackListed[a]`, which is `Stuck`. -/
theorem bad_add (hfork : .berlin ≤ fork)
    (hsize : 4 ≤ message.data.size) (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x0ecb93c0) (hv : message.value = 0)
    (hown : callerWord message = ownerOf state message.currentTarget)
    {c0 cB : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hcB : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget
      (listSlot (addrArg message.data 0)) = cB) {gas : Nat}
    (hbad : Gas.NoWrite message state (gas - (478 + slotCost c0 + slotCost cB)))
    (hg : 478 + slotCost c0 + slotCost cB ≤ gas) :
    Gas.HoareG fork (At CODE message 0 [] .empty gas state substate) Gas.Stuck := by
  refine Triple.seq (toBody1 (e := 721) (r := 0x0308) (b := 3284) (t := 5) (by decide) (by decide)
    (by rw [hsel]; decide) hsize hsize' hv (by omega)) ?_
  exact listTailBad hfork (Or.inl ⟨rfl, rfl, rfl, rfl⟩) hown hc0 hcB (hbad.le (by omega))
    (by omega)

/-- `removeBlackList(a)` by the owner, in a static frame or with no account for `C`: the run
reaches the `SSTORE` of `isBlackListed[a]`, which is `Stuck`. -/
theorem bad_remove (hfork : .berlin ≤ fork)
    (hsize : 4 ≤ message.data.size) (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0xe4997dc5) (hv : message.value = 0)
    (hown : callerWord message = ownerOf state message.currentTarget)
    {c0 cB : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hcB : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget
      (listSlot (addrArg message.data 0)) = cB) {gas : Nat}
    (hbad : Gas.NoWrite message state (gas - (1006 + slotCost c0 + slotCost cB)))
    (hg : 1006 + slotCost c0 + slotCost cB ≤ gas) :
    Gas.HoareG fork (At CODE message 0 [] .empty gas state substate) Gas.Stuck := by
  refine Triple.seq (toBody1 (e := 2276) (r := 0x091b) (b := 7288) (t := 29) (by decide)
    (by decide) (by rw [hsel]; decide) hsize hsize' hv (by omega)) ?_
  exact listTailBad hfork (Or.inr ⟨rfl, rfl, rfl, rfl⟩) hown hc0 hcB (hbad.le (by omega))
    (by omega)

/-- In plain terms: after `addBlackList(a)` / `removeBlackList(a)` the low byte of
`isBlackListed[a]` is 1 / 0 (the flag that transfer and transferFrom test), and every other
slot read in the end state is as in the start state. -/
theorem listState_flag (hacc : hasAccount state message.currentTarget) (v : U256)
    (hvb : v = 0 ∨ v = 1) :
    (storageAt (listState state message v) message.currentTarget
      (listSlot (addrArg message.data 0))).toNat % 256 = v.toNat := by
  rw [listState, storageAt_writeSlot_self (hasAccount_readSlot hacc)]
  exact lowByte_setLow _ v hvb

theorem listState_other (hacc : hasAccount state message.currentTarget) (v : U256) {n : U256}
    (hn : n ≠ listSlot (addrArg message.data 0)) :
    storageAt (listState state message v) message.currentTarget n =
      storageAt state message.currentTarget n := by
  rw [listState, storageAt_writeSlot_of_ne (hasAccount_readSlot hacc) hn, storageAt_readSlot]

end UsdtVerify.BlackListSpec
