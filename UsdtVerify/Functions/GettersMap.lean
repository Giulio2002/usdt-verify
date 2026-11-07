import UsdtVerify.Functions.Getters
import UsdtVerify.Functions.MemRev

/-!
# The getters with address arguments

`a`, `a0`, `a1` are argument words 0 and 1 masked to 160 bits (`addrArg`).

- balances(a) (public mapping, 4291): returns `balances[a]`, slot `keccak(a ++ 2)`.
- isBlackListed(a) (public mapping, 7256) and getBlackListStatus(a) (4523): return 1 if the low
  byte of `isBlackListed[a]` (slot `keccak(a ++ 6)`) is nonzero, else 0.
- allowed(a0, a1) (public mapping, 4609): returns `allowed[a0][a1]`, slot
  `keccak(a1 ++ keccak(a0 ++ 5))`.
- allowance(a0, a1) (6925), when not deprecated: the same slot, through StandardToken's
  `allowance` (lookup at 10814).

The public mapping getters write the base word at 32 before the key word at 0 (`pubMem`); their
hash reads the two words through `memoryReadBytes_write_rev` (MemRev.lean).
-/

namespace UsdtVerify.GettersMap

open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts
open Transfer TransferOk Owner Admin BlackList Issue Getters

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate}

/-- The entries `(e, r, b)` of the getters with one address argument. -/
abbrev ENTRY1M : List (Nat × Nat × Nat) := [(1001, 1056, 4291), (1222, 1277, 4523),
  (2195, 2250, 7256)]

/-- The entry of a getter with one address argument (as `Admin.entry1`). -/
theorem entry1m {e r b : Nat} (hp : (e, r, b) ∈ ENTRY1M) (hv : message.value = 0) {x : U256}
    {M : ByteArray} {gas : Nat} (hg : 74 ≤ gas) :
    Hoare fork (At CODE message e [x] M gas state substate)
      (At CODE message b [addrArg message.data 0, BitVec.ofNat 256 r, x] M (gas - 74) state
        substate) := by
  simp only [ENTRY1M, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hp
  rcases hp with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  all_goals
    step jumpdestR
    step Logic.callvalue (by code_fact) (by code_fact) (by gas_ok) (by stk_ok)
    step unR 0x15 instruction_iszero
    step pushAnyR 2
    step jumpiR (by simp [hv, isZero])
    step jumpdestR
    step pushAnyR 2
    step pushR 1 (0x04 : U256)
    step dupR 0
    step dupR 0
    step calldataload (by code_fact) (by code_fact) (by gas_ok)
    step pushR 20 ADDR_MASK
    step binR 0x16 Local.instruction_and
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
    exact restate (by decide) (congrArg (addrArg message.data 0 :: · :: [x]) (by decide)) rfl
      (by gas_ok) rfl rfl

/-- The entries `(e, r, b)` of the getters with two address arguments. -/
abbrev ENTRY2 : List (Nat × Nat × Nat) := [(1303, 1389, 4609), (2046, 2132, 6925)]

/-- The entry of a getter with two address arguments: the body `b` gets `a1`, `a0` and the
return address `r`. -/
theorem entry2 {e r b : Nat} (hp : (e, r, b) ∈ ENTRY2) (hv : message.value = 0) {x : U256}
    {M : ByteArray} {gas : Nat} (hg : 104 ≤ gas) :
    Hoare fork (At CODE message e [x] M gas state substate)
      (At CODE message b [addrArg message.data 1, addrArg message.data 0, BitVec.ofNat 256 r, x]
        M (gas - 104) state substate) := by
  simp only [ENTRY2, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hp
  rcases hp with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  all_goals
    step jumpdestR
    step Logic.callvalue (by code_fact) (by code_fact) (by gas_ok) (by stk_ok)
    step unR 0x15 instruction_iszero
    step pushAnyR 2
    step jumpiR (by simp [hv, isZero])
    step jumpdestR
    step pushAnyR 2
    step pushR 1 (0x04 : U256)
    step dupR 0
    step dupR 0
    step calldataload (by code_fact) (by code_fact) (by gas_ok)
    step pushR 20 ADDR_MASK
    step binR 0x16 Local.instruction_and
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
    step calldataload (by code_fact) (by code_fact) (by gas_ok)
    step pushR 20 ADDR_MASK
    step binR 0x16 Local.instruction_and
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
    exact restate (by decide)
      (congrArg (addrArg message.data 1 :: addrArg message.data 0 :: · :: [x]) (by decide)) rfl
      (by gas_ok) rfl rfl

/-- The memory after a public mapping getter's hash: `base` written at 32, then `k` at 0. -/
abbrev pubMem (M : ByteArray) (k base : U256) : ByteArray :=
  memoryWrite (memoryWrite M 32 (wordBytes base)) 0 (wordBytes k)

theorem size_pubMem {M : ByteArray} (hM : M.size = 96) (k base : U256) :
    (pubMem M k base).size = 96 := by
  rw [pubMem, size_memoryWrite, size_memoryWrite] <;>
    simp [size_memoryWrite, hM, size_wordBytes]

theorem ptr_pubMem {M : ByteArray} (hM : M.size = 96)
    (hptr : loadWord (memoryReadBytes M 64 32) 0 32 = 0x60) (k base : U256) :
    loadWord (memoryReadBytes (pubMem M k base) 64 32) 0 32 = 0x60 := by
  rw [pubMem, memoryReadBytes_memoryWrite_of_disjoint,
    memoryReadBytes_memoryWrite_of_disjoint, hptr] <;>
    simp [size_memoryWrite, hM, size_wordBytes]

/-- The hash of a public mapping getter, at 4294 (balances), 7259 (isBlackListed) and 4624
(allowed, second level): `base` at 32, the key word `k` at 0, keccak of the 64 bytes. -/
theorem hashPub {p : Nat} (hp : p = 4294 ∨ p = 7259 ∨ p = 4624) {k base : U256}
    {rest : List U256} (hrest : rest.length ≤ 900) {M : ByteArray} (hM : M.size = 96)
    {gas : Nat} (hg : 63 ≤ gas) :
    Hoare fork (At CODE message p (base :: k :: rest) M gas state substate)
      (At CODE message (p + 12) (mapSlot k base :: k :: rest) (pubMem M k base) (gas - 63) state
        substate) := by
  have hs1 : (memoryWrite M 32 (wordBytes base)).size = 96 := by
    rw [size_memoryWrite] <;> simp [hM, size_wordBytes]
  have hext1 : extendMemory M.size [((0x20 : U256), (32 : U256))] = ⟨0, 0⟩ := by
    rw [hM]; decide
  have hext2 : extendMemory (memoryWrite M 32 (wordBytes base)).size
      [((0 : U256), (32 : U256))] = ⟨0, 0⟩ := by
    rw [hs1]; decide
  have hext3 : extendMemory (pubMem M k base).size [((0 : U256), (0x40 : U256))] = ⟨0, 0⟩ := by
    rw [size_pubMem hM]; decide
  have hk : keccak256Cost (0x40 : U256) = 42 := by decide
  have hread : memoryReadBytes (pubMem M k base) 0 64 = wordBytes k ++ wordBytes base := by
    have h := memoryReadBytes_write_rev (memory := M) (a := wordBytes k) (b := wordBytes base)
      (s := 0) (by simp [hM, size_wordBytes])
    simpa [size_wordBytes, pubMem] using h
  rcases hp with rfl | rfl | rfl
  all_goals
    step pushR 1 (0x20 : U256)
    step mstore (by code_fact) (by code_fact) (by rw [hext1]; gas_ok)
    step reshape (m' := memoryWrite M 32 (wordBytes base)) rfl
      (by rw [hext1, memoryExtend_zero]; rfl) (by rw [hext1] <;> gas_ok)
    step dupR 0
    step pushR 1 (0 : U256)
    step mstore (by code_fact) (by code_fact) (by rw [hext2]; gas_ok)
    step reshape (m' := pubMem M k base) rfl (by rw [hext2, memoryExtend_zero]; rfl)
      (by rw [hext2] <;> gas_ok)
    step pushR 1 (0x40 : U256)
    step pushR 1 (0 : U256)
    step keccak256 (by code_fact) (by code_fact) (by rw [hk, hext3]; gas_ok)
    exact restate (by decide)
      (by rw [hext3, memoryExtend_zero, show (0 : U256).toNat = 0 from rfl,
        show (0x40 : U256).toNat = 64 from rfl, hread]; rfl)
      (by rw [hext3, memoryExtend_zero]) (by rw [hext3, hk] <;> gas_ok) rfl rfl

/-! ## balances(a) -/

/-- The specification of `balances(address)` (selector 0x27e235e3): the run returns the 32 bytes
of `balances[a]` (slot `keccak(a ++ 2)`, the slot of `balanceOf`), after one read of it. It has
no deprecation check. -/
theorem spec_balances (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x27e235e3)
    (hv : message.value = 0) {c : Bool}
    (hc : coldIn substate message.currentTarget (mapSlot (addrArg message.data 0) 2) = c)
    {gas : Nat} (hg : 478 + slotCost c ≤ gas) :
    Spec fork (At CODE message 0 [] .empty gas state substate)
      (Halted false (wordBytes (storageAt state message.currentTarget
          (mapSlot (addrArg message.data 0) 2)))
        (gas - (478 + slotCost c))
        (readSlot state message.currentTarget (mapSlot (addrArg message.data 0) 2))
        (accessSlot substate message.currentTarget (mapSlot (addrArg message.data 0) 2))) := by
  refine Spec.seq ((toEntry (t := 9) (e := 1001) (by decide) hsize hsize' hsel (by omega)).seq
    (entry1m (r := 1056) (b := 4291) (by decide) hv (by omega))) ?_
  step jumpdestR
  step pushR 1 (0x02 : U256)
  step hashPub (Or.inl rfl) (by simp) size_MEM0 (by gas_ok)
  step pushR 1 (0 : U256)
  step swapR 1
  norm
  step popR
  step swapR 0
  norm
  step popR
  step sload hfork (cold := c) (by code_fact) (by code_fact) hc (by gas_ok)
  rw [getStorage_eq]
  step dupR 1
  step jumpR
  at_pc 1056
  refine (ret (by decide) (size_pubMem size_MEM0 _ _) (ptr_pubMem size_MEM0 mload_MEM0 _ _)
    (rest := [_, _]) (by simp) (by gas_ok)).consequence (fun _ h => h) ?_
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  exact ⟨hr, he, ho, by rw [hgas]; gas_ok, hs, hss⟩

/-! ## isBlackListed(a), getBlackListStatus(a) -/

theorem isZero_isZero_eq_one {y : U256} (h : isZero (isZero y) ≠ 0) : isZero (isZero y) = 1 := by
  generalize isZero y = z at h ⊢
  unfold isZero at h ⊢
  split
  · rfl
  · simp_all

/-- The word that the code returns for a flag in the low byte: 1 if it is nonzero, else 0. -/
theorem isZero4_low (w : U256) :
    isZero (isZero (isZero (isZero (bitwiseAnd (0xff : U256)
      (div w (exp (0x0100 : U256) (0 : U256))))))) = if w.toNat % 256 = 0 then 0 else 1 := by
  by_cases h : w.toNat % 256 = 0
  · rw [Destroy.lowTest_eq h]; simp only [h, ↓reduceIte]; decide
  · rw [isZero_isZero_eq_one (DestroySpec.lowTest_ne h)]; simp only [h, ↓reduceIte]; decide

/-- The specification of `isBlackListed(address)` (selector 0xe47d6060): the run returns the
word 1 if the low byte of `isBlackListed[a]` (slot `keccak(a ++ 6)`) is nonzero and 0
otherwise, after one read of that slot. -/
theorem spec_isBlackListed (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xe47d6060)
    (hv : message.value = 0) {c : Bool}
    (hc : coldIn substate message.currentTarget (mapSlot (addrArg message.data 0) 6) = c)
    {gas : Nat} (hg : 933 + slotCost c ≤ gas) :
    Spec fork (At CODE message 0 [] .empty gas state substate)
      (Halted false (wordBytes (if (storageAt state message.currentTarget
          (mapSlot (addrArg message.data 0) 6)).toNat % 256 = 0 then 0 else 1))
        (gas - (933 + slotCost c))
        (readSlot state message.currentTarget (mapSlot (addrArg message.data 0) 6))
        (accessSlot substate message.currentTarget (mapSlot (addrArg message.data 0) 6))) := by
  have hexp : exponentBytes (0 : U256) = 0 := by decide
  refine Spec.seq ((toEntry (t := 28) (e := 2195) (by decide) hsize hsize' hsel (by omega)).seq
    (entry1m (r := 2250) (b := 7256) (by decide) hv (by omega))) ?_
  step jumpdestR
  step pushR 1 (0x06 : U256)
  step hashPub (Or.inr (Or.inl rfl)) (by simp) size_MEM0 (by gas_ok)
  step pushR 1 (0 : U256)
  step swapR 1
  norm
  step popR
  step sload hfork (cold := c) (by code_fact) (by code_fact) hc (by gas_ok)
  rw [getStorage_eq]
  step swapR 0
  norm
  step pushR 2 (0x0100 : U256)
  step Local.exp (Nat.le_trans (by decide) hfork) (by code_fact) (by code_fact) (by gas_ok)
  step swapR 0
  norm
  step binR 0x04 Local.instruction_div
  step pushR 1 (0xff : U256)
  step binR 0x16 Local.instruction_and
  step dupR 1
  step jumpR
  at_pc 2250
  refine (retB (by decide) (size_pubMem size_MEM0 _ _) (ptr_pubMem size_MEM0 mload_MEM0 _ _)
    (rest := [_, _]) (by simp) (by gas_ok)).consequence (fun _ h => h) ?_
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  refine ⟨hr, he, ?_, by rw [hgas]; gas_ok, hs, hss⟩
  rw [ho, isZero4_low]

/-- The specification of `getBlackListStatus(address)` (selector 0x59bf1abe): as
`isBlackListed`, through TetherToken's own function. -/
theorem spec_getBlackListStatus (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x59bf1abe)
    (hv : message.value = 0) {c : Bool}
    (hc : coldIn substate message.currentTarget (mapSlot (addrArg message.data 0) 6) = c)
    {gas : Nat} (hg : 663 + slotCost c ≤ gas) :
    Spec fork (At CODE message 0 [] .empty gas state substate)
      (Halted false (wordBytes (if (storageAt state message.currentTarget
          (mapSlot (addrArg message.data 0) 6)).toNat % 256 = 0 then 0 else 1))
        (gas - (663 + slotCost c))
        (readSlot state message.currentTarget (mapSlot (addrArg message.data 0) 6))
        (accessSlot substate message.currentTarget (mapSlot (addrArg message.data 0) 6))) := by
  have hexp : exponentBytes (0 : U256) = 0 := by decide
  have hk := mkey_addrArg0 message.data
  refine Spec.seq ((toEntry (t := 14) (e := 1222) (by decide) hsize hsize' hsel (by omega)).seq
    (entry1m (r := 1277) (b := 4523) (by decide) hv (by omega))) ?_
  step jumpdestR
  step pushR 1 (0 : U256)
  step pushR 1 (0x06 : U256)
  step pushR 1 (0 : U256)
  step dupR 3
  step hashTail7 (by decide) (by simp) size_MEM0 (by gas_ok)
  rw [hk]
  step pushR 1 (0 : U256)
  step swapR 0
  norm
  step sload hfork (cold := c) (by code_fact) (by code_fact) hc (by gas_ok)
  rw [getStorage_eq]
  step swapR 0
  norm
  step pushR 2 (0x0100 : U256)
  step Local.exp (Nat.le_trans (by decide) hfork) (by code_fact) (by code_fact) (by gas_ok)
  step swapR 0
  norm
  step binR 0x04 Local.instruction_div
  step pushR 1 (0xff : U256)
  step binR 0x16 Local.instruction_and
  step swapR 0
  norm
  step popR
  step swapR 1
  norm
  step swapR 0
  norm
  step popR
  step jumpR
  at_pc 1277
  refine (retB (by decide) (size_mapMem size_MEM0 _ _) (ptr_mapMem size_MEM0 mload_MEM0 _ _)
    (rest := [_]) (by simp) (by gas_ok)).consequence (fun _ h => h) ?_
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  refine ⟨hr, he, ?_, by rw [hgas]; gas_ok, hs, hss⟩
  rw [ho, isZero4_low]

/-! ## allowed(a0, a1), allowance(a0, a1) -/

theorem mkey_addrArg (data : ByteArray) (i : Nat) : mkey (addrArg data i) = addrArg data i := by
  simp only [mkey, addrArg, mask_mask]

/-- The slot of `allowed[a0][a1]`: `keccak(a1 ++ keccak(a0 ++ 5))`. -/
abbrev allowSlot (data : ByteArray) : U256 :=
  mapSlot (addrArg data 1) (mapSlot (addrArg data 0) 5)

/-- The first hash of `allowed` at 4612: `base` at 32, the second word below (`k`) at 0. -/
theorem hashPub2 {k1 k base : U256} {rest : List U256} (hrest : rest.length ≤ 900)
    {M : ByteArray} (hM : M.size = 96) {gas : Nat} (hg : 63 ≤ gas) :
    Hoare fork (At CODE message 4612 (base :: k1 :: k :: rest) M gas state substate)
      (At CODE message 4624 (mapSlot k base :: k1 :: k :: rest) (pubMem M k base) (gas - 63)
        state substate) := by
  have hs1 : (memoryWrite M 32 (wordBytes base)).size = 96 := by
    rw [size_memoryWrite] <;> simp [hM, size_wordBytes]
  have hext1 : extendMemory M.size [((0x20 : U256), (32 : U256))] = ⟨0, 0⟩ := by
    rw [hM]; decide
  have hext2 : extendMemory (memoryWrite M 32 (wordBytes base)).size
      [((0 : U256), (32 : U256))] = ⟨0, 0⟩ := by
    rw [hs1]; decide
  have hext3 : extendMemory (pubMem M k base).size [((0 : U256), (0x40 : U256))] = ⟨0, 0⟩ := by
    rw [size_pubMem hM]; decide
  have hk : keccak256Cost (0x40 : U256) = 42 := by decide
  have hread : memoryReadBytes (pubMem M k base) 0 64 = wordBytes k ++ wordBytes base := by
    have h := memoryReadBytes_write_rev (memory := M) (a := wordBytes k) (b := wordBytes base)
      (s := 0) (by simp [hM, size_wordBytes])
    simpa [size_wordBytes, pubMem] using h
  step pushR 1 (0x20 : U256)
  step mstore (by code_fact) (by code_fact) (by rw [hext1]; gas_ok)
  step reshape (m' := memoryWrite M 32 (wordBytes base)) rfl
    (by rw [hext1, memoryExtend_zero]; rfl) (by rw [hext1] <;> gas_ok)
  step dupR 1
  step pushR 1 (0 : U256)
  step mstore (by code_fact) (by code_fact) (by rw [hext2]; gas_ok)
  step reshape (m' := pubMem M k base) rfl (by rw [hext2, memoryExtend_zero]; rfl)
    (by rw [hext2] <;> gas_ok)
  step pushR 1 (0x40 : U256)
  step pushR 1 (0 : U256)
  step keccak256 (by code_fact) (by code_fact) (by rw [hk, hext3]; gas_ok)
  exact restate (by decide)
    (by rw [hext3, memoryExtend_zero, show (0 : U256).toNat = 0 from rfl,
      show (0x40 : U256).toNat = 64 from rfl, hread]; rfl)
    (by rw [hext3, memoryExtend_zero]) (by rw [hext3, hk] <;> gas_ok) rfl rfl

/-- The specification of `allowed(address,address)` (selector 0x5c658165): the run returns the
32 bytes of `allowed[a0][a1]`, after one read of it. -/
theorem spec_allowed (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x5c658165)
    (hv : message.value = 0) {c : Bool}
    (hc : coldIn substate message.currentTarget (allowSlot message.data) = c)
    {gas : Nat} (hg : 705 + slotCost c ≤ gas) :
    Spec fork (At CODE message 0 [] .empty gas state substate)
      (Halted false (wordBytes (storageAt state message.currentTarget (allowSlot message.data)))
        (gas - (705 + slotCost c))
        (readSlot state message.currentTarget (allowSlot message.data))
        (accessSlot substate message.currentTarget (allowSlot message.data))) := by
  refine Spec.seq ((toEntry (t := 15) (e := 1303) (by decide) hsize hsize' hsel (by omega)).seq
    (entry2 (r := 1389) (b := 4609) (by decide) hv (by omega))) ?_
  step jumpdestR
  step pushR 1 (0x05 : U256)
  step hashPub2 (by simp) size_MEM0 (by gas_ok)
  step hashPub (Or.inr (Or.inr rfl)) (by simp) (size_pubMem size_MEM0 _ _) (by gas_ok)
  step pushR 1 (0 : U256)
  step swapR 1
  norm
  step popR
  step swapR 1
  norm
  step popR
  step popR
  step sload hfork (cold := c) (by code_fact) (by code_fact) hc (by gas_ok)
  rw [getStorage_eq]
  step dupR 1
  step jumpR
  at_pc 1389
  refine (ret (by decide) (size_pubMem (size_pubMem size_MEM0 _ _) _ _)
    (ptr_pubMem (size_pubMem size_MEM0 _ _) (ptr_pubMem size_MEM0 mload_MEM0 _ _) _ _)
    (rest := [_, _]) (by simp) (by gas_ok)).consequence (fun _ h => h) ?_
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  exact ⟨hr, he, ho, by rw [hgas]; gas_ok, hs, hss⟩

/-- The specification of `allowance(address,address)` (selector 0xdd62ed3e) when not
deprecated: the run returns the 32 bytes of `allowed[a0][a1]`, after reads of slot 10 and that
slot. -/
theorem spec_allowance (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xdd62ed3e)
    (hv : message.value = 0) (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    {c10 c : Bool} (hc10 : coldIn substate message.currentTarget 10 = c10)
    (hc : coldIn (accessSlot substate message.currentTarget 10) message.currentTarget
      (allowSlot message.data) = c)
    {gas : Nat} (hg : 1156 + slotCost c10 + slotCost c ≤ gas) :
    Spec fork (At CODE message 0 [] .empty gas state substate)
      (Halted false (wordBytes (storageAt state message.currentTarget (allowSlot message.data)))
        (gas - (1156 + slotCost c10 + slotCost c))
        (readSlot (readSlot state message.currentTarget 10) message.currentTarget
          (allowSlot message.data))
        (accessSlot (accessSlot substate message.currentTarget 10) message.currentTarget
          (allowSlot message.data))) := by
  have hk0 := mkey_addrArg message.data 0
  have hk1 := mkey_addrArg message.data 1
  refine Spec.seq ((toEntry (t := 26) (e := 2046) (by decide) hsize hsize' hsel (by omega)).seq
    (entry2 (r := 2132) (b := 6925) (by decide) hv (by omega))) ?_
  step depCheck hfork (Or.inr (Or.inr ⟨rfl, rfl⟩)) (by simp) hdep hc10 (by gas_ok)
  at_pc 7231
  step jumpdestR
  step pushR 2 (0x1c49 : U256)
  step dupR 3
  step dupR 3
  step pushR 2 (0x2a3e : U256)
  step jumpR
  at_pc 10814
  step jumpdestR
  step pushR 1 (0 : U256)
  step pushR 1 (0x05 : U256)
  step pushR 1 (0 : U256)
  step dupR 4
  step hashTail7 (by decide) (by simp) size_MEM0 (by gas_ok)
  step pushR 1 (0 : U256)
  step dupR 3
  step hashTail7 (by decide) (by simp) (size_mapMem size_MEM0 _ _) (by gas_ok)
  rw [hk0, hk1]
  step sload hfork (cold := c) (by code_fact) (by code_fact) hc (by gas_ok)
  rw [getStorage_eq, storageAt_readSlot]
  step swapR 0
  norm
  step popR
  step swapR 2
  norm
  step swapR 1
  norm
  step popR
  step popR
  step jumpR
  at_pc 7241
  step jumpdestR
  step swapR 0
  norm
  step popR
  step jumpdestR
  step swapR 2
  norm
  step swapR 1
  norm
  step popR
  step popR
  step jumpR
  at_pc 2132
  refine (ret (by decide) (size_mapMem (size_mapMem size_MEM0 _ _) _ _)
    (ptr_mapMem (size_mapMem size_MEM0 _ _) (ptr_mapMem size_MEM0 mload_MEM0 _ _) _ _)
    (rest := [_]) (by simp) (by gas_ok)).consequence (fun _ h => h) ?_
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  exact ⟨hr, he, ho, by rw [hgas]; gas_ok, hs, hss⟩

end UsdtVerify.GettersMap
