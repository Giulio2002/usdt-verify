import UsdtVerify.Functions.DestroySpec

/-!
# The getters without arguments

Each public getter is `entry` (value check, push the return address `r`, jump to the body `b`),
the body (reads the slot, leaves the value under `r`, jumps to `r`), and a return block at `r`
(`ret`, `retB` or `retA` of Common.lean). Write `C` for the contract.

- uint slots (`SLOT_GETTERS`): decimals() slot 9, maximumFee() slot 4, _totalSupply() slot 1,
  basisPointsRate() slot 3: the 32 bytes of the slot word.
- MAX_UINT(): the word 2^256 - 1 (a constant, no read).
- flags (`FLAG_GETTERS`): deprecated() (byte 20 of slot 10), paused() (byte 20 of slot 0): the
  word 1 if the byte is nonzero, else 0.
- addresses: upgradedAddress() (slot 10), owner() and getOwner() (slot 0): the low 160 bits of
  the slot word.
-/

namespace UsdtVerify.Getters

open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts
open Transfer TransferOk Owner Admin BlackList Issue

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate}

/-- The entries `(e, r, b)` of the getters without arguments. -/
abbrev ENTRY0 : List (Nat × Nat × Nat) := [(676, 695, 3265), (916, 935, 4253),
  (1078, 1097, 4315), (1119, 1138, 4321), (1160, 1179, 4327), (1411, 1430, 4646),
  (1554, 1573, 5128), (1639, 1658, 5169), (2154, 2173, 7250), (2333, 2352, 7569)]

/-- The entry of a getter without arguments: with no value, jump to the body `b` with the return
address `r` pushed. -/
theorem entry0 {e r b : Nat} (hp : (e, r, b) ∈ ENTRY0) (hv : message.value = 0) {x : U256}
    {M : ByteArray} {gas : Nat} (hg : 34 ≤ gas) :
    Hoare fork (At CODE message e [x] M gas state substate)
      (At CODE message b [BitVec.ofNat 256 r, x] M (gas - 34) state substate) := by
  simp only [ENTRY0, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hp
  rcases hp with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩
  all_goals
    step jumpdestR
    step Logic.callvalue (by code_fact) (by code_fact) (by gas_ok) (by stk_ok)
    step unR 0x15 instruction_iszero
    step pushAnyR 2
    step jumpiR (by simp [hv, isZero])
    step jumpdestR
    step pushAnyR 2
    step pushAnyR 2
    step jumpR
    exact restate (by decide) (congrArg (· :: [x]) (by decide)) rfl (by gas_ok) rfl rfl

/-- From pc 0 to the entry `e` of the selector `sel`, the `t`-th key of the table. -/
theorem toEntry {sel t e : Nat}
    (ht : tested (BitVec.ofNat 256 sel) ENTRIES = t ∧
      branch (BitVec.ofNat 256 sel) 54 (entrySize 4 2) ENTRIES = e)
    (hsize : 4 ≤ message.data.size) (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = sel) {gas : Nat} (hg : 62 + 22 * t ≤ gas) :
    Hoare fork (At CODE message 0 [] .empty gas state substate)
      (At CODE message e [BitVec.ofNat 256 (selector message.data)] MEM0 (gas - (62 + 22 * t))
        state substate) := by
  have h1 := dispatch (state := state) (substate := substate) hsize hsize' (gas := gas)
    (by rw [hsel, ht.1]; omega)
  rw [hsel, ht.1, ht.2] at h1
  rw [hsel]
  exact h1.seq (restate rfl rfl rfl (by omega) rfl rfl)

/-! ## uint slots -/

/-- The getters of a uint slot `(sel, t, e, r, b, k)`: selector, its table key number, entry,
return block, body, slot. -/
abbrev SLOT_GETTERS : List (Nat × Nat × Nat × Nat × Nat × Nat) :=
  [(0x313ce567, 10, 1078, 1097, 4315, 9), (0x35390714, 11, 1119, 1138, 4321, 4),
   (0x3eaaf86b, 12, 1160, 1179, 4327, 1), (0xdd644f72, 27, 2154, 2173, 7250, 3)]

/-- The specification of the getters of a uint slot (decimals, maximumFee, _totalSupply,
basisPointsRate): the run returns the 32 bytes of slot `k`, after one read of it. -/
theorem spec_slot (hfork : .berlin ≤ fork) {sel t e r b k : Nat}
    (hp : (sel, t, e, r, b, k) ∈ SLOT_GETTERS) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = sel)
    (hv : message.value = 0) {ck : Bool}
    (hck : coldIn substate message.currentTarget (BitVec.ofNat 256 k) = ck) {gas : Nat}
    (hg : 164 + 22 * t + slotCost ck ≤ gas) :
    Spec fork (At CODE message 0 [] .empty gas state substate)
      (Halted false (wordBytes (storageAt state message.currentTarget (BitVec.ofNat 256 k)))
        (gas - (164 + 22 * t + slotCost ck))
        (readSlot state message.currentTarget (BitVec.ofNat 256 k))
        (accessSlot substate message.currentTarget (BitVec.ofNat 256 k))) := by
  simp only [SLOT_GETTERS, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hp
  refine Spec.seq ((toEntry (t := t) (e := e) (by rcases hp with h | h | h | h <;>
      (obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := h; decide)) hsize hsize' hsel (by omega)).seq
    (entry0 (r := r) (b := b) (by rcases hp with h | h | h | h <;>
      (obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := h; decide)) hv (by omega))) ?_
  rcases hp with ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  all_goals
    step jumpdestR
    step pushAnyR 1
    step sload hfork (cold := ck) (by code_fact) (by code_fact) hck (by gas_ok)
    rw [getStorage_eq]
    step dupR 1
    step jumpR
    first | at_pc 1097 | at_pc 1138 | at_pc 1179 | at_pc 2173
    refine (ret (by decide) size_MEM0 mload_MEM0 (rest := [_, _]) (by simp)
      (by gas_ok)).consequence (fun _ h => h) ?_
    rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
    exact ⟨hr, he, ho, by rw [hgas]; gas_ok, hs, hss⟩

theorem spec_decimals (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x313ce567)
    (hv : message.value = 0) {c : Bool} (hc : coldIn substate message.currentTarget 9 = c)
    {gas : Nat} (hg : 384 + slotCost c ≤ gas) :
    Spec fork (At CODE message 0 [] .empty gas state substate)
      (Halted false (wordBytes (storageAt state message.currentTarget 9)) (gas - (384 + slotCost c))
        (readSlot state message.currentTarget 9) (accessSlot substate message.currentTarget 9)) :=
  spec_slot (t := 10) (e := 1078) (r := 1097) (b := 4315) (k := 9) hfork (by decide) hsize hsize'
    hsel hv hc hg

theorem spec_maximumFee (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x35390714)
    (hv : message.value = 0) {c : Bool} (hc : coldIn substate message.currentTarget 4 = c)
    {gas : Nat} (hg : 406 + slotCost c ≤ gas) :
    Spec fork (At CODE message 0 [] .empty gas state substate)
      (Halted false (wordBytes (storageAt state message.currentTarget 4)) (gas - (406 + slotCost c))
        (readSlot state message.currentTarget 4) (accessSlot substate message.currentTarget 4)) :=
  spec_slot (t := 11) (e := 1119) (r := 1138) (b := 4321) (k := 4) hfork (by decide) hsize hsize'
    hsel hv hc hg

theorem spec_totalSupplyVar (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x3eaaf86b)
    (hv : message.value = 0) {c : Bool} (hc : coldIn substate message.currentTarget 1 = c)
    {gas : Nat} (hg : 428 + slotCost c ≤ gas) :
    Spec fork (At CODE message 0 [] .empty gas state substate)
      (Halted false (wordBytes (storageAt state message.currentTarget 1)) (gas - (428 + slotCost c))
        (readSlot state message.currentTarget 1) (accessSlot substate message.currentTarget 1)) :=
  spec_slot (t := 12) (e := 1160) (r := 1179) (b := 4327) (k := 1) hfork (by decide) hsize hsize'
    hsel hv hc hg

theorem spec_basisPointsRate (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xdd644f72)
    (hv : message.value = 0) {c : Bool} (hc : coldIn substate message.currentTarget 3 = c)
    {gas : Nat} (hg : 758 + slotCost c ≤ gas) :
    Spec fork (At CODE message 0 [] .empty gas state substate)
      (Halted false (wordBytes (storageAt state message.currentTarget 3)) (gas - (758 + slotCost c))
        (readSlot state message.currentTarget 3) (accessSlot substate message.currentTarget 3)) :=
  spec_slot (t := 27) (e := 2154) (r := 2173) (b := 7250) (k := 3) hfork (by decide) hsize hsize'
    hsel hv hc hg

/-! ## MAX_UINT -/

/-- `MAX_UINT()` returns the word 2^256 - 1, with no storage read. -/
theorem spec_maxUint (hsize : 4 ≤ message.data.size) (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0xe5b5019a) (hv : message.value = 0) {gas : Nat}
    (hg : 824 ≤ gas) :
    Spec fork (At CODE message 0 [] .empty gas state substate)
      (Halted false (wordBytes (BitVec.ofNat 256 (2 ^ 256 - 1))) (gas - 824) state substate) := by
  refine Spec.seq ((toEntry (t := 30) (e := 2333) (by decide) hsize hsize' hsel (by omega)).seq
    (entry0 (r := 2352) (b := 7569) (by decide) hv (by omega))) ?_
  step jumpdestR
  step push (n := 32) (word := BitVec.ofNat 256 (2 ^ 256 - 1)) (by decide) (by code_fact)
    (by code_fact) (decode_push 32 (by decide)) (by rw [pushData_CODE]; decide) (by gas_ok)
    (by stk_ok)
  step dupR 1
  step jumpR
  at_pc 2352
  refine (ret (by decide) size_MEM0 mload_MEM0 (rest := [_, _]) (by simp)
    (by gas_ok)).consequence (fun _ h => h) ?_
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  exact ⟨hr, he, ho, by rw [hgas]; gas_ok, hs, hss⟩

/-! ## Flags -/

/-- The word that the code returns for a flag at byte 20: 1 if the byte is nonzero, else 0. -/
theorem isZero4_flag (w : U256) :
    isZero (isZero (isZero (isZero (bitwiseAnd (0xff : U256)
      (div w (exp (0x0100 : U256) (0x14 : U256))))))) = if byte20 w = 0 then 0 else 1 := by
  by_cases h : byte20 w = 0
  · rw [flag_eq, h]; decide
  · rw [isZero3_flag h]; simp only [h, ↓reduceIte]; decide

/-- The flag getters `(sel, t, e, r, b, k)`: deprecated() (slot 10), paused() (slot 0). -/
abbrev FLAG_GETTERS : List (Nat × Nat × Nat × Nat × Nat × Nat) :=
  [(0x0e136b19, 4, 676, 695, 3265, 10), (0x5c975abb, 16, 1411, 1430, 4646, 0)]

/-- The specification of `deprecated()` and `paused()`: the run returns the word 1 if byte 20 of
slot `k` is nonzero and 0 otherwise, after one read of slot `k`. -/
theorem spec_flag (hfork : .berlin ≤ fork) {sel t e r b k : Nat}
    (hp : (sel, t, e, r, b, k) ∈ FLAG_GETTERS) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = sel)
    (hv : message.value = 0) {ck : Bool}
    (hck : coldIn substate message.currentTarget (BitVec.ofNat 256 k) = ck) {gas : Nat}
    (hg : 262 + 22 * t + slotCost ck ≤ gas) :
    Spec fork (At CODE message 0 [] .empty gas state substate)
      (Halted false (wordBytes (if byte20 (storageAt state message.currentTarget
          (BitVec.ofNat 256 k)) = 0 then 0 else 1))
        (gas - (262 + 22 * t + slotCost ck))
        (readSlot state message.currentTarget (BitVec.ofNat 256 k))
        (accessSlot substate message.currentTarget (BitVec.ofNat 256 k))) := by
  have hexp : exponentBytes (0x14 : U256) = 1 := by decide
  simp only [FLAG_GETTERS, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hp
  refine Spec.seq ((toEntry (t := t) (e := e) (by rcases hp with h | h <;>
      (obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := h; decide)) hsize hsize' hsel (by omega)).seq
    (entry0 (r := r) (b := b) (by rcases hp with h | h <;>
      (obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := h; decide)) hv (by omega))) ?_
  rcases hp with ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  all_goals
    step jumpdestR
    first | step pushR 1 (0x0a : U256) | step pushR 1 (0 : U256)
    step pushR 1 (0x14 : U256)
    step swapR 0
    norm
    step sload hfork (cold := ck) (by code_fact) (by code_fact) hck (by gas_ok)
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
    first | at_pc 695 | at_pc 1430
    refine (retB (by decide) size_MEM0 mload_MEM0 (rest := [_, _]) (by simp)
      (by gas_ok)).consequence (fun _ h => h) ?_
    rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
    refine ⟨hr, he, ?_, by rw [hgas]; gas_ok, hs, hss⟩
    rw [ho, isZero4_flag]; rfl

theorem spec_deprecated (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x0e136b19)
    (hv : message.value = 0) {c : Bool} (hc : coldIn substate message.currentTarget 10 = c)
    {gas : Nat} (hg : 350 + slotCost c ≤ gas) :
    Spec fork (At CODE message 0 [] .empty gas state substate)
      (Halted false (wordBytes (if byte20 (storageAt state message.currentTarget 10) = 0 then 0
          else 1)) (gas - (350 + slotCost c))
        (readSlot state message.currentTarget 10) (accessSlot substate message.currentTarget 10)) :=
  spec_flag (t := 4) (e := 676) (r := 695) (b := 3265) (k := 10) hfork (by decide) hsize hsize'
    hsel hv hc hg

theorem spec_paused (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x5c975abb)
    (hv : message.value = 0) {c : Bool} (hc : coldIn substate message.currentTarget 0 = c)
    {gas : Nat} (hg : 614 + slotCost c ≤ gas) :
    Spec fork (At CODE message 0 [] .empty gas state substate)
      (Halted false (wordBytes (if byte20 (storageAt state message.currentTarget 0) = 0 then 0
          else 1)) (gas - (614 + slotCost c))
        (readSlot state message.currentTarget 0) (accessSlot substate message.currentTarget 0)) :=
  spec_flag (t := 16) (e := 1411) (r := 1430) (b := 4646) (k := 0) hfork (by decide) hsize hsize'
    hsel hv hc hg

/-! ## Addresses -/

theorem addr_expr (w : U256) :
    bitwiseAnd ADDR_MASK (bitwiseAnd ADDR_MASK (bitwiseAnd ADDR_MASK
      (div w (exp (0x0100 : U256) (0 : U256))))) = bitwiseAnd ADDR_MASK w := by
  rw [owner_expr, mask_mask]

/-- `upgradedAddress()` returns the low 160 bits of slot 10. -/
theorem spec_upgradedAddress (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x26976e3f)
    (hv : message.value = 0) {c : Bool} (hc : coldIn substate message.currentTarget 10 = c)
    {gas : Nat} (hg : 388 + slotCost c ≤ gas) :
    Spec fork (At CODE message 0 [] .empty gas state substate)
      (Halted false (wordBytes (bitwiseAnd ADDR_MASK (storageAt state message.currentTarget 10)))
        (gas - (388 + slotCost c))
        (readSlot state message.currentTarget 10) (accessSlot substate message.currentTarget 10)) := by
  have hexp : exponentBytes (0 : U256) = 0 := by decide
  refine Spec.seq ((toEntry (t := 8) (e := 916) (by decide) hsize hsize' hsel (by omega)).seq
    (entry0 (r := 935) (b := 4253) (by decide) hv (by omega))) ?_
  step jumpdestR
  step pushR 1 (0x0a : U256)
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
  step pushR 20 ADDR_MASK
  step binR 0x16 Local.instruction_and
  step dupR 1
  step jumpR
  at_pc 935
  refine (retA (by decide) size_MEM0 mload_MEM0 (rest := [_, _]) (by simp)
    (by gas_ok)).consequence (fun _ h => h) ?_
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  refine ⟨hr, he, ?_, by rw [hgas]; gas_ok, hs, hss⟩
  rw [ho, addr_expr]

/-- `owner()` returns the low 160 bits of slot 0 (`ownerOf`). -/
theorem spec_owner (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x8da5cb5b)
    (hv : message.value = 0) {c : Bool} (hc : coldIn substate message.currentTarget 0 = c)
    {gas : Nat} (hg : 652 + slotCost c ≤ gas) :
    Spec fork (At CODE message 0 [] .empty gas state substate)
      (Halted false (wordBytes (ownerOf state message.currentTarget))
        (gas - (652 + slotCost c))
        (readSlot state message.currentTarget 0) (accessSlot substate message.currentTarget 0)) := by
  have hexp : exponentBytes (0 : U256) = 0 := by decide
  refine Spec.seq ((toEntry (t := 20) (e := 1639) (by decide) hsize hsize' hsel (by omega)).seq
    (entry0 (r := 1658) (b := 5169) (by decide) hv (by omega))) ?_
  step jumpdestR
  step pushR 1 (0 : U256)
  step dupR 0
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
  step pushR 20 ADDR_MASK
  step binR 0x16 Local.instruction_and
  step dupR 1
  step jumpR
  at_pc 1658
  refine (retA (by decide) size_MEM0 mload_MEM0 (rest := [_, _]) (by simp)
    (by gas_ok)).consequence (fun _ h => h) ?_
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  refine ⟨hr, he, ?_, by rw [hgas]; gas_ok, hs, hss⟩
  rw [ho, addr_expr]

/-- `getOwner()` returns the low 160 bits of slot 0 (`ownerOf`). -/
theorem spec_getOwner (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x893d20e8)
    (hv : message.value = 0) {c : Bool} (hc : coldIn substate message.currentTarget 0 = c)
    {gas : Nat} (hg : 638 + slotCost c ≤ gas) :
    Spec fork (At CODE message 0 [] .empty gas state substate)
      (Halted false (wordBytes (ownerOf state message.currentTarget))
        (gas - (638 + slotCost c))
        (readSlot state message.currentTarget 0) (accessSlot substate message.currentTarget 0)) := by
  have hexp : exponentBytes (0 : U256) = 0 := by decide
  refine Spec.seq ((toEntry (t := 19) (e := 1554) (by decide) hsize hsize' hsel (by omega)).seq
    (entry0 (r := 1573) (b := 5128) (by decide) hv (by omega))) ?_
  step jumpdestR
  step pushR 1 (0 : U256)
  step dupR 0
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
  step pushR 20 ADDR_MASK
  step binR 0x16 Local.instruction_and
  step swapR 0
  norm
  step popR
  step swapR 0
  norm
  step jumpR
  at_pc 1573
  refine (retA (by decide) size_MEM0 mload_MEM0 (rest := [_]) (by simp)
    (by gas_ok)).consequence (fun _ h => h) ?_
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  refine ⟨hr, he, ?_, by rw [hgas]; gas_ok, hs, hss⟩
  rw [ho, addr_expr]

end UsdtVerify.Getters
