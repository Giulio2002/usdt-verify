import UsdtVerify.Evm.MemRev
import UsdtVerify.Usdt.Spec.Destroy

/-!
# The getters: the specifications from pc 0

Proves what a call of each getter does from pc 0: it returns the word of its slot, or of its
mapping entry.

The parts below keep their own headers:

- The getters without arguments
- The getters with address arguments
-/

section

/-!
## The getters without arguments

Each public getter is `entry` (value check, push the return address `r`, jump to the body `b`),
the body (reads the slot, leaves the value under `r`, jumps to `r`), and a return block at `r`
(`ret`, `retB` or `retA` of Usdt/Proofs/Common.lean). Write `C` for the contract.

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
    Gas.HoareG fork (At CODE message e [x] M gas state substate)
      (At CODE message b [BitVec.ofNat 256 r, x] M (gas - 34) state substate) := by
  simp only [ENTRY0, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hp
  rcases hp with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩
  all_goals
    step jumpdestR
    step Gas.callvalueG (by code_fact) (by code_fact) (by gas_ok) (by stk_ok)
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
    Gas.HoareG fork (At CODE message 0 [] .empty gas state substate)
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
    Gas.SpecG fork (At CODE message 0 [] .empty gas state substate)
      (Halted false (wordBytes (storageAt state message.currentTarget (BitVec.ofNat 256 k)))
        (gas - (164 + 22 * t + slotCost ck))
        (readSlot state message.currentTarget (BitVec.ofNat 256 k))
        (accessSlot substate message.currentTarget (BitVec.ofNat 256 k))) := by
  simp only [SLOT_GETTERS, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hp
  refine Gas.SpecG.seq ((toEntry (t := t) (e := e) (by rcases hp with h | h | h | h <;>
      (obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := h; decide)) hsize hsize' hsel (by omega)).seq
    (entry0 (r := r) (b := b) (by rcases hp with h | h | h | h <;>
      (obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := h; decide)) hv (by omega))) ?_
  rcases hp with ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  all_goals
    step jumpdestR
    step pushAnyR 1
    step Gas.sloadG hfork (cold := ck) (by code_fact) (by code_fact) hck (by gas_ok)
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
    Gas.SpecG fork (At CODE message 0 [] .empty gas state substate)
      (Halted false (wordBytes (storageAt state message.currentTarget 9)) (gas - (384 + slotCost c))
        (readSlot state message.currentTarget 9) (accessSlot substate message.currentTarget 9)) :=
  spec_slot (t := 10) (e := 1078) (r := 1097) (b := 4315) (k := 9) hfork (by decide) hsize hsize'
    hsel hv hc hg

theorem spec_maximumFee (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x35390714)
    (hv : message.value = 0) {c : Bool} (hc : coldIn substate message.currentTarget 4 = c)
    {gas : Nat} (hg : 406 + slotCost c ≤ gas) :
    Gas.SpecG fork (At CODE message 0 [] .empty gas state substate)
      (Halted false (wordBytes (storageAt state message.currentTarget 4)) (gas - (406 + slotCost c))
        (readSlot state message.currentTarget 4) (accessSlot substate message.currentTarget 4)) :=
  spec_slot (t := 11) (e := 1119) (r := 1138) (b := 4321) (k := 4) hfork (by decide) hsize hsize'
    hsel hv hc hg

theorem spec_totalSupplyVar (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x3eaaf86b)
    (hv : message.value = 0) {c : Bool} (hc : coldIn substate message.currentTarget 1 = c)
    {gas : Nat} (hg : 428 + slotCost c ≤ gas) :
    Gas.SpecG fork (At CODE message 0 [] .empty gas state substate)
      (Halted false (wordBytes (storageAt state message.currentTarget 1)) (gas - (428 + slotCost c))
        (readSlot state message.currentTarget 1) (accessSlot substate message.currentTarget 1)) :=
  spec_slot (t := 12) (e := 1160) (r := 1179) (b := 4327) (k := 1) hfork (by decide) hsize hsize'
    hsel hv hc hg

theorem spec_basisPointsRate (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xdd644f72)
    (hv : message.value = 0) {c : Bool} (hc : coldIn substate message.currentTarget 3 = c)
    {gas : Nat} (hg : 758 + slotCost c ≤ gas) :
    Gas.SpecG fork (At CODE message 0 [] .empty gas state substate)
      (Halted false (wordBytes (storageAt state message.currentTarget 3)) (gas - (758 + slotCost c))
        (readSlot state message.currentTarget 3) (accessSlot substate message.currentTarget 3)) :=
  spec_slot (t := 27) (e := 2154) (r := 2173) (b := 7250) (k := 3) hfork (by decide) hsize hsize'
    hsel hv hc hg

/-! ## MAX_UINT -/

/-- `MAX_UINT()` returns the word 2^256 - 1, with no storage read. -/
theorem spec_maxUint (hsize : 4 ≤ message.data.size) (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0xe5b5019a) (hv : message.value = 0) {gas : Nat}
    (hg : 824 ≤ gas) :
    Gas.SpecG fork (At CODE message 0 [] .empty gas state substate)
      (Halted false (wordBytes (BitVec.ofNat 256 (2 ^ 256 - 1))) (gas - 824) state substate) := by
  refine Gas.SpecG.seq ((toEntry (t := 30) (e := 2333) (by decide) hsize hsize' hsel (by omega)).seq
    (entry0 (r := 2352) (b := 7569) (by decide) hv (by omega))) ?_
  step jumpdestR
  step Gas.pushG (n := 32) (word := BitVec.ofNat 256 (2 ^ 256 - 1)) (by decide) (by code_fact)
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
    Gas.SpecG fork (At CODE message 0 [] .empty gas state substate)
      (Halted false (wordBytes (if byte20 (storageAt state message.currentTarget
          (BitVec.ofNat 256 k)) = 0 then 0 else 1))
        (gas - (262 + 22 * t + slotCost ck))
        (readSlot state message.currentTarget (BitVec.ofNat 256 k))
        (accessSlot substate message.currentTarget (BitVec.ofNat 256 k))) := by
  have hexp : exponentBytes (0x14 : U256) = 1 := by decide
  simp only [FLAG_GETTERS, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hp
  refine Gas.SpecG.seq ((toEntry (t := t) (e := e) (by rcases hp with h | h <;>
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
    step Gas.sloadG hfork (cold := ck) (by code_fact) (by code_fact) hck (by gas_ok)
    rw [getStorage_eq]
    step swapR 0
    norm
    step pushR 2 (0x0100 : U256)
    step Gas.expLG (Nat.le_trans (by decide) hfork) (by code_fact) (by code_fact) (by gas_ok)
    step swapR 0
    norm
    step binR 0x04 (instruction_of_stackOnlyStep rfl)
    step pushR 1 (0xff : U256)
    step binR 0x16 (instruction_of_stackOnlyStep rfl)
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
    Gas.SpecG fork (At CODE message 0 [] .empty gas state substate)
      (Halted false (wordBytes (if byte20 (storageAt state message.currentTarget 10) = 0 then 0
          else 1)) (gas - (350 + slotCost c))
        (readSlot state message.currentTarget 10) (accessSlot substate message.currentTarget 10)) :=
  spec_flag (t := 4) (e := 676) (r := 695) (b := 3265) (k := 10) hfork (by decide) hsize hsize'
    hsel hv hc hg

theorem spec_paused (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x5c975abb)
    (hv : message.value = 0) {c : Bool} (hc : coldIn substate message.currentTarget 0 = c)
    {gas : Nat} (hg : 614 + slotCost c ≤ gas) :
    Gas.SpecG fork (At CODE message 0 [] .empty gas state substate)
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
    Gas.SpecG fork (At CODE message 0 [] .empty gas state substate)
      (Halted false (wordBytes (bitwiseAnd ADDR_MASK (storageAt state message.currentTarget 10)))
        (gas - (388 + slotCost c))
        (readSlot state message.currentTarget 10) (accessSlot substate message.currentTarget 10)) := by
  have hexp : exponentBytes (0 : U256) = 0 := by decide
  refine Gas.SpecG.seq ((toEntry (t := 8) (e := 916) (by decide) hsize hsize' hsel (by omega)).seq
    (entry0 (r := 935) (b := 4253) (by decide) hv (by omega))) ?_
  step jumpdestR
  step pushR 1 (0x0a : U256)
  step pushR 1 (0 : U256)
  step swapR 0
  norm
  step Gas.sloadG hfork (cold := c) (by code_fact) (by code_fact) hc (by gas_ok)
  rw [getStorage_eq]
  step swapR 0
  norm
  step pushR 2 (0x0100 : U256)
  step Gas.expLG (Nat.le_trans (by decide) hfork) (by code_fact) (by code_fact) (by gas_ok)
  step swapR 0
  norm
  step binR 0x04 (instruction_of_stackOnlyStep rfl)
  step pushR 20 ADDR_MASK
  step binR 0x16 (instruction_of_stackOnlyStep rfl)
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
    Gas.SpecG fork (At CODE message 0 [] .empty gas state substate)
      (Halted false (wordBytes (ownerOf state message.currentTarget))
        (gas - (652 + slotCost c))
        (readSlot state message.currentTarget 0) (accessSlot substate message.currentTarget 0)) := by
  have hexp : exponentBytes (0 : U256) = 0 := by decide
  refine Gas.SpecG.seq ((toEntry (t := 20) (e := 1639) (by decide) hsize hsize' hsel (by omega)).seq
    (entry0 (r := 1658) (b := 5169) (by decide) hv (by omega))) ?_
  step jumpdestR
  step pushR 1 (0 : U256)
  step dupR 0
  step swapR 0
  norm
  step Gas.sloadG hfork (cold := c) (by code_fact) (by code_fact) hc (by gas_ok)
  rw [getStorage_eq]
  step swapR 0
  norm
  step pushR 2 (0x0100 : U256)
  step Gas.expLG (Nat.le_trans (by decide) hfork) (by code_fact) (by code_fact) (by gas_ok)
  step swapR 0
  norm
  step binR 0x04 (instruction_of_stackOnlyStep rfl)
  step pushR 20 ADDR_MASK
  step binR 0x16 (instruction_of_stackOnlyStep rfl)
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
    Gas.SpecG fork (At CODE message 0 [] .empty gas state substate)
      (Halted false (wordBytes (ownerOf state message.currentTarget))
        (gas - (638 + slotCost c))
        (readSlot state message.currentTarget 0) (accessSlot substate message.currentTarget 0)) := by
  have hexp : exponentBytes (0 : U256) = 0 := by decide
  refine Gas.SpecG.seq ((toEntry (t := 19) (e := 1554) (by decide) hsize hsize' hsel (by omega)).seq
    (entry0 (r := 1573) (b := 5128) (by decide) hv (by omega))) ?_
  step jumpdestR
  step pushR 1 (0 : U256)
  step dupR 0
  step pushR 1 (0 : U256)
  step swapR 0
  norm
  step Gas.sloadG hfork (cold := c) (by code_fact) (by code_fact) hc (by gas_ok)
  rw [getStorage_eq]
  step swapR 0
  norm
  step pushR 2 (0x0100 : U256)
  step Gas.expLG (Nat.le_trans (by decide) hfork) (by code_fact) (by code_fact) (by gas_ok)
  step swapR 0
  norm
  step binR 0x04 (instruction_of_stackOnlyStep rfl)
  step pushR 20 ADDR_MASK
  step binR 0x16 (instruction_of_stackOnlyStep rfl)
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

end

section

/-!
## The getters with address arguments

`a`, `a0`, `a1` are argument words 0 and 1 masked to 160 bits (`addrArg`).

- balances(a) (public mapping, 4291): returns `balances[a]`, slot `keccak(a ++ 2)`.
- isBlackListed(a) (public mapping, 7256) and getBlackListStatus(a) (4523): return 1 if the low
  byte of `isBlackListed[a]` (slot `keccak(a ++ 6)`) is nonzero, else 0.
- allowed(a0, a1) (public mapping, 4609): returns `allowed[a0][a1]`, slot
  `keccak(a1 ++ keccak(a0 ++ 5))`.
- allowance(a0, a1) (6925), when not deprecated: the same slot, through StandardToken's
  `allowance` (lookup at 10814).

The public mapping getters write the base word at 32 before the key word at 0 (`pubMem`); their
hash reads the two words through `memoryReadBytes_write_rev` (Evm/MemRev.lean).
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
    Gas.HoareG fork (At CODE message e [x] M gas state substate)
      (At CODE message b [addrArg message.data 0, BitVec.ofNat 256 r, x] M (gas - 74) state
        substate) := by
  simp only [ENTRY1M, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hp
  rcases hp with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
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
    step pushR 20 ADDR_MASK
    step binR 0x16 (instruction_of_stackOnlyStep rfl)
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
    Gas.HoareG fork (At CODE message e [x] M gas state substate)
      (At CODE message b [addrArg message.data 1, addrArg message.data 0, BitVec.ofNat 256 r, x]
        M (gas - 104) state substate) := by
  simp only [ENTRY2, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hp
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
    step pushR 20 ADDR_MASK
    step binR 0x16 (instruction_of_stackOnlyStep rfl)
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
    step pushR 20 ADDR_MASK
    step binR 0x16 (instruction_of_stackOnlyStep rfl)
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
    Gas.HoareG fork (At CODE message p (base :: k :: rest) M gas state substate)
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
    step Gas.mstoreG (by code_fact) (by code_fact) (by rw [hext1]; gas_ok)
    step Gas.reshapeG (m' := memoryWrite M 32 (wordBytes base)) rfl
      (by rw [hext1, memoryExtend_zero]; rfl) (by rw [hext1] <;> gas_ok)
    step dupR 0
    step pushR 1 (0 : U256)
    step Gas.mstoreG (by code_fact) (by code_fact) (by rw [hext2]; gas_ok)
    step Gas.reshapeG (m' := pubMem M k base) rfl (by rw [hext2, memoryExtend_zero]; rfl)
      (by rw [hext2] <;> gas_ok)
    step pushR 1 (0x40 : U256)
    step pushR 1 (0 : U256)
    step Gas.keccak256G (by code_fact) (by code_fact) (by rw [hk, hext3]; gas_ok)
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
    Gas.SpecG fork (At CODE message 0 [] .empty gas state substate)
      (Halted false (wordBytes (storageAt state message.currentTarget
          (mapSlot (addrArg message.data 0) 2)))
        (gas - (478 + slotCost c))
        (readSlot state message.currentTarget (mapSlot (addrArg message.data 0) 2))
        (accessSlot substate message.currentTarget (mapSlot (addrArg message.data 0) 2))) := by
  refine Gas.SpecG.seq ((toEntry (t := 9) (e := 1001) (by decide) hsize hsize' hsel (by omega)).seq
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
  step Gas.sloadG hfork (cold := c) (by code_fact) (by code_fact) hc (by gas_ok)
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
    Gas.SpecG fork (At CODE message 0 [] .empty gas state substate)
      (Halted false (wordBytes (if (storageAt state message.currentTarget
          (mapSlot (addrArg message.data 0) 6)).toNat % 256 = 0 then 0 else 1))
        (gas - (933 + slotCost c))
        (readSlot state message.currentTarget (mapSlot (addrArg message.data 0) 6))
        (accessSlot substate message.currentTarget (mapSlot (addrArg message.data 0) 6))) := by
  have hexp : exponentBytes (0 : U256) = 0 := by decide
  refine Gas.SpecG.seq ((toEntry (t := 28) (e := 2195) (by decide) hsize hsize' hsel (by omega)).seq
    (entry1m (r := 2250) (b := 7256) (by decide) hv (by omega))) ?_
  step jumpdestR
  step pushR 1 (0x06 : U256)
  step hashPub (Or.inr (Or.inl rfl)) (by simp) size_MEM0 (by gas_ok)
  step pushR 1 (0 : U256)
  step swapR 1
  norm
  step popR
  step Gas.sloadG hfork (cold := c) (by code_fact) (by code_fact) hc (by gas_ok)
  rw [getStorage_eq]
  step swapR 0
  norm
  step pushR 2 (0x0100 : U256)
  step Gas.expLG (Nat.le_trans (by decide) hfork) (by code_fact) (by code_fact) (by gas_ok)
  step swapR 0
  norm
  step binR 0x04 (instruction_of_stackOnlyStep rfl)
  step pushR 1 (0xff : U256)
  step binR 0x16 (instruction_of_stackOnlyStep rfl)
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
    Gas.SpecG fork (At CODE message 0 [] .empty gas state substate)
      (Halted false (wordBytes (if (storageAt state message.currentTarget
          (mapSlot (addrArg message.data 0) 6)).toNat % 256 = 0 then 0 else 1))
        (gas - (663 + slotCost c))
        (readSlot state message.currentTarget (mapSlot (addrArg message.data 0) 6))
        (accessSlot substate message.currentTarget (mapSlot (addrArg message.data 0) 6))) := by
  have hexp : exponentBytes (0 : U256) = 0 := by decide
  have hk := mkey_addrArg message.data 0
  refine Gas.SpecG.seq ((toEntry (t := 14) (e := 1222) (by decide) hsize hsize' hsel (by omega)).seq
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
  step Gas.sloadG hfork (cold := c) (by code_fact) (by code_fact) hc (by gas_ok)
  rw [getStorage_eq]
  step swapR 0
  norm
  step pushR 2 (0x0100 : U256)
  step Gas.expLG (Nat.le_trans (by decide) hfork) (by code_fact) (by code_fact) (by gas_ok)
  step swapR 0
  norm
  step binR 0x04 (instruction_of_stackOnlyStep rfl)
  step pushR 1 (0xff : U256)
  step binR 0x16 (instruction_of_stackOnlyStep rfl)
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

/-- The slot of `allowed[a0][a1]`: `keccak(a1 ++ keccak(a0 ++ 5))`. -/
abbrev allowSlot (data : ByteArray) : U256 :=
  mapSlot (addrArg data 1) (mapSlot (addrArg data 0) 5)

/-- The first hash of `allowed` at 4612: `base` at 32, the second word below (`k`) at 0. -/
theorem hashPub2 {k1 k base : U256} {rest : List U256} (hrest : rest.length ≤ 900)
    {M : ByteArray} (hM : M.size = 96) {gas : Nat} (hg : 63 ≤ gas) :
    Gas.HoareG fork (At CODE message 4612 (base :: k1 :: k :: rest) M gas state substate)
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
  step Gas.mstoreG (by code_fact) (by code_fact) (by rw [hext1]; gas_ok)
  step Gas.reshapeG (m' := memoryWrite M 32 (wordBytes base)) rfl
    (by rw [hext1, memoryExtend_zero]; rfl) (by rw [hext1] <;> gas_ok)
  step dupR 1
  step pushR 1 (0 : U256)
  step Gas.mstoreG (by code_fact) (by code_fact) (by rw [hext2]; gas_ok)
  step Gas.reshapeG (m' := pubMem M k base) rfl (by rw [hext2, memoryExtend_zero]; rfl)
    (by rw [hext2] <;> gas_ok)
  step pushR 1 (0x40 : U256)
  step pushR 1 (0 : U256)
  step Gas.keccak256G (by code_fact) (by code_fact) (by rw [hk, hext3]; gas_ok)
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
    Gas.SpecG fork (At CODE message 0 [] .empty gas state substate)
      (Halted false (wordBytes (storageAt state message.currentTarget (allowSlot message.data)))
        (gas - (705 + slotCost c))
        (readSlot state message.currentTarget (allowSlot message.data))
        (accessSlot substate message.currentTarget (allowSlot message.data))) := by
  refine Gas.SpecG.seq ((toEntry (t := 15) (e := 1303) (by decide) hsize hsize' hsel (by omega)).seq
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
  step Gas.sloadG hfork (cold := c) (by code_fact) (by code_fact) hc (by gas_ok)
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
    Gas.SpecG fork (At CODE message 0 [] .empty gas state substate)
      (Halted false (wordBytes (storageAt state message.currentTarget (allowSlot message.data)))
        (gas - (1156 + slotCost c10 + slotCost c))
        (readSlot (readSlot state message.currentTarget 10) message.currentTarget
          (allowSlot message.data))
        (accessSlot (accessSlot substate message.currentTarget 10) message.currentTarget
          (allowSlot message.data))) := by
  have hk0 := mkey_addrArg message.data 0
  have hk1 := mkey_addrArg message.data 1
  refine Gas.SpecG.seq ((toEntry (t := 26) (e := 2046) (by decide) hsize hsize' hsel (by omega)).seq
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
  step Gas.sloadG hfork (cold := c) (by code_fact) (by code_fact) hc (by gas_ok)
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

end
