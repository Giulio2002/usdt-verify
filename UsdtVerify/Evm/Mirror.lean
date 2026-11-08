import UsdtVerify.Evm.GasRules
import UsdtVerify.Evm.Exact
import UsdtVerify.Evm.MemRev
import UsdtVerify.Evm.Storage
import UsdtVerify.Evm.Runners

/-!
# GENERIC: a contract that answers `balanceOf(a)` from its own mapping at slot 2

Round 30 (docs/AUDIT.md, findings 2 and 3). `MIRROR` is 25 bytes of bytecode:

```
PUSH1 2  PUSH1 32  MSTORE        ; memory[32..64] := 2
PUSH1 4  CALLDATALOAD  PUSH1 0  MSTORE   ; memory[0..32] := the word at byte 4 of the call data
PUSH1 64  PUSH1 0  KECCAK256     ; keccak(word ++ 2): the slot of the word in a mapping at 2
SLOAD                            ; the word in that slot of the running account
PUSH1 0  MSTORE  PUSH1 32  PUSH1 0  RETURN   ; return it
```

It ignores the selector. For the call data of `balanceOf(a)` (`SEL ++ wordBytes a`), it returns
the word in slot `keccak(a ++ 2)` of its own storage, the slot of `balances[a]` in USDT's layout.

- `mirror_spec`: from Berlin, a frame of `MIRROR` at pc 0 with the word `k` at byte 4 of its call
  data and at least `87 + slotCost c` gas (`c`: whether the slot is cold) returns the 32 bytes
  of `storageAt state target (mapSlot k 2)`, with the slot recorded read and accessed, and
  `87 + slotCost c` gas paid.
- `process_mirror`: from Paris, a message that runs `MIRROR` (no value, no precompile), run by
  EthLib's `processRunner` with any gas, that ends with no error returns the word in that slot
  of its current target in the caller's state, and ends in the caller's state with the slot
  recorded read (`Complete.ok_exact`: a successful run with less gas ends as `mirror_spec` says).
-/

namespace UsdtVerify

open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic

variable {fork : Fork}

/-- The bytecode of the mirror contract. -/
def MIRROR : ByteArray :=
  ⟨#[0x60, 0x02, 0x60, 0x20, 0x52, 0x60, 0x04, 0x35, 0x60, 0x00, 0x52, 0x60, 0x40, 0x60, 0x00,
    0x20, 0x54, 0x60, 0x00, 0x52, 0x60, 0x20, 0x60, 0x00, 0xf3]⟩

theorem size_MIRROR : MIRROR.size = 25 := rfl

theorem delegatedAddress_mirror : delegatedAddress MIRROR = none := by decide

/-- PUSH1 of `w` in `MIRROR`. -/
local macro "mpush " w:term:max : term =>
  `(Gas.pushG (n := 1) (word := $w) (by decide) (by decide) (by decide)
    (decode_push 1 (by decide)) (by decide) (by omega) (by simp [STACK_LIMIT]))

theorem mirror_spec (hfork : .berlin ≤ fork) {message : Message fork}
    {state : State.TransactionState} {substate : Substate} {k : U256}
    (hk : loadWord message.data 4 32 = k) {c : Bool}
    (hc : coldIn substate message.currentTarget (mapSlot k 2) = c) {gas : Nat}
    (hg : 87 + slotCost c ≤ gas) :
    Gas.SpecG fork (At MIRROR message 0 [] .empty gas state substate)
      (Halted false (wordBytes (storageAt state message.currentTarget (mapSlot k 2)))
        (gas - (87 + slotCost c)) (readSlot state message.currentTarget (mapSlot k 2))
        (accessSlot substate message.currentTarget (mapSlot k 2))) := by
  have hs : slotCost c ≤ 2100 := by unfold slotCost; split <;> omega
  simp only [slotCost] at hg hs ⊢
  have hext1 : extendMemory ByteArray.empty.size [((32 : U256), (32 : U256))] = ⟨6, 64⟩ := by
    decide
  have hZ : (memoryExtend ByteArray.empty 64).size = 64 := by
    rw [size_memoryExtend]; rfl
  have hM1 : (memoryWrite (memoryExtend ByteArray.empty 64) 32 (wordBytes 2)).size = 64 := by
    rw [size_memoryWrite (by rw [hZ, size_wordBytes]; omega), hZ]
  have hext2 : extendMemory (memoryWrite (memoryExtend ByteArray.empty 64) 32 (wordBytes 2)).size
      [((0 : U256), (32 : U256))] = ⟨0, 0⟩ := by rw [hM1]; decide
  have hM2 : (memoryWrite (memoryWrite (memoryExtend ByteArray.empty 64) 32 (wordBytes 2)) 0
      (wordBytes k)).size = 64 := by
    rw [size_memoryWrite (by rw [hM1, size_wordBytes]; omega), hM1]
  have hext3 : extendMemory (memoryWrite (memoryWrite (memoryExtend ByteArray.empty 64) 32
      (wordBytes 2)) 0 (wordBytes k)).size [((0 : U256), (64 : U256))] = ⟨0, 0⟩ := by
    rw [hM2]; decide
  have hext4 : extendMemory (memoryWrite (memoryWrite (memoryExtend ByteArray.empty 64) 32
      (wordBytes 2)) 0 (wordBytes k)).size [((0 : U256), (32 : U256))] = ⟨0, 0⟩ := by
    rw [hM2]; decide
  have hkc : keccak256Cost (64 : U256) = 42 := by decide
  have hread : memoryReadBytes (memoryWrite (memoryWrite (memoryExtend ByteArray.empty 64) 32
      (wordBytes 2)) 0 (wordBytes k)) 0 64 = wordBytes k ++ wordBytes 2 := by
    have h := memoryReadBytes_write_rev (memory := memoryExtend ByteArray.empty 64)
      (a := wordBytes k) (b := wordBytes 2) (s := 0) (by rw [hZ, size_wordBytes, size_wordBytes]; omega)
    simpa [size_wordBytes] using h
  step mpush (2 : U256)
  step mpush (32 : U256)
  step Gas.mstoreG (by decide) (by decide) (by simp only [hext1]; omega)
  simp only [hext1, show (32 : U256).toNat = 32 from rfl, show (0 : U256).toNat = 0 from rfl, show (64 : U256).toNat = 64 from rfl, show (4 : U256).toNat = 4 from rfl]
  step mpush (4 : U256)
  step Gas.calldataloadG (by decide) (by decide) (by omega)
  step mpush (0 : U256)
  step Gas.mstoreG (by decide) (by decide) (by simp only [hext2]; omega)
  simp only [hext2, memoryExtend_zero, show (32 : U256).toNat = 32 from rfl, show (0 : U256).toNat = 0 from rfl, show (64 : U256).toNat = 64 from rfl, show (4 : U256).toNat = 4 from rfl, hk]
  step mpush (64 : U256)
  step mpush (0 : U256)
  step Gas.keccak256G (by decide) (by decide) (by simp only [hext3, hkc]; omega)
  simp only [hext3, hkc, memoryExtend_zero, show (32 : U256).toNat = 32 from rfl, show (0 : U256).toNat = 0 from rfl, show (64 : U256).toNat = 64 from rfl, show (4 : U256).toNat = 4 from rfl, hread]
  step Gas.sloadG hfork (cold := c) (by decide) (by decide)
    (by exact hc)
    (by omega)
  step mpush (0 : U256)
  step Gas.mstoreG (by decide) (by decide) (by simp only [hext4]; omega)
  simp only [hext4, memoryExtend_zero, show (32 : U256).toNat = 32 from rfl, show (0 : U256).toNat = 0 from rfl, show (64 : U256).toNat = 64 from rfl, show (4 : U256).toNat = 4 from rfl]
  step mpush (32 : U256)
  step mpush (0 : U256)
  have hM3 : (memoryWrite (memoryWrite (memoryWrite (memoryExtend ByteArray.empty 64) 32
      (wordBytes 2)) 0 (wordBytes k)) 0 (wordBytes (state.getStorage message.currentTarget
        (keccak (wordBytes k ++ wordBytes 2)).toBeBytes))).size = 64 := by
    rw [size_memoryWrite (by rw [hM2, size_wordBytes]; omega), hM2]
  have hext5 : extendMemory (memoryWrite (memoryWrite (memoryWrite (memoryExtend ByteArray.empty 64)
      32 (wordBytes 2)) 0 (wordBytes k)) 0 (wordBytes (state.getStorage message.currentTarget
        (keccak (wordBytes k ++ wordBytes 2)).toBeBytes))).size [((0 : U256), (32 : U256))] = ⟨0, 0⟩ := by
    rw [hM3]; decide
  refine (Gas.returnG (by decide) (by decide) (by rw [hext5]; exact Nat.zero_le _)).consequence
    (fun _ h => h) ?_
  rintro evm ⟨hr, he, ho, hgas, hst, hss⟩
  refine ⟨hr, he, ?_, ?_, hst, hss⟩
  · rw [ho, hext5, memoryExtend_zero]
    have h := memoryReadBytes_memoryWrite (memory := memoryWrite (memoryWrite
      (memoryExtend ByteArray.empty 64) 32 (wordBytes 2)) 0 (wordBytes k)) (start := 0)
      (value := wordBytes (state.getStorage message.currentTarget (keccak (wordBytes k ++ wordBytes 2)).toBeBytes))
      (by rw [hM2, size_wordBytes]; omega)
    rw [size_wordBytes] at h
    exact h
  · rw [hgas, hext5]
    dsimp only
    omega

/-- From Paris, a message that runs `MIRROR` at a target, with no value, no precompile and the word
`k` at byte 4 of its call data, run by `processRunner`: if it ends with no error, it returns the
word in slot `mapSlot k 2` of its current target in the caller's state, and ends in the caller's
state with that slot recorded read. -/
theorem process_mirror (hparis : .paris ≤ fork) {bound : Nat} (caller : Evm fork Nat)
    {msg : Message fork} (lt : msg.gas < bound) (hcode : msg.code = MIRROR)
    {ua : EthLib.Base.Address} (ht : msg.target = some ua) (hv : msg.value = 0)
    (hpre : precompileAddress fork msg = none) {k : U256} (hk : loadWord msg.data 4 32 = k)
    {child : { evm : Evm fork Nat // GasMeter.gasHeld evm.gas ≤ msg.gas }}
    (hch : processRunner fork bound caller msg lt = .ok child) (he : child.1.error = none) :
    child.1.output = wordBytes (storageAt caller.state msg.currentTarget (mapSlot k 2)) ∧
      child.1.state = readSlot caller.state msg.currentTarget (mapSlot k 2) := by
  have hberlin : .berlin ≤ fork := Nat.le_trans (by decide) hparis
  have hst : startState fork msg caller.state = caller.state := by
    simp only [startState, show ¬fork < Fork.paris from Nat.not_lt.mpr hparis, ite_false]
  have hp : processRunner fork bound caller msg lt =
      processMessage fork msg caller.state caller.substate.child := by
    simp only [processRunner, ht]
  cases hr : runFrame (step fork) (step_decreases fork) msg.gas (processRunner fork msg.gas)
      (startFrame msg (startState fork msg caller.state) caller.substate.child
        (GasMeter.start msg.gas msg.reservoir)) (Nat.le_refl _) with
  | error e =>
    have hm := processMessage_map_val (fun h => h.2 hv) hpre hr
    rw [← hp, hch] at hm
    cases hm
  | ok s =>
    have hm := processMessage_map_val (fun h => h.2 hv) hpre hr
    rw [← hp, hch] at hm
    have hc : child.1 = rollbackOnError caller.state s := by simpa [Except.map] using hm
    have hse : s.error = none := by
      rw [hc] at he
      unfold rollbackOnError at he
      split at he <;> exact he
    obtain ⟨-, -, ho, -, hs, -⟩ := Complete.ok_exact (Nat.le_refl _)
      (fun g hg => mirror_spec (state := startState fork msg caller.state)
        (substate := caller.substate.child) hberlin hk rfl hg)
      (at_startFrame hcode _ _) (Nat.le_refl _) hr hse
    rw [hc, rollbackOnError_of_error_eq_none hse, ho, hs, hst]
    exact ⟨rfl, rfl⟩

end UsdtVerify
