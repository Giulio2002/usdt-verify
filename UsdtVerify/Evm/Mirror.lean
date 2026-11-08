import UsdtVerify.Evm.NoAbort
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
- Round 31: `mirror_specA` is `mirror_spec` over `StepGA` (Evm/NoAbort.lean), and `mirror_spec`
  follows from it. `process_mirror_iff`: from Paris, under `processRunner` with any gas, such a
  message gives a frame, never an error (`Gas.no_error_ga`). The frame ends with no error exactly
  when the message has at least `87 + slotCost c` gas, `c` the coldness of the slot in the
  caller's substate. Then it has that much less gas, the output and state of `process_mirror`,
  and the caller's substate (as `Substate.child` passes it on) with the slot accessed.
  `process_mirror` is derived from it.
- `hasAccount_readSlot_iff`: recording a read of a slot keeps every account.
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
  `(Gas.pushGA (n := 1) (word := $w) (by decide) (by decide) (by decide)
    (decode_push 1 (by decide)) (by decide) (by omega) (by simp [STACK_LIMIT]))

/-- `mirror_spec` over `StepGA` (Evm/NoAbort.lean): with less gas, every step of the run halts the
frame or follows it. -/
theorem mirror_specA (hfork : .berlin ≤ fork) {message : Message fork}
    {state : State.TransactionState} {substate : Substate} {k : U256}
    (hk : loadWord message.data 4 32 = k) {c : Bool}
    (hc : coldIn substate message.currentTarget (mapSlot k 2) = c) {gas : Nat}
    (hg : 87 + slotCost c ≤ gas) :
    Gas.SpecGA fork (At MIRROR message 0 [] .empty gas state substate)
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
  step Gas.mstoreGA (by decide) (by decide) (by simp only [hext1]; omega)
  simp only [hext1, show (32 : U256).toNat = 32 from rfl]
  step mpush (4 : U256)
  step Gas.calldataloadGA (by decide) (by decide) (by omega)
  step mpush (0 : U256)
  step Gas.mstoreGA (by decide) (by decide) (by simp only [hext2]; omega)
  simp only [hext2, memoryExtend_zero, show (0 : U256).toNat = 0 from rfl, show (4 : U256).toNat = 4 from rfl, hk]
  step mpush (64 : U256)
  step mpush (0 : U256)
  step Gas.keccak256GA (by decide) (by decide) (by simp only [hext3, hkc]; omega)
  simp only [hext3, hkc, memoryExtend_zero, show (0 : U256).toNat = 0 from rfl, show (64 : U256).toNat = 64 from rfl, hread]
  step Gas.sloadGA hfork (cold := c) (by decide) (by decide)
    (by exact hc)
    (by omega)
  step mpush (0 : U256)
  step Gas.mstoreGA (by decide) (by decide) (by simp only [hext4]; omega)
  simp only [hext4, memoryExtend_zero, show (0 : U256).toNat = 0 from rfl]
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
  refine (Gas.returnGA (by decide) (by decide) (by rw [hext5]; exact Nat.zero_le _)).consequence
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

theorem mirror_spec (hfork : .berlin ≤ fork) {message : Message fork}
    {state : State.TransactionState} {substate : Substate} {k : U256}
    (hk : loadWord message.data 4 32 = k) {c : Bool}
    (hc : coldIn substate message.currentTarget (mapSlot k 2) = c) {gas : Nat}
    (hg : 87 + slotCost c ≤ gas) :
    Gas.SpecG fork (At MIRROR message 0 [] .empty gas state substate)
      (Halted false (wordBytes (storageAt state message.currentTarget (mapSlot k 2)))
        (gas - (87 + slotCost c)) (readSlot state message.currentTarget (mapSlot k 2))
        (accessSlot substate message.currentTarget (mapSlot k 2))) :=
  (mirror_specA hfork hk hc hg).toG

/-- **`MIRROR` under `processRunner`, at every gas (round 31).** From Paris, a message that runs
`MIRROR` at a target, with no value, no precompile and the word `k` at byte 4 of its call data,
run by `processRunner` from any caller frame: the runner returns a frame (never an error), and
that frame ends with no error exactly when the message has at least `87 + slotCost c` gas, `c`
the coldness of slot `mapSlot k 2` of its current target in the caller's substate. Then it has
that much less gas, returns the word in that slot in the caller's state, ends in the caller's
state with the slot recorded read, and in the substate `Substate.child` passes on with the slot
accessed. -/
theorem process_mirror_iff (hparis : .paris ≤ fork) {bound : Nat} (caller : Evm fork Nat)
    {msg : Message fork} (lt : msg.gas < bound) (hcode : msg.code = MIRROR)
    {ua : EthLib.Base.Address} (ht : msg.target = some ua) (hv : msg.value = 0)
    (hpre : precompileAddress fork msg = none) {k : U256} (hk : loadWord msg.data 4 32 = k) :
    ∃ child, processRunner fork bound caller msg lt = .ok child ∧
      (child.1.error = none ↔
        87 + slotCost (coldIn caller.substate msg.currentTarget (mapSlot k 2)) ≤ msg.gas) ∧
      (child.1.error = none →
        child.1.gas = msg.gas - (87 + slotCost (coldIn caller.substate msg.currentTarget
          (mapSlot k 2))) ∧
        child.1.output = wordBytes (storageAt caller.state msg.currentTarget (mapSlot k 2)) ∧
        child.1.state = readSlot caller.state msg.currentTarget (mapSlot k 2) ∧
        child.1.substate = accessSlot caller.substate.child msg.currentTarget (mapSlot k 2)) := by
  have hberlin : .berlin ≤ fork := Nat.le_trans (by decide) hparis
  have hst : startState fork msg caller.state = caller.state := by
    simp only [startState, show ¬fork < Fork.paris from Nat.not_lt.mpr hparis, ite_false]
  have hp : processRunner fork bound caller msg lt =
      processMessage fork msg caller.state caller.substate.child := by
    simp only [processRunner, ht]
  have hspec : ∀ g, 87 + slotCost (coldIn caller.substate msg.currentTarget (mapSlot k 2)) ≤ g →
      Gas.SpecGA fork (At MIRROR msg 0 [] .empty g (startState fork msg caller.state)
        caller.substate.child)
      (Halted false (wordBytes (storageAt (startState fork msg caller.state) msg.currentTarget
          (mapSlot k 2)))
        (g - (87 + slotCost (coldIn caller.substate msg.currentTarget (mapSlot k 2))))
        (readSlot (startState fork msg caller.state) msg.currentTarget (mapSlot k 2))
        (accessSlot caller.substate.child msg.currentTarget (mapSlot k 2))) :=
    fun g hg => mirror_specA (state := startState fork msg caller.state)
      (substate := caller.substate.child) hberlin hk rfl hg
  cases hr : runFrame (step fork) (step_decreases fork) msg.gas (processRunner fork msg.gas)
      (startFrame msg (startState fork msg caller.state) caller.substate.child
        (GasMeter.start msg.gas msg.reservoir)) (Nat.le_refl _) with
  | error e => exact absurd hr (Gas.no_error_ga hspec (at_startFrame hcode _ _) _ e)
  | ok s =>
    have hm := processMessage_map_val (fun h => h.2 hv) hpre hr
    rw [← hp] at hm
    cases hpm : processRunner fork bound caller msg lt with
    | error e => rw [hpm] at hm; cases hm
    | ok child =>
      rw [hpm] at hm
      have hc : child.1 = rollbackOnError caller.state s := by simpa [Except.map] using hm
      have herr : child.1.error = s.error := by
        rw [hc]; unfold rollbackOnError; split <;> rfl
      refine ⟨child, rfl, ⟨fun he => ?_, fun hle => ?_⟩, fun he => ?_⟩
      · exact (Complete.ok_exact (Nat.le_refl _) (fun g hg => (hspec g hg).toG)
          (at_startFrame hcode _ _) (Nat.le_refl _) hr (herr ▸ he)).1
      · obtain ⟨stopped, hrun, -, hq⟩ := Gas.SpecG.runFrame (hspec msg.gas hle).toG
          (bound := msg.gas) (runChild := processRunner fork msg.gas) (at_startFrame hcode _ _)
          (Nat.le_refl _)
        rw [hr] at hrun
        cases hrun
        rw [herr]
        simpa using hq.1
      · have hse : s.error = none := herr ▸ he
        obtain ⟨-, -, ho, hg, hs, hss⟩ := Complete.ok_exact (Nat.le_refl _)
          (fun g hg => (hspec g hg).toG) (at_startFrame hcode _ _) (Nat.le_refl _) hr hse
        rw [hc, rollbackOnError_of_error_eq_none hse, ho, hg, hs, hss, hst]
        exact ⟨rfl, rfl, rfl, rfl⟩

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
  obtain ⟨child', hc, -, hok⟩ := process_mirror_iff hparis caller lt hcode ht hv hpre hk
  rw [hch] at hc
  cases hc
  obtain ⟨-, ho, hs, -⟩ := hok he
  exact ⟨ho, hs⟩

/-- Recording a read of a slot keeps every account. -/
theorem hasAccount_readSlot_iff {state : State.TransactionState} {target other : EthLib.Base.Address}
    {n : U256} : hasAccount (readSlot state other n) target ↔ hasAccount state target := by
  unfold hasAccount readSlot
  rw [(State.TransactionState.recordStorageRead_reads state other target
    (U256.toBeBytes n) (U256.toBeBytes n) default).1]

end UsdtVerify
