import UsdtVerify.Functions.Common
import UsdtVerify.Spec.Write
import EthLib.Execution.Proofs.Evm.Logic.Rules

/-!
# The `onlyOwner` check

Ownable's modifier `onlyOwner` is `require(msg.sender == owner)`. The compiler inlines it at the
start of each owner function. From the `SWAP1` before the `SLOAD` of slot 0, the 87 bytes are the
same at every copy:

`SWAP1 SLOAD SWAP1 PUSH2 0100 EXP SWAP1 DIV PUSH20 mask AND PUSH20 mask AND CALLER PUSH20 mask
AND EQ ISZERO ISZERO PUSH2 (s + 87) JUMPI PUSH1 0 DUP1 REVERT`

with the two words `0, 0` on top of the stack (the slot key 0 and the byte offset 0).

- `CHECKS`: the ten copies (deprecate, addBlackList, unpause, pause, setParams, issue, redeem,
  removeBlackList, transferOwnership, destroyBlackFunds).
- `ownerOk`: when the caller is the owner (the low 160 bits of slot 0), the run goes on at
  `s + 87`, after reading slot 0.
- `ownerRevert`: otherwise it reverts with no output.
-/

namespace UsdtVerify.Owner

open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate}

/-- The owner as the code reads it: the low 160 bits of slot 0. -/
abbrev ownerOf (state : State.TransactionState) (target : EthLib.Base.Address) : U256 :=
  bitwiseAnd ADDR_MASK (storageAt state target 0)

/-- The caller, as the word that the code compares with the owner. -/
abbrev callerWord (message : Message fork) : U256 := bitwiseAnd ADDR_MASK message.caller.toU256

/-- The positions of the ten copies of the check (the `SWAP1` before `SLOAD`). -/
def CHECKS : List Nat := [2650, 3288, 4337, 4940, 5794, 6023, 6526, 7292, 7609, 7824]

/-- Dividing by `256 ^ 0` and masking twice is masking once. -/
theorem owner_expr (w : U256) :
    bitwiseAnd ADDR_MASK (bitwiseAnd ADDR_MASK (div w (exp (0x0100 : U256) (0 : U256)))) =
      bitwiseAnd ADDR_MASK w := by
  have he : exp (0x0100 : U256) (0 : U256) = 1 := by decide +kernel
  have hd : div w 1 = w := by
    apply BitVec.eq_of_toNat_eq
    simp [div]
  rw [he, hd, mask_mask]

/-- The check, from `s` to the `JUMPI`, leaves the test word on the stack. -/
theorem ownerTest (hfork : .berlin ≤ fork) {s : Nat} (hs : s ∈ CHECKS) {rest : List U256}
    (hrest : rest.length ≤ 16) {M : ByteArray} {c0 : Bool}
    (hc0 : coldIn substate message.currentTarget 0 = c0) {gas : Nat}
    (hg : 56 + slotCost c0 ≤ gas) :
    Gas.HoareG fork (At CODE message s (0 :: 0 :: rest) M gas state substate)
      (At CODE message (s + 79)
        (isZero (isZero (equal (callerWord message) (ownerOf state message.currentTarget))) ::
          rest) M (gas - (56 + slotCost c0))
        (readSlot state message.currentTarget 0) (accessSlot substate message.currentTarget 0)) := by
  have hexp : exponentBytes (0 : U256) = 0 := by decide
  simp only [CHECKS, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    step swapR 0
    norm
    step Gas.sloadG hfork (cold := c0) (by code_fact) (by code_fact) hc0 (by gas_ok)
    step swapR 0
    norm
    step pushR 2 (0x0100 : U256)
    step Gas.expLG (Nat.le_trans (by decide) hfork) (by code_fact) (by code_fact) (by gas_ok)
    step swapR 0
    norm
    step binR 0x04 Local.instruction_div
    step pushR 20 ADDR_MASK
    step binR 0x16 Local.instruction_and
    step pushR 20 ADDR_MASK
    step binR 0x16 Local.instruction_and
    step Gas.callerG (by code_fact) (by code_fact) (by gas_ok) (by stk_ok)
    step pushR 20 ADDR_MASK
    step binR 0x16 Local.instruction_and
    step binR 0x14 instruction_eq
    step unR 0x15 instruction_iszero
    step unR 0x15 instruction_iszero
    refine restate (by decide) ?_ rfl (by gas_ok) rfl rfl
    rw [owner_expr]

/-- When the caller is the owner, the check goes on at `s + 87`. -/
theorem ownerOk (hfork : .berlin ≤ fork) {s : Nat} (hs : s ∈ CHECKS) {rest : List U256}
    (hrest : rest.length ≤ 16) {M : ByteArray} {c0 : Bool}
    (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hown : callerWord message = ownerOf state message.currentTarget) {gas : Nat}
    (hg : 69 + slotCost c0 ≤ gas) :
    Gas.HoareG fork (At CODE message s (0 :: 0 :: rest) M gas state substate)
      (At CODE message (s + 87) rest M (gas - (69 + slotCost c0))
        (readSlot state message.currentTarget 0) (accessSlot substate message.currentTarget 0)) := by
  have hc : isZero (isZero (equal (callerWord message) (ownerOf state message.currentTarget))) ≠
      0 := by
    rw [hown]; simp [equal, isZero]
  refine (ownerTest hfork hs hrest hc0 (by gas_ok)).seq ?_
  simp only [CHECKS, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    step pushAnyR 2
    step jumpiR hc
    exact restate (by decide) rfl rfl (by gas_ok) rfl rfl

/-- When the caller is not the owner, the check reverts with no output. -/
theorem ownerRevert (hfork : .berlin ≤ fork) {s : Nat} (hs : s ∈ CHECKS) {rest : List U256}
    (hrest : rest.length ≤ 16) {M : ByteArray} (hM : M.size = 96) {c0 : Bool}
    (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hown : callerWord message ≠ ownerOf state message.currentTarget) {gas : Nat}
    (hg : 75 + slotCost c0 ≤ gas) :
    Gas.SpecG fork (At CODE message s (0 :: 0 :: rest) M gas state substate)
      (Halted true .empty (gas - (75 + slotCost c0)) (readSlot state message.currentTarget 0)
        (accessSlot substate message.currentTarget 0)) := by
  have hz : extendMemory M.size [((0 : U256), (0 : U256))] = ⟨0, 0⟩ := by
    rw [hM]; decide
  have hc : isZero (isZero (equal (callerWord message) (ownerOf state message.currentTarget))) =
      0 := by
    simp [equal, isZero, hown]
  refine Gas.SpecG.seq (ownerTest hfork hs hrest hc0 (by gas_ok)) ?_
  simp only [CHECKS, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    step pushAnyR 2
    step jumpi0R hc
    step pushR 1 (0 : U256)
    step dupR 0
    refine (Gas.revertG (Nat.le_trans (by decide) hfork) (by code_fact) (by code_fact)
      (by rw [hz]; gas_ok)).consequence (fun _ h => h) ?_
    rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
    refine ⟨hr, he, ?_, ?_, hs, hss⟩
    · rw [ho]; simp [memoryReadBytes]
    · rw [hgas, hz]; gas_ok

/-- The starts of the nine owner functions whose check follows `JUMPDEST PUSH1 0 DUP1`. -/
def BODIES : List Nat := [2646, 3284, 4333, 4936, 5790, 6019, 6522, 7288, 7605]

/-- At the start `b` of an owner function, `JUMPDEST PUSH1 0 DUP1` pushes the two words of the
check, for 7 gas. -/
theorem prefix9 {b : Nat} (hb : b ∈ BODIES) {rest : List U256} (hrest : rest.length ≤ 16)
    {M : ByteArray} {gas : Nat} (hg : 7 ≤ gas) :
    Gas.HoareG fork (At CODE message b rest M gas state substate)
      (At CODE message (b + 4) (0 :: 0 :: rest) M (gas - 7) state substate) := by
  simp only [BODIES, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    step jumpdestR
    step pushR 1 (0 : U256)
    step dupR 0
    exact restate (by decide) rfl rfl (by gas_ok) rfl rfl

theorem mem_CHECKS {b : Nat} (hb : b ∈ BODIES) : b + 4 ∈ CHECKS := by
  simp only [BODIES, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- GENERIC: writing a slot after recording its read is writing it. -/
theorem writeSlot_readSlot {st : State.TransactionState} {t : EthLib.Base.Address} (n v : U256)
    (h : hasAccount st t) : writeSlot (readSlot st t n) t n v = writeSlot st t n v := by
  have h1 := setStorage_writeSlot (state := readSlot st t n) (n := n) (v := v)
    (hasAccount_readSlot h)
  have h2 := setStorage_writeSlot (state := st) (n := n) (v := v) h
  rw [show (readSlot st t n).recordStorageRead t (U256.toBeBytes n) =
    readSlot (readSlot st t n) t n from rfl, readSlot_readSlot] at h1
  exact Except.ok.inj (h1.symm.trans h2)

/-- GENERIC: the substate of a write after an access of the slot is the substate of the write. -/
theorem storeSub_accessSlot (ss : Substate) (t : EthLib.Base.Address) (n o c v : U256) :
    storeSub fork (accessSlot ss t n) t n o c v = storeSub fork ss t n o c v := by
  unfold storeSub
  rw [accessSlot_accessSlot]

end UsdtVerify.Owner
