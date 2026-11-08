import UsdtVerify.Usdt.Proofs.Transfer

/-!
# transferFrom(address,address,uint256): the blocks

Proves the Hoare triples of the blocks of transferFrom, and its success path from 8648 with a
fee of 0.

The specifications that compose these blocks are in Usdt/Spec/TransferFrom.lean.

The parts below keep their own headers:

- transferFrom(address,address,uint256): the blocks of the success path
- transferFrom(address,address,uint256): the success path from 8648, with a fee of 0
-/

section

/-!
## transferFrom(address,address,uint256): the blocks of the success path

As the bytecode runs it (selector 0x23b872dd):

- 819: no value; reads `_from` (argument word 0, masked), `_to` (word 1, masked), `_value`
  (word 2); jumps to 3773 with return address 914 (0x0392).
- 3773: `paused` (slot 0, byte 20) must be 0.
- 3801: `isBlackListed[_from]` (base slot 6) must be 0 (low byte). Only `_from` is checked.
- 3890: `deprecated` (slot 10, byte 20); when 0, StandardToken's `transferFrom` at 8619 (4236).
- 8619: the payload check `CALLDATASIZE ≥ 0x64` (three argument words).
- 8648: `_allowance = allowed[_from][msg.sender]` (nested mapping at base slot 5).
- 8776: `fee = mul(_value, basisPointsRate).div(10000)` (slot 3), capped by `maximumFee` at 8816.
- 8834: `if (_allowance < MAX_UINT) allowed[_from][msg.sender] = _allowance.sub(_value)`: the
  allowance is left as it is when it is 2^256 - 1.
- 9022: `sendAmount = _value.sub(fee)`.
- 9041: `balances[_from] = balances[_from].sub(_value)` (base slot 2).
- 9193: `balances[_to] = balances[_to].add(sendAmount)`, read after the write of `_from`.
- 9342: `if (fee > 0)` the owner's credit (not covered: the fee is 0 here).
- 9700: `Transfer(_from, _to, sendAmount)` (LOG3), back to 4247, then STOP at 915.
-/

namespace UsdtVerify.TransferFrom

open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts
open Transfer SafeMath TransferOk

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate}

/-- From 819, a call with no value goes to 3773 with the value, `_to`, `_from` and 914. -/
theorem entry (hv : message.value = 0) {x : U256} {gas : Nat} (hg : 128 ≤ gas) :
    Gas.HoareG fork (At CODE message 819 [x] MEM0 gas state substate)
      (At CODE message 3773 [wordArg message.data 2, addrArg message.data 1,
        addrArg message.data 0, 0x0392, x] MEM0 (gas - 128) state substate) := by
  step jumpdestR
  step Gas.callvalueG (by code_fact) (by code_fact) (by gas_ok) (by stk_ok)
  step unR 0x15 instruction_iszero
  step pushR 2 (0x033e : U256)
  step jumpiR (by simp [hv, isZero])
  step jumpdestR
  step pushR 2 (0x0392 : U256)
  step pushR 1 (0x04 : U256)
  step dupR 0
  step dupR 0
  step Gas.calldataloadG (by code_fact) (by code_fact) (by gas_ok)
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
  step Gas.calldataloadG (by code_fact) (by code_fact) (by gas_ok)
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
  step pushR 2 (0x0ebd : U256)
  step jumpR
  exact (repc (by decide)).seq (Gas.reshapeG rfl rfl (by gas_ok))

/-- At 3773, when byte 20 of slot 0 is 0 (not paused), the code goes on to 3801. -/
theorem notPaused (hfork : .berlin ≤ fork) {rest : List U256} (hrest : rest.length ≤ 16)
    {c0 : Bool} (hnp : byte20 (storageAt state message.currentTarget 0) = 0)
    (hc0 : coldIn substate message.currentTarget 0 = c0) {gas : Nat}
    (hg : 112 + slotCost c0 ≤ gas) {M : ByteArray} :
    Gas.HoareG fork (At CODE message 3773 rest M gas state substate)
      (At CODE message 3801 rest M (gas - (112 + slotCost c0))
        (readSlot state message.currentTarget 0) (accessSlot substate message.currentTarget 0)) := by
  have hexp : exponentBytes (0x14 : U256) = 1 := by decide
  step jumpdestR
  step pushR 1 (0 : U256)
  step pushR 1 (0x14 : U256)
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
  step pushR 1 (0xff : U256)
  step binR 0x16 Local.instruction_and
  step unR 0x15 instruction_iszero
  step unR 0x15 instruction_iszero
  step unR 0x15 instruction_iszero
  step pushR 2 (0x0ed9 : U256)
  step jumpiR (isZero3_flag_ne hnp)
  exact (repc (by decide)).seq (Gas.reshapeG rfl rfl (by gas_ok))

/-- The slot of `isBlackListed[_from]` for the word `f`: mapping base slot 6. -/
abbrev blackFrom (f : U256) : U256 := mapSlot (mkey f) 6

/-- At 3801, when the low byte of `isBlackListed[_from]` is 0, the code goes on to 3890. -/
theorem notBlack (hfork : .berlin ≤ fork) {v t f : U256} {rest : List U256}
    (hrest : rest.length ≤ 16) {cB : Bool}
    (hcB : coldIn substate message.currentTarget (blackFrom f) = cB)
    (hnb : (storageAt state message.currentTarget (blackFrom f)).toNat % 256 = 0) {gas : Nat}
    (hg : 152 + slotCost cB ≤ gas) {M : ByteArray} (hM : M.size = 96) :
    Gas.HoareG fork (At CODE message 3801 (v :: t :: f :: rest) M gas state substate)
      (At CODE message 3890 (v :: t :: f :: rest) (mapMem M (mkey f) 6)
        (gas - (152 + slotCost cB)) (readSlot state message.currentTarget (blackFrom f))
        (accessSlot substate message.currentTarget (blackFrom f))) := by
  have hexp : exponentBytes (0 : U256) = 0 := by decide
  simp only [blackFrom, mkey] at hcB hnb ⊢
  step jumpdestR
  step pushR 1 (0x06 : U256)
  step pushR 1 (0 : U256)
  step dupR 4
  at_pc 3807
  step hashTail (by decide) (by simp; omega) hM (by gas_ok)
  at_pc 3865
  step pushR 1 (0 : U256)
  step swapR 0
  norm
  step Gas.sloadG hfork (cold := cB) (by code_fact) (by code_fact) hcB (by gas_ok)
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
  step unR 0x15 instruction_iszero
  step pushR 2 (0x0f32 : U256)
  step jumpiR (blackTest_ne hnb)
  exact restate (by decide) rfl rfl (by gas_ok) rfl rfl

/-- At 3890, when byte 20 of slot 10 is 0 (not deprecated), the code goes to 4236. -/
theorem notDeprecated (hfork : .berlin ≤ fork) {rest : List U256} (hrest : rest.length ≤ 16)
    {c10 : Bool} (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    (hc10 : coldIn substate message.currentTarget 10 = c10) {gas : Nat}
    (hg : 106 + slotCost c10 ≤ gas) {M : ByteArray} :
    Gas.HoareG fork (At CODE message 3890 rest M gas state substate)
      (At CODE message 4236 rest M (gas - (106 + slotCost c10))
        (readSlot state message.currentTarget 10) (accessSlot substate message.currentTarget 10)) := by
  have hexp : exponentBytes (0x14 : U256) = 1 := by decide
  step jumpdestR
  step pushR 1 (0x0a : U256)
  step pushR 1 (0x14 : U256)
  step swapR 0
  norm
  step Gas.sloadG hfork (cold := c10) (by code_fact) (by code_fact) hc10 (by gas_ok)
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
  step pushR 2 (0x108c : U256)
  step jumpiR (isZero_flag_ne hdep)
  exact (repc (by decide)).seq (Gas.reshapeG rfl rfl (by gas_ok))

/-- At 4236, the code calls StandardToken's `transferFrom` at 8619. -/
theorem toStandard {v t f r x : U256} {gas : Nat} (hg : 24 ≤ gas) {M : ByteArray} :
    Gas.HoareG fork (At CODE message 4236 [v, t, f, r, x] M gas state substate)
      (At CODE message 8619 [v, t, f, 0x1097, v, t, f, r, x] M (gas - 24) state substate) := by
  step jumpdestR
  step pushR 2 (0x1097 : U256)
  step dupR 3
  step dupR 3
  step dupR 3
  step pushR 2 (0x21ab : U256)
  step jumpR
  exact (repc (by decide)).seq (Gas.reshapeG rfl rfl (by gas_ok))

/-- At 8619, call data of at least 100 bytes passes the payload check of three words. -/
theorem payload (hlong : 100 ≤ message.data.size) (hsz : message.data.size < 2 ^ 256)
    {rest : List U256} (hrest : rest.length ≤ 20) {gas : Nat} (hg : 57 ≤ gas) {M : ByteArray} :
    Gas.HoareG fork (At CODE message 8619 rest M gas state substate)
      (At CODE message 8648 (0x60 :: 0 :: 0 :: 0 :: rest) M (gas - 57) state substate) := by
  have hlt : lessThan (BitVec.ofNat 256 message.data.size) (add (0x60 : U256) (0x04 : U256)) =
      0 := by
    have h100 : (add (0x60 : U256) (0x04 : U256)).toNat = 100 := by decide
    simp only [lessThan, h100, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsz]
    rw [ite_eq_right (by omega)]
  step jumpdestR
  step pushR 1 (0 : U256)
  step dupR 0
  step pushR 1 (0 : U256)
  step pushR 1 (0x60 : U256)
  step pushR 1 (0x04 : U256)
  step dupR 1
  step binR 0x01 instruction_add
  step pushR 1 (0 : U256)
  step Gas.calldatasizeG (by code_fact) (by code_fact) (by gas_ok) (by stk_ok)
  step swapR 0
  norm
  step popR
  step binR 0x10 Local.instruction_lt
  step unR 0x15 instruction_iszero
  step unR 0x15 instruction_iszero
  step unR 0x15 instruction_iszero
  step pushR 2 (0x21c8 : U256)
  step jumpiR (by rw [hlt]; decide)
  exact (repc (by decide)).seq (Gas.reshapeG rfl rfl (by gas_ok))

/-- The slot of `allowed[_from][msg.sender]` for the word `f`: the nested mapping at base 5. -/
abbrev allowFrom (message : Message fork) (f : U256) : U256 :=
  mapSlot (mkey message.caller.toU256) (mapSlot (mkey f) 5)

/-- The memory after the lookup of `allowed[_from][msg.sender]`. -/
abbrev allowMem (message : Message fork) (M : ByteArray) (f : U256) : ByteArray :=
  mapMem (mapMem M (mkey f) 5) (mkey message.caller.toU256) (mapSlot (mkey f) 5)

theorem size_allowMem {M : ByteArray} (hM : M.size = 96) (f : U256) :
    (allowMem message M f).size = 96 :=
  size_mapMem (size_mapMem hM _ _) _ _

theorem ptr_allowMem {M : ByteArray} (hM : M.size = 96)
    (hptr : loadWord (memoryReadBytes M 64 32) 0 32 = 0x60) (f : U256) :
    loadWord (memoryReadBytes (allowMem message M f) 64 32) 0 32 = 0x60 :=
  ptr_mapMem (size_mapMem hM _ _) (ptr_mapMem hM hptr _ _) _ _

/-- At 8648, the code reads `_allowance = allowed[_from][msg.sender]`. -/
theorem allowRead (hfork : .berlin ≤ fork) {v t f : U256} {rest : List U256}
    (hrest : rest.length ≤ 16) {cA : Bool}
    (hcA : coldIn substate message.currentTarget (allowFrom message f) = cA) {gas : Nat}
    (hg : 188 + slotCost cA ≤ gas) {M : ByteArray} (hM : M.size = 96) :
    Gas.HoareG fork (At CODE message 8648 (0x60 :: 0 :: 0 :: 0 :: v :: t :: f :: rest) M gas state
        substate)
      (At CODE message 8776 (0x60 :: 0 :: 0 ::
        storageAt state message.currentTarget (allowFrom message f) :: v :: t :: f :: rest)
        (allowMem message M f) (gas - (188 + slotCost cA))
        (readSlot state message.currentTarget (allowFrom message f))
        (accessSlot substate message.currentTarget (allowFrom message f))) := by
  simp only [allowFrom, allowMem, mkey] at hcA ⊢
  step jumpdestR
  step pushR 1 (0x05 : U256)
  step pushR 1 (0 : U256)
  step dupR 8
  at_pc 8654
  step hashTail (by decide) (by simp; omega) hM (by gas_ok)
  at_pc 8712
  step pushR 1 (0 : U256)
  step Gas.callerG (by code_fact) (by code_fact) (by gas_ok) (by stk_ok)
  at_pc 8715
  step hashTail (by decide) (by simp; omega) (size_mapMem hM _ _) (by gas_ok)
  at_pc 8773
  step Gas.sloadG hfork (cold := cA) (by code_fact) (by code_fact) hcA (by gas_ok)
  step swapR 3
  norm
  step popR
  exact restate (by decide) rfl rfl (by gas_ok) rfl rfl

/-- At 8776, the code reads `basisPointsRate` (slot 3) and calls `mul(_value, rate)`. -/
theorem feeCall (hfork : .berlin ≤ fork) {A v t f : U256} {rest : List U256}
    (hrest : rest.length ≤ 16) {c3 : Bool} (hc3 : coldIn substate message.currentTarget 3 = c3)
    {gas : Nat} (hg : 41 + slotCost c3 ≤ gas) {M : ByteArray} :
    Gas.HoareG fork (At CODE message 8776 (0x60 :: 0 :: 0 :: A :: v :: t :: f :: rest) M gas state
        substate)
      (At CODE message 10755 (storageAt state message.currentTarget 3 :: v :: 0x2262 :: 0x2710 ::
        0x2270 :: 0x60 :: 0 :: 0 :: A :: v :: t :: f :: rest) M (gas - (41 + slotCost c3))
        (readSlot state message.currentTarget 3) (accessSlot substate message.currentTarget 3)) := by
  step pushR 2 (0x2270 : U256)
  step pushR 2 (0x2710 : U256)
  step pushR 2 (0x2262 : U256)
  step pushR 1 (0x03 : U256)
  step Gas.sloadG hfork (cold := c3) (by code_fact) (by code_fact) hc3 (by gas_ok)
  step dupR 8
  step pushR 2 (0x2a03 : U256)
  step swapR 0
  norm
  step swapR 1
  norm
  step swapR 0
  norm
  step pushR 4 (0xffffffff : U256)
  step binR 0x16 Local.instruction_and
  step jumpR
  exact (repc (by decide)).seq (Gas.reshapeG rfl rfl (by gas_ok))

/-- At 8802, back from `mul`, the code calls `div(product, 10000)`. -/
theorem divCall {m r : U256} {rest : List U256} (hrest : rest.length ≤ 20) {gas : Nat}
    (hg : 27 ≤ gas) {M : ByteArray} :
    Gas.HoareG fork (At CODE message 8802 (m :: 0x2710 :: r :: rest) M gas state substate)
      (At CODE message 10949 (0x2710 :: m :: r :: rest) M (gas - 27) state substate) := by
  step jumpdestR
  step pushR 2 (0x2ac5 : U256)
  step swapR 0
  norm
  step swapR 1
  norm
  step swapR 0
  norm
  step pushR 4 (0xffffffff : U256)
  step binR 0x16 Local.instruction_and
  step jumpR
  exact (repc (by decide)).seq (Gas.reshapeG rfl rfl (by gas_ok))

/-- At 8816, with the raw fee `f0`, the code caps it by `maximumFee` (slot 4). -/
theorem capBlock (hfork : .berlin ≤ fork) {f0 A v t f : U256} {rest : List U256}
    (hrest : rest.length ≤ 16) {c4 : Bool} (hc4 : coldIn substate message.currentTarget 4 = c4)
    {gas : Nat}
    (hg : 31 + slotCost c4 + capCost f0 (storageAt state message.currentTarget 4) ≤ gas)
    {M : ByteArray} :
    Gas.HoareG fork (At CODE message 8816 (f0 :: 0x60 :: 0 :: 0 :: A :: v :: t :: f :: rest) M gas
        state substate)
      (At CODE message 8834
        (0x60 :: 0 :: capped f0 (storageAt state message.currentTarget 4) :: A :: v :: t :: f ::
          rest) M
        (gas - (31 + slotCost c4 + capCost f0 (storageAt state message.currentTarget 4)))
        (readSlot state message.currentTarget 4) (accessSlot substate message.currentTarget 4)) := by
  step jumpdestR
  step swapR 2
  norm
  step popR
  step pushR 1 (0x04 : U256)
  step Gas.sloadG hfork (cold := c4) (by code_fact) (by code_fact) hc4 (by gas_ok)
  step dupR 3
  step binR 0x11 Local.instruction_gt
  step unR 0x15 instruction_iszero
  step pushR 2 (0x2282 : U256)
  by_cases hcap : f0.toNat > (storageAt state message.currentTarget 4).toNat
  · simp only [capCost, capped, hcap, ite_true] at hg ⊢
    step jumpi0R (by simp only [greaterThan]; rw [ite_eq_left hcap]; decide)
    step pushR 1 (0x04 : U256)
    step Gas.sloadG hfork (cold := false) (by code_fact) (by code_fact)
      (coldIn_accessSlot_self _ _ _) (by gas_ok)
    step swapR 2
    norm
    step popR
    exact restate (by decide) rfl rfl (by gas_ok) (readSlot_readSlot _ _ _)
      (accessSlot_accessSlot _ _ _)
  · simp only [capCost, capped, hcap, ite_false] at hg ⊢
    step jumpiR (by simp only [greaterThan]; rw [ite_eq_right hcap]; decide)
    exact (repc (by decide)).seq (Gas.reshapeG rfl rfl (by gas_ok))

/-- The word `MAX_UINT = 2^256 - 1`. -/
abbrev MAX_UINT : U256 := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff

/-- The state after the allowance step: unchanged at `MAX_UINT`, else the slot `n` set to
`A - v`. -/
def allowState (state : State.TransactionState) (target : EthLib.Base.Address) (n A v : U256) :
    State.TransactionState :=
  if A = MAX_UINT then state else writeSlot state target n (sub A v)

/-- The substate after the allowance step. -/
def allowSub (fork : Fork) (substate : Substate) (target : EthLib.Base.Address)
    (n orig A v : U256) : Substate :=
  if A = MAX_UINT then substate else storeSub fork substate target n orig A (sub A v)

/-- The gas of the allowance step: 26 at `MAX_UINT`, else 320 and the price of the (warm) write. -/
def allowCost (fork : Fork) (orig A v : U256) : Nat :=
  if A = MAX_UINT then 26 else 320 + Gas.writeCost fork orig A (sub A v) false

/-- The memory after the allowance step. -/
def allowMem2 (message : Message fork) (M : ByteArray) (A f : U256) : ByteArray :=
  if A = MAX_UINT then M else allowMem message M f

theorem size_allowMem2 {M : ByteArray} (hM : M.size = 96) (A f : U256) :
    (allowMem2 message M A f).size = 96 := by
  unfold allowMem2; split
  · exact hM
  · exact size_allowMem hM f

theorem ptr_allowMem2 {M : ByteArray} (hM : M.size = 96)
    (hptr : loadWord (memoryReadBytes M 64 32) 0 32 = 0x60) (A f : U256) :
    loadWord (memoryReadBytes (allowMem2 message M A f) 64 32) 0 32 = 0x60 := by
  unfold allowMem2; split
  · exact hptr
  · exact ptr_allowMem hM hptr f

theorem hasAccount_allowState {state : State.TransactionState} {target : EthLib.Base.Address}
    {n A v : U256} (h : hasAccount state target) :
    hasAccount (allowState state target n A v) target := by
  unfold allowState; split
  · exact h
  · exact hasAccount_writeSlot h

theorem originalAt_allowState {state : State.TransactionState} {target other : EthLib.Base.Address}
    {n m A v : U256} (h : hasAccount state target) :
    originalAt (allowState state target n A v) other m = originalAt state other m := by
  unfold allowState; split
  · rfl
  · exact originalAt_writeSlot h

-- The allowance step when `A ≠ MAX_UINT`, from the `JUMPDEST` at 8834 to the `SSTORE` of the
-- allowance.
set_option hygiene false in
macro "allow_pre" : tactic => `(tactic| (
  step jumpdestR
  step pushR 32 MAX_UINT
  step dupR 4
  step binR 0x10 Local.instruction_lt
  step unR 0x15 instruction_iszero
  step pushR 2 (0x233e : U256)
  step jumpi0R (by simp [lessThan, isZero]; omega)
  step pushR 2 (0x22bd : U256)
  step dupR 5
  step dupR 5
  step pushR 2 (0x2ae0 : U256)
  step swapR 0
  norm
  step swapR 1
  norm
  step swapR 0
  norm
  step pushR 4 (0xffffffff : U256)
  step binR 0x16 Local.instruction_and
  step jumpR
  step subBlock (by simp; omega) (by valid_dest) hle (by gas_ok)
  at_pc 8893
  step jumpdestR
  step pushR 1 (0x05 : U256)
  step pushR 1 (0 : U256)
  step dupR 9
  at_pc 8899
  step hashTail (by decide) (by simp; omega) hM (by gas_ok)
  at_pc 8957
  step pushR 1 (0 : U256)
  step Gas.callerG (by code_fact) (by code_fact) (by gas_ok) (by stk_ok)
  at_pc 8960
  step hashTail (by decide) (by simp; omega) (size_mapMem hM _ _) (by gas_ok)
  at_pc 9018
  step dupR 1
  step swapR 0
  norm))

/-- At 8834, the allowance step: with `_allowance = A`, either `A = MAX_UINT` (nothing is
written) or `v ≤ A` and `allowed[_from][msg.sender] := A - v`. The slot was read at 8773 and is
warm. The frame must be able to write (`hgood`) only when `A ≠ MAX_UINT`. -/
theorem allowStep (hfork : .berlin ≤ fork)
    {fee A v t f : U256} {rest : List U256} (hrest : rest.length ≤ 8)
    (hA : storageAt state message.currentTarget (allowFrom message f) = A)
    (hok : A = MAX_UINT ∨ v.toNat ≤ A.toNat)
    (hgood : A ≠ MAX_UINT → message.isStatic = false ∧ hasAccount state message.currentTarget)
    (hw : coldIn substate message.currentTarget (allowFrom message f) = false) {gas : Nat}
    (hg : allowCost fork (originalAt state message.currentTarget (allowFrom message f)) A v +
      2300 ≤ gas) {M : ByteArray} (hM : M.size = 96) :
    Gas.HoareG fork (At CODE message 8834 (0x60 :: 0 :: fee :: A :: v :: t :: f :: rest) M gas state
        substate)
      (At CODE message 9022 (0x60 :: 0 :: fee :: A :: v :: t :: f :: rest)
        (allowMem2 message M A f)
        (gas - allowCost fork (originalAt state message.currentTarget (allowFrom message f)) A v)
        (allowState state message.currentTarget (allowFrom message f) A v)
        (allowSub fork substate message.currentTarget (allowFrom message f)
          (originalAt state message.currentTarget (allowFrom message f)) A v)) := by
  by_cases hmax : A = MAX_UINT
  · simp only [allowCost, allowState, allowSub, allowMem2, hmax, ite_true] at hg ⊢
    subst hmax
    step jumpdestR
    step pushR 32 MAX_UINT
    step dupR 4
    step binR 0x10 Local.instruction_lt
    step unR 0x15 instruction_iszero
    step pushR 2 (0x233e : U256)
    step jumpiR (by decide)
    exact (repc (by decide)).seq (Gas.reshapeG rfl rfl (by gas_ok))
  · simp only [allowCost, allowState, allowSub, allowMem2, hmax, ite_false] at hg ⊢
    obtain ⟨hstatic, hacc⟩ := hgood hmax
    have hle : v.toNat ≤ A.toNat := hok.resolve_left hmax
    have hlt : A.toNat < 2 ^ 256 - 1 := by
      have h1 := A.isLt
      have h2 : A.toNat ≠ MAX_UINT.toNat := fun h => hmax (BitVec.eq_of_toNat_eq h)
      have h3 : MAX_UINT.toNat = 2 ^ 256 - 1 := by decide
      omega
    clear hok hmax
    subst hA
    simp only [allowFrom, allowMem, mkey] at hw hg hle hlt ⊢
    allow_pre
    step Gas.sstoreWG hfork (by code_fact) (by code_fact) hstatic hacc hw (by gas_ok) (by gas_ok)
    step popR
    exact restate (by decide) rfl rfl (by gas_ok) rfl rfl

/-- At 8834, with `_allowance = A ≠ MAX_UINT` and `v ≤ A`, in a static frame or with no account
for `C`: the run reaches the `SSTORE` of the allowance, which is `Stuck`. -/
theorem allowStepBad {fee A v t f : U256} {rest : List U256} (hrest : rest.length ≤ 8)
    (hbad : message.isStatic = true ∨ ¬hasAccount state message.currentTarget)
    (hmax : A ≠ MAX_UINT) (hle : v.toNat ≤ A.toNat) {gas : Nat} (hg : 1000 ≤ gas) {M : ByteArray}
    (hM : M.size = 96) :
    Gas.HoareG fork (At CODE message 8834 (0x60 :: 0 :: fee :: A :: v :: t :: f :: rest) M gas state
        substate) Gas.Stuck := by
  have hlt : A.toNat < 2 ^ 256 - 1 := by
    have h1 := A.isLt
    have h2 : A.toNat ≠ MAX_UINT.toNat := fun h => hmax (BitVec.eq_of_toNat_eq h)
    have h3 : MAX_UINT.toNat = 2 ^ 256 - 1 := by decide
    omega
  allow_pre
  exact Gas.sstoreStuckW (by code_fact) (by code_fact) hbad

/-- At 9022, the code calls `sub(_value, fee)`. -/
theorem sendCall {fee A v t f : U256} {rest : List U256} (hrest : rest.length ≤ 8) {gas : Nat}
    (hg : 36 ≤ gas) {M : ByteArray} :
    Gas.HoareG fork (At CODE message 9022 (0x60 :: 0 :: fee :: A :: v :: t :: f :: rest) M gas state
        substate)
      (At CODE message 10976 (fee :: v :: 0x2351 :: 0x60 :: 0 :: fee :: A :: v :: t :: f :: rest)
        M (gas - 36) state substate) := by
  step jumpdestR
  step pushR 2 (0x2351 : U256)
  step dupR 3
  step dupR 6
  step pushR 2 (0x2ae0 : U256)
  step swapR 0
  norm
  step swapR 1
  norm
  step swapR 0
  norm
  step pushR 4 (0xffffffff : U256)
  step binR 0x16 Local.instruction_and
  step jumpR
  exact (repc (by decide)).seq (Gas.reshapeG rfl rfl (by gas_ok))

/-- At 9041, the code keeps `sendAmount`, reads `balances[_from]` and calls
`sub(balance, _value)`. -/
theorem debitCall (hfork : .berlin ≤ fork) {send fee A v t f : U256} {rest : List U256}
    (hrest : rest.length ≤ 8) {cF : Bool}
    (hcF : coldIn substate message.currentTarget (recipientSlot f) = cF) {gas : Nat}
    (hg : 131 + slotCost cF ≤ gas) {M : ByteArray} (hM : M.size = 96) :
    Gas.HoareG fork (At CODE message 9041 (send :: 0x60 :: 0 :: fee :: A :: v :: t :: f :: rest) M gas
        state substate)
      (At CODE message 10976 (v :: storageAt state message.currentTarget (recipientSlot f) ::
        0x23a5 :: 0x60 :: send :: fee :: A :: v :: t :: f :: rest) (mapMem M (mkey f) 2)
        (gas - (131 + slotCost cF)) (readSlot state message.currentTarget (recipientSlot f))
        (accessSlot substate message.currentTarget (recipientSlot f))) := by
  simp only [recipientSlot, mkey] at hcF ⊢
  step jumpdestR
  step swapR 1
  norm
  step popR
  step pushR 2 (0x23a5 : U256)
  step dupR 5
  step pushR 1 (0x02 : U256)
  step pushR 1 (0 : U256)
  step dupR 10
  at_pc 9053
  step hashTail (by decide) (by simp; omega) hM (by gas_ok)
  at_pc 9111
  step Gas.sloadG hfork (cold := cF) (by code_fact) (by code_fact) hcF (by gas_ok)
  step pushR 2 (0x2ae0 : U256)
  step swapR 0
  norm
  step swapR 1
  norm
  step swapR 0
  norm
  step pushR 4 (0xffffffff : U256)
  step binR 0x16 Local.instruction_and
  step jumpR
  exact restate (by decide) rfl rfl (by gas_ok) rfl rfl

-- At 9125, from the `JUMPDEST` to the `SSTORE` of `balances[_from]`.
set_option hygiene false in
macro "debitF_pre" : tactic => `(tactic| (
  step jumpdestR
  step pushR 1 (0x02 : U256)
  step pushR 1 (0 : U256)
  step dupR 9
  at_pc 9131
  step hashTail (by decide) (by simp; omega) hM (by gas_ok)
  at_pc 9189
  step dupR 1
  step swapR 0
  norm))

/-- At 9125, the code writes the new balance of `_from`. -/
theorem debitStore (hfork : .berlin ≤ fork)
    {nb send fee A v t f : U256} {rest : List U256} (hrest : rest.length ≤ 8)
    (hstatic : message.isStatic = false) (hacc : hasAccount state message.currentTarget)
    {cF : Bool} (hcF : coldIn substate message.currentTarget (recipientSlot f) = cF) {gas : Nat}
    (hg : 102 + Gas.writeCost fork (originalAt state message.currentTarget (recipientSlot f))
      (storageAt state message.currentTarget (recipientSlot f)) nb cF + 2300 ≤ gas)
    {M : ByteArray} (hM : M.size = 96) :
    Gas.HoareG fork (At CODE message 9125 (nb :: 0x60 :: send :: fee :: A :: v :: t :: f :: rest) M
        gas state substate)
      (At CODE message 9193 (0x60 :: send :: fee :: A :: v :: t :: f :: rest)
        (mapMem M (mkey f) 2)
        (gas - (102 + Gas.writeCost fork (originalAt state message.currentTarget (recipientSlot f))
          (storageAt state message.currentTarget (recipientSlot f)) nb cF))
        (writeSlot state message.currentTarget (recipientSlot f) nb)
        (storeSub fork substate message.currentTarget (recipientSlot f)
          (originalAt state message.currentTarget (recipientSlot f))
          (storageAt state message.currentTarget (recipientSlot f)) nb)) := by
  simp only [recipientSlot, mkey] at hcF hg ⊢
  debitF_pre
  step Gas.sstoreWG hfork (by code_fact) (by code_fact) hstatic hacc hcF (by gas_ok) (by gas_ok)
  step popR
  exact restate (by decide) rfl rfl (by gas_ok) rfl rfl

/-- At 9125, in a static frame or with no account for `C`: the run reaches the `SSTORE` of
`balances[_from]`, which is `Stuck`. -/
theorem debitStoreFBad {nb send fee A v t f : U256} {rest : List U256} (hrest : rest.length ≤ 8)
    (hbad : message.isStatic = true ∨ ¬hasAccount state message.currentTarget) {gas : Nat}
    (hg : 102 ≤ gas) {M : ByteArray} (hM : M.size = 96) :
    Gas.HoareG fork (At CODE message 9125 (nb :: 0x60 :: send :: fee :: A :: v :: t :: f :: rest) M
        gas state substate) Gas.Stuck := by
  debitF_pre
  exact Gas.sstoreStuckW (by code_fact) (by code_fact) hbad

/-- At 9193, the code reads `balances[_to]` and calls `add(balance, sendAmount)`. -/
theorem creditCall (hfork : .berlin ≤ fork) {send fee A v t f : U256} {rest : List U256}
    (hrest : rest.length ≤ 8) {cT : Bool}
    (hcT : coldIn substate message.currentTarget (recipientSlot t) = cT) {gas : Nat}
    (hg : 125 + slotCost cT ≤ gas) {M : ByteArray} (hM : M.size = 96) :
    Gas.HoareG fork (At CODE message 9193 (0x60 :: send :: fee :: A :: v :: t :: f :: rest) M gas
        state substate)
      (At CODE message 11001 (send :: storageAt state message.currentTarget (recipientSlot t) ::
        0x243a :: 0x60 :: send :: fee :: A :: v :: t :: f :: rest) (mapMem M (mkey t) 2)
        (gas - (125 + slotCost cT)) (readSlot state message.currentTarget (recipientSlot t))
        (accessSlot substate message.currentTarget (recipientSlot t))) := by
  simp only [recipientSlot, mkey] at hcT ⊢
  step pushR 2 (0x243a : U256)
  step dupR 2
  step pushR 1 (0x02 : U256)
  step pushR 1 (0 : U256)
  step dupR 9
  at_pc 9202
  step hashTail (by decide) (by simp; omega) hM (by gas_ok)
  at_pc 9260
  step Gas.sloadG hfork (cold := cT) (by code_fact) (by code_fact) hcT (by gas_ok)
  step pushR 2 (0x2af9 : U256)
  step swapR 0
  norm
  step swapR 1
  norm
  step swapR 0
  norm
  step pushR 4 (0xffffffff : U256)
  step binR 0x16 Local.instruction_and
  step jumpR
  exact restate (by decide) rfl rfl (by gas_ok) rfl rfl

/-- At 9274, the code writes the new balance of `_to`; with a fee of 0 it skips the owner's
credit and goes to the log at 9700. -/
theorem creditStore (hfork : .berlin ≤ fork)
    {nt send A v t f : U256} {rest : List U256} (hrest : rest.length ≤ 8)
    (hstatic : message.isStatic = false) (hacc : hasAccount state message.currentTarget)
    {cT : Bool} (hcT : coldIn substate message.currentTarget (recipientSlot t) = cT) {gas : Nat}
    (hstip : 2401 ≤ gas)
    (hg : 127 + Gas.writeCost fork (originalAt state message.currentTarget (recipientSlot t))
      (storageAt state message.currentTarget (recipientSlot t)) nt cT ≤ gas)
    {M : ByteArray} (hM : M.size = 96) :
    Gas.HoareG fork (At CODE message 9274 (nt :: 0x60 :: send :: 0 :: A :: v :: t :: f :: rest) M
        gas state substate)
      (At CODE message 9700 (0x60 :: send :: 0 :: A :: v :: t :: f :: rest)
        (mapMem M (mkey t) 2)
        (gas - (127 + Gas.writeCost fork (originalAt state message.currentTarget (recipientSlot t))
          (storageAt state message.currentTarget (recipientSlot t)) nt cT))
        (writeSlot state message.currentTarget (recipientSlot t) nt)
        (storeSub fork substate message.currentTarget (recipientSlot t)
          (originalAt state message.currentTarget (recipientSlot t))
          (storageAt state message.currentTarget (recipientSlot t)) nt)) := by
  simp only [recipientSlot, mkey] at hcT hg ⊢
  step jumpdestR
  step pushR 1 (0x02 : U256)
  step pushR 1 (0 : U256)
  step dupR 8
  at_pc 9280
  step hashTail (by decide) (by simp; omega) hM (by gas_ok)
  at_pc 9338
  step dupR 1
  step swapR 0
  norm
  step Gas.sstoreWG hfork (by code_fact) (by code_fact) hstatic hacc hcT (by gas_ok) (by gas_ok)
  step popR
  step pushR 1 (0 : U256)
  step dupR 3
  step binR 0x11 Local.instruction_gt
  step unR 0x15 instruction_iszero
  step pushR 2 (0x25e4 : U256)
  step jumpiR (by decide)
  exact restate (by decide) rfl rfl (by gas_ok) rfl rfl

/-- At 9274 (fee of 0), when the `SSTORE` of `balances[_to]` cannot complete (`NoWrite`): the run
reaches it, and it is `Stuck`. -/
theorem creditStoreBadF {nt send A v t f : U256} {rest : List U256} (hrest : rest.length ≤ 8)
    {gas : Nat} (hbad : Gas.NoWrite message state (gas - 100)) (hg : 100 ≤ gas) {M : ByteArray}
    (hM : M.size = 96) :
    Gas.HoareG fork (At CODE message 9274 (nt :: 0x60 :: send :: 0 :: A :: v :: t :: f :: rest) M
        gas state substate) Gas.Stuck := by
  step jumpdestR
  step pushR 1 (0x02 : U256)
  step pushR 1 (0 : U256)
  step dupR 8
  at_pc 9280
  step hashTail (by decide) (by simp; omega) hM (by gas_ok)
  at_pc 9338
  step dupR 1
  step swapR 0
  norm
  exact Gas.sstoreNoWrite (by code_fact) (by code_fact) (hbad.le (by gas_ok))

/-- At 9700, the code logs `Transfer(_from, _to, sendAmount)` and returns to 4247. -/
theorem logBlock {send fee A v t f : U256} {rest : List U256} (hrest : rest.length ≤ 900)
    (hstatic : message.isStatic = false) {gas : Nat} (hg : 1855 ≤ gas) {M : ByteArray}
    (hM : M.size = 96) (hptr : loadWord (memoryReadBytes M 64 32) 0 32 = 0x60) :
    Gas.HoareG fork (At CODE message 9700 (0x60 :: send :: fee :: A :: v :: t :: f :: 0x1097 :: rest)
        M gas state substate)
      (At CODE message 4247 rest (M ++ wordBytes send) (gas - 1855) state
        { substate with logs := substate.logs.push (transferLog message.currentTarget
          (bitwiseAnd ADDR_MASK f) (bitwiseAnd ADDR_MASK t) send) }) := by
  have hext0 : extendMemory M.size [((0x40 : U256), (32 : U256))] = ⟨0, 0⟩ := by
    rw [hM]; decide
  have hext1 : extendMemory M.size [((0x60 : U256), (32 : U256))] = ⟨3, 32⟩ := by
    rw [hM]; decide
  have hsz : (M ++ wordBytes send).size = 128 := by
    rw [ByteArray.size_append, hM, size_wordBytes]
  have hext2 : extendMemory (M ++ wordBytes send).size [((0x40 : U256), (32 : U256))] =
      ⟨0, 0⟩ := by rw [hsz]; decide
  have hext3 : extendMemory (M ++ wordBytes send).size [((0x60 : U256), (0x20 : U256))] =
      ⟨0, 0⟩ := by rw [hsz]; decide
  have hmem1 : memoryWrite (memoryExtend M 32) (0x60 : U256).toNat (wordBytes send) =
      M ++ wordBytes send := by
    have h := memoryWrite_extend_end (memory := M) (value := wordBytes send)
    rwa [size_wordBytes, hM] at h
  have hread2 : memoryReadBytes (M ++ wordBytes send) 64 32 = memoryReadBytes M 64 32 := by
    simp only [memoryReadBytes, ByteArray.extract_append, hM]
    simp
  have hlog : logCost (3 : Fin 5).val (0x20 : U256) = 1756 := by decide
  step jumpdestR
  step dupR 5
  step pushR 20 ADDR_MASK
  step binR 0x16 Local.instruction_and
  step dupR 7
  step pushR 20 ADDR_MASK
  step binR 0x16 Local.instruction_and
  step pushR 32 TransferOk.TRANSFER_TOPIC
  step dupR 4
  step pushR 1 (0x40 : U256)
  step Gas.mloadG (by code_fact) (by code_fact) (by rw [hext0]; gas_ok)
  step Gas.reshapeG (s' := 0x60 :: send :: TransferOk.TRANSFER_TOPIC :: bitwiseAnd ADDR_MASK f ::
      bitwiseAnd ADDR_MASK t :: 0x60 :: send :: fee :: A :: v :: t :: f :: 0x1097 :: rest) (m' := M)
    (by rw [hext0, memoryExtend_zero]; exact congrArg (· :: _) hptr)
    (by rw [hext0, memoryExtend_zero]) (by rw [hext0])
  step dupR 0
  step dupR 2
  step dupR 1
  step Gas.mstoreG (by code_fact) (by code_fact) (by rw [hext1]; gas_ok)
  step Gas.reshapeG (m' := M ++ wordBytes send) rfl (by rw [hext1]; exact hmem1) (by rw [hext1])
  step pushR 1 (0x20 : U256)
  step binR 0x01 instruction_add
  step swapR 1
  norm
  step popR
  step popR
  step pushR 1 (0x40 : U256)
  step Gas.mloadG (by code_fact) (by code_fact) (by rw [hext2]; gas_ok)
  step Gas.reshapeG (s' := 0x60 :: 0x80 :: TransferOk.TRANSFER_TOPIC :: bitwiseAnd ADDR_MASK f ::
      bitwiseAnd ADDR_MASK t :: 0x60 :: send :: fee :: A :: v :: t :: f :: 0x1097 :: rest)
    (m' := M ++ wordBytes send)
    (by rw [hext2, memoryExtend_zero, show (0x40 : U256).toNat = 64 from rfl, hread2, hptr]; rfl)
    (by rw [hext2, memoryExtend_zero]) (by rw [hext2])
  step dupR 0
  step swapR 1
  norm
  step binR 0x03 Local.instruction_sub
  step swapR 0
  norm
  step Gas.reshapeG (s' := 0x60 :: 0x20 :: ([TransferOk.TRANSFER_TOPIC, bitwiseAnd ADDR_MASK f,
      bitwiseAnd ADDR_MASK t] ++ (0x60 :: send :: fee :: A :: v :: t :: f :: 0x1097 :: rest)))
    rfl rfl rfl
  step Gas.logG (n := 3) (byte := 0xa3) rfl (by code_fact) (by code_fact) rfl hstatic
    (by rw [hlog, hext3]; gas_ok)
  step Gas.reshapeG rfl (by rw [hext3, memoryExtend_zero]) (by rw [hlog, hext3])
  step popR
  step popR
  step popR
  step popR
  step popR
  step popR
  step popR
  step jumpR
  refine restate (by decide) rfl rfl (by gas_ok) rfl ?_
  rw [hext3, memoryExtend_zero, show (0x60 : U256).toNat = 96 from rfl,
    show (0x20 : U256).toNat = 32 from rfl, read_after hM _ (size_wordBytes send)]

/-- At 4247, the code returns to 914, where it stops. -/
theorem endBlock {v t f sel : U256} {gas : Nat} (hg : 17 ≤ gas) {M : ByteArray} :
    Gas.SpecG fork (At CODE message 4247 [v, t, f, 0x0392, sel] M gas state substate)
      (Halted false .empty (gas - 17) state substate) := by
  step jumpdestR
  step jumpdestR
  step popR
  step popR
  step popR
  step jumpR
  step repc (pc' := 914) (by decide)
  step jumpdestR
  refine (Gas.stopG (by code_fact) (by code_fact)).consequence (fun _ h => h) ?_
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  exact ⟨hr, he, ho, by rw [hgas]; gas_ok, hs, hss⟩

end UsdtVerify.TransferFrom

end

section

/-!
## transferFrom(address,address,uint256): the success path from 8648, with a fee of 0

`body` composes the blocks of `TransferFrom` from 8648 (after the payload check) to the STOP at
915. The states and substates along the path are named below. Each word is read in the state
where the code reads it: `balances[_from]` after the allowance step, `balances[_to]` after the
write of `_from`.
-/

namespace UsdtVerify.TransferFrom

open EthLib.Base (Fork U256 Address)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts
open Transfer SafeMath TransferOk

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate}

/-- A slot accessed stays accessed when another slot is accessed. -/
theorem coldIn_accessSlot_false {ss : Substate} {target : Address} {n m : U256}
    (h : coldIn ss target m = false) : coldIn (accessSlot ss target n) target m = false := by
  simp only [coldIn, decide_eq_false_iff_not, Decidable.not_not] at h ⊢
  simp only [Std.ExtTreeMap.getD_insert_self, Std.ExtTreeSet.mem_insert]
  exact Or.inr h

theorem slotCost_ge (c : Bool) : 100 ≤ slotCost c := by cases c <;> decide

/-- `_allowance`: the word of `allowed[_from][msg.sender]`. -/
abbrev allowOf (state : State.TransactionState) (message : Message fork) (f : U256) : U256 :=
  storageAt state message.currentTarget (allowFrom message f)

/-- The state after the reads of the allowance, slot 3 and slot 4. -/
abbrev readsF (state : State.TransactionState) (message : Message fork) (f : U256) :
    State.TransactionState :=
  readSlot (readSlot (readSlot state message.currentTarget (allowFrom message f))
    message.currentTarget 3) message.currentTarget 4

/-- The substate after the accesses of the allowance, slot 3 and slot 4. -/
abbrev accessF (substate : Substate) (message : Message fork) (f : U256) : Substate :=
  accessSlot (accessSlot (accessSlot substate message.currentTarget (allowFrom message f))
    message.currentTarget 3) message.currentTarget 4

/-- The state after the allowance step. -/
abbrev allowedF (state : State.TransactionState) (message : Message fork) (v f : U256) :
    State.TransactionState :=
  allowState (readsF state message f) message.currentTarget (allowFrom message f)
    (allowOf state message f) v

/-- The substate after the allowance step. -/
abbrev allowedSubF (fork : Fork) (substate : Substate) (state : State.TransactionState)
    (message : Message fork) (v f : U256) : Substate :=
  allowSub fork (accessF substate message f) message.currentTarget (allowFrom message f)
    (originalAt state message.currentTarget (allowFrom message f)) (allowOf state message f) v

/-- `balances[_from]`, read after the allowance step. -/
abbrev balFrom (state : State.TransactionState) (message : Message fork) (v f : U256) : U256 :=
  storageAt (allowedF state message v f) message.currentTarget (recipientSlot f)

/-- The state after the write of `balances[_from] = balFrom - v`. -/
abbrev debitedF (state : State.TransactionState) (message : Message fork) (v f : U256) :
    State.TransactionState :=
  writeSlot (readSlot (allowedF state message v f) message.currentTarget (recipientSlot f))
    message.currentTarget (recipientSlot f) (sub (balFrom state message v f) v)

/-- The substate after that write. -/
abbrev debitedSubF (fork : Fork) (substate : Substate) (state : State.TransactionState)
    (message : Message fork) (v f : U256) : Substate :=
  storeSub fork (accessSlot (allowedSubF fork substate state message v f) message.currentTarget
      (recipientSlot f)) message.currentTarget (recipientSlot f)
    (originalAt state message.currentTarget (recipientSlot f)) (balFrom state message v f)
    (sub (balFrom state message v f) v)

/-- `balances[_to]`, read after the write of `_from`. -/
abbrev balTo (state : State.TransactionState) (message : Message fork) (v t f : U256) : U256 :=
  storageAt (debitedF state message v f) message.currentTarget (recipientSlot t)

/-- The state at the end: `balances[_to] = balTo + v`. -/
abbrev creditedF (state : State.TransactionState) (message : Message fork) (v t f : U256) :
    State.TransactionState :=
  writeSlot (readSlot (debitedF state message v f) message.currentTarget (recipientSlot t))
    message.currentTarget (recipientSlot t) (add (balTo state message v t f) v)

/-- The substate after the write of `_to`. -/
abbrev creditedSubF (fork : Fork) (substate : Substate) (state : State.TransactionState)
    (message : Message fork) (v t f : U256) : Substate :=
  storeSub fork (accessSlot (debitedSubF fork substate state message v f) message.currentTarget
      (recipientSlot t)) message.currentTarget (recipientSlot t)
    (originalAt state message.currentTarget (recipientSlot t)) (balTo state message v t f)
    (add (balTo state message v t f) v)

/-- The substate at the end: the log `Transfer(_from, _to, v)` appended. -/
abbrev loggedSubF (fork : Fork) (substate : Substate) (state : State.TransactionState)
    (message : Message fork) (v t f : U256) : Substate :=
  { creditedSubF fork substate state message v t f with
    logs := (creditedSubF fork substate state message v t f).logs.push
      (transferLog message.currentTarget (bitwiseAnd ADDR_MASK f) (bitwiseAnd ADDR_MASK t) v) }

/-- The price of the allowance step. -/
abbrev allowCostF (fork : Fork) (state : State.TransactionState) (message : Message fork)
    (v f : U256) : Nat :=
  allowCost fork (originalAt state message.currentTarget (allowFrom message f))
    (allowOf state message f) v

/-- The price of the write of `_from` (warm). -/
abbrev debitCostF (fork : Fork) (state : State.TransactionState) (message : Message fork)
    (v f : U256) : Nat :=
  Gas.writeCost fork (originalAt state message.currentTarget (recipientSlot f))
    (balFrom state message v f) (sub (balFrom state message v f) v) false

/-- The price of the write of `_to` (warm). -/
abbrev creditCostF (fork : Fork) (state : State.TransactionState) (message : Message fork)
    (v t f : U256) : Nat :=
  Gas.writeCost fork (originalAt state message.currentTarget (recipientSlot t))
    (balTo state message v t f) (add (balTo state message v t f) v) false

/-- From 8648, with a fee of 0, the success path of StandardToken's `transferFrom` up to the STOP
at 915. -/
theorem body (hfork : .berlin ≤ fork)
    (hstatic : message.isStatic = false) (hacc : hasAccount state message.currentTarget)
    {v t f sel : U256} {M : ByteArray} (hM : M.size = 96)
    (hptr : loadWord (memoryReadBytes M 64 32) 0 32 = 0x60)
    (hov : v.toNat * (storageAt state message.currentTarget 3).toNat < 2 ^ 256)
    (hfee : feeOf state message v = 0)
    (hallow : allowOf state message f = MAX_UINT ∨ v.toNat ≤ (allowOf state message f).toNat)
    (hbal : v.toNat ≤ (balFrom state message v f).toNat)
    (hto : (balTo state message v t f).toNat + v.toNat < 2 ^ 256)
    {cA c3 c4 cF cT : Bool}
    (hcA : coldIn substate message.currentTarget (allowFrom message f) = cA)
    (hc3 : coldIn (accessSlot substate message.currentTarget (allowFrom message f))
      message.currentTarget 3 = c3)
    (hc4 : coldIn (accessSlot (accessSlot substate message.currentTarget (allowFrom message f))
      message.currentTarget 3) message.currentTarget 4 = c4)
    (hcF : coldIn (allowedSubF fork substate state message v f) message.currentTarget
      (recipientSlot f) = cF)
    (hcT : coldIn (accessSlot (allowedSubF fork substate state message v f) message.currentTarget
      (recipientSlot f)) message.currentTarget (recipientSlot t) = cT)
    {gas : Nat}
    (hstip : 972 + slotCost cA + slotCost c3 + slotCost c4 + slotCost cF + slotCost cT +
      mulCost v + capCost (rawFee state message v) (storageAt state message.currentTarget 4) +
      allowCostF fork state message v f + debitCostF fork state message v f + 2401 ≤ gas)
    (hg : 2971 + slotCost cA + slotCost c3 + slotCost c4 + slotCost cF + slotCost cT +
      mulCost v + capCost (rawFee state message v) (storageAt state message.currentTarget 4) +
      allowCostF fork state message v f + debitCostF fork state message v f +
      creditCostF fork state message v t f ≤ gas) :
    Gas.SpecG fork (At CODE message 8648 [0x60, 0, 0, 0, v, t, f, 0x1097, v, t, f, 0x0392, sel] M gas
        state substate)
      (Halted false .empty (gas - (2971 + slotCost cA + slotCost c3 + slotCost c4 + slotCost cF +
        slotCost cT + mulCost v +
        capCost (rawFee state message v) (storageAt state message.currentTarget 4) +
        allowCostF fork state message v f + debitCostF fork state message v f +
        creditCostF fork state message v t f))
        (creditedF state message v t f) (loggedSubF fork substate state message v t f)) := by
  have hacc3 : hasAccount (readsF state message f) message.currentTarget :=
    hasAccount_readSlot (hasAccount_readSlot (hasAccount_readSlot hacc))
  have hacc4 : hasAccount (readSlot (allowedF state message v f) message.currentTarget
      (recipientSlot f)) message.currentTarget :=
    hasAccount_readSlot (hasAccount_allowState hacc3)
  have hacc5 : hasAccount (readSlot (debitedF state message v f) message.currentTarget
      (recipientSlot t)) message.currentTarget :=
    hasAccount_readSlot (hasAccount_writeSlot hacc4)
  have horig : ∀ m, originalAt (allowedF state message v f) message.currentTarget m =
      originalAt state message.currentTarget m := by
    intro m
    rw [originalAt_allowState hacc3]
    simp only [originalAt_readSlot]
  have horig2 : ∀ m, originalAt (debitedF state message v f) message.currentTarget m =
      originalAt state message.currentTarget m := by
    intro m
    rw [originalAt_writeSlot hacc4, originalAt_readSlot, horig]
  have hT := slotCost_ge cT
  simp only [allowCostF, debitCostF, creditCostF, rawFee, feeOf, allowOf, balFrom, balTo,
    creditedF, debitedF, allowedF, readsF, loggedSubF, allowedSubF,
    accessF] at hstip hg hfee hbal hto hallow hcF hcT hacc4 hacc5 horig horig2 ⊢
  step allowRead hfork (by simp) hcA (by gas_ok) hM
  step feeCall hfork (by simp) hc3 (by gas_ok)
  step mulBlock (by simp) (by valid_dest) (by simpa only [storageAt_readSlot] using hov)
    (by gas_ok)
  at_pc 8802
  step divCall (by simp) (by gas_ok)
  step divBlock (by simp) (by valid_dest) (by decide) (by gas_ok)
  at_pc 8816
  step capBlock hfork (by simp) hc4 (by simp only [storageAt_readSlot]; gas_ok)
  simp only [storageAt_readSlot]
  step Gas.reshapeG (s' := (0x60 : U256) :: 0 :: 0 ::
      storageAt state message.currentTarget (allowFrom message f) :: v :: t :: f ::
      [0x1097, v, t, f, 0x0392, sel]) (by rw [hfee]) rfl rfl
  step allowStep hfork (by simp) (by simp only [storageAt_readSlot]) hallow
    (fun _ => ⟨hstatic, hacc3⟩)
    (coldIn_accessSlot_false (coldIn_accessSlot_false (coldIn_accessSlot_self _ _ _)))
    (by simp only [originalAt_readSlot]; gas_ok)
    (size_allowMem hM f)
  simp only [originalAt_readSlot]
  have hMa : (allowMem message M f).size = 96 := size_allowMem hM f
  have hMb := size_allowMem2 (message := message) hMa (storageAt state message.currentTarget
    (allowFrom message f)) f
  have hPb := ptr_allowMem2 (message := message) hMa (ptr_allowMem hM hptr f)
    (storageAt state message.currentTarget (allowFrom message f)) f
  step sendCall (by simp) (by gas_ok)
  step subBlock (by simp) (by valid_dest) (by simp) (by gas_ok)
  at_pc 9041
  step Gas.reshapeG (s' := v :: (0x60 : U256) :: 0 :: 0 ::
      storageAt state message.currentTarget (allowFrom message f) :: v :: t :: f ::
      [0x1097, v, t, f, 0x0392, sel]) (by simp [sub]) rfl rfl
  step debitCall hfork (by simp) hcF (by gas_ok) hMb
  step subBlock (by simp) (by valid_dest) hbal (by gas_ok)
  at_pc 9125
  step debitStore hfork (by simp) hstatic hacc4 (coldIn_accessSlot_self _ _ _)
    (by simp only [storageAt_readSlot, originalAt_readSlot, horig]; gas_ok) (size_mapMem hMb _ _)
  simp only [storageAt_readSlot, originalAt_readSlot, horig]
  step creditCall hfork (by simp) (cT := cT) (by rw [coldIn_storeSub]; exact hcT) (by gas_ok)
    (size_mapMem (size_mapMem hMb _ _) _ _)
  step addBlock (by simp) (by valid_dest) hto (by gas_ok)
  at_pc 9274
  step creditStore hfork (by simp) hstatic hacc5 (coldIn_accessSlot_self _ _ _) (by gas_ok)
    (by simp only [storageAt_readSlot, originalAt_readSlot, horig2]; gas_ok)
    (size_mapMem (size_mapMem (size_mapMem hMb _ _) _ _) _ _)
  simp only [storageAt_readSlot, originalAt_readSlot, horig2]
  step logBlock (by simp) hstatic (by gas_ok)
    (size_mapMem (size_mapMem (size_mapMem (size_mapMem hMb _ _) _ _) _ _) _ _)
    (ptr_mapMem (size_mapMem (size_mapMem (size_mapMem hMb _ _) _ _) _ _)
      (ptr_mapMem (size_mapMem (size_mapMem hMb _ _) _ _)
        (ptr_mapMem (size_mapMem hMb _ _) (ptr_mapMem hMb hPb _ _) _ _) _ _) _ _)
  refine (endBlock (by gas_ok)).consequence (fun _ h => h) ?_
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  exact ⟨hr, he, ho, by rw [hgas]; gas_ok, hs, hss⟩

/-- From 8648, with a fee of 0 and the gas of the whole success path (`hg`; the SSTOREs of the
allowance and of `balances[_from]` then have more than 2300 gas left), a frame that may write and
an account for `C`, with at most 2300 gas left at the `SSTORE` of `balances[_to]` (`hlow`): the
run reaches it, and it is `Stuck`. -/
theorem bodyLow2F (hfork : .berlin ≤ fork)
    (hstatic : message.isStatic = false) (hacc : hasAccount state message.currentTarget)
    {v t f sel : U256} {M : ByteArray} (hM : M.size = 96)
    (hov : v.toNat * (storageAt state message.currentTarget 3).toNat < 2 ^ 256)
    (hfee : feeOf state message v = 0)
    (hallow : allowOf state message f = MAX_UINT ∨ v.toNat ≤ (allowOf state message f).toNat)
    (hbal : v.toNat ≤ (balFrom state message v f).toNat)
    (hto : (balTo state message v t f).toNat + v.toNat < 2 ^ 256)
    {cA c3 c4 cF cT : Bool}
    (hcA : coldIn substate message.currentTarget (allowFrom message f) = cA)
    (hc3 : coldIn (accessSlot substate message.currentTarget (allowFrom message f))
      message.currentTarget 3 = c3)
    (hc4 : coldIn (accessSlot (accessSlot substate message.currentTarget (allowFrom message f))
      message.currentTarget 3) message.currentTarget 4 = c4)
    (hcF : coldIn (allowedSubF fork substate state message v f) message.currentTarget
      (recipientSlot f) = cF)
    (hcT : coldIn (accessSlot (allowedSubF fork substate state message v f) message.currentTarget
      (recipientSlot f)) message.currentTarget (recipientSlot t) = cT)
    {gas : Nat}
    (hg : 2971 + slotCost cA + slotCost c3 + slotCost c4 + slotCost cF + slotCost cT +
      mulCost v + capCost (rawFee state message v) (storageAt state message.currentTarget 4) +
      allowCostF fork state message v f + debitCostF fork state message v f +
      creditCostF fork state message v t f ≤ gas)
    (hlow : gas < 972 + slotCost cA + slotCost c3 + slotCost c4 + slotCost cF + slotCost cT +
      mulCost v + capCost (rawFee state message v) (storageAt state message.currentTarget 4) +
      allowCostF fork state message v f + debitCostF fork state message v f + 2401) :
    Gas.HoareG fork (At CODE message 8648 [0x60, 0, 0, 0, v, t, f, 0x1097, v, t, f, 0x0392, sel] M
        gas state substate) Gas.Stuck := by
  have hacc3 : hasAccount (readsF state message f) message.currentTarget :=
    hasAccount_readSlot (hasAccount_readSlot (hasAccount_readSlot hacc))
  have hacc4 : hasAccount (readSlot (allowedF state message v f) message.currentTarget
      (recipientSlot f)) message.currentTarget :=
    hasAccount_readSlot (hasAccount_allowState hacc3)
  have horig : ∀ m, originalAt (allowedF state message v f) message.currentTarget m =
      originalAt state message.currentTarget m := by
    intro m
    rw [originalAt_allowState hacc3]
    simp only [originalAt_readSlot]
  have hT := slotCost_ge cT
  simp only [allowCostF, debitCostF, creditCostF, rawFee, feeOf, allowOf, balFrom, balTo,
    debitedF, allowedF, readsF, allowedSubF,
    accessF] at hlow hg hfee hbal hto hallow hcF hcT hacc4 horig ⊢
  step allowRead hfork (by simp) hcA (by gas_ok) hM
  step feeCall hfork (by simp) hc3 (by gas_ok)
  step mulBlock (by simp) (by valid_dest) (by simpa only [storageAt_readSlot] using hov)
    (by gas_ok)
  at_pc 8802
  step divCall (by simp) (by gas_ok)
  step divBlock (by simp) (by valid_dest) (by decide) (by gas_ok)
  at_pc 8816
  step capBlock hfork (by simp) hc4 (by simp only [storageAt_readSlot]; gas_ok)
  simp only [storageAt_readSlot]
  step Gas.reshapeG (s' := (0x60 : U256) :: 0 :: 0 ::
      storageAt state message.currentTarget (allowFrom message f) :: v :: t :: f ::
      [0x1097, v, t, f, 0x0392, sel]) (by rw [hfee]) rfl rfl
  step allowStep hfork (by simp) (by simp only [storageAt_readSlot]) hallow
    (fun _ => ⟨hstatic, hacc3⟩)
    (coldIn_accessSlot_false (coldIn_accessSlot_false (coldIn_accessSlot_self _ _ _)))
    (by simp only [originalAt_readSlot]; gas_ok)
    (size_allowMem hM f)
  simp only [originalAt_readSlot]
  have hMa : (allowMem message M f).size = 96 := size_allowMem hM f
  have hMb := size_allowMem2 (message := message) hMa (storageAt state message.currentTarget
    (allowFrom message f)) f
  step sendCall (by simp) (by gas_ok)
  step subBlock (by simp) (by valid_dest) (by simp) (by gas_ok)
  at_pc 9041
  step Gas.reshapeG (s' := v :: (0x60 : U256) :: 0 :: 0 ::
      storageAt state message.currentTarget (allowFrom message f) :: v :: t :: f ::
      [0x1097, v, t, f, 0x0392, sel]) (by simp [sub]) rfl rfl
  step debitCall hfork (by simp) hcF (by gas_ok) hMb
  step subBlock (by simp) (by valid_dest) hbal (by gas_ok)
  at_pc 9125
  step debitStore hfork (by simp) hstatic hacc4 (coldIn_accessSlot_self _ _ _)
    (by simp only [storageAt_readSlot, originalAt_readSlot, horig]; gas_ok) (size_mapMem hMb _ _)
  simp only [storageAt_readSlot, originalAt_readSlot, horig]
  step creditCall hfork (by simp) (cT := cT) (by rw [coldIn_storeSub]; exact hcT) (by gas_ok)
    (size_mapMem (size_mapMem hMb _ _) _ _)
  step addBlock (by simp) (by valid_dest) hto (by gas_ok)
  at_pc 9274
  refine creditStoreBadF (by simp) (.of_low hfork ?_) ?_
    (size_mapMem (size_mapMem (size_mapMem hMb _ _) _ _) _ _)
  · gas_ok
  · gas_ok

end UsdtVerify.TransferFrom

end
