import UsdtVerify.Usdt.Proofs.Approve
import UsdtVerify.Usdt.Spec.Deprecated.TotalSupply
import UsdtVerify.Usdt.Spec.Transfer
import UsdtVerify.Usdt.Spec.Deprecated.BalanceOf

/-!
# transfer(to, value) when deprecated: the forward to the upgraded contract

The path of a call with selector 0xa9059cbb, no value, not paused, the caller not blacklisted,
and byte 20 of slot 10 (`deprecated`) set. TetherToken then calls
`UpgradedStandardToken(upgradedAddress).transferByLegacy(msg.sender, _to, _value)`.

- 1866 (entry), 5364 (paused check), 5392 (blacklist of the caller): the blocks of `Transfer`.
- At 5481, the deprecation check; the flag is set, so the JUMPI goes on at 5503 (`depSetW`).
- At 5503, the code reads slot 10 again and keeps its low 160 bits (`upLoad`).
- At 5560, it pushes the selector 0x6e18980a and the caller, and at 5568 it writes the call data
  at the free memory pointer 0x60: the selector, then the caller, `_to` and `_value` as words
  (`encode3`, 100 bytes from 0x60, memory grows from 96 to 224 bytes).
- At 5739, EXTCODESIZE of the address (`Deprecated.toCall`, `Deprecated.noCode`); at 5756, CALL
  with gas `gasleft - 710`, value 0, input 100 bytes at 0x60 and NO output range (size 0).
- At 5757, a revert with no output when the call failed (`Deprecated.failTail`); else the code
  goes back to 1930 and stops (STOP): `transfer` returns no word.

The blocks `depSetW`, `upLoad`, `encode3` are proved for the pcs of `approve` too.

# approve(spender, value) when deprecated

Selector 0x095ea7b3, no value, at least 68 bytes of call data (TetherToken's own
`onlyPayloadSize(2 * 32)` at 2931 comes before the deprecation check), byte 20 of slot 10 set.
TetherToken then calls `approveByLegacy(msg.sender, _spender, _value)` (selector 0xaee92d33).

- 610 (entry), 2931 (payload check): the blocks of `Approve`.
- 2955 (`depSetW`), 2977 (`upLoad`), 3034: selector and caller, 3042 (`encode3`), 3213
  (EXTCODESIZE), CALL at 3230 with input 100 bytes at 0x60 and no output range; 3231: revert on
  failure, else back to 674 and STOP.
-/

namespace UsdtVerify.DeprecatedTransfer

open EthLib.Base (Fork U256 toAddressMasked)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts
open UsdtVerify.Complete (Route Routes routeAddr routeCode routeCost routeState routeSub SendsVia
  routes_congr routeCost_insert_insert callWithR)
open Deprecated DeprecatedBalance Transfer TransferOk

-- `Approve.entry` and `Approve.payload` are used by their full names.

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate}

/-! ## Reads of memory -/

/-- Growth keeps a read within the memory before it. -/
theorem read_ext {X : ByteArray} {n s k : Nat} (h : s + k ≤ X.size) :
    memoryReadBytes (memoryExtend X n) s k = memoryReadBytes X s k := by
  have h' : s + k ≤ (memoryExtend X n).size := by rw [size_memoryExtend]; omega
  apply EthLib.Base.eq_of_byteAt
  · rw [size_memoryReadBytes h', size_memoryReadBytes h]
  · intro i
    rw [byteAt_memoryReadBytes h', byteAt_memoryReadBytes h, byteAt_memoryExtend]

/-- A read of the first `k` bytes of a written range gives the first `k` bytes of the value. -/
theorem read_prefix {X w : ByteArray} {s k : Nat} (hfit : s + w.size ≤ X.size)
    (hk : k ≤ w.size) : memoryReadBytes (memoryWrite X s w) s k = w.extract 0 k := by
  have hw : (memoryWrite X s w).size = X.size := size_memoryWrite hfit
  apply EthLib.Base.eq_of_byteAt
  · rw [size_memoryReadBytes (by omega), ByteArray.size_extract]; omega
  · intro i
    rw [byteAt_memoryReadBytes (by omega), byteAt_memoryWrite hfit, EthLib.Base.byteAt_extract]
    by_cases hi : i < k
    · rw [ite_eq_left hi, ite_eq_left (by omega), ite_eq_left (by omega)]
      congr 1; omega
    · rw [ite_eq_right hi, ite_eq_right (by omega)]

/-! ## The memory of the encoding of three words -/

/-- The word that the code writes for a selector `sel`: its 4 bytes shifted left by 224 bits. -/
abbrev selWord (sel : U256) : U256 :=
  mul (0x0100000000000000000000000000000000000000000000000000000000 : U256)
    (bitwiseAnd (0xffffffff : U256) sel)

/-- The selector word written at 0x60, over a memory of 96 bytes grown by 32. -/
def W1 (M : ByteArray) (sel : U256) : ByteArray :=
  memoryWrite (memoryExtend M 32) 96 (wordBytes (selWord sel))

/-- Then the word `k` at 0x64. -/
def W2 (M : ByteArray) (sel k : U256) : ByteArray :=
  memoryWrite (memoryExtend (W1 M sel) 32) 100 (wordBytes k)

/-- Then the word `b` at 0x84. -/
def W3 (M : ByteArray) (sel k b : U256) : ByteArray :=
  memoryWrite (memoryExtend (W2 M sel k) 32) 132 (wordBytes b)

/-- Then the word `w` at 0xa4: the memory before the CALL (224 bytes). -/
def W4 (M : ByteArray) (sel k b w : U256) : ByteArray :=
  memoryWrite (memoryExtend (W3 M sel k b) 32) 164 (wordBytes w)

section Sizes

variable {M : ByteArray} (hM : M.size = 96) {sel k b w : U256}
include hM

theorem size_W1 : (W1 M sel).size = 128 := by
  rw [W1, size_memoryWrite (by rw [size_wordBytes, size_memoryExtend, hM]; omega), size_memoryExtend, hM]

theorem size_W2 : (W2 M sel k).size = 160 := by
  rw [W2, size_memoryWrite (by rw [size_wordBytes, size_memoryExtend, size_W1 hM]; omega),
    size_memoryExtend, size_W1 hM]

theorem size_W3 : (W3 M sel k b).size = 192 := by
  rw [W3, size_memoryWrite (by rw [size_wordBytes, size_memoryExtend, size_W2 hM]; omega),
    size_memoryExtend, size_W2 hM]

theorem size_W4 : (W4 M sel k b w).size = 224 := by
  rw [W4, size_memoryWrite (by rw [size_wordBytes, size_memoryExtend, size_W3 hM]; omega),
    size_memoryExtend, size_W3 hM]

/-- The free memory pointer at 0x40 is kept by the four writes (all from 0x60 on). -/
theorem read40_W4 : memoryReadBytes (W4 M sel k b w) 64 32 = memoryReadBytes M 64 32 := by
  rw [W4, memoryReadBytes_memoryWrite_of_disjoint
      (by rw [size_wordBytes, size_memoryExtend, size_W3 hM]; omega) (.inl (by decide)),
    read_ext (by rw [size_W3 hM]; omega), W3, memoryReadBytes_memoryWrite_of_disjoint
      (by rw [size_wordBytes, size_memoryExtend, size_W2 hM]; omega) (.inl (by decide)),
    read_ext (by rw [size_W2 hM]; omega), W2, memoryReadBytes_memoryWrite_of_disjoint
      (by rw [size_wordBytes, size_memoryExtend, size_W1 hM]; omega) (.inl (by decide)),
    read_ext (by rw [size_W1 hM]; omega), W1, memoryReadBytes_memoryWrite_of_disjoint
      (by rw [size_wordBytes, size_memoryExtend, hM]; omega) (.inl (by decide)),
    read_ext (by rw [hM]; omega)]

/-- The 100 bytes from 0x60: the 4 bytes of the selector, then the words `k`, `b`, `w`. -/
theorem data_W4 : memoryReadBytes (W4 M sel k b w) 96 100 =
    (wordBytes (selWord sel)).extract 0 4 ++ wordBytes k ++ wordBytes b ++ wordBytes w := by
  have h4 := memoryReadBytes_memoryWrite_eq_append
    (memory := memoryExtend (W3 M sel k b) 32)
    (value := wordBytes w) (s := 96) (k := 68)
    (by rw [size_wordBytes, size_memoryExtend, size_W3 hM]; omega)
  have h3 := memoryReadBytes_memoryWrite_eq_append
    (memory := memoryExtend (W2 M sel k) 32)
    (value := wordBytes b) (s := 96) (k := 36)
    (by rw [size_wordBytes, size_memoryExtend, size_W2 hM]; omega)
  have h2 := memoryReadBytes_memoryWrite_eq_append
    (memory := memoryExtend (W1 M sel) 32)
    (value := wordBytes k) (s := 96) (k := 4)
    (by rw [size_wordBytes, size_memoryExtend, size_W1 hM]; omega)
  rw [size_wordBytes] at h4 h3 h2
  rw [W4, h4, read_ext (by rw [size_W3 hM]; omega), W3, h3, read_ext (by rw [size_W2 hM]; omega), W2, h2,
    read_ext (by rw [size_W1 hM]; omega), W1,
    read_prefix (by rw [size_wordBytes, size_memoryExtend, hM]; omega) (by rw [size_wordBytes]; decide)]

end Sizes

/-! ## The blocks of the forward -/

/-- The deprecation check at 5481 (transfer), 2955 (approve) or 3890 (transferFrom) with the flag
set: it reads slot 10, the JUMPI goes on, and the stack is as before. -/
theorem depSetW (hfork : .berlin ≤ fork) {p q : Nat}
    (hp : (p = 5481 ∧ q = 5503) ∨ (p = 2955 ∧ q = 2977) ∨ (p = 3890 ∧ q = 3912)) {M : ByteArray}
    {rest : List U256} (hrest : rest.length ≤ 16) {c10 : Bool}
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0)
    (hc10 : coldIn substate message.currentTarget 10 = c10)
    {gas : Nat} (hg : 106 + slotCost c10 ≤ gas) :
    Gas.HoareG fork (At CODE message p rest M gas state substate)
      (At CODE message q rest M (gas - (106 + slotCost c10))
        (readSlot state message.currentTarget 10)
        (accessSlot substate message.currentTarget 10)) := by
  have hexp : exponentBytes (0x14 : U256) = 1 := by decide
  rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals
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
    step pushAnyR 2
    step jumpi0R (isZero_flag_set hdep)
    exact (repc (by decide)).seq (Gas.reshapeG rfl rfl (by gas_ok))

/-- At 5503 (transfer), 2977 (approve) or 3912 (transferFrom): the code reads slot 10 again
(warm) and pushes its low 160 bits, the upgraded address. -/
theorem upLoad (hfork : .berlin ≤ fork) {p q : Nat}
    (hp : (p = 5503 ∧ q = 5560) ∨ (p = 2977 ∧ q = 3034) ∨ (p = 3912 ∧ q = 3969)) {M : ByteArray}
    {rest : List U256} (hrest : rest.length ≤ 16) {gas : Nat} (hg : 145 ≤ gas) :
    Gas.HoareG fork (At CODE message p rest M gas
        (readSlot state message.currentTarget 10) (accessSlot substate message.currentTarget 10))
      (At CODE message q (upWord (storageAt state message.currentTarget 10) :: rest) M
        (gas - 145) (readSlot state message.currentTarget 10)
        (accessSlot substate message.currentTarget 10)) := by
  have hexp : exponentBytes (0 : U256) = 0 := by decide
  rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals
    step pushR 1 (0x0a : U256)
    step pushR 1 (0 : U256)
    step swapR 0
    norm
    step Gas.sloadG hfork (cold := false) (by code_fact) (by code_fact)
      (coldIn_accessSlot_self _ _ _) (by gas_ok)
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
    exact restate (by decide)
      (by rw [up_eq, ← storageAt_readSlot state message.currentTarget message.currentTarget 10 10])
      rfl (by gas_ok) (readSlot_readSlot state message.currentTarget 10)
      (accessSlot_accessSlot substate message.currentTarget 10)

/-- From 5568 (transfer) or 3042 (approve), with the stack `w, b, C, sel, U` on top: the code
writes at the free memory pointer 0x60 the selector word of `sel`, then the words `C`, `b` (both
masked to 160 bits) and `w`, and pushes the operands of CALL down to the EXTCODESIZE at 5739 or
3213: input 0x64 bytes at 0x60, output 0 bytes at 0x60. -/
theorem encode3 {p q : Nat} (hp : (p = 5568 ∧ q = 5739) ∨ (p = 3042 ∧ q = 3213)) {M : ByteArray}
    (hM : M.size = 96) (hptr : loadWord (memoryReadBytes M 64 32) 0 32 = 0x60)
    {w b C sel U : U256} {rest : List U256} (hrest : rest.length ≤ 16) {gas : Nat}
    (hg : 160 ≤ gas) :
    Gas.HoareG fork (At CODE message p ([w, b, C, sel, U] ++ rest) M gas state substate)
      (At CODE message q ([U, U, 0, 0x60, 0x64, 0x60, 0, 0xc4, sel, U] ++ rest)
        (W4 M sel (mkey C) (mkey b) w) (gas - 160) state substate) := by
  have hx0 : extendMemory M.size [((0x40 : U256), (32 : U256))] = ⟨0, 0⟩ := by
    rw [hM]; decide
  have hx1 : extendMemory M.size [((0x60 : U256), (32 : U256))] = ⟨3, 32⟩ := by
    rw [hM]; decide
  have hx2 : extendMemory (W1 M sel).size [((0x64 : U256), (32 : U256))] = ⟨3, 32⟩ := by
    rw [size_W1 hM]; decide
  have hx3 : extendMemory (W2 M sel (mkey C)).size [((0x84 : U256), (32 : U256))] = ⟨3, 32⟩ := by
    rw [size_W2 hM]; decide
  have hx4 : extendMemory (W3 M sel (mkey C) (mkey b)).size [((0xa4 : U256), (32 : U256))] =
      ⟨3, 32⟩ := by
    rw [size_W3 hM]; decide
  have hx5 : extendMemory (W4 M sel (mkey C) (mkey b) w).size [((0x40 : U256), (32 : U256))] =
      ⟨0, 0⟩ := by
    rw [size_W4 hM]; decide
  have h64 : add (0x04 : U256) (0x60 : U256) = 0x64 := by decide
  have h84 : add (0x20 : U256) (0x64 : U256) = 0x84 := by decide
  have ha4 : add (0x20 : U256) (0x84 : U256) = 0xa4 := by decide
  have hc4 : add (0x20 : U256) (0xa4 : U256) = 0xc4 := by decide
  have hs4 : sub (0xc4 : U256) (0x60 : U256) = 0x64 := by decide
  rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals
    step pushR 1 (0x40 : U256)
    step Gas.mloadG (by code_fact) (by code_fact) (by rw [hx0]; gas_ok)
    step Gas.reshapeG (s' := [0x60, w, b, C, sel, U] ++ rest) (m' := M) (g' := gas - 6)
      (by rw [hx0, memoryExtend_zero, show (0x40 : U256).toNat = 64 from rfl, hptr]; rfl)
      (by rw [hx0, memoryExtend_zero]) (by rw [hx0]; gas_ok)
    step dupR 4
    step pushR 4 (0xffffffff : U256)
    step binR 0x16 Local.instruction_and
    step pushR 29 (0x0100000000000000000000000000000000000000000000000000000000 : U256)
    step binR 0x02 Local.instruction_mul
    step dupR 1
    step Gas.mstoreG (by code_fact) (by code_fact) (by rw [hx1]; gas_ok)
    step Gas.reshapeG (s' := [0x60, w, b, C, sel, U] ++ rest) (m' := W1 M sel) (g' := gas - 32) rfl
      (by rw [hx1]; rfl) (by rw [hx1]; gas_ok)
    step pushR 1 (0x04 : U256)
    step binR 0x01 instruction_add
    rw [h64]
    step dupR 0
    step dupR 4
    step pushR 20 ADDR_MASK
    step binR 0x16 Local.instruction_and
    step pushR 20 ADDR_MASK
    step binR 0x16 Local.instruction_and
    step dupR 1
    step Gas.mstoreG (by code_fact) (by code_fact) (by rw [hx2]; gas_ok)
    step Gas.reshapeG (s' := [0x64, 0x64, w, b, C, sel, U] ++ rest) (m' := W2 M sel (mkey C))
      (g' := gas - 65) rfl (by rw [hx2]; rfl) (by rw [hx2]; gas_ok)
    step pushR 1 (0x20 : U256)
    step binR 0x01 instruction_add
    rw [h84]
    step dupR 3
    step pushR 20 ADDR_MASK
    step binR 0x16 Local.instruction_and
    step pushR 20 ADDR_MASK
    step binR 0x16 Local.instruction_and
    step dupR 1
    step Gas.mstoreG (by code_fact) (by code_fact) (by rw [hx3]; gas_ok)
    step Gas.reshapeG (s' := [0x84, 0x64, w, b, C, sel, U] ++ rest)
      (m' := W3 M sel (mkey C) (mkey b)) (g' := gas - 95) rfl (by rw [hx3]; rfl)
      (by rw [hx3]; gas_ok)
    step pushR 1 (0x20 : U256)
    step binR 0x01 instruction_add
    rw [ha4]
    step dupR 2
    step dupR 1
    step Gas.mstoreG (by code_fact) (by code_fact) (by rw [hx4]; gas_ok)
    step Gas.reshapeG (s' := [0xa4, 0x64, w, b, C, sel, U] ++ rest)
      (m' := W4 M sel (mkey C) (mkey b) w) (g' := gas - 113) rfl (by rw [hx4]; rfl)
      (by rw [hx4]; gas_ok)
    step pushR 1 (0x20 : U256)
    step binR 0x01 instruction_add
    rw [hc4]
    step swapR 3
    norm
    step popR
    step popR
    step popR
    step popR
    step pushR 1 (0 : U256)
    step pushR 1 (0x40 : U256)
    step Gas.mloadG (by code_fact) (by code_fact) (by rw [hx5]; gas_ok)
    step Gas.reshapeG (s' := [0x60, 0, 0xc4, sel, U] ++ rest) (m' := W4 M sel (mkey C) (mkey b) w)
      (g' := gas - 139)
      (by rw [hx5, memoryExtend_zero, show (0x40 : U256).toNat = 64 from rfl, read40_W4 hM,
        hptr]; rfl)
      (by rw [hx5, memoryExtend_zero]) (by rw [hx5]; gas_ok)
    step dupR 0
    step dupR 3
    step binR 0x03 Local.instruction_sub
    rw [hs4]
    step dupR 1
    step pushR 1 (0 : U256)
    step dupR 7
    step dupR 0
    exact (repc (by decide)).seq (Gas.reshapeG rfl rfl (by gas_ok))

/-! ## transfer -/

/-- After a call that succeeded (flag 1), from 5757: the code drops the call operands, returns
to 1930 and stops. -/
theorem okTailT {sel U v a x : U256} {M : ByteArray} {gas : Nat} (hg : 51 ≤ gas) :
    Gas.SpecG fork (At CODE message 5757 [1, 0xc4, sel, U, v, a, 0x078a, x] M gas state substate)
      (Halted false .empty (gas - 51) state substate) := by
  step unR 0x15 instruction_iszero
  step unR 0x15 instruction_iszero
  step pushR 2 (0x1687 : U256)
  step jumpiR (by decide)
  step jumpdestR
  step popR
  step popR
  step popR
  step pushR 2 (0x169a : U256)
  step jumpR
  at_pc 5786
  step jumpdestR
  step popR
  step popR
  step jumpR
  step repc (pc' := 1930) (by decide)
  step jumpdestR
  refine (Gas.stopG (by code_fact) (by code_fact)).consequence (fun _ h => h) ?_
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  exact ⟨hr, he, ho, by rw [hgas]; gas_ok, hs, hss⟩

/-- The selector of `transferByLegacy(address,address,uint256)`. -/
def SEL_T : ByteArray := ⟨#[0x6e, 0x18, 0x98, 0x0a]⟩

theorem sel_T : (wordBytes (selWord 0x6e18980a)).extract 0 4 = SEL_T := by decide +kernel

/-- The call data that `transfer` forwards when deprecated:
`transferByLegacy(msg.sender, _to, _value)`, i.e. the selector 0x6e18980a, then the caller, `_to`
(argument word 0 masked to 160 bits) and `_value` (argument word 1) as words. -/
abbrev dataT (message : Message fork) : ByteArray :=
  SEL_T ++ wordBytes (callerKey message) ++ wordBytes (addrArg message.data 0) ++
    wordBytes (wordArg message.data 1)

/-- The memory before the CALL of the deprecated `transfer`. -/
abbrev memT (message : Message fork) : ByteArray :=
  W4 (MEMK (callerKey message) 6) 0x6e18980a (mkey message.caller.toU256)
    (mkey (addrArg message.data 0)) (wordArg message.data 1)

theorem data_memT (message : Message fork) :
    memoryReadBytes (memoryExtend (memT message) 0) 96 100 = dataT message := by
  rw [memoryExtend_zero, memT, data_W4 (size_MEMK _ _), sel_T, TransferOk.mkey_addrArg]

/-- The gas of the path from pc 0 to the CALL, for `transfer`. -/
abbrev preCostT (fork : Fork) (c0 cB c10 cU : Bool) : Nat :=
  1357 + slotCost c0 + slotCost cB + slotCost c10 + extCost fork cU

/-- The gas that the code asks CALL to pass on, for a frame that starts with `gas`. -/
abbrev askedOfT (fork : Fork) (gas : Nat) (c0 cB c10 cU : Bool) : U256 :=
  asked (gas - (1354 + slotCost c0 + slotCost cB + slotCost c10 + extCost fork cU))

/-- What CALL pays and passes on (EIP-150, EIP-2929; the address is warm after EXTCODESIZE; no
growth of memory at the CALL). -/
abbrev callGasT (fork : Fork) (gas : Nat) (c0 cB c10 cU : Bool) (R : Nat) :
    MessageCallGas :=
  messageCallGas fork 0 (askedOfT fork gas c0 cB c10 cU).toNat (gas - preCostT fork c0 cB c10 cU) 0 (100 + R)

/-- The state when `transfer` calls: slots 0, `isBlackListed[caller]` and 10 recorded read, then
the upgraded account. -/
abbrev callStateT (state : State.TransactionState) (message : Message fork) :
    State.TransactionState :=
  (shortState state message).recordAccountRead (upAddr state message)

/-- The substate when `transfer` calls: those slots and the upgraded address accessed. -/
abbrev callSubT (substate : Substate) (state : State.TransactionState) (message : Message fork) :
    Substate :=
  { shortSubstate substate message with
    accessedAddresses := substate.accessedAddresses.insert (upAddr state message) }

/-- The extra price of the CALL along the route `r` (the access to the delegate, or 0). -/
abbrev callRT (substate : Substate) (state : State.TransactionState) (message : Message fork)
    (r : Route) : Nat :=
  routeCost fork (callSubT substate state message).accessedAddresses r

/-- From pc 0 to the CALL at 5756, for a deprecated `transfer` whose upgraded account has code. -/
theorem preCallT (hfork : .berlin ≤ fork)
    (hsize : 4 ≤ message.data.size) (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0xa9059cbb) (hv : message.value = 0)
    (hnp : byte20 (storageAt state message.currentTarget 0) = 0)
    (hnb : (storageAt state message.currentTarget (blackSlot message)).toNat % 256 = 0)
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0) {c : ByteArray}
    (hcode : state.getCode (state.getAccount (upAddr state message)).codeHash = .ok c)
    (hsz : 0 < c.size) (hszl : c.size < 2 ^ 256)
    {c0 cB c10 cU : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hcB : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget
      (blackSlot message) = cB)
    (hc10 : coldIn (accessSlot (accessSlot substate message.currentTarget 0) message.currentTarget
      (blackSlot message)) message.currentTarget 10 = c10)
    (hcU : decide (upAddr state message ∉ substate.accessedAddresses) = cU)
    {gas : Nat} (hg : preCostT fork c0 cB c10 cU ≤ gas) :
    Hoare fork (At CODE message 0 [] .empty gas state substate)
      (At CODE message 5756
        [askedOfT fork gas c0 cB c10 cU, upWord (storageAt state message.currentTarget 10), 0, 0x60,
          0x64, 0x60, 0, 0xc4, 0x6e18980a, upWord (storageAt state message.currentTarget 10),
          wordArg message.data 1, addrArg message.data 0, 0x078a,
          BitVec.ofNat 256 (selector message.data)]
        (memT message) (gas - preCostT fork c0 cB c10 cU) (callStateT state message)
        (callSubT substate state message)) := by
  simp only [preCostT, askedOfT, extCost] at hg ⊢
  have ht : tested (BitVec.ofNat 256 (selector message.data)) ENTRIES = 22 := by
    rw [hsel]; decide
  have hb : branch (BitVec.ofNat 256 (selector message.data)) 54 (entrySize 4 2) ENTRIES =
      1866 := by
    rw [hsel]; decide
  have h1 := dispatch (state := state) (substate := substate) hsize hsize' (gas := gas)
    (by rw [ht]; gas_ok)
  rw [ht, hb] at h1
  refine Gas.Triple.seqL h1 ?_
  step entry hv (by gas_ok)
  step notPaused hfork (by simp) hnp hc0 (by gas_ok)
  step blackLookup hfork (by simp) hcB (by gas_ok)
  step jumpiR (blackTest_ne (by rw [storageAt_readSlot]; exact hnb))
  step repcH (pc' := 5481) (by decide)
  step depSetW hfork (Or.inl ⟨rfl, rfl⟩) (by simp)
    (by rw [storageAt_readSlot, storageAt_readSlot]; exact hdep) hc10 (by gas_ok)
  step upLoad (state := readSlot (readSlot state message.currentTarget 0) message.currentTarget
    (blackSlot message)) hfork (Or.inl ⟨rfl, rfl⟩) (by simp) (by gas_ok)
  rw [storageAt_readSlot, storageAt_readSlot]
  step pushR 4 (0x6e18980a : U256)
  step Logic.caller (by code_fact) (by code_fact) (by gas_ok) (by stk_ok)
  step dupR 4
  step dupR 4
  step encode3 (Or.inl ⟨rfl, rfl⟩) (size_MEMK _ _) (ptr_MEMK _ _)
    (rest := [wordArg message.data 1, addrArg message.data 0, 0x078a,
      BitVec.ofNat 256 (selector message.data)]) (by simp) (by gas_ok)
  step Logic.reshape (g' := gas - (1329 + slotCost c0 + slotCost cB + slotCost c10)) rfl rfl (by gas_ok)
  refine (toCall (gas := gas - (1329 + slotCost c0 + slotCost cB + slotCost c10))
    (st := shortState state message) (ss := shortSubstate substate message) (message := message)
    (M := memT message)
    (rest := [upWord (storageAt state message.currentTarget 10), 0, 0x60, 0x64, 0x60, 0, 0xc4,
      0x6e18980a, upWord (storageAt state message.currentTarget 10), wordArg message.data 1,
      addrArg message.data 0, 0x078a, BitVec.ofNat 256 (selector message.data)])
    hfork (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))) (by simp) hcode hsz hszl hcU
    (by simp only [extCost]; gas_ok)).seq ?_
  refine Logic.reshape ?_ rfl (by simp only [extCost]; gas_ok)
  simp only [List.cons.injEq, and_true]
  congr 1
  unfold extCost; omega

/-- The hypotheses shared by the deprecated `transfer` theorems, besides the gas.

Berlin ≤ fork (Glamsterdam included); call data of 4 to 2^256 - 1 bytes with the selector 0xa9059cbb (NO
check of 68 bytes: that payload check is in BasicToken, which the deprecated path does not reach;
missing argument bytes read as 0); no value; not paused (byte 20 of slot 0 is 0); the caller not
blacklisted (low byte of `isBlackListed[caller]` is 0); deprecated (byte 20 of slot 10 is not 0);
the upgraded address `ua` (low 160 bits of slot 10) holds a code `c` of 1 to 2^256 - 1 bytes;
the CALL follows the route `r` (`Routes`: no delegation, or from Pectra an EIP-7702 delegate whose
code is found); the depth leaves room for one more frame; `c0`, `cB`, `c10`,
`cU` are whether slot 0, the blacklist slot, slot 10 and `ua` are cold when the code reads them. -/
structure HypT (fork : Fork) (message : Message fork) (state : State.TransactionState)
    (substate : Substate) (c : ByteArray) (r : Route) (c0 cB c10 cU : Bool) : Prop where
  berlin : .berlin ≤ fork
  size : 4 ≤ message.data.size
  size' : message.data.size < 2 ^ 256
  sel : selector message.data = 0xa9059cbb
  value : message.value = 0
  notPaused : byte20 (storageAt state message.currentTarget 0) = 0
  notBlack : (storageAt state message.currentTarget (blackSlot message)).toNat % 256 = 0
  deprecated : byte20 (storageAt state message.currentTarget 10) ≠ 0
  code : state.getCode (state.getAccount (upAddr state message)).codeHash = .ok c
  codeSize : 0 < c.size
  codeSize' : c.size < 2 ^ 256
  route : Routes fork state c r
  depth : message.depth + 1 ≤ STACK_DEPTH_LIMIT
  cold0 : coldIn substate message.currentTarget 0 = c0
  coldB : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget
    (blackSlot message) = cB
  cold10 : coldIn (accessSlot (accessSlot substate message.currentTarget 0)
    message.currentTarget (blackSlot message)) message.currentTarget 10 = c10
  coldU : decide (upAddr state message ∉ substate.accessedAddresses) = cU

/-- `spec_depT` with the bound `htail` (at least 51 gas left after the price of the CALL) replaced by
`hcg`: every ended forwarded message that meets `callee` leaves at least 51 gas for the code after
the CALL, the gas the CALL keeps plus the gas left in the ended frame.
Stated as a `Sends.SpecOn` (round 26): the frames that end the runner's messages meet
`callee`, the runner may fail with any error, and the run ends as stated or at a failure of the
runner on a forwarded message (`SendsVia`); `.toUnder` gives EthLib's `SpecUnder`. -/
theorem spec_depT_g {c : ByteArray} {r : Route} {c0 cB c10 cU : Bool}
    (h : HypT fork message state substate c r c0 cB c10 cU) {gas : Nat}
    (hg : preCostT fork c0 cB c10 cU + 100 + callRT substate state message r ≤ gas)
    {callee : Evm fork Nat → Message fork → Evm fork Nat → Prop}
    (hcg : ∀ caller msg child, callee caller msg child →
      SendsVia message (upAddr state message) c r (dataT message) msg →
      51 ≤ gas - preCostT fork c0 cB c10 cU - (callGasT fork gas c0 cB c10 cU (callRT substate state message r)).cost + child.gas) :
    Sends.SpecOn fork callee (SendsVia message (upAddr state message) c r (dataT message))
      (At CODE message 0 [] .empty gas state substate)
      fun evm => ∃ caller msg child, callee caller msg child ∧
        SendsVia message (upAddr state message) c r (dataT message) msg ∧
        msg.gas = (callGasT fork gas c0 cB c10 cU (callRT substate state message r)).subCall ∧
        caller.state = (routeState ((callStateT state message).recordAccountRead
          (upAddr state message)) r).recordAccountRead message.currentTarget ∧
        caller.substate = routeSub { callSubT substate state message with
          accessedAddresses :=
            (callSubT substate state message).accessedAddresses.insert (upAddr state message) } r ∧
        (child.error = none →
          Halted false .empty
            (gas - preCostT fork c0 cB c10 cU - (callGasT fork gas c0 cB c10 cU (callRT substate state message r)).cost + child.gas - 51)
            (incorporateChild fork caller child).state
            (incorporateChild fork caller child).substate evm) ∧
        (child.error ≠ none →
          Halted true .empty
            (gas - preCostT fork c0 cB c10 cU - (callGasT fork gas c0 cB c10 cU (callRT substate state message r)).cost + child.gas - 25)
            (incorporateChild fork caller child).state
            (incorporateChild fork caller child).substate evm) := by
  have hext : extendMemory (memT message).size
      [((0x60 : U256), (0x64 : U256)), ((0x60 : U256), (0 : U256))] = ⟨0, 0⟩ := by
    rw [memT, size_W4 (size_MEMK _ _)]; decide
  have hR : routeCost fork ((callSubT substate state message).accessedAddresses.insert
      (toAddressMasked (upWord (storageAt state message.currentTarget 10)))) r =
      callRT substate state message r := routeCost_insert_insert _ _ _
  have hcall := Complete.callWithRS (fork := fork) (code := CODE) (message := message) (pc := 5756)
    (memory := memT message) (gas := gas - preCostT fork c0 cB c10 cU)
    (state := callStateT state message)
    (substate := callSubT substate state message) (callee := callee)
    (asked := askedOfT fork gas c0 cB c10 cU) (to := upWord (storageAt state message.currentTarget 10))
    (i := 0x60) (isz := 0x64) (o := 0x60) (osz := 0)
    (rest := [0xc4, 0x6e18980a, upWord (storageAt state message.currentTarget 10),
      wordArg message.data 1, addrArg message.data 0, 0x078a,
      BitVec.ofNat 256 (selector message.data)]) (cold := false)
    h.berlin (by code_fact) (by code_fact) h.code (routes_congr (fun _ => rfl) h.route) h.depth
    (by simp [upAddr]) (by rw [hext, hR]; simp only [accCost_false]; omega)
  rw [hext, hR] at hcall
  simp only [accCost_false] at hcall
  have hcall := hcall.mono_S (S' := SendsVia message (upAddr state message) c r (dataT message)) fun _ h => by
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ := h
    exact ⟨a1, a2, a3, a4, a5, a6, by rw [a7]; exact data_memT message, a8, a9, a10⟩
  refine Sends.SpecOn.seq (Sends.HoareOn.of_hoare (preCallT h.berlin h.size h.size' h.sel h.value
    h.notPaused h.notBlack h.deprecated h.code h.codeSize h.codeSize' h.cold0 h.coldB h.cold10
    h.coldU (by omega))) (Sends.HoareOn.seq hcall (Sends.HoareOn.of_hoare ?_))
  rintro evm ⟨caller, msg, child, hcal, -, hcs, hcss, hmg, hmc, hmt, hmtg, hmca, hmcode, hmdp, hmd, hmv,
    hmdep, hmst, hat⟩
  have hfwd : SendsVia message (upAddr state message) c r (dataT message) msg := by
    refine ⟨hmc, hmt, hmtg, hmca, hmcode, hmdp, ?_, hmv, hmdep, hmst⟩
    rw [hmd]; exact data_memT message
  have hT := hcg caller msg child hcal hfwd
  by_cases he : child.error = none
  · simp only [he, Option.isNone_none, ↓reduceIte] at hat
    obtain ⟨after, hreach, hrun, hq⟩ := okTailT (fork := fork) (message := message)
      (state := (incorporateChild fork caller child).state)
      (substate := (incorporateChild fork caller child).substate)
      (gas := gas - preCostT fork c0 cB c10 cU - ((callGasT fork gas c0 cB c10 cU (callRT substate state message r)).cost + 0) +
        child.gas)
      (by omega) evm hat
    refine ⟨after, Gas.reaches_toStep hreach, hrun, caller, msg, child, hcal, hfwd, hmg, hcs, hcss, fun _ => ?_,
      fun h => absurd he h⟩
    obtain ⟨h1, h2, h0, h3, h4, h5⟩ := hq
    exact ⟨h1, h2, h0, by rw [h3]; omega, h4, h5⟩
  · have hz : child.error.isNone = false := by
      cases h : child.error
      · exact absurd h he
      · rfl
    simp only [hz, Bool.false_eq_true, ↓reduceIte] at hat
    obtain ⟨after, hreach, hrun, hq⟩ := failTail (fork := fork) (message := message)
      (state := (incorporateChild fork caller child).state)
      (substate := (incorporateChild fork caller child).substate) h.berlin
      (Or.inr (Or.inr (Or.inl rfl)))
      (rest := [0xc4, 0x6e18980a, upWord (storageAt state message.currentTarget 10),
        wordArg message.data 1, addrArg message.data 0, 0x078a,
        BitVec.ofNat 256 (selector message.data)]) (by simp)
      (gas := gas - preCostT fork c0 cB c10 cU - ((callGasT fork gas c0 cB c10 cU (callRT substate state message r)).cost + 0) +
        child.gas)
      (by omega) evm hat
    refine ⟨after, Gas.reaches_toStep hreach, hrun, caller, msg, child, hcal, hfwd, hmg, hcs, hcss,
      fun h => absurd h he, fun _ => ?_⟩
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hq
    exact ⟨h1, h2, h3, by rw [h4]; omega, h5, h6⟩

/-- The specification of `transfer(to, value)` when deprecated, for every callee.

Under the hypotheses `HypT`, with the gas of the path to the CALL and of the CALL (`hg`), and 51 gas
left after the price of the CALL (`htail`): under every runner whose ended messages meet `callee`,
the run ends (or the runner aborts) in a stopped frame for which there are a caller frame, a
message `msg` and an ended frame `child` with `callee caller msg child`, `msg` sent to `ua` along
the route `r` (`SendsVia`) with the data `transferByLegacy(caller, to, value)` (`dataT`) and no value, with the gas of EIP-150
(`callGasT`), and:
- if `child` ended with no error, the frame STOPs with no error (`Halted false .empty`);
- otherwise it reverts with no output.
Gas left, state and substate are given exactly (the state and substate after the CALL are those
of `incorporateChild`). -/
theorem spec_depT {c : ByteArray} {r : Route} {c0 cB c10 cU : Bool}
    (h : HypT fork message state substate c r c0 cB c10 cU) {gas : Nat}
    (hg : preCostT fork c0 cB c10 cU + 100 + callRT substate state message r ≤ gas)
    (htail : 51 ≤ gas - preCostT fork c0 cB c10 cU - (callGasT fork gas c0 cB c10 cU (callRT substate state message r)).cost)
    {callee : Evm fork Nat → Message fork → Evm fork Nat → Prop} :
    SpecUnder fork callee (At CODE message 0 [] .empty gas state substate)
      fun evm => ∃ caller msg child, callee caller msg child ∧
        SendsVia message (upAddr state message) c r (dataT message) msg ∧
        msg.gas = (callGasT fork gas c0 cB c10 cU (callRT substate state message r)).subCall ∧
        caller.state = (routeState ((callStateT state message).recordAccountRead
          (upAddr state message)) r).recordAccountRead message.currentTarget ∧
        caller.substate = routeSub { callSubT substate state message with
          accessedAddresses :=
            (callSubT substate state message).accessedAddresses.insert (upAddr state message) } r ∧
        (child.error = none →
          Halted false .empty
            (gas - preCostT fork c0 cB c10 cU - (callGasT fork gas c0 cB c10 cU (callRT substate state message r)).cost + child.gas - 51)
            (incorporateChild fork caller child).state
            (incorporateChild fork caller child).substate evm) ∧
        (child.error ≠ none →
          Halted true .empty
            (gas - preCostT fork c0 cB c10 cU - (callGasT fork gas c0 cB c10 cU (callRT substate state message r)).cost + child.gas - 25)
            (incorporateChild fork caller child).state
            (incorporateChild fork caller child).substate evm) := by
  apply Sends.SpecOn.toUnder
  apply spec_depT_g
  all_goals first | assumption | (intro _ _ _ _ _; omega)

/-- A callee assumption under which the call succeeds: every message sent to `ua` (code `c`) along
the route `r` with the data `d` ends with no error. -/
def SucceedsD (message : Message fork) (ua : EthLib.Base.Address) (c : ByteArray) (r : Route)
    (d : ByteArray)
    (callee : Evm fork Nat → Message fork → Evm fork Nat → Prop) : Prop :=
  ∀ caller msg child, callee caller msg child → SendsVia message ua c r d msg → child.error = none

/-- A callee assumption under which the call fails: every message sent to `ua` (code `c`) along
the route `r` with the data `d` ends with an error. -/
def FailsD (message : Message fork) (ua : EthLib.Base.Address) (c : ByteArray) (r : Route)
    (d : ByteArray)
    (callee : Evm fork Nat → Message fork → Evm fork Nat → Prop) : Prop :=
  ∀ caller msg child, callee caller msg child → SendsVia message ua c r d msg → child.error ≠ none

/-- `transfer(to, value)` when deprecated, for a callee that succeeds on the forwarded call: the
run STOPs with no error, after a message `msg` sent to `ua` with the data `dataT` that ended in
`child`; the state and substate are those of `incorporateChild` of `child`. -/
theorem spec_depT_succeeds {c : ByteArray} {r : Route} {c0 cB c10 cU : Bool}
    (h : HypT fork message state substate c r c0 cB c10 cU) {gas : Nat}
    (hg : preCostT fork c0 cB c10 cU + 100 + callRT substate state message r ≤ gas)
    (htail : 51 ≤ gas - preCostT fork c0 cB c10 cU - (callGasT fork gas c0 cB c10 cU (callRT substate state message r)).cost)
    {callee : Evm fork Nat → Message fork → Evm fork Nat → Prop}
    (hok : SucceedsD message (upAddr state message) c r (dataT message) callee) :
    SpecUnder fork callee (At CODE message 0 [] .empty gas state substate)
      fun evm => ∃ caller msg child, callee caller msg child ∧
        SendsVia message (upAddr state message) c r (dataT message) msg ∧ child.error = none ∧
        Halted false .empty
          (gas - preCostT fork c0 cB c10 cU - (callGasT fork gas c0 cB c10 cU (callRT substate state message r)).cost + child.gas - 51)
          (incorporateChild fork caller child).state
          (incorporateChild fork caller child).substate evm := by
  refine (spec_depT h hg htail).consequence (fun _ h => h) ?_
  rintro evm ⟨caller, msg, child, hcal, hfwd, -, -, -, hstop, -⟩
  have he := hok caller msg child hcal hfwd
  exact ⟨caller, msg, child, hcal, hfwd, he, hstop he⟩

/-- `transfer(to, value)` when deprecated, for a callee that fails on the forwarded call: the run
reverts with no output (the callee's revert data is not forwarded). -/
theorem spec_depT_fails {c : ByteArray} {r : Route} {c0 cB c10 cU : Bool}
    (h : HypT fork message state substate c r c0 cB c10 cU) {gas : Nat}
    (hg : preCostT fork c0 cB c10 cU + 100 + callRT substate state message r ≤ gas)
    (htail : 51 ≤ gas - preCostT fork c0 cB c10 cU - (callGasT fork gas c0 cB c10 cU (callRT substate state message r)).cost)
    {callee : Evm fork Nat → Message fork → Evm fork Nat → Prop}
    (hfail : FailsD message (upAddr state message) c r (dataT message) callee) :
    SpecUnder fork callee (At CODE message 0 [] .empty gas state substate)
      fun evm => evm.error = some .revert ∧ evm.output = .empty := by
  refine (spec_depT h hg htail).consequence (fun _ h => h) ?_
  rintro evm ⟨caller, msg, child, hcal, hfwd, -, -, -, -, hko⟩
  obtain ⟨-, herr, hevm, -⟩ := hko (hfail caller msg child hcal hfwd)
  exact ⟨by simpa using herr, hevm⟩

/-- EthLib's `RunsAs (routeCode c r) G Q` succeeds on the messages sent with data `d` when every stopped frame of
`Q` has no error, those messages meet `G`, and `ua` is no precompile. -/
theorem succeedsD_runsAs {ua : EthLib.Base.Address} {c d : ByteArray} {r : Route}
    {G : Message fork → State.TransactionState → Substate → Prop}
    {Q : Message fork → State.TransactionState → Substate → Evm fork Nat → Prop}
    (hQ : ∀ msg st ss stopped, Q msg st ss stopped → stopped.error = none)
    (hG : ∀ msg st ss, SendsVia message ua c r d msg → G msg st ss)
    (hpre : Precompiles.isPrecompile fork (routeAddr ua r).toU256.toNat = false) :
    SucceedsD message ua c r d (RunsAs (routeCode c r) G Q) := by
  intro caller msg child hrun hfwd'
  have ⟨_, _, hmt, hmca, hmc, _, _, hmv, _, _⟩ := hfwd'
  obtain ⟨stopped, hq, hchild⟩ := hrun hmc (by simp [hmt]) (by simp [hmv])
    (by simp [precompileAddress, hmca, hpre]) (hG _ _ _ hfwd')
  have he := hQ _ _ _ _ hq
  rw [hchild, rollbackOnError_of_error_eq_none he]
  exact he

/-- `transfer(to, value)` when deprecated, run by the interpreter's own message runner
(`processRunner`, which runs the callee's code): for every upgraded code `c` with a specification
(as EthLib's `meets_of_spec` takes it) whose stopped frames end with no error, the run of the
interpreter loop STOPs with no error after the forwarded call (state and substate from
`incorporateChild`), or the runner aborts. -/
theorem runFrame_depT_process {c : ByteArray} {r : Route} {c0 cB c10 cU : Bool}
    (h : HypT fork message state substate c r c0 cB c10 cU)
    (hpre : Precompiles.isPrecompile fork (routeAddr (upAddr state message) r).toU256.toNat = false)
    {gas : Nat} (hg : preCostT fork c0 cB c10 cU + 100 + callRT substate state message r ≤ gas)
    (htail : 51 ≤ gas - preCostT fork c0 cB c10 cU - (callGasT fork gas c0 cB c10 cU (callRT substate state message r)).cost)
    {G : Message fork → State.TransactionState → Substate → Prop}
    {Q : Message fork → State.TransactionState → Substate → Evm fork Nat → Prop}
    (hspec : ∀ msg st ss, msg.code = routeCode c r → G msg st ss →
      Spec fork (At (routeCode c r) msg 0 [] .empty msg.gas (startState fork msg st) ss)
        (Q msg st ss))
    (hG : ∀ msg st ss, SendsVia message (upAddr state message) c r (dataT message) msg → G msg st ss)
    (hQ : ∀ msg st ss stopped, Q msg st ss stopped → stopped.error = none)
    {bound : Nat} {evm : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    (∃ stopped, runFrame (step fork) (step_decreases fork) bound (processRunner fork bound) evm
        within = .ok stopped ∧ ∃ caller msg child, RunsAs (routeCode c r) G Q caller msg child ∧
        SendsVia message (upAddr state message) c r (dataT message) msg ∧ child.error = none ∧
        Halted false .empty
          (gas - preCostT fork c0 cB c10 cU - (callGasT fork gas c0 cB c10 cU (callRT substate state message r)).cost + child.gas - 51)
          (incorporateChild fork caller child).state
          (incorporateChild fork caller child).substate stopped) ∨
    ∃ e, runFrame (step fork) (step_decreases fork) bound (processRunner fork bound) evm
        within = .error e ∧ e.aborts = true :=
  (spec_depT_succeeds h hg htail (succeedsD_runsAs hQ hG hpre)).runFrame
    (meets_of_spec hspec bound) start within

/-- The specification of `transfer(to, value)` when deprecated and the upgraded address has no
code (empty code in the state): the run reverts with no output before any call, after the reads of
slots 0, `isBlackListed[caller]`, 10 and of the upgraded account.
Gas `1354 + the three slot prices + price(upgraded address)`. -/
theorem spec_depTNoCode (hfork : .berlin ≤ fork)
    (hsize : 4 ≤ message.data.size) (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0xa9059cbb) (hv : message.value = 0)
    (hnp : byte20 (storageAt state message.currentTarget 0) = 0)
    (hnb : (storageAt state message.currentTarget (blackSlot message)).toNat % 256 = 0)
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0)
    (hcode : state.getCode (state.getAccount (upAddr state message)).codeHash = .ok .empty)
    {c0 cB c10 cU : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hcB : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget
      (blackSlot message) = cB)
    (hc10 : coldIn (accessSlot (accessSlot substate message.currentTarget 0) message.currentTarget
      (blackSlot message)) message.currentTarget 10 = c10)
    (hcU : decide (upAddr state message ∉ substate.accessedAddresses) = cU)
    {gas : Nat} (hg : 1354 + slotCost c0 + slotCost cB + slotCost c10 + extCost fork cU ≤ gas) :
    Spec fork (At CODE message 0 [] .empty gas state substate)
      (Halted true .empty (gas - (1354 + slotCost c0 + slotCost cB + slotCost c10 + extCost fork cU))
        (callStateT state message) (callSubT substate state message)) := by
  simp only [extCost] at hg ⊢
  have ht : tested (BitVec.ofNat 256 (selector message.data)) ENTRIES = 22 := by
    rw [hsel]; decide
  have hb : branch (BitVec.ofNat 256 (selector message.data)) 54 (entrySize 4 2) ENTRIES =
      1866 := by
    rw [hsel]; decide
  have h1 := dispatch (state := state) (substate := substate) hsize hsize' (gas := gas)
    (by rw [ht]; gas_ok)
  rw [ht, hb] at h1
  refine Gas.Triple.seqL h1 ?_
  step entry hv (by gas_ok)
  step notPaused hfork (by simp) hnp hc0 (by gas_ok)
  step blackLookup hfork (by simp) hcB (by gas_ok)
  step jumpiR (blackTest_ne (by rw [storageAt_readSlot]; exact hnb))
  step repcH (pc' := 5481) (by decide)
  step depSetW hfork (Or.inl ⟨rfl, rfl⟩) (by simp)
    (by rw [storageAt_readSlot, storageAt_readSlot]; exact hdep) hc10 (by gas_ok)
  step upLoad (state := readSlot (readSlot state message.currentTarget 0) message.currentTarget
    (blackSlot message)) hfork (Or.inl ⟨rfl, rfl⟩) (by simp) (by gas_ok)
  rw [storageAt_readSlot, storageAt_readSlot]
  step pushR 4 (0x6e18980a : U256)
  step Logic.caller (by code_fact) (by code_fact) (by gas_ok) (by stk_ok)
  step dupR 4
  step dupR 4
  step encode3 (Or.inl ⟨rfl, rfl⟩) (size_MEMK _ _) (ptr_MEMK _ _)
    (rest := [wordArg message.data 1, addrArg message.data 0, 0x078a,
      BitVec.ofNat 256 (selector message.data)]) (by simp) (by gas_ok)
  step Logic.reshape (g' := gas - (1329 + slotCost c0 + slotCost cB + slotCost c10)) rfl rfl (by gas_ok)
  refine (noCode (gas := gas - (1329 + slotCost c0 + slotCost cB + slotCost c10))
    (st := shortState state message) (ss := shortSubstate substate message) (message := message)
    (M := memT message)
    (rest := [upWord (storageAt state message.currentTarget 10), 0, 0x60, 0x64, 0x60, 0, 0xc4,
      0x6e18980a, upWord (storageAt state message.currentTarget 10), wordArg message.data 1,
      addrArg message.data 0, 0x078a, BitVec.ofNat 256 (selector message.data)])
    hfork (Or.inr (Or.inr (Or.inl rfl))) (by simp) hcode hcU
    (by simp only [extCost]; gas_ok)).consequence (fun _ h => h) ?_
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  exact ⟨hr, he, ho, by rw [hgas]; simp only [extCost]; gas_ok, hs, hss⟩

/-! ## approve -/

/-- After a call that succeeded (flag 1), from 3231: the code drops the call operands, returns
to 674 and stops. -/
theorem okTailA {sel U v s x : U256} {M : ByteArray} {gas : Nat} (hg : 53 ≤ gas) :
    Spec fork (At CODE message 3231 [1, 0xc4, sel, U, 0x40, v, s, 0x02a2, x] M gas state
        substate)
      (Halted false .empty (gas - 53) state substate) := by
  step unR 0x15 instruction_iszero
  step unR 0x15 instruction_iszero
  step pushR 2 (0x0ca9 : U256)
  step jumpiR (by decide)
  step jumpdestR
  step popR
  step popR
  step popR
  step pushR 2 (0x0cbc : U256)
  step jumpR
  at_pc 3260
  step jumpdestR
  step popR
  step popR
  step popR
  step jumpR
  step repcH (pc' := 674) (by decide)
  step jumpdestR
  refine (Logic.stop (by code_fact) (by code_fact)).consequence (fun _ h => h) ?_
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  exact ⟨hr, he, ho, by rw [hgas]; gas_ok, hs, hss⟩

/-- The selector of `approveByLegacy(address,address,uint256)`. -/
def SEL_A : ByteArray := ⟨#[0xae, 0xe9, 0x2d, 0x33]⟩

theorem sel_A : (wordBytes (selWord 0xaee92d33)).extract 0 4 = SEL_A := by decide +kernel

/-- The call data that `approve` forwards when deprecated:
`approveByLegacy(msg.sender, _spender, _value)`, i.e. the selector 0xaee92d33, then the caller,
`_spender` (argument word 0 masked to 160 bits) and `_value` (argument word 1) as words. -/
abbrev dataA (message : Message fork) : ByteArray :=
  SEL_A ++ wordBytes (callerKey message) ++ wordBytes (addrArg message.data 0) ++
    wordBytes (wordArg message.data 1)

/-- The memory before the CALL of the deprecated `approve`. -/
abbrev memA (message : Message fork) : ByteArray :=
  W4 MEM0 0xaee92d33 (mkey message.caller.toU256) (mkey (addrArg message.data 0))
    (wordArg message.data 1)

theorem data_memA (message : Message fork) :
    memoryReadBytes (memoryExtend (memA message) 0) 96 100 = dataA message := by
  rw [memoryExtend_zero, memA, data_W4 size_MEM0, sel_A, TransferOk.mkey_addrArg]

/-- The gas of the path from pc 0 to the CALL, for `approve`. -/
abbrev preCostA (fork : Fork) (c10 cU : Bool) : Nat := 724 + slotCost c10 + extCost fork cU

/-- The gas that the code asks CALL to pass on, for a frame that starts with `gas`. -/
abbrev askedOfA (fork : Fork) (gas : Nat) (c10 cU : Bool) : U256 :=
  asked (gas - (721 + slotCost c10 + extCost fork cU))

/-- What CALL pays and passes on, for `approve`. -/
abbrev callGasA (fork : Fork) (gas : Nat) (c10 cU : Bool) (R : Nat) :
    MessageCallGas :=
  messageCallGas fork 0 (askedOfA fork gas c10 cU).toNat (gas - preCostA fork c10 cU) 0 (100 + R)

/-- The hypotheses shared by the deprecated `approve` theorems, besides the gas: as `HypT` with
the selector 0x095ea7b3, at least 68 bytes of call data, and no paused or blacklist check (the
bytecode of `approve` has none); `c10`, `cU` are whether slot 10 and `ua` are cold. -/
structure HypA (fork : Fork) (message : Message fork) (state : State.TransactionState)
    (substate : Substate) (c : ByteArray) (r : Route) (c10 cU : Bool) : Prop where
  berlin : .berlin ≤ fork
  size : 68 ≤ message.data.size
  size' : message.data.size < 2 ^ 256
  sel : selector message.data = 0x095ea7b3
  value : message.value = 0
  deprecated : byte20 (storageAt state message.currentTarget 10) ≠ 0
  code : state.getCode (state.getAccount (upAddr state message)).codeHash = .ok c
  codeSize : 0 < c.size
  codeSize' : c.size < 2 ^ 256
  route : Routes fork state c r
  depth : message.depth + 1 ≤ STACK_DEPTH_LIMIT
  cold10 : coldIn substate message.currentTarget 10 = c10
  coldU : decide (upAddr state message ∉ substate.accessedAddresses) = cU

/-- From pc 0 to the EXTCODESIZE at 3213, for a deprecated `approve`. -/
theorem preExtA (hfork : .berlin ≤ fork) (hlong : 68 ≤ message.data.size)
    (hsz : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x095ea7b3)
    (hv : message.value = 0) (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0)
    {c10 : Bool} (hc10 : coldIn substate message.currentTarget 10 = c10) {gas : Nat}
    (hg : 696 + slotCost c10 ≤ gas) :
    Hoare fork (At CODE message 0 [] .empty gas state substate)
      (At CODE message 3213
        [upWord (storageAt state message.currentTarget 10),
          upWord (storageAt state message.currentTarget 10), 0, 0x60, 0x64, 0x60, 0, 0xc4,
          0xaee92d33, upWord (storageAt state message.currentTarget 10), 0x40,
          wordArg message.data 1, addrArg message.data 0, 0x02a2,
          BitVec.ofNat 256 (selector message.data)]
        (memA message) (gas - (696 + slotCost c10)) (readSlot state message.currentTarget 10)
        (accessSlot substate message.currentTarget 10)) := by
  have ht : tested (BitVec.ofNat 256 (selector message.data)) ENTRIES = 3 := by
    rw [hsel]; decide
  have hb : branch (BitVec.ofNat 256 (selector message.data)) 54 (entrySize 4 2) ENTRIES =
      610 := by
    rw [hsel]; decide
  have h1 := dispatch (state := state) (substate := substate) (by omega) hsz (gas := gas)
    (by rw [ht]; gas_ok)
  rw [ht, hb] at h1
  refine Gas.Triple.seqL h1 ?_
  step Approve.entry hv (by gas_ok)
  step Approve.payload (Or.inl ⟨rfl, rfl⟩) hlong hsz (by simp) (by gas_ok)
  step depSetW hfork (Or.inr (Or.inl ⟨rfl, rfl⟩)) (by simp) hdep hc10 (by gas_ok)
  step upLoad hfork (Or.inr (Or.inl ⟨rfl, rfl⟩)) (by simp) (by gas_ok)
  step pushR 4 (0xaee92d33 : U256)
  step Logic.caller (by code_fact) (by code_fact) (by gas_ok) (by stk_ok)
  step dupR 5
  step dupR 5
  step encode3 (Or.inr ⟨rfl, rfl⟩) size_MEM0 mload_MEM0
    (rest := [0x40, wordArg message.data 1, addrArg message.data 0, 0x02a2,
      BitVec.ofNat 256 (selector message.data)]) (by simp) (by gas_ok)
  exact Logic.reshape rfl rfl (by gas_ok)

/-- `spec_depA` with the bound `htail` (at least 53 gas left after the price of the CALL) replaced by
`hcg`: every ended forwarded message that meets `callee` leaves at least 53 gas for the code after
the CALL, the gas the CALL keeps plus the gas left in the ended frame.
Stated as a `Sends.SpecOn` (round 26): the frames that end the runner's messages meet
`callee`, the runner may fail with any error, and the run ends as stated or at a failure of the
runner on a forwarded message (`SendsVia`); `.toUnder` gives EthLib's `SpecUnder`. -/
theorem spec_depA_g {c : ByteArray} {r : Route} {c10 cU : Bool}
    (h : HypA fork message state substate c r c10 cU) {gas : Nat}
    (hg : preCostA fork c10 cU + 100 + callR substate state message r ≤ gas)
    {callee : Evm fork Nat → Message fork → Evm fork Nat → Prop}
    (hcg : ∀ caller msg child, callee caller msg child →
      SendsVia message (upAddr state message) c r (dataA message) msg →
      53 ≤ gas - preCostA fork c10 cU - (callGasA fork gas c10 cU (callR substate state message r)).cost + child.gas) :
    Sends.SpecOn fork callee (SendsVia message (upAddr state message) c r (dataA message))
      (At CODE message 0 [] .empty gas state substate)
      fun evm => ∃ caller msg child, callee caller msg child ∧
        SendsVia message (upAddr state message) c r (dataA message) msg ∧
        msg.gas = (callGasA fork gas c10 cU (callR substate state message r)).subCall ∧
        caller.state = (routeState ((callState state message).recordAccountRead
          (upAddr state message)) r).recordAccountRead message.currentTarget ∧
        caller.substate = routeSub { callSub substate state message with
          accessedAddresses :=
            (callSub substate state message).accessedAddresses.insert (upAddr state message) } r ∧
        (child.error = none →
          Halted false .empty
            (gas - preCostA fork c10 cU - (callGasA fork gas c10 cU (callR substate state message r)).cost + child.gas - 53)
            (incorporateChild fork caller child).state
            (incorporateChild fork caller child).substate evm) ∧
        (child.error ≠ none →
          Halted true .empty
            (gas - preCostA fork c10 cU - (callGasA fork gas c10 cU (callR substate state message r)).cost + child.gas - 25)
            (incorporateChild fork caller child).state
            (incorporateChild fork caller child).substate evm) := by
  have hext : extendMemory (memA message).size
      [((0x60 : U256), (0x64 : U256)), ((0x60 : U256), (0 : U256))] = ⟨0, 0⟩ := by
    rw [memA, size_W4 size_MEM0]; decide
  have hpre : Hoare fork (At CODE message 0 [] .empty gas state substate)
      (At CODE message 3230
        [askedOfA fork gas c10 cU, upWord (storageAt state message.currentTarget 10), 0, 0x60, 0x64,
          0x60, 0, 0xc4, 0xaee92d33, upWord (storageAt state message.currentTarget 10), 0x40,
          wordArg message.data 1, addrArg message.data 0, 0x02a2,
          BitVec.ofNat 256 (selector message.data)]
        (memA message) (gas - preCostA fork c10 cU) (callState state message)
        (callSub substate state message)) := by
    simp only [preCostA, askedOfA, extCost] at hg ⊢
    refine (preExtA h.berlin h.size h.size' h.sel h.value h.deprecated h.cold10
      (by gas_ok)).seq ?_
    refine (toCall (gas := gas - (696 + slotCost c10))
      (st := readSlot state message.currentTarget 10)
      (ss := accessSlot substate message.currentTarget 10) (message := message)
      (M := memA message)
      (rest := [upWord (storageAt state message.currentTarget 10), 0, 0x60, 0x64, 0x60, 0, 0xc4,
        0xaee92d33, upWord (storageAt state message.currentTarget 10), 0x40,
        wordArg message.data 1, addrArg message.data 0, 0x02a2,
        BitVec.ofNat 256 (selector message.data)])
      h.berlin (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))) (by simp) h.code
      h.codeSize h.codeSize' h.coldU (by simp only [extCost]; gas_ok)).seq ?_
    refine Logic.reshape ?_ rfl (by simp only [extCost]; gas_ok)
    simp only [List.cons.injEq, and_true]
    exact congrArg asked (by unfold extCost; omega)
  have hR : routeCost fork ((callSub substate state message).accessedAddresses.insert
      (toAddressMasked (upWord (storageAt state message.currentTarget 10)))) r =
      callR substate state message r := routeCost_insert_insert _ _ _
  have hcall := Complete.callWithRS (fork := fork) (code := CODE) (message := message) (pc := 3230)
    (memory := memA message) (gas := gas - preCostA fork c10 cU)
    (state := callState state message)
    (substate := callSub substate state message) (callee := callee)
    (asked := askedOfA fork gas c10 cU) (to := upWord (storageAt state message.currentTarget 10))
    (i := 0x60) (isz := 0x64) (o := 0x60) (osz := 0)
    (rest := [0xc4, 0xaee92d33, upWord (storageAt state message.currentTarget 10), 0x40,
      wordArg message.data 1, addrArg message.data 0, 0x02a2,
      BitVec.ofNat 256 (selector message.data)]) (cold := false)
    h.berlin (by code_fact) (by code_fact) h.code (routes_congr (fun _ => rfl) h.route) h.depth
    (by simp [upAddr]) (by rw [hext, hR]; simp only [accCost_false]; omega)
  rw [hext, hR] at hcall
  simp only [accCost_false] at hcall
  have hcall := hcall.mono_S (S' := SendsVia message (upAddr state message) c r (dataA message)) fun _ h => by
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ := h
    exact ⟨a1, a2, a3, a4, a5, a6, by rw [a7]; exact data_memA message, a8, a9, a10⟩
  refine Sends.SpecOn.seq (Sends.HoareOn.of_hoare hpre) (Sends.HoareOn.seq hcall (Sends.HoareOn.of_hoare ?_))
  rintro evm ⟨caller, msg, child, hcal, -, hcs, hcss, hmg, hmc, hmt, hmtg, hmca, hmcode, hmdp, hmd, hmv,
    hmdep, hmst, hat⟩
  have hfwd : SendsVia message (upAddr state message) c r (dataA message) msg := by
    refine ⟨hmc, hmt, hmtg, hmca, hmcode, hmdp, ?_, hmv, hmdep, hmst⟩
    rw [hmd]; exact data_memA message
  have hT := hcg caller msg child hcal hfwd
  by_cases he : child.error = none
  · simp only [he, Option.isNone_none, ↓reduceIte] at hat
    obtain ⟨after, hreach, hrun, hq⟩ := okTailA (fork := fork) (message := message)
      (state := (incorporateChild fork caller child).state)
      (substate := (incorporateChild fork caller child).substate)
      (gas := gas - preCostA fork c10 cU - ((callGasA fork gas c10 cU (callR substate state message r)).cost + 0) + child.gas)
      (by omega) evm hat
    refine ⟨after, hreach, hrun, caller, msg, child, hcal, hfwd, hmg, hcs, hcss, fun _ => ?_,
      fun h => absurd he h⟩
    obtain ⟨h1, h2, h0, h3, h4, h5⟩ := hq
    exact ⟨h1, h2, h0, by rw [h3]; omega, h4, h5⟩
  · have hz : child.error.isNone = false := by
      cases h : child.error
      · exact absurd h he
      · rfl
    simp only [hz, Bool.false_eq_true, ↓reduceIte] at hat
    obtain ⟨after, hreach, hrun, hq⟩ := failTail (fork := fork) (message := message)
      (state := (incorporateChild fork caller child).state)
      (substate := (incorporateChild fork caller child).substate) h.berlin
      (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
      (rest := [0xc4, 0xaee92d33, upWord (storageAt state message.currentTarget 10), 0x40,
        wordArg message.data 1, addrArg message.data 0, 0x02a2,
        BitVec.ofNat 256 (selector message.data)]) (by simp)
      (gas := gas - preCostA fork c10 cU - ((callGasA fork gas c10 cU (callR substate state message r)).cost + 0) + child.gas)
      (by omega) evm hat
    refine ⟨after, Gas.reaches_toStep hreach, hrun, caller, msg, child, hcal, hfwd, hmg, hcs, hcss,
      fun h => absurd h he, fun _ => ?_⟩
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hq
    exact ⟨h1, h2, h3, by rw [h4]; omega, h5, h6⟩

/-- The specification of `approve(spender, value)` when deprecated, for every callee: as
`spec_depT`, with the data `approveByLegacy(caller, spender, value)` (`dataA`), the gas of this
path (`preCostA`, `callGasA`, 53 gas after the price of the CALL), and the state and substate
`Deprecated.callState`/`callSub` (slot 10 and `ua` read and accessed) at the CALL. -/
theorem spec_depA {c : ByteArray} {r : Route} {c10 cU : Bool}
    (h : HypA fork message state substate c r c10 cU) {gas : Nat}
    (hg : preCostA fork c10 cU + 100 + callR substate state message r ≤ gas)
    (htail : 53 ≤ gas - preCostA fork c10 cU - (callGasA fork gas c10 cU (callR substate state message r)).cost)
    {callee : Evm fork Nat → Message fork → Evm fork Nat → Prop} :
    SpecUnder fork callee (At CODE message 0 [] .empty gas state substate)
      fun evm => ∃ caller msg child, callee caller msg child ∧
        SendsVia message (upAddr state message) c r (dataA message) msg ∧
        msg.gas = (callGasA fork gas c10 cU (callR substate state message r)).subCall ∧
        caller.state = (routeState ((callState state message).recordAccountRead
          (upAddr state message)) r).recordAccountRead message.currentTarget ∧
        caller.substate = routeSub { callSub substate state message with
          accessedAddresses :=
            (callSub substate state message).accessedAddresses.insert (upAddr state message) } r ∧
        (child.error = none →
          Halted false .empty
            (gas - preCostA fork c10 cU - (callGasA fork gas c10 cU (callR substate state message r)).cost + child.gas - 53)
            (incorporateChild fork caller child).state
            (incorporateChild fork caller child).substate evm) ∧
        (child.error ≠ none →
          Halted true .empty
            (gas - preCostA fork c10 cU - (callGasA fork gas c10 cU (callR substate state message r)).cost + child.gas - 25)
            (incorporateChild fork caller child).state
            (incorporateChild fork caller child).substate evm) := by
  apply Sends.SpecOn.toUnder
  apply spec_depA_g
  all_goals first | assumption | (intro _ _ _ _ _; omega)

/-- `approve(spender, value)` when deprecated, for a callee that succeeds on the forwarded call:
the run STOPs with no error after the call (state and substate from `incorporateChild`). -/
theorem spec_depA_succeeds {c : ByteArray} {r : Route} {c10 cU : Bool}
    (h : HypA fork message state substate c r c10 cU) {gas : Nat}
    (hg : preCostA fork c10 cU + 100 + callR substate state message r ≤ gas)
    (htail : 53 ≤ gas - preCostA fork c10 cU - (callGasA fork gas c10 cU (callR substate state message r)).cost)
    {callee : Evm fork Nat → Message fork → Evm fork Nat → Prop}
    (hok : SucceedsD message (upAddr state message) c r (dataA message) callee) :
    SpecUnder fork callee (At CODE message 0 [] .empty gas state substate)
      fun evm => ∃ caller msg child, callee caller msg child ∧
        SendsVia message (upAddr state message) c r (dataA message) msg ∧ child.error = none ∧
        Halted false .empty
          (gas - preCostA fork c10 cU - (callGasA fork gas c10 cU (callR substate state message r)).cost + child.gas - 53)
          (incorporateChild fork caller child).state
          (incorporateChild fork caller child).substate evm := by
  refine (spec_depA h hg htail).consequence (fun _ h => h) ?_
  rintro evm ⟨caller, msg, child, hcal, hfwd, -, -, -, hstop, -⟩
  have he := hok caller msg child hcal hfwd
  exact ⟨caller, msg, child, hcal, hfwd, he, hstop he⟩

/-- `approve(spender, value)` when deprecated, for a callee that fails on the forwarded call: the
run reverts with no output. -/
theorem spec_depA_fails {c : ByteArray} {r : Route} {c10 cU : Bool}
    (h : HypA fork message state substate c r c10 cU) {gas : Nat}
    (hg : preCostA fork c10 cU + 100 + callR substate state message r ≤ gas)
    (htail : 53 ≤ gas - preCostA fork c10 cU - (callGasA fork gas c10 cU (callR substate state message r)).cost)
    {callee : Evm fork Nat → Message fork → Evm fork Nat → Prop}
    (hfail : FailsD message (upAddr state message) c r (dataA message) callee) :
    SpecUnder fork callee (At CODE message 0 [] .empty gas state substate)
      fun evm => evm.error = some .revert ∧ evm.output = .empty := by
  refine (spec_depA h hg htail).consequence (fun _ h => h) ?_
  rintro evm ⟨caller, msg, child, hcal, hfwd, -, -, -, -, hko⟩
  obtain ⟨-, herr, hevm, -⟩ := hko (hfail caller msg child hcal hfwd)
  exact ⟨by simpa using herr, hevm⟩

/-- `approve(spender, value)` when deprecated, run by the interpreter's own message runner: for
every upgraded code `c` with a specification whose stopped frames end with no error, the run STOPs
with no error after the forwarded call, or the runner aborts. -/
theorem runFrame_depA_process {c : ByteArray} {r : Route} {c10 cU : Bool}
    (h : HypA fork message state substate c r c10 cU)
    (hpre : Precompiles.isPrecompile fork (routeAddr (upAddr state message) r).toU256.toNat = false)
    {gas : Nat} (hg : preCostA fork c10 cU + 100 + callR substate state message r ≤ gas)
    (htail : 53 ≤ gas - preCostA fork c10 cU - (callGasA fork gas c10 cU (callR substate state message r)).cost)
    {G : Message fork → State.TransactionState → Substate → Prop}
    {Q : Message fork → State.TransactionState → Substate → Evm fork Nat → Prop}
    (hspec : ∀ msg st ss, msg.code = routeCode c r → G msg st ss →
      Spec fork (At (routeCode c r) msg 0 [] .empty msg.gas (startState fork msg st) ss)
        (Q msg st ss))
    (hG : ∀ msg st ss, SendsVia message (upAddr state message) c r (dataA message) msg → G msg st ss)
    (hQ : ∀ msg st ss stopped, Q msg st ss stopped → stopped.error = none)
    {bound : Nat} {evm : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    (∃ stopped, runFrame (step fork) (step_decreases fork) bound (processRunner fork bound) evm
        within = .ok stopped ∧ ∃ caller msg child, RunsAs (routeCode c r) G Q caller msg child ∧
        SendsVia message (upAddr state message) c r (dataA message) msg ∧ child.error = none ∧
        Halted false .empty
          (gas - preCostA fork c10 cU - (callGasA fork gas c10 cU (callR substate state message r)).cost + child.gas - 53)
          (incorporateChild fork caller child).state
          (incorporateChild fork caller child).substate stopped) ∨
    ∃ e, runFrame (step fork) (step_decreases fork) bound (processRunner fork bound) evm
        within = .error e ∧ e.aborts = true :=
  (spec_depA_succeeds h hg htail (succeedsD_runsAs hQ hG hpre)).runFrame
    (meets_of_spec hspec bound) start within

/-- The specification of `approve(spender, value)` when deprecated and the upgraded address has no
code: the run reverts with no output before any call. Gas `721 + price(slot 10) + price(ua)`. -/
theorem spec_depANoCode (hfork : .berlin ≤ fork)
    (hlong : 68 ≤ message.data.size) (hsz : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x095ea7b3) (hv : message.value = 0)
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0)
    (hcode : state.getCode (state.getAccount (upAddr state message)).codeHash = .ok .empty)
    {c10 cU : Bool} (hc10 : coldIn substate message.currentTarget 10 = c10)
    (hcU : decide (upAddr state message ∉ substate.accessedAddresses) = cU)
    {gas : Nat} (hg : 721 + slotCost c10 + extCost fork cU ≤ gas) :
    Spec fork (At CODE message 0 [] .empty gas state substate)
      (Halted true .empty (gas - (721 + slotCost c10 + extCost fork cU)) (callState state message)
        (callSub substate state message)) := by
  simp only [extCost] at hg ⊢
  refine (preExtA hfork hlong hsz hsel hv hdep hc10 (by gas_ok)).seq ?_
  refine (noCode (gas := gas - (696 + slotCost c10))
    (st := readSlot state message.currentTarget 10)
    (ss := accessSlot substate message.currentTarget 10) (message := message)
    (M := memA message)
    (rest := [upWord (storageAt state message.currentTarget 10), 0, 0x60, 0x64, 0x60, 0, 0xc4,
      0xaee92d33, upWord (storageAt state message.currentTarget 10), 0x40,
      wordArg message.data 1, addrArg message.data 0, 0x02a2,
      BitVec.ofNat 256 (selector message.data)])
    hfork (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) (by simp) hcode hcU
    (by simp only [extCost]; gas_ok)).consequence (fun _ h => h) ?_
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  exact ⟨hr, he, ho, by rw [hgas]; simp only [extCost]; gas_ok, hs, hss⟩

end UsdtVerify.DeprecatedTransfer
