import UsdtVerify.Functions.DeprecatedTransfer
import UsdtVerify.Functions.TransferFromFault

/-!
# transferFrom(from, to, value) when deprecated: the forward to the upgraded contract

Selector 0x23b872dd, no value, not paused, `_from` not blacklisted, byte 20 of slot 10 set.
TetherToken then calls `transferFromByLegacy(msg.sender, _from, _to, _value)` (selector
0x8b477adb).

- 819 (entry), 3773 (paused check), 3801 (blacklist of `_from`): the blocks of `TransferFrom`.
- 3890 (`depSetW`), 3912 (`upLoad`), 3969: selector, caller, `_from`, `_to`, `_value`.
- 3978 (`encode4`): the call data at 0x60, 132 bytes (memory grows from 96 to 256 bytes).
- 4200 (EXTCODESIZE), CALL at 4217 with input 132 bytes at 0x60 and no output range; 4218: revert
  on failure, else back to 914 and STOP.

No payload check: StandardToken's `onlyPayloadSize(3 * 32)` is not on this path.
-/

namespace UsdtVerify.DeprecatedTransferFrom

open EthLib.Base (Fork U256 toAddressMasked)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts
open Deprecated DeprecatedBalance DeprecatedTransfer TransferOk TransferFrom

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate}

/-- The memory with a fifth word `w` at 0xc4 (256 bytes). -/
def W5 (M : ByteArray) (sel k f t w : U256) : ByteArray :=
  memoryWrite (memoryExtend (W4 M sel k f t) 32) 196 (wordBytes w)

section Sizes

variable {M : ByteArray} (hM : M.size = 96) {sel k f t w : U256}
include hM

theorem size_W5 : (W5 M sel k f t w).size = 256 := by
  rw [W5, size_memoryWrite (by rw [size_wordBytes, size_memoryExtend, size_W4 hM]; omega),
    size_memoryExtend, size_W4 hM]

theorem read40_W5 : memoryReadBytes (W5 M sel k f t w) 64 32 = memoryReadBytes M 64 32 := by
  rw [W5, memoryReadBytes_memoryWrite_of_disjoint
      (by rw [size_wordBytes, size_memoryExtend, size_W4 hM]; omega) (.inl (by decide)),
    read_ext (by rw [size_W4 hM]; omega), read40_W4 hM]

theorem data_W5 : memoryReadBytes (W5 M sel k f t w) 96 132 =
    (wordBytes (selWord sel)).extract 0 4 ++ wordBytes k ++ wordBytes f ++ wordBytes t ++
      wordBytes w := by
  have h5 := memoryReadBytes_memoryWrite_eq_append
    (memory := memoryExtend (W4 M sel k f t) 32)
    (value := wordBytes w) (s := 96) (k := 100)
    (by rw [size_wordBytes, size_memoryExtend, size_W4 hM]; omega)
  rw [size_wordBytes] at h5
  rw [W5, h5, read_ext (by rw [size_W4 hM]; omega), data_W4 hM]

end Sizes

/-- From 3978, with the stack `w, t, f, C, sel, U` on top: the code writes at 0x60 the selector
word of `sel`, then the words `C`, `f`, `t` (masked to 160 bits) and `w`, and pushes the operands
of CALL down to the EXTCODESIZE at 4200: input 0x84 bytes at 0x60, output 0 bytes at 0x60. -/
theorem encode4 {M : ByteArray} (hM : M.size = 96)
    (hptr : loadWord (memoryReadBytes M 64 32) 0 32 = 0x60)
    {w t f C sel U : U256} {rest : List U256} (hrest : rest.length ≤ 16) {gas : Nat}
    (hg : 192 ≤ gas) :
    Gas.HoareG fork (At CODE message 3978 ([w, t, f, C, sel, U] ++ rest) M gas state substate)
      (At CODE message 4200 ([U, U, 0, 0x60, 0x84, 0x60, 0, 0xe4, sel, U] ++ rest)
        (W5 M sel (mkey C) (mkey f) (mkey t) w) (gas - 192) state substate) := by
  have hx0 : extendMemory M.size [((0x40 : U256), (32 : U256))] = ⟨0, 0⟩ := by
    rw [hM]; decide
  have hx1 : extendMemory M.size [((0x60 : U256), (32 : U256))] = ⟨3, 32⟩ := by
    rw [hM]; decide
  have hx2 : extendMemory (W1 M sel).size [((0x64 : U256), (32 : U256))] = ⟨3, 32⟩ := by
    rw [size_W1 hM]; decide
  have hx3 : extendMemory (W2 M sel (mkey C)).size [((0x84 : U256), (32 : U256))] = ⟨3, 32⟩ := by
    rw [size_W2 hM]; decide
  have hx4 : extendMemory (W3 M sel (mkey C) (mkey f)).size [((0xa4 : U256), (32 : U256))] =
      ⟨3, 32⟩ := by
    rw [size_W3 hM]; decide
  have hx5 : extendMemory (W4 M sel (mkey C) (mkey f) (mkey t)).size
      [((0xc4 : U256), (32 : U256))] = ⟨3, 32⟩ := by
    rw [size_W4 hM]; decide
  have hx6 : extendMemory (W5 M sel (mkey C) (mkey f) (mkey t) w).size
      [((0x40 : U256), (32 : U256))] = ⟨0, 0⟩ := by
    rw [size_W5 hM]; decide
  have h64 : add (0x04 : U256) (0x60 : U256) = 0x64 := by decide
  have h84 : add (0x20 : U256) (0x64 : U256) = 0x84 := by decide
  have ha4 : add (0x20 : U256) (0x84 : U256) = 0xa4 := by decide
  have hc4 : add (0x20 : U256) (0xa4 : U256) = 0xc4 := by decide
  have he4 : add (0x20 : U256) (0xc4 : U256) = 0xe4 := by decide
  have hs4 : sub (0xe4 : U256) (0x60 : U256) = 0x84 := by decide
  step pushR 1 (0x40 : U256)
  step Gas.mloadG (by code_fact) (by code_fact) (by rw [hx0]; gas_ok)
  step Gas.reshapeG (s' := [0x60, w, t, f, C, sel, U] ++ rest) (m' := M) (g' := gas - 6)
    (by rw [hx0, memoryExtend_zero, show (0x40 : U256).toNat = 64 from rfl, hptr]; rfl)
    (by rw [hx0, memoryExtend_zero]) (by rw [hx0]; gas_ok)
  step dupR 5
  step pushR 4 (0xffffffff : U256)
  step binR 0x16 Local.instruction_and
  step pushR 29 (0x0100000000000000000000000000000000000000000000000000000000 : U256)
  step binR 0x02 Local.instruction_mul
  step dupR 1
  step Gas.mstoreG (by code_fact) (by code_fact) (by rw [hx1]; gas_ok)
  step Gas.reshapeG (s' := [0x60, w, t, f, C, sel, U] ++ rest) (m' := W1 M sel) (g' := gas - 32) rfl
    (by rw [hx1]; rfl) (by rw [hx1]; gas_ok)
  step pushR 1 (0x04 : U256)
  step binR 0x01 instruction_add
  rw [h64]
  step dupR 0
  step dupR 5
  step pushR 20 ADDR_MASK
  step binR 0x16 Local.instruction_and
  step pushR 20 ADDR_MASK
  step binR 0x16 Local.instruction_and
  step dupR 1
  step Gas.mstoreG (by code_fact) (by code_fact) (by rw [hx2]; gas_ok)
  step Gas.reshapeG (s' := [0x64, 0x64, w, t, f, C, sel, U] ++ rest) (m' := W2 M sel (mkey C))
    (g' := gas - 65) rfl (by rw [hx2]; rfl) (by rw [hx2]; gas_ok)
  step pushR 1 (0x20 : U256)
  step binR 0x01 instruction_add
  rw [h84]
  step dupR 4
  step pushR 20 ADDR_MASK
  step binR 0x16 Local.instruction_and
  step pushR 20 ADDR_MASK
  step binR 0x16 Local.instruction_and
  step dupR 1
  step Gas.mstoreG (by code_fact) (by code_fact) (by rw [hx3]; gas_ok)
  step Gas.reshapeG (s' := [0x84, 0x64, w, t, f, C, sel, U] ++ rest)
    (m' := W3 M sel (mkey C) (mkey f)) (g' := gas - 95) rfl (by rw [hx3]; rfl)
    (by rw [hx3]; gas_ok)
  at_pc 4122
  step pushR 1 (0x20 : U256)
  step binR 0x01 instruction_add
  rw [ha4]
  step dupR 3
  step pushR 20 ADDR_MASK
  step binR 0x16 Local.instruction_and
  step pushR 20 ADDR_MASK
  step binR 0x16 Local.instruction_and
  step dupR 1
  step Gas.mstoreG (by code_fact) (by code_fact) (by rw [hx4]; gas_ok)
  step Gas.reshapeG (s' := [0xa4, 0x64, w, t, f, C, sel, U] ++ rest)
    (m' := W4 M sel (mkey C) (mkey f) (mkey t)) (g' := gas - 125) rfl (by rw [hx4]; rfl)
    (by rw [hx4]; gas_ok)
  step pushR 1 (0x20 : U256)
  step binR 0x01 instruction_add
  rw [hc4]
  step dupR 2
  step dupR 1
  step Gas.mstoreG (by code_fact) (by code_fact) (by rw [hx5]; gas_ok)
  step Gas.reshapeG (s' := [0xc4, 0x64, w, t, f, C, sel, U] ++ rest)
    (m' := W5 M sel (mkey C) (mkey f) (mkey t) w) (g' := gas - 143) rfl (by rw [hx5]; rfl)
    (by rw [hx5]; gas_ok)
  step pushR 1 (0x20 : U256)
  step binR 0x01 instruction_add
  rw [he4]
  step swapR 4
  norm
  step popR
  step popR
  step popR
  step popR
  step popR
  step pushR 1 (0 : U256)
  step pushR 1 (0x40 : U256)
  step Gas.mloadG (by code_fact) (by code_fact) (by rw [hx6]; gas_ok)
  step Gas.reshapeG (s' := [0x60, 0, 0xe4, sel, U] ++ rest)
    (m' := W5 M sel (mkey C) (mkey f) (mkey t) w) (g' := gas - 171)
    (by rw [hx6, memoryExtend_zero, show (0x40 : U256).toNat = 64 from rfl, read40_W5 hM,
      hptr]; rfl)
    (by rw [hx6, memoryExtend_zero]) (by rw [hx6]; gas_ok)
  step dupR 0
  step dupR 3
  step binR 0x03 Local.instruction_sub
  rw [hs4]
  step dupR 1
  step pushR 1 (0 : U256)
  step dupR 7
  step dupR 0
  exact (repc (by decide)).seq (Gas.reshapeG rfl rfl (by gas_ok))

/-- After a call that succeeded (flag 1), from 4218: the code drops the call operands, returns
to 914 and stops. -/
theorem okTailF {sel U v t f x : U256} {M : ByteArray} {gas : Nat} (hg : 53 ≤ gas) :
    Gas.SpecG fork (At CODE message 4218 [1, 0xe4, sel, U, v, t, f, 0x0392, x] M gas state substate)
      (Halted false .empty (gas - 53) state substate) := by
  step unR 0x15 instruction_iszero
  step unR 0x15 instruction_iszero
  step pushR 2 (0x1084 : U256)
  step jumpiR (by decide)
  step jumpdestR
  step popR
  step popR
  step popR
  step pushR 2 (0x1098 : U256)
  step jumpR
  at_pc 4248
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

/-- The selector of `transferFromByLegacy(address,address,address,uint256)`. -/
def SEL_F : ByteArray := ⟨#[0x8b, 0x47, 0x7a, 0xdb]⟩

theorem sel_F : (wordBytes (selWord 0x8b477adb)).extract 0 4 = SEL_F := by decide +kernel

/-- The call data that `transferFrom` forwards when deprecated:
`transferFromByLegacy(msg.sender, _from, _to, _value)`, i.e. the selector 0x8b477adb, then the
caller, `_from`, `_to` (argument words 0 and 1 masked to 160 bits) and `_value` (word 2). -/
abbrev dataF (message : Message fork) : ByteArray :=
  SEL_F ++ wordBytes (Transfer.callerKey message) ++ wordBytes (fromArg message) ++
    wordBytes (toArg message) ++ wordBytes (valArg message)

/-- The memory before the CALL of the deprecated `transferFrom`. -/
abbrev memFD (message : Message fork) : ByteArray :=
  W5 (memF message) 0x8b477adb (mkey message.caller.toU256) (mkey (fromArg message))
    (mkey (toArg message)) (valArg message)

theorem size_memF (message : Message fork) : (memF message).size = 96 := size_mapMem size_MEM0 _ _

theorem ptr_memF (message : Message fork) :
    loadWord (memoryReadBytes (memF message) 64 32) 0 32 = 0x60 :=
  ptr_mapMem size_MEM0 mload_MEM0 _ _

theorem data_memFD (message : Message fork) :
    memoryReadBytes (memoryExtend (memFD message) 0) 96 132 = dataF message := by
  rw [memoryExtend_zero, memFD, data_W5 (size_memF message), sel_F]
  simp only [fromArg, toArg, DeprecatedTransfer.mkey_addrArg]

/-- The gas of the path from pc 0 to the CALL, for `transferFrom`. -/
abbrev preCostF (c0 cB c10 cU : Bool) : Nat :=
  1093 + slotCost c0 + slotCost cB + slotCost c10 + accCost cU

/-- The gas that the code asks CALL to pass on, for a frame that starts with `gas`. -/
abbrev askedOfF (gas : Nat) (c0 cB c10 cU : Bool) : U256 :=
  asked (gas - (1090 + slotCost c0 + slotCost cB + slotCost c10 + accCost cU))

/-- What CALL pays and passes on, for `transferFrom`. -/
abbrev callGasF (fork : Fork) (gas : Nat) (c0 cB c10 cU : Bool) : MessageCallGas :=
  messageCallGas fork 0 (askedOfF gas c0 cB c10 cU).toNat (gas - preCostF c0 cB c10 cU) 0 100

/-- The state when `transferFrom` calls: slots 0, `isBlackListed[_from]`, 10, then the upgraded
account recorded read. -/
abbrev callStateF (state : State.TransactionState) (message : Message fork) :
    State.TransactionState :=
  (checkState state message).recordAccountRead (upAddr state message)

/-- The substate when `transferFrom` calls. -/
abbrev callSubF (substate : Substate) (state : State.TransactionState) (message : Message fork) :
    Substate :=
  { checkSub substate message with
    accessedAddresses := substate.accessedAddresses.insert (upAddr state message) }

/-- The hypotheses shared by the deprecated `transferFrom` theorems, besides the gas: as `HypT`
with the selector 0x23b872dd and the blacklist slot of `_from` (`blackFrom (fromArg message)`),
not of the caller. -/
structure HypF (fork : Fork) (message : Message fork) (state : State.TransactionState)
    (substate : Substate) (c : ByteArray) (c0 cB c10 cU : Bool) : Prop where
  berlin : .berlin ≤ fork
  glam : fork < .glamsterdam
  size : 4 ≤ message.data.size
  size' : message.data.size < 2 ^ 256
  sel : selector message.data = 0x23b872dd
  value : message.value = 0
  notPaused : byte20 (storageAt state message.currentTarget 0) = 0
  notBlack : (storageAt state message.currentTarget (blackFrom (fromArg message))).toNat % 256 = 0
  deprecated : byte20 (storageAt state message.currentTarget 10) ≠ 0
  code : state.getCode (state.getAccount (upAddr state message)).codeHash = .ok c
  codeSize : 0 < c.size
  codeSize' : c.size < 2 ^ 256
  noDelegation : .pectra ≤ fork → delegatedAddress c = none
  depth : message.depth + 1 ≤ STACK_DEPTH_LIMIT
  cold0 : coldIn substate message.currentTarget 0 = c0
  coldB : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget
    (blackFrom (fromArg message)) = cB
  cold10 : coldIn (accessSlot (accessSlot substate message.currentTarget 0)
    message.currentTarget (blackFrom (fromArg message))) message.currentTarget 10 = c10
  coldU : decide (upAddr state message ∉ substate.accessedAddresses) = cU

/-- From pc 0 to the EXTCODESIZE at 4200, for a deprecated `transferFrom`. -/
theorem preExtF (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsz : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x23b872dd) (hv : message.value = 0)
    (hnp : byte20 (storageAt state message.currentTarget 0) = 0)
    (hnb : (storageAt state message.currentTarget (blackFrom (fromArg message))).toNat % 256 = 0)
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0)
    {c0 cB c10 : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hcB : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget
      (blackFrom (fromArg message)) = cB)
    (hc10 : coldIn (accessSlot (accessSlot substate message.currentTarget 0) message.currentTarget
      (blackFrom (fromArg message))) message.currentTarget 10 = c10)
    {gas : Nat} (hg : 1065 + slotCost c0 + slotCost cB + slotCost c10 ≤ gas) :
    Hoare fork (At CODE message 0 [] .empty gas state substate)
      (At CODE message 4200
        [upWord (storageAt state message.currentTarget 10),
          upWord (storageAt state message.currentTarget 10), 0, 0x60, 0x84, 0x60, 0, 0xe4,
          0x8b477adb, upWord (storageAt state message.currentTarget 10), valArg message,
          toArg message, fromArg message, 0x0392, BitVec.ofNat 256 (selector message.data)]
        (memFD message) (gas - (1065 + slotCost c0 + slotCost cB + slotCost c10))
        (checkState state message) (checkSub substate message)) := by
  have ht : tested (BitVec.ofNat 256 (selector message.data)) ENTRIES = 7 := by
    rw [hsel]; decide
  have hb : branch (BitVec.ofNat 256 (selector message.data)) 54 (entrySize 4 2) ENTRIES =
      819 := by
    rw [hsel]; decide
  have h1 := dispatch (state := state) (substate := substate) hsize hsz (gas := gas)
    (by rw [ht]; gas_ok)
  rw [ht, hb] at h1
  refine Gas.Triple.seqL h1 ?_
  step TransferFrom.entry hv (by gas_ok)
  step TransferFrom.notPaused hfork (by simp) hnp hc0 (by gas_ok)
  step notBlack hfork (by simp) hcB (by rw [storageAt_readSlot]; exact hnb) (by gas_ok) size_MEM0
  step depSetW hfork (Or.inr (Or.inr ⟨rfl, rfl⟩)) (by simp)
    (by rw [storageAt_readSlot, storageAt_readSlot]; exact hdep) hc10 (by gas_ok)
  step upLoad (state := readSlot (readSlot state message.currentTarget 0) message.currentTarget
    (blackFrom (fromArg message))) hfork (Or.inr (Or.inr ⟨rfl, rfl⟩)) (by simp) (by gas_ok)
  rw [storageAt_readSlot, storageAt_readSlot]
  step pushR 4 (0x8b477adb : U256)
  step Logic.caller (by code_fact) (by code_fact) (by gas_ok) (by stk_ok)
  step dupR 5
  step dupR 5
  step dupR 5
  step encode4 (size_memF message) (ptr_memF message)
    (rest := [valArg message, toArg message, fromArg message, 0x0392,
      BitVec.ofNat 256 (selector message.data)]) (by simp) (by gas_ok)
  exact Logic.reshape rfl rfl (by gas_ok)

/-- The specification of `transferFrom(from, to, value)` when deprecated, for every callee: as
`spec_depT`, with the data `transferFromByLegacy(caller, from, to, value)` (`dataF`), the gas of this
path (`preCostF`, `callGasF`, 53 gas after the price of the CALL), and the state and substate
`callStateF`/`callSubF` (slots 0, `isBlackListed[_from]`, 10 and `ua` read and accessed) at the CALL. -/
theorem spec_depF {c : ByteArray} {c0 cB c10 cU : Bool}
    (h : HypF fork message state substate c c0 cB c10 cU) {gas : Nat}
    (hg : preCostF c0 cB c10 cU + 100 ≤ gas)
    (htail : 53 ≤ gas - preCostF c0 cB c10 cU - (callGasF fork gas c0 cB c10 cU).cost)
    {callee : Evm fork Nat → Message fork → Evm fork Nat → Prop} :
    SpecUnder fork callee (At CODE message 0 [] .empty gas state substate)
      fun evm => ∃ caller msg child, callee caller msg child ∧
        Sends message (upAddr state message) c (dataF message) msg ∧
        msg.gas = (callGasF fork gas c0 cB c10 cU).subCall ∧
        caller.state = ((callStateF state message).recordAccountRead
          (upAddr state message)).recordAccountRead message.currentTarget ∧
        caller.substate = { callSubF substate state message with
          accessedAddresses :=
            (callSubF substate state message).accessedAddresses.insert (upAddr state message) } ∧
        (child.error = none →
          Halted false .empty
            (gas - preCostF c0 cB c10 cU - (callGasF fork gas c0 cB c10 cU).cost + child.gas - 53)
            (incorporateChild fork caller child).state
            (incorporateChild fork caller child).substate evm) ∧
        (child.error ≠ none →
          Halted true .empty
            (gas - preCostF c0 cB c10 cU - (callGasF fork gas c0 cB c10 cU).cost + child.gas - 25)
            (incorporateChild fork caller child).state
            (incorporateChild fork caller child).substate evm) := by
  have hext : extendMemory (memFD message).size
      [((0x60 : U256), (0x84 : U256)), ((0x60 : U256), (0 : U256))] = ⟨0, 0⟩ := by
    rw [memFD, size_W5 (size_memF message)]; decide
  have hpre : Hoare fork (At CODE message 0 [] .empty gas state substate)
      (At CODE message 4217
        [askedOfF gas c0 cB c10 cU, upWord (storageAt state message.currentTarget 10), 0, 0x60,
          0x84, 0x60, 0, 0xe4, 0x8b477adb, upWord (storageAt state message.currentTarget 10),
          valArg message, toArg message, fromArg message, 0x0392,
          BitVec.ofNat 256 (selector message.data)]
        (memFD message) (gas - preCostF c0 cB c10 cU) (callStateF state message)
        (callSubF substate state message)) := by
    simp only [preCostF, askedOfF, accCost] at hg ⊢
    refine (preExtF h.berlin h.size h.size' h.sel h.value h.notPaused h.notBlack h.deprecated
      h.cold0 h.coldB h.cold10 (by gas_ok)).seq ?_
    refine (toCall (gas := gas - (1065 + slotCost c0 + slotCost cB + slotCost c10))
      (st := checkState state message) (ss := checkSub substate message) (message := message)
      (M := memFD message)
      (rest := [upWord (storageAt state message.currentTarget 10), 0, 0x60, 0x84, 0x60, 0, 0xe4,
      0x8b477adb, upWord (storageAt state message.currentTarget 10), valArg message,
      toArg message, fromArg message, 0x0392, BitVec.ofNat 256 (selector message.data)])
      h.berlin h.glam (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))) (by simp) h.code
      h.codeSize h.codeSize' h.coldU (by simp only [accCost]; gas_ok)).seq ?_
    refine Logic.reshape ?_ rfl (by simp only [accCost]; gas_ok)
    simp only [List.cons.injEq, and_true]
    exact congrArg asked (by unfold accCost; omega)
  have hcall := callWith (fork := fork) (code := CODE) (message := message) (pc := 4217)
    (memory := memFD message) (gas := gas - preCostF c0 cB c10 cU)
    (state := callStateF state message)
    (substate := callSubF substate state message) (callee := callee)
    (asked := askedOfF gas c0 cB c10 cU) (to := upWord (storageAt state message.currentTarget 10))
    (inputStart := 0x60) (inputSize := 0x84) (outputStart := 0x60) (outputSize := 0)
    (rest := [0xe4, 0x8b477adb, upWord (storageAt state message.currentTarget 10),
      valArg message, toArg message, fromArg message, 0x0392,
      BitVec.ofNat 256 (selector message.data)]) (cold := false)
    h.berlin h.glam (by code_fact) (by code_fact) h.code h.noDelegation h.depth
    (by simp [upAddr]) (by rw [hext]; simp only [Bool.false_eq_true, ↓reduceIte]; omega)
  rw [hext] at hcall
  simp only [Bool.false_eq_true, ↓reduceIte] at hcall
  refine SpecUnder.seq (HoareUnder.of_hoare hpre) (HoareUnder.seq hcall (HoareUnder.of_hoare ?_))
  rintro evm ⟨caller, msg, child, hcal, -, hcs, hcss, hmg, hmc, hmt, hmtg, hmca, hmcode, hmd, hmv,
    hmdep, hmst, hat⟩
  have hfwd : Sends message (upAddr state message) c (dataF message) msg := by
    refine ⟨hmc, hmt, hmtg, hmca, hmcode, ?_, hmv, hmdep, hmst⟩
    rw [hmd]; exact data_memFD message
  by_cases he : child.error = none
  · simp only [he, Option.isNone_none, ↓reduceIte] at hat
    obtain ⟨after, hreach, hrun, hq⟩ := okTailF (fork := fork) (message := message)
      (state := (incorporateChild fork caller child).state)
      (substate := (incorporateChild fork caller child).substate)
      (gas := gas - preCostF c0 cB c10 cU - ((callGasF fork gas c0 cB c10 cU).cost + 0) + child.gas)
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
      (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
      (rest := [0xe4, 0x8b477adb, upWord (storageAt state message.currentTarget 10),
        valArg message, toArg message, fromArg message, 0x0392,
        BitVec.ofNat 256 (selector message.data)]) (by simp)
      (gas := gas - preCostF c0 cB c10 cU - ((callGasF fork gas c0 cB c10 cU).cost + 0) + child.gas)
      (by omega) evm hat
    refine ⟨after, Gas.reaches_toStep hreach, hrun, caller, msg, child, hcal, hfwd, hmg, hcs, hcss,
      fun h => absurd h he, fun _ => ?_⟩
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hq
    exact ⟨h1, h2, h3, by rw [h4]; omega, h5, h6⟩

/-- `transferFrom(from, to, value)` when deprecated, for a callee that succeeds on the forwarded call:
the run STOPs with no error after the call (state and substate from `incorporateChild`). -/
theorem spec_depF_succeeds {c : ByteArray} {c0 cB c10 cU : Bool}
    (h : HypF fork message state substate c c0 cB c10 cU) {gas : Nat}
    (hg : preCostF c0 cB c10 cU + 100 ≤ gas)
    (htail : 53 ≤ gas - preCostF c0 cB c10 cU - (callGasF fork gas c0 cB c10 cU).cost)
    {callee : Evm fork Nat → Message fork → Evm fork Nat → Prop}
    (hok : SucceedsD message (upAddr state message) c (dataF message) callee) :
    SpecUnder fork callee (At CODE message 0 [] .empty gas state substate)
      fun evm => ∃ caller msg child, callee caller msg child ∧
        Sends message (upAddr state message) c (dataF message) msg ∧ child.error = none ∧
        Halted false .empty
          (gas - preCostF c0 cB c10 cU - (callGasF fork gas c0 cB c10 cU).cost + child.gas - 53)
          (incorporateChild fork caller child).state
          (incorporateChild fork caller child).substate evm := by
  refine (spec_depF h hg htail).consequence (fun _ h => h) ?_
  rintro evm ⟨caller, msg, child, hcal, hfwd, -, -, -, hstop, -⟩
  have he := hok caller msg child hcal hfwd
  exact ⟨caller, msg, child, hcal, hfwd, he, hstop he⟩

/-- `transferFrom(from, to, value)` when deprecated, for a callee that fails on the forwarded call: the
run reverts with no output. -/
theorem spec_depF_fails {c : ByteArray} {c0 cB c10 cU : Bool}
    (h : HypF fork message state substate c c0 cB c10 cU) {gas : Nat}
    (hg : preCostF c0 cB c10 cU + 100 ≤ gas)
    (htail : 53 ≤ gas - preCostF c0 cB c10 cU - (callGasF fork gas c0 cB c10 cU).cost)
    {callee : Evm fork Nat → Message fork → Evm fork Nat → Prop}
    (hfail : FailsD message (upAddr state message) c (dataF message) callee) :
    SpecUnder fork callee (At CODE message 0 [] .empty gas state substate)
      fun evm => evm.error = some .revert ∧ evm.output = .empty := by
  refine (spec_depF h hg htail).consequence (fun _ h => h) ?_
  rintro evm ⟨caller, msg, child, hcal, hfwd, -, -, -, -, hko⟩
  obtain ⟨-, herr, hevm, -⟩ := hko (hfail caller msg child hcal hfwd)
  exact ⟨by simpa using herr, hevm⟩

/-- `transferFrom(from, to, value)` when deprecated, run by the interpreter's own message runner: for
every upgraded code `c` with a specification whose stopped frames end with no error, the run STOPs
with no error after the forwarded call, or the runner aborts. -/
theorem runFrame_depF_process {c : ByteArray} {c0 cB c10 cU : Bool}
    (h : HypF fork message state substate c c0 cB c10 cU)
    (hpre : Precompiles.isPrecompile fork (upAddr state message).toU256.toNat = false)
    {gas : Nat} (hg : preCostF c0 cB c10 cU + 100 ≤ gas)
    (htail : 53 ≤ gas - preCostF c0 cB c10 cU - (callGasF fork gas c0 cB c10 cU).cost)
    {G : Message fork → State.TransactionState → Substate → Prop}
    {Q : Message fork → State.TransactionState → Substate → Evm fork Nat → Prop}
    (hspec : ∀ msg st ss, msg.code = c → G msg st ss →
      Spec fork (At c msg 0 [] .empty msg.gas (startState fork msg st) ss) (Q msg st ss))
    (hG : ∀ msg st ss, Sends message (upAddr state message) c (dataF message) msg → G msg st ss)
    (hQ : ∀ msg st ss stopped, Q msg st ss stopped → stopped.error = none)
    {bound : Nat} {evm : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    (∃ stopped, runFrame (step fork) (step_decreases fork) bound (processRunner fork bound) evm
        within = .ok stopped ∧ ∃ caller msg child, RunsAs c G Q caller msg child ∧
        Sends message (upAddr state message) c (dataF message) msg ∧ child.error = none ∧
        Halted false .empty
          (gas - preCostF c0 cB c10 cU - (callGasF fork gas c0 cB c10 cU).cost + child.gas - 53)
          (incorporateChild fork caller child).state
          (incorporateChild fork caller child).substate stopped) ∨
    ∃ e, runFrame (step fork) (step_decreases fork) bound (processRunner fork bound) evm
        within = .error e ∧ e.aborts = true :=
  (spec_depF_succeeds h hg htail (succeedsD_runsAs hQ hG hpre)).runFrame
    (meets_of_spec hspec bound) start within

/-- The specification of `transferFrom(from, to, value)` when deprecated and the upgraded
address has no code: the run reverts with no output before any call.
Gas `1090 + the three slot prices + price(ua)`. -/
theorem spec_depFNoCode (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    (hsize : 4 ≤ message.data.size) (hsz : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x23b872dd) (hv : message.value = 0)
    (hnp : byte20 (storageAt state message.currentTarget 0) = 0)
    (hnb : (storageAt state message.currentTarget (blackFrom (fromArg message))).toNat % 256 = 0)
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0)
    (hcode : state.getCode (state.getAccount (upAddr state message)).codeHash = .ok .empty)
    {c0 cB c10 cU : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hcB : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget
      (blackFrom (fromArg message)) = cB)
    (hc10 : coldIn (accessSlot (accessSlot substate message.currentTarget 0) message.currentTarget
      (blackFrom (fromArg message))) message.currentTarget 10 = c10)
    (hcU : decide (upAddr state message ∉ substate.accessedAddresses) = cU)
    {gas : Nat} (hg : 1090 + slotCost c0 + slotCost cB + slotCost c10 + accCost cU ≤ gas) :
    Spec fork (At CODE message 0 [] .empty gas state substate)
      (Halted true .empty (gas - (1090 + slotCost c0 + slotCost cB + slotCost c10 + accCost cU))
        (callStateF state message) (callSubF substate state message)) := by
  simp only [accCost] at hg ⊢
  refine (preExtF hfork hsize hsz hsel hv hnp hnb hdep hc0 hcB hc10 (by gas_ok)).seq ?_
  refine (noCode (gas := gas - (1065 + slotCost c0 + slotCost cB + slotCost c10))
    (st := checkState state message) (ss := checkSub substate message) (message := message)
    (M := memFD message)
    (rest := [upWord (storageAt state message.currentTarget 10), 0, 0x60, 0x84, 0x60, 0, 0xe4,
      0x8b477adb, upWord (storageAt state message.currentTarget 10), valArg message,
      toArg message, fromArg message, 0x0392, BitVec.ofNat 256 (selector message.data)])
    hfork hglam (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) (by simp) hcode hcU
    (by simp only [accCost]; gas_ok)).consequence (fun _ h => h) ?_
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  exact ⟨hr, he, ho, by rw [hgas]; simp only [accCost]; gas_ok, hs, hss⟩

end UsdtVerify.DeprecatedTransferFrom
