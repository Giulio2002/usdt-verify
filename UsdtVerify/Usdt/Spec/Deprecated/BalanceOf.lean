import UsdtVerify.Usdt.Spec.BalanceOf
import UsdtVerify.Usdt.Spec.Deprecated.TotalSupply

/-!
# balanceOf(who) when deprecated: the forward to the upgraded contract

The path of a call with selector 0x70a08231, no value, and byte 20 of slot 10 (`deprecated`) set.

- At 1456, the entry checks that the call has no value and calls the getter at 4665 with `who`
  (argument word 0 masked to 160 bits) and return address 1511.
- At 4665, the deprecation check (shared block `depSet`); the flag is set, so on at 4689.
- At 4689, the code reads slot 10 again and keeps its low 160 bits: `upgradedAddress`.
- It writes 0 at 0x80, the selector 0x70a08231 shifted left by 224 bits at 0x60, and `who` at
  0x64: the call data is the 4 selector bytes then the 32 bytes of `who`.
- At 4874, EXTCODESIZE (shared block `toCall` / `noCode`); at 4891, CALL with gas
  `gasleft - 710`, value 0, input 36 bytes at 0x60, output 32 bytes at 0x60.
- At 4892, a revert when the call failed (shared block `failTail`); else the code reads the word
  at 0x60 and returns it through 1511 (shared block `retBig`).
-/

namespace UsdtVerify.DeprecatedBalance

open EthLib.Base (Fork U256 toAddressMasked)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts
open UsdtVerify.Complete (Route Routes routeAddr routeCode routeCost routeState routeSub SendsVia
  CallFrom atCallState atCallSub routes_congr routeCost_insert_insert callWithR)
open Deprecated

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate}

/-- The selector word that the code writes at 0x60: 0x70a08231 shifted left by 224 bits. -/
def SELWB : U256 :=
  mul (0x0100000000000000000000000000000000000000000000000000000000 : U256)
    (bitwiseAnd (0xffffffff : U256) (0x70a08231 : U256))

/-- The memory with the selector word at 0x60 (160 bytes). -/
def M1B : ByteArray := memoryWrite M1 96 (wordBytes SELWB)

/-- The memory before the call: `who` written at 0x64, over the selector word. -/
abbrev M2B (a : U256) : ByteArray := memoryWrite M1B 100 (wordBytes a)

/-- The 4 bytes of the selector of `balanceOf(address)`. -/
def SEL_B : ByteArray := ⟨#[0x70, 0xa0, 0x82, 0x31]⟩

theorem size_M1B : M1B.size = 160 := by decide +kernel

theorem mload_M1B : loadWord (memoryReadBytes (memoryExtend M1B 0) 64 32) 0 32 = 0x60 := by
  decide +kernel

theorem sel_M1B : memoryReadBytes M1B 96 4 = SEL_B := by decide +kernel

theorem size_M2B (a : U256) : (M2B a).size = 160 := by
  rw [M2B, size_memoryWrite (by rw [size_wordBytes, size_M1B]; decide), size_M1B]

theorem mload_M2B (a : U256) :
    loadWord (memoryReadBytes (memoryExtend (M2B a) 0) 64 32) 0 32 = 0x60 := by
  have h := mload_M1B
  rw [memoryExtend_zero] at h
  rw [memoryExtend_zero, M2B, memoryReadBytes_memoryWrite_of_disjoint
    (by rw [size_wordBytes, size_M1B]; decide) (.inl (by decide))]
  exact h

theorem data_M2B (a : U256) :
    memoryReadBytes (memoryExtend (M2B a) 0) 96 36 = SEL_B ++ wordBytes a := by
  rw [memoryExtend_zero, M2B]
  have h := memoryReadBytes_memoryWrite_eq_append (memory := M1B) (value := wordBytes a) (s := 96) (k := 4)
    (by rw [size_wordBytes, size_M1B]; decide)
  rw [size_wordBytes] at h
  rw [h, sel_M1B]

/-- From 4689: the code reads slot 10 again (warm), keeps the address, writes the call data at
0x60 (the selector, then `a` at 0x64) and pushes the operands of CALL, up to EXTCODESIZE at 4874.
The address argument `a` is already masked (`a = addrArg ...`), so its masks change nothing. -/
theorem fwdArgsB (hfork : .berlin ≤ fork) {a : U256} (ha : bitwiseAnd ADDR_MASK a = a)
    {rest : List U256} (hrest : rest.length ≤ 4) {gas : Nat} (hg : 277 ≤ gas) :
    Gas.HoareG fork (At CODE message 4689 (0 :: a :: rest) MEM0 gas
        (readSlot state message.currentTarget 10) (accessSlot substate message.currentTarget 10))
      (At CODE message 4874
        ([upWord (storageAt state message.currentTarget 10),
          upWord (storageAt state message.currentTarget 10), 0, 0x60, 0x24, 0x60, 0x20, 0x84,
          0x70a08231, upWord (storageAt state message.currentTarget 10), 0, a] ++ rest) (M2B a)
        (gas - 277) (readSlot state message.currentTarget 10)
        (accessSlot substate message.currentTarget 10)) := by
  have hexp : exponentBytes (0 : U256) = 0 := by decide
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
  step Gas.reshapeG (s' := [upWord (storageAt state message.currentTarget 10), 0, a] ++ rest)
    (m' := MEM0) (g' := gas - 145)
    (by rw [up_eq, ← storageAt_readSlot state message.currentTarget message.currentTarget 10 10]
        rfl) rfl (by gas_ok)
  step pushR 4 (0x70a08231 : U256)
  step dupR 3
  step pushR 1 (0 : U256)
  step pushR 1 (0x40 : U256)
  have hx0 : extendMemory MEM0.size [((0x40 : U256), (32 : U256))] = ⟨0, 0⟩ := by
    rw [size_MEM0]; decide
  step Gas.mloadG (by code_fact) (by code_fact) (by rw [hx0]; gas_ok)
  step Gas.reshapeG (s' := [0x60, 0, a, 0x70a08231, upWord (storageAt state message.currentTarget 10),
      0, a] ++ rest) (m' := MEM0) (g' := gas - 160)
    (by rw [hx0, memoryExtend_zero, show (0x40 : U256).toNat = 64 from rfl, mload_MEM0]; rfl)
    (by rw [hx0, memoryExtend_zero]) (by rw [hx0]; gas_ok)
  step pushR 1 (0x20 : U256)
  step binR 0x01 instruction_add
  step Gas.reshapeG (s' := [0x80, 0, a, 0x70a08231, upWord (storageAt state message.currentTarget 10),
      0, a] ++ rest) (m' := MEM0) (g' := gas - 166) rfl rfl (by gas_ok)
  have hx1 : extendMemory MEM0.size [((0x80 : U256), (32 : U256))] = ⟨6, 64⟩ := by
    rw [size_MEM0]; decide
  step Gas.mstoreG (by code_fact) (by code_fact) (by rw [hx1]; gas_ok)
  step Gas.reshapeG (s' := [a, 0x70a08231, upWord (storageAt state message.currentTarget 10), 0, a]
      ++ rest) (m' := M1) (g' := gas - 175) rfl (by rw [hx1]; rfl) (by rw [hx1]; gas_ok)
  at_pc 4761
  step pushR 1 (0x40 : U256)
  have hx2 : extendMemory M1.size [((0x40 : U256), (32 : U256))] = ⟨0, 0⟩ := by
    rw [size_M1]; decide
  step Gas.mloadG (by code_fact) (by code_fact) (by rw [hx2]; gas_ok)
  step Gas.reshapeG (s' := [0x60, a, 0x70a08231, upWord (storageAt state message.currentTarget 10), 0,
      a] ++ rest) (m' := M1) (g' := gas - 181)
    (by rw [hx2, show (0x40 : U256).toNat = 64 from rfl, mload_M1]; rfl)
    (by rw [hx2, memoryExtend_zero]) (by rw [hx2]; gas_ok)
  step dupR 2
  step pushR 4 (0xffffffff : U256)
  step binR 0x16 Local.instruction_and
  step pushR 29 (0x0100000000000000000000000000000000000000000000000000000000 : U256)
  step binR 0x02 Local.instruction_mul
  step dupR 1
  have hx3 : extendMemory M1.size [((0x60 : U256), (32 : U256))] = ⟨0, 0⟩ := by
    rw [size_M1]; decide
  step Gas.mstoreG (by code_fact) (by code_fact) (by rw [hx3]; gas_ok)
  step Gas.reshapeG (s' := [0x60, a, 0x70a08231, upWord (storageAt state message.currentTarget 10), 0,
      a] ++ rest) (m' := M1B) (g' := gas - 204) rfl (by rw [hx3, memoryExtend_zero]; rfl)
    (by rw [hx3]; gas_ok)
  at_pc 4804
  step pushR 1 (0x04 : U256)
  step binR 0x01 instruction_add
  have h64 : add (0x04 : U256) (0x60 : U256) = 0x64 := by decide
  rw [h64]
  step dupR 0
  step dupR 2
  step pushR 20 ADDR_MASK
  step binR 0x16 Local.instruction_and
  step pushR 20 ADDR_MASK
  step binR 0x16 Local.instruction_and
  rw [ha, ha]
  step dupR 1
  have hx4 : extendMemory M1B.size [((0x64 : U256), (32 : U256))] = ⟨0, 0⟩ := by
    rw [size_M1B]; decide
  step Gas.mstoreG (by code_fact) (by code_fact) (by rw [hx4]; gas_ok)
  step Gas.reshapeG (s' := [0x64, 0x64, a, 0x70a08231, upWord (storageAt state message.currentTarget 10),
      0, a] ++ rest) (m' := M2B a) (g' := gas - 234) rfl (by rw [hx4, memoryExtend_zero]; rfl)
    (by rw [hx4]; gas_ok)
  at_pc 4855
  step pushR 1 (0x20 : U256)
  step binR 0x01 instruction_add
  have h84 : add (0x20 : U256) (0x64 : U256) = 0x84 := by decide
  rw [h84]
  step swapR 1
  norm
  step popR
  step popR
  step pushR 1 (0x20 : U256)
  step pushR 1 (0x40 : U256)
  have hx5 : extendMemory (M2B a).size [((0x40 : U256), (32 : U256))] = ⟨0, 0⟩ := by
    rw [size_M2B]; decide
  step Gas.mloadG (by code_fact) (by code_fact) (by rw [hx5]; gas_ok)
  step Gas.reshapeG (s' := [0x60, 0x20, 0x84, 0x70a08231,
      upWord (storageAt state message.currentTarget 10), 0, a] ++ rest) (m' := M2B a)
    (g' := gas - 256)
    (by rw [hx5, show (0x40 : U256).toNat = 64 from rfl, mload_M2B]; rfl)
    (by rw [hx5, memoryExtend_zero]) (by rw [hx5]; gas_ok)
  step dupR 0
  step dupR 3
  step binR 0x03 instruction_sub
  have h24 : sub (0x84 : U256) (0x60 : U256) = 0x24 := by decide
  rw [h24]
  step dupR 1
  step pushR 1 (0 : U256)
  step dupR 7
  step dupR 0
  exact restate (by decide) (by simp) rfl (by gas_ok)
    (readSlot_readSlot state message.currentTarget 10)
    (accessSlot_accessSlot substate message.currentTarget 10)

/-- After a call that succeeded (flag 1), from 4892: the code reads the word at 0x60 and returns
it through 1511. -/
theorem okTailB {M : ByteArray} (hM : M.size = 160)
    (hptr : loadWord (memoryReadBytes M 64 32) 0 32 = 0x60) {U a x : U256} {gas : Nat}
    (hg : 126 ≤ gas) :
    Gas.SpecG fork (At CODE message 4892 [1, 0x84, 0x70a08231, U, 0, a, 0x05e7, x] M gas state
        substate)
      (Halted false (wordBytes (resWord M)) (gas - 126) state substate) := by
  have hext0 : extendMemory M.size [((0x40 : U256), (32 : U256))] = ⟨0, 0⟩ := by
    rw [hM]; decide
  have hext1 : extendMemory M.size [((0x60 : U256), (32 : U256))] = ⟨0, 0⟩ := by
    rw [hM]; decide
  step unR 0x15 instruction_iszero
  step unR 0x15 instruction_iszero
  step pushR 2 (0x1326 : U256)
  step jumpiR (by decide)
  step jumpdestR
  step popR
  step popR
  step popR
  step pushR 1 (0x40 : U256)
  step Gas.mloadG (by code_fact) (by code_fact) (by rw [hext0]; gas_ok)
  step Gas.reshapeG (s' := [0x60, 0, a, 0x05e7, x]) (m' := M) (g' := gas - 32)
    (by rw [hext0, memoryExtend_zero]; exact congrArg (· :: [0, a, 0x05e7, x]) hptr)
    (by rw [hext0, memoryExtend_zero]) (by rw [hext0]; gas_ok)
  step dupR 0
  step Gas.mloadG (by code_fact) (by code_fact) (by rw [hext1]; gas_ok)
  step Gas.reshapeG (s' := [resWord M, 0x60, 0, a, 0x05e7, x]) (m' := M) (g' := gas - 38)
    (by rw [hext1, memoryExtend_zero]; rfl) (by rw [hext1, memoryExtend_zero])
    (by rw [hext1]; gas_ok)
  step swapR 0
  norm
  step popR
  step swapR 0
  norm
  step popR
  step pushR 2 (0x1343 : U256)
  step jumpR
  at_pc 4931
  step jumpdestR
  step swapR 1
  norm
  step swapR 0
  norm
  step popR
  step jumpR
  refine (repc (pc' := 1511) (by decide)).seq ?_
  refine (retBig (Or.inr rfl) hM hptr (gas := gas - 76) (by gas_ok)).consequence (fun _ h => h) ?_
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  exact ⟨hr, he, ho, by rw [hgas]; gas_ok, hs, hss⟩

/-- The memory after the call, from a memory `B` before it: CALL writes the first
`min 32 o.size` bytes of the output `o` of the callee at 0x60. -/
abbrev outMemOf (B o : ByteArray) : ByteArray :=
  memoryWrite (memoryExtend B 0) 96 (o.extract 0 (min 32 o.size))

theorem size_outMemOf {B : ByteArray} (hB : B.size = 160) (o : ByteArray) :
    (outMemOf B o).size = 160 := by
  rw [outMemOf, memoryExtend_zero, size_memoryWrite (by rw [ByteArray.size_extract, hB]; omega), hB]

theorem mload_outMemOf {B : ByteArray} (hB : B.size = 160)
    (hptr : loadWord (memoryReadBytes (memoryExtend B 0) 64 32) 0 32 = 0x60) (o : ByteArray) :
    loadWord (memoryReadBytes (outMemOf B o) 64 32) 0 32 = 0x60 := by
  rw [memoryExtend_zero] at hptr
  rw [outMemOf, memoryExtend_zero, memoryReadBytes_memoryWrite_of_disjoint
    (by rw [ByteArray.size_extract, hB]; omega) (.inl (by decide))]
  exact hptr

theorem resWord_outMemOf {B : ByteArray} (hB : B.size = 160) {o : ByteArray} (ho : 32 ≤ o.size) :
    resWord (outMemOf B o) = loadWord o 0 32 := by
  have hm : min 32 o.size = 32 := Nat.min_eq_left ho
  have hs : (o.extract 0 32).size = 32 := by rw [ByteArray.size_extract]; omega
  have hfit : 96 + (o.extract 0 32).size ≤ (memoryExtend B 0).size := by
    rw [hs, memoryExtend_zero, hB]; decide
  have h := memoryReadBytes_memoryWrite hfit
  rw [hs] at h
  rw [resWord, outMemOf, hm, h]
  unfold loadWord bufferRead
  congr 2
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  rw [EthLib.Base.byteAt_extract, ite_eq_left (by omega), Nat.zero_add]

/-- The gas of the path from pc 0 to the CALL, for `balanceOf`. -/
abbrev preCostB (fork : Fork) (c10 cU : Bool) : Nat := 924 + slotCost c10 + extCost fork cU

/-- The gas that the code asks CALL to pass on, for a frame that starts with `gas`. -/
abbrev askedOfB (fork : Fork) (gas : Nat) (c10 cU : Bool) : U256 :=
  asked (gas - (921 + slotCost c10 + extCost fork cU))

/-- What CALL pays and passes on (EIP-150, EIP-2929; the address is warm after EXTCODESIZE). -/
abbrev callGasB (fork : Fork) (gas : Nat) (c10 cU : Bool) (R : Nat) :
    MessageCallGas :=
  messageCallGas fork 0 (askedOfB fork gas c10 cU).toNat (gas - preCostB fork c10 cU) 0 (100 + R)

/-- The call data that the code forwards: the selector of `balanceOf`, then `who`. -/
abbrev dataB (message : Message fork) : ByteArray := SEL_B ++ wordBytes (addrArg message.data 0)

/-- From pc 0 to the CALL at 4891, when deprecated and the upgraded account has code. -/
theorem preCallB (hfork : .berlin ≤ fork)
    (hsize : 4 ≤ message.data.size) (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x70a08231) (hv : message.value = 0)
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0) {c : ByteArray}
    (hcode : state.getCode (state.getAccount (upAddr state message)).codeHash = .ok c)
    (hsz : 0 < c.size) (hszl : c.size < 2 ^ 256) {c10 cU : Bool}
    (hc10 : coldIn substate message.currentTarget 10 = c10)
    (hcU : decide (upAddr state message ∉ substate.accessedAddresses) = cU)
    {gas : Nat} (hg : preCostB fork c10 cU ≤ gas) :
    Hoare fork (At CODE message 0 [] .empty gas state substate)
      (At CODE message 4891
        [askedOfB fork gas c10 cU, upWord (storageAt state message.currentTarget 10), 0, 0x60, 0x24,
          0x60, 0x20, 0x84, 0x70a08231, upWord (storageAt state message.currentTarget 10), 0,
          addrArg message.data 0, 0x05e7, BitVec.ofNat 256 (selector message.data)]
        (M2B (addrArg message.data 0)) (gas - preCostB fork c10 cU) (callState state message)
        (callSub substate state message)) := by
  simp only [preCostB, askedOfB, extCost] at hg ⊢
  have ht : tested (BitVec.ofNat 256 (selector message.data)) ENTRIES = 17 := by
    rw [hsel]; decide
  have hb : branch (BitVec.ofNat 256 (selector message.data)) 54 (entrySize 4 2) ENTRIES =
      1456 := by
    rw [hsel]; decide
  have h1 := dispatch (state := state) (substate := substate) hsize hsize' (gas := gas)
    (by rw [ht]; gas_ok)
  rw [ht, hb] at h1
  refine Gas.Triple.seqL h1 ?_
  step BalanceOf.entry hv (by gas_ok)
  step depSet hfork (Or.inr ⟨rfl, rfl⟩) (by simp) hdep hc10 (by gas_ok)
  step fwdArgsB (state := state) hfork (by simp only [addrArg, mask_mask]) (by simp)
    (by gas_ok)
  step At.reshape (g' := gas - (896 + slotCost c10)) rfl rfl (by gas_ok)
  refine (toCall (gas := gas - (896 + slotCost c10)) (st := readSlot state message.currentTarget 10)
    (ss := accessSlot substate message.currentTarget 10) (message := message)
    (M := M2B (addrArg message.data 0))
    (rest := [upWord (storageAt state message.currentTarget 10), 0, 0x60, 0x24, 0x60, 0x20, 0x84,
      0x70a08231, upWord (storageAt state message.currentTarget 10), 0, addrArg message.data 0,
      0x05e7, BitVec.ofNat 256 (selector message.data)]) hfork (Or.inr (Or.inl ⟨rfl, rfl⟩))
    (by simp) hcode hsz hszl hcU (by simp only [extCost]; gas_ok)).seq ?_
  refine At.reshape ?_ rfl (by simp only [extCost]; gas_ok)
  simp only [List.cons.injEq, and_true]
  congr 1
  unfold extCost; omega

/-- `spec_depB` with the bound `htail` (at least 126 gas left after the price of the CALL) replaced by
`hcg`: every ended forwarded message that meets `callee`, sent with the gas the CALL gives from
the caller frame at the CALL (`CallFrom`, round 30), leaves at least 126 gas for the code after
the CALL, the gas the CALL keeps plus the gas left in the ended frame.
Stated as a `SpecOn` (round 26): the frames that end the runner's messages meet
`callee`, the runner may fail with any error, and the run ends as stated or at a failure of the
runner on a forwarded message (`SendsVia`); `.toUnder` gives EthLib's `SpecUnder`. -/
theorem spec_depB_g (hfork : .berlin ≤ fork)
    (hsize : 4 ≤ message.data.size) (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x70a08231) (hv : message.value = 0)
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0) {c : ByteArray}
    (hcode : state.getCode (state.getAccount (upAddr state message)).codeHash = .ok c)
    (hsz : 0 < c.size) (hszl : c.size < 2 ^ 256)
    {r : Route} (hroute : Routes fork state c r)
    (hdepth : message.depth + 1 ≤ STACK_DEPTH_LIMIT) {c10 cU : Bool}
    (hc10 : coldIn substate message.currentTarget 10 = c10)
    (hcU : decide (upAddr state message ∉ substate.accessedAddresses) = cU)
    {gas : Nat} (hg : preCostB fork c10 cU + 100 + callR substate state message r ≤ gas)
    {callee : Evm fork Nat → Message fork → Evm fork Nat → Prop}
    (hcg : ∀ caller msg child, callee caller msg child →
      SendsVia message (upAddr state message) c r (dataB message) msg →
      CallFrom (callGasB fork gas c10 cU (callR substate state message r)).subCall
        (atCallState (callState state message) (upAddr state message) r message.currentTarget)
        (atCallSub (callSub substate state message) (upAddr state message) r) caller msg →
      126 ≤ gas - preCostB fork c10 cU - (callGasB fork gas c10 cU (callR substate state message r)).cost + child.gas) :
    SpecOn fork callee (fun caller msg => SendsVia message (upAddr state message) c r (dataB message) msg ∧
      CallFrom (callGasB fork gas c10 cU (callR substate state message r)).subCall (atCallState (callState state message) (upAddr state message) r message.currentTarget) (atCallSub (callSub substate state message) (upAddr state message) r) caller msg)
      (At CODE message 0 [] .empty gas state substate)
      fun evm => ∃ caller msg child, callee caller msg child ∧
        SendsVia message (upAddr state message) c r (dataB message) msg ∧
        msg.gas = (callGasB fork gas c10 cU (callR substate state message r)).subCall ∧
        caller.state = (routeState ((callState state message).recordAccountRead
          (upAddr state message)) r).recordAccountRead message.currentTarget ∧
        caller.substate = routeSub { callSub substate state message with
          accessedAddresses :=
            (callSub substate state message).accessedAddresses.insert (upAddr state message) } r ∧
        (child.error = none →
          Halted false (wordBytes (resWord (outMemOf (M2B (addrArg message.data 0)) child.output)))
            (gas - preCostB fork c10 cU - (callGasB fork gas c10 cU (callR substate state message r)).cost + child.gas - 126)
            (incorporateChild fork caller child).state
            (incorporateChild fork caller child).substate evm) ∧
        (child.error ≠ none →
          Halted true .empty
            (gas - preCostB fork c10 cU - (callGasB fork gas c10 cU (callR substate state message r)).cost + child.gas - 25)
            (incorporateChild fork caller child).state
            (incorporateChild fork caller child).substate evm) := by
  have hext : extendMemory (M2B (addrArg message.data 0)).size
      [((0x60 : U256), (0x24 : U256)), ((0x60 : U256), (0x20 : U256))] = ⟨0, 0⟩ := by
    rw [size_M2B]; decide
  have hR : routeCost fork ((callSub substate state message).accessedAddresses.insert
      (toAddressMasked (upWord (storageAt state message.currentTarget 10)))) r =
      callR substate state message r := routeCost_insert_insert _ _ _
  have hcall := Complete.callWithRS (fork := fork) (code := CODE) (message := message) (pc := 4891)
    (memory := M2B (addrArg message.data 0)) (gas := gas - preCostB fork c10 cU)
    (state := callState state message)
    (substate := callSub substate state message) (callee := callee)
    (asked := askedOfB fork gas c10 cU) (to := upWord (storageAt state message.currentTarget 10))
    (i := 0x60) (isz := 0x24) (o := 0x60) (osz := 0x20)
    (rest := [0x84, 0x70a08231, upWord (storageAt state message.currentTarget 10), 0,
      addrArg message.data 0, 0x05e7, BitVec.ofNat 256 (selector message.data)]) (cold := false)
    hfork (by code_fact) (by code_fact) hcode (routes_congr (fun _ => rfl) hroute) hdepth
    (by simp [upAddr])
    (by rw [hext, hR]; simp only [accCost_false]; omega)
  rw [hext, hR] at hcall
  simp only [accCost_false] at hcall
  have hcall := hcall.mono (S' := (fun caller msg => SendsVia message (upAddr state message) c r (dataB message) msg ∧
      CallFrom (callGasB fork gas c10 cU (callR substate state message r)).subCall (atCallState (callState state message) (upAddr state message) r message.currentTarget) (atCallSub (callSub substate state message) (upAddr state message) r) caller msg))
    fun _ _ h => by
    obtain ⟨⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩, b1, b2, b3⟩ := h
    exact ⟨⟨a1, a2, a3, a4, a5, a6, by rw [a7]; exact data_M2B _, a8, a9, a10⟩, b3, b1, b2⟩
  refine SpecOn.seq (HoareOn.of_hoare (preCallB hfork hsize hsize' hsel hv hdep hcode
    hsz hszl hc10 hcU (by omega))) (HoareOn.seq hcall (HoareOn.of_hoare ?_))
  rintro evm ⟨caller, msg, child, hcal, -, hcs, hcss, hmg, hmc, hmt, hmtg, hmca, hmcode, hmdp, hmd, hmv,
    hmdep, hmst, hat⟩
  have hfwd : SendsVia message (upAddr state message) c r (dataB message) msg := by
    refine ⟨hmc, hmt, hmtg, hmca, hmcode, hmdp, ?_, hmv, hmdep, hmst⟩
    rw [hmd]; exact data_M2B _
  have hT := hcg caller msg child hcal hfwd ⟨hmg, hcs, hcss⟩
  have hB := size_M2B (addrArg message.data 0)
  by_cases he : child.error = none
  · simp only [he, Option.isNone_none, ↓reduceIte] at hat
    obtain ⟨after, hreach, hrun, hq⟩ := okTailB (fork := fork) (message := message)
      (state := (incorporateChild fork caller child).state)
      (substate := (incorporateChild fork caller child).substate)
      (U := upWord (storageAt state message.currentTarget 10)) (a := addrArg message.data 0)
      (size_outMemOf hB child.output) (mload_outMemOf hB (mload_M2B _) child.output)
      (x := BitVec.ofNat 256 (selector message.data))
      (gas := gas - preCostB fork c10 cU - ((callGasB fork gas c10 cU (callR substate state message r)).cost + 0) + child.gas)
      (by omega) evm hat
    refine ⟨after, Gas.reaches_toStep hreach, hrun, caller, msg, child, hcal, hfwd, hmg, hcs, hcss, fun _ => ?_,
      fun h => absurd he h⟩
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hq
    exact ⟨h1, h2, h3, by rw [h4]; omega, h5, h6⟩
  · have hz : child.error.isNone = false := by
      cases h : child.error
      · exact absurd h he
      · rfl
    simp only [hz, Bool.false_eq_true, ↓reduceIte] at hat
    obtain ⟨after, hreach, hrun, hq⟩ := failTail (fork := fork) (message := message)
      (state := (incorporateChild fork caller child).state)
      (substate := (incorporateChild fork caller child).substate) hfork (Or.inr (Or.inl rfl))
      (rest := [0x84, 0x70a08231,
        upWord (storageAt state message.currentTarget 10), 0, addrArg message.data 0, 0x05e7,
        BitVec.ofNat 256 (selector message.data)])
      (by simp)
      (gas := gas - preCostB fork c10 cU - ((callGasB fork gas c10 cU (callR substate state message r)).cost + 0) + child.gas)
      (by omega) evm hat
    refine ⟨after, Gas.reaches_toStep hreach, hrun, caller, msg, child, hcal, hfwd, hmg, hcs, hcss,
      fun h => absurd h he, fun _ => ?_⟩
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hq
    exact ⟨h1, h2, h3, by rw [h4]; omega, h5, h6⟩

/-- The specification of `balanceOf(who)` when deprecated, for every callee.

Hypotheses as `Deprecated.spec_dep` with selector 0x70a08231 and the gas of this path
(`preCostB`, `callGasB`, 126 gas after the price of the CALL). Then under every runner whose
ended messages meet `callee`, the run ends (or the runner aborts) in a stopped frame for which
there are a caller frame, a message `msg` and an ended frame `child` with
`callee caller msg child`, `msg` sent to `ua` along the route `r` (`SendsVia`) with data
`0x70a08231 ++ who` (`dataB`; `who` =
argument word 0 masked to 160 bits) and no value, and: if `child` ended with no error, the frame
returns the 32 bytes of the word at 0x60 after CALL wrote the first `min 32 (output size)` bytes
of `child`'s output there; otherwise it reverts with no output. -/
theorem spec_depB (hfork : .berlin ≤ fork)
    (hsize : 4 ≤ message.data.size) (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x70a08231) (hv : message.value = 0)
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0) {c : ByteArray}
    (hcode : state.getCode (state.getAccount (upAddr state message)).codeHash = .ok c)
    (hsz : 0 < c.size) (hszl : c.size < 2 ^ 256)
    {r : Route} (hroute : Routes fork state c r)
    (hdepth : message.depth + 1 ≤ STACK_DEPTH_LIMIT) {c10 cU : Bool}
    (hc10 : coldIn substate message.currentTarget 10 = c10)
    (hcU : decide (upAddr state message ∉ substate.accessedAddresses) = cU)
    {gas : Nat} (hg : preCostB fork c10 cU + 100 + callR substate state message r ≤ gas)
    (htail : 126 ≤ gas - preCostB fork c10 cU - (callGasB fork gas c10 cU (callR substate state message r)).cost)
    {callee : Evm fork Nat → Message fork → Evm fork Nat → Prop} :
    SpecUnder fork callee (At CODE message 0 [] .empty gas state substate)
      fun evm => ∃ caller msg child, callee caller msg child ∧
        SendsVia message (upAddr state message) c r (dataB message) msg ∧
        msg.gas = (callGasB fork gas c10 cU (callR substate state message r)).subCall ∧
        caller.state = (routeState ((callState state message).recordAccountRead
          (upAddr state message)) r).recordAccountRead message.currentTarget ∧
        caller.substate = routeSub { callSub substate state message with
          accessedAddresses :=
            (callSub substate state message).accessedAddresses.insert (upAddr state message) } r ∧
        (child.error = none →
          Halted false (wordBytes (resWord (outMemOf (M2B (addrArg message.data 0)) child.output)))
            (gas - preCostB fork c10 cU - (callGasB fork gas c10 cU (callR substate state message r)).cost + child.gas - 126)
            (incorporateChild fork caller child).state
            (incorporateChild fork caller child).substate evm) ∧
        (child.error ≠ none →
          Halted true .empty
            (gas - preCostB fork c10 cU - (callGasB fork gas c10 cU (callR substate state message r)).cost + child.gas - 25)
            (incorporateChild fork caller child).state
            (incorporateChild fork caller child).substate evm) := by
  apply SpecOn.toUnder
  apply spec_depB_g
  all_goals first | assumption | (intro _ _ _ _ _ _; omega)

/-- A callee assumption that pins the answer: every message sent to `ua` (code `c`) along the
route `r` with data `d` ends with no error and the output `o`. -/
def AnswersD (message : Message fork) (ua : EthLib.Base.Address) (c : ByteArray) (r : Route)
    (d o : ByteArray)
    (callee : Evm fork Nat → Message fork → Evm fork Nat → Prop) : Prop :=
  ∀ caller msg child, callee caller msg child → SendsVia message ua c r d msg →
    child.error = none ∧ child.output = o

/-- `balanceOf(who)` when deprecated, for a callee that answers `o` (at least 32 bytes) to the
forwarded call: the run returns the first word of `o`, with no error. -/
theorem spec_depB_answers (hfork : .berlin ≤ fork)
    (hsize : 4 ≤ message.data.size) (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x70a08231) (hv : message.value = 0)
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0) {c : ByteArray}
    (hcode : state.getCode (state.getAccount (upAddr state message)).codeHash = .ok c)
    (hsz : 0 < c.size) (hszl : c.size < 2 ^ 256)
    {r : Route} (hroute : Routes fork state c r)
    (hdepth : message.depth + 1 ≤ STACK_DEPTH_LIMIT) {c10 cU : Bool}
    (hc10 : coldIn substate message.currentTarget 10 = c10)
    (hcU : decide (upAddr state message ∉ substate.accessedAddresses) = cU)
    {gas : Nat} (hg : preCostB fork c10 cU + 100 + callR substate state message r ≤ gas)
    (htail : 126 ≤ gas - preCostB fork c10 cU - (callGasB fork gas c10 cU (callR substate state message r)).cost)
    {callee : Evm fork Nat → Message fork → Evm fork Nat → Prop} {o : ByteArray}
    (hans : AnswersD message (upAddr state message) c r (dataB message) o callee)
    (ho : 32 ≤ o.size) :
    SpecUnder fork callee (At CODE message 0 [] .empty gas state substate)
      fun evm => evm.error = none ∧ evm.output = wordBytes (loadWord o 0 32) := by
  refine (spec_depB hfork hsize hsize' hsel hv hdep hcode hsz hszl hroute hdepth hc10 hcU hg
    htail).consequence (fun _ h => h) ?_
  rintro evm ⟨caller, msg, child, hcal, hfwd, -, -, -, hok, -⟩
  obtain ⟨he, hout⟩ := hans caller msg child hcal hfwd
  obtain ⟨-, herr, hevm, -⟩ := hok he
  refine ⟨by simpa using herr, ?_⟩
  rw [hevm, hout, resWord_outMemOf (size_M2B _) ho]

/-- `balanceOf(who)` when deprecated, for a callee whose answer fails: the run reverts with no
output. -/
theorem spec_depB_fails (hfork : .berlin ≤ fork)
    (hsize : 4 ≤ message.data.size) (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x70a08231) (hv : message.value = 0)
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0) {c : ByteArray}
    (hcode : state.getCode (state.getAccount (upAddr state message)).codeHash = .ok c)
    (hsz : 0 < c.size) (hszl : c.size < 2 ^ 256)
    {r : Route} (hroute : Routes fork state c r)
    (hdepth : message.depth + 1 ≤ STACK_DEPTH_LIMIT) {c10 cU : Bool}
    (hc10 : coldIn substate message.currentTarget 10 = c10)
    (hcU : decide (upAddr state message ∉ substate.accessedAddresses) = cU)
    {gas : Nat} (hg : preCostB fork c10 cU + 100 + callR substate state message r ≤ gas)
    (htail : 126 ≤ gas - preCostB fork c10 cU - (callGasB fork gas c10 cU (callR substate state message r)).cost)
    {callee : Evm fork Nat → Message fork → Evm fork Nat → Prop}
    (hfail : ∀ caller msg child, callee caller msg child →
      SendsVia message (upAddr state message) c r (dataB message) msg → child.error ≠ none) :
    SpecUnder fork callee (At CODE message 0 [] .empty gas state substate)
      fun evm => evm.error = some .revert ∧ evm.output = .empty := by
  refine (spec_depB hfork hsize hsize' hsel hv hdep hcode hsz hszl hroute hdepth hc10 hcU hg
    htail).consequence (fun _ h => h) ?_
  rintro evm ⟨caller, msg, child, hcal, hfwd, -, -, -, -, hko⟩
  obtain ⟨-, herr, hevm, -⟩ := hko (hfail caller msg child hcal hfwd)
  exact ⟨by simpa using herr, hevm⟩

/-- EthLib's `RunsAs (routeCode c r) G Q` answers `o` to the messages sent with data `d` when every stopped frame
of `Q` has no error and the output `o`, those messages meet `G`, and `ua` is no precompile. -/
theorem answersD_runsAs {ua : EthLib.Base.Address} {c d o : ByteArray} {r : Route}
    {G : Message fork → State.TransactionState → Substate → Prop}
    {Q : Message fork → State.TransactionState → Substate → Evm fork Nat → Prop}
    (hQ : ∀ msg st ss stopped, Q msg st ss stopped → stopped.error = none ∧ stopped.output = o)
    (hG : ∀ msg st ss, SendsVia message ua c r d msg → G msg st ss)
    (hpre : Precompiles.isPrecompile fork (routeAddr ua r).toU256.toNat = false) :
    AnswersD message ua c r d o (RunsAs (routeCode c r) G Q) := by
  intro caller msg child hrun hfwd'
  have ⟨_, _, hmt, hmca, hmc, _, _, hmv, _, _⟩ := hfwd'
  obtain ⟨stopped, hq, hchild⟩ := hrun hmc (by simp [hmt]) (by simp [hmv])
    (by simp [precompileAddress, hmca, hpre]) (hG _ _ _ hfwd')
  obtain ⟨he, ho⟩ := hQ _ _ _ _ hq
  rw [hchild, rollbackOnError_of_error_eq_none he]
  exact ⟨he, ho⟩

/-- `balanceOf(who)` when deprecated, run by the interpreter's own message runner: for every
upgraded code `c` with a specification (as `meets_of_spec` takes it) whose stopped frames end with
no error and the output `o` (at least 32 bytes), the run returns the first word of `o`, or the
runner aborts. -/
theorem runFrame_depB_process (hfork : .berlin ≤ fork)
    (hsize : 4 ≤ message.data.size) (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x70a08231) (hv : message.value = 0)
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0) {c : ByteArray}
    (hcode : state.getCode (state.getAccount (upAddr state message)).codeHash = .ok c)
    (hsz : 0 < c.size) (hszl : c.size < 2 ^ 256)
    {r : Route} (hroute : Routes fork state c r)
    (hpre : Precompiles.isPrecompile fork (routeAddr (upAddr state message) r).toU256.toNat = false)
    (hdepth : message.depth + 1 ≤ STACK_DEPTH_LIMIT) {c10 cU : Bool}
    (hc10 : coldIn substate message.currentTarget 10 = c10)
    (hcU : decide (upAddr state message ∉ substate.accessedAddresses) = cU)
    {gas : Nat} (hg : preCostB fork c10 cU + 100 + callR substate state message r ≤ gas)
    (htail : 126 ≤ gas - preCostB fork c10 cU - (callGasB fork gas c10 cU (callR substate state message r)).cost)
    {G : Message fork → State.TransactionState → Substate → Prop}
    {Q : Message fork → State.TransactionState → Substate → Evm fork Nat → Prop}
    (hspec : ∀ msg st ss, msg.code = routeCode c r → G msg st ss →
      Spec fork (At (routeCode c r) msg 0 [] .empty msg.gas (startState fork msg st) ss)
        (Q msg st ss))
    (hG : ∀ msg st ss, SendsVia message (upAddr state message) c r (dataB message) msg → G msg st ss)
    {o : ByteArray} (hQ : ∀ msg st ss stopped, Q msg st ss stopped →
      stopped.error = none ∧ stopped.output = o) (ho : 32 ≤ o.size)
    {bound : Nat} {evm : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    (∃ stopped, runFrame (step fork) (step_decreases fork) bound (processRunner fork bound) evm
        within = .ok stopped ∧ stopped.error = none ∧
      stopped.output = wordBytes (loadWord o 0 32)) ∨
    ∃ e, runFrame (step fork) (step_decreases fork) bound (processRunner fork bound) evm
        within = .error e ∧ e.aborts = true :=
  (spec_depB_answers hfork hsize hsize' hsel hv hdep hcode hsz hszl hroute hdepth hc10 hcU
    hg htail (answersD_runsAs hQ hG hpre) ho).runFrame (meets_of_specAt hspec bound) start within

/-- The specification of `balanceOf(who)` when deprecated and the upgraded address has no code:
the run reverts with no output before any call. Gas `921 + price(slot 10) + price(address)`. -/
theorem spec_depBNoCode (hfork : .berlin ≤ fork)
    (hsize : 4 ≤ message.data.size) (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x70a08231) (hv : message.value = 0)
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0)
    (hcode : state.getCode (state.getAccount (upAddr state message)).codeHash = .ok .empty)
    {c10 cU : Bool} (hc10 : coldIn substate message.currentTarget 10 = c10)
    (hcU : decide (upAddr state message ∉ substate.accessedAddresses) = cU)
    {gas : Nat} (hg : 921 + slotCost c10 + extCost fork cU ≤ gas) :
    Spec fork (At CODE message 0 [] .empty gas state substate)
      (Halted true .empty (gas - (921 + slotCost c10 + extCost fork cU)) (callState state message)
        (callSub substate state message)) := by
  simp only [extCost] at hg ⊢
  have ht : tested (BitVec.ofNat 256 (selector message.data)) ENTRIES = 17 := by
    rw [hsel]; decide
  have hb : branch (BitVec.ofNat 256 (selector message.data)) 54 (entrySize 4 2) ENTRIES =
      1456 := by
    rw [hsel]; decide
  have h1 := dispatch (state := state) (substate := substate) hsize hsize' (gas := gas)
    (by rw [ht]; gas_ok)
  rw [ht, hb] at h1
  refine Gas.Triple.seqL h1 ?_
  step BalanceOf.entry hv (by gas_ok)
  step depSet hfork (Or.inr ⟨rfl, rfl⟩) (by simp) hdep hc10 (by gas_ok)
  step fwdArgsB (state := state) hfork (by simp only [addrArg, mask_mask]) (by simp)
    (by gas_ok)
  step At.reshape (g' := gas - (896 + slotCost c10)) rfl rfl (by gas_ok)
  refine (noCode (gas := gas - (896 + slotCost c10)) (st := readSlot state message.currentTarget 10)
    (ss := accessSlot substate message.currentTarget 10) (message := message)
    (M := M2B (addrArg message.data 0))
    (rest := [upWord (storageAt state message.currentTarget 10), 0, 0x60, 0x24, 0x60, 0x20, 0x84,
      0x70a08231, upWord (storageAt state message.currentTarget 10), 0, addrArg message.data 0,
      0x05e7, BitVec.ofNat 256 (selector message.data)]) hfork (Or.inr (Or.inl rfl)) (by simp)
    hcode hcU (by simp only [extCost]; gas_ok)).consequence (fun _ h => h) ?_
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  exact ⟨hr, he, ho, by rw [hgas]; simp only [extCost]; gas_ok, hs, hss⟩

end UsdtVerify.DeprecatedBalance
