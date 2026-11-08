import UsdtVerify.Usdt.Proofs.Transfer

/-!
# approve(address,uint256)

The path of a call with selector 0x095ea7b3, no value, and the contract not deprecated.

- 610: the entry checks that the call has no value, reads argument word 0 masked to 160 bits
  (the spender) and argument word 1 (the value), and jumps to 2931 with return address 674.
- 2931: TetherToken's payload check (`onlyPayloadSize(2 * 32)`).
- 2955: the deprecation check (slot 10, byte 20); when it is 0, StandardToken's `approve` at 8206.
- 8206: the payload check again, then
  `require(!((_value != 0) && (allowed[msg.sender][_spender] != 0)))` (the allowance is read only
  when `_value != 0`; `allowed` is the nested mapping at base slot 5).
- 8384: `allowed[msg.sender][_spender] = _value`.
- 8514: `Approval(msg.sender, _spender, _value)` (LOG3), back to 3259, then STOP at 675.

`approve` returns no word: the run stops with STOP.
-/

namespace UsdtVerify.Approve

open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts
open Transfer TransferOk

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate}

/-- From 610, a call with no value goes to 2931 with the value, the spender and 674. -/
theorem entry (hv : message.value = 0) {x : U256} {gas : Nat} (hg : 98 ≤ gas) :
    Gas.HoareG fork (At CODE message 610 [x] MEM0 gas state substate)
      (At CODE message 2931 [wordArg message.data 1, addrArg message.data 0, 0x02a2, x] MEM0
        (gas - 98) state substate) := by
  step jumpdestR
  step Gas.callvalueG (by code_fact) (by code_fact) (by gas_ok) (by stk_ok)
  step unR 0x15 instruction_iszero
  step pushR 2 (0x026d : U256)
  step jumpiR (by simp [hv, isZero])
  step jumpdestR
  step pushR 2 (0x02a2 : U256)
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
  step pushR 2 (0x0b73 : U256)
  step jumpR
  exact (repc (by decide)).seq (Gas.reshapeG rfl rfl (by gas_ok))

/-- The payload check `CALLDATASIZE ≥ 0x44` at 2931 and at 8206, when it passes. -/
theorem payload {p d : Nat} (hp : (p = 2931 ∧ d = 2955) ∨ (p = 8206 ∧ d = 8230))
    (hlong : 68 ≤ message.data.size) (hsz : message.data.size < 2 ^ 256) {rest : List U256}
    (hrest : rest.length ≤ 900) {gas : Nat} (hg : 48 ≤ gas) {M : ByteArray} :
    Gas.HoareG fork (At CODE message p rest M gas state substate)
      (At CODE message d (0x40 :: rest) M (gas - 48) state substate) := by
  have hlt : lessThan (BitVec.ofNat 256 message.data.size) (add (0x40 : U256) (0x04 : U256)) =
      0 := by
    have h68 : (add (0x40 : U256) (0x04 : U256)).toNat = 68 := by decide
    simp only [lessThan, h68, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsz]
    rw [if_neg (by omega)]
  rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals
    step jumpdestR
    step pushR 1 (0x40 : U256)
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
    step pushAnyR 2
    step jumpiR (by rw [hlt]; decide)
    exact (repc (by decide)).seq (Gas.reshapeG rfl rfl (by gas_ok))

/-- At 2955, when byte 20 of slot 10 is 0 (not deprecated), the code goes to 3249. -/
theorem notDeprecated (hfork : .berlin ≤ fork) {rest : List U256} (hrest : rest.length ≤ 16)
    {c10 : Bool} (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    (hc10 : coldIn substate message.currentTarget 10 = c10) {gas : Nat}
    (hg : 106 + slotCost c10 ≤ gas) {M : ByteArray} :
    Gas.HoareG fork (At CODE message 2955 rest M gas state substate)
      (At CODE message 3249 rest M (gas - (106 + slotCost c10))
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
  step pushR 2 (0x0cb1 : U256)
  step jumpiR (isZero_flag_ne hdep)
  exact (repc (by decide)).seq (Gas.reshapeG rfl rfl (by gas_ok))

/-- At 3249, the code calls StandardToken's `approve` at 8206. -/
theorem toStandard {v s r x : U256} {gas : Nat} (hg : 21 ≤ gas) {M : ByteArray} :
    Gas.HoareG fork (At CODE message 3249 [0x40, v, s, r, x] M gas state substate)
      (At CODE message 8206 [v, s, 0x0cbb, 0x40, v, s, r, x] M (gas - 21) state substate) := by
  step jumpdestR
  step pushR 2 (0x0cbb : U256)
  step dupR 3
  step dupR 3
  step pushR 2 (0x200e : U256)
  step jumpR
  exact (repc (by decide)).seq (Gas.reshapeG rfl rfl (by gas_ok))

/-- The slot of `allowed[msg.sender][s]`: the nested mapping at base slot 5. -/
abbrev allowSlot (message : Message fork) (s : U256) : U256 :=
  mapSlot (mkey s) (mapSlot (mkey message.caller.toU256) 5)

/-- At 8230, with `_value = 0`, the check passes without reading the allowance. -/
theorem checkZero {s : U256} {rest : List U256} (hrest : rest.length ≤ 800) {gas : Nat}
    (hg : 55 ≤ gas) {M : ByteArray} :
    Gas.HoareG fork (At CODE message 8230 (0x40 :: 0 :: s :: rest) M gas state substate)
      (At CODE message 8384 (0x40 :: 0 :: s :: rest) M (gas - 55) state substate) := by
  step jumpdestR
  step pushR 1 (0 : U256)
  step dupR 2
  step binR 0x14 instruction_eq
  step unR 0x15 instruction_iszero
  step dupR 0
  step unR 0x15 instruction_iszero
  step pushR 2 (0x20b4 : U256)
  step jumpiR (by decide)
  at_pc 8372
  step jumpdestR
  step unR 0x15 instruction_iszero
  step unR 0x15 instruction_iszero
  step unR 0x15 instruction_iszero
  step pushR 2 (0x20c0 : U256)
  step jumpiR (by decide)
  exact (repc (by decide)).seq (Gas.reshapeG rfl rfl (by gas_ok))

/-- At 8230, with `_value ≠ 0` and `allowed[msg.sender][_spender] = 0`, the check passes after it
reads the allowance. -/
theorem checkNonzero (hfork : .berlin ≤ fork) {v s : U256} (hv0 : v ≠ 0) {rest : List U256}
    (hrest : rest.length ≤ 800) {cA : Bool}
    (hcA : coldIn substate message.currentTarget (allowSlot message s) = cA)
    (hzero : storageAt state message.currentTarget (allowSlot message s) = 0) {gas : Nat}
    (hg : 248 + slotCost cA ≤ gas) {M : ByteArray} (hM : M.size = 96) :
    Gas.HoareG fork (At CODE message 8230 (0x40 :: v :: s :: rest) M gas state substate)
      (At CODE message 8384 (0x40 :: v :: s :: rest)
        (mapMem (mapMem M (mkey message.caller.toU256) 5) (mkey s)
          (mapSlot (mkey message.caller.toU256) 5)) (gas - (248 + slotCost cA))
        (readSlot state message.currentTarget (allowSlot message s))
        (accessSlot substate message.currentTarget (allowSlot message s))) := by
  step jumpdestR
  step pushR 1 (0 : U256)
  step dupR 2
  step binR 0x14 instruction_eq
  step unR 0x15 instruction_iszero
  step dupR 0
  step unR 0x15 instruction_iszero
  step pushR 2 (0x20b4 : U256)
  step jumpi0R (by simp [equal, isZero]; exact hv0)
  step popR
  step pushR 1 (0 : U256)
  step pushR 1 (0x05 : U256)
  step pushR 1 (0 : U256)
  step Gas.callerG (by code_fact) (by code_fact) (by gas_ok) (by stk_ok)
  at_pc 8250
  step hashTail (by decide) (by simp; omega) hM (by gas_ok)
  at_pc 8308
  step pushR 1 (0 : U256)
  step dupR 5
  at_pc 8311
  step hashTail (by decide) (by simp; omega) (size_mapMem hM _ _) (by gas_ok)
  at_pc 8369
  step Gas.sloadG hfork (cold := cA) (by code_fact) (by code_fact) hcA (by gas_ok)
  step binR 0x14 instruction_eq
  step unR 0x15 instruction_iszero
  step jumpdestR
  step unR 0x15 instruction_iszero
  step unR 0x15 instruction_iszero
  step unR 0x15 instruction_iszero
  step pushR 2 (0x20c0 : U256)
  step jumpiR (by
    have h : storageAt state message.currentTarget (allowSlot message s) = 0 := hzero
    simp only [storageAt, allowSlot, mkey] at h
    rw [h]; decide)
  exact restate (by decide) rfl rfl (by gas_ok) rfl rfl

-- At 8384, from the `JUMPDEST` to the `SSTORE` of the allowance.
set_option hygiene false in
macro "store_pre" : tactic => `(tactic| (
  step jumpdestR
  step dupR 1
  step pushR 1 (0x05 : U256)
  step pushR 1 (0 : U256)
  step Gas.callerG (by code_fact) (by code_fact) (by gas_ok) (by stk_ok)
  at_pc 8391
  step hashTail (by decide) (by simp; omega) hM (by gas_ok)
  at_pc 8449
  step pushR 1 (0 : U256)
  step dupR 5
  at_pc 8452
  step hashTail (by decide) (by simp; omega) (size_mapMem hM _ _) (by gas_ok)
  at_pc 8510
  step dupR 1
  step swapR 0
  norm))

/-- At 8384, the code writes `_value` to `allowed[msg.sender][_spender]`. -/
theorem store (hfork : .berlin ≤ fork) {v s : U256}
    {rest : List U256} (hrest : rest.length ≤ 800) (hstatic : message.isStatic = false)
    (hacc : hasAccount state message.currentTarget) {cA : Bool}
    (hcA : coldIn substate message.currentTarget (allowSlot message s) = cA) {gas : Nat}
    (hstip : 2493 ≤ gas)
    (hg : 194 + Gas.writeCost fork (originalAt state message.currentTarget (allowSlot message s))
      (storageAt state message.currentTarget (allowSlot message s)) v cA ≤ gas)
    {M : ByteArray} (hM : M.size = 96) :
    Gas.HoareG fork (At CODE message 8384 (0x40 :: v :: s :: rest) M gas state substate)
      (At CODE message 8514 (0x40 :: v :: s :: rest)
        (mapMem (mapMem M (mkey message.caller.toU256) 5) (mkey s)
          (mapSlot (mkey message.caller.toU256) 5))
        (gas - (194 + Gas.writeCost fork (originalAt state message.currentTarget (allowSlot message s))
          (storageAt state message.currentTarget (allowSlot message s)) v cA))
        (writeSlot state message.currentTarget (allowSlot message s) v)
        (storeSub fork substate message.currentTarget (allowSlot message s)
          (originalAt state message.currentTarget (allowSlot message s))
          (storageAt state message.currentTarget (allowSlot message s)) v)) := by
  simp only [allowSlot, mkey] at hcA hg ⊢
  store_pre
  step Gas.sstoreWG hfork (by code_fact) (by code_fact) hstatic hacc hcA (by gas_ok) (by gas_ok)
  step popR
  exact restate (by decide) rfl rfl (by gas_ok) rfl rfl

/-- At 8384, when the `SSTORE` of the allowance cannot complete (`NoWrite`: a static frame, no
account for `C`, or at most 2300 gas left there): the run reaches it, and it is `Stuck`. -/
theorem storeBad {v s : U256} {rest : List U256} (hrest : rest.length ≤ 800) {gas : Nat}
    (hbad : Gas.NoWrite message state (gas - 192))
    (hg : 192 ≤ gas) {M : ByteArray} (hM : M.size = 96) :
    Gas.HoareG fork (At CODE message 8384 (0x40 :: v :: s :: rest) M gas state substate)
      Gas.Stuck := by
  store_pre
  exact Gas.sstoreNoWrite (by code_fact) (by code_fact) (hbad.le (by gas_ok))

/-- The topic of the event `Approval(address,address,uint256)`. -/
abbrev APPROVAL_TOPIC : U256 :=
  0x8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b925

/-- The log of `Approval(owner, spender, value)` by the contract `c`. -/
abbrev approvalLog (c : EthLib.Base.Address) (owner spender value : U256) : Blocks.Log :=
  { address := c
    topics := [APPROVAL_TOPIC, owner, spender].map U256.toBeBytes
    data := wordBytes value }

/-- At 8514, the code logs `Approval(msg.sender, _spender, _value)` and returns to 3259. -/
theorem logApproval {v s : U256} {rest : List U256} (hrest : rest.length ≤ 900)
    (hstatic : message.isStatic = false) {gas : Nat} (hg : 1845 ≤ gas) {M : ByteArray}
    (hM : M.size = 96) (hptr : loadWord (memoryReadBytes M 64 32) 0 32 = 0x60) :
    Gas.HoareG fork (At CODE message 8514 (0x40 :: v :: s :: 0x0cbb :: rest) M gas state substate)
      (At CODE message 3259 rest (M ++ wordBytes v) (gas - 1845) state
        { substate with logs := substate.logs.push (approvalLog message.currentTarget
          (bitwiseAnd ADDR_MASK message.caller.toU256) (bitwiseAnd ADDR_MASK s) v) }) := by
  have hext0 : extendMemory M.size [((0x40 : U256), (32 : U256))] = ⟨0, 0⟩ := by
    rw [hM]; decide
  have hext1 : extendMemory M.size [((0x60 : U256), (32 : U256))] = ⟨3, 32⟩ := by
    rw [hM]; decide
  have hsz : (M ++ wordBytes v).size = 128 := by
    rw [ByteArray.size_append, hM, size_wordBytes]
  have hext2 : extendMemory (M ++ wordBytes v).size [((0x40 : U256), (32 : U256))] =
      ⟨0, 0⟩ := by rw [hsz]; decide
  have hext3 : extendMemory (M ++ wordBytes v).size [((0x60 : U256), (0x20 : U256))] =
      ⟨0, 0⟩ := by rw [hsz]; decide
  have hmem1 : memoryWrite (memoryExtend M 32) (0x60 : U256).toNat (wordBytes v) =
      M ++ wordBytes v := by
    have h := memoryWrite_extend_end (memory := M) (value := wordBytes v)
    rwa [size_wordBytes, hM] at h
  have hread2 : memoryReadBytes (M ++ wordBytes v) 64 32 = memoryReadBytes M 64 32 := by
    simp only [memoryReadBytes, ByteArray.extract_append, hM]
    simp
  have hlog : logCost (3 : Fin 5).val (0x20 : U256) = 1756 := by decide
  step dupR 2
  step pushR 20 ADDR_MASK
  step binR 0x16 Local.instruction_and
  step Gas.callerG (by code_fact) (by code_fact) (by gas_ok) (by stk_ok)
  step pushR 20 ADDR_MASK
  step binR 0x16 Local.instruction_and
  step pushR 32 APPROVAL_TOPIC
  step dupR 4
  step pushR 1 (0x40 : U256)
  step Gas.mloadG (by code_fact) (by code_fact) (by rw [hext0]; gas_ok)
  step Gas.reshapeG (s' := 0x60 :: v :: APPROVAL_TOPIC :: bitwiseAnd ADDR_MASK message.caller.toU256 ::
      bitwiseAnd ADDR_MASK s :: 0x40 :: v :: s :: 0x0cbb :: rest) (m' := M)
    (by rw [hext0, memoryExtend_zero]; exact congrArg (· :: _) hptr)
    (by rw [hext0, memoryExtend_zero]) (by rw [hext0])
  step dupR 0
  step dupR 2
  step dupR 1
  step Gas.mstoreG (by code_fact) (by code_fact) (by rw [hext1]; gas_ok)
  step Gas.reshapeG (m' := M ++ wordBytes v) rfl (by rw [hext1]; exact hmem1) (by rw [hext1])
  step pushR 1 (0x20 : U256)
  step binR 0x01 instruction_add
  step swapR 1
  norm
  step popR
  step popR
  step pushR 1 (0x40 : U256)
  step Gas.mloadG (by code_fact) (by code_fact) (by rw [hext2]; gas_ok)
  step Gas.reshapeG (s' := 0x60 :: 0x80 :: APPROVAL_TOPIC :: bitwiseAnd ADDR_MASK message.caller.toU256 ::
      bitwiseAnd ADDR_MASK s :: 0x40 :: v :: s :: 0x0cbb :: rest)
    (m' := M ++ wordBytes v)
    (by rw [hext2, memoryExtend_zero, show (0x40 : U256).toNat = 64 from rfl, hread2, hptr]; rfl)
    (by rw [hext2, memoryExtend_zero]) (by rw [hext2])
  step dupR 0
  step swapR 1
  norm
  step binR 0x03 Local.instruction_sub
  step swapR 0
  norm
  step Gas.reshapeG (s' := 0x60 :: 0x20 :: ([APPROVAL_TOPIC, bitwiseAnd ADDR_MASK message.caller.toU256,
      bitwiseAnd ADDR_MASK s] ++ (0x40 :: v :: s :: 0x0cbb :: rest))) rfl rfl rfl
  step Gas.logG (n := 3) (byte := 0xa3) rfl (by code_fact) (by code_fact) rfl hstatic
    (by rw [hlog, hext3]; gas_ok)
  step Gas.reshapeG rfl (by rw [hext3, memoryExtend_zero]) (by rw [hlog, hext3])
  step popR
  step popR
  step popR
  step jumpR
  refine restate (by decide) rfl rfl (by gas_ok) rfl ?_
  rw [hext3, memoryExtend_zero, show (0x60 : U256).toNat = 96 from rfl,
    show (0x20 : U256).toNat = 32 from rfl, read_after hM _ (size_wordBytes v)]

/-- At 3259, the code returns to 674, where it stops. -/
theorem stopA {v s sel : U256} {gas : Nat} (hg : 17 ≤ gas) {M : ByteArray} :
    Gas.SpecG fork (At CODE message 3259 [0x40, v, s, 0x02a2, sel] M gas state substate)
      (Halted false .empty (gas - 17) state substate) := by
  step jumpdestR
  step jumpdestR
  step popR
  step popR
  step popR
  step jumpR
  step repc (pc' := 674) (by decide)
  step jumpdestR
  refine (Gas.stopG (by code_fact) (by code_fact)).consequence (fun _ h => h) ?_
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  exact ⟨hr, he, ho, by rw [hgas]; gas_ok, hs, hss⟩

end UsdtVerify.Approve
