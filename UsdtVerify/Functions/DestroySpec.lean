import UsdtVerify.Functions.Destroy
import UsdtVerify.Functions.BalanceOf
import UsdtVerify.Functions.SetParams

/-!
# destroyBlackFunds(address): the success path

After the `require` (7999) the code calls TetherToken's `balanceOf` getter at 4665 with return
address 8008 (`PUSH2 0x1f48 DUP3 PUSH2 0x1239 JUMP`). When not deprecated the getter reads
`balances[a]` (`BalanceOf.toLookup`, `lookup`, `back`, here with other words below). Then:

- 8008: `balances[a] := 0` (lookup tail at 8018, SSTORE at 8078);
- 8080: `_totalSupply -= dirtyFunds` (SLOAD and unchecked SUB, SSTORE at 8094);
- 8096: `DestroyedBlackFunds(a, dirtyFunds)` (LOG1, 64 bytes of data), back to 2486, STOP.

The deprecated case (the getter calls the upgraded contract) is not covered.
-/

namespace UsdtVerify.DestroySpec

open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts
open Transfer TransferOk Owner Admin BlackList Issue Destroy

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate}

/-- The flag test of the code is nonzero for a nonzero low byte. -/
theorem lowTest_ne {w : U256} (h : w.toNat % 256 ≠ 0) :
    isZero (isZero (bitwiseAnd (0xff : U256) (div w (exp (0x0100 : U256) (0 : U256))))) ≠ 0 := by
  have hd : div w (exp (0x0100 : U256) (0 : U256)) = w := by
    rw [exp0]; apply BitVec.eq_of_toNat_eq; simp [div]
  have hz : bitwiseAnd (0xff : U256) w ≠ 0 := by
    intro hz
    apply h
    have := congrArg BitVec.toNat hz
    simp only [bitwiseAnd, BitVec.toNat_and] at this
    rw [show BitVec.toNat (0xff : U256) = 2 ^ 8 - 1 by rfl, Nat.and_comm,
      Nat.and_two_pow_sub_one_eq_mod] at this
    simpa using this
  rw [hd]
  unfold isZero
  split
  · contradiction
  · decide

/-- The reads before the getter: slot 0 (owner) and `isBlackListed[a]`. -/
abbrev preState (state : State.TransactionState) (message : Message fork) :
    State.TransactionState :=
  readSlot (readSlot state message.currentTarget 0) message.currentTarget
    (listSlot (addrArg message.data 0))

abbrev preSub (substate : Substate) (message : Message fork) : Substate :=
  accessSlot (accessSlot substate message.currentTarget 0) message.currentTarget
    (listSlot (addrArg message.data 0))

/-- The memory after the lookup of `isBlackListed[a]`. -/
abbrev MEMB (message : Message fork) : ByteArray :=
  mapMem MEM0 (addrArg message.data 0) 6

/-- From pc 0, the owner with `a` blacklisted reaches the getter at 4665. -/
theorem toGetter (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xf3bdc228)
    (hv : message.value = 0) (hown : callerWord message = ownerOf state message.currentTarget)
    (hl : (storageAt state message.currentTarget (listSlot (addrArg message.data 0))).toNat % 256 ≠ 0)
    {c0 cL : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hcL : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget
      (listSlot (addrArg message.data 0)) = cL) {gas : Nat}
    (hg : 1086 + slotCost c0 + slotCost cL ≤ gas) :
    Hoare fork (At CODE message 0 [] .empty gas state substate)
      (At CODE message 4665 [addrArg message.data 0, 0x1f48, 0, addrArg message.data 0, 0x09b6,
          BitVec.ofNat 256 (selector message.data)]
        (MEMB message) (gas - (1086 + slotCost c0 + slotCost cL)) (preState state message)
        (preSub substate message)) := by
  have hexp : exponentBytes (0 : U256) = 0 := by decide
  have hk := mkey_addrArg0 message.data
  simp only [preState, preSub, MEMB, listSlot, hk] at hl hcL ⊢
  refine (toBody hsize hsize' hsel hv (by omega)).seq ?_
  step ownerOk hfork (by decide) (by simp) hc0 hown (by gas_ok)
  at_pc 7911
  step jumpdestR
  step pushR 1 (0x06 : U256)
  step pushR 1 (0 : U256)
  step dupR 3
  step hashTail7 (by decide) (by simp) size_MEM0 (by gas_ok)
  rw [hk]
  step pushR 1 (0 : U256)
  step swapR 0
  norm
  step sload hfork (cold := cL) (by code_fact) (by code_fact) hcL (by gas_ok)
  rw [getStorage_eq, storageAt_readSlot]
  step swapR 0
  norm
  step pushR 2 (0x0100 : U256)
  step Local.exp (Nat.le_trans (by decide) hfork) (by code_fact) (by code_fact) (by gas_ok)
  step swapR 0
  norm
  step binR 0x04 Local.instruction_div
  step pushR 1 (0xff : U256)
  step binR 0x16 Local.instruction_and
  step unR 0x15 instruction_iszero
  step unR 0x15 instruction_iszero
  step pushR 2 (0x1f3f : U256)
  step jumpiR (lowTest_ne hl)
  step jumpdestR
  step pushR 2 (0x1f48 : U256)
  step dupR 2
  step pushR 2 (0x1239 : U256)
  step jumpR
  exact restate (by decide) rfl rfl (by gas_ok) rfl rfl

/-- At 8008, back from the getter with `b = balances[a]`: `balances[a] := 0`. -/
theorem zeroBal (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam) {a b : U256}
    {rest : List U256} (hrest : rest.length ≤ 800) (hstatic : message.isStatic = false)
    (hacc : hasAccount state message.currentTarget)
    (hcB : coldIn substate message.currentTarget (mapSlot (mkey a) 2) = false) {M : ByteArray}
    (hM : M.size = 96) {gas : Nat} (hstip : 2409 ≤ gas)
    (hg : 110 + sstoreCost fork (originalAt state message.currentTarget (mapSlot (mkey a) 2))
      (storageAt state message.currentTarget (mapSlot (mkey a) 2)) 0 false ≤ gas) :
    Hoare fork (At CODE message 8008 (b :: 0 :: a :: rest) M gas state substate)
      (At CODE message 8080 (b :: a :: rest) (mapMem M (mkey a) 2)
        (gas - (110 + sstoreCost fork (originalAt state message.currentTarget (mapSlot (mkey a) 2))
          (storageAt state message.currentTarget (mapSlot (mkey a) 2)) 0 false))
        (writeSlot state message.currentTarget (mapSlot (mkey a) 2) 0)
        (storeSub fork substate message.currentTarget (mapSlot (mkey a) 2)
          (originalAt state message.currentTarget (mapSlot (mkey a) 2))
          (storageAt state message.currentTarget (mapSlot (mkey a) 2)) 0)) := by
  step jumpdestR
  step swapR 0
  norm
  step popR
  step pushR 1 (0 : U256)
  step pushR 1 (0x02 : U256)
  step pushR 1 (0 : U256)
  step dupR 4
  step hashTail7 (by decide) (by simp; omega) hM (by gas_ok)
  step dupR 1
  step swapR 0
  norm
  step sstoreW hfork hglam (by code_fact) (by code_fact) hstatic hacc hcB (by gas_ok) (by gas_ok)
  step popR
  exact restate (by decide) rfl rfl (by gas_ok) rfl rfl

/-- At 8080: `_totalSupply -= b` (unchecked), reading slot 1 first. -/
theorem subTotal (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam) {a b : U256}
    {rest : List U256} (hrest : rest.length ≤ 800) (hstatic : message.isStatic = false)
    (hacc : hasAccount state message.currentTarget) {c1 : Bool}
    (hc1 : coldIn substate message.currentTarget 1 = c1) {M : ByteArray} {gas : Nat}
    (hstip : 2332 + slotCost c1 ≤ gas)
    (hg : 33 + slotCost c1 + sstoreCost fork (originalAt state message.currentTarget 1)
      (storageAt state message.currentTarget 1) (sub (storageAt state message.currentTarget 1) b)
      false ≤ gas) :
    Hoare fork (At CODE message 8080 (b :: a :: rest) M gas state substate)
      (At CODE message 8096 (b :: a :: rest) M
        (gas - (33 + slotCost c1 + sstoreCost fork (originalAt state message.currentTarget 1)
          (storageAt state message.currentTarget 1)
          (sub (storageAt state message.currentTarget 1) b) false))
        (writeSlot state message.currentTarget 1 (sub (storageAt state message.currentTarget 1) b))
        (storeSub fork substate message.currentTarget 1 (originalAt state message.currentTarget 1)
          (storageAt state message.currentTarget 1)
          (sub (storageAt state message.currentTarget 1) b))) := by
  step dupR 0
  step pushR 1 (0x01 : U256)
  step pushR 1 (0 : U256)
  step dupR 2
  step dupR 2
  step sload hfork (cold := c1) (by code_fact) (by code_fact) hc1 (by gas_ok)
  rw [getStorage_eq]
  step binR 0x03 Local.instruction_sub
  step swapR 2
  norm
  step popR
  step popR
  step dupR 1
  step swapR 0
  norm
  step sstoreW hfork hglam (by code_fact) (by code_fact) hstatic (hasAccount_readSlot hacc)
    (coldIn_accessSlot_self _ _ _) (by gas_ok)
    (by rw [originalAt_readSlot, storageAt_readSlot]; gas_ok)
  rw [originalAt_readSlot, storageAt_readSlot, writeSlot_readSlot _ _ hacc, storeSub_accessSlot]
  step popR
  exact restate (by decide) rfl rfl (by gas_ok) rfl rfl

/-- The topic of `DestroyedBlackFunds(address,uint256)`. -/
abbrev DESTROY_TOPIC : U256 :=
  0x61e6e66b0d6339b2980aecc6ccc0039736791f0ccde9ed512e789a7fbdd698c6

/-- The log `DestroyedBlackFunds(a, b)` of the contract `c`: one topic, the two words as data. -/
abbrev destroyLog (c : EthLib.Base.Address) (a b : U256) : Blocks.Log :=
  { address := c, topics := [DESTROY_TOPIC].map U256.toBeBytes,
    data := wordBytes a ++ wordBytes b }

/-- At 8096: logs `DestroyedBlackFunds(a, b)` (the address word masked), returns to 2486 and
stops. -/
theorem logBlock {a b x : U256} (hstatic : message.isStatic = false) {M : ByteArray}
    (hM : M.size = 96) (hptr : loadWord (memoryReadBytes M 64 32) 0 32 = 0x60) {gas : Nat}
    (hg : 1368 ≤ gas) :
    Spec fork (At CODE message 8096 [b, a, 0x09b6, x] M gas state substate)
      (Local.Stopped (gas - 1368) state
        { substate with logs := substate.logs.push (destroyLog message.currentTarget (mkey a) b) }) := by
  have hext0 : extendMemory M.size [((0x40 : U256), (32 : U256))] = ⟨0, 0⟩ := by
    rw [hM]; decide
  have hext1 : extendMemory M.size [((0x60 : U256), (32 : U256))] = ⟨3, 32⟩ := by
    rw [hM]; decide
  have hs1 : (M ++ wordBytes (mkey a)).size = 128 := by
    rw [ByteArray.size_append, hM, size_wordBytes]
  have hext2 : extendMemory (M ++ wordBytes (mkey a)).size
      [((0x80 : U256), (32 : U256))] = ⟨3, 32⟩ := by rw [hs1]; decide
  have hs2 : (M ++ wordBytes (mkey a) ++ wordBytes b).size = 160 := by
    rw [ByteArray.size_append, hs1, size_wordBytes]
  have hext3 : extendMemory (M ++ wordBytes (mkey a) ++ wordBytes b).size
      [((0x40 : U256), (32 : U256))] = ⟨0, 0⟩ := by rw [hs2]; decide
  have hext4 : extendMemory (M ++ wordBytes (mkey a) ++ wordBytes b).size
      [((0x60 : U256), (0x40 : U256))] = ⟨0, 0⟩ := by rw [hs2]; decide
  have hmem1 : memoryWrite (memoryExtend M 32) (0x60 : U256).toNat (wordBytes (mkey a)) =
      M ++ wordBytes (mkey a) := by
    have h := memoryWrite_extend_end (memory := M) (value := wordBytes (mkey a))
    rwa [size_wordBytes, hM] at h
  have hmem2 : memoryWrite (memoryExtend (M ++ wordBytes (mkey a)) 32) (0x80 : U256).toNat
      (wordBytes b) = M ++ wordBytes (mkey a) ++ wordBytes b := by
    have h := memoryWrite_extend_end (memory := M ++ wordBytes (mkey a)) (value := wordBytes b)
    rwa [size_wordBytes, hs1] at h
  have hread : memoryReadBytes (M ++ wordBytes (mkey a) ++ wordBytes b) 64 32 =
      memoryReadBytes M 64 32 := by
    simp only [memoryReadBytes, ByteArray.extract_append, ByteArray.size_append, hM, size_wordBytes]
    simp
  have hlog : logCost (1 : Fin 5).val (0x40 : U256) = 1262 := by decide
  step push (n := 32) (word := DESTROY_TOPIC) (by decide) (by code_fact) (by code_fact)
    (decode_push 32 (by decide)) (by rw [pushData_CODE]; decide) (by gas_ok) (by stk_ok)
  step dupR 2
  step dupR 2
  step pushR 1 (0x40 : U256)
  step mload (by code_fact) (by code_fact) (by rw [hext0]; gas_ok)
  step reshape (s' := (0x60 : U256) :: _) (m' := M)
    (by rw [hext0, memoryExtend_zero]; exact congrArg (· :: _) hptr)
    (by rw [hext0, memoryExtend_zero]) (by rw [hext0])
  step dupR 0
  step dupR 3
  step pushR 20 ADDR_MASK
  step binR 0x16 Local.instruction_and
  step pushR 20 ADDR_MASK
  step binR 0x16 Local.instruction_and
  step dupR 1
  step mstore (by code_fact) (by code_fact) (by rw [hext1]; gas_ok)
  step reshape (m' := M ++ wordBytes (mkey a)) rfl (by rw [hext1]; exact hmem1) (by rw [hext1])
  step pushR 1 (0x20 : U256)
  step binR 0x01 instruction_add
  step dupR 2
  step dupR 1
  step reshape (s' := (0x80 : U256) :: _ :: 0x80 :: _) rfl rfl rfl
  step mstore (by code_fact) (by code_fact) (by rw [hext2]; gas_ok)
  step reshape (m' := M ++ wordBytes (mkey a) ++ wordBytes b) rfl
    (by rw [hext2]; exact hmem2) (by rw [hext2])
  step pushR 1 (0x20 : U256)
  step binR 0x01 instruction_add
  step swapR 2
  norm
  step popR
  step popR
  step popR
  step pushR 1 (0x40 : U256)
  step mload (by code_fact) (by code_fact) (by rw [hext3]; gas_ok)
  step reshape (s' := (0x60 : U256) :: _) (m' := M ++ wordBytes (mkey a) ++ wordBytes b)
    (by rw [hext3, memoryExtend_zero, show (0x40 : U256).toNat = 64 from rfl, hread, hptr])
    (by rw [hext3, memoryExtend_zero]) (by rw [hext3])
  step dupR 0
  step swapR 1
  norm
  step binR 0x03 Local.instruction_sub
  step swapR 0
  norm
  step reshape (s' := 0x60 :: 0x40 :: ([DESTROY_TOPIC] ++ [b, a, 0x09b6, x])) rfl rfl rfl
  step Logic.log (n := 1) (byte := 0xa1) rfl (by code_fact) (by code_fact) rfl hstatic
    (by rw [hlog, hext4]; gas_ok)
  step reshape rfl (by rw [hext4, memoryExtend_zero]) (by rw [hlog, hext4])
  step popR
  step popR
  step jumpR
  step jumpdestR
  refine (Local.stop (by code_fact) (by code_fact)).consequence (fun _ h => h) ?_
  rintro evm ⟨hr, he, hgas, hs, hss⟩
  refine ⟨hr, he, by rw [hgas]; gas_ok, hs, ?_⟩
  rw [hss, hext4, memoryExtend_zero, show (0x60 : U256).toNat = 96 from rfl,
    show (0x40 : U256).toNat = 64 from rfl, SetParams.read_after64 hM _ _ (size_wordBytes _) (size_wordBytes _)]

/-! ## The whole success path -/

/-- The slot of `balances[a]`. -/
abbrev balSlot (message : Message fork) : U256 := mapSlot (addrArg message.data 0) 2

/-- `dirtyFunds`: the word of `balances[a]`. -/
abbrev dirty (state : State.TransactionState) (message : Message fork) : U256 :=
  storageAt state message.currentTarget (balSlot message)

/-- The reads of the path: slot 0, `isBlackListed[a]`, slot 10, `balances[a]`. -/
abbrev readState (state : State.TransactionState) (message : Message fork) :
    State.TransactionState :=
  readSlot (readSlot (preState state message) message.currentTarget 10) message.currentTarget
    (balSlot message)

abbrev readSub (substate : Substate) (message : Message fork) : Substate :=
  accessSlot (accessSlot (preSub substate message) message.currentTarget 10) message.currentTarget
    (balSlot message)

/-- The state after `balances[a] := 0`. -/
abbrev state1 (state : State.TransactionState) (message : Message fork) :
    State.TransactionState :=
  writeSlot (readState state message) message.currentTarget (balSlot message) 0

/-- The state at the end: then `_totalSupply := T' - dirtyFunds` (`T'` read after the first
write; `T' = T` unless `balances[a]` is slot 1, see `destroy_effects`). -/
abbrev destroyState (state : State.TransactionState) (message : Message fork) :
    State.TransactionState :=
  writeSlot (state1 state message) message.currentTarget 1
    (sub (storageAt (state1 state message) message.currentTarget 1) (dirty state message))

/-- The price of the write of `balances[a]` (warm). -/
abbrev costB (fork : Fork) (state : State.TransactionState) (message : Message fork) : Nat :=
  sstoreCost fork (originalAt state message.currentTarget (balSlot message))
    (dirty state message) 0 false

/-- The price of the write of slot 1 (warm after its read). -/
abbrev costT (fork : Fork) (state : State.TransactionState) (message : Message fork) : Nat :=
  sstoreCost fork (originalAt state message.currentTarget 1)
    (storageAt (state1 state message) message.currentTarget 1)
    (sub (storageAt (state1 state message) message.currentTarget 1) (dirty state message)) false

/-- The substate at the end: both writes (accesses, refunds) and the log. -/
abbrev destroySub (fork : Fork) (substate : Substate) (state : State.TransactionState)
    (message : Message fork) : Substate :=
  { storeSub fork (storeSub fork (readSub substate message) message.currentTarget
        (balSlot message) (originalAt state message.currentTarget (balSlot message))
        (dirty state message) 0)
      message.currentTarget 1 (originalAt state message.currentTarget 1)
      (storageAt (state1 state message) message.currentTarget 1)
      (sub (storageAt (state1 state message) message.currentTarget 1) (dirty state message)) with
    logs := substate.logs.push
      (destroyLog message.currentTarget (addrArg message.data 0) (dirty state message)) }

/-- The specification of a successful `destroyBlackFunds(a)`.

Hypotheses: Berlin ≤ fork < Glamsterdam; a frame that may write, of an existing account `C`;
call data of 4 to 2^256 - 1 bytes with selector 0xf3bdc228; no value; the caller is the owner;
`a` (argument word 0 masked to 160 bits) blacklisted (the low byte of `isBlackListed[a]` is not
0); not deprecated (byte 20 of slot 10 is 0); enough gas, and more than 2300 left at each SSTORE.

Then the run stops normally after: `balances[a] := 0`, then `_totalSupply := T' - d` where `d`
is the old word of `balances[a]` (unchecked subtraction); one log `DestroyedBlackFunds(a, d)`
(topic 0x61e6e66b…, data the address word and `d`). Gas left:
`gas - (2865 + prices of the reads of slots 0, isBlackListed[a], 10, balances[a], 1 + prices of
the two writes)`. -/
theorem spec (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    (hstatic : message.isStatic = false) (hacc : hasAccount state message.currentTarget)
    (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xf3bdc228)
    (hv : message.value = 0) (hown : callerWord message = ownerOf state message.currentTarget)
    (hl : (storageAt state message.currentTarget (listSlot (addrArg message.data 0))).toNat % 256 ≠ 0)
    (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    {c0 cL c10 cB c1 : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hcL : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget
      (listSlot (addrArg message.data 0)) = cL)
    (hc10 : coldIn (preSub substate message) message.currentTarget 10 = c10)
    (hcB : coldIn (accessSlot (preSub substate message) message.currentTarget 10)
      message.currentTarget (balSlot message) = cB)
    (hc1 : coldIn (readSub substate message) message.currentTarget 1 = c1)
    {gas : Nat}
    (hstip1 : 3763 + slotCost c0 + slotCost cL + slotCost c10 + slotCost cB ≤ gas)
    (hstip2 : 3796 + slotCost c0 + slotCost cL + slotCost c10 + slotCost cB +
      costB fork state message + slotCost c1 ≤ gas)
    (hg : 2865 + slotCost c0 + slotCost cL + slotCost c10 + slotCost cB + slotCost c1 +
      costB fork state message + costT fork state message ≤ gas) :
    Spec fork (At CODE message 0 [] .empty gas state substate)
      (Local.Stopped (gas - (2865 + slotCost c0 + slotCost cL + slotCost c10 + slotCost cB +
          slotCost c1 + costB fork state message + costT fork state message))
        (destroyState state message) (destroySub fork substate state message)) := by
  simp only [costB, costT, dirty, balSlot, state1] at hstip2 hg ⊢
  have hkey : BalanceOf.key (addrArg message.data 0) = addrArg message.data 0 :=
    mkey_addrArg0 message.data
  have hk := mkey_addrArg0 message.data
  have hacc1 : hasAccount (readState state message) message.currentTarget :=
    hasAccount_readSlot (hasAccount_readSlot (hasAccount_readSlot (hasAccount_readSlot hacc)))
  have hM1 : (MEMB message).size = 96 := size_mapMem size_MEM0 _ _
  have hp1 : loadWord (memoryReadBytes (MEMB message) 64 32) 0 32 = 0x60 :=
    ptr_mapMem size_MEM0 mload_MEM0 _ _
  refine Spec.seq (toGetter hfork hsize hsize' hsel hv hown hl hc0 hcL (by omega)) ?_
  step depCheck hfork (Or.inr (Or.inl ⟨rfl, rfl⟩)) (by simp)
    (by simp only [preState, storageAt_readSlot]; exact hdep) hc10 (by gas_ok)
  step BalanceOf.toLookup (by simp) (by gas_ok)
  step BalanceOf.lookup hfork (by simp) hM1 (cB := cB) (by rw [hkey]; exact hcB) (by gas_ok)
  rw [hkey, storageAt_readSlot, storageAt_readSlot, storageAt_readSlot]
  step BalanceOf.back (Or.inr rfl) (by gas_ok)
  step zeroBal hfork hglam (by simp) hstatic hacc1 (by rw [hk]; exact coldIn_accessSlot_self _ _ _)
    (BalanceOf.size_lookMem hM1 _) (by gas_ok)
    (by simp only [hk, originalAt_readSlot, storageAt_readSlot]; gas_ok)
  simp only [hk, originalAt_readSlot, storageAt_readSlot]
  step subTotal hfork hglam (by simp) hstatic (hasAccount_writeSlot hacc1) (c1 := c1)
    (by rw [TransferFee.coldIn_storeSub', accessSlot_accessSlot]; exact hc1) (by gas_ok)
    (by rw [originalAt_writeSlot hacc1]; simp only [originalAt_readSlot]; gas_ok)
  rw [originalAt_writeSlot hacc1]
  simp only [originalAt_readSlot]
  refine (logBlock hstatic (size_mapMem (BalanceOf.size_lookMem hM1 _) _ _)
    (ptr_mapMem (BalanceOf.size_lookMem hM1 _) (ptr_mapMem hM1 hp1 _ _) _ _)
    (by gas_ok)).consequence (fun _ h => h) ?_
  rintro evm ⟨hr, he, hgas, hs, hss⟩
  refine ⟨hr, he, by rw [hgas]; gas_ok, hs, ?_⟩
  rw [hss, hk]

/-- After `destroyBlackFunds(a)`, when `balances[a]` is not slot 1: `balances[a]` is 0,
`_totalSupply` is `T - d` as a word (`d` the old balance; the subtraction is unchecked, and is
`T - d` as numbers when `d ≤ T`), and every other slot is unchanged. -/
theorem destroy_effects (hacc : hasAccount state message.currentTarget)
    (hB1 : balSlot message ≠ 1) :
    storageAt (destroyState state message) message.currentTarget (balSlot message) = 0 ∧
    storageAt (destroyState state message) message.currentTarget 1 =
      sub (storageAt state message.currentTarget 1) (dirty state message) ∧
    ((dirty state message).toNat ≤ (storageAt state message.currentTarget 1).toNat →
      (storageAt (destroyState state message) message.currentTarget 1).toNat =
        (storageAt state message.currentTarget 1).toNat - (dirty state message).toNat) ∧
    ∀ n, n ≠ balSlot message → n ≠ 1 →
      storageAt (destroyState state message) message.currentTarget n =
        storageAt state message.currentTarget n := by
  have hacc1 : hasAccount (readState state message) message.currentTarget :=
    hasAccount_readSlot (hasAccount_readSlot (hasAccount_readSlot (hasAccount_readSlot hacc)))
  have h1 : storageAt (state1 state message) message.currentTarget 1 =
      storageAt state message.currentTarget 1 := by
    rw [state1, storageAt_writeSlot_of_ne hacc1 (Ne.symm hB1)]
    simp only [storageAt_readSlot]
  have hT : storageAt (destroyState state message) message.currentTarget 1 =
      sub (storageAt state message.currentTarget 1) (dirty state message) := by
    rw [destroyState, storageAt_writeSlot_self (hasAccount_writeSlot hacc1), h1]
  refine ⟨?_, hT, ?_, ?_⟩
  · rw [destroyState, storageAt_writeSlot_of_ne (hasAccount_writeSlot hacc1) hB1,
      storageAt_writeSlot_self hacc1]
  · intro hle
    rw [hT, IssueSpec.toNat_sub' hle]
  · intro n hnB hn1
    rw [destroyState, storageAt_writeSlot_of_ne (hasAccount_writeSlot hacc1) hn1,
      storageAt_writeSlot_of_ne hacc1 hnB]
    simp only [storageAt_readSlot]

/-- The loop of the interpreter runs a successful `destroyBlackFunds(a)` to `spec`'s end. -/
theorem runFrame_spec (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    (hstatic : message.isStatic = false) (hacc : hasAccount state message.currentTarget)
    (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xf3bdc228)
    (hv : message.value = 0) (hown : callerWord message = ownerOf state message.currentTarget)
    (hl : (storageAt state message.currentTarget (listSlot (addrArg message.data 0))).toNat % 256 ≠ 0)
    (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    {c0 cL c10 cB c1 : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hcL : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget
      (listSlot (addrArg message.data 0)) = cL)
    (hc10 : coldIn (preSub substate message) message.currentTarget 10 = c10)
    (hcB : coldIn (accessSlot (preSub substate message) message.currentTarget 10)
      message.currentTarget (balSlot message) = cB)
    (hc1 : coldIn (readSub substate message) message.currentTarget 1 = c1)
    {gas : Nat}
    (hstip1 : 3763 + slotCost c0 + slotCost cL + slotCost c10 + slotCost cB ≤ gas)
    (hstip2 : 3796 + slotCost c0 + slotCost cL + slotCost c10 + slotCost cB +
      costB fork state message + slotCost c1 ≤ gas)
    (hg : 2865 + slotCost c0 + slotCost cL + slotCost c10 + slotCost cB + slotCost c1 +
      costB fork state message + costT fork state message ≤ gas) {bound : Nat}
    {runChild : MessageRunner fork Nat bound} {evm : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    ∃ stopped, runFrame (step fork) (step_decreases fork) bound runChild evm within =
      .ok stopped ∧
      Local.Stopped (gas - (2865 + slotCost c0 + slotCost cL + slotCost c10 + slotCost cB +
          slotCost c1 + costB fork state message + costT fork state message))
        (destroyState state message) (destroySub fork substate state message) stopped :=
  (spec hfork hglam hstatic hacc hsize hsize' hsel hv hown hl hdep hc0 hcL hc10 hcB hc1 hstip1
    hstip2 hg).runFrame start within

end UsdtVerify.DestroySpec
