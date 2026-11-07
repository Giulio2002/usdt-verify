import UsdtVerify.Functions.Transfer
import UsdtVerify.Functions.SafeMath
import EthLib.Execution.Proofs.Evm.Logic.Rules
import UsdtVerify.Spec.Write
import EthLib.Execution.Proofs.Evm.Logic.Log

/-!
# transfer(address,uint256): the blocks of the success path, from 9883

BasicToken's `transfer(_to, _value)` at 9883 (0x269b), as the bytecode runs it:

- 9883: the payload check `CALLDATASIZE ≥ 0x44` (two argument words) passes, JUMPI to 9910.
- 9910: `fee = mul(_value, basisPointsRate)` (slot 3), `fee = div(fee, 10000)`.
- 9951: `if (fee > maximumFee) fee = maximumFee` (slot 4, read again when the cap applies).
- 9969: `sendAmount = sub(_value, fee)`.
- 9988: `balances[msg.sender] = sub(balances[msg.sender], _value)` (mapping at slot 2).
- 10140: `balances[_to] = add(balances[_to], sendAmount)`, read after the first write.
- 10289: `if (fee > 0)` credit the owner and log (not covered here: the fee is 0).
- 10647: `Transfer(msg.sender, _to, sendAmount)`, LOG3, and back to 5785, then STOP at 1931.
-/

namespace UsdtVerify.TransferOk

open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts
open Transfer SafeMath

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate}

/-- At 9883, call data of at least 68 bytes passes the payload check. -/
theorem payloadOk (hlong : 68 ≤ message.data.size) (hsz : message.data.size < 2 ^ 256)
    {v a : U256} {rest : List U256} (hrest : rest.length ≤ 20) {gas : Nat} (hg : 54 ≤ gas)
    {M : ByteArray} :
    Gas.HoareG fork (At CODE message 9883 (v :: a :: rest) M gas state substate)
      (At CODE message 9910 (0x40 :: 0 :: 0 :: v :: a :: rest) M (gas - 54) state substate) := by
  have hlt : lessThan (BitVec.ofNat 256 message.data.size) (add (0x40 : U256) (0x04 : U256)) =
      0 := by
    have h68 : (add (0x40 : U256) (0x04 : U256)).toNat = 68 := by decide
    simp only [lessThan, h68, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsz]
    rw [if_neg (by omega)]
  step jumpdestR
  step pushR 1 (0 : U256)
  step dupR 0
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
  step pushR 2 (0x26b6 : U256)
  step jumpiR (by rw [hlt]; decide)
  exact (repc (by decide)).seq (Gas.reshapeG rfl rfl (by gas_ok))

/-- At 9910, the code reads `basisPointsRate` (slot 3) and calls `mul(_value, rate)`. -/
theorem feeCall (hfork : .berlin ≤ fork) {v a : U256} {rest : List U256}
    (hrest : rest.length ≤ 20) {c3 : Bool} (hc3 : coldIn substate message.currentTarget 3 = c3)
    {gas : Nat} (hg : 42 + slotCost c3 ≤ gas) {M : ByteArray} :
    Gas.HoareG fork (At CODE message 9910 (0x40 :: 0 :: 0 :: v :: a :: rest) M gas state substate)
      (At CODE message 10755 (storageAt state message.currentTarget 3 :: v :: 0x26d1 :: 0x2710 ::
        0x26df :: 0x40 :: 0 :: 0 :: v :: a :: rest) M (gas - (42 + slotCost c3))
        (readSlot state message.currentTarget 3) (accessSlot substate message.currentTarget 3)) := by
  step jumpdestR
  step pushR 2 (0x26df : U256)
  step pushR 2 (0x2710 : U256)
  step pushR 2 (0x26d1 : U256)
  step pushR 1 (0x03 : U256)
  step Gas.sloadG hfork (cold := c3) (by code_fact) (by code_fact) hc3 (by gas_ok)
  step dupR 7
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

/-- At 9937, back from `mul`, the code calls `div(product, 10000)`. -/
theorem divCall {m r : U256} {rest : List U256} (hrest : rest.length ≤ 20) {gas : Nat}
    (hg : 27 ≤ gas) {M : ByteArray} :
    Gas.HoareG fork (At CODE message 9937 (m :: 0x2710 :: r :: rest) M gas state substate)
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

/-- The fee after the cap: `maximumFee` when the raw fee is above it, else the raw fee. -/
abbrev capped (f0 maxFee : U256) : U256 := if f0.toNat > maxFee.toNat then maxFee else f0

/-- The extra gas of the cap: the second read of slot 4 (warm) and four opcodes. -/
abbrev capCost (f0 maxFee : U256) : Nat := if f0.toNat > maxFee.toNat then 108 else 0

/-- At 9951, with the raw fee `f0`, the code caps it by `maximumFee` (slot 4). -/
theorem capBlock (hfork : .berlin ≤ fork) {f0 v a : U256} {rest : List U256}
    (hrest : rest.length ≤ 20) {c4 : Bool} (hc4 : coldIn substate message.currentTarget 4 = c4)
    {gas : Nat}
    (hg : 31 + slotCost c4 + capCost f0 (storageAt state message.currentTarget 4) ≤ gas)
    {M : ByteArray} :
    Gas.HoareG fork (At CODE message 9951 (f0 :: 0x40 :: 0 :: 0 :: v :: a :: rest) M gas state substate)
      (At CODE message 9969
        (0x40 :: 0 :: capped f0 (storageAt state message.currentTarget 4) :: v :: a :: rest) M
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
  step pushR 2 (0x26f1 : U256)
  by_cases hcap : f0.toNat > (storageAt state message.currentTarget 4).toNat
  · simp only [capCost, capped, hcap, ite_true] at hg ⊢
    step jumpi0R (by simp only [greaterThan]; rw [if_pos hcap]; decide)
    step pushR 1 (0x04 : U256)
    step Gas.sloadG hfork (cold := false) (by code_fact) (by code_fact)
      (coldIn_accessSlot_self _ _ _) (by gas_ok)
    step swapR 2
    norm
    step popR
    exact restate (by decide) rfl rfl (by gas_ok) (readSlot_readSlot _ _ _)
      (accessSlot_accessSlot _ _ _)
  · simp only [capCost, capped, hcap, ite_false] at hg ⊢
    step jumpiR (by simp only [greaterThan]; rw [if_neg hcap]; decide)
    exact (repc (by decide)).seq (Gas.reshapeG rfl rfl (by gas_ok))

/-- At 9969, the code calls `sub(_value, fee)`. -/
theorem sendCall {fee v a : U256} {rest : List U256} (hrest : rest.length ≤ 20) {gas : Nat}
    (hg : 36 ≤ gas) {M : ByteArray} :
    Gas.HoareG fork (At CODE message 9969 (0x40 :: 0 :: fee :: v :: a :: rest) M gas state substate)
      (At CODE message 10976 (fee :: v :: 0x2704 :: 0x40 :: 0 :: fee :: v :: a :: rest) M
        (gas - 36) state substate) := by
  step jumpdestR
  step pushR 2 (0x2704 : U256)
  step dupR 3
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
  exact (repc (by decide)).seq (Gas.reshapeG rfl rfl (by gas_ok))

/-- The memory after a lookup in a mapping at base `b` from memory `M`: key word at 0, `b` at 32. -/
abbrev mapMem (M : ByteArray) (k b : U256) : ByteArray :=
  memoryWrite (memoryWrite M 0 (wordBytes k)) 32 (wordBytes b)

theorem size_mapMem {M : ByteArray} (hM : M.size = 96) (k b : U256) : (mapMem M k b).size = 96 := by
  rw [mapMem, size_memoryWrite, size_memoryWrite] <;> simp [size_memoryWrite, hM, size_wordBytes]

theorem ptr_mapMem {M : ByteArray} (hM : M.size = 96)
    (hptr : loadWord (memoryReadBytes M 64 32) 0 32 = 0x60) (k b : U256) :
    loadWord (memoryReadBytes (mapMem M k b) 64 32) 0 32 = 0x60 := by
  rw [mapMem, memoryReadBytes_memoryWrite_of_disjoint,
    memoryReadBytes_memoryWrite_of_disjoint, hptr] <;>
    simp [size_memoryWrite, hM, size_wordBytes]

/-- The key word of a mapping lookup: the word masked twice to 160 bits. -/
abbrev mkey (x : U256) : U256 := bitwiseAnd ADDR_MASK (bitwiseAnd ADDR_MASK x)

/-- The positions of the copies of the lookup tail used here: four in `transfer`, four in
`approve`, nine in `transferFrom`, two in the owner's credit of `transfer`. -/
abbrev HASH_PCS : List Nat := [10000, 10078, 10149, 10227, 8250, 8311, 8391, 8452,
  3807, 8654, 8715, 8899, 8960, 9053, 9131, 9202, 9280, 10340, 10451]

/-- The tail of a lookup in a mapping, at its copies in `HASH_PCS`: with the word `x`, 0
and the base `b` on the stack, it masks `x`, writes the key word at 0 and `b` at 32, and hashes
those 64 bytes. -/
theorem hashTail {p : Nat} (hp : p ∈ HASH_PCS) {x base : U256}
    {rest : List U256} (hrest : rest.length ≤ 900) {M : ByteArray} (hM : M.size = 96) {gas : Nat}
    (hg : 84 ≤ gas) :
    Gas.HoareG fork (At CODE message p (x :: 0 :: base :: rest) M gas state substate)
      (At CODE message (p + 58) (mapSlot ((bitwiseAnd ADDR_MASK (bitwiseAnd ADDR_MASK x))) base :: rest) (mapMem M ((bitwiseAnd ADDR_MASK (bitwiseAnd ADDR_MASK x))) base)
        (gas - 84) state substate) := by
  have hs1 : (memoryWrite M 0 (wordBytes ((bitwiseAnd ADDR_MASK (bitwiseAnd ADDR_MASK x))))).size = 96 := by
    rw [size_memoryWrite] <;> simp [hM, size_wordBytes]
  have hext1 : extendMemory M.size [((0 : U256), (32 : U256))] = ⟨0, 0⟩ := by rw [hM]; decide
  have hext2 : extendMemory (memoryWrite M 0 (wordBytes ((bitwiseAnd ADDR_MASK (bitwiseAnd ADDR_MASK x))))).size
      [((0x20 : U256), (32 : U256))] = ⟨0, 0⟩ := by rw [hs1]; decide
  have hext3 : extendMemory (mapMem M ((bitwiseAnd ADDR_MASK (bitwiseAnd ADDR_MASK x))) base).size [((0 : U256), (0x40 : U256))] =
      ⟨0, 0⟩ := by rw [size_mapMem hM]; decide
  have hk : keccak256Cost (0x40 : U256) = 42 := by decide
  have hread : memoryReadBytes (mapMem M ((bitwiseAnd ADDR_MASK (bitwiseAnd ADDR_MASK x))) base) 0 64 =
      wordBytes ((bitwiseAnd ADDR_MASK (bitwiseAnd ADDR_MASK x))) ++ wordBytes base := by
    have h := memoryReadBytes_memoryWrite_memoryWrite (memory := M) (a := wordBytes ((bitwiseAnd ADDR_MASK (bitwiseAnd ADDR_MASK x))))
      (b := wordBytes base) (s := 0) (by simp [hM, size_wordBytes])
    simpa [size_wordBytes, mapMem] using h
  simp only [HASH_PCS, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl
  all_goals
    step pushR 20 ADDR_MASK
    step binR 0x16 Local.instruction_and
    step pushR 20 ADDR_MASK
    step binR 0x16 Local.instruction_and
    step dupR 1
    step Gas.mstoreG (by code_fact) (by code_fact) (by rw [hext1]; gas_ok)
    step Gas.reshapeG (m' := memoryWrite M 0 (wordBytes ((bitwiseAnd ADDR_MASK (bitwiseAnd ADDR_MASK x))))) rfl
      (by rw [hext1, memoryExtend_zero]; rfl) (by rw [hext1] <;> gas_ok)
    step pushR 1 (0x20 : U256)
    step binR 0x01 instruction_add
    step swapR 0
    norm
    step dupR 1
    step Gas.reshapeG (s' := (0x20 : U256) :: base :: 0x20 :: rest) rfl rfl rfl
    step Gas.mstoreG (by code_fact) (by code_fact) (by rw [hext2]; gas_ok)
    step Gas.reshapeG (m' := mapMem M ((bitwiseAnd ADDR_MASK (bitwiseAnd ADDR_MASK x))) base) rfl (by rw [hext2, memoryExtend_zero]; rfl)
      (by rw [hext2] <;> gas_ok)
    step pushR 1 (0x20 : U256)
    step binR 0x01 instruction_add
    step pushR 1 (0 : U256)
    step Gas.reshapeG (s' := (0 : U256) :: 0x40 :: rest) rfl rfl rfl
    step Gas.keccak256G (by code_fact) (by code_fact) (by rw [hk, hext3]; gas_ok)
    exact restate (by decide)
      (by rw [hext3, memoryExtend_zero, show (0 : U256).toNat = 0 from rfl,
        show (0x40 : U256).toNat = 64 from rfl, hread]; rfl)
      (by rw [hext3, memoryExtend_zero]) (by rw [hext3, hk] <;> gas_ok) rfl rfl

/-- The slot of `balances[msg.sender]`: mapping base slot 2. -/
abbrev senderSlot (message : Message fork) : U256 := mapSlot (callerKey message) 2

/-- At 9988, the code keeps `sendAmount`, reads `balances[msg.sender]` and calls
`sub(balance, _value)`. -/
theorem debitCall (hfork : .berlin ≤ fork) {send fee v a : U256} {rest : List U256}
    (hrest : rest.length ≤ 800) {cS : Bool}
    (hcS : coldIn substate message.currentTarget (senderSlot message) = cS) {gas : Nat}
    (hg : 130 + slotCost cS ≤ gas) {M : ByteArray} (hM : M.size = 96) :
    Gas.HoareG fork (At CODE message 9988 (send :: 0x40 :: 0 :: fee :: v :: a :: rest) M gas state
        substate)
      (At CODE message 10976 (v :: storageAt state message.currentTarget (senderSlot message) ::
        0x2758 :: 0x40 :: send :: fee :: v :: a :: rest) (mapMem M (callerKey message) 2)
        (gas - (130 + slotCost cS)) (readSlot state message.currentTarget (senderSlot message))
        (accessSlot substate message.currentTarget (senderSlot message))) := by
  step jumpdestR
  step swapR 1
  norm
  step popR
  step pushR 2 (0x2758 : U256)
  step dupR 4
  step pushR 1 (0x02 : U256)
  step pushR 1 (0 : U256)
  step Gas.callerG (by code_fact) (by code_fact) (by gas_ok) (by stk_ok)
  at_pc 10000
  step hashTail (by decide) (by simp; omega) hM (by gas_ok)
  at_pc 10058
  step Gas.sloadG hfork (cold := cS) (by code_fact) (by code_fact) hcS (by gas_ok)
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

/-- At 10072, the code writes the new balance of the sender to `balances[msg.sender]`. -/
theorem debitStore (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam) {nb send fee v a : U256}
    {rest : List U256} (hrest : rest.length ≤ 800) (hstatic : message.isStatic = false)
    (hacc : hasAccount state message.currentTarget) {cS : Bool}
    (hcS : coldIn substate message.currentTarget (senderSlot message) = cS) {gas : Nat}
    (hstip : 2400 ≤ gas)
    (hg : 101 + sstoreCost fork (originalAt state message.currentTarget (senderSlot message))
      (storageAt state message.currentTarget (senderSlot message)) nb cS ≤ gas)
    {M : ByteArray} (hM : M.size = 96) :
    Gas.HoareG fork (At CODE message 10072 (nb :: 0x40 :: send :: fee :: v :: a :: rest) M gas state
        substate)
      (At CODE message 10140 (0x40 :: send :: fee :: v :: a :: rest)
        (mapMem M (callerKey message) 2)
        (gas - (101 + sstoreCost fork (originalAt state message.currentTarget (senderSlot message))
          (storageAt state message.currentTarget (senderSlot message)) nb cS))
        (writeSlot state message.currentTarget (senderSlot message) nb)
        (storeSub fork substate message.currentTarget (senderSlot message)
          (originalAt state message.currentTarget (senderSlot message))
          (storageAt state message.currentTarget (senderSlot message)) nb)) := by
  simp only [senderSlot, callerKey] at hcS hg ⊢
  step jumpdestR
  step pushR 1 (0x02 : U256)
  step pushR 1 (0 : U256)
  step Gas.callerG (by code_fact) (by code_fact) (by gas_ok) (by stk_ok)
  at_pc 10078
  step hashTail (by decide) (by simp; omega) hM (by gas_ok)
  at_pc 10136
  step dupR 1
  step swapR 0
  norm
  step Gas.sstoreWG hfork hglam (by code_fact) (by code_fact) hstatic hacc hcS (by gas_ok) (by gas_ok)
  step popR
  exact restate (by decide) rfl rfl (by gas_ok) rfl rfl

/-- The slot of `balances[_to]` for the recipient word `a`: mapping base slot 2. -/
abbrev recipientSlot (a : U256) : U256 := mapSlot (mkey a) 2

/-- At 10140, the code reads `balances[_to]` and calls `add(balance, sendAmount)`. -/
theorem creditCall (hfork : .berlin ≤ fork) {send fee v a : U256} {rest : List U256}
    (hrest : rest.length ≤ 800) {cT : Bool}
    (hcT : coldIn substate message.currentTarget (recipientSlot a) = cT) {gas : Nat}
    (hg : 125 + slotCost cT ≤ gas) {M : ByteArray} (hM : M.size = 96) :
    Gas.HoareG fork (At CODE message 10140 (0x40 :: send :: fee :: v :: a :: rest) M gas state
        substate)
      (At CODE message 11001 (send :: storageAt state message.currentTarget (recipientSlot a) ::
        0x27ed :: 0x40 :: send :: fee :: v :: a :: rest) (mapMem M (mkey a) 2)
        (gas - (125 + slotCost cT)) (readSlot state message.currentTarget (recipientSlot a))
        (accessSlot substate message.currentTarget (recipientSlot a))) := by
  step pushR 2 (0x27ed : U256)
  step dupR 2
  step pushR 1 (0x02 : U256)
  step pushR 1 (0 : U256)
  step dupR 8
  at_pc 10149
  step hashTail (by decide) (by simp; omega) hM (by gas_ok)
  at_pc 10207
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

/-- At 10221, the code writes the new balance of the recipient to `balances[_to]`; with a fee of
0 it skips the owner's credit and goes to the log at 10647. -/
theorem creditStore (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam) {nt send v a : U256}
    {rest : List U256} (hrest : rest.length ≤ 800) (hstatic : message.isStatic = false)
    (hacc : hasAccount state message.currentTarget) {cT : Bool}
    (hcT : coldIn substate message.currentTarget (recipientSlot a) = cT) {gas : Nat}
    (hstip : 2401 ≤ gas)
    (hg : 127 + sstoreCost fork (originalAt state message.currentTarget (recipientSlot a))
      (storageAt state message.currentTarget (recipientSlot a)) nt cT ≤ gas)
    {M : ByteArray} (hM : M.size = 96) :
    Gas.HoareG fork (At CODE message 10221 (nt :: 0x40 :: send :: 0 :: v :: a :: rest) M gas state
        substate)
      (At CODE message 10647 (0x40 :: send :: 0 :: v :: a :: rest) (mapMem M (mkey a) 2)
        (gas - (127 + sstoreCost fork (originalAt state message.currentTarget (recipientSlot a))
          (storageAt state message.currentTarget (recipientSlot a)) nt cT))
        (writeSlot state message.currentTarget (recipientSlot a) nt)
        (storeSub fork substate message.currentTarget (recipientSlot a)
          (originalAt state message.currentTarget (recipientSlot a))
          (storageAt state message.currentTarget (recipientSlot a)) nt)) := by
  simp only [recipientSlot, mkey] at hcT hg ⊢
  step jumpdestR
  step pushR 1 (0x02 : U256)
  step pushR 1 (0 : U256)
  step dupR 7
  at_pc 10227
  step hashTail (by decide) (by simp; omega) hM (by gas_ok)
  at_pc 10285
  step dupR 1
  step swapR 0
  norm
  step Gas.sstoreWG hfork hglam (by code_fact) (by code_fact) hstatic hacc hcT (by gas_ok) (by gas_ok)
  step popR
  step pushR 1 (0 : U256)
  step dupR 3
  step binR 0x11 Local.instruction_gt
  step unR 0x15 instruction_iszero
  step pushR 2 (0x2997 : U256)
  step jumpiR (by decide)
  exact restate (by decide) rfl rfl (by gas_ok) rfl rfl

/-- The topic of the event `Transfer(address,address,uint256)`. -/
abbrev TRANSFER_TOPIC : U256 :=
  0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef

/-- The log of `Transfer(from, to, value)` by the contract `c`: three topics and one data word. -/
abbrev transferLog (c : EthLib.Base.Address) (src dst value : U256) : Blocks.Log :=
  { address := c
    topics := [TRANSFER_TOPIC, src, dst].map U256.toBeBytes
    data := wordBytes value }

/-- At 10647, the code logs `Transfer(msg.sender, _to, sendAmount)` and returns to 5785. -/
theorem logBlock {send fee v a : U256} {rest : List U256} (hrest : rest.length ≤ 900)
    (hstatic : message.isStatic = false) {gas : Nat} (hg : 1850 ≤ gas) {M : ByteArray}
    (hM : M.size = 96) (hptr : loadWord (memoryReadBytes M 64 32) 0 32 = 0x60) :
    Gas.HoareG fork (At CODE message 10647 (0x40 :: send :: fee :: v :: a :: 0x1699 :: rest) M gas
        state substate)
      (At CODE message 5785 rest (M ++ wordBytes send) (gas - 1850) state
        { substate with logs := substate.logs.push (transferLog message.currentTarget
          (bitwiseAnd ADDR_MASK message.caller.toU256) (bitwiseAnd ADDR_MASK a) send) }) := by
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
  step dupR 4
  step pushR 20 ADDR_MASK
  step binR 0x16 Local.instruction_and
  step Gas.callerG (by code_fact) (by code_fact) (by gas_ok) (by stk_ok)
  step pushR 20 ADDR_MASK
  step binR 0x16 Local.instruction_and
  step pushR 32 TRANSFER_TOPIC
  step dupR 4
  step pushR 1 (0x40 : U256)
  step Gas.mloadG (by code_fact) (by code_fact) (by rw [hext0]; gas_ok)
  step Gas.reshapeG (s' := 0x60 :: send :: TRANSFER_TOPIC :: bitwiseAnd ADDR_MASK message.caller.toU256 ::
      bitwiseAnd ADDR_MASK a :: 0x40 :: send :: fee :: v :: a :: 0x1699 :: rest) (m' := M)
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
  step Gas.reshapeG (s' := 0x60 :: 0x80 :: TRANSFER_TOPIC :: bitwiseAnd ADDR_MASK message.caller.toU256 ::
      bitwiseAnd ADDR_MASK a :: 0x40 :: send :: fee :: v :: a :: 0x1699 :: rest)
    (m' := M ++ wordBytes send)
    (by rw [hext2, memoryExtend_zero, show (0x40 : U256).toNat = 64 from rfl, hread2, hptr]; rfl)
    (by rw [hext2, memoryExtend_zero]) (by rw [hext2])
  step dupR 0
  step swapR 1
  norm
  step binR 0x03 Local.instruction_sub
  step swapR 0
  norm
  step Gas.reshapeG (s' := 0x60 :: 0x20 :: ([TRANSFER_TOPIC, bitwiseAnd ADDR_MASK message.caller.toU256,
      bitwiseAnd ADDR_MASK a] ++ (0x40 :: send :: fee :: v :: a :: 0x1699 :: rest))) rfl rfl rfl
  step Gas.logG (n := 3) (byte := 0xa3) rfl (by code_fact) (by code_fact) rfl hstatic
    (by rw [hlog, hext3]; gas_ok)
  step Gas.reshapeG rfl (by rw [hext3, memoryExtend_zero]) (by rw [hlog, hext3])
  step popR
  step popR
  step popR
  step popR
  step popR
  step jumpR
  refine restate (by decide) rfl rfl (by gas_ok) rfl ?_
  rw [hext3, memoryExtend_zero, show (0x60 : U256).toNat = 96 from rfl,
    show (0x20 : U256).toNat = 32 from rfl, read_after hM _ (size_wordBytes send)]

/-- At 5785, the code returns to 1930, where it stops. -/
theorem endBlock {w a sel : U256} {gas : Nat} (hg : 15 ≤ gas) {M : ByteArray} :
    Gas.SpecG fork (At CODE message 5785 [w, a, 0x078a, sel] M gas state substate)
      (Halted false .empty (gas - 15) state substate) := by
  step jumpdestR
  step jumpdestR
  step popR
  step popR
  step jumpR
  step repc (pc' := 1930) (by decide)
  step jumpdestR
  refine (Gas.stopG (by code_fact) (by code_fact)).consequence (fun _ h => h) ?_
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  exact ⟨hr, he, ho, by rw [hgas]; gas_ok, hs, hss⟩

end UsdtVerify.TransferOk
