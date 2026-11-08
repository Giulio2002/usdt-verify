import UsdtVerify.Usdt.Refill.ChainTransfer

/-!
# transfer with a fee over the EIP-8037 meter: the exact condition and gas (round 43)

The success path of `transfer(a, v)` with a fee above 0 writes three slots: `balances[msg.sender]`,
`balances[_to]` and `balances[owner]`. It is split at the three SSTOREs (`feeW1`, `feeW2`,
`feeW3`, `feePost`), and `Complete.exactS_write` is applied three times, then
`Complete.exactS_halt`.

- `transferFee_sgm`: from a frame with any meter, for any gas bound and message runner, under the
  hypotheses of `spec_fee` except the gas, the run ends with no error if and only if the chain
  condition holds, and every run that ends with no error has the state and substate of `spec_fee`
  and `gasLeft + feeCost = gas` plus the three bumps.

No hypothesis on refills or on the reservoir.
-/

namespace UsdtVerify.TransferFee
open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts
open Transfer SafeMath TransferOk TransferFrom
open Complete (wBump wSgm wOk wMeter)
variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate}

/-- At 10412: from the `JUMPDEST` to the `SSTORE` of `balances[owner]` (10511). -/
theorem ownerToW (hfork : .berlin ≤ fork) {w0 : U256}
    (hw0 : storageAt state message.currentTarget 0 = w0)
    {no send fee v a : U256} {rest : List U256} (hrest : rest.length ≤ 800)
    (hc0 : coldIn substate message.currentTarget 0 = false) {gas : Nat}
    (hg : 236 ≤ gas) {M : ByteArray} (hM : M.size = 96) :
    Gas.HoareG fork (At CODE message 10412 (no :: 0x40 :: send :: fee :: v :: a :: rest) M gas state
        substate)
      (At CODE message 10511 (ownerSlot w0 :: no :: no :: 0x40 :: send :: fee :: v :: a :: rest)
        (mapMem M (mkey (ownerKey w0)) 2) (gas - 236) (readSlot state message.currentTarget 0)
        (accessSlot substate message.currentTarget 0)) := by
  have hexp : exponentBytes (0 : U256) = 0 := by decide
  step jumpdestR
  step pushR 1 (0x02 : U256)
  step pushR 1 (0 : U256)
  step dupR 0
  step pushR 1 (0 : U256)
  step swapR 0
  norm
  step Gas.sloadG hfork (cold := false) (by code_fact) (by code_fact) hc0 (by gas_ok)
  rw [show state.getStorage message.currentTarget (U256.toBeBytes 0) = w0 from hw0]
  step swapR 0
  norm
  step pushR 2 (0x0100 : U256)
  step Gas.expLG (Nat.le_trans (by decide) hfork) (by code_fact) (by code_fact) (by gas_ok)
  step swapR 0
  norm
  step binR 0x04 Local.instruction_div
  step pushR 20 ADDR_MASK
  step binR 0x16 Local.instruction_and
  at_pc 10451
  step hashTail (by decide) (by simp; omega) hM (by gas_ok)
  at_pc 10509
  step dupR 1
  step swapR 0
  norm
  exact restate (by decide) rfl rfl (by gas_ok) rfl rfl

/-- From 9883 (fee above 0) to the `SSTORE` of `balances[msg.sender]` (10138). -/
theorem feeW1 (hfork : .berlin ≤ fork)
    (hlong : 68 ≤ message.data.size) (hsz : message.data.size < 2 ^ 256)
    {v a sel : U256} {M : ByteArray} (hM : M.size = 96)
    (hov : v.toNat * (storageAt state message.currentTarget 3).toNat < 2 ^ 256)
    (hfv : (feeOf state message v).toNat ≤ v.toNat)
    (hbal : v.toNat ≤ (balS state message).toNat)
    {c3 c4 cS : Bool} (hc3 : coldIn substate message.currentTarget 3 = c3)
    (hc4 : coldIn (accessSlot substate message.currentTarget 3) message.currentTarget 4 = c4)
    (hcS : coldIn (accessSlot (accessSlot substate message.currentTarget 3) message.currentTarget 4)
      message.currentTarget (senderSlot message) = cS)
    {gas : Nat}
    (hg : 629 + slotCost c3 + slotCost c4 + slotCost cS + mulCost v +
      capCost (rawFee state message v) (storageAt state message.currentTarget 4) ≤ gas) :
    Gas.HoareG fork (At CODE message 9883 [v, a, 0x1699, v, a, 0x078a, sel] M gas state substate)
      (At CODE message 10138 (senderSlot message :: sub (balS state message) v ::
          sub (balS state message) v :: 0x40 :: sendOf state message v :: feeOf state message v ::
          v :: a :: [0x1699, v, a, 0x078a, sel])
        (mapMem (mapMem M (callerKey message) 2) (callerKey message) 2)
        (gas - (629 + slotCost c3 + slotCost c4 + slotCost cS + mulCost v +
          capCost (rawFee state message v) (storageAt state message.currentTarget 4)))
        (reads3 state message) (access3 substate message)) := by
  simp only [rawFee, feeOf, balS, reads3, sendOf] at hg hfv hbal ⊢
  step payloadOk hlong hsz (by simp) (by gas_ok)
  step feeCall hfork (by simp) hc3 (by gas_ok)
  step mulBlock (by simp) (by valid_dest) hov (by gas_ok)
  at_pc 9937
  step divCall (by simp) (by gas_ok)
  step divBlock (by simp) (by valid_dest) (by decide) (by gas_ok)
  at_pc 9951
  step capBlock hfork (by simp) hc4 (by simp only [storageAt_readSlot]; gas_ok)
  simp only [storageAt_readSlot]
  step sendCall (by simp) (by gas_ok)
  step subBlock (by simp) (by valid_dest) hfv (by gas_ok)
  at_pc 9988
  step debitCall hfork (by simp) hcS (by gas_ok) hM
  simp only [storageAt_readSlot]
  step subBlock (by simp) (by valid_dest) hbal (by gas_ok)
  at_pc 10072
  refine Triple.seq (debitToW (by simp) (by gas_ok) (size_mapMem hM _ _)) ?_
  exact restate rfl rfl rfl (by gas_ok) rfl rfl

/-- From the `POP` at 10139 after the sender's `SSTORE` to the `SSTORE` of `balances[_to]`
(10287), with `send` the amount after the fee. -/
theorem feeW2 (hfork : .berlin ≤ fork) {nb send fee v a sel : U256} {M : ByteArray}
    (hM : M.size = 96)
    (hto : (storageAt state message.currentTarget (recipientSlot a)).toNat + send.toNat < 2 ^ 256)
    {cT : Bool} (hcT : coldIn substate message.currentTarget (recipientSlot a) = cT) {gas : Nat}
    (hg : 308 + slotCost cT ≤ gas) :
    Gas.HoareG fork (At CODE message 10139 [nb, 0x40, send, fee, v, a, 0x1699, v, a, 0x078a, sel] M
        gas state substate)
      (At CODE message 10287 (recipientSlot a ::
          add (storageAt state message.currentTarget (recipientSlot a)) send ::
          add (storageAt state message.currentTarget (recipientSlot a)) send ::
          [0x40, send, fee, v, a, 0x1699, v, a, 0x078a, sel])
        (mapMem (mapMem M (mkey a) 2) (mkey a) 2) (gas - (308 + slotCost cT))
        (readSlot state message.currentTarget (recipientSlot a))
        (accessSlot substate message.currentTarget (recipientSlot a))) := by
  refine Triple.seq (Gas.Triple.seqL popR (restate (pc' := 10140) (by decide) rfl rfl
    (g' := gas - 2) (by gas_ok) rfl rfl)) ?_
  step creditCall hfork (by simp) (cT := cT) hcT (by gas_ok) hM
  step addBlock (by simp) (by valid_dest) (by simpa using hto) (by gas_ok)
  at_pc 10221
  refine Triple.seq (creditToW (by simp) (by gas_ok) (size_mapMem hM _ _)) ?_
  exact restate rfl rfl rfl (by gas_ok) rfl rfl

/-- From the `POP` at 10288 after the recipient's `SSTORE` (fee above 0) to the `SSTORE` of
`balances[owner]` (10511). -/
theorem feeW3 (hfork : .berlin ≤ fork) {nt send fee v a sel : U256} (hfee : fee ≠ 0)
    {M : ByteArray} (hM : M.size = 96)
    (hc0 : coldIn substate message.currentTarget 0 = false) {cO : Bool}
    (hcO : coldIn substate message.currentTarget (ownerSlotOf state message.currentTarget) = cO)
    (hown : (balOf state message.currentTarget).toNat + fee.toNat < 2 ^ 256) {gas : Nat}
    (hg : 605 + slotCost cO ≤ gas) :
    Gas.HoareG fork (At CODE message 10288 [nt, 0x40, send, fee, v, a, 0x1699, v, a, 0x078a, sel] M
        gas state substate)
      (At CODE message 10511 (ownerSlotOf state message.currentTarget ::
          add (balOf state message.currentTarget) fee :: add (balOf state message.currentTarget) fee ::
          [0x40, send, fee, v, a, 0x1699, v, a, 0x078a, sel])
        (mapMem (mapMem M (mkey (ownerKey (storageAt state message.currentTarget 0))) 2)
          (mkey (ownerKey (storageAt state message.currentTarget 0))) 2)
        (gas - (605 + slotCost cO))
        (readSlot (readSlot (readSlot state message.currentTarget 0) message.currentTarget
          (ownerSlotOf state message.currentTarget)) message.currentTarget 0)
        (accessSlot (accessSlot (accessSlot substate message.currentTarget 0) message.currentTarget
          (ownerSlotOf state message.currentTarget)) message.currentTarget 0)) := by
  have hpos : 0 < fee.toNat := by
    rcases Nat.eq_zero_or_pos fee.toNat with h | h
    · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h)) hfee
    · exact h
  simp only [ownerSlotOf, balOf] at hcO hown ⊢
  step popR
  step pushR 1 (0 : U256)
  step dupR 3
  step binR 0x11 Local.instruction_gt
  step unR 0x15 instruction_iszero
  step pushR 2 (0x2997 : U256)
  step jumpi0R (by simp [greaterThan, isZero, hpos])
  at_pc 10298
  step ownerCall (cO := cO) hfork rfl (by simp) hc0 (by rw [coldIn_accessSlot_of_warm hc0]; exact hcO)
    (by gas_ok) hM
  step addBlock (by simp) (by valid_dest) hown (by gas_ok)
  at_pc 10412
  refine Triple.seq (ownerToW hfork (by rw [storageAt_readSlot, storageAt_readSlot]) (by simp)
    (TransferFrom.coldIn_accessSlot_false (TransferFrom.coldIn_accessSlot_false hc0)) (by gas_ok)
    (size_mapMem hM _ _)) ?_
  try simp only [storageAt_readSlot]
  exact restate rfl rfl rfl (by gas_ok) rfl rfl

/-- From the `POP` at 10512 after the owner's `SSTORE` to the STOP. -/
theorem feePost (hfork : .berlin ≤ fork) {no send fee v a sel : U256}
    (hstatic : message.isStatic = false) (hc0 : coldIn substate message.currentTarget 0 = false)
    {M : ByteArray} (hM : M.size = 96) (hptr : loadWord (memoryReadBytes M 64 32) 0 32 = 0x60)
    {gas : Nat} (hg : 3831 ≤ gas) :
    Gas.SpecG fork (At CODE message 10512 [no, 0x40, send, fee, v, a, 0x1699, v, a, 0x078a, sel] M
        gas state substate)
      (Halted false .empty (gas - 3831) (readSlot state message.currentTarget 0)
        { { accessSlot substate message.currentTarget 0 with
            logs := substate.logs.push (transferLog message.currentTarget
              (bitwiseAnd ADDR_MASK message.caller.toU256)
              (bitwiseAnd ADDR_MASK (ownerKey (storageAt state message.currentTarget 0))) fee) } with
          logs := (substate.logs.push (transferLog message.currentTarget
              (bitwiseAnd ADDR_MASK message.caller.toU256)
              (bitwiseAnd ADDR_MASK (ownerKey (storageAt state message.currentTarget 0))) fee)).push
            (transferLog message.currentTarget (bitwiseAnd ADDR_MASK message.caller.toU256)
              (bitwiseAnd ADDR_MASK a) send) }) := by
  refine Triple.seq (Gas.Triple.seqL popR (restate (pc' := 10513) (by decide) rfl rfl
    (g' := gas - 2) (by gas_ok) rfl rfl)) ?_
  step ownerLog hfork rfl (by simp) hstatic hc0 (by gas_ok) hM hptr
  step logBlock128 (by simp) hstatic (by gas_ok)
    (by rw [ByteArray.size_append, size_wordBytes]; exact congrArg (· + 32) hM)
    (by rw [read64_append hM]; exact hptr)
  refine (TransferOk.endBlock (by gas_ok)).consequence (fun _ h => h) ?_
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  exact ⟨hr, he, ho, by rw [hgas]; gas_ok, hs, hss⟩

/-- The meter after the sender's write in `transfer` with a fee, from the meter `g`. -/
abbrev fM1 (fork : Fork) (g : StateGasMeter) (state : State.TransactionState)
    (message : Message fork) (c0 cB c10 c3 c4 cS : Bool) : StateGasMeter :=
  TransferOk.tM1 fork g state message c0 cB c10 c3 c4 cS

/-- The meter after the recipient's write in `transfer` with a fee. -/
abbrev fM2 (fork : Fork) (g : StateGasMeter) (state : State.TransactionState)
    (message : Message fork) (c0 cB c10 c3 c4 cS cT : Bool) : StateGasMeter :=
  wMeter fork (fM1 fork g state message c0 cB c10 c3 c4 cS) (308 + slotCost cT)
    (originalAt state message.currentTarget (recipientSlot (addrArg message.data 0)))
    (balT (shortState state message) message (wordArg message.data 1) (addrArg message.data 0))
    (add (balT (shortState state message) message (wordArg message.data 1) (addrArg message.data 0))
      (sendOf (shortState state message) message (wordArg message.data 1))) false

/-- The meter after the owner's write in `transfer` with a fee. -/
abbrev fM3 (fork : Fork) (g : StateGasMeter) (state : State.TransactionState)
    (message : Message fork) (c0 cB c10 c3 c4 cS cT cO : Bool) : StateGasMeter :=
  wMeter fork (fM2 fork g state message c0 cB c10 c3 c4 cS cT) (605 + slotCost cO)
    (originalAt state message.currentTarget
      (ownerSlot (ownerWord (shortState state message) message (wordArg message.data 1)
        (addrArg message.data 0))))
    (balO (shortState state message) message (wordArg message.data 1) (addrArg message.data 0))
    (add (balO (shortState state message) message (wordArg message.data 1) (addrArg message.data 0))
      (feeOf (shortState state message) message (wordArg message.data 1))) false

/-- **transfer(a, v) with a fee above 0 over the EIP-8037 meter, exactly, at any reservoir, refills
allowed.** From Berlin, from a frame `m` of `StateGasMeter` with any meter whose `toNat` is the
fresh frame of `CODE`, under the hypotheses of `spec_fee` except the gas: the run, for any gas bound
and message runner, ends with no error if and only if `wOk` of the sender's write from `m.gas`,
`wOk` of the recipient's write from `fM1`, `wOk` of the owner's write from `fM2`, and
`3831 ≤ (fM3 …).gasLeft`. A refill of one write goes to the reservoir and spill that the next
write reads. Every run that ends with no error stops with the state and substate of `spec_fee`,
with `gasLeft + feeCost = gas` plus the three bumps, and the meter `fM3` for the rest. -/
theorem transferFee_sgm (hfork : .berlin ≤ fork)
    (hstatic : message.isStatic = false) (hacc : hasAccount state message.currentTarget)
    (hlong : 68 ≤ message.data.size) (hsz : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0xa9059cbb) (hv : message.value = 0)
    (hnp : byte20 (storageAt state message.currentTarget 0) = 0)
    (hnb : (storageAt state message.currentTarget (blackSlot message)).toNat % 256 = 0)
    (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    (hov : (wordArg message.data 1).toNat *
      (storageAt (shortState state message) message.currentTarget 3).toNat < 2 ^ 256)
    (hfee : feeOf (shortState state message) message (wordArg message.data 1) ≠ 0)
    (hfv : (feeOf (shortState state message) message (wordArg message.data 1)).toNat ≤
      (wordArg message.data 1).toNat)
    (hbal : (wordArg message.data 1).toNat ≤ (balS (shortState state message) message).toNat)
    (hto : (balT (shortState state message) message (wordArg message.data 1)
      (addrArg message.data 0)).toNat +
      (sendOf (shortState state message) message (wordArg message.data 1)).toNat < 2 ^ 256)
    (hown : (balO (shortState state message) message (wordArg message.data 1)
      (addrArg message.data 0)).toNat +
      (feeOf (shortState state message) message (wordArg message.data 1)).toNat < 2 ^ 256)
    {c0 cB c10 c3 c4 cS cT cO : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hcB : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget
      (blackSlot message) = cB)
    (hc10 : coldIn (accessSlot (accessSlot substate message.currentTarget 0) message.currentTarget
      (blackSlot message)) message.currentTarget 10 = c10)
    (hc3 : coldIn (shortSubstate substate message) message.currentTarget 3 = c3)
    (hc4 : coldIn (accessSlot (shortSubstate substate message) message.currentTarget 3)
      message.currentTarget 4 = c4)
    (hcS : coldIn (accessSlot (accessSlot (shortSubstate substate message) message.currentTarget 3)
      message.currentTarget 4) message.currentTarget (senderSlot message) = cS)
    (hcT : coldIn (access3 (shortSubstate substate message) message) message.currentTarget
      (recipientSlot (addrArg message.data 0)) = cT)
    (hcO : coldIn (creditedSubFee fork (shortSubstate substate message) (shortState state message)
      message (wordArg message.data 1) (addrArg message.data 0)) message.currentTarget
      (ownerSlot (ownerWord (shortState state message) message (wordArg message.data 1)
        (addrArg message.data 0))) = cO)
    {gas : Nat} {m : Evm fork StateGasMeter}
    (start : At CODE message 0 [] .empty gas state substate (Meter.toNat m))
    {bound : Nat} {runChild : MessageRunner fork StateGasMeter bound}
    (within : GasMeter.gasHeld m.gas ≤ bound) :
    (Shadow.RunsOkS fork bound runChild m within ↔
      wOk fork m.gas (TransferOk.tP1 state message c0 cB c10 c3 c4 cS)
          (originalAt state message.currentTarget (senderSlot message))
          (balS (shortState state message) message)
          (sub (balS (shortState state message) message) (wordArg message.data 1)) false ∧
      wOk fork (fM1 fork m.gas state message c0 cB c10 c3 c4 cS) (308 + slotCost cT)
          (originalAt state message.currentTarget (recipientSlot (addrArg message.data 0)))
          (balT (shortState state message) message (wordArg message.data 1) (addrArg message.data 0))
          (add (balT (shortState state message) message (wordArg message.data 1)
            (addrArg message.data 0))
            (sendOf (shortState state message) message (wordArg message.data 1))) false ∧
      wOk fork (fM2 fork m.gas state message c0 cB c10 c3 c4 cS cT) (605 + slotCost cO)
          (originalAt state message.currentTarget
            (ownerSlot (ownerWord (shortState state message) message (wordArg message.data 1)
              (addrArg message.data 0))))
          (balO (shortState state message) message (wordArg message.data 1) (addrArg message.data 0))
          (add (balO (shortState state message) message (wordArg message.data 1)
            (addrArg message.data 0))
            (feeOf (shortState state message) message (wordArg message.data 1))) false ∧
      3831 ≤ (fM3 fork m.gas state message c0 cB c10 c3 c4 cS cT cO).gasLeft) ∧
    ∀ s, Evm.runFrame (step fork) (step_decreases fork) bound runChild m within = .ok s →
      s.error = none →
      s.running = false ∧ s.output = .empty ∧
      s.state = feeState (shortState state message) message (wordArg message.data 1)
        (addrArg message.data 0) ∧
      s.substate = feeSub fork (shortSubstate substate message) (shortState state message) message
        (wordArg message.data 1) (addrArg message.data 0) ∧
      s.gas.gasLeft + feeCost fork state message c0 cB c10 c3 c4 cS cT cO =
        gas + wBump fork m.gas (originalAt state message.currentTarget (senderSlot message))
            (balS (shortState state message) message)
            (sub (balS (shortState state message) message) (wordArg message.data 1)) +
          wBump fork (fM1 fork m.gas state message c0 cB c10 c3 c4 cS)
            (originalAt state message.currentTarget (recipientSlot (addrArg message.data 0)))
            (balT (shortState state message) message (wordArg message.data 1)
              (addrArg message.data 0))
            (add (balT (shortState state message) message (wordArg message.data 1)
              (addrArg message.data 0))
              (sendOf (shortState state message) message (wordArg message.data 1))) +
          wBump fork (fM2 fork m.gas state message c0 cB c10 c3 c4 cS cT)
            (originalAt state message.currentTarget
              (ownerSlot (ownerWord (shortState state message) message (wordArg message.data 1)
                (addrArg message.data 0))))
            (balO (shortState state message) message (wordArg message.data 1)
              (addrArg message.data 0))
            (add (balO (shortState state message) message (wordArg message.data 1)
              (addrArg message.data 0))
              (feeOf (shortState state message) message (wordArg message.data 1))) ∧
      s.gas = { fM3 fork m.gas state message c0 cB c10 c3 c4 cS cT cO with
        gasLeft := s.gas.gasLeft } := by
  have haccS : hasAccount (shortState state message) message.currentTarget :=
    hasAccount_readSlot (hasAccount_readSlot (hasAccount_readSlot hacc))
  have hacc3 : hasAccount (reads3 (shortState state message) message) message.currentTarget :=
    hasAccount_readSlot (hasAccount_readSlot (hasAccount_readSlot haccS))
  have hacc4 : hasAccount (writeSlot (reads3 (shortState state message) message) message.currentTarget (senderSlot message) (sub (balS (shortState state message) message) (wordArg message.data 1))) message.currentTarget := hasAccount_writeSlot hacc3
  have hacc5 : hasAccount (readSlot (writeSlot (reads3 (shortState state message) message) message.currentTarget (senderSlot message) (sub (balS (shortState state message) message) (wordArg message.data 1))) message.currentTarget (recipientSlot (addrArg message.data 0))) message.currentTarget := hasAccount_readSlot hacc4
  have hacc6 : hasAccount (writeSlot (readSlot (writeSlot (reads3 (shortState state message) message) message.currentTarget (senderSlot message) (sub (balS (shortState state message) message) (wordArg message.data 1))) message.currentTarget (recipientSlot (addrArg message.data 0))) message.currentTarget (recipientSlot (addrArg message.data 0)) (add (storageAt (writeSlot (reads3 (shortState state message) message) message.currentTarget (senderSlot message) (sub (balS (shortState state message) message) (wordArg message.data 1))) message.currentTarget (recipientSlot (addrArg message.data 0))) (sendOf (shortState state message) message (wordArg message.data 1)))) message.currentTarget := hasAccount_writeSlot hacc5
  have hacc7 : hasAccount (readSlot (readSlot (readSlot (writeSlot (readSlot (writeSlot (reads3 (shortState state message) message) message.currentTarget (senderSlot message) (sub (balS (shortState state message) message) (wordArg message.data 1))) message.currentTarget (recipientSlot (addrArg message.data 0))) message.currentTarget (recipientSlot (addrArg message.data 0)) (add (storageAt (writeSlot (reads3 (shortState state message) message) message.currentTarget (senderSlot message) (sub (balS (shortState state message) message) (wordArg message.data 1))) message.currentTarget (recipientSlot (addrArg message.data 0))) (sendOf (shortState state message) message (wordArg message.data 1)))) message.currentTarget 0) message.currentTarget (ownerSlotOf (writeSlot (readSlot (writeSlot (reads3 (shortState state message) message) message.currentTarget (senderSlot message) (sub (balS (shortState state message) message) (wordArg message.data 1))) message.currentTarget (recipientSlot (addrArg message.data 0))) message.currentTarget (recipientSlot (addrArg message.data 0)) (add (storageAt (writeSlot (reads3 (shortState state message) message) message.currentTarget (senderSlot message) (sub (balS (shortState state message) message) (wordArg message.data 1))) message.currentTarget (recipientSlot (addrArg message.data 0))) (sendOf (shortState state message) message (wordArg message.data 1)))) message.currentTarget)) message.currentTarget 0) message.currentTarget :=
    hasAccount_readSlot (hasAccount_readSlot (hasAccount_readSlot hacc6))
  have hP : TransferOk.tP1 state message c0 cB c10 c3 c4 cS < 97920 := by
    have := Complete.slotCost_le c0; have := Complete.slotCost_le cB
    have := Complete.slotCost_le c10; have := Complete.slotCost_le c3
    have := Complete.slotCost_le c4; have := Complete.slotCost_le cS
    have : mulCost (wordArg message.data 1) ≤ 138 := by unfold mulCost; split <;> omega
    have : capCost (rawFee (shortState state message) message (wordArg message.data 1)) (storageAt (shortState state message) message.currentTarget 4) ≤ 108 := by
      unfold capCost; split <;> omega
    simp only [TransferOk.tP1, PRE_COST]; omega
  have hQ : 308 + slotCost cT < 97920 := by have := Complete.slotCost_le cT; omega
  have hR : 605 + slotCost cO < 97920 := by have := Complete.slotCost_le cO; omega
  have hpre : ∀ g, TransferOk.tP1 state message c0 cB c10 c3 c4 cS ≤ g → Gas.HoareG fork
      (At CODE message 0 [] .empty g state substate)
      (At CODE message 10138 [senderSlot message, (sub (balS (shortState state message) message) (wordArg message.data 1)), (sub (balS (shortState state message) message) (wordArg message.data 1)), 0x40, (sendOf (shortState state message) message (wordArg message.data 1)), (feeOf (shortState state message) message (wordArg message.data 1)), (wordArg message.data 1), (addrArg message.data 0),
          0x1699, (wordArg message.data 1), (addrArg message.data 0), 0x078a, BitVec.ofNat 256 (selector message.data)] (mapMem (mapMem (MEMK (callerKey message) 6) (callerKey message) 2) (callerKey message) 2)
        (g - TransferOk.tP1 state message c0 cB c10 c3 c4 cS) (reads3 (shortState state message) message) (access3 (shortSubstate substate message) message)) := by
    intro g hg
    simp only [TransferOk.tP1] at hg ⊢
    refine Triple.seq (pre hfork (by omega) hsz hsel hv hnp hnb hdep hc0 hcB hc10
      (Nat.le_trans (Nat.le_add_right _ _) hg)) ?_
    refine (feeW1 (state := (shortState state message)) (substate := (shortSubstate substate message))
      hfork hlong hsz (size_MEMK (callerKey message) 6) hov hfv hbal hc3 hc4 hcS
      (by omega)).consequence (fun _ h => h) ?_
    intro e he
    rw [Nat.sub_sub] at he
    exact he
  have hcT' : coldIn (storeSub fork (access3 (shortSubstate substate message) message) message.currentTarget (senderSlot message) (originalAt (reads3 (shortState state message) message) message.currentTarget (senderSlot message)) (storageAt (reads3 (shortState state message) message) message.currentTarget (senderSlot message)) (sub (balS (shortState state message) message) (wordArg message.data 1))) message.currentTarget (recipientSlot (addrArg message.data 0)) = cT := by rw [coldIn_storeSub]; exact hcT
  have hmid := fun g (hg : 308 + slotCost cT ≤ g) => feeW2 (state := (writeSlot (reads3 (shortState state message) message) message.currentTarget (senderSlot message) (sub (balS (shortState state message) message) (wordArg message.data 1)))) (substate := (storeSub fork (access3 (shortSubstate substate message) message) message.currentTarget (senderSlot message) (originalAt (reads3 (shortState state message) message) message.currentTarget (senderSlot message)) (storageAt (reads3 (shortState state message) message) message.currentTarget (senderSlot message)) (sub (balS (shortState state message) message) (wordArg message.data 1))))
    (nb := (sub (balS (shortState state message) message) (wordArg message.data 1))) (send := (sendOf (shortState state message) message (wordArg message.data 1))) (fee := (feeOf (shortState state message) message (wordArg message.data 1))) (v := (wordArg message.data 1)) (a := (addrArg message.data 0))
    (sel := BitVec.ofNat 256 (selector message.data)) (M := (mapMem (mapMem (MEMK (callerKey message) 6) (callerKey message) 2) (callerKey message) 2))
    hfork (size_mapMem (size_mapMem (size_MEMK _ _) _ _) _ _) hto hcT' hg
  have hw0 : coldIn (storeSub fork (accessSlot (storeSub fork (access3 (shortSubstate substate message) message) message.currentTarget (senderSlot message) (originalAt (reads3 (shortState state message) message) message.currentTarget (senderSlot message)) (storageAt (reads3 (shortState state message) message) message.currentTarget (senderSlot message)) (sub (balS (shortState state message) message) (wordArg message.data 1))) message.currentTarget (recipientSlot (addrArg message.data 0))) message.currentTarget (recipientSlot (addrArg message.data 0)) (originalAt (readSlot (writeSlot (reads3 (shortState state message) message) message.currentTarget (senderSlot message) (sub (balS (shortState state message) message) (wordArg message.data 1))) message.currentTarget (recipientSlot (addrArg message.data 0))) message.currentTarget (recipientSlot (addrArg message.data 0))) (storageAt (readSlot (writeSlot (reads3 (shortState state message) message) message.currentTarget (senderSlot message) (sub (balS (shortState state message) message) (wordArg message.data 1))) message.currentTarget (recipientSlot (addrArg message.data 0))) message.currentTarget (recipientSlot (addrArg message.data 0))) (add (storageAt (writeSlot (reads3 (shortState state message) message) message.currentTarget (senderSlot message) (sub (balS (shortState state message) message) (wordArg message.data 1))) message.currentTarget (recipientSlot (addrArg message.data 0))) (sendOf (shortState state message) message (wordArg message.data 1)))) message.currentTarget 0 = false :=
    coldIn_storeSub_false (TransferFrom.coldIn_accessSlot_false (coldIn_storeSub_false
      (TransferFrom.coldIn_accessSlot_false (TransferFrom.coldIn_accessSlot_false
        (TransferFrom.coldIn_accessSlot_false (TransferFrom.coldIn_accessSlot_false
          (TransferFrom.coldIn_accessSlot_false (coldIn_accessSlot_self _ _ _))))))))
  have hcO' : coldIn (storeSub fork (accessSlot (storeSub fork (access3 (shortSubstate substate message) message) message.currentTarget (senderSlot message) (originalAt (reads3 (shortState state message) message) message.currentTarget (senderSlot message)) (storageAt (reads3 (shortState state message) message) message.currentTarget (senderSlot message)) (sub (balS (shortState state message) message) (wordArg message.data 1))) message.currentTarget (recipientSlot (addrArg message.data 0))) message.currentTarget (recipientSlot (addrArg message.data 0)) (originalAt (readSlot (writeSlot (reads3 (shortState state message) message) message.currentTarget (senderSlot message) (sub (balS (shortState state message) message) (wordArg message.data 1))) message.currentTarget (recipientSlot (addrArg message.data 0))) message.currentTarget (recipientSlot (addrArg message.data 0))) (storageAt (readSlot (writeSlot (reads3 (shortState state message) message) message.currentTarget (senderSlot message) (sub (balS (shortState state message) message) (wordArg message.data 1))) message.currentTarget (recipientSlot (addrArg message.data 0))) message.currentTarget (recipientSlot (addrArg message.data 0))) (add (storageAt (writeSlot (reads3 (shortState state message) message) message.currentTarget (senderSlot message) (sub (balS (shortState state message) message) (wordArg message.data 1))) message.currentTarget (recipientSlot (addrArg message.data 0))) (sendOf (shortState state message) message (wordArg message.data 1)))) message.currentTarget (ownerSlotOf (writeSlot (readSlot (writeSlot (reads3 (shortState state message) message) message.currentTarget (senderSlot message) (sub (balS (shortState state message) message) (wordArg message.data 1))) message.currentTarget (recipientSlot (addrArg message.data 0))) message.currentTarget (recipientSlot (addrArg message.data 0)) (add (storageAt (writeSlot (reads3 (shortState state message) message) message.currentTarget (senderSlot message) (sub (balS (shortState state message) message) (wordArg message.data 1))) message.currentTarget (recipientSlot (addrArg message.data 0))) (sendOf (shortState state message) message (wordArg message.data 1)))) message.currentTarget) = cO := hcO
  have hw3 := fun g (hg : 605 + slotCost cO ≤ g) => feeW3 (state := (writeSlot (readSlot (writeSlot (reads3 (shortState state message) message) message.currentTarget (senderSlot message) (sub (balS (shortState state message) message) (wordArg message.data 1))) message.currentTarget (recipientSlot (addrArg message.data 0))) message.currentTarget (recipientSlot (addrArg message.data 0)) (add (storageAt (writeSlot (reads3 (shortState state message) message) message.currentTarget (senderSlot message) (sub (balS (shortState state message) message) (wordArg message.data 1))) message.currentTarget (recipientSlot (addrArg message.data 0))) (sendOf (shortState state message) message (wordArg message.data 1))))) (substate := (storeSub fork (accessSlot (storeSub fork (access3 (shortSubstate substate message) message) message.currentTarget (senderSlot message) (originalAt (reads3 (shortState state message) message) message.currentTarget (senderSlot message)) (storageAt (reads3 (shortState state message) message) message.currentTarget (senderSlot message)) (sub (balS (shortState state message) message) (wordArg message.data 1))) message.currentTarget (recipientSlot (addrArg message.data 0))) message.currentTarget (recipientSlot (addrArg message.data 0)) (originalAt (readSlot (writeSlot (reads3 (shortState state message) message) message.currentTarget (senderSlot message) (sub (balS (shortState state message) message) (wordArg message.data 1))) message.currentTarget (recipientSlot (addrArg message.data 0))) message.currentTarget (recipientSlot (addrArg message.data 0))) (storageAt (readSlot (writeSlot (reads3 (shortState state message) message) message.currentTarget (senderSlot message) (sub (balS (shortState state message) message) (wordArg message.data 1))) message.currentTarget (recipientSlot (addrArg message.data 0))) message.currentTarget (recipientSlot (addrArg message.data 0))) (add (storageAt (writeSlot (reads3 (shortState state message) message) message.currentTarget (senderSlot message) (sub (balS (shortState state message) message) (wordArg message.data 1))) message.currentTarget (recipientSlot (addrArg message.data 0))) (sendOf (shortState state message) message (wordArg message.data 1)))))
    (nt := (add (storageAt (writeSlot (reads3 (shortState state message) message) message.currentTarget (senderSlot message) (sub (balS (shortState state message) message) (wordArg message.data 1))) message.currentTarget (recipientSlot (addrArg message.data 0))) (sendOf (shortState state message) message (wordArg message.data 1)))) (send := (sendOf (shortState state message) message (wordArg message.data 1))) (fee := (feeOf (shortState state message) message (wordArg message.data 1))) (v := (wordArg message.data 1)) (a := (addrArg message.data 0))
    (sel := BitVec.ofNat 256 (selector message.data)) (M := (mapMem (mapMem (mapMem (mapMem (MEMK (callerKey message) 6) (callerKey message) 2) (callerKey message) 2) (mkey (addrArg message.data 0)) 2) (mkey (addrArg message.data 0)) 2))
    hfork hfee (size_mapMem (size_mapMem (size_mapMem (size_mapMem (size_MEMK _ _) _ _) _ _) _ _) _ _)
    hw0 hcO' hown hg
  have hpost := fun g (hg : 3831 ≤ g) => feePost (state := (writeSlot (readSlot (readSlot (readSlot (writeSlot (readSlot (writeSlot (reads3 (shortState state message) message) message.currentTarget (senderSlot message) (sub (balS (shortState state message) message) (wordArg message.data 1))) message.currentTarget (recipientSlot (addrArg message.data 0))) message.currentTarget (recipientSlot (addrArg message.data 0)) (add (storageAt (writeSlot (reads3 (shortState state message) message) message.currentTarget (senderSlot message) (sub (balS (shortState state message) message) (wordArg message.data 1))) message.currentTarget (recipientSlot (addrArg message.data 0))) (sendOf (shortState state message) message (wordArg message.data 1)))) message.currentTarget 0) message.currentTarget (ownerSlotOf (writeSlot (readSlot (writeSlot (reads3 (shortState state message) message) message.currentTarget (senderSlot message) (sub (balS (shortState state message) message) (wordArg message.data 1))) message.currentTarget (recipientSlot (addrArg message.data 0))) message.currentTarget (recipientSlot (addrArg message.data 0)) (add (storageAt (writeSlot (reads3 (shortState state message) message) message.currentTarget (senderSlot message) (sub (balS (shortState state message) message) (wordArg message.data 1))) message.currentTarget (recipientSlot (addrArg message.data 0))) (sendOf (shortState state message) message (wordArg message.data 1)))) message.currentTarget)) message.currentTarget 0) message.currentTarget (ownerSlotOf (writeSlot (readSlot (writeSlot (reads3 (shortState state message) message) message.currentTarget (senderSlot message) (sub (balS (shortState state message) message) (wordArg message.data 1))) message.currentTarget (recipientSlot (addrArg message.data 0))) message.currentTarget (recipientSlot (addrArg message.data 0)) (add (storageAt (writeSlot (reads3 (shortState state message) message) message.currentTarget (senderSlot message) (sub (balS (shortState state message) message) (wordArg message.data 1))) message.currentTarget (recipientSlot (addrArg message.data 0))) (sendOf (shortState state message) message (wordArg message.data 1)))) message.currentTarget) (add (balOf (writeSlot (readSlot (writeSlot (reads3 (shortState state message) message) message.currentTarget (senderSlot message) (sub (balS (shortState state message) message) (wordArg message.data 1))) message.currentTarget (recipientSlot (addrArg message.data 0))) message.currentTarget (recipientSlot (addrArg message.data 0)) (add (storageAt (writeSlot (reads3 (shortState state message) message) message.currentTarget (senderSlot message) (sub (balS (shortState state message) message) (wordArg message.data 1))) message.currentTarget (recipientSlot (addrArg message.data 0))) (sendOf (shortState state message) message (wordArg message.data 1)))) message.currentTarget) (feeOf (shortState state message) message (wordArg message.data 1))))) (substate := (storeSub fork (accessSlot (accessSlot (accessSlot (storeSub fork (accessSlot (storeSub fork (access3 (shortSubstate substate message) message) message.currentTarget (senderSlot message) (originalAt (reads3 (shortState state message) message) message.currentTarget (senderSlot message)) (storageAt (reads3 (shortState state message) message) message.currentTarget (senderSlot message)) (sub (balS (shortState state message) message) (wordArg message.data 1))) message.currentTarget (recipientSlot (addrArg message.data 0))) message.currentTarget (recipientSlot (addrArg message.data 0)) (originalAt (readSlot (writeSlot (reads3 (shortState state message) message) message.currentTarget (senderSlot message) (sub (balS (shortState state message) message) (wordArg message.data 1))) message.currentTarget (recipientSlot (addrArg message.data 0))) message.currentTarget (recipientSlot (addrArg message.data 0))) (storageAt (readSlot (writeSlot (reads3 (shortState state message) message) message.currentTarget (senderSlot message) (sub (balS (shortState state message) message) (wordArg message.data 1))) message.currentTarget (recipientSlot (addrArg message.data 0))) message.currentTarget (recipientSlot (addrArg message.data 0))) (add (storageAt (writeSlot (reads3 (shortState state message) message) message.currentTarget (senderSlot message) (sub (balS (shortState state message) message) (wordArg message.data 1))) message.currentTarget (recipientSlot (addrArg message.data 0))) (sendOf (shortState state message) message (wordArg message.data 1)))) message.currentTarget 0) message.currentTarget (ownerSlotOf (writeSlot (readSlot (writeSlot (reads3 (shortState state message) message) message.currentTarget (senderSlot message) (sub (balS (shortState state message) message) (wordArg message.data 1))) message.currentTarget (recipientSlot (addrArg message.data 0))) message.currentTarget (recipientSlot (addrArg message.data 0)) (add (storageAt (writeSlot (reads3 (shortState state message) message) message.currentTarget (senderSlot message) (sub (balS (shortState state message) message) (wordArg message.data 1))) message.currentTarget (recipientSlot (addrArg message.data 0))) (sendOf (shortState state message) message (wordArg message.data 1)))) message.currentTarget)) message.currentTarget 0) message.currentTarget (ownerSlotOf (writeSlot (readSlot (writeSlot (reads3 (shortState state message) message) message.currentTarget (senderSlot message) (sub (balS (shortState state message) message) (wordArg message.data 1))) message.currentTarget (recipientSlot (addrArg message.data 0))) message.currentTarget (recipientSlot (addrArg message.data 0)) (add (storageAt (writeSlot (reads3 (shortState state message) message) message.currentTarget (senderSlot message) (sub (balS (shortState state message) message) (wordArg message.data 1))) message.currentTarget (recipientSlot (addrArg message.data 0))) (sendOf (shortState state message) message (wordArg message.data 1)))) message.currentTarget) (originalAt (readSlot (readSlot (readSlot (writeSlot (readSlot (writeSlot (reads3 (shortState state message) message) message.currentTarget (senderSlot message) (sub (balS (shortState state message) message) (wordArg message.data 1))) message.currentTarget (recipientSlot (addrArg message.data 0))) message.currentTarget (recipientSlot (addrArg message.data 0)) (add (storageAt (writeSlot (reads3 (shortState state message) message) message.currentTarget (senderSlot message) (sub (balS (shortState state message) message) (wordArg message.data 1))) message.currentTarget (recipientSlot (addrArg message.data 0))) (sendOf (shortState state message) message (wordArg message.data 1)))) message.currentTarget 0) message.currentTarget (ownerSlotOf (writeSlot (readSlot (writeSlot (reads3 (shortState state message) message) message.currentTarget (senderSlot message) (sub (balS (shortState state message) message) (wordArg message.data 1))) message.currentTarget (recipientSlot (addrArg message.data 0))) message.currentTarget (recipientSlot (addrArg message.data 0)) (add (storageAt (writeSlot (reads3 (shortState state message) message) message.currentTarget (senderSlot message) (sub (balS (shortState state message) message) (wordArg message.data 1))) message.currentTarget (recipientSlot (addrArg message.data 0))) (sendOf (shortState state message) message (wordArg message.data 1)))) message.currentTarget)) message.currentTarget 0) message.currentTarget (ownerSlotOf (writeSlot (readSlot (writeSlot (reads3 (shortState state message) message) message.currentTarget (senderSlot message) (sub (balS (shortState state message) message) (wordArg message.data 1))) message.currentTarget (recipientSlot (addrArg message.data 0))) message.currentTarget (recipientSlot (addrArg message.data 0)) (add (storageAt (writeSlot (reads3 (shortState state message) message) message.currentTarget (senderSlot message) (sub (balS (shortState state message) message) (wordArg message.data 1))) message.currentTarget (recipientSlot (addrArg message.data 0))) (sendOf (shortState state message) message (wordArg message.data 1)))) message.currentTarget)) (storageAt (readSlot (readSlot (readSlot (writeSlot (readSlot (writeSlot (reads3 (shortState state message) message) message.currentTarget (senderSlot message) (sub (balS (shortState state message) message) (wordArg message.data 1))) message.currentTarget (recipientSlot (addrArg message.data 0))) message.currentTarget (recipientSlot (addrArg message.data 0)) (add (storageAt (writeSlot (reads3 (shortState state message) message) message.currentTarget (senderSlot message) (sub (balS (shortState state message) message) (wordArg message.data 1))) message.currentTarget (recipientSlot (addrArg message.data 0))) (sendOf (shortState state message) message (wordArg message.data 1)))) message.currentTarget 0) message.currentTarget (ownerSlotOf (writeSlot (readSlot (writeSlot (reads3 (shortState state message) message) message.currentTarget (senderSlot message) (sub (balS (shortState state message) message) (wordArg message.data 1))) message.currentTarget (recipientSlot (addrArg message.data 0))) message.currentTarget (recipientSlot (addrArg message.data 0)) (add (storageAt (writeSlot (reads3 (shortState state message) message) message.currentTarget (senderSlot message) (sub (balS (shortState state message) message) (wordArg message.data 1))) message.currentTarget (recipientSlot (addrArg message.data 0))) (sendOf (shortState state message) message (wordArg message.data 1)))) message.currentTarget)) message.currentTarget 0) message.currentTarget (ownerSlotOf (writeSlot (readSlot (writeSlot (reads3 (shortState state message) message) message.currentTarget (senderSlot message) (sub (balS (shortState state message) message) (wordArg message.data 1))) message.currentTarget (recipientSlot (addrArg message.data 0))) message.currentTarget (recipientSlot (addrArg message.data 0)) (add (storageAt (writeSlot (reads3 (shortState state message) message) message.currentTarget (senderSlot message) (sub (balS (shortState state message) message) (wordArg message.data 1))) message.currentTarget (recipientSlot (addrArg message.data 0))) (sendOf (shortState state message) message (wordArg message.data 1)))) message.currentTarget)) (add (balOf (writeSlot (readSlot (writeSlot (reads3 (shortState state message) message) message.currentTarget (senderSlot message) (sub (balS (shortState state message) message) (wordArg message.data 1))) message.currentTarget (recipientSlot (addrArg message.data 0))) message.currentTarget (recipientSlot (addrArg message.data 0)) (add (storageAt (writeSlot (reads3 (shortState state message) message) message.currentTarget (senderSlot message) (sub (balS (shortState state message) message) (wordArg message.data 1))) message.currentTarget (recipientSlot (addrArg message.data 0))) (sendOf (shortState state message) message (wordArg message.data 1)))) message.currentTarget) (feeOf (shortState state message) message (wordArg message.data 1)))))
    (no := (add (balOf (writeSlot (readSlot (writeSlot (reads3 (shortState state message) message) message.currentTarget (senderSlot message) (sub (balS (shortState state message) message) (wordArg message.data 1))) message.currentTarget (recipientSlot (addrArg message.data 0))) message.currentTarget (recipientSlot (addrArg message.data 0)) (add (storageAt (writeSlot (reads3 (shortState state message) message) message.currentTarget (senderSlot message) (sub (balS (shortState state message) message) (wordArg message.data 1))) message.currentTarget (recipientSlot (addrArg message.data 0))) (sendOf (shortState state message) message (wordArg message.data 1)))) message.currentTarget) (feeOf (shortState state message) message (wordArg message.data 1)))) (send := (sendOf (shortState state message) message (wordArg message.data 1))) (fee := (feeOf (shortState state message) message (wordArg message.data 1))) (v := (wordArg message.data 1)) (a := (addrArg message.data 0))
    (sel := BitVec.ofNat 256 (selector message.data)) (M := (mapMem (mapMem (mapMem (mapMem (mapMem (mapMem (MEMK (callerKey message) 6) (callerKey message) 2) (callerKey message) 2) (mkey (addrArg message.data 0)) 2) (mkey (addrArg message.data 0)) 2) (mkey (ownerKey (storageAt (writeSlot (readSlot (writeSlot (reads3 (shortState state message) message) message.currentTarget (senderSlot message) (sub (balS (shortState state message) message) (wordArg message.data 1))) message.currentTarget (recipientSlot (addrArg message.data 0))) message.currentTarget (recipientSlot (addrArg message.data 0)) (add (storageAt (writeSlot (reads3 (shortState state message) message) message.currentTarget (senderSlot message) (sub (balS (shortState state message) message) (wordArg message.data 1))) message.currentTarget (recipientSlot (addrArg message.data 0))) (sendOf (shortState state message) message (wordArg message.data 1)))) message.currentTarget 0))) 2) (mkey (ownerKey (storageAt (writeSlot (readSlot (writeSlot (reads3 (shortState state message) message) message.currentTarget (senderSlot message) (sub (balS (shortState state message) message) (wordArg message.data 1))) message.currentTarget (recipientSlot (addrArg message.data 0))) message.currentTarget (recipientSlot (addrArg message.data 0)) (add (storageAt (writeSlot (reads3 (shortState state message) message) message.currentTarget (senderSlot message) (sub (balS (shortState state message) message) (wordArg message.data 1))) message.currentTarget (recipientSlot (addrArg message.data 0))) (sendOf (shortState state message) message (wordArg message.data 1)))) message.currentTarget 0))) 2)) hfork hstatic
    (coldIn_storeSub_false (coldIn_accessSlot_self _ _ _))
    (size_mapMem (size_mapMem (size_mapMem (size_mapMem (size_mapMem (size_mapMem (size_MEMK _ _) _ _) _ _) _ _) _ _) _ _) _ _)
    (ptr_mapMem (size_mapMem (size_mapMem (size_mapMem (size_mapMem (size_mapMem (size_MEMK _ _) _ _) _ _) _ _) _ _) _ _)
      (ptr_mapMem (size_mapMem (size_mapMem (size_mapMem (size_mapMem (size_MEMK _ _) _ _) _ _) _ _) _ _)
        (ptr_mapMem (size_mapMem (size_mapMem (size_mapMem (size_MEMK _ _) _ _) _ _) _ _)
          (ptr_mapMem (size_mapMem (size_mapMem (size_MEMK _ _) _ _) _ _)
            (ptr_mapMem (size_mapMem (size_MEMK _ _) _ _)
              (ptr_mapMem (size_MEMK _ _) (ptr_MEMK _ _) _ _) _ _) _ _) _ _) _ _) _ _) hg
  have hx := Complete.exactS_write hfork hpre hP
    (fun _ _ => by simp only [Complete.getStorage_readSlot]) (by code_fact) (by code_fact)
    hstatic hacc3 (coldIn_accessSlot_self _ _ _)
    (Complete.exactS_write hfork hmid hQ (fun _ _ => by simp only [Complete.getStorage_readSlot])
      (by code_fact) (by code_fact) hstatic hacc5 (coldIn_accessSlot_self _ _ _)
      (Complete.exactS_write hfork hw3 hR
        (fun _ _ => by simp only [Complete.getStorage_readSlot]) (by code_fact) (by code_fact)
        hstatic hacc7 (TransferFrom.coldIn_accessSlot_false (coldIn_accessSlot_self _ _ _))
        (Complete.exactS_halt hpost (by decide) (fun _ _ => by simp only [Complete.getStorage_readSlot]))))
  obtain ⟨hgas, hiff, hend⟩ := hx.run start (runChild := runChild) within
  have eo1 : originalAt (reads3 (shortState state message) message) message.currentTarget (senderSlot message) =
      originalAt (shortState state message) message.currentTarget (senderSlot message) := by simp only [reads3, originalAt_readSlot]
  have ec1 : storageAt (reads3 (shortState state message) message) message.currentTarget (senderSlot message) = balS (shortState state message) message := by
    simp only [reads3, storageAt_readSlot]
  have eo2 : originalAt (readSlot (writeSlot (reads3 (shortState state message) message) message.currentTarget (senderSlot message) (sub (balS (shortState state message) message) (wordArg message.data 1))) message.currentTarget (recipientSlot (addrArg message.data 0))) message.currentTarget (recipientSlot (addrArg message.data 0)) = originalAt (shortState state message) message.currentTarget (recipientSlot (addrArg message.data 0)) := by
    rw [originalAt_readSlot, originalAt_writeSlot hacc3]; simp only [reads3, originalAt_readSlot]
  have ec2 : storageAt (readSlot (writeSlot (reads3 (shortState state message) message) message.currentTarget (senderSlot message) (sub (balS (shortState state message) message) (wordArg message.data 1))) message.currentTarget (recipientSlot (addrArg message.data 0))) message.currentTarget (recipientSlot (addrArg message.data 0)) = balT (shortState state message) message (wordArg message.data 1) (addrArg message.data 0) := by
    rw [storageAt_readSlot]
  have eo3 : originalAt (readSlot (readSlot (readSlot (writeSlot (readSlot (writeSlot (reads3 (shortState state message) message) message.currentTarget (senderSlot message) (sub (balS (shortState state message) message) (wordArg message.data 1))) message.currentTarget (recipientSlot (addrArg message.data 0))) message.currentTarget (recipientSlot (addrArg message.data 0)) (add (storageAt (writeSlot (reads3 (shortState state message) message) message.currentTarget (senderSlot message) (sub (balS (shortState state message) message) (wordArg message.data 1))) message.currentTarget (recipientSlot (addrArg message.data 0))) (sendOf (shortState state message) message (wordArg message.data 1)))) message.currentTarget 0) message.currentTarget (ownerSlotOf (writeSlot (readSlot (writeSlot (reads3 (shortState state message) message) message.currentTarget (senderSlot message) (sub (balS (shortState state message) message) (wordArg message.data 1))) message.currentTarget (recipientSlot (addrArg message.data 0))) message.currentTarget (recipientSlot (addrArg message.data 0)) (add (storageAt (writeSlot (reads3 (shortState state message) message) message.currentTarget (senderSlot message) (sub (balS (shortState state message) message) (wordArg message.data 1))) message.currentTarget (recipientSlot (addrArg message.data 0))) (sendOf (shortState state message) message (wordArg message.data 1)))) message.currentTarget)) message.currentTarget 0) message.currentTarget (ownerSlotOf (writeSlot (readSlot (writeSlot (reads3 (shortState state message) message) message.currentTarget (senderSlot message) (sub (balS (shortState state message) message) (wordArg message.data 1))) message.currentTarget (recipientSlot (addrArg message.data 0))) message.currentTarget (recipientSlot (addrArg message.data 0)) (add (storageAt (writeSlot (reads3 (shortState state message) message) message.currentTarget (senderSlot message) (sub (balS (shortState state message) message) (wordArg message.data 1))) message.currentTarget (recipientSlot (addrArg message.data 0))) (sendOf (shortState state message) message (wordArg message.data 1)))) message.currentTarget) = originalAt (shortState state message) message.currentTarget (ownerSlotOf (writeSlot (readSlot (writeSlot (reads3 (shortState state message) message) message.currentTarget (senderSlot message) (sub (balS (shortState state message) message) (wordArg message.data 1))) message.currentTarget (recipientSlot (addrArg message.data 0))) message.currentTarget (recipientSlot (addrArg message.data 0)) (add (storageAt (writeSlot (reads3 (shortState state message) message) message.currentTarget (senderSlot message) (sub (balS (shortState state message) message) (wordArg message.data 1))) message.currentTarget (recipientSlot (addrArg message.data 0))) (sendOf (shortState state message) message (wordArg message.data 1)))) message.currentTarget) := by
    rw [originalAt_readSlot, originalAt_readSlot, originalAt_readSlot, originalAt_writeSlot hacc5,
      originalAt_readSlot, originalAt_writeSlot hacc3]
    simp only [reads3, originalAt_readSlot]
  have ec3 : storageAt (readSlot (readSlot (readSlot (writeSlot (readSlot (writeSlot (reads3 (shortState state message) message) message.currentTarget (senderSlot message) (sub (balS (shortState state message) message) (wordArg message.data 1))) message.currentTarget (recipientSlot (addrArg message.data 0))) message.currentTarget (recipientSlot (addrArg message.data 0)) (add (storageAt (writeSlot (reads3 (shortState state message) message) message.currentTarget (senderSlot message) (sub (balS (shortState state message) message) (wordArg message.data 1))) message.currentTarget (recipientSlot (addrArg message.data 0))) (sendOf (shortState state message) message (wordArg message.data 1)))) message.currentTarget 0) message.currentTarget (ownerSlotOf (writeSlot (readSlot (writeSlot (reads3 (shortState state message) message) message.currentTarget (senderSlot message) (sub (balS (shortState state message) message) (wordArg message.data 1))) message.currentTarget (recipientSlot (addrArg message.data 0))) message.currentTarget (recipientSlot (addrArg message.data 0)) (add (storageAt (writeSlot (reads3 (shortState state message) message) message.currentTarget (senderSlot message) (sub (balS (shortState state message) message) (wordArg message.data 1))) message.currentTarget (recipientSlot (addrArg message.data 0))) (sendOf (shortState state message) message (wordArg message.data 1)))) message.currentTarget)) message.currentTarget 0) message.currentTarget (ownerSlotOf (writeSlot (readSlot (writeSlot (reads3 (shortState state message) message) message.currentTarget (senderSlot message) (sub (balS (shortState state message) message) (wordArg message.data 1))) message.currentTarget (recipientSlot (addrArg message.data 0))) message.currentTarget (recipientSlot (addrArg message.data 0)) (add (storageAt (writeSlot (reads3 (shortState state message) message) message.currentTarget (senderSlot message) (sub (balS (shortState state message) message) (wordArg message.data 1))) message.currentTarget (recipientSlot (addrArg message.data 0))) (sendOf (shortState state message) message (wordArg message.data 1)))) message.currentTarget) = balOf (writeSlot (readSlot (writeSlot (reads3 (shortState state message) message) message.currentTarget (senderSlot message) (sub (balS (shortState state message) message) (wordArg message.data 1))) message.currentTarget (recipientSlot (addrArg message.data 0))) message.currentTarget (recipientSlot (addrArg message.data 0)) (add (storageAt (writeSlot (reads3 (shortState state message) message) message.currentTarget (senderSlot message) (sub (balS (shortState state message) message) (wordArg message.data 1))) message.currentTarget (recipientSlot (addrArg message.data 0))) (sendOf (shortState state message) message (wordArg message.data 1)))) message.currentTarget := by
    rw [storageAt_readSlot, storageAt_readSlot, storageAt_readSlot]
  rw [eo1, ec1, eo2, ec2, eo3, ec3] at hiff
  refine ⟨by
    simp only [originalAt_readSlot, storageAt_readSlot, shortState, reads3, balS, balT, debited, TransferOk.tM1, TransferOk.tP1, fM1, fM2, fM3, sendOf, balO, balOf, ownerSlotOf, ownerWord, creditedFee] at hiff ⊢
    exact hiff, fun s hrun hok => ?_⟩
  have hok' := hiff.mp ⟨s, hrun, hok⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := hend s hrun hok
  rw [eo1, ec1, eo2, ec2, eo3, ec3] at h5
  refine ⟨h1, h2, ?_, ?_, ?_, ?_⟩
  · rw [h3]
  · rw [h4, eo1, ec1, eo2, ec2, eo3, ec3]
  · obtain ⟨o1, o2, o3, o4⟩ := hok'
    have e1 := Complete.wMeter_gasLeft o1
    have e2 := Complete.wMeter_gasLeft o2
    have e3 := Complete.wMeter_gasLeft o3
    have e4 : s.gas.gasLeft = _ := congrArg StateGasMeter.gasLeft h5
    simp only [originalAt_readSlot, storageAt_readSlot, shortState, reads3, balS, balT, debited, TransferOk.tM1, TransferOk.tP1, fM1, fM2, fM3, sendOf, balO, balOf, ownerSlotOf, ownerWord, creditedFee, feeCost, readCost, debitCost, creditCostFee, ownerCost, wBump] at e1 e2 e3 e4 o4 ⊢
    omega
  · rw [h5]
    simp only [originalAt_readSlot, storageAt_readSlot, shortState, reads3, balS, balT, debited, TransferOk.tM1, TransferOk.tP1, fM1, fM2, fM3, sendOf, balO, balOf, ownerSlotOf, ownerWord, creditedFee]

end UsdtVerify.TransferFee
