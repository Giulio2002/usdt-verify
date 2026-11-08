import UsdtVerify.Usdt.Refill.ChainOwner
import UsdtVerify.Usdt.Refill.TransferFrom

/-!
# transfer over the EIP-8037 meter: the exact condition and gas through the chain of writes (round 43)

The success path of `transfer(a, v)` is split at its SSTOREs into cheap stretches, and
`Complete.exactS_write` is applied once per write, then `Complete.exactS_halt`.

- `transfer_sgm` (fee 0): two writes, `balances[msg.sender]` then `balances[_to]`. From a frame
  with any meter, for any gas bound and message runner, under the hypotheses of `spec_ok` except
  the gas, the run ends with no error if and only if the chain condition holds, and every run that
  ends with no error has the state and substate of `spec_ok` and
  `gasLeft + okCost = gas + the two bumps`.

No hypothesis on refills or on the reservoir.
-/

namespace UsdtVerify.TransferOk
open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts
open Transfer SafeMath
open Complete (wBump wSgm wOk wMeter)
variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate}

/-- At 10072: from the `JUMPDEST` to the `SSTORE` of `balances[msg.sender]` (10138). -/
theorem debitToW {nb send fee v a : U256} {rest : List U256} (hrest : rest.length ≤ 800)
    {gas : Nat} (hg : 99 ≤ gas) {M : ByteArray} (hM : M.size = 96) :
    Gas.HoareG fork (At CODE message 10072 (nb :: 0x40 :: send :: fee :: v :: a :: rest) M gas state
        substate)
      (At CODE message 10138 (senderSlot message :: nb :: nb :: 0x40 :: send :: fee :: v :: a :: rest)
        (mapMem M (callerKey message) 2) (gas - 99) state substate) := by
  debit_pre
  exact restate (by decide) rfl rfl (by gas_ok) rfl rfl

/-- At 10221 (fee 0): from the `JUMPDEST` to the `SSTORE` of `balances[_to]` (10287). -/
theorem creditToW {nt send fee v a : U256} {rest : List U256} (hrest : rest.length ≤ 800)
    {gas : Nat} (hg : 100 ≤ gas) {M : ByteArray} (hM : M.size = 96) :
    Gas.HoareG fork (At CODE message 10221 (nt :: 0x40 :: send :: fee :: v :: a :: rest) M gas state
        substate)
      (At CODE message 10287 (recipientSlot a :: nt :: nt :: 0x40 :: send :: fee :: v :: a :: rest)
        (mapMem M (mkey a) 2) (gas - 100) state substate) := by
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
  exact restate (by decide) rfl rfl (by gas_ok) rfl rfl

/-- From 9883 (fee 0) to the `SSTORE` of `balances[msg.sender]` (10138). -/
theorem bodyW1 (hfork : .berlin ≤ fork)
    (hlong : 68 ≤ message.data.size) (hsz : message.data.size < 2 ^ 256)
    {v a sel : U256} {M : ByteArray} (hM : M.size = 96)
    (hov : v.toNat * (storageAt state message.currentTarget 3).toNat < 2 ^ 256)
    (hfee : feeOf state message v = 0)
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
          sub (balS state message) v :: 0x40 :: v :: 0 :: v :: a :: [0x1699, v, a, 0x078a, sel])
        (mapMem (mapMem M (callerKey message) 2) (callerKey message) 2)
        (gas - (629 + slotCost c3 + slotCost c4 + slotCost cS + mulCost v +
          capCost (rawFee state message v) (storageAt state message.currentTarget 4)))
        (reads3 state message) (access3 substate message)) := by
  simp only [rawFee, feeOf, balS, reads3] at hg hfee hbal ⊢
  step payloadOk hlong hsz (by simp) (by gas_ok)
  step feeCall hfork (by simp) hc3 (by gas_ok)
  step mulBlock (by simp) (by valid_dest) hov (by gas_ok)
  at_pc 9937
  step divCall (by simp) (by gas_ok)
  step divBlock (by simp) (by valid_dest) (by decide) (by gas_ok)
  at_pc 9951
  step capBlock hfork (by simp) hc4 (by simp only [storageAt_readSlot]; gas_ok)
  simp only [storageAt_readSlot]
  step Gas.reshapeG (s' := (0x40 : U256) :: 0 :: 0 :: v :: a :: [0x1699, v, a, 0x078a, sel])
    (by rw [hfee]) rfl rfl
  step sendCall (by simp) (by gas_ok)
  step subBlock (by simp) (by valid_dest) (by simp) (by gas_ok)
  at_pc 9988
  step Gas.reshapeG (s' := v :: (0x40 : U256) :: 0 :: 0 :: v :: a :: [0x1699, v, a, 0x078a, sel])
    (by simp [sub]) rfl rfl
  step debitCall hfork (by simp) hcS (by gas_ok) hM
  simp only [storageAt_readSlot]
  step subBlock (by simp) (by valid_dest) hbal (by gas_ok)
  at_pc 10072
  refine Triple.seq (debitToW (by simp) (by gas_ok) (size_mapMem hM _ _)) ?_
  exact restate rfl rfl rfl (by gas_ok) rfl rfl

/-- From the `POP` at 10139 after the sender's `SSTORE` to the `SSTORE` of `balances[_to]` (10287),
fee 0. -/
theorem bodyW2 (hfork : .berlin ≤ fork) {nb v a sel : U256} {M : ByteArray} (hM : M.size = 96)
    (hto : (storageAt state message.currentTarget (recipientSlot a)).toNat + v.toNat < 2 ^ 256)
    {cT : Bool} (hcT : coldIn substate message.currentTarget (recipientSlot a) = cT) {gas : Nat}
    (hg : 308 + slotCost cT ≤ gas) :
    Gas.HoareG fork (At CODE message 10139 [nb, 0x40, v, 0, v, a, 0x1699, v, a, 0x078a, sel] M gas
        state substate)
      (At CODE message 10287 (recipientSlot a ::
          add (storageAt state message.currentTarget (recipientSlot a)) v ::
          add (storageAt state message.currentTarget (recipientSlot a)) v ::
          [0x40, v, 0, v, a, 0x1699, v, a, 0x078a, sel])
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

/-- From the `POP` at 10288 after the recipient's `SSTORE` (fee 0) to the STOP. -/
theorem bodyW3 {nt v a sel : U256} (hstatic : message.isStatic = false) {M : ByteArray}
    (hM : M.size = 96) (hptr : loadWord (memoryReadBytes M 64 32) 0 32 = 0x60) {gas : Nat}
    (hg : 1892 ≤ gas) :
    Gas.SpecG fork (At CODE message 10288 [nt, 0x40, v, 0, v, a, 0x1699, v, a, 0x078a, sel] M gas
        state substate)
      (Halted false .empty (gas - 1892) state
        { substate with logs := substate.logs.push (transferLog message.currentTarget
          (bitwiseAnd ADDR_MASK message.caller.toU256) (bitwiseAnd ADDR_MASK a) v) }) := by
  step popR
  step pushR 1 (0 : U256)
  step dupR 3
  step binR 0x11 Local.instruction_gt
  step unR 0x15 instruction_iszero
  step pushR 2 (0x2997 : U256)
  step jumpiR (by decide)
  at_pc 10647
  step logBlock (by simp) hstatic (by gas_ok) hM hptr
  refine (endBlock (by gas_ok)).consequence (fun _ h => h) ?_
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  exact ⟨hr, he, ho, by rw [hgas]; gas_ok, hs, hss⟩

/-- The execution gas from pc 0 to the sender's `SSTORE` of `transfer` (fee 0). -/
abbrev tP1 (state : State.TransactionState) (message : Message fork)
    (c0 cB c10 c3 c4 cS : Bool) : Nat :=
  PRE_COST + slotCost c0 + slotCost cB + slotCost c10 + (629 + slotCost c3 + slotCost c4 +
    slotCost cS + mulCost (wordArg message.data 1) +
    capCost (rawFee (shortState state message) message (wordArg message.data 1))
      (storageAt (shortState state message) message.currentTarget 4))

/-- The meter after the sender's write in `transfer`, from the meter `g`. -/
abbrev tM1 (fork : Fork) (g : StateGasMeter) (state : State.TransactionState)
    (message : Message fork) (c0 cB c10 c3 c4 cS : Bool) : StateGasMeter :=
  wMeter fork g (tP1 state message c0 cB c10 c3 c4 cS)
    (originalAt state message.currentTarget (senderSlot message))
    (balS (shortState state message) message)
    (sub (balS (shortState state message) message) (wordArg message.data 1)) false

/-- The meter after the recipient's write in `transfer` (fee 0). -/
abbrev tM2 (fork : Fork) (g : StateGasMeter) (state : State.TransactionState)
    (message : Message fork) (c0 cB c10 c3 c4 cS cT : Bool) : StateGasMeter :=
  wMeter fork (tM1 fork g state message c0 cB c10 c3 c4 cS) (308 + slotCost cT)
    (originalAt state message.currentTarget (recipientSlot (addrArg message.data 0)))
    (balT (shortState state message) message (wordArg message.data 1) (addrArg message.data 0))
    (add (balT (shortState state message) message (wordArg message.data 1)
      (addrArg message.data 0)) (wordArg message.data 1)) false

/-- **transfer(a, v) with a fee of 0 over the EIP-8037 meter, exactly, at any reservoir, refills
allowed.** From Berlin, from a frame `m` of `StateGasMeter` with any meter whose `toNat` is the
fresh frame of `CODE`, under the hypotheses of `spec_ok` except the gas: the run, for any gas bound
and message runner, ends with no error if and only if `wOk` of the sender's write from `m.gas`,
`wOk` of the recipient's write from the meter after the sender's write (`tM1`), and
`1892 ≤ (tM2 …).gasLeft`. A refill of the sender's write goes to the reservoir and spill of
`tM1`, which the recipient's write reads. Every run that ends with no error stops with the state
and substate of `spec_ok`, with `gasLeft + okCost = gas + wBump m.gas (sender) + wBump tM1
(recipient)` and the meter `tM2` for the rest. -/
theorem transfer_sgm (hfork : .berlin ≤ fork)
    (hstatic : message.isStatic = false) (hacc : hasAccount state message.currentTarget)
    (hlong : 68 ≤ message.data.size) (hsz : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0xa9059cbb) (hv : message.value = 0)
    (hnp : byte20 (storageAt state message.currentTarget 0) = 0)
    (hnb : (storageAt state message.currentTarget (blackSlot message)).toNat % 256 = 0)
    (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    (hov : (wordArg message.data 1).toNat *
      (storageAt (shortState state message) message.currentTarget 3).toNat < 2 ^ 256)
    (hfee : feeOf (shortState state message) message (wordArg message.data 1) = 0)
    (hbal : (wordArg message.data 1).toNat ≤ (balS (shortState state message) message).toNat)
    (hto : (balT (shortState state message) message (wordArg message.data 1)
      (addrArg message.data 0)).toNat + (wordArg message.data 1).toNat < 2 ^ 256)
    {c0 cB c10 c3 c4 cS cT : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
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
    {gas : Nat} {m : Evm fork StateGasMeter}
    (start : At CODE message 0 [] .empty gas state substate (Meter.toNat m))
    {bound : Nat} {runChild : MessageRunner fork StateGasMeter bound}
    (within : GasMeter.gasHeld m.gas ≤ bound) :
    (Shadow.RunsOkS fork bound runChild m within ↔
      wOk fork m.gas (tP1 state message c0 cB c10 c3 c4 cS)
          (originalAt state message.currentTarget (senderSlot message))
          (balS (shortState state message) message)
          (sub (balS (shortState state message) message) (wordArg message.data 1)) false ∧
      wOk fork (tM1 fork m.gas state message c0 cB c10 c3 c4 cS) (308 + slotCost cT)
          (originalAt state message.currentTarget (recipientSlot (addrArg message.data 0)))
          (balT (shortState state message) message (wordArg message.data 1) (addrArg message.data 0))
          (add (balT (shortState state message) message (wordArg message.data 1)
            (addrArg message.data 0)) (wordArg message.data 1)) false ∧
      1892 ≤ (tM2 fork m.gas state message c0 cB c10 c3 c4 cS cT).gasLeft) ∧
    ∀ s, Evm.runFrame (step fork) (step_decreases fork) bound runChild m within = .ok s →
      s.error = none →
      s.running = false ∧ s.output = .empty ∧
      s.state = credited (shortState state message) message (wordArg message.data 1)
        (addrArg message.data 0) ∧
      s.substate = loggedSub fork (shortSubstate substate message) (shortState state message)
        message (wordArg message.data 1) (addrArg message.data 0) ∧
      s.gas.gasLeft + okCost fork state message c0 cB c10 c3 c4 cS cT =
        gas + wBump fork m.gas (originalAt state message.currentTarget (senderSlot message))
            (balS (shortState state message) message)
            (sub (balS (shortState state message) message) (wordArg message.data 1)) +
          wBump fork (tM1 fork m.gas state message c0 cB c10 c3 c4 cS)
            (originalAt state message.currentTarget (recipientSlot (addrArg message.data 0)))
            (balT (shortState state message) message (wordArg message.data 1)
              (addrArg message.data 0))
            (add (balT (shortState state message) message (wordArg message.data 1)
              (addrArg message.data 0)) (wordArg message.data 1)) ∧
      s.gas = { tM2 fork m.gas state message c0 cB c10 c3 c4 cS cT with
        gasLeft := s.gas.gasLeft } := by
  have haccS : hasAccount (shortState state message) message.currentTarget :=
    hasAccount_readSlot (hasAccount_readSlot (hasAccount_readSlot hacc))
  have hacc3 : hasAccount (reads3 (shortState state message) message) message.currentTarget :=
    hasAccount_readSlot (hasAccount_readSlot (hasAccount_readSlot haccS))
  have hacc4 := hasAccount_writeSlot (n := senderSlot message)
    (v := sub (balS (shortState state message) message) (wordArg message.data 1)) hacc3
  have hacc5 := hasAccount_readSlot (n := recipientSlot (addrArg message.data 0))
    (other := message.currentTarget) hacc4
  have hP : tP1 state message c0 cB c10 c3 c4 cS < 97920 := by
    have := Complete.slotCost_le c0; have := Complete.slotCost_le cB
    have := Complete.slotCost_le c10; have := Complete.slotCost_le c3
    have := Complete.slotCost_le c4; have := Complete.slotCost_le cS
    have : mulCost (wordArg message.data 1) ≤ 138 := by unfold mulCost; split <;> omega
    have : capCost (rawFee (shortState state message) message (wordArg message.data 1))
      (storageAt (shortState state message) message.currentTarget 4) ≤ 108 := by
      unfold capCost; split <;> omega
    simp only [tP1, PRE_COST]; omega
  have hQ : 308 + slotCost cT < 97920 := by have := Complete.slotCost_le cT; omega
  have hpre : ∀ g, tP1 state message c0 cB c10 c3 c4 cS ≤ g → Gas.HoareG fork
      (At CODE message 0 [] .empty g state substate)
      (At CODE message 10138 (senderSlot message ::
          sub (balS (shortState state message) message) (wordArg message.data 1) ::
          sub (balS (shortState state message) message) (wordArg message.data 1) ::
          0x40 :: wordArg message.data 1 :: 0 :: wordArg message.data 1 :: addrArg message.data 0 ::
          [0x1699, wordArg message.data 1, addrArg message.data 0, 0x078a,
            BitVec.ofNat 256 (selector message.data)])
        (mapMem (mapMem (MEMK (callerKey message) 6) (callerKey message) 2) (callerKey message) 2)
        (g - tP1 state message c0 cB c10 c3 c4 cS)
        (reads3 (shortState state message) message) (access3 (shortSubstate substate message) message)) := by
    intro g hg
    simp only [tP1] at hg ⊢
    refine Triple.seq (pre hfork (by omega) hsz hsel hv hnp hnb hdep hc0 hcB hc10
      (Nat.le_trans (Nat.le_add_right _ _) hg)) ?_
    refine (bodyW1 (state := shortState state message) (substate := shortSubstate substate message)
      hfork hlong hsz (size_MEMK (callerKey message) 6) hov hfee hbal hc3 hc4 hcS
      (by omega)).consequence (fun _ h => h) ?_
    intro e he
    rw [Nat.sub_sub] at he
    exact he
  have hcT' : coldIn (storeSub fork (access3 (shortSubstate substate message) message)
      message.currentTarget (senderSlot message)
      (originalAt (reads3 (shortState state message) message) message.currentTarget (senderSlot message))
      (storageAt (reads3 (shortState state message) message) message.currentTarget (senderSlot message))
      (sub (balS (shortState state message) message) (wordArg message.data 1)))
      message.currentTarget (recipientSlot (addrArg message.data 0)) = cT := by
    rw [coldIn_storeSub]; exact hcT
  have hmid := fun g (hg : 308 + slotCost cT ≤ g) => bodyW2
    (state := writeSlot (reads3 (shortState state message) message) message.currentTarget
      (senderSlot message) (sub (balS (shortState state message) message) (wordArg message.data 1)))
    (substate := storeSub fork (access3 (shortSubstate substate message) message)
      message.currentTarget (senderSlot message)
      (originalAt (reads3 (shortState state message) message) message.currentTarget (senderSlot message))
      (storageAt (reads3 (shortState state message) message) message.currentTarget (senderSlot message))
      (sub (balS (shortState state message) message) (wordArg message.data 1)))
    (nb := sub (balS (shortState state message) message) (wordArg message.data 1))
    (v := wordArg message.data 1) (a := addrArg message.data 0)
    (sel := BitVec.ofNat 256 (selector message.data))
    (M := mapMem (mapMem (MEMK (callerKey message) 6) (callerKey message) 2) (callerKey message) 2)
    hfork (size_mapMem (size_mapMem (size_MEMK _ _) _ _) _ _) hto hcT' hg
  have hpost := fun g (hg : 1892 ≤ g) => bodyW3 (fork := fork) (message := message)
    (state := writeSlot (readSlot (writeSlot (reads3 (shortState state message) message)
      message.currentTarget (senderSlot message)
      (sub (balS (shortState state message) message) (wordArg message.data 1)))
      message.currentTarget (recipientSlot (addrArg message.data 0))) message.currentTarget
      (recipientSlot (addrArg message.data 0))
      (add (storageAt (writeSlot (reads3 (shortState state message) message)
        message.currentTarget (senderSlot message)
        (sub (balS (shortState state message) message) (wordArg message.data 1)))
        message.currentTarget (recipientSlot (addrArg message.data 0))) (wordArg message.data 1)))
    (substate := storeSub fork (accessSlot (storeSub fork (access3 (shortSubstate substate message) message)
      message.currentTarget (senderSlot message)
      (originalAt (reads3 (shortState state message) message) message.currentTarget (senderSlot message))
      (storageAt (reads3 (shortState state message) message) message.currentTarget (senderSlot message))
      (sub (balS (shortState state message) message) (wordArg message.data 1)))
      message.currentTarget (recipientSlot (addrArg message.data 0))) message.currentTarget
      (recipientSlot (addrArg message.data 0))
      (originalAt (readSlot (writeSlot (reads3 (shortState state message) message)
        message.currentTarget (senderSlot message)
        (sub (balS (shortState state message) message) (wordArg message.data 1)))
        message.currentTarget (recipientSlot (addrArg message.data 0))) message.currentTarget
        (recipientSlot (addrArg message.data 0)))
      (storageAt (readSlot (writeSlot (reads3 (shortState state message) message)
        message.currentTarget (senderSlot message)
        (sub (balS (shortState state message) message) (wordArg message.data 1)))
        message.currentTarget (recipientSlot (addrArg message.data 0))) message.currentTarget
        (recipientSlot (addrArg message.data 0)))
      (add (storageAt (writeSlot (reads3 (shortState state message) message)
        message.currentTarget (senderSlot message)
        (sub (balS (shortState state message) message) (wordArg message.data 1)))
        message.currentTarget (recipientSlot (addrArg message.data 0))) (wordArg message.data 1)))
    (nt := add (storageAt (writeSlot (reads3 (shortState state message) message)
        message.currentTarget (senderSlot message)
        (sub (balS (shortState state message) message) (wordArg message.data 1)))
        message.currentTarget (recipientSlot (addrArg message.data 0))) (wordArg message.data 1))
    (v := wordArg message.data 1) (a := addrArg message.data 0)
    (sel := BitVec.ofNat 256 (selector message.data))
    (M := mapMem (mapMem (mapMem (mapMem (MEMK (callerKey message) 6) (callerKey message) 2)
      (callerKey message) 2) (mkey (addrArg message.data 0)) 2) (mkey (addrArg message.data 0)) 2)
    hstatic (size_mapMem (size_mapMem (size_mapMem (size_mapMem (size_MEMK _ _) _ _) _ _) _ _) _ _)
    (ptr_mapMem (size_mapMem (size_mapMem (size_mapMem (size_MEMK _ _) _ _) _ _) _ _)
      (ptr_mapMem (size_mapMem (size_mapMem (size_MEMK _ _) _ _) _ _)
        (ptr_mapMem (size_mapMem (size_MEMK _ _) _ _)
          (ptr_mapMem (size_MEMK _ _) (ptr_MEMK _ _) _ _) _ _) _ _) _ _) hg
  have hx := Complete.exactS_write hfork hpre hP
    (fun _ _ => by simp only [Complete.getStorage_readSlot]) (by code_fact) (by code_fact)
    hstatic hacc3 (coldIn_accessSlot_self _ _ _)
    (Complete.exactS_write hfork hmid hQ (fun _ _ => by simp only [Complete.getStorage_readSlot])
      (by code_fact) (by code_fact) hstatic
      hacc5 (coldIn_accessSlot_self _ _ _)
      (Complete.exactS_halt hpost (by decide) (fun _ _ => rfl)))
  obtain ⟨hgas, hiff, hend⟩ := hx.run start (runChild := runChild) within
  refine ⟨by
    simp only [originalAt_readSlot, storageAt_readSlot, originalAt_writeSlot hacc3, shortState,
      reads3, balS, balT, debited, tM1, tM2] at hiff ⊢
    exact hiff, fun s hrun hok => ?_⟩
  have hok' := hiff.mp ⟨s, hrun, hok⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := hend s hrun hok
  refine ⟨h1, h2, ?_, ?_, ?_, ?_⟩
  · rw [h3]
  · have eo1 : originalAt (reads3 (shortState state message) message) message.currentTarget
        (senderSlot message) = originalAt (shortState state message) message.currentTarget
        (senderSlot message) := by simp only [reads3, originalAt_readSlot]
    have ec1 : storageAt (reads3 (shortState state message) message) message.currentTarget
        (senderSlot message) = balS (shortState state message) message := by
      simp only [reads3, storageAt_readSlot]
    have eo2 : originalAt (readSlot (writeSlot (reads3 (shortState state message) message)
        message.currentTarget (senderSlot message)
        (sub (balS (shortState state message) message) (wordArg message.data 1)))
        message.currentTarget (recipientSlot (addrArg message.data 0))) message.currentTarget
        (recipientSlot (addrArg message.data 0)) = originalAt (shortState state message)
        message.currentTarget (recipientSlot (addrArg message.data 0)) := by
      rw [originalAt_readSlot, originalAt_writeSlot hacc3]; simp only [reads3, originalAt_readSlot]
    have ec2 : storageAt (readSlot (writeSlot (reads3 (shortState state message) message)
        message.currentTarget (senderSlot message)
        (sub (balS (shortState state message) message) (wordArg message.data 1)))
        message.currentTarget (recipientSlot (addrArg message.data 0))) message.currentTarget
        (recipientSlot (addrArg message.data 0)) = balT (shortState state message) message
        (wordArg message.data 1) (addrArg message.data 0) := by
      rw [storageAt_readSlot]
    rw [h4, eo1, ec1, eo2, ec2]
  · obtain ⟨o1, o2, o3⟩ := hok'
    have e1 := Complete.wMeter_gasLeft o1
    have e2 := Complete.wMeter_gasLeft o2
    have e3 : s.gas.gasLeft = _ := congrArg StateGasMeter.gasLeft h5
    simp only [originalAt_readSlot, storageAt_readSlot, originalAt_writeSlot hacc3, shortState,
      reads3, balS, balT, debited, tM1, tM2, tP1, okCost, readCost, debitCost, creditCost,
      wBump] at e1 e2 e3 o3 ⊢
    omega
  · rw [h5]
    simp only [originalAt_readSlot, storageAt_readSlot, originalAt_writeSlot hacc3, shortState,
      reads3, balS, balT, debited, tM1, tM2]

end UsdtVerify.TransferOk
