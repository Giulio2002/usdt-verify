import UsdtVerify.Usdt.Refill.Approve
import UsdtVerify.Evm.OneWrite

/-!
# approve over the EIP-8037 meter: the exact success condition and gas, with refills (round 42)

`approve(s, v)` not deprecated is a path with one write (`Complete.one_write_sgm`): the
dispatcher, the checks and the hash of the allowance slot (`P`), the SSTORE of the allowance, and
the log and the STOP (`T = 1864`). Over `StateGasMeter`, from a frame `m` with any meter:

- `approve_zero_sgm` (`approve(s, 0)`): the run ends with no error if and only if
  `2997 + price(slot 10) ≤ gas` and `2560 + price(slot 10) + writeCost ≤ gas + bump`, where
  `bump = sstoreBump m.gas A 0` and `A` is the refill of the write of 0 over the allowance
  (97,920 when the slot was 0 at the start of the transaction and is not 0 now, from
  Glamsterdam). Every run that ends with no error has `gasLeft + 2560 + price + writeCost =
  gas + bump`, and its meter is `sstoreMeter m.gas A c 0` for the reservoir and the spill.
- `approve_set_sgm` (`approve(s, v)`, `v ≠ 0`, over an allowance of 0): the same with
  `3190 + price(slot 10) + price(allowance)`, `2753 + …`, and `bump = sstoreBump m.gas 0 S`, where
  `S` is the state gas of the write (97,920 when the slot was 0 at the start of the transaction),
  paid by the reservoir first.

Neither takes a hypothesis on refills or on the reservoir.
-/

namespace UsdtVerify.Approve

open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts
open Transfer TransferOk
open Refill
open Complete (sstoreBump sstoreMeter)

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate}

/-- From 8384 to the SSTORE at 8512 (the hash of the allowance slot), over `StepG`. -/
theorem storePre {v s : U256} {rest : List U256} (hrest : rest.length ≤ 800) {gas : Nat}
    (hg : 192 ≤ gas) {M : ByteArray} (hM : M.size = 96) :
    Gas.HoareG fork (At CODE message 8384 (0x40 :: v :: s :: rest) M gas state substate)
      (At CODE message 8512
        (mapSlot (bitwiseAnd ADDR_MASK (bitwiseAnd ADDR_MASK s))
          (mapSlot (bitwiseAnd ADDR_MASK (bitwiseAnd ADDR_MASK message.caller.toU256)) 5) ::
          v :: v :: 64 :: v :: s :: rest)
        (mapMem (mapMem M (bitwiseAnd ADDR_MASK (bitwiseAnd ADDR_MASK message.caller.toU256)) 5)
          (bitwiseAnd ADDR_MASK (bitwiseAnd ADDR_MASK s))
          (mapSlot (bitwiseAnd ADDR_MASK (bitwiseAnd ADDR_MASK message.caller.toU256)) 5))
        (gas - 192) state substate) := by
  store_pre
  exact Triple.of_imp fun _ h => h

/-- From 8513, after the SSTORE, to the STOP: the POP, the Approval log and the return, over
`StepG` (1864 gas). -/
theorem postA (hstatic : message.isStatic = false) {v s sel : U256} {gas : Nat} (hg : 1864 ≤ gas)
    {M : ByteArray} (hM : M.size = 96) (hptr : loadWord (memoryReadBytes M 64 32) 0 32 = 0x60) :
    Gas.SpecG fork (At CODE message 8513 [v, 0x40, v, s, 0x0cbb, 0x40, v, s, 0x02a2, sel] M gas
        state substate)
      (Halted false .empty (gas - 1864) state
        { substate with logs := substate.logs.push (approvalLog message.currentTarget
          (bitwiseAnd ADDR_MASK message.caller.toU256) (bitwiseAnd ADDR_MASK s) v) }) := by
  refine Triple.seq (Gas.Triple.seqL popR (restate (pc' := 8514) (by decide) rfl rfl
    (g' := gas - 2) (by gas_ok) rfl rfl)) ?_
  refine Triple.seq (logApproval (by simp) hstatic (by omega) hM hptr) ?_
  refine (stopA (by omega)).consequence (fun _ h => h) ?_
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  exact ⟨hr, he, ho, by rw [hgas]; gas_ok, hs, hss⟩

/-- From pc 0 to the SSTORE at 8512 of `approve(s, 0)`, over `StepG`. -/
theorem preZero (hfork : .berlin ≤ fork) (hlong : 68 ≤ message.data.size)
    (hsz : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x095ea7b3)
    (hv : message.value = 0) (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    (hzero : wordArg message.data 1 = 0)
    {c10 : Bool} (hc10 : coldIn substate message.currentTarget 10 = c10) (g : Nat)
    (hg : 696 + slotCost c10 ≤ g) :
    Gas.HoareG fork (At CODE message 0 [] .empty g state substate)
      (At CODE message 8512 (allowArg message :: 0 :: 0 :: 64 :: 0 :: addrArg message.data 0 ::
          [0x0cbb, 0x40, 0, addrArg message.data 0, 0x02a2,
            BitVec.ofNat 256 (selector message.data)])
        (mapMem (mapMem MEM0 (bitwiseAnd ADDR_MASK (bitwiseAnd ADDR_MASK message.caller.toU256)) 5)
          (bitwiseAnd ADDR_MASK (bitwiseAnd ADDR_MASK (addrArg message.data 0)))
          (mapSlot (bitwiseAnd ADDR_MASK (bitwiseAnd ADDR_MASK message.caller.toU256)) 5))
        (g - (696 + slotCost c10)) (readSlot state message.currentTarget 10)
        (accessSlot substate message.currentTarget 10)) := by
  have h1 := prefixA hfork hlong hsz hsel hv hdep hc10 (gas := g) (by omega)
  rw [hzero] at h1
  refine Triple.seq h1 ?_
  refine Triple.seq (checkZero (by simp) (by omega)) ?_
  refine (storePre (by simp) (by omega) size_MEM0).consequence (fun _ h => h) ?_
  intro e he
  have hx : g - (449 + slotCost c10) - 55 - 192 = g - (696 + slotCost c10) := by omega
  rw [hx] at he
  exact he

/-- **approve(s, 0) over the EIP-8037 meter, exactly, at any reservoir, refills allowed.** From
Berlin, from a frame `m` of `StateGasMeter` with any meter whose `toNat` is the fresh frame of
`CODE` with selector 0x095ea7b3, not deprecated, `wordArg 1 = 0`, a frame that is not static and
an account: the run of the loop, for any gas bound and message runner, ends with no error if and
only if `2997 + price(slot 10) ≤ gas` and `2560 + price(slot 10) + writeCost ≤ gas + bump`, where
`bump = sstoreBump m.gas A S` for the refill `A` and the state gas `S` of the write of 0 over the
allowance. Every run that ends with no error stops, with the output empty, the allowance written,
`gasLeft + 2560 + price(slot 10) + writeCost = gas + bump`, and the meter `sstoreMeter m.gas A c S`
for the rest. -/
theorem approve_zero_sgm (hfork : .berlin ≤ fork)
    (hstatic : message.isStatic = false) (hacc : hasAccount state message.currentTarget)
    (hlong : 68 ≤ message.data.size) (hsz : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x095ea7b3) (hv : message.value = 0)
    (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    (hzero : wordArg message.data 1 = 0)
    {c10 cA : Bool} (hc10 : coldIn substate message.currentTarget 10 = c10)
    (hcA : coldIn (accessSlot substate message.currentTarget 10) message.currentTarget
      (allowArg message) = cA) {gas : Nat} {m : Evm fork StateGasMeter}
    (start : At CODE message 0 [] .empty gas state substate (Meter.toNat m))
    {bound : Nat} {runChild : MessageRunner fork StateGasMeter bound}
    (within : GasMeter.gasHeld m.gas ≤ bound) :
    (Shadow.RunsOkS fork bound runChild m within ↔
      696 + slotCost c10 + 2301 ≤ gas ∧
      696 + slotCost c10 + Gas.writeCost fork
          (originalAt (readSlot state message.currentTarget 10) message.currentTarget (allowArg message))
          (storageAt (readSlot state message.currentTarget 10) message.currentTarget (allowArg message))
          0 cA + 1864 ≤
        gas + sstoreBump m.gas
          (sstoreStateRefill fork
            (originalAt (readSlot state message.currentTarget 10) message.currentTarget (allowArg message))
            (storageAt (readSlot state message.currentTarget 10) message.currentTarget (allowArg message)) 0)
          (sstoreStateGas fork
            (originalAt (readSlot state message.currentTarget 10) message.currentTarget (allowArg message))
            (storageAt (readSlot state message.currentTarget 10) message.currentTarget (allowArg message)) 0)) ∧
    ∀ s, Evm.runFrame (step fork) (step_decreases fork) bound runChild m within = .ok s →
      s.error = none →
      s.running = false ∧ s.output = .empty ∧
      s.state = writeSlot (readSlot state message.currentTarget 10) message.currentTarget
        (allowArg message) 0 ∧
      s.gas.gasLeft + (696 + slotCost c10) + Gas.writeCost fork
          (originalAt (readSlot state message.currentTarget 10) message.currentTarget (allowArg message))
          (storageAt (readSlot state message.currentTarget 10) message.currentTarget (allowArg message))
          0 cA + 1864 =
        gas + sstoreBump m.gas
          (sstoreStateRefill fork
            (originalAt (readSlot state message.currentTarget 10) message.currentTarget (allowArg message))
            (storageAt (readSlot state message.currentTarget 10) message.currentTarget (allowArg message)) 0)
          (sstoreStateGas fork
            (originalAt (readSlot state message.currentTarget 10) message.currentTarget (allowArg message))
            (storageAt (readSlot state message.currentTarget 10) message.currentTarget (allowArg message)) 0) ∧
      s.gas = { sstoreMeter m.gas
          (sstoreStateRefill fork
            (originalAt (readSlot state message.currentTarget 10) message.currentTarget (allowArg message))
            (storageAt (readSlot state message.currentTarget 10) message.currentTarget (allowArg message)) 0)
          (sstoreCost fork
            (originalAt (readSlot state message.currentTarget 10) message.currentTarget (allowArg message))
            (storageAt (readSlot state message.currentTarget 10) message.currentTarget (allowArg message)) 0 cA)
          (sstoreStateGas fork
            (originalAt (readSlot state message.currentTarget 10) message.currentTarget (allowArg message))
            (storageAt (readSlot state message.currentTarget 10) message.currentTarget (allowArg message)) 0)
          with gasLeft := s.gas.gasLeft } := by
  have hP : 696 + slotCost c10 < 97920 := by have := Complete.slotCost_le c10; omega
  have hpost := fun g (hg : 1864 ≤ g) => postA (state := writeSlot (readSlot state
      message.currentTarget 10) message.currentTarget (allowArg message) 0)
    (substate := storeSub fork (accessSlot substate message.currentTarget 10) message.currentTarget
      (allowArg message)
      (originalAt (readSlot state message.currentTarget 10) message.currentTarget (allowArg message))
      (storageAt (readSlot state message.currentTarget 10) message.currentTarget (allowArg message)) 0)
    (v := 0) (s := addrArg message.data 0) (sel := BitVec.ofNat 256 (selector message.data))
    hstatic (gas := g) hg (size_mapMem (size_mapMem size_MEM0 (bitwiseAnd ADDR_MASK (bitwiseAnd ADDR_MASK message.caller.toU256)) 5) (bitwiseAnd ADDR_MASK (bitwiseAnd ADDR_MASK (addrArg message.data 0))) (mapSlot (bitwiseAnd ADDR_MASK (bitwiseAnd ADDR_MASK message.caller.toU256)) 5))
    (ptr_mapMem (size_mapMem size_MEM0 (bitwiseAnd ADDR_MASK (bitwiseAnd ADDR_MASK message.caller.toU256)) 5) (ptr_mapMem size_MEM0 mload_MEM0 (bitwiseAnd ADDR_MASK (bitwiseAnd ADDR_MASK message.caller.toU256)) 5) (bitwiseAnd ADDR_MASK (bitwiseAnd ADDR_MASK (addrArg message.data 0))) (mapSlot (bitwiseAnd ADDR_MASK (bitwiseAnd ADDR_MASK message.caller.toU256)) 5))
  refine ⟨Complete.one_write_sgm hfork (preZero hfork hlong hsz hsel hv hdep hzero hc10) hP
    (fun _ _ => rfl) (by code_fact) (by code_fact) hstatic (hasAccount_readSlot hacc) hcA hpost
    (by decide) (fun _ _ => rfl) start within, fun s hrun hok => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5, -, h7, h8⟩ := Complete.one_write_end hfork
    (preZero hfork hlong hsz hsel hv hdep hzero hc10) hP (fun _ _ => rfl) (by code_fact)
    (by code_fact) hstatic (hasAccount_readSlot hacc) hcA hpost (by decide) (fun _ _ => rfl) start
    hrun hok
  exact ⟨h3, h4, h5, by omega, h8⟩

/-- From pc 0 to the SSTORE at 8512 of `approve(s, v)`, `v ≠ 0`, over an allowance of 0. -/
theorem preSet (hfork : .berlin ≤ fork) (hlong : 68 ≤ message.data.size)
    (hsz : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x095ea7b3)
    (hv : message.value = 0) (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    (hnz : (wordArg message.data 1) ≠ 0)
    (hallow : storageAt state message.currentTarget (allowArg message) = 0)
    {c10 cA : Bool} (hc10 : coldIn substate message.currentTarget 10 = c10)
    (hcA : coldIn (accessSlot substate message.currentTarget 10) message.currentTarget
      (allowArg message) = cA) (g : Nat)
    (hg : 889 + slotCost c10 + slotCost cA ≤ g) :
    Gas.HoareG fork (At CODE message 0 [] .empty g state substate)
      (At CODE message 8512 (allowArg message :: (wordArg message.data 1) :: (wordArg message.data 1) :: 64 :: (wordArg message.data 1) ::
          addrArg message.data 0 :: [0x0cbb, 0x40, (wordArg message.data 1), addrArg message.data 0, 0x02a2,
            BitVec.ofNat 256 (selector message.data)])
        (mapMem (mapMem (mapMem (mapMem MEM0 (bitwiseAnd ADDR_MASK (bitwiseAnd ADDR_MASK message.caller.toU256)) 5) (bitwiseAnd ADDR_MASK (bitwiseAnd ADDR_MASK (addrArg message.data 0))) (mapSlot (bitwiseAnd ADDR_MASK (bitwiseAnd ADDR_MASK message.caller.toU256)) 5)) (bitwiseAnd ADDR_MASK (bitwiseAnd ADDR_MASK message.caller.toU256)) 5) (bitwiseAnd ADDR_MASK (bitwiseAnd ADDR_MASK (addrArg message.data 0))) (mapSlot (bitwiseAnd ADDR_MASK (bitwiseAnd ADDR_MASK message.caller.toU256)) 5)) (g - (889 + slotCost c10 + slotCost cA)) (readSlot (readSlot state message.currentTarget 10) message.currentTarget (allowArg message)) (accessSlot (accessSlot substate message.currentTarget 10) message.currentTarget (allowArg message))) := by
  have h1 := prefixA hfork hlong hsz hsel hv hdep hc10 (gas := g) (by omega)
  refine Triple.seq h1 ?_
  refine Triple.seq (checkNonzero hfork hnz (by simp) hcA
    (by rw [storageAt_readSlot]; exact hallow) (by omega) size_MEM0) ?_
  refine (storePre (by simp) (by omega) (size_mapMem (size_mapMem size_MEM0 _ _) _ _)).consequence
    (fun _ h => h) ?_
  intro e he
  have hx : g - (449 + slotCost c10) - (248 + slotCost cA) - 192 =
      g - (889 + slotCost c10 + slotCost cA) := by omega
  rw [hx] at he
  exact he

/-- **approve(s, v), v ≠ 0, over the EIP-8037 meter, exactly, at any reservoir.** As
`approve_zero_sgm`, over an allowance of 0, with `3190 + price(slot 10) + price(allowance)` and
`2753 + price(slot 10) + price(allowance) + writeCost`. The write is warm. Its state gas (97,920 when
the slot was 0 at the start of the transaction, from Glamsterdam) comes from the reservoir first,
which is what `bump` counts. -/
theorem approve_set_sgm (hfork : .berlin ≤ fork)
    (hstatic : message.isStatic = false) (hacc : hasAccount state message.currentTarget)
    (hlong : 68 ≤ message.data.size) (hsz : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x095ea7b3) (hv : message.value = 0)
    (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    (hnz : (wordArg message.data 1) ≠ 0)
    (hallow : storageAt state message.currentTarget (allowArg message) = 0)
    {c10 cA : Bool} (hc10 : coldIn substate message.currentTarget 10 = c10)
    (hcA : coldIn (accessSlot substate message.currentTarget 10) message.currentTarget
      (allowArg message) = cA) {gas : Nat} {m : Evm fork StateGasMeter}
    (start : At CODE message 0 [] .empty gas state substate (Meter.toNat m))
    {bound : Nat} {runChild : MessageRunner fork StateGasMeter bound}
    (within : GasMeter.gasHeld m.gas ≤ bound) :
    (Shadow.RunsOkS fork bound runChild m within ↔
      889 + slotCost c10 + slotCost cA + 2301 ≤ gas ∧
      889 + slotCost c10 + slotCost cA + Gas.writeCost fork (originalAt (readSlot (readSlot state message.currentTarget 10) message.currentTarget (allowArg message)) message.currentTarget (allowArg message)) (storageAt (readSlot (readSlot state message.currentTarget 10) message.currentTarget (allowArg message)) message.currentTarget (allowArg message)) (wordArg message.data 1) false + 1864 ≤
        gas + sstoreBump m.gas (sstoreStateRefill fork (originalAt (readSlot (readSlot state message.currentTarget 10) message.currentTarget (allowArg message)) message.currentTarget (allowArg message)) (storageAt (readSlot (readSlot state message.currentTarget 10) message.currentTarget (allowArg message)) message.currentTarget (allowArg message)) (wordArg message.data 1))
          (sstoreStateGas fork (originalAt (readSlot (readSlot state message.currentTarget 10) message.currentTarget (allowArg message)) message.currentTarget (allowArg message)) (storageAt (readSlot (readSlot state message.currentTarget 10) message.currentTarget (allowArg message)) message.currentTarget (allowArg message)) (wordArg message.data 1))) ∧
    ∀ s, Evm.runFrame (step fork) (step_decreases fork) bound runChild m within = .ok s →
      s.error = none →
      s.running = false ∧ s.output = .empty ∧
      s.state = writeSlot (readSlot (readSlot state message.currentTarget 10) message.currentTarget (allowArg message)) message.currentTarget (allowArg message) (wordArg message.data 1) ∧
      s.gas.gasLeft + (889 + slotCost c10 + slotCost cA) + Gas.writeCost fork (originalAt (readSlot (readSlot state message.currentTarget 10) message.currentTarget (allowArg message)) message.currentTarget (allowArg message)) (storageAt (readSlot (readSlot state message.currentTarget 10) message.currentTarget (allowArg message)) message.currentTarget (allowArg message)) (wordArg message.data 1) false +
          1864 =
        gas + sstoreBump m.gas (sstoreStateRefill fork (originalAt (readSlot (readSlot state message.currentTarget 10) message.currentTarget (allowArg message)) message.currentTarget (allowArg message)) (storageAt (readSlot (readSlot state message.currentTarget 10) message.currentTarget (allowArg message)) message.currentTarget (allowArg message)) (wordArg message.data 1))
          (sstoreStateGas fork (originalAt (readSlot (readSlot state message.currentTarget 10) message.currentTarget (allowArg message)) message.currentTarget (allowArg message)) (storageAt (readSlot (readSlot state message.currentTarget 10) message.currentTarget (allowArg message)) message.currentTarget (allowArg message)) (wordArg message.data 1)) ∧
      s.gas = { sstoreMeter m.gas (sstoreStateRefill fork (originalAt (readSlot (readSlot state message.currentTarget 10) message.currentTarget (allowArg message)) message.currentTarget (allowArg message)) (storageAt (readSlot (readSlot state message.currentTarget 10) message.currentTarget (allowArg message)) message.currentTarget (allowArg message)) (wordArg message.data 1))
          (sstoreCost fork (originalAt (readSlot (readSlot state message.currentTarget 10) message.currentTarget (allowArg message)) message.currentTarget (allowArg message)) (storageAt (readSlot (readSlot state message.currentTarget 10) message.currentTarget (allowArg message)) message.currentTarget (allowArg message)) (wordArg message.data 1) false) (sstoreStateGas fork (originalAt (readSlot (readSlot state message.currentTarget 10) message.currentTarget (allowArg message)) message.currentTarget (allowArg message)) (storageAt (readSlot (readSlot state message.currentTarget 10) message.currentTarget (allowArg message)) message.currentTarget (allowArg message)) (wordArg message.data 1))
          with gasLeft := s.gas.gasLeft } := by
  have hP : 889 + slotCost c10 + slotCost cA < 97920 := by
    have := Complete.slotCost_le c10; have := Complete.slotCost_le cA; omega
  have hpost := fun g (hg : 1864 ≤ g) => postA (state := writeSlot (readSlot (readSlot state message.currentTarget 10) message.currentTarget (allowArg message)) message.currentTarget
      (allowArg message) (wordArg message.data 1))
    (substate := storeSub fork (accessSlot (accessSlot substate message.currentTarget 10) message.currentTarget (allowArg message)) message.currentTarget (allowArg message) (originalAt (readSlot (readSlot state message.currentTarget 10) message.currentTarget (allowArg message)) message.currentTarget (allowArg message)) (storageAt (readSlot (readSlot state message.currentTarget 10) message.currentTarget (allowArg message)) message.currentTarget (allowArg message)) (wordArg message.data 1))
    (v := (wordArg message.data 1)) (s := addrArg message.data 0) (sel := BitVec.ofNat 256 (selector message.data))
    hstatic (gas := g) hg (size_mapMem (size_mapMem (size_mapMem (size_mapMem size_MEM0 (bitwiseAnd ADDR_MASK (bitwiseAnd ADDR_MASK message.caller.toU256)) 5) (bitwiseAnd ADDR_MASK (bitwiseAnd ADDR_MASK (addrArg message.data 0))) (mapSlot (bitwiseAnd ADDR_MASK (bitwiseAnd ADDR_MASK message.caller.toU256)) 5)) (bitwiseAnd ADDR_MASK (bitwiseAnd ADDR_MASK message.caller.toU256)) 5) (bitwiseAnd ADDR_MASK (bitwiseAnd ADDR_MASK (addrArg message.data 0))) (mapSlot (bitwiseAnd ADDR_MASK (bitwiseAnd ADDR_MASK message.caller.toU256)) 5))
    (ptr_mapMem (size_mapMem (size_mapMem (size_mapMem size_MEM0 (bitwiseAnd ADDR_MASK (bitwiseAnd ADDR_MASK message.caller.toU256)) 5) (bitwiseAnd ADDR_MASK (bitwiseAnd ADDR_MASK (addrArg message.data 0))) (mapSlot (bitwiseAnd ADDR_MASK (bitwiseAnd ADDR_MASK message.caller.toU256)) 5)) (bitwiseAnd ADDR_MASK (bitwiseAnd ADDR_MASK message.caller.toU256)) 5)
      (ptr_mapMem (size_mapMem (size_mapMem size_MEM0 (bitwiseAnd ADDR_MASK (bitwiseAnd ADDR_MASK message.caller.toU256)) 5) (bitwiseAnd ADDR_MASK (bitwiseAnd ADDR_MASK (addrArg message.data 0))) (mapSlot (bitwiseAnd ADDR_MASK (bitwiseAnd ADDR_MASK message.caller.toU256)) 5))
        (ptr_mapMem (size_mapMem size_MEM0 (bitwiseAnd ADDR_MASK (bitwiseAnd ADDR_MASK message.caller.toU256)) 5) (ptr_mapMem size_MEM0 mload_MEM0 (bitwiseAnd ADDR_MASK (bitwiseAnd ADDR_MASK message.caller.toU256)) 5) (bitwiseAnd ADDR_MASK (bitwiseAnd ADDR_MASK (addrArg message.data 0))) (mapSlot (bitwiseAnd ADDR_MASK (bitwiseAnd ADDR_MASK message.caller.toU256)) 5))
        (bitwiseAnd ADDR_MASK (bitwiseAnd ADDR_MASK message.caller.toU256)) 5) (bitwiseAnd ADDR_MASK (bitwiseAnd ADDR_MASK (addrArg message.data 0))) (mapSlot (bitwiseAnd ADDR_MASK (bitwiseAnd ADDR_MASK message.caller.toU256)) 5))
  have hpre := preSet hfork hlong hsz hsel hv hdep hnz hallow hc10 hcA
  have hacc' : hasAccount (readSlot (readSlot state message.currentTarget 10) message.currentTarget
      (allowArg message)) message.currentTarget :=
    hasAccount_readSlot (hasAccount_readSlot hacc)
  have hcold : coldIn (accessSlot (accessSlot substate message.currentTarget 10) message.currentTarget (allowArg message)) message.currentTarget (allowArg message) = false :=
    coldIn_accessSlot_self _ _ _
  refine ⟨Complete.one_write_sgm hfork hpre hP (fun _ _ => rfl) (by code_fact) (by code_fact)
    hstatic hacc' hcold hpost (by decide) (fun _ _ => rfl) start within, fun s hrun hok => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5, -, h7, h8⟩ := Complete.one_write_end hfork hpre hP (fun _ _ => rfl)
    (by code_fact) (by code_fact) hstatic hacc' hcold hpost (by decide) (fun _ _ => rfl) start
    hrun hok
  exact ⟨h3, h4, h5, by omega, h8⟩

end UsdtVerify.Approve
