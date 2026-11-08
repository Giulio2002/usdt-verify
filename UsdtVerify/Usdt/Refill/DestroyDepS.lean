import UsdtVerify.Usdt.Refill.ChainOwner
import UsdtVerify.Usdt.Spec.Deprecated.Destroy

/-!
# The tail of deprecated destroyBlackFunds over the EIP-8037 meter, exactly (round 44)

After the CALL of deprecated destroyBlackFunds answers with no error, the code at 4892 hands the
answer `d` back to the body at 8008, writes `balances[a] := 0` (SSTORE at 8078), then
`_totalSupply := _totalSupply - d` (SSTORE at 8094), logs and stops. Both writes may refill.

- `zeroToWD`, `tailW1D`: from 4892 to the first SSTORE (184 gas, on the 160-byte memory of the
  forward). `destroyW2` (round 43) goes from the first SSTORE to the second. `tailPostD`: from
  the second SSTORE to the STOP (1364 gas).
- `tailDM1`, `tailDM2`: the meters after the two writes, from the meter `g` at 4892 (`wMeter`).
- `tailD_sgm`: from a frame of `StateGasMeter` with any meter whose `toNat` is the frame at 4892
  (the answer 1 on the stack, the memory `M` of 160 bytes with the free memory pointer, a frame
  that is not static and an account of the contract), for any gas bound and message runner: the
  run ends with no error if and only if `wOk` of the first write, `wOk` of the second write from
  the meter after the first, and 1364 gas left after the second. Every run that ends with no
  error stops in `tailState` and `tailSub` with the word `d = resWord M`, and its meter is the
  meter after the second write less 1364 execution gas. No hypothesis on refills or on the
  reservoir.
-/

namespace UsdtVerify.DeprecatedDestroy

open EthLib.Base (Fork U256 toAddressMasked)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts
open Deprecated DeprecatedBalance Transfer TransferOk Owner Admin BlackList Destroy DestroySpec
open Complete (wBump wSgm wOk wMeter ExactS)

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate}

/-- At 8008 on the 160-byte memory: from the `JUMPDEST` to the `SSTORE` of `balances[a]` (8078). -/
theorem zeroToWD {a b : U256} {rest : List U256} (hrest : rest.length ≤ 800) {M : ByteArray}
    (hM : M.size = 160) {gas : Nat} (hg : 108 ≤ gas) :
    Gas.HoareG fork (At CODE message 8008 (b :: 0 :: a :: rest) M gas state substate)
      (At CODE message 8078 (mapSlot (mkey a) 2 :: 0 :: 0 :: b :: a :: rest) (mapMem M (mkey a) 2)
        (gas - 108) state substate) := by
  step jumpdestR
  step swapR 0
  norm
  step popR
  step pushR 1 (0 : U256)
  step pushR 1 (0x02 : U256)
  step pushR 1 (0 : U256)
  step dupR 4
  step hashTail160 (by simp; omega) hM (by gas_ok)
  step dupR 1
  step swapR 0
  norm
  exact restate (by decide) rfl rfl (by gas_ok) rfl rfl

/-- From 4892 after a CALL that succeeded to the `SSTORE` of `balances[a]` (8078). -/
theorem tailW1D {a x U : U256} {M : ByteArray} (hM : M.size = 160)
    (hptr : loadWord (memoryReadBytes M 64 32) 0 32 = 0x60) {gas : Nat} (hg : 184 ≤ gas) :
    Gas.HoareG fork (At CODE message 4892 [1, 0x84, 0x70a08231, U, 0, a, 0x1f48, 0, a, 0x09b6, x] M
        gas state substate)
      (At CODE message 8078 (mapSlot (mkey a) 2 :: 0 :: 0 :: resWord M :: a :: [0x09b6, x])
        (mapMem M (mkey a) 2) (gas - 184) state substate) := by
  refine Triple.seq (okTailD hM hptr (rest := [0, a, 0x09b6, x]) (by simp) (by omega)) ?_
  refine Triple.seq (zeroToWD (by simp) hM (by omega)) ?_
  exact restate rfl rfl rfl (by gas_ok) rfl rfl

/-- From the `POP` at 8095 after the `SSTORE` of `_totalSupply` to the STOP, on a 160-byte memory. -/
theorem tailPostD {a b c x : U256} (hstatic : message.isStatic = false) {M : ByteArray}
    (hM : M.size = 160) (hptr : loadWord (memoryReadBytes M 64 32) 0 32 = 0x60) {gas : Nat}
    (hg : 1364 ≤ gas) :
    Gas.SpecG fork (At CODE message 8095 [c, b, a, 0x09b6, x] M gas state substate)
      (Halted false .empty (gas - 1364) state
        { substate with logs := substate.logs.push (destroyLog message.currentTarget (mkey a) b) }) := by
  refine Triple.seq (Gas.Triple.seqL popR (restate (pc' := 8096) (by decide) rfl rfl
    (g' := gas - 2) (by gas_ok) rfl rfl)) ?_
  refine (logBlockD hstatic hM hptr (by omega)).consequence (fun _ h => h) ?_
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  exact ⟨hr, he, ho, by rw [hgas]; gas_ok, hs, hss⟩

/-- The meter after the write of `balances[a]` in the tail, from the meter `g` at 4892. -/
abbrev tailDM1 (fork : Fork) (g : StateGasMeter) (S : State.TransactionState)
    (C : EthLib.Base.Address) (a : U256) (cB : Bool) : StateGasMeter :=
  wMeter fork g 184 (originalAt S C (mapSlot a 2)) (storageAt S C (mapSlot a 2)) 0 cB

/-- The meter after the write of `_totalSupply` in the tail. -/
abbrev tailDM2 (fork : Fork) (g : StateGasMeter) (S : State.TransactionState)
    (C : EthLib.Base.Address) (a d : U256) (cB c1 : Bool) : StateGasMeter :=
  wMeter fork (tailDM1 fork g S C a cB) (33 + slotCost c1) (originalAt S C 1)
    (storageAt (writeSlot S C (mapSlot a 2) 0) C 1)
    (sub (storageAt (writeSlot S C (mapSlot a 2) 0) C 1) d) false

/-- **The tail of deprecated destroyBlackFunds over the EIP-8037 meter, exactly.** See the module
doc. -/
theorem tailD_sgm (hfork : .berlin ≤ fork) {a x U : U256} (ha : mkey a = a)
    (hstatic : message.isStatic = false) {S : State.TransactionState} {ss : Substate}
    (hacc : hasAccount S message.currentTarget) {M : ByteArray}
    (hM : M.size = 160) (hptr : loadWord (memoryReadBytes M 64 32) 0 32 = 0x60) {cB c1 : Bool}
    (hcB : coldIn ss message.currentTarget (mapSlot a 2) = cB)
    (hc1 : coldIn (accessSlot ss message.currentTarget (mapSlot a 2)) message.currentTarget 1 = c1)
    {y : Evm fork StateGasMeter}
    (start : At CODE message 4892 [1, 0x84, 0x70a08231, U, 0, a, 0x1f48, 0, a, 0x09b6, x] M
      y.gas.gasLeft S ss (Meter.toNat y))
    {bound : Nat} {runChild : MessageRunner fork StateGasMeter bound}
    (within : GasMeter.gasHeld y.gas ≤ bound) :
    (Shadow.RunsOkS fork bound runChild y within ↔
      wOk fork y.gas 184 (originalAt S message.currentTarget (mapSlot a 2))
          (storageAt S message.currentTarget (mapSlot a 2)) 0 cB ∧
      wOk fork (tailDM1 fork y.gas S message.currentTarget a cB) (33 + slotCost c1)
          (originalAt S message.currentTarget 1)
          (storageAt (writeSlot S message.currentTarget (mapSlot a 2) 0) message.currentTarget 1)
          (sub (storageAt (writeSlot S message.currentTarget (mapSlot a 2) 0) message.currentTarget 1)
            (resWord M)) false ∧
      1364 ≤ (tailDM2 fork y.gas S message.currentTarget a (resWord M) cB c1).gasLeft) ∧
    ∀ s, Evm.runFrame (step fork) (step_decreases fork) bound runChild y within = .ok s →
      s.error = none →
      s.running = false ∧ s.output = .empty ∧
      s.state = tailState S message.currentTarget a (resWord M) ∧
      s.substate = tailSub fork ss S message.currentTarget a (resWord M) ∧
      s.gas = { tailDM2 fork y.gas S message.currentTarget a (resWord M) cB c1 with
        gasLeft := (tailDM2 fork y.gas S message.currentTarget a (resWord M) cB c1).gasLeft -
          1364 } := by
  have hM1 : (mapMem M (mkey a) 2).size = 160 := size_mapMem160 hM _ _
  have hp1 := ptr_mapMem160 hM hptr (mkey a) 2
  rw [ha] at hM1 hp1
  have hacc2 := hasAccount_writeSlot (n := mapSlot a 2) (v := 0) hacc
  have hacc3 := hasAccount_readSlot (n := 1) (other := message.currentTarget) hacc2
  have hc1' : coldIn (storeSub fork ss message.currentTarget (mapSlot a 2)
      (originalAt S message.currentTarget (mapSlot a 2)) (storageAt S message.currentTarget
        (mapSlot a 2)) 0) message.currentTarget 1 = c1 := by
    rw [TransferFee.coldIn_storeSub']; exact hc1
  have hw1 := fun g (hg : 184 ≤ g) => tailW1D (fork := fork) (message := message) (state := S)
    (substate := ss) (a := a) (x := x) (U := U) hM hptr hg
  simp only [ha] at hw1
  have hw2 := fun g (hg : 33 + slotCost c1 ≤ g) => destroyW2 (a := a) (b := resWord M) (x := x)
    (M := mapMem M a 2) (state := writeSlot S message.currentTarget (mapSlot a 2) 0)
    (substate := storeSub fork ss message.currentTarget (mapSlot a 2)
      (originalAt S message.currentTarget (mapSlot a 2)) (storageAt S message.currentTarget
        (mapSlot a 2)) 0)
    hfork hc1' (gas := g) hg
  have hpost := fun g (hg : 1364 ≤ g) => tailPostD (fork := fork) (message := message)
    (a := a) (b := resWord M)
    (c := sub (storageAt (writeSlot S message.currentTarget (mapSlot a 2) 0) message.currentTarget
      1) (resWord M)) (x := x) (M := mapMem M a 2)
    (state := writeSlot (readSlot (writeSlot S message.currentTarget (mapSlot a 2) 0)
      message.currentTarget 1) message.currentTarget 1
      (sub (storageAt (writeSlot S message.currentTarget (mapSlot a 2) 0) message.currentTarget 1)
        (resWord M)))
    (substate := storeSub fork (accessSlot (storeSub fork ss message.currentTarget (mapSlot a 2)
      (originalAt S message.currentTarget (mapSlot a 2)) (storageAt S message.currentTarget
        (mapSlot a 2)) 0) message.currentTarget 1) message.currentTarget 1
      (originalAt (readSlot (writeSlot S message.currentTarget (mapSlot a 2) 0)
        message.currentTarget 1) message.currentTarget 1)
      (storageAt (readSlot (writeSlot S message.currentTarget (mapSlot a 2) 0)
        message.currentTarget 1) message.currentTarget 1)
      (sub (storageAt (writeSlot S message.currentTarget (mapSlot a 2) 0) message.currentTarget 1)
        (resWord M)))
    hstatic hM1 hp1 hg
  have hx := Complete.exactS_write hfork hw1 (by decide) (fun _ _ => rfl)
    (by code_fact) (by code_fact) hstatic hacc hcB
    (Complete.exactS_write hfork hw2 (by have := Complete.slotCost_le c1; omega) (fun _ _ => rfl)
      (by code_fact) (by code_fact) hstatic hacc3 (coldIn_accessSlot_self _ _ _)
      (Complete.exactS_halt hpost (by decide) (fun _ _ => rfl)))
  obtain ⟨-, hiff, hend⟩ := hx.run start (runChild := runChild) within
  simp only [originalAt_readSlot, storageAt_readSlot, originalAt_writeSlot hacc] at hiff
  refine ⟨hiff, fun s hrun hok => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := hend s hrun hok
  simp only [originalAt_readSlot, storageAt_readSlot, originalAt_writeSlot hacc] at h5
  refine ⟨h1, h2, ?_, ?_, h5⟩
  · rw [h3, writeSlot_readSlot _ _ hacc2]
  · rw [h4, storeSub_accessSlot]
    simp only [originalAt_readSlot, originalAt_writeSlot hacc, storageAt_readSlot, ha]

end UsdtVerify.DeprecatedDestroy
