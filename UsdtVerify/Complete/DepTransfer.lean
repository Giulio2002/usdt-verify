import UsdtVerify.Complete.DepBalance
import UsdtVerify.Functions.DeprecatedTransfer
import UsdtVerify.Functions.DeprecatedTransferFrom
import UsdtVerify.Functions.ApproveRevert

/-!
# Completeness of deprecated transfer(address,uint256), for any gas and any runner

`prefixG_transfer` (pc 0 to EXTCODESIZE at 5739, over `StepG`), `dep_transfer_split` and
`dep_transfer_complete`: every run of a deprecated `transfer` call that ends with no error, with
any gas, any gas bound and ANY message runner, passed the paused check and the caller's
blacklist check, and is the forward `transferByLegacy(caller, to, value)` to the upgraded address
(`Sends … (dataT message)`): the runner gave a frame with no error, and the run stopped with no
output; gas, state and substate exact (those of `incorporateChild`).

The paused and blacklisted cases are excluded by `Transfer.spec_paused` and
`Transfer.spec_blacklisted` (both over `StepG`). Named hypotheses `hcode` (the code `c` of the
upgraded account is found in the state) and `hdel` (from Pectra, `c` is no delegation); the
coldness flags `c0`, `cB`, `c10`, `cU` are named by `hc0`, `hcB`, `hc10`, `hcU`.
-/

namespace UsdtVerify.Complete

open EthLib.Base (Fork U256 toAddressMasked)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open UsdtVerify.Gas
open GasCosts
open Deprecated DeprecatedBalance DeprecatedTransfer DeprecatedTransferFrom Transfer TransferOk
  TransferFrom

variable {fork : Fork} {bound : Nat} {runChild : MessageRunner fork Nat bound}
  {message : Message fork} {state : State.TransactionState} {substate : Substate}

/-- From pc 0 to 5739 (EXTCODESIZE of the upgraded address), deprecated `transfer`, over
`StepG`. -/
theorem prefixG_transfer (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xa9059cbb)
    (hv : message.value = 0)
    (hnp : byte20 (storageAt state message.currentTarget 0) = 0)
    (hnb : (storageAt state message.currentTarget (blackSlot message)).toNat % 256 = 0)
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0)
    {c0 cB c10 : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hcB : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget
      (blackSlot message) = cB)
    (hc10 : coldIn (accessSlot (accessSlot substate message.currentTarget 0) message.currentTarget
      (blackSlot message)) message.currentTarget 10 = c10)
    {gas : Nat} (hg : 1329 + slotCost c0 + slotCost cB + slotCost c10 ≤ gas) :
    HoareG fork (At CODE message 0 [] .empty gas state substate)
      (At CODE message 5739
        [upWord (storageAt state message.currentTarget 10),
          upWord (storageAt state message.currentTarget 10), 0, 0x60, 0x64, 0x60, 0, 0xc4,
          0x6e18980a, upWord (storageAt state message.currentTarget 10),
          wordArg message.data 1, addrArg message.data 0, 0x078a,
          BitVec.ofNat 256 (selector message.data)]
        (memT message) (gas - (1329 + slotCost c0 + slotCost cB + slotCost c10))
        (shortState state message) (shortSubstate substate message)) := by
  have ht : tested (BitVec.ofNat 256 (selector message.data)) ENTRIES = 22 := by
    rw [hsel]; decide
  have hb : branch (BitVec.ofNat 256 (selector message.data)) 54 (entrySize 4 2) ENTRIES =
      1866 := by
    rw [hsel]; decide
  have h1 := dispatch (state := state) (substate := substate) hsize hsize' (gas := gas)
    (by rw [ht]; gas_ok)
  rw [ht, hb] at h1
  refine Triple.seq h1 ?_
  step Transfer.entry hv (by gas_ok)
  step Transfer.notPaused hfork (by simp) hnp hc0 (by gas_ok)
  step blackLookup hfork (by simp) hcB (by gas_ok)
  step jumpiR (blackTest_ne (by rw [storageAt_readSlot]; exact hnb))
  step repc (pc' := 5481) (by decide)
  step depSetW hfork (Or.inl ⟨rfl, rfl⟩) (by simp)
    (by rw [storageAt_readSlot, storageAt_readSlot]; exact hdep) hc10 (by gas_ok)
  step upLoad (state := readSlot (readSlot state message.currentTarget 0) message.currentTarget
    (blackSlot message)) hfork (Or.inl ⟨rfl, rfl⟩) (by simp) (by gas_ok)
  rw [storageAt_readSlot, storageAt_readSlot]
  step pushR 4 (0x6e18980a : U256)
  step Gas.callerG (by code_fact) (by code_fact) (by gas_ok) (by stk_ok)
  step dupR 4
  step dupR 4
  step encode3 (Or.inl ⟨rfl, rfl⟩) (size_MEMK _ _) (ptr_MEMK _ _)
    (rest := [wordArg message.data 1, addrArg message.data 0, 0x078a,
      BitVec.ofNat 256 (selector message.data)]) (by simp) (by gas_ok)
  exact Gas.reshapeG rfl rfl (by gas_ok)

theorem dep_transfer_split (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xa9059cbb)
    (hv : message.value = 0)
    (hnp : byte20 (storageAt state message.currentTarget 0) = 0)
    (hnb : (storageAt state message.currentTarget (blackSlot message)).toNat % 256 = 0)
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0)
    {c0 cB c10 : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hcB : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget
      (blackSlot message) = cB)
    (hc10 : coldIn (accessSlot (accessSlot substate message.currentTarget 0) message.currentTarget
      (blackSlot message)) message.currentTarget 10 = c10)
    {gas : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) :
    1329 + slotCost c0 + slotCost cB + slotCost c10 ≤ gas ∧ ∃ z' w,
      At CODE message 5739
        [upWord (storageAt state message.currentTarget 10),
          upWord (storageAt state message.currentTarget 10), 0, 0x60, 0x64, 0x60, 0, 0xc4,
          0x6e18980a, upWord (storageAt state message.currentTarget 10),
          wordArg message.data 1, addrArg message.data 0, 0x078a,
          BitVec.ofNat 256 (selector message.data)]
        (memT message) (gas - (1329 + slotCost c0 + slotCost cB + slotCost c10))
        (shortState state message) (shortSubstate substate message) z' ∧
      Evm.runFrame (step fork) (step_decreases fork) bound runChild z' w = .ok s :=
  ok_split (Nat.le_refl _)
    (fun g hg => prefixG_transfer hfork hsize hsize' hsel hv hnp hnb hdep hc0 hcB hc10 hg)
    start within hrun hok

/-- Every successful deprecated `transfer(to, value)` run, for any gas and any runner: not
paused, the caller not blacklisted, a nonzero code size at the upgraded address, the gas of the
path, a depth below the limit, and the forward of `transferByLegacy(caller, to, value)` that the
runner ended with no error; then STOP with no output, gas, state and substate exact. -/
theorem dep_transfer_complete (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xa9059cbb)
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0) {c : ByteArray}
    (hcode : state.getCode (state.getAccount (upAddr state message)).codeHash = .ok c)
    (hdel : .pectra ≤ fork → delegatedAddress c = none)
    {c0 cB c10 cU : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hcB : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget
      (blackSlot message) = cB)
    (hc10 : coldIn (accessSlot (accessSlot substate message.currentTarget 0) message.currentTarget
      (blackSlot message)) message.currentTarget 10 = c10)
    (hcU : decide (upAddr state message ∉ substate.accessedAddresses) = cU)
    {gas : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) :
    byte20 (storageAt state message.currentTarget 0) = 0 ∧
    (storageAt state message.currentTarget (blackSlot message)).toNat % 256 = 0 ∧
    BitVec.ofNat 256 c.size ≠ 0 ∧
    preCostT c0 cB c10 cU + 100 ≤ gas ∧
    message.depth + 1 ≤ STACK_DEPTH_LIMIT ∧
    ∃ caller msg lt child, runChild caller msg lt = .ok child ∧ child.1.error = none ∧
      Sends message (upAddr state message) c (dataT message) msg ∧
      msg.gas = (callGasT fork gas c0 cB c10 cU).subCall ∧
      caller.state = ((callStateT state message).recordAccountRead
        (upAddr state message)).recordAccountRead message.currentTarget ∧
      caller.substate = { callSubT substate state message with
        accessedAddresses :=
          (callSubT substate state message).accessedAddresses.insert (upAddr state message) } ∧
      51 ≤ gas - preCostT c0 cB c10 cU - (callGasT fork gas c0 cB c10 cU).cost + child.1.gas ∧
      s.running = false ∧ s.output = .empty ∧
      s.gas = gas - preCostT c0 cB c10 cU - (callGasT fork gas c0 cB c10 cU).cost +
        child.1.gas - 51 ∧
      s.state = (incorporateChild fork caller child.1).state ∧
      s.substate = (incorporateChild fork caller child.1).substate := by
  obtain ⟨h4, hv, -⟩ := runFrame_ok_dispatch hfork hsize' start within hrun hok
  by_cases hp : byte20 (storageAt state message.currentTarget 0) ≠ 0
  · exact (no_ok (fun g hg => Transfer.spec_paused hfork h4 hsize' hsel hv hp hc0 hg)
      (fun _ e h => halted_true_error e h) start within hrun hok).elim
  have hp : byte20 (storageAt state message.currentTarget 0) = 0 := by omega
  by_cases hb : (storageAt state message.currentTarget (blackSlot message)).toNat % 256 ≠ 0
  · exact (no_ok (fun g hg => Transfer.spec_blacklisted hfork h4 hsize' hsel hv hp hb hc0 hcB hg)
      (fun _ e h => halted_true_error e h) start within hrun hok).elim
  have hb : (storageAt state message.currentTarget (blackSlot message)).toNat % 256 = 0 := by
    omega
  obtain ⟨hg0, z, w, hz, hrunz⟩ :=
    dep_transfer_split hfork h4 hsize' hsel hv hp hb hdep hc0 hcB hc10 start within hrun hok
  obtain ⟨hw, hgc, hdepth, hCE⟩ := fromExt (U := upWord (storageAt state message.currentTarget 10))
    (rest := [0xc4, 0x6e18980a, upWord (storageAt state message.currentTarget 10),
      wordArg message.data 1, addrArg message.data 0, 0x078a,
      BitVec.ofNat 256 (selector message.data)])
    (st := shortState state message) (ss := shortSubstate substate message)
    hfork hglam (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))) (by simp) hcode hdel hz w hrunz hok
  have hext : extendMemory (memT message).size
      [((0x60 : U256), (0x64 : U256)), ((0x60 : U256), (0 : U256))] = ⟨0, 0⟩ := by
    rw [memT, size_W4 (size_MEMK _ _)]; decide
  have hcU' : decide (toAddressMasked (upWord (storageAt state message.currentTarget 10)) ∉
      (shortSubstate substate message).accessedAddresses) =
      decide (upAddr state message ∉ substate.accessedAddresses) := rfl
  rw [hcU', hcU] at hgc hCE
  rw [hext] at hgc
  simp only [accCost] at hgc hg0
  have e1 : gas - (1329 + slotCost c0 + slotCost cB + slotCost c10) - (accCost cU + 25) =
      gas - (1354 + slotCost c0 + slotCost cB + slotCost c10 + accCost cU) := by
    simp only [accCost]; omega
  have e2 : gas - (1329 + slotCost c0 + slotCost cB + slotCost c10) - (accCost cU + 28) =
      gas - preCostT c0 cB c10 cU := by
    simp only [preCostT, accCost]; omega
  rw [e1, e2] at hCE
  obtain ⟨caller, msg, lt, child, hch, hcs, hcss, hmg, hmc, hmt, hmtg, hmca, hmcode, hmd, hmv,
    hmdep, hmst, after, wa, hat, hruna⟩ := hCE
  rw [hext] at hmg hmd hat
  simp only [Bool.false_eq_true, ↓reduceIte] at hmg hat
  refine ⟨hp, hb, hw, by simp only [preCostT, accCost]; omega, hdepth, ?_⟩
  have hfwd : Sends message (upAddr state message) c (dataT message) msg := by
    refine ⟨hmc, hmt, hmtg, hmca, hmcode, ?_, hmv, hmdep, hmst⟩
    rw [hmd]; exact data_memT message
  by_cases he : child.1.error = none
  · simp only [he, Option.isNone_none, ↓reduceIte] at hat
    obtain ⟨h51, hr, ho, hgs, hst, hss⟩ := ok_exact (Nat.le_refl 51)
      (fun g _ => okTailT (fork := fork) (message := message)
        (state := (incorporateChild fork caller child.1).state)
        (substate := (incorporateChild fork caller child.1).substate)
        (gas := g) (by omega)) hat wa hruna hok
    refine ⟨caller, msg, lt, child, hch, he, hfwd, hmg, hcs, hcss, ?_, hr, ho, ?_, hst, hss⟩
    · simp only [Nat.add_zero] at h51
      omega
    · rw [hgs]
      simp only [Nat.add_zero]
  · have hz : child.1.error.isNone = false := by
      cases h : child.1.error
      · exact absurd h he
      · rfl
    simp only [hz, Bool.false_eq_true, ↓reduceIte] at hat
    exact (no_ok (fun g hg => failTail hfork (Or.inr (Or.inr (Or.inl rfl))) (by simp) hg)
      (fun g e h => by rw [h.2.1]; simp) hat wa hruna hok).elim

/-! ## approve -/

/-- `okTailA` over `StepG`: after a call that succeeded (flag 1), from 3231, back to 674 and
STOP. -/
theorem okTailAG {sel U v s x : U256} {M : ByteArray} {gas : Nat} (hg : 53 ≤ gas) :
    SpecG fork (At CODE message 3231 [1, 0xc4, sel, U, 0x40, v, s, 0x02a2, x] M gas state
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
  step repc (pc' := 674) (by decide)
  step jumpdestR
  refine (Gas.stopG (by code_fact) (by code_fact)).consequence (fun _ h => h) ?_
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  exact ⟨hr, he, ho, by rw [hgas]; gas_ok, hs, hss⟩

/-- From pc 0 to 3213 (EXTCODESIZE of the upgraded address), deprecated `approve`, over
`StepG` (`preExtA`). -/
theorem prefixG_approve (hfork : .berlin ≤ fork) (hlong : 68 ≤ message.data.size)
    (hsz : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x095ea7b3)
    (hv : message.value = 0) (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0)
    {c10 : Bool} (hc10 : coldIn substate message.currentTarget 10 = c10) {gas : Nat}
    (hg : 696 + slotCost c10 ≤ gas) :
    HoareG fork (At CODE message 0 [] .empty gas state substate)
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
  refine Triple.seq h1 ?_
  step Approve.entry hv (by gas_ok)
  step Approve.payload (Or.inl ⟨rfl, rfl⟩) hlong hsz (by simp) (by gas_ok)
  step depSetW hfork (Or.inr (Or.inl ⟨rfl, rfl⟩)) (by simp) hdep hc10 (by gas_ok)
  step upLoad hfork (Or.inr (Or.inl ⟨rfl, rfl⟩)) (by simp) (by gas_ok)
  step pushR 4 (0xaee92d33 : U256)
  step Gas.callerG (by code_fact) (by code_fact) (by gas_ok) (by stk_ok)
  step dupR 5
  step dupR 5
  step encode3 (Or.inr ⟨rfl, rfl⟩) size_MEM0 mload_MEM0
    (rest := [0x40, wordArg message.data 1, addrArg message.data 0, 0x02a2,
      BitVec.ofNat 256 (selector message.data)]) (by simp) (by gas_ok)
  exact Gas.reshapeG rfl rfl (by gas_ok)

/-- Every successful deprecated `approve(spender, value)` run, for any gas and any runner: at
least 68 bytes of call data, a nonzero code size at the upgraded address, the gas of the path, a
depth below the limit, and the forward of `approveByLegacy(caller, spender, value)` that the
runner ended with no error; then STOP with no output, gas, state and substate exact. -/
theorem dep_approve_complete (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x095ea7b3)
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0) {c : ByteArray}
    (hcode : state.getCode (state.getAccount (upAddr state message)).codeHash = .ok c)
    (hdel : .pectra ≤ fork → delegatedAddress c = none)
    {c10 cU : Bool} (hc10 : coldIn substate message.currentTarget 10 = c10)
    (hcU : decide (upAddr state message ∉ substate.accessedAddresses) = cU)
    {gas : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) :
    68 ≤ message.data.size ∧
    BitVec.ofNat 256 c.size ≠ 0 ∧
    preCostA c10 cU + 100 ≤ gas ∧
    message.depth + 1 ≤ STACK_DEPTH_LIMIT ∧
    ∃ caller msg lt child, runChild caller msg lt = .ok child ∧ child.1.error = none ∧
      Sends message (upAddr state message) c (dataA message) msg ∧
      msg.gas = (callGasA fork gas c10 cU).subCall ∧
      caller.state = ((callState state message).recordAccountRead
        (upAddr state message)).recordAccountRead message.currentTarget ∧
      caller.substate = { callSub substate state message with
        accessedAddresses :=
          (callSub substate state message).accessedAddresses.insert (upAddr state message) } ∧
      53 ≤ gas - preCostA c10 cU - (callGasA fork gas c10 cU).cost + child.1.gas ∧
      s.running = false ∧ s.output = .empty ∧
      s.gas = gas - preCostA c10 cU - (callGasA fork gas c10 cU).cost + child.1.gas - 53 ∧
      s.state = (incorporateChild fork caller child.1).state ∧
      s.substate = (incorporateChild fork caller child.1).substate := by
  obtain ⟨h4, hv, -⟩ := runFrame_ok_dispatch hfork hsize' start within hrun hok
  by_cases hl : message.data.size < 68
  · exact (no_ok (fun g hg => Approve.spec_payload hfork h4 hl hsel hv hg)
      (fun _ e h => halted_true_error e h) start within hrun hok).elim
  have hl : 68 ≤ message.data.size := by omega
  obtain ⟨hg0, z, w, hz, hrunz⟩ := ok_split (Nat.le_refl _)
    (fun g hg => prefixG_approve hfork hl hsize' hsel hv hdep hc10 hg) start within hrun hok
  obtain ⟨hw, hgc, hdepth, hCE⟩ := fromExt (U := upWord (storageAt state message.currentTarget 10))
    (rest := [0xc4, 0xaee92d33, upWord (storageAt state message.currentTarget 10), 0x40,
      wordArg message.data 1, addrArg message.data 0, 0x02a2,
      BitVec.ofNat 256 (selector message.data)])
    (st := readSlot state message.currentTarget 10)
    (ss := accessSlot substate message.currentTarget 10)
    hfork hglam (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))) (by simp) hcode hdel hz w hrunz hok
  have hext : extendMemory (memA message).size
      [((0x60 : U256), (0x64 : U256)), ((0x60 : U256), (0 : U256))] = ⟨0, 0⟩ := by
    rw [memA, size_W4 size_MEM0]; decide
  have hcU' : decide (toAddressMasked (upWord (storageAt state message.currentTarget 10)) ∉
      (accessSlot substate message.currentTarget 10).accessedAddresses) =
      decide (upAddr state message ∉ substate.accessedAddresses) := rfl
  rw [hcU', hcU] at hgc hCE
  rw [hext] at hgc
  simp only [accCost] at hgc hg0
  have e1 : gas - (696 + slotCost c10) - (accCost cU + 25) =
      gas - (721 + slotCost c10 + accCost cU) := by
    simp only [accCost]; omega
  have e2 : gas - (696 + slotCost c10) - (accCost cU + 28) = gas - preCostA c10 cU := by
    simp only [preCostA, accCost]; omega
  rw [e1, e2] at hCE
  obtain ⟨caller, msg, lt, child, hch, hcs, hcss, hmg, hmc, hmt, hmtg, hmca, hmcode, hmd, hmv,
    hmdep, hmst, after, wa, hat, hruna⟩ := hCE
  rw [hext] at hmg hmd hat
  simp only [Bool.false_eq_true, ↓reduceIte] at hmg hat
  refine ⟨hl, hw, by simp only [preCostA, accCost]; omega, hdepth, ?_⟩
  have hfwd : Sends message (upAddr state message) c (dataA message) msg := by
    refine ⟨hmc, hmt, hmtg, hmca, hmcode, ?_, hmv, hmdep, hmst⟩
    rw [hmd]; exact data_memA message
  by_cases he : child.1.error = none
  · simp only [he, Option.isNone_none, ↓reduceIte] at hat
    obtain ⟨h53, hr, ho, hgs, hst, hss⟩ := ok_exact (Nat.le_refl 53)
      (fun g _ => okTailAG (fork := fork) (message := message)
        (state := (incorporateChild fork caller child.1).state)
        (substate := (incorporateChild fork caller child.1).substate)
        (gas := g) (by omega)) hat wa hruna hok
    refine ⟨caller, msg, lt, child, hch, he, hfwd, hmg, hcs, hcss, ?_, hr, ho, ?_, hst, hss⟩
    · simp only [Nat.add_zero] at h53
      omega
    · rw [hgs]
      simp only [Nat.add_zero]
  · have hz : child.1.error.isNone = false := by
      cases h : child.1.error
      · exact absurd h he
      · rfl
    simp only [hz, Bool.false_eq_true, ↓reduceIte] at hat
    exact (no_ok (fun g hg => failTail hfork (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) (by simp) hg)
      (fun g e h => by rw [h.2.1]; simp) hat wa hruna hok).elim

/-! ## transferFrom -/

/-- From pc 0 to 4200 (EXTCODESIZE of the upgraded address), deprecated `transferFrom`, over
`StepG` (`preExtF`). -/
theorem prefixG_transferFrom (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
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
    HoareG fork (At CODE message 0 [] .empty gas state substate)
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
  refine Triple.seq h1 ?_
  step TransferFrom.entry hv (by gas_ok)
  step TransferFrom.notPaused hfork (by simp) hnp hc0 (by gas_ok)
  step notBlack hfork (by simp) hcB (by rw [storageAt_readSlot]; exact hnb) (by gas_ok) size_MEM0
  step depSetW hfork (Or.inr (Or.inr ⟨rfl, rfl⟩)) (by simp)
    (by rw [storageAt_readSlot, storageAt_readSlot]; exact hdep) hc10 (by gas_ok)
  step upLoad (state := readSlot (readSlot state message.currentTarget 0) message.currentTarget
    (blackFrom (fromArg message))) hfork (Or.inr (Or.inr ⟨rfl, rfl⟩)) (by simp) (by gas_ok)
  rw [storageAt_readSlot, storageAt_readSlot]
  step pushR 4 (0x8b477adb : U256)
  step Gas.callerG (by code_fact) (by code_fact) (by gas_ok) (by stk_ok)
  step dupR 5
  step dupR 5
  step dupR 5
  step encode4 (size_memF message) (ptr_memF message)
    (rest := [valArg message, toArg message, fromArg message, 0x0392,
      BitVec.ofNat 256 (selector message.data)]) (by simp) (by gas_ok)
  exact Gas.reshapeG rfl rfl (by gas_ok)

/-- Every successful deprecated `transferFrom(from, to, value)` run, for any gas and any runner:
not paused, `_from` not blacklisted, a nonzero code size at the upgraded address, the gas of the
path, a depth below the limit, and the forward of `transferFromByLegacy(caller, from, to, value)`
that the runner ended with no error; then STOP with no output, gas, state and substate exact. -/
theorem dep_transferFrom_complete (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x23b872dd)
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0) {c : ByteArray}
    (hcode : state.getCode (state.getAccount (upAddr state message)).codeHash = .ok c)
    (hdel : .pectra ≤ fork → delegatedAddress c = none)
    {c0 cB c10 cU : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hcB : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget
      (blackFrom (fromArg message)) = cB)
    (hc10 : coldIn (accessSlot (accessSlot substate message.currentTarget 0) message.currentTarget
      (blackFrom (fromArg message))) message.currentTarget 10 = c10)
    (hcU : decide (upAddr state message ∉ substate.accessedAddresses) = cU)
    {gas : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) :
    byte20 (storageAt state message.currentTarget 0) = 0 ∧
    (storageAt state message.currentTarget (blackFrom (fromArg message))).toNat % 256 = 0 ∧
    BitVec.ofNat 256 c.size ≠ 0 ∧
    DeprecatedTransferFrom.preCostF c0 cB c10 cU + 100 ≤ gas ∧
    message.depth + 1 ≤ STACK_DEPTH_LIMIT ∧
    ∃ caller msg lt child, runChild caller msg lt = .ok child ∧ child.1.error = none ∧
      Sends message (upAddr state message) c (dataF message) msg ∧
      msg.gas = (callGasF fork gas c0 cB c10 cU).subCall ∧
      caller.state = ((callStateF state message).recordAccountRead
        (upAddr state message)).recordAccountRead message.currentTarget ∧
      caller.substate = { callSubF substate state message with
        accessedAddresses :=
          (callSubF substate state message).accessedAddresses.insert (upAddr state message) } ∧
      53 ≤ gas - DeprecatedTransferFrom.preCostF c0 cB c10 cU - (callGasF fork gas c0 cB c10 cU).cost + child.1.gas ∧
      s.running = false ∧ s.output = .empty ∧
      s.gas = gas - DeprecatedTransferFrom.preCostF c0 cB c10 cU - (callGasF fork gas c0 cB c10 cU).cost +
        child.1.gas - 53 ∧
      s.state = (incorporateChild fork caller child.1).state ∧
      s.substate = (incorporateChild fork caller child.1).substate := by
  obtain ⟨h4, hv, -⟩ := runFrame_ok_dispatch hfork hsize' start within hrun hok
  by_cases hp : byte20 (storageAt state message.currentTarget 0) ≠ 0
  · exact (no_ok (fun g hg => TransferFrom.spec_paused hfork h4 hsize' hsel hv hp hc0 hg)
      (fun _ e h => halted_true_error e h) start within hrun hok).elim
  have hp : byte20 (storageAt state message.currentTarget 0) = 0 := by omega
  by_cases hb : (storageAt state message.currentTarget (blackFrom (fromArg message))).toNat % 256 ≠ 0
  · exact (no_ok (fun g hg => TransferFrom.spec_blacklisted hfork h4 hsize' hsel hv hp hb hc0 hcB hg)
      (fun _ e h => halted_true_error e h) start within hrun hok).elim
  have hb : (storageAt state message.currentTarget (blackFrom (fromArg message))).toNat % 256 = 0 :=
    by omega
  obtain ⟨hg0, z, w, hz, hrunz⟩ := ok_split (Nat.le_refl _)
    (fun g hg => prefixG_transferFrom hfork h4 hsize' hsel hv hp hb hdep hc0 hcB hc10 hg)
    start within hrun hok
  obtain ⟨hw, hgc, hdepth, hCE⟩ := fromExt (U := upWord (storageAt state message.currentTarget 10))
    (rest := [0xe4, 0x8b477adb, upWord (storageAt state message.currentTarget 10), valArg message,
      toArg message, fromArg message, 0x0392, BitVec.ofNat 256 (selector message.data)])
    (st := checkState state message) (ss := checkSub substate message)
    hfork hglam (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))) (by simp) hcode hdel hz w hrunz hok
  have hext : extendMemory (memFD message).size
      [((0x60 : U256), (0x84 : U256)), ((0x60 : U256), (0 : U256))] = ⟨0, 0⟩ := by
    rw [memFD, size_W5 (size_memF message)]; decide
  have hcU' : decide (toAddressMasked (upWord (storageAt state message.currentTarget 10)) ∉
      (checkSub substate message).accessedAddresses) =
      decide (upAddr state message ∉ substate.accessedAddresses) := rfl
  rw [hcU', hcU] at hgc hCE
  rw [hext] at hgc
  simp only [accCost] at hgc hg0
  have e1 : gas - (1065 + slotCost c0 + slotCost cB + slotCost c10) - (accCost cU + 25) =
      gas - (1090 + slotCost c0 + slotCost cB + slotCost c10 + accCost cU) := by
    simp only [accCost]; omega
  have e2 : gas - (1065 + slotCost c0 + slotCost cB + slotCost c10) - (accCost cU + 28) =
      gas - DeprecatedTransferFrom.preCostF c0 cB c10 cU := by
    simp only [DeprecatedTransferFrom.preCostF, accCost]; omega
  rw [e1, e2] at hCE
  obtain ⟨caller, msg, lt, child, hch, hcs, hcss, hmg, hmc, hmt, hmtg, hmca, hmcode, hmd, hmv,
    hmdep, hmst, after, wa, hat, hruna⟩ := hCE
  rw [hext] at hmg hmd hat
  simp only [Bool.false_eq_true, ↓reduceIte] at hmg hat
  refine ⟨hp, hb, hw, by simp only [DeprecatedTransferFrom.preCostF, accCost]; omega, hdepth, ?_⟩
  have hfwd : Sends message (upAddr state message) c (dataF message) msg := by
    refine ⟨hmc, hmt, hmtg, hmca, hmcode, ?_, hmv, hmdep, hmst⟩
    rw [hmd]; exact data_memFD message
  by_cases he : child.1.error = none
  · simp only [he, Option.isNone_none, ↓reduceIte] at hat
    obtain ⟨h53, hr, ho, hgs, hst, hss⟩ := ok_exact (Nat.le_refl 53)
      (fun g _ => okTailF (fork := fork) (message := message)
        (state := (incorporateChild fork caller child.1).state)
        (substate := (incorporateChild fork caller child.1).substate)
        (gas := g) (by omega)) hat wa hruna hok
    refine ⟨caller, msg, lt, child, hch, he, hfwd, hmg, hcs, hcss, ?_, hr, ho, ?_, hst, hss⟩
    · simp only [Nat.add_zero] at h53
      omega
    · rw [hgs]
      simp only [Nat.add_zero]
  · have hz : child.1.error.isNone = false := by
      cases h : child.1.error
      · exact absurd h he
      · rfl
    simp only [hz, Bool.false_eq_true, ↓reduceIte] at hat
    exact (no_ok (fun g hg => failTail hfork (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) (by simp) hg)
      (fun g e h => by rw [h.2.1]; simp) hat wa hruna hok).elim

end UsdtVerify.Complete
