import UsdtVerify.Evm.RunCR
import UsdtVerify.Usdt.Complete.Deprecated.Meter

/-!
# The deprecated paths over EthLib's EIP-8037 meter at any reservoir, with the gas (round 42)

The completeness theorems of the deprecated paths for a run of the loop of the interpreter over
`StateGasMeter` from a frame with ANY reservoir, for any gas bound and any message runner over
`StateGasMeter`, through `runC_of_sgmR`. Each conclusion is the one of `dep_X_completeS` with
two changes:

- the message the runner ran carries the reservoir of the first frame (`msg.reservoir =
  m.gas.reservoir`), and the caller frame has reservoir 0;
- the gas at the end: for totalSupply, balanceOf, allowance, transfer, approve and transferFrom,
  the execution gas left plus the reservoir at the end, plus the gas of the tail after the CALL,
  equals the gas before the CALL less the price of the CALL, plus the execution gas left and the
  reservoir that the child gave back. For destroyBlackFunds the same sum is a lower bound.

The split of that sum between execution gas and reservoir is not stated here. For
destroyBlackFunds, Usdt/Complete/Deprecated/DestroyS.lean (round 44, `dep_destroy_exactR`) states
the meter after the CALL and the exact end, refills included; for the six other paths,
Usdt/Complete/Deprecated/PathsS.lean (round 45, `dep_X_exactR`) does the same.
-/

namespace UsdtVerify.Complete

open EthLib.Base (Fork U256 toAddressMasked)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open UsdtVerify.Gas
open UsdtVerify.Meter
open GasCosts
open Deprecated DeprecatedBalance DeprecatedAllowance DeprecatedTransfer DeprecatedTransferFrom
  DeprecatedDestroy Owner Admin Destroy BlackList Transfer TransferOk TransferFrom DestroySpec

set_option linter.unusedSimpArgs false

variable {fork : Fork}
variable {bound : Nat} {runChild : MessageRunner fork StateGasMeter bound}
  {message : Message fork} {state : State.TransactionState} {substate : Substate}

/-- **Deprecated totalSupply() over the EIP-8037 meter, any reservoir, with the gas.** From
Berlin, from a frame `m` of `StateGasMeter` with any reservoir whose `toNat` is the fresh frame of
`CODE` at pc 0 with selector 0x18160ddd, deprecated, any gas: if the loop of the interpreter, for
any gas bound and message runner over `StateGasMeter`, ends with no error, then the conclusion of
`dep_totalSupply_completeS` holds with the message carrying the reservoir of `m`, and the
execution gas left plus the reservoir at the end, plus 121, is the gas before the CALL less its
price plus the execution gas left and the reservoir of the child. -/
theorem dep_totalSupply_completeR (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x18160ddd)
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0)
    {gas : Nat} {m s : Evm fork StateGasMeter}
    (start : At CODE message 0 [] .empty gas state substate (toNat m))
    {within : GasMeter.gasHeld m.gas ≤ bound}
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild m within = .ok s)
    (hok : s.error = none) :
    ∃ c r, state.getCode (state.getAccount (upAddr state message)).codeHash = .ok c ∧
    Routes fork state c r ∧
    BitVec.ofNat 256 c.size ≠ 0 ∧
    preCost fork (coldIn substate message.currentTarget 10)
      (decide (upAddr state message ∉ substate.accessedAddresses)) + 100 +
      routeCost fork (callSub substate state message).accessedAddresses r ≤ gas ∧
    message.depth + 1 ≤ STACK_DEPTH_LIMIT ∧
    ∃ caller msg lt child, runChild caller msg lt = .ok child ∧ child.1.error = none ∧
      caller.gas.reservoir = 0 ∧ msg.reservoir = m.gas.reservoir ∧
      SendsVia message (upAddr state message) c r SEL_TS msg ∧
      msg.gas = (depCallGas fork (askedOf fork gas (coldIn substate message.currentTarget 10)
          (decide (upAddr state message ∉ substate.accessedAddresses)))
        (gas - preCost fork (coldIn substate message.currentTarget 10)
          (decide (upAddr state message ∉ substate.accessedAddresses)))
        (routeCost fork (callSub substate state message).accessedAddresses r)).subCall ∧
      caller.state = (routeState ((callState state message).recordAccountRead
        (upAddr state message)) r).recordAccountRead message.currentTarget ∧
      caller.substate = routeSub { callSub substate state message with
        accessedAddresses :=
          (callSub substate state message).accessedAddresses.insert (upAddr state message) } r ∧
      s.running = false ∧ s.output = wordBytes (resWord (outMem child.1.output)) ∧
      s.state = (incorporateChild fork caller child.1).state ∧
      s.substate = (incorporateChild fork caller child.1).substate ∧
      s.gas.gasLeft + s.gas.reservoir + 121 =
        gas - preCost fork (coldIn substate message.currentTarget 10)
          (decide (upAddr state message ∉ substate.accessedAddresses)) -
        (depCallGas fork (askedOf fork gas (coldIn substate message.currentTarget 10)
          (decide (upAddr state message ∉ substate.accessedAddresses)))
        (gas - preCost fork (coldIn substate message.currentTarget 10)
          (decide (upAddr state message ∉ substate.accessedAddresses)))
        (routeCost fork (callSub substate state message).accessedAddresses r)).cost +
        child.1.gas.gasLeft + child.1.gas.reservoir := by
  obtain ⟨G, hC⟩ := runC_of_sgmR (g0 := m.gas) hfork hrun hok (.inl rfl) (Nat.le_refl _)
  obtain ⟨c, r, h1, h2, h3, h4, h5, caller, msg, child,
    ⟨cS, msgS, lt, chS, hch, hmsg, rfl, hchN, hcg⟩, he, hfwd, hmg, hcs, hcss, h121, hr, ho, hgs,
    hst, hss, after, hT, hnr⟩ :=
    dep_totalSupply_completeC hfork hsize' hsel hdep start hC (endsOk_of_sgm hfork hrun hok) hok
  have hG := hT.2 hnr
  have cs : child.state = chS.1.state := by rw [hchN]; rfl
  have css : child.substate = chS.1.substate := by rw [hchN]; rfl
  have ce : child.error = chS.1.error := by rw [hchN]; rfl
  have co : child.output = chS.1.output := by rw [hchN]; rfl
  have cg : child.gas = chS.1.gas.gasLeft + chS.1.gas.reservoir +
      STORAGE_SET_STATE_GAS * Evm.measure m := by rw [hchN]
  obtain ⟨i1, i2⟩ := incorporateChild_toNat cS chS.1 child cs css ce (by rw [hchN]; rfl)
  simp only [i1, i2, cs, css, ce, co] at he ho hst hss
  subst hmsg
  refine ⟨c, r, h1, h2, h3, h4, h5, cS, _, lt, chS, hch, he, by rw [hcg], rfl, hfwd, hmg, hcs, hcss,
    hr, ho, hst, hss, ?_⟩
  simp only at hgs hG h121 ⊢
  rw [cg] at hgs h121
  generalize STORAGE_SET_STATE_GAS * Evm.measure m = E at hgs hG h121
  omega

/-- **Deprecated balanceOf over the EIP-8037 meter, any reservoir, with the gas.**
`dep_balanceOf_completeS` from a frame `m` with any reservoir: the message carries the reservoir of
`m`, and the execution gas left plus the reservoir at the end, plus the gas of the tail (126), is
the gas before the CALL less its price plus the execution gas left and the reservoir of the
child. -/
theorem dep_balanceOf_completeR (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x70a08231)
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0)
    {gas : Nat} {m s : Evm fork StateGasMeter}
    (start : At CODE message 0 [] .empty gas state substate (toNat m))
    {within : GasMeter.gasHeld m.gas ≤ bound}
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild m within = .ok s)
    (hok : s.error = none) :
    ∃ c r, state.getCode (state.getAccount (upAddr state message)).codeHash = .ok c ∧
    Routes fork state c r ∧
    BitVec.ofNat 256 c.size ≠ 0 ∧
    preCostB fork (coldIn substate message.currentTarget 10)
      (decide (upAddr state message ∉ substate.accessedAddresses)) + 100 +
      routeCost fork (callSub substate state message).accessedAddresses r ≤ gas ∧
    message.depth + 1 ≤ STACK_DEPTH_LIMIT ∧
    ∃ caller msg lt child, runChild caller msg lt = .ok child ∧ child.1.error = none ∧
      caller.gas.reservoir = 0 ∧ msg.reservoir = m.gas.reservoir ∧
      SendsVia message (upAddr state message) c r (dataB message) msg ∧
      msg.gas = (depCallGas fork (askedOfB fork gas (coldIn substate message.currentTarget 10)
          (decide (upAddr state message ∉ substate.accessedAddresses)))
        (gas - preCostB fork (coldIn substate message.currentTarget 10)
          (decide (upAddr state message ∉ substate.accessedAddresses)))
        (routeCost fork (callSub substate state message).accessedAddresses r)).subCall ∧
      caller.state = (routeState ((callState state message).recordAccountRead
        (upAddr state message)) r).recordAccountRead message.currentTarget ∧
      caller.substate = routeSub { callSub substate state message with
        accessedAddresses :=
          (callSub substate state message).accessedAddresses.insert (upAddr state message) } r ∧
      s.running = false ∧
      s.output = wordBytes (resWord (outMemOf (M2B (addrArg message.data 0)) child.1.output)) ∧
      s.state = (incorporateChild fork caller child.1).state ∧
      s.substate = (incorporateChild fork caller child.1).substate ∧
      s.gas.gasLeft + s.gas.reservoir + 126 =
        gas - preCostB fork (coldIn substate message.currentTarget 10)
          (decide (upAddr state message ∉ substate.accessedAddresses)) -
        (depCallGas fork (askedOfB fork gas (coldIn substate message.currentTarget 10)
          (decide (upAddr state message ∉ substate.accessedAddresses)))
        (gas - preCostB fork (coldIn substate message.currentTarget 10)
          (decide (upAddr state message ∉ substate.accessedAddresses)))
        (routeCost fork (callSub substate state message).accessedAddresses r)).cost +
        child.1.gas.gasLeft + child.1.gas.reservoir := by
  obtain ⟨G, hC⟩ := runC_of_sgmR (g0 := m.gas) hfork hrun hok (.inl rfl) (Nat.le_refl _)
  obtain ⟨c, r, h1, h2, h3, h4, h5, caller, msg, child,
    ⟨cS, msgS, lt, chS, hch, hmsg, rfl, hchN, hcg⟩, he, hfwd, hmg, hcs, hcss, hN, hr, ho, hgs,
    hst, hss, after, hT, hnr⟩ :=
    dep_balanceOf_completeC hfork hsize' hsel hdep start hC (endsOk_of_sgm hfork hrun hok) hok
  have hG := hT.2 hnr
  have cs : child.state = chS.1.state := by rw [hchN]; rfl
  have css : child.substate = chS.1.substate := by rw [hchN]; rfl
  have ce : child.error = chS.1.error := by rw [hchN]; rfl
  have co : child.output = chS.1.output := by rw [hchN]; rfl
  have cg : child.gas = chS.1.gas.gasLeft + chS.1.gas.reservoir +
      STORAGE_SET_STATE_GAS * Evm.measure m := by rw [hchN]
  obtain ⟨i1, i2⟩ := incorporateChild_toNat cS chS.1 child cs css ce (by rw [hchN]; rfl)
  try simp only [i1, i2, cs, css, ce, co] at he
  try simp only [i1, i2, cs, css, ce, co] at ho
  try simp only [i1, i2, cs, css, ce, co] at hst
  try simp only [i1, i2, cs, css, ce, co] at hss
  subst hmsg
  refine ⟨c, r, h1, h2, h3, h4, h5, cS, _, lt, chS, hch, he, by rw [hcg], rfl, hfwd, hmg, hcs, hcss,
    hr, ho, hst, hss, ?_⟩
  simp only at hgs hG hN ⊢
  rw [cg] at hgs hN
  generalize STORAGE_SET_STATE_GAS * Evm.measure m = E at hgs hG hN
  omega

/-- **Deprecated allowance over the EIP-8037 meter, any reservoir, with the gas.**
`dep_allowance_completeS` from a frame `m` with any reservoir: the message carries the reservoir of
`m`, and the execution gas left plus the reservoir at the end, plus the gas of the tail (128), is
the gas before the CALL less its price plus the execution gas left and the reservoir of the
child. -/
theorem dep_allowance_completeR (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xdd62ed3e)
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0)
    {c10 cU : Bool} (hc10 : coldIn substate message.currentTarget 10 = c10)
    (hcU : decide (upAddr state message ∉ substate.accessedAddresses) = cU)
    {gas : Nat} {m s : Evm fork StateGasMeter}
    (start : At CODE message 0 [] .empty gas state substate (toNat m))
    {within : GasMeter.gasHeld m.gas ≤ bound}
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild m within = .ok s)
    (hok : s.error = none) :
    ∃ c r, state.getCode (state.getAccount (upAddr state message)).codeHash = .ok c ∧
    Routes fork state c r ∧
    BitVec.ofNat 256 c.size ≠ 0 ∧
    preCostAl fork c10 cU + 100 + routeCost fork (callSub substate state message).accessedAddresses r ≤ gas ∧
    message.depth + 1 ≤ STACK_DEPTH_LIMIT ∧
    ∃ caller msg lt child, runChild caller msg lt = .ok child ∧ child.1.error = none ∧
      caller.gas.reservoir = 0 ∧ msg.reservoir = m.gas.reservoir ∧
      SendsVia message (upAddr state message) c r (dataAl message) msg ∧
      msg.gas = (depCallGas fork (askedOfAl fork gas c10 cU) (gas - preCostAl fork c10 cU)
        (routeCost fork (callSub substate state message).accessedAddresses r)).subCall ∧
      caller.state = (routeState ((callState state message).recordAccountRead
        (upAddr state message)) r).recordAccountRead message.currentTarget ∧
      caller.substate = routeSub { callSub substate state message with
        accessedAddresses :=
          (callSub substate state message).accessedAddresses.insert (upAddr state message) } r ∧
      s.running = false ∧
      s.output = wordBytes (resWord (outMemOf (memAl message) child.1.output)) ∧
      s.state = (incorporateChild fork caller child.1).state ∧
      s.substate = (incorporateChild fork caller child.1).substate ∧
      s.gas.gasLeft + s.gas.reservoir + 128 =
        gas - preCostAl fork c10 cU - (depCallGas fork (askedOfAl fork gas c10 cU) (gas - preCostAl fork c10 cU)
        (routeCost fork (callSub substate state message).accessedAddresses r)).cost +
        child.1.gas.gasLeft + child.1.gas.reservoir := by
  obtain ⟨G, hC⟩ := runC_of_sgmR (g0 := m.gas) hfork hrun hok (.inl rfl) (Nat.le_refl _)
  obtain ⟨c, r, h1, h2, h3, h4, h5, caller, msg, child,
    ⟨cS, msgS, lt, chS, hch, hmsg, rfl, hchN, hcg⟩, he, hfwd, hmg, hcs, hcss, hN, hr, ho, hgs,
    hst, hss, after, hT, hnr⟩ :=
    dep_allowance_completeC hfork hsize' hsel hdep hc10 hcU start hC (endsOk_of_sgm hfork hrun hok) hok
  have hG := hT.2 hnr
  have cs : child.state = chS.1.state := by rw [hchN]; rfl
  have css : child.substate = chS.1.substate := by rw [hchN]; rfl
  have ce : child.error = chS.1.error := by rw [hchN]; rfl
  have co : child.output = chS.1.output := by rw [hchN]; rfl
  have cg : child.gas = chS.1.gas.gasLeft + chS.1.gas.reservoir +
      STORAGE_SET_STATE_GAS * Evm.measure m := by rw [hchN]
  obtain ⟨i1, i2⟩ := incorporateChild_toNat cS chS.1 child cs css ce (by rw [hchN]; rfl)
  try simp only [i1, i2, cs, css, ce, co] at he
  try simp only [i1, i2, cs, css, ce, co] at ho
  try simp only [i1, i2, cs, css, ce, co] at hst
  try simp only [i1, i2, cs, css, ce, co] at hss
  subst hmsg
  refine ⟨c, r, h1, h2, h3, h4, h5, cS, _, lt, chS, hch, he, by rw [hcg], rfl, hfwd, hmg, hcs, hcss,
    hr, ho, hst, hss, ?_⟩
  simp only at hgs hG hN ⊢
  rw [cg] at hgs hN
  generalize STORAGE_SET_STATE_GAS * Evm.measure m = E at hgs hG hN
  omega

/-- **Deprecated transfer over the EIP-8037 meter, any reservoir, with the gas.**
`dep_transfer_completeS` from a frame `m` with any reservoir: the message carries the reservoir of
`m`, and the execution gas left plus the reservoir at the end, plus the gas of the tail (51), is
the gas before the CALL less its price plus the execution gas left and the reservoir of the
child. -/
theorem dep_transfer_completeR (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xa9059cbb)
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0)
    {c0 cB c10 cU : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hcB : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget
      (blackSlot message) = cB)
    (hc10 : coldIn (accessSlot (accessSlot substate message.currentTarget 0) message.currentTarget
      (blackSlot message)) message.currentTarget 10 = c10)
    (hcU : decide (upAddr state message ∉ substate.accessedAddresses) = cU)
    {gas : Nat} {m s : Evm fork StateGasMeter}
    (start : At CODE message 0 [] .empty gas state substate (toNat m))
    {within : GasMeter.gasHeld m.gas ≤ bound}
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild m within = .ok s)
    (hok : s.error = none) :
    ∃ c r, state.getCode (state.getAccount (upAddr state message)).codeHash = .ok c ∧
    Routes fork state c r ∧
    byte20 (storageAt state message.currentTarget 0) = 0 ∧
    (storageAt state message.currentTarget (blackSlot message)).toNat % 256 = 0 ∧
    BitVec.ofNat 256 c.size ≠ 0 ∧
    preCostT fork c0 cB c10 cU + 100 + routeCost fork (callSubT substate state message).accessedAddresses r ≤ gas ∧
    message.depth + 1 ≤ STACK_DEPTH_LIMIT ∧
    ∃ caller msg lt child, runChild caller msg lt = .ok child ∧ child.1.error = none ∧
      caller.gas.reservoir = 0 ∧ msg.reservoir = m.gas.reservoir ∧
      SendsVia message (upAddr state message) c r (dataT message) msg ∧
      msg.gas = (depCallGas fork (askedOfT fork gas c0 cB c10 cU) (gas - preCostT fork c0 cB c10 cU)
        (routeCost fork (callSubT substate state message).accessedAddresses r)).subCall ∧
      caller.state = (routeState ((callStateT state message).recordAccountRead
        (upAddr state message)) r).recordAccountRead message.currentTarget ∧
      caller.substate = routeSub { callSubT substate state message with
        accessedAddresses :=
          (callSubT substate state message).accessedAddresses.insert (upAddr state message) } r ∧
      s.running = false ∧ s.output = .empty ∧
      s.state = (incorporateChild fork caller child.1).state ∧
      s.substate = (incorporateChild fork caller child.1).substate ∧
      s.gas.gasLeft + s.gas.reservoir + 51 =
        gas - preCostT fork c0 cB c10 cU - (depCallGas fork (askedOfT fork gas c0 cB c10 cU) (gas - preCostT fork c0 cB c10 cU)
        (routeCost fork (callSubT substate state message).accessedAddresses r)).cost +
        child.1.gas.gasLeft + child.1.gas.reservoir := by
  obtain ⟨G, hC⟩ := runC_of_sgmR (g0 := m.gas) hfork hrun hok (.inl rfl) (Nat.le_refl _)
  obtain ⟨c, r, h1, h2, h3, h4, h5, h6, h7, caller, msg, child,
    ⟨cS, msgS, lt, chS, hch, hmsg, rfl, hchN, hcg⟩, he, hfwd, hmg, hcs, hcss, hN, hr, ho, hgs,
    hst, hss, after, hT, hnr⟩ :=
    dep_transfer_completeC hfork hsize' hsel hdep hc0 hcB hc10 hcU start hC (endsOk_of_sgm hfork hrun hok) hok
  have hG := hT.2 hnr
  have cs : child.state = chS.1.state := by rw [hchN]; rfl
  have css : child.substate = chS.1.substate := by rw [hchN]; rfl
  have ce : child.error = chS.1.error := by rw [hchN]; rfl
  have co : child.output = chS.1.output := by rw [hchN]; rfl
  have cg : child.gas = chS.1.gas.gasLeft + chS.1.gas.reservoir +
      STORAGE_SET_STATE_GAS * Evm.measure m := by rw [hchN]
  obtain ⟨i1, i2⟩ := incorporateChild_toNat cS chS.1 child cs css ce (by rw [hchN]; rfl)
  try simp only [i1, i2, cs, css, ce, co] at he
  try simp only [i1, i2, cs, css, ce, co] at ho
  try simp only [i1, i2, cs, css, ce, co] at hst
  try simp only [i1, i2, cs, css, ce, co] at hss
  subst hmsg
  refine ⟨c, r, h1, h2, h3, h4, h5, h6, h7, cS, _, lt, chS, hch, he, by rw [hcg], rfl, hfwd, hmg, hcs, hcss,
    hr, ho, hst, hss, ?_⟩
  simp only at hgs hG hN ⊢
  rw [cg] at hgs hN
  generalize STORAGE_SET_STATE_GAS * Evm.measure m = E at hgs hG hN
  omega

/-- **Deprecated approve over the EIP-8037 meter, any reservoir, with the gas.**
`dep_approve_completeS` from a frame `m` with any reservoir: the message carries the reservoir of
`m`, and the execution gas left plus the reservoir at the end, plus the gas of the tail (53), is
the gas before the CALL less its price plus the execution gas left and the reservoir of the
child. -/
theorem dep_approve_completeR (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x095ea7b3)
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0)
    {c10 cU : Bool} (hc10 : coldIn substate message.currentTarget 10 = c10)
    (hcU : decide (upAddr state message ∉ substate.accessedAddresses) = cU)
    {gas : Nat} {m s : Evm fork StateGasMeter}
    (start : At CODE message 0 [] .empty gas state substate (toNat m))
    {within : GasMeter.gasHeld m.gas ≤ bound}
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild m within = .ok s)
    (hok : s.error = none) :
    ∃ c r, state.getCode (state.getAccount (upAddr state message)).codeHash = .ok c ∧
    Routes fork state c r ∧
    68 ≤ message.data.size ∧
    BitVec.ofNat 256 c.size ≠ 0 ∧
    preCostA fork c10 cU + 100 + routeCost fork (callSub substate state message).accessedAddresses r ≤ gas ∧
    message.depth + 1 ≤ STACK_DEPTH_LIMIT ∧
    ∃ caller msg lt child, runChild caller msg lt = .ok child ∧ child.1.error = none ∧
      caller.gas.reservoir = 0 ∧ msg.reservoir = m.gas.reservoir ∧
      SendsVia message (upAddr state message) c r (dataA message) msg ∧
      msg.gas = (depCallGas fork (askedOfA fork gas c10 cU) (gas - preCostA fork c10 cU)
        (routeCost fork (callSub substate state message).accessedAddresses r)).subCall ∧
      caller.state = (routeState ((callState state message).recordAccountRead
        (upAddr state message)) r).recordAccountRead message.currentTarget ∧
      caller.substate = routeSub { callSub substate state message with
        accessedAddresses :=
          (callSub substate state message).accessedAddresses.insert (upAddr state message) } r ∧
      s.running = false ∧ s.output = .empty ∧
      s.state = (incorporateChild fork caller child.1).state ∧
      s.substate = (incorporateChild fork caller child.1).substate ∧
      s.gas.gasLeft + s.gas.reservoir + 53 =
        gas - preCostA fork c10 cU - (depCallGas fork (askedOfA fork gas c10 cU) (gas - preCostA fork c10 cU)
        (routeCost fork (callSub substate state message).accessedAddresses r)).cost +
        child.1.gas.gasLeft + child.1.gas.reservoir := by
  obtain ⟨G, hC⟩ := runC_of_sgmR (g0 := m.gas) hfork hrun hok (.inl rfl) (Nat.le_refl _)
  obtain ⟨c, r, h1, h2, h3, h4, h5, h6, caller, msg, child,
    ⟨cS, msgS, lt, chS, hch, hmsg, rfl, hchN, hcg⟩, he, hfwd, hmg, hcs, hcss, hN, hr, ho, hgs,
    hst, hss, after, hT, hnr⟩ :=
    dep_approve_completeC hfork hsize' hsel hdep hc10 hcU start hC (endsOk_of_sgm hfork hrun hok) hok
  have hG := hT.2 hnr
  have cs : child.state = chS.1.state := by rw [hchN]; rfl
  have css : child.substate = chS.1.substate := by rw [hchN]; rfl
  have ce : child.error = chS.1.error := by rw [hchN]; rfl
  have co : child.output = chS.1.output := by rw [hchN]; rfl
  have cg : child.gas = chS.1.gas.gasLeft + chS.1.gas.reservoir +
      STORAGE_SET_STATE_GAS * Evm.measure m := by rw [hchN]
  obtain ⟨i1, i2⟩ := incorporateChild_toNat cS chS.1 child cs css ce (by rw [hchN]; rfl)
  try simp only [i1, i2, cs, css, ce, co] at he
  try simp only [i1, i2, cs, css, ce, co] at ho
  try simp only [i1, i2, cs, css, ce, co] at hst
  try simp only [i1, i2, cs, css, ce, co] at hss
  subst hmsg
  refine ⟨c, r, h1, h2, h3, h4, h5, h6, cS, _, lt, chS, hch, he, by rw [hcg], rfl, hfwd, hmg, hcs, hcss,
    hr, ho, hst, hss, ?_⟩
  simp only at hgs hG hN ⊢
  rw [cg] at hgs hN
  generalize STORAGE_SET_STATE_GAS * Evm.measure m = E at hgs hG hN
  omega

/-- **Deprecated transferFrom over the EIP-8037 meter, any reservoir, with the gas.**
`dep_transferFrom_completeS` from a frame `m` with any reservoir: the message carries the reservoir of
`m`, and the execution gas left plus the reservoir at the end, plus the gas of the tail (53), is
the gas before the CALL less its price plus the execution gas left and the reservoir of the
child. -/
theorem dep_transferFrom_completeR (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x23b872dd)
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0)
    {c0 cB c10 cU : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hcB : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget
      (blackFrom (fromArg message)) = cB)
    (hc10 : coldIn (accessSlot (accessSlot substate message.currentTarget 0) message.currentTarget
      (blackFrom (fromArg message))) message.currentTarget 10 = c10)
    (hcU : decide (upAddr state message ∉ substate.accessedAddresses) = cU)
    {gas : Nat} {m s : Evm fork StateGasMeter}
    (start : At CODE message 0 [] .empty gas state substate (toNat m))
    {within : GasMeter.gasHeld m.gas ≤ bound}
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild m within = .ok s)
    (hok : s.error = none) :
    ∃ c r, state.getCode (state.getAccount (upAddr state message)).codeHash = .ok c ∧
    Routes fork state c r ∧
    byte20 (storageAt state message.currentTarget 0) = 0 ∧
    (storageAt state message.currentTarget (blackFrom (fromArg message))).toNat % 256 = 0 ∧
    BitVec.ofNat 256 c.size ≠ 0 ∧
    DeprecatedTransferFrom.preCostF fork c0 cB c10 cU + 100 + routeCost fork (callSubF substate state message).accessedAddresses r ≤ gas ∧
    message.depth + 1 ≤ STACK_DEPTH_LIMIT ∧
    ∃ caller msg lt child, runChild caller msg lt = .ok child ∧ child.1.error = none ∧
      caller.gas.reservoir = 0 ∧ msg.reservoir = m.gas.reservoir ∧
      SendsVia message (upAddr state message) c r (dataF message) msg ∧
      msg.gas = (depCallGas fork (askedOfF fork gas c0 cB c10 cU) (gas - DeprecatedTransferFrom.preCostF fork c0 cB c10 cU)
        (routeCost fork (callSubF substate state message).accessedAddresses r)).subCall ∧
      caller.state = (routeState ((callStateF state message).recordAccountRead
        (upAddr state message)) r).recordAccountRead message.currentTarget ∧
      caller.substate = routeSub { callSubF substate state message with
        accessedAddresses :=
          (callSubF substate state message).accessedAddresses.insert (upAddr state message) } r ∧
      s.running = false ∧ s.output = .empty ∧
      s.state = (incorporateChild fork caller child.1).state ∧
      s.substate = (incorporateChild fork caller child.1).substate ∧
      s.gas.gasLeft + s.gas.reservoir + 53 =
        gas - DeprecatedTransferFrom.preCostF fork c0 cB c10 cU - (depCallGas fork (askedOfF fork gas c0 cB c10 cU) (gas - DeprecatedTransferFrom.preCostF fork c0 cB c10 cU)
        (routeCost fork (callSubF substate state message).accessedAddresses r)).cost +
        child.1.gas.gasLeft + child.1.gas.reservoir := by
  obtain ⟨G, hC⟩ := runC_of_sgmR (g0 := m.gas) hfork hrun hok (.inl rfl) (Nat.le_refl _)
  obtain ⟨c, r, h1, h2, h3, h4, h5, h6, h7, caller, msg, child,
    ⟨cS, msgS, lt, chS, hch, hmsg, rfl, hchN, hcg⟩, he, hfwd, hmg, hcs, hcss, hN, hr, ho, hgs,
    hst, hss, after, hT, hnr⟩ :=
    dep_transferFrom_completeC hfork hsize' hsel hdep hc0 hcB hc10 hcU start hC (endsOk_of_sgm hfork hrun hok) hok
  have hG := hT.2 hnr
  have cs : child.state = chS.1.state := by rw [hchN]; rfl
  have css : child.substate = chS.1.substate := by rw [hchN]; rfl
  have ce : child.error = chS.1.error := by rw [hchN]; rfl
  have co : child.output = chS.1.output := by rw [hchN]; rfl
  have cg : child.gas = chS.1.gas.gasLeft + chS.1.gas.reservoir +
      STORAGE_SET_STATE_GAS * Evm.measure m := by rw [hchN]
  obtain ⟨i1, i2⟩ := incorporateChild_toNat cS chS.1 child cs css ce (by rw [hchN]; rfl)
  try simp only [i1, i2, cs, css, ce, co] at he
  try simp only [i1, i2, cs, css, ce, co] at ho
  try simp only [i1, i2, cs, css, ce, co] at hst
  try simp only [i1, i2, cs, css, ce, co] at hss
  subst hmsg
  refine ⟨c, r, h1, h2, h3, h4, h5, h6, h7, cS, _, lt, chS, hch, he, by rw [hcg], rfl, hfwd, hmg, hcs, hcss,
    hr, ho, hst, hss, ?_⟩
  simp only at hgs hG hN ⊢
  rw [cg] at hgs hN
  generalize STORAGE_SET_STATE_GAS * Evm.measure m = E at hgs hG hN
  omega

/-- **Deprecated destroyBlackFunds(a) over the EIP-8037 meter, any reservoir, a bound on the
gas.** `dep_destroy_completeS` from a frame `m` with any reservoir: the message carries the
reservoir of `m`, and the execution gas left plus the reservoir at the end, plus the gas of the
tail (`tailCost`), is at least the gas before the CALL less its price plus the execution gas left
and the reservoir of the child. The two writes of the tail may refill, so no equality is stated. -/
theorem dep_destroy_completeR (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xf3bdc228)
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0)
    {c0 cL c10 cU : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hcL : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget
      (listSlot (addrArg message.data 0)) = cL)
    (hc10 : coldIn (preSub substate message) message.currentTarget 10 = c10)
    (hcU : decide (upAddr state message ∉ substate.accessedAddresses) = cU)
    {gas : Nat} {m s : Evm fork StateGasMeter}
    (start : At CODE message 0 [] .empty gas state substate (toNat m))
    {within : GasMeter.gasHeld m.gas ≤ bound}
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild m within = .ok s)
    (hok : s.error = none) :
    ∃ c r, state.getCode (state.getAccount (upAddr state message)).codeHash = .ok c ∧
    Routes fork state c r ∧
    callerWord message = ownerOf state message.currentTarget ∧
    (storageAt state message.currentTarget (listSlot (addrArg message.data 0))).toNat % 256 ≠ 0 ∧
    BitVec.ofNat 256 c.size ≠ 0 ∧
    preCostD fork c0 cL c10 cU + 100 + routeCost fork (callSubD substate state message).accessedAddresses r ≤ gas ∧
    message.depth + 1 ≤ STACK_DEPTH_LIMIT ∧
    ∃ caller msg lt child, runChild caller msg lt = .ok child ∧ child.1.error = none ∧
      caller.gas.reservoir = 0 ∧ msg.reservoir = m.gas.reservoir ∧
      message.isStatic = false ∧ hasAccount child.1.state message.currentTarget ∧
      SendsVia message (upAddr state message) c r (dataB message) msg ∧
      msg.gas = (depCallGas fork (askedOfD fork gas c0 cL c10 cU) (gas - preCostD fork c0 cL c10 cU)
        (routeCost fork (callSubD substate state message).accessedAddresses r)).subCall ∧
      caller.state = (routeState ((callStateD state message).recordAccountRead
        (upAddr state message)) r).recordAccountRead message.currentTarget ∧
      caller.substate = routeSub { callSubD substate state message with
        accessedAddresses :=
          (callSubD substate state message).accessedAddresses.insert (upAddr state message) } r ∧
      s.running = false ∧ s.output = .empty ∧
      s.state = tailState (incorporateChild fork caller child.1).state message.currentTarget
        (addrArg message.data 0) (resWord (outMemOf (memD message) child.1.output)) ∧
      s.substate = tailSub fork (incorporateChild fork caller child.1).substate
        (incorporateChild fork caller child.1).state message.currentTarget
        (addrArg message.data 0) (resWord (outMemOf (memD message) child.1.output)) ∧
      gas - preCostD fork c0 cL c10 cU - (depCallGas fork (askedOfD fork gas c0 cL c10 cU) (gas - preCostD fork c0 cL c10 cU)
        (routeCost fork (callSubD substate state message).accessedAddresses r)).cost +
        child.1.gas.gasLeft + child.1.gas.reservoir ≤
      s.gas.gasLeft + s.gas.reservoir +
        tailCost fork (incorporateChild fork caller child.1).state message.currentTarget
          (addrArg message.data 0) (resWord (outMemOf (memD message) child.1.output))
          (coldIn (incorporateChild fork caller child.1).substate message.currentTarget
            (balSlot message))
          (coldIn (accessSlot (incorporateChild fork caller child.1).substate
            message.currentTarget (balSlot message)) message.currentTarget 1) := by
  obtain ⟨G, hC⟩ := runC_of_sgmR (g0 := m.gas) hfork hrun hok (.inl rfl) (Nat.le_refl _)
  obtain ⟨c, r, h1, h2, h3, h4, h5, h6, h7, caller, msg, child,
    ⟨cS, msgS, lt, chS, hch, hmsg, rfl, hchN, hcg⟩, he, hstat, hacc, hfwd, hmg, hcs, hcss, hN, hr,
    ho, hgs, hst, hss, -, after, hT⟩ :=
    dep_destroy_completeC hfork hsize' hsel hdep hc0 hcL hc10 hcU start hC (endsOk_of_sgm hfork hrun hok) hok
  have hG := hT.1
  have cs : child.state = chS.1.state := by rw [hchN]; rfl
  have css : child.substate = chS.1.substate := by rw [hchN]; rfl
  have ce : child.error = chS.1.error := by rw [hchN]; rfl
  have co : child.output = chS.1.output := by rw [hchN]; rfl
  have cg : child.gas = chS.1.gas.gasLeft + chS.1.gas.reservoir +
      STORAGE_SET_STATE_GAS * Evm.measure m := by rw [hchN]
  obtain ⟨i1, i2⟩ := incorporateChild_toNat cS chS.1 child cs css ce (by rw [hchN]; rfl)
  try simp only [i1, i2, cs, css, ce, co] at he
  try simp only [i1, i2, cs, css, ce, co] at hacc
  try simp only [i1, i2, cs, css, ce, co] at ho
  try simp only [i1, i2, cs, css, ce, co] at hst
  try simp only [i1, i2, cs, css, ce, co] at hss
  try simp only [i1, i2, cs, css, ce, co] at hgs
  try simp only [i1, i2, cs, css, ce, co] at hN
  subst hmsg
  refine ⟨c, r, h1, h2, h3, h4, h5, h6, h7, cS, _, lt, chS, hch, he, by rw [hcg], rfl, hstat, hacc, hfwd, hmg, hcs, hcss,
    hr, ho, hst, hss, ?_⟩
  simp only at hgs hG hN ⊢
  rw [cg] at hgs hN
  generalize STORAGE_SET_STATE_GAS * Evm.measure m = E at hgs hG hN
  omega

end UsdtVerify.Complete
