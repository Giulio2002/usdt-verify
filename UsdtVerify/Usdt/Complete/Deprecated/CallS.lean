import UsdtVerify.Evm.FwdS
import UsdtVerify.Usdt.Complete.Deprecated.Call

/-!
# The forward of balanceOf and destroyBlackFunds over the EIP-8037 meter, to the CALL (round 44)

`fromExtS`: from EXTCODESIZE at 4874 (the forward that deprecated balanceOf and deprecated
destroyBlackFunds share), over `StateGasMeter` from any reservoir, when the code of the upgraded
address is found and is not empty, with its route, a depth below the limit, and the gas of
EXTCODESIZE, the two blocks, GAS, SUB and CALL (no memory to extend): the run goes on, step for
step with the meter of the frame but for its execution gas left, to the CALL at 4891, whose step
sends the message. The caller frame and the message are those of `callStep_child_rS`: the caller
has reservoir 0 and the message carries the reservoir of the frame.

Round 45: `fromExtSG` is the same at the six sites of the deprecated forwards (`fromExtC`), with
any input and output of the CALL in a memory it does not extend; `fromExtS` is its instance at
4874.
-/

namespace UsdtVerify.Complete

open EthLib.Base (Fork U256 toAddressMasked Address)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open UsdtVerify.Gas
open UsdtVerify.Meter
open GasCosts
open Deprecated

variable {fork : Fork} {message : Message fork}

/-- **From EXTCODESIZE to the CALL, over `StateGasMeter`, at any of the six sites** (round 45):
EXTCODESIZE at `p` and the CALL at `q` for totalSupply (3719, 3736), balanceOf and
destroyBlackFunds (4874, 4891), transfer (5739, 5756), approve (3213, 3230), transferFrom (4200,
4217) or allowance (7186, 7203), with the input `(i, isz)` and output `(o, osz)` of the CALL in a
memory `M` it does not extend. See the module doc. `A` is the price of EXTCODESIZE and `R` that of
the route. -/
theorem fromExtSG (hfork : .berlin ≤ fork) {p q : Nat}
    (hp : (p = 3719 ∧ q = 3736) ∨ (p = 4874 ∧ q = 4891) ∨ (p = 5739 ∧ q = 5756) ∨
      (p = 3213 ∧ q = 3230) ∨ (p = 4200 ∧ q = 4217) ∨ (p = 7186 ∧ q = 7203))
    {U i isz o osz : U256} {rest : List U256} (hrest : rest.length ≤ 10)
    {M : ByteArray} (hM : extendMemory M.size [(i, isz), (o, osz)] = ⟨0, 0⟩)
    {st : State.TransactionState} {ss : Substate} {c : ByteArray} {r : Route}
    (hcode : st.getCode (st.getAccount (toAddressMasked U)).codeHash = .ok c)
    (hw : BitVec.ofNat 256 c.size ≠ 0) (hroute : Routes fork st c r)
    (hdepth : message.depth + 1 ≤ STACK_DEPTH_LIMIT)
    {A R : Nat} (hA : extCost fork (decide (toAddressMasked U ∉ ss.accessedAddresses)) = A)
    (hR : routeCost fork (ss.accessedAddresses.insert (toAddressMasked U)) r = R)
    {G : Nat} (hg : A + 128 + R ≤ G) {m : Evm fork StateGasMeter}
    (start : At CODE message p (U :: U :: 0 :: i :: isz :: o :: osz :: rest) M G st ss
      (toNat m)) :
    ∃ (mC caller : Evm fork StateGasMeter) (msg : Message fork),
      mC.gas = { m.gas with gasLeft := mC.gas.gasLeft } ∧ mC.running = true ∧
      (∀ {bound : Nat} {runChild : MessageRunner fork StateGasMeter bound}
        (within : GasMeter.gasHeld m.gas ≤ bound), ∃ w,
        Evm.runFrame (step fork) (step_decreases fork) bound runChild m within =
          Evm.runFrame (step fork) (step_decreases fork) bound runChild mC w) ∧
      step fork mC = .ok (.child caller msg (resumeCall fork caller 0 o osz)) ∧
      caller.code = CODE ∧ caller.validJumpDestinations = validJumpDestinations CODE ∧
      caller.message = message ∧ caller.pc = q ∧ caller.stack.val = rest ∧ caller.memory = M ∧
      caller.gas = { m.gas with reservoir := 0, gasLeft := G - (A + 28) -
        (depCallGas fork (asked (G - (A + 25))) (G - (A + 28)) R).cost } ∧
      caller.running = true ∧ caller.error = none ∧ caller.output = .empty ∧
      caller.state = (routeState ((st.recordAccountRead (toAddressMasked U)).recordAccountRead
        (toAddressMasked U)) r).recordAccountRead message.currentTarget ∧
      caller.substate = routeSub { ss with
        accessedAddresses := (ss.accessedAddresses.insert (toAddressMasked U)).insert
          (toAddressMasked U) } r ∧
      msg.reservoir = m.gas.reservoir ∧
      msg.gas = (depCallGas fork (asked (G - (A + 25))) (G - (A + 28)) R).subCall ∧
      msg.caller = message.currentTarget ∧ msg.currentTarget = toAddressMasked U ∧
      msg.target = some (toAddressMasked U) ∧
      msg.codeAddress = some (routeAddr (toAddressMasked U) r) ∧
      msg.code = routeCode c r ∧ msg.disablePrecompiles = r.isSome ∧
      msg.data = memoryReadBytes M i.toNat isz.toNat ∧
      msg.value = 0 ∧ msg.depth = message.depth + 1 ∧
      msg.isStatic = message.isStatic ∧ msg.blockEnv = message.blockEnv ∧
      msg.txEnv = message.txEnv ∧ msg.shouldTransferValue = true := by
  have key : ∃ (h0 : p < CODE.size) (h15 : p + 15 < CODE.size) (hq : q < CODE.size),
      CODE[p] = 0x3b ∧ CODE[p + 15] = 0x5a ∧ CODE[q] = 0xf1 := by
    rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      exact ⟨by code_fact, by code_fact, by code_fact, by code_fact, by code_fact, by code_fact⟩
  have hm : (p + 1 = 3720 ∧ p + 15 = 3734) ∨ (p + 1 = 4875 ∧ p + 15 = 4889) ∨
      (p + 1 = 5740 ∧ p + 15 = 5754) ∨ (p + 1 = 3214 ∧ p + 15 = 3228) ∨
      (p + 1 = 4201 ∧ p + 15 = 4215) ∨ (p + 1 = 7187 ∧ p + 15 = 7201) := by
    rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
  have hsb : (p + 15 + 1 = 3735 ∧ q = 3736) ∨ (p + 15 + 1 = 4890 ∧ q = 4891) ∨
      (p + 15 + 1 = 5755 ∧ q = 5756) ∨ (p + 15 + 1 = 3229 ∧ q = 3230) ∨
      (p + 15 + 1 = 4216 ∧ q = 4217) ∨ (p + 15 + 1 = 7202 ∧ q = 7203) := by
    rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
  obtain ⟨h0, h15, hqs, b0, b15, bq⟩ := key
  have hA' : externalBaseCost fork (decide (toAddressMasked U ∉ ss.accessedAddresses)) = A := hA
  -- EXTCODESIZE
  obtain ⟨hlt1, hop1, z1, hz1, hpost1⟩ := At.next_of (post := At CODE message (p + 1)
      (BitVec.ofNat 256 c.size :: U :: 0 :: i :: isz :: o :: osz :: rest) M (G - A)
      (st.recordAccountRead (toAddressMasked U))
      { ss with accessedAddresses := ss.accessedAddresses.insert (toAddressMasked U) }) h0 b0
    (ofByte_of_decode (op := .extcodesize) rfl (Fork.frontier_le _)) rfl (fun evm hat => by
      obtain ⟨hc, hj, hm, hpc, hst, hmem, hgs, hrn, herr, hout, hs, hss⟩ := hat
      have found : accountCode evm (toAddressMasked U) = .ok c := by
        simp [accountCode, hs, hcode, Except.mapError]
      rw [extcodesizeStep_of_accountCode hst found]
      simp only [accessAddress, hfork, ↓reduceIte, hss, hgs, hA', charge_nat (show A ≤ G by omega)]
      exact ⟨_, rfl, hc, hj, hm, by simp [hpc], rfl, hmem, rfl, hrn, herr, hout, by simp [hs],
        by simp⟩) start
  obtain ⟨m1, hm1, hg1, hrun1⟩ := fwd_stepS (m := m) (.inr ⟨hlt1, .inl hop1⟩) hlt1 hop1
    (by decide) start.2.2.2.2.2.2.2.1 hz1 hpost1.2.2.2.2.2.2.2.1
  rw [← hm1] at hpost1
  -- the size is not 0
  obtain ⟨m2, hpost2, hg2, hrun2⟩ := fwd_splitS (B := 23) (c := 23)
    (fun g hg => midG (message := message) hm hw (by simp; omega) hg) (by decide) (fun _ _ => rfl)
    (by omega) hpost1
  -- GAS
  obtain ⟨hlt3, hop3, z3, hz3, hpost3⟩ := At.next_of (post := At CODE message (p + 15 + 1)
      (BitVec.ofNat 256 (G - A - 23 - 2) :: 0x02c6 :: U :: 0 :: i :: isz :: o :: osz :: rest) M
      (G - A - 23 - 2) (st.recordAccountRead (toAddressMasked U))
      { ss with accessedAddresses := ss.accessedAddresses.insert (toAddressMasked U) }) h15 b15
    (ofByte_of_decode (op := .gas) rfl (Fork.frontier_le _)) rfl (fun evm hat => by
      obtain ⟨hcode', hj, hm, hpc, hst, hmem, hgs, hrn, herr, hout, hs, hss⟩ := hat
      rw [readFrame_of_length_lt (by rw [hst]; simp [STACK_LIMIT]; omega),
        charge_nat (by rw [hgs, show OPCODE_GAS = 2 from rfl]; omega)]
      refine ⟨_, rfl, hcode', hj, hm, by simp [hpc], ?_, hmem, by simp [hgs, OPCODE_GAS, BASE],
        hrn, herr, hout, hs, hss⟩
      simp [hst, hgs, OPCODE_GAS, BASE, GasMeter.gasLeft]) hpost2
  obtain ⟨m3, hm3, hg3, hrun3⟩ := fwd_stepS (m := m2) (.inr ⟨hlt3, .inr hop3⟩) hlt3 hop3
    (by decide) hpost2.2.2.2.2.2.2.2.1 hz3 hpost3.2.2.2.2.2.2.2.1
  rw [← hm3] at hpost3
  -- SUB
  obtain ⟨mC, hpostC, hgC, hrunC⟩ := fwd_splitS (B := 3) (c := 3)
    (fun g hg => subG (message := message) hsb hg)
    (by decide) (fun _ _ => rfl) (by omega) hpost3
  have e1 : G - A - 23 - 2 = G - (A + 25) := by omega
  have e2 : G - (A + 25) - 3 = G - (A + 28) := by omega
  rw [e1, e2] at hpostC
  obtain ⟨hc4, hj4, hm4, hpc4, hst4, hmem4, hg4, hr4, herr4, hout4, hs4, hss4⟩ := hpostC
  -- CALL
  have hlt4 : mC.pc < mC.code.size := by
    show (toNat mC).pc < (toNat mC).code.size
    rw [hc4, hpc4]; exact hqs
  have hop4 : Op.ofByte fork mC.code[mC.pc] = some .call := by
    show Op.ofByte fork (toNat mC).code[(toNat mC).pc] = some .call
    simp only [hc4, hpc4, bq]; exact ofByte_of_decode (op := .call) rfl (Fork.frontier_le _)
  have hstS : mC.stack.val = asked (G - (A + 25)) :: U :: 0 :: i :: isz :: o :: osz ::
      rest := hst4
  have hsS : mC.state = st.recordAccountRead (toAddressMasked U) := hs4
  have hssS : mC.substate =
      { ss with accessedAddresses := ss.accessedAddresses.insert (toAddressMasked U) } := hss4
  have hmS : mC.message = message := hm4
  have hmemS : mC.memory = M := hmem4
  have hgS : mC.gas.gasLeft = G - (A + 28) := hg4
  have hcodeS : mC.state.getCode (mC.state.getAccount (toAddressMasked U)).codeHash = .ok c := by
    rw [hsS]; exact hcode
  have hrouteS : Routes fork mC.state c r := by rw [hsS]; exact routes_rec hroute
  have hwarm : callBaseCost fork (decide (toAddressMasked U ∉ mC.substate.accessedAddresses)) =
      100 := by
    rw [hssS, callBaseCost_eq hfork]; simp [accCost_false]
  have hRS : routeCost fork (mC.substate.accessedAddresses.insert (toAddressMasked U)) r = R := by
    rw [hssS]; exact (routeCost_insert_insert _ _ r).trans hR
  obtain ⟨caller, msg, hstep, c1, c2, c3, c4, c5, c6, c7, c8, c9, co, c10, c11, m0, mg, mcl, mct,
      mtg, mca, mcode, mdp, md, mv, mdep, mst, mbe, mte, msh⟩ :=
    callStep_child_rS hfork hstS hcodeS hrouteS (by rw [hmS]; exact hdepth)
      (by rw [hwarm, hRS, hmemS, hM, hgS]; simp only; omega)
  rw [hwarm, hRS, hmemS, hM, hgS] at c7 mg
  rw [hmemS, hM] at c6 md
  simp only [memoryExtend_zero] at c6 md
  have hcg : mC.gas = { m.gas with gasLeft := mC.gas.gasLeft } :=
    hgC.trans (by rw [hg3, hg2, hg1])
  refine ⟨mC, caller, msg, hcg, hr4, fun within => ?_, by rw [step_callS hlt4 hop4]; exact hstep,
    by rw [c1]; exact hc4, by rw [c2]; exact hj4, by rw [c3]; exact hmS, by rw [c4]; exact hpc4,
    c5, c6, ?_, by rw [c8]; exact hr4, by rw [c9]; exact herr4, by rw [co]; exact hout4,
    by rw [c10, hsS, hmS], by rw [c11, hssS], by rw [m0, hcg], ?_, by rw [mcl, hmS], mct,
    mtg, mca, mcode, mdp, md, mv, by rw [mdep, hmS], by rw [mst, hmS], by rw [mbe, hmS],
    by rw [mte, hmS], msh⟩
  · obtain ⟨w1, e1⟩ := hrun1 within
    obtain ⟨w2, e2⟩ := hrun2 w1
    obtain ⟨w3, e3⟩ := hrun3 w2
    obtain ⟨wC, eC⟩ := hrunC w3
    exact ⟨wC, e1.trans (e2.trans (e3.trans eC))⟩
  · rw [c7, hcg]
    simp only [depCallGas, Nat.add_zero]
  · rw [mg]

/-- **From EXTCODESIZE at 4874 to the CALL, over `StateGasMeter`.** `fromExtSG` at the site of
balanceOf and destroyBlackFunds, with the input (0x60, 0x24) and output (0x60, 0x20) of the CALL. -/
theorem fromExtS (hfork : .berlin ≤ fork) {U : U256} {rest : List U256} (hrest : rest.length ≤ 10)
    {M : ByteArray}
    (hM : extendMemory M.size [((0x60 : U256), (0x24 : U256)), ((0x60 : U256), (0x20 : U256))] =
      ⟨0, 0⟩)
    {st : State.TransactionState} {ss : Substate} {c : ByteArray} {r : Route}
    (hcode : st.getCode (st.getAccount (toAddressMasked U)).codeHash = .ok c)
    (hw : BitVec.ofNat 256 c.size ≠ 0) (hroute : Routes fork st c r)
    (hdepth : message.depth + 1 ≤ STACK_DEPTH_LIMIT)
    {A R : Nat} (hA : extCost fork (decide (toAddressMasked U ∉ ss.accessedAddresses)) = A)
    (hR : routeCost fork (ss.accessedAddresses.insert (toAddressMasked U)) r = R)
    {G : Nat} (hg : A + 128 + R ≤ G) {m : Evm fork StateGasMeter}
    (start : At CODE message 4874 (U :: U :: 0 :: 0x60 :: 0x24 :: 0x60 :: 0x20 :: rest) M G st ss
      (toNat m)) :
    ∃ (mC caller : Evm fork StateGasMeter) (msg : Message fork),
      mC.gas = { m.gas with gasLeft := mC.gas.gasLeft } ∧ mC.running = true ∧
      (∀ {bound : Nat} {runChild : MessageRunner fork StateGasMeter bound}
        (within : GasMeter.gasHeld m.gas ≤ bound), ∃ w,
        Evm.runFrame (step fork) (step_decreases fork) bound runChild m within =
          Evm.runFrame (step fork) (step_decreases fork) bound runChild mC w) ∧
      step fork mC = .ok (.child caller msg (resumeCall fork caller 0 0x60 0x20)) ∧
      caller.code = CODE ∧ caller.validJumpDestinations = validJumpDestinations CODE ∧
      caller.message = message ∧ caller.pc = 4891 ∧ caller.stack.val = rest ∧ caller.memory = M ∧
      caller.gas = { m.gas with reservoir := 0, gasLeft := G - (A + 28) -
        (depCallGas fork (asked (G - (A + 25))) (G - (A + 28)) R).cost } ∧
      caller.running = true ∧ caller.error = none ∧ caller.output = .empty ∧
      caller.state = (routeState ((st.recordAccountRead (toAddressMasked U)).recordAccountRead
        (toAddressMasked U)) r).recordAccountRead message.currentTarget ∧
      caller.substate = routeSub { ss with
        accessedAddresses := (ss.accessedAddresses.insert (toAddressMasked U)).insert
          (toAddressMasked U) } r ∧
      msg.reservoir = m.gas.reservoir ∧
      msg.gas = (depCallGas fork (asked (G - (A + 25))) (G - (A + 28)) R).subCall ∧
      msg.caller = message.currentTarget ∧ msg.currentTarget = toAddressMasked U ∧
      msg.target = some (toAddressMasked U) ∧
      msg.codeAddress = some (routeAddr (toAddressMasked U) r) ∧
      msg.code = routeCode c r ∧ msg.disablePrecompiles = r.isSome ∧
      msg.data = memoryReadBytes M 0x60 0x24 ∧
      msg.value = 0 ∧ msg.depth = message.depth + 1 ∧
      msg.isStatic = message.isStatic ∧ msg.blockEnv = message.blockEnv ∧
      msg.txEnv = message.txEnv ∧ msg.shouldTransferValue = true :=
  fromExtSG hfork (Or.inr (Or.inl ⟨rfl, rfl⟩)) hrest hM hcode hw hroute hdepth hA hR hg start

end UsdtVerify.Complete
