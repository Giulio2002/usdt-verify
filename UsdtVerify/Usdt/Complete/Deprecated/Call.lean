import UsdtVerify.Evm.RunC
import UsdtVerify.Usdt.Spec.Deprecated.Allowance
import UsdtVerify.Usdt.Complete.Dispatch

/-!
# The deprecated paths of USDT from EXTCODESIZE on, for any gas and any runner

The generic steps (EXTCODESIZE, GAS, SUB and CALL for any gas and any runner, `call_ok`,
`CallEnd`) are in Evm/Call.lean. Here:

- `midG`, `noCodeG`, `subG`: the blocks of `CODE` between EXTCODESIZE and CALL;
- `fromExt_found`: a successful run found the code of the upgraded address;
- `fromExt`: from EXTCODESIZE to the frame after CALL, for any gas.
- `fromExt_foundC`, `fromExtC` (round 39): the same over `RunC` (Evm/RunC.lean), for any relation
  `Run` of the child, ending in `CallEndC`.
-/

namespace UsdtVerify.Complete

open EthLib.Base (Fork U256 toAddressMasked Address)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open UsdtVerify.Gas
open GasCosts
open Deprecated

variable {fork : Fork} {bound : Nat} {runChild : MessageRunner fork Nat bound}
variable {code : ByteArray} {message : Message fork} {pc : Nat} {memory : ByteArray} {gas : Nat}
  {state : State.TransactionState} {substate : Substate}
/-! ## The blocks between EXTCODESIZE and CALL -/

/-- After EXTCODESIZE pushed a nonzero size: the JUMPI goes on, then PUSH2 710, up to GAS. -/
theorem midG {p q : Nat} (hp : (p = 3720 ∧ q = 3734) ∨ (p = 4875 ∧ q = 4889) ∨
      (p = 5740 ∧ q = 5754) ∨ (p = 3214 ∧ q = 3228) ∨ (p = 4201 ∧ q = 4215) ∨
      (p = 7187 ∧ q = 7201))
    {w : U256} (hw : w ≠ 0) {rest : List U256} (hrest : rest.length ≤ 16) {M : ByteArray}
    {st : State.TransactionState} {ss : Substate} {g : Nat} (hg : 23 ≤ g) :
    HoareG fork (At CODE message p (w :: rest) M g st ss)
      (At CODE message q (0x02c6 :: rest) M (g - 23) st ss) := by
  rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals
    step unR 0x15 instruction_iszero
    step unR 0x15 instruction_iszero
    step pushAnyR 2
    step jumpiR (isZero2_ne hw)
    step jumpdestR
    step pushR 2 (0x02c6 : U256)
    exact (repc (by decide)).seq (Gas.reshapeG rfl rfl (by gas_ok))

/-- After EXTCODESIZE pushed 0: the code reverts with no output. -/
theorem noCodeG (hfork : .berlin ≤ fork) {p : Nat}
    (hp : p = 3720 ∨ p = 4875 ∨ p = 5740 ∨ p = 3214 ∨ p = 4201 ∨ p = 7187) {M : ByteArray}
    {rest : List U256} (hrest : rest.length ≤ 16) {st : State.TransactionState} {ss : Substate}
    {g : Nat} (hg : 25 ≤ g) :
    SpecG fork (At CODE message p (0 :: rest) M g st ss) (Halted true .empty (g - 25) st ss) := by
  have hz : extendMemory M.size [((0 : U256), (0 : U256))] = ⟨0, 0⟩ := by
    simp [extendMemory]
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    step unR 0x15 instruction_iszero
    step unR 0x15 instruction_iszero
    step pushAnyR 2
    step jumpi0R isZero2_zero
    step pushR 1 (0 : U256)
    step dupR 0
    refine (Gas.revertG (Nat.le_trans (by decide) hfork) (by code_fact)
      (by code_fact) (by rw [hz]; gas_ok)).consequence (fun _ h => h) ?_
    rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
    refine ⟨hr, he, ?_, ?_, hs, hss⟩
    · rw [ho]; simp [memoryReadBytes]
    · rw [hgas, hz]; gas_ok

/-- SUB before the CALL. -/
theorem subG {p q : Nat} (hp : (p = 3735 ∧ q = 3736) ∨ (p = 4890 ∧ q = 4891) ∨
      (p = 5755 ∧ q = 5756) ∨ (p = 3229 ∧ q = 3230) ∨ (p = 4216 ∧ q = 4217) ∨
      (p = 7202 ∧ q = 7203))
    {x y : U256} {rest : List U256} {M : ByteArray} {st : State.TransactionState} {ss : Substate}
    {g : Nat} (hg : 3 ≤ g) :
    HoareG fork (At CODE message p (x :: y :: rest) M g st ss)
      (At CODE message q (sub x y :: rest) M (g - 3) st ss) := by
  rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals
    step binR 0x03 Local.instruction_sub
    exact Gas.reshapeG rfl rfl (by gas_ok)

/-! ## The code of the upgraded account is found -/

/-- At the EXTCODESIZE of the upgraded address (any of the six pcs), a run of the loop that ends
with no error found the code of the address in the state. -/
theorem fromExt_found {p : Nat}
    (hp : p = 3719 ∨ p = 4874 ∨ p = 5739 ∨ p = 3213 ∨ p = 4200 ∨ p = 7186)
    {U : U256} {rest : List U256} {M : ByteArray} {st : State.TransactionState} {ss : Substate}
    {G : Nat} {evm s : Evm fork Nat}
    (start : At CODE message p (U :: rest) M G st ss evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) :
    ∃ c, st.getCode (st.getAccount (toAddressMasked U)).codeHash = .ok c := by
  have key : ∃ (h0 : p < CODE.size), CODE[p] = 0x3b := by
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by code_fact, by code_fact⟩
  obtain ⟨h0, b0⟩ := key
  rcases hgc : st.getCode (st.getAccount (toAddressMasked U)).codeHash with e | c
  · exfalso
    obtain ⟨hc, -, -, hpc, hst, -, -, hr, -, -, hs, -⟩ := start
    have missing : accountCode evm (toAddressMasked U) = .error (.state e) := by
      simp [accountCode, hs, hgc, Except.mapError]
    obtain ⟨e', he'⟩ := extcodesizeStep_notFound hst missing
    refine ok_step_error (e := e') hr ?_ hrun hok
    rw [step_of_instruction (by rw [hc, hpc]; exact h0)
      (by simp only [hc, hpc, b0]; exact ofByte_of_decode (op := .extcodesize) rfl (Fork.frontier_le _)) instruction_extcodesize', he']
    rfl
  · exact ⟨c, rfl⟩

/-! ## From EXTCODESIZE to the frame after CALL, for any gas -/

/-- From EXTCODESIZE of the upgraded address at 3719 (totalSupply), 4874 (balanceOf), 5739
(transfer), 3213 (approve), 4200 (transferFrom) or 7186 (allowance; its failure tail at 7204 is
`DeprecatedAllowance.failTailA`), with ANY gas `G`, under ANY runner: a run of the
loop that ends with no error had a nonzero code size, the gas of EXTCODESIZE, the blocks and the
CALL's access and memory (`extCost fork + 128 + memory`, EXTCODESIZE at its price `extCost`), a depth below the limit, and it goes through
`CallEnd` (the runner gave a frame, and the loop goes on from the frame after CALL).

The CALL follows a route `r` (`Routes`): no delegation, or, from Pectra, a delegation indicator in
`c` to an address whose code is found (a failed lookup of that code makes the CALL fail). The gas
covers the access to the delegate too (`routeCost`). Hypothesis: the code `c` of the address is
found (`hcode`; `fromExt_found` proves it for a successful run). -/
theorem fromExt (hfork : .berlin ≤ fork) {p q : Nat}
    (hp : (p = 3719 ∧ q = 3736) ∨ (p = 4874 ∧ q = 4891) ∨ (p = 5739 ∧ q = 5756) ∨
      (p = 3213 ∧ q = 3230) ∨ (p = 4200 ∧ q = 4217) ∨ (p = 7186 ∧ q = 7203))
    {U i isz o osz : U256} {rest : List U256} (hrest : rest.length ≤ 10) {M : ByteArray}
    {st : State.TransactionState} {ss : Substate} {c : ByteArray}
    (hcode : st.getCode (st.getAccount (toAddressMasked U)).codeHash = .ok c)
    {G : Nat} {evm s : Evm fork Nat}
    (start : At CODE message p (U :: U :: 0 :: i :: isz :: o :: osz :: rest) M G st ss evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) :
    ∃ r, Routes fork st c r ∧
    BitVec.ofNat 256 c.size ≠ 0 ∧
    extCost fork (decide (toAddressMasked U ∉ ss.accessedAddresses)) + 128 +
      routeCost fork (ss.accessedAddresses.insert (toAddressMasked U)) r +
      (extendMemory M.size [(i, isz), (o, osz)]).cost ≤ G ∧
    message.depth + 1 ≤ STACK_DEPTH_LIMIT ∧
    CallEnd runChild CODE message q
      (asked (G - (extCost fork (decide (toAddressMasked U ∉ ss.accessedAddresses)) + 25)))
      U i isz o osz rest M (G - (extCost fork (decide (toAddressMasked U ∉ ss.accessedAddresses)) + 28))
      (st.recordAccountRead (toAddressMasked U))
      { ss with accessedAddresses := ss.accessedAddresses.insert (toAddressMasked U) } false c r s := by
  have key : ∃ (h0 : p < CODE.size) (h15 : p + 15 < CODE.size) (hq : q < CODE.size),
      CODE[p] = 0x3b ∧ CODE[p + 15] = 0x5a ∧ CODE[q] = 0xf1 ∧ q = p + 17 := by
    rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      exact ⟨by code_fact, by code_fact, by code_fact, by code_fact, by code_fact, by code_fact, rfl⟩
  have hm : (p + 1 = 3720 ∧ p + 15 = 3734) ∨ (p + 1 = 4875 ∧ p + 15 = 4889) ∨
      (p + 1 = 5740 ∧ p + 15 = 5754) ∨ (p + 1 = 3214 ∧ p + 15 = 3228) ∨
      (p + 1 = 4201 ∧ p + 15 = 4215) ∨ (p + 1 = 7187 ∧ p + 15 = 7201) := by
    rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
  have hn : p + 1 = 3720 ∨ p + 1 = 4875 ∨ p + 1 = 5740 ∨ p + 1 = 3214 ∨ p + 1 = 4201 ∨
      p + 1 = 7187 := by
    rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
  have hsb : (p + 15 + 1 = 3735 ∧ q = 3736) ∨ (p + 15 + 1 = 4890 ∧ q = 4891) ∨
      (p + 15 + 1 = 5755 ∧ q = 5756) ∨ (p + 15 + 1 = 3229 ∧ q = 3230) ∨
      (p + 15 + 1 = 4216 ∧ q = 4217) ∨ (p + 15 + 1 = 7202 ∧ q = 7203) := by
    rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
  have hf : (q + 1 = 3737 ∨ q + 1 = 4892 ∨ q + 1 = 5757 ∨ q + 1 = 3231 ∨ q + 1 = 4218) ∨
      q + 1 = 7204 := by
    rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
  obtain ⟨h0, h15, hqs, b0, b15, bq, -⟩ := key
  generalize hA : extCost fork (decide (toAddressMasked U ∉ ss.accessedAddresses)) = A
  have hr0 : evm.running = true := start.2.2.2.2.2.2.2.1
  -- EXTCODESIZE
  by_cases hlow : G < A
  · exact absurd hok (ok_step_error hr0 (extcodesize_low hfork h0 b0 hcode
      (by rw [hA]; exact hlow) start) hrun)
  obtain ⟨z1, w1, hz1, hrun1⟩ := ok_hoare (Local.extcodesize hfork h0 b0 hcode rfl
    (by rw [← hA] at hlow; simp only [extCost] at hlow; omega)) start within hrun
  have hz1' : At CODE message (p + 1) (BitVec.ofNat 256 c.size :: U :: 0 :: i :: isz :: o :: osz ::
      rest) M (G - A) (st.recordAccountRead (toAddressMasked U))
      { ss with accessedAddresses := ss.accessedAddresses.insert (toAddressMasked U) } z1 := by
    rw [← hA]; exact hz1
  -- the size
  by_cases hw : BitVec.ofNat 256 c.size = 0
  · rw [hw] at hz1'
    exact (no_ok (fun g hg => noCodeG hfork hn (by simp; omega) hg)
      (fun g e h => by rw [h.2.1]; simp) hz1' w1 hrun1 hok).elim
  obtain ⟨h23, z2, w2, hz2, hrun2⟩ := ok_split (c := 23) (B := 23) (Nat.le_refl _)
    (fun g hg => midG hm hw (by simp; omega) hg) hz1' w1 hrun1 hok
  -- GAS
  by_cases hg2 : G - A - 23 < 2
  · exact absurd hok (ok_step_error hz2.2.2.2.2.2.2.2.1 (step_gas_low h15 b15 hg2 hz2) hrun2)
  obtain ⟨z3, w3, hz3, hrun3⟩ := ok_hoare (Logic.gas_rule h15 b15 (by omega)
    (by simp [STACK_LIMIT]; omega)) hz2 w2 hrun2
  -- SUB
  obtain ⟨h3, z4, w4, hz4, hrun4⟩ := ok_split (c := 3) (B := 3) (Nat.le_refl _)
    (fun g hg => subG hsb hg) hz3 w3 hrun3 hok
  have e1 : G - A - 23 - 2 = G - (A + 25) := by omega
  have e2 : G - (A + 25) - 3 = G - (A + 28) := by omega
  rw [e1, e2] at hz4
  obtain ⟨hc4, hj4, hm4, hpc4, hst4, hmem4, hg4, hr4, herr4, hout4, hs4, hss4⟩ := hz4
  have hlt4 : z4.pc < z4.code.size := by rw [hc4, hpc4]; exact hqs
  have hb4 : z4.code[z4.pc] = 0xf1 := by simp only [hc4, hpc4, bq]
  have hcode4 : z4.state.getCode (z4.state.getAccount (toAddressMasked U)).codeHash = .ok c := by
    rw [hs4]; exact hcode
  have hwarm : callBaseCost fork (decide (toAddressMasked U ∉ z4.substate.accessedAddresses)) =
      100 := by
    rw [hss4, callBaseCost_eq hfork]; simp [accCost_false]
  -- the route: a delegate whose code is not found makes the CALL fail
  have hex : ∃ r, Routes fork st c r := by
    by_cases hpec : Fork.pectra ≤ fork
    · rcases hd : delegatedAddress c with _ | d
      · exact ⟨none, fun _ => hd⟩
      · rcases hdc : st.getCode (st.getAccount d).codeHash with e | c'
        · exact absurd hok (ok_step_bad hr4 (by
            rw [step_call hlt4 hb4]
            exact callStep_missing hfork hst4 hcode4 hpec hd (by rw [hs4]; exact hdc)) hrun4)
        · exact ⟨some (d, c'), hpec, hd, hdc⟩
    · exact ⟨none, fun h => absurd h hpec⟩
  obtain ⟨r, hroute⟩ := hex
  have hroute4 : Routes fork z4.state c r := by rw [hs4]; exact routes_rec hroute
  generalize hR : routeCost fork (ss.accessedAddresses.insert (toAddressMasked U)) r = R
  have hR4 : routeCost fork (z4.substate.accessedAddresses.insert (toAddressMasked U)) r = R := by
    rw [hss4]; exact (routeCost_insert_insert _ _ r).trans hR
  -- CALL with too little gas
  by_cases hlowc : G - (A + 28) < 100 + R + (extendMemory M.size [(i, isz), (o, osz)]).cost
  · exact absurd hok (ok_step_bad hr4 (by
      rw [step_call hlt4 hb4]
      exact callStep_low_r hfork hst4 hcode4 hroute4 (by rw [hwarm, hR4, hmem4, hg4]; omega)) hrun4)
  -- CALL at the greatest depth
  by_cases hdeep : STACK_DEPTH_LIMIT < message.depth + 1
  · obtain ⟨after, hstep, a1, a2, a3, a4, a5, a6, a7, a8⟩ := callStep_deep_r hfork hst4
      hcode4 hroute4 (by rw [hm4]; exact hdeep) (by rw [hwarm, hR4, hmem4, hg4]; omega)
    rw [runFrame_of_step_eq_next hr4 (by rw [step_call hlt4 hb4]; exact hstep)] at hrun4
    have hat : At CODE message (q + 1) (0 :: rest) after.memory after.gas after.state
        after.substate after :=
      ⟨by rw [a1, hc4], by rw [a2, hj4], by rw [a3, hm4], by rw [a4, hpc4], a5, rfl, rfl,
        by rw [a6, hr4], by rw [a7, herr4], by rw [a8, hout4], rfl, rfl⟩
    rcases hf with hf | hf
    · exact (no_ok (fun g hg => failTail hfork hf (by omega) hg)
        (fun g e h => by rw [h.2.1]; simp) hat _ hrun4 hok).elim
    · rw [hf] at hat
      exact (no_ok (fun g hg => DeprecatedAllowance.failTailA hfork (by omega) hg)
        (fun g e h => by rw [h.2.1]; simp) hat _ hrun4 hok).elim
  refine ⟨r, hroute, hw, by omega, by omega, ?_⟩
  exact call_ok (state := st.recordAccountRead (toAddressMasked U))
    (substate := { ss with accessedAddresses := ss.accessedAddresses.insert (toAddressMasked U) })
    hfork hqs bq hcode (routes_rec hroute) (by omega) (by simp)
    (by rw [accCost_false, routeCost_insert_insert, hR]; omega)
    ⟨hc4, hj4, hm4, hpc4, hst4, hmem4, hg4, hr4, herr4, hout4, hs4, hss4⟩ w4 hrun4

/-! ## The same over `RunC` (round 39) -/

section RunC

variable {Run : Evm fork Nat → Message fork → Evm fork Nat → Prop}

/-- `fromExt_found` over `RunC`. -/
theorem fromExt_foundC {p : Nat}
    (hp : p = 3719 ∨ p = 4874 ∨ p = 5739 ∨ p = 3213 ∨ p = 4200 ∨ p = 7186)
    {U : U256} {rest : List U256} {M : ByteArray} {st : State.TransactionState} {ss : Substate}
    {G : Nat} {evm s : Evm fork Nat}
    (start : At CODE message p (U :: rest) M G st ss evm)
    (hrun : RunC fork Run evm s) (hok : s.error = none) :
    ∃ c, st.getCode (st.getAccount (toAddressMasked U)).codeHash = .ok c := by
  have key : ∃ (h0 : p < CODE.size), CODE[p] = 0x3b := by
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by code_fact, by code_fact⟩
  obtain ⟨h0, b0⟩ := key
  rcases hgc : st.getCode (st.getAccount (toAddressMasked U)).codeHash with e | c
  · exfalso
    obtain ⟨hc, -, -, hpc, hst, -, -, hr, -, -, hs, -⟩ := start
    have missing : accountCode evm (toAddressMasked U) = .error (.state e) := by
      simp [accountCode, hs, hgc, Except.mapError]
    obtain ⟨e', he'⟩ := extcodesizeStep_notFound hst missing
    have hlt : evm.pc < evm.code.size := by rw [hc, hpc]; exact h0
    have hop : Op.ofByte fork evm.code[evm.pc] = some .extcodesize := by
      simp only [hc, hpc, b0]; exact ofByte_of_decode (op := .extcodesize) rfl (Fork.frontier_le _)
    refine hrun.not_bad hr (fwd_of_op hlt hop (.inl rfl)) (.inl ⟨e', ?_⟩) hok
    rw [step_of_instruction hlt hop instruction_extcodesize', he']
    rfl
  · exact ⟨c, rfl⟩

/-- `fromExt` over `RunC`: from EXTCODESIZE of the upgraded address, with any gas, a `RunC` with
any relation `Run` of the child that ends with no error had a nonzero code size, the gas of
EXTCODESIZE, the blocks and the CALL's accesses and memory, a depth below the limit, and goes
through `CallEndC`. -/
theorem fromExtC (hfork : .berlin ≤ fork) {p q : Nat}
    (hp : (p = 3719 ∧ q = 3736) ∨ (p = 4874 ∧ q = 4891) ∨ (p = 5739 ∧ q = 5756) ∨
      (p = 3213 ∧ q = 3230) ∨ (p = 4200 ∧ q = 4217) ∨ (p = 7186 ∧ q = 7203))
    {U i isz o osz : U256} {rest : List U256} (hrest : rest.length ≤ 10) {M : ByteArray}
    {st : State.TransactionState} {ss : Substate} {c : ByteArray}
    (hcode : st.getCode (st.getAccount (toAddressMasked U)).codeHash = .ok c)
    {G : Nat} {evm s : Evm fork Nat}
    (start : At CODE message p (U :: U :: 0 :: i :: isz :: o :: osz :: rest) M G st ss evm)
    (hrun : RunC fork Run evm s) (hok : s.error = none) :
    ∃ r, Routes fork st c r ∧
    BitVec.ofNat 256 c.size ≠ 0 ∧
    extCost fork (decide (toAddressMasked U ∉ ss.accessedAddresses)) + 128 +
      routeCost fork (ss.accessedAddresses.insert (toAddressMasked U)) r +
      (extendMemory M.size [(i, isz), (o, osz)]).cost ≤ G ∧
    message.depth + 1 ≤ STACK_DEPTH_LIMIT ∧
    CallEndC Run CODE message q
      (asked (G - (extCost fork (decide (toAddressMasked U ∉ ss.accessedAddresses)) + 25)))
      U i isz o osz rest M (G - (extCost fork (decide (toAddressMasked U ∉ ss.accessedAddresses)) + 28))
      (st.recordAccountRead (toAddressMasked U))
      { ss with accessedAddresses := ss.accessedAddresses.insert (toAddressMasked U) } false c r s := by
  have key : ∃ (h0 : p < CODE.size) (h15 : p + 15 < CODE.size) (hq : q < CODE.size),
      CODE[p] = 0x3b ∧ CODE[p + 15] = 0x5a ∧ CODE[q] = 0xf1 ∧ q = p + 17 := by
    rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      exact ⟨by code_fact, by code_fact, by code_fact, by code_fact, by code_fact, by code_fact, rfl⟩
  have hm : (p + 1 = 3720 ∧ p + 15 = 3734) ∨ (p + 1 = 4875 ∧ p + 15 = 4889) ∨
      (p + 1 = 5740 ∧ p + 15 = 5754) ∨ (p + 1 = 3214 ∧ p + 15 = 3228) ∨
      (p + 1 = 4201 ∧ p + 15 = 4215) ∨ (p + 1 = 7187 ∧ p + 15 = 7201) := by
    rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
  have hn : p + 1 = 3720 ∨ p + 1 = 4875 ∨ p + 1 = 5740 ∨ p + 1 = 3214 ∨ p + 1 = 4201 ∨
      p + 1 = 7187 := by
    rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
  have hsb : (p + 15 + 1 = 3735 ∧ q = 3736) ∨ (p + 15 + 1 = 4890 ∧ q = 4891) ∨
      (p + 15 + 1 = 5755 ∧ q = 5756) ∨ (p + 15 + 1 = 3229 ∧ q = 3230) ∨
      (p + 15 + 1 = 4216 ∧ q = 4217) ∨ (p + 15 + 1 = 7202 ∧ q = 7203) := by
    rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
  have hf : (q + 1 = 3737 ∨ q + 1 = 4892 ∨ q + 1 = 5757 ∨ q + 1 = 3231 ∨ q + 1 = 4218) ∨
      q + 1 = 7204 := by
    rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
  obtain ⟨h0, h15, hqs, b0, b15, bq, -⟩ := key
  generalize hA : extCost fork (decide (toAddressMasked U ∉ ss.accessedAddresses)) = A
  have hr0 : evm.running = true := start.2.2.2.2.2.2.2.1
  -- EXTCODESIZE
  have hF0 : Fwd evm := by
    obtain ⟨hc, -, -, hpc, -⟩ := start
    have hlt : evm.pc < evm.code.size := by rw [hc, hpc]; exact h0
    exact fwd_of_op hlt (by
      simp only [hc, hpc, b0]; exact ofByte_of_decode (op := .extcodesize) rfl (Fork.frontier_le _))
      (.inl rfl)
  by_cases hlow : G < A
  · exact (hrun.not_bad hr0 hF0 (.inl ⟨_, extcodesize_low hfork h0 b0 hcode
      (by rw [hA]; exact hlow) start⟩) hok).elim
  obtain ⟨z1, hz1, hrun1⟩ := RunC.extcodesize hfork h0 b0 hcode
    (by rw [← hA] at hlow; simp only [extCost] at hlow; omega) start hrun hok
  have hz1' : At CODE message (p + 1) (BitVec.ofNat 256 c.size :: U :: 0 :: i :: isz :: o :: osz ::
      rest) M (G - A) (st.recordAccountRead (toAddressMasked U))
      { ss with accessedAddresses := ss.accessedAddresses.insert (toAddressMasked U) } z1 := by
    rw [← hA]; exact hz1
  -- the size
  by_cases hw : BitVec.ofNat 256 c.size = 0
  · rw [hw] at hz1'
    exact (no_okC (Nat.le_refl 25) (fun g hg => noCodeG hfork hn (by simp; omega) hg)
      (by omega) (fun _ _ => rfl) hz1' hrun1 hok).elim
  obtain ⟨h23, z2, hz2, hrun2⟩ := ok_splitCA (c := 23) (B := 23) (Nat.le_refl _)
    (fun g hg => midG hm hw (by simp; omega) hg) (by omega) (fun _ _ => rfl) hz1' hrun1 hok
  -- GAS
  have hF2 : Fwd z2 := by
    obtain ⟨hc, -, -, hpc, -⟩ := hz2
    have hlt : z2.pc < z2.code.size := by rw [hc, hpc]; exact h15
    exact fwd_of_op hlt (by
      simp only [hc, hpc, b15]; exact ofByte_of_decode (op := .gas) rfl (Fork.frontier_le _))
      (.inr rfl)
  by_cases hg2 : G - A - 23 < 2
  · exact (hrun2.not_bad hz2.2.2.2.2.2.2.2.1 hF2 (.inl ⟨_, step_gas_low h15 b15 hg2 hz2⟩) hok).elim
  obtain ⟨z3, hz3, hrun3⟩ := RunC.gasOp h15 b15 (by omega) (by simp [STACK_LIMIT]; omega) hz2
    hrun2 hok
  -- SUB
  obtain ⟨h3, z4, hz4, hrun4⟩ := ok_splitCA (c := 3) (B := 3) (Nat.le_refl _)
    (fun g hg => subG hsb hg) (by omega) (fun _ _ => rfl) hz3 hrun3 hok
  have e1 : G - A - 23 - 2 = G - (A + 25) := by omega
  have e2 : G - (A + 25) - 3 = G - (A + 28) := by omega
  rw [e1, e2] at hz4
  obtain ⟨hc4, hj4, hm4, hpc4, hst4, hmem4, hg4, hr4, herr4, hout4, hs4, hss4⟩ := hz4
  have hlt4 : z4.pc < z4.code.size := by rw [hc4, hpc4]; exact hqs
  have hb4 : z4.code[z4.pc] = 0xf1 := by simp only [hc4, hpc4, bq]
  have hcode4 : z4.state.getCode (z4.state.getAccount (toAddressMasked U)).codeHash = .ok c := by
    rw [hs4]; exact hcode
  have hF4 : Fwd z4 := .inr ⟨hlt4, by
    rw [hb4]; exact ofByte_of_decode (op := .call) rfl (Fork.frontier_le _),
    _, _, _, _, _, _, _, _, hst4, hcode4⟩
  have hwarm : callBaseCost fork (decide (toAddressMasked U ∉ z4.substate.accessedAddresses)) =
      100 := by
    rw [hss4, callBaseCost_eq hfork]; simp [accCost_false]
  -- the route: a delegate whose code is not found makes the CALL fail
  have hex : ∃ r, Routes fork st c r := by
    by_cases hpec : Fork.pectra ≤ fork
    · rcases hd : delegatedAddress c with _ | d
      · exact ⟨none, fun _ => hd⟩
      · rcases hdc : st.getCode (st.getAccount d).codeHash with e | c'
        · exact (hrun4.not_bad hr4 hF4 (by
            rw [step_call hlt4 hb4]
            exact callStep_missing hfork hst4 hcode4 hpec hd (by rw [hs4]; exact hdc)) hok).elim
        · exact ⟨some (d, c'), hpec, hd, hdc⟩
    · exact ⟨none, fun h => absurd h hpec⟩
  obtain ⟨r, hroute⟩ := hex
  have hroute4 : Routes fork z4.state c r := by rw [hs4]; exact routes_rec hroute
  generalize hR : routeCost fork (ss.accessedAddresses.insert (toAddressMasked U)) r = R
  have hR4 : routeCost fork (z4.substate.accessedAddresses.insert (toAddressMasked U)) r = R := by
    rw [hss4]; exact (routeCost_insert_insert _ _ r).trans hR
  -- CALL with too little gas
  by_cases hlowc : G - (A + 28) < 100 + R + (extendMemory M.size [(i, isz), (o, osz)]).cost
  · exact (hrun4.not_bad hr4 hF4 (by
      rw [step_call hlt4 hb4]
      exact callStep_low_r hfork hst4 hcode4 hroute4 (by rw [hwarm, hR4, hmem4, hg4]; omega))
      hok).elim
  -- CALL at the greatest depth
  by_cases hdeep : STACK_DEPTH_LIMIT < message.depth + 1
  · obtain ⟨after, hstep, a1, a2, a3, a4, a5, a6, a7, a8⟩ := callStep_deep_r hfork hst4
      hcode4 hroute4 (by rw [hm4]; exact hdeep) (by rw [hwarm, hR4, hmem4, hg4]; omega)
    have hruna := hrun4.next_of hr4 hF4 (by rw [step_call hlt4 hb4]; exact hstep) hok
    have hat : At CODE message (q + 1) (0 :: rest) after.memory after.gas after.state
        after.substate after :=
      ⟨by rw [a1, hc4], by rw [a2, hj4], by rw [a3, hm4], by rw [a4, hpc4], a5, rfl, rfl,
        by rw [a6, hr4], by rw [a7, herr4], by rw [a8, hout4], rfl, rfl⟩
    rcases hf with hf | hf
    · exact (no_okC (Nat.le_refl 25) (fun g hg => failTail hfork hf (by omega) hg)
        (by omega) (fun _ _ => rfl) hat hruna hok).elim
    · rw [hf] at hat
      exact (no_okC (Nat.le_refl 25) (fun g hg => DeprecatedAllowance.failTailA hfork (by omega) hg)
        (by omega) (fun _ _ => rfl) hat hruna hok).elim
  refine ⟨r, hroute, hw, by omega, by omega, ?_⟩
  exact call_okC (state := st.recordAccountRead (toAddressMasked U))
    (substate := { ss with accessedAddresses := ss.accessedAddresses.insert (toAddressMasked U) })
    hfork hqs bq hcode (routes_rec hroute) (by omega) (by simp)
    (by rw [accCost_false, routeCost_insert_insert, hR]; omega)
    ⟨hc4, hj4, hm4, hpc4, hst4, hmem4, hg4, hr4, herr4, hout4, hs4, hss4⟩ hrun4 hok

/-- The dispatcher over `EndsOk`: from a fresh frame where `EndsOk` holds, the call data has 4
bytes or more, a selector of the table, and the call value is 0. -/
theorem EndsOk.dispatch (hfork : .berlin ≤ fork) (hsize' : message.data.size < 2 ^ 256)
    {gas : Nat} {evm : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm) (hE : EndsOk fork evm) :
    4 ≤ message.data.size ∧ message.value = 0 ∧
      ∃ i : Fin 32, selector message.data = ENTRIES[i].1.toNat :=
  let ⟨k, _, hs, hok⟩ := hE
  ends_ok_dispatch hfork hsize' (at_sh start k) hs hok

end RunC

end UsdtVerify.Complete
