import UsdtVerify.Invariant

/-!
# The invariant when deprecated: destroyBlackFunds(a)

When deprecated, `destroyBlackFunds(a)` asks the UPGRADED contract for `balanceOf(a)` (answer
`d`), then writes, in THIS contract, `balances[a] := 0` and `_totalSupply := _totalSupply - d`
(unchecked). `S` below is the state that the call left (the callee may call back into this
contract, so `S` may differ from the state at the start in this contract's storage too).

- `inv_tail_iff`: if `Inv C S` holds and `C` has an account in `S`, then `Inv` holds after the
  two writes exactly when `d` is the local balance `balances[a]` in `S`.
- `exists_breaks`: under `KeccakSep`, for every address `C` there are a state `S` (an empty
  account at `C`, every storage word 0), `a = 0` and `d = 1` with `Inv C S`, an account of `C`,
  and not `Inv C (tailState S C a d)`.
- `depD_inv`: every run of deprecated `destroyBlackFunds(a)` under a runner whose successful
  forwarded calls leave `Inv C` and the account of `C` (`hcallee`) ends, when it ends with no
  error, in a state `tailState S C a d` with `Inv C S`, where `Inv` holds iff `d = balances[a]`
  in `S`.
- `depD_keeps`: the same, with a callee that answers the local balance in its end state: `Inv`
  holds at the end.
- `depD_breaks`: from a state with `Inv C`, with a callee that succeeds, answers `o` (at least
  32 bytes) and leaves every word of `C`'s storage as it was, and `loadWord o 0 32 ≠ balances[a]`:
  every run ends with no error in a state where `Inv C` FAILS.

All of `depD_*` are under the hypotheses of `spec_depD` (enough gas, code at the upgraded
address, the route of the CALL (no delegation, or an EIP-7702 delegate), depth), as `SpecUnder` statements (they hold under every runner that
meets the callee assumption; the run may also abort).
-/

namespace UsdtVerify.DepInv

open EthLib.Base (Fork U256 Address)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open Invariant Deprecated DeprecatedBalance DeprecatedDestroy DestroySpec Transfer TransferOk
  Owner BlackList
open UsdtVerify.Complete (Route Routes routeState SendsVia)

theorem toNat_sub_gt {x a : U256} (h : x.toNat < a.toNat) :
    (sub x a).toNat = 2 ^ 256 - a.toNat + x.toNat := by
  have ha := a.isLt
  simp only [sub, BitVec.toNat_sub]
  rw [Nat.mod_eq_of_lt (by omega)]

/-- After the two writes of deprecated destroyBlackFunds over a state `S` with `Inv`, `Inv`
holds exactly when the answer `d` is the local balance of `a` in `S`. -/
theorem inv_tail_iff (K : KeccakSep) {C : Address} {S : State.TransactionState}
    (hacc : hasAccount S C) {a : U256} (ha : a.toNat < 2 ^ 160) (hI : Inv C S) (d : U256) :
    Inv C (tailState S C a d) ↔ d = storageAt S C (mapSlot a 2) := by
  have hb := le_sumTo (f := bal C S) (fun i => Int.natCast_nonneg _) (a := a.toNat) (2 ^ 160) ha
  simp only [bal, ofNat_toNat] at hb
  have hI' : sumBal C S = ((storageAt S C 1).toNat : Int) := hI
  unfold sumBal at hI'
  rw [hI'] at hb
  have h1 : storageAt (writeSlot S C (mapSlot a 2) 0) C 1 = storageAt S C 1 :=
    storageAt_writeSlot_of_ne hacc (Ne.symm (bal_ne_one K a))
  unfold Invariant.Inv
  simp only [tailState, h1]
  rw [sumBal_write_nb (hasAccount_writeSlot hacc) (fun x _ e => bal_ne_one K x e.symm),
    sumBal_write_bal K hacc ha, tot_write_one (hasAccount_writeSlot hacc)]
  have hI2 : sumBal C S = ((storageAt S C 1).toNat : Int) := hI
  rw [hI2]
  have z : (0 : U256).toNat = 0 := rfl
  rw [z]
  have hdl := d.isLt
  by_cases hd : d.toNat ≤ (storageAt S C 1).toNat
  · rw [toNat_sub hd]
    constructor
    · intro h
      apply BitVec.eq_of_toNat_eq
      omega
    · intro h
      rw [h]
      omega
  · rw [toNat_sub_gt (by omega)]
    generalize (2 : Nat) ^ 256 = N at *
    constructor
    · intro h
      omega
    · intro h
      rw [h] at hd
      omega

/-- An answer other than the local balance breaks `Inv`. -/
theorem not_inv_tail (K : KeccakSep) {C : Address} {S : State.TransactionState}
    (hacc : hasAccount S C) {a : U256} (ha : a.toNat < 2 ^ 160) (hI : Inv C S) {d : U256}
    (hd : d ≠ storageAt S C (mapSlot a 2)) : ¬ Inv C (tailState S C a d) :=
  fun h => hd ((inv_tail_iff K hacc ha hI d).mp h)

/-- `Σ_{i < n} 0 = 0`. -/
theorem sumTo_zero : ∀ n, sumTo (fun _ => (0 : Int)) n = 0
  | 0 => rfl
  | n + 1 => by rw [sumTo, sumTo_zero n]; rfl

/-- A state with an empty account at `C` and no storage word set anywhere. -/
def zeroState (C : Address) : State.TransactionState :=
  { State.TransactionState.ofBlock ⟨⟨∅, ∅, ∅⟩, ∅, ∅, ∅, ∅⟩ with
    accountWrites := (∅ : Std.ExtTreeMap Address (Option State.Account)).insert C
      (some State.EMPTY_ACCOUNT) }

theorem storageAt_zeroState (C c : Address) (n : U256) : storageAt (zeroState C) c n = 0 := by
  simp [storageAt, zeroState, State.TransactionState.ofBlock, State.TransactionState.getStorage,
    State.StorageMap.slot, State.State.getStorage]

theorem hasAccount_zeroState (C : Address) : hasAccount (zeroState C) C := by
  simp [hasAccount, zeroState, State.TransactionState.ofBlock,
    State.TransactionState.getAccountOptional]

/-- The concrete counterexample to `Inv` after deprecated destroyBlackFunds: the zero state, `a = 0`,
the answer `d = 1` (the local balance is 0). -/
theorem exists_breaks (K : KeccakSep) (C : Address) :
    ∃ S : State.TransactionState, ∃ a d : U256, hasAccount S C ∧ Inv C S ∧
      ¬ Inv C (tailState S C a d) := by
  have hI : Inv C (zeroState C) := by
    unfold Invariant.Inv sumBal tot
    rw [sumTo_congr (g := fun _ => (0 : Int)) _ (fun i _ => by simp [bal, storageAt_zeroState]),
      sumTo_zero, storageAt_zeroState]
    rfl
  refine ⟨zeroState C, 0, 1, hasAccount_zeroState C, hI,
    not_inv_tail K (hasAccount_zeroState C) (by decide) hI ?_⟩
  rw [storageAt_zeroState]
  decide

/-- Two states with the same words in `C`'s storage have the same `Inv C`. -/
theorem inv_congr {C : Address} {S S' : State.TransactionState}
    (h : ∀ n, storageAt S' C n = storageAt S C n) : Inv C S' ↔ Inv C S := by
  unfold Invariant.Inv sumBal tot
  rw [h 1, sumTo_congr (f := bal C S') (g := bal C S) _ (fun i _ => by simp only [bal, h])]

/-- The state at the CALL of deprecated destroyBlackFunds, along any route, has the words of the
start state. -/
theorem storageAt_callerD {fork : Fork} (state : State.TransactionState) (message : Message fork)
    (u : Address) (r : Route) (n : U256) :
    storageAt ((routeState ((callStateD state message).recordAccountRead u) r).recordAccountRead
      message.currentTarget) message.currentTarget n = storageAt state message.currentTarget n := by
  rcases r with _ | ⟨d, _⟩ <;>
  · simp only [routeState, callStateD, preState, storageAt,
      State.TransactionState.getStorage_recordAccountRead]
    rw [← storageAt, storageAt_readSlot, storageAt_readSlot, storageAt_readSlot]

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate}

/-- Deprecated `destroyBlackFunds(a)`: a successful end is `tailState S C a d` over a state `S`
with `Inv` (by `hcallee`), and there `Inv` holds iff `d = balances[a]` in `S`. -/
theorem depD_inv (K : KeccakSep) (hfork : .berlin ≤ fork)
    (hstatic : message.isStatic = false)
    (hsize : 4 ≤ message.data.size) (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0xf3bdc228) (hv : message.value = 0)
    (hown : callerWord message = ownerOf state message.currentTarget)
    (hl : (storageAt state message.currentTarget (listSlot (addrArg message.data 0))).toNat % 256 ≠ 0)
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0) {c : ByteArray}
    (hcode : state.getCode (state.getAccount (upAddr state message)).codeHash = .ok c)
    (hsz : 0 < c.size) (hszl : c.size < 2 ^ 256)
    {r : Route} (hroute : Routes fork state c r)
    (hdepth : message.depth + 1 ≤ STACK_DEPTH_LIMIT) {c0 cL c10 cU : Bool}
    (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hcL : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget
      (listSlot (addrArg message.data 0)) = cL)
    (hc10 : coldIn (preSub substate message) message.currentTarget 10 = c10)
    (hcU : decide (upAddr state message ∉ substate.accessedAddresses) = cU)
    {gas : Nat} (hg : preCostD fork c0 cL c10 cU + 100 + callRD substate state message r ≤ gas)
    (htail : TAIL_MAX fork ≤ gas - preCostD fork c0 cL c10 cU - (callGasD fork gas c0 cL c10 cU (callRD substate state message r)).cost)
    {callee : Evm fork Nat → Message fork → Evm fork Nat → Prop}
    (hcallee : ∀ caller msg child, callee caller msg child →
      SendsVia message (upAddr state message) c r (dataB message) msg → child.error = none →
        hasAccount child.state message.currentTarget ∧ Inv message.currentTarget child.state) :
    SpecUnder fork callee (At CODE message 0 [] .empty gas state substate)
      fun evm => evm.error = none → ∃ S d, Inv message.currentTarget S ∧
        evm.state = tailState S message.currentTarget (addrArg message.data 0) d ∧
        (Inv message.currentTarget evm.state ↔ d = storageAt S message.currentTarget (balSlot message)) := by
  refine (spec_depD hfork hstatic hsize hsize' hsel hv hown hl hdep hcode hsz hszl hroute
    hdepth hc0 hcL hc10 hcU hg htail
    (fun cl m ch h1 h2 h3 => (hcallee cl m ch h1 h2 h3).1)).consequence (fun _ h => h) ?_
  rintro evm ⟨caller, msg, child, hcal, hfwd, -, -, -, hok, hko⟩ herr
  by_cases he : child.error = none
  · obtain ⟨-, -, -, -, hs, -⟩ := hok he
    obtain ⟨hacc, hI⟩ := hcallee caller msg child hcal hfwd he
    rw [state_incorporateChild] at hs
    refine ⟨child.state, _, hI, hs, ?_⟩
    rw [hs]
    exact inv_tail_iff K hacc (addrArg_lt _ _) hI _
  · obtain ⟨-, herr', -⟩ := hko he
    rw [herr] at herr'
    simp at herr'

/-- Deprecated `destroyBlackFunds(a)` with a callee that keeps `Inv` and answers the local
balance of `a` in its end state (`hans`): every successful end keeps `Inv`. -/
theorem depD_keeps (K : KeccakSep) (hfork : .berlin ≤ fork)
    (hstatic : message.isStatic = false)
    (hsize : 4 ≤ message.data.size) (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0xf3bdc228) (hv : message.value = 0)
    (hown : callerWord message = ownerOf state message.currentTarget)
    (hl : (storageAt state message.currentTarget (listSlot (addrArg message.data 0))).toNat % 256 ≠ 0)
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0) {c : ByteArray}
    (hcode : state.getCode (state.getAccount (upAddr state message)).codeHash = .ok c)
    (hsz : 0 < c.size) (hszl : c.size < 2 ^ 256)
    {r : Route} (hroute : Routes fork state c r)
    (hdepth : message.depth + 1 ≤ STACK_DEPTH_LIMIT) {c0 cL c10 cU : Bool}
    (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hcL : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget
      (listSlot (addrArg message.data 0)) = cL)
    (hc10 : coldIn (preSub substate message) message.currentTarget 10 = c10)
    (hcU : decide (upAddr state message ∉ substate.accessedAddresses) = cU)
    {gas : Nat} (hg : preCostD fork c0 cL c10 cU + 100 + callRD substate state message r ≤ gas)
    (htail : TAIL_MAX fork ≤ gas - preCostD fork c0 cL c10 cU - (callGasD fork gas c0 cL c10 cU (callRD substate state message r)).cost)
    {callee : Evm fork Nat → Message fork → Evm fork Nat → Prop}
    (hcallee : ∀ caller msg child, callee caller msg child →
      SendsVia message (upAddr state message) c r (dataB message) msg → child.error = none →
        hasAccount child.state message.currentTarget ∧ Inv message.currentTarget child.state)
    (hans : ∀ caller msg child, callee caller msg child →
      SendsVia message (upAddr state message) c r (dataB message) msg → child.error = none →
        resWord (outMemOf (memD message) child.output) =
          storageAt child.state message.currentTarget (balSlot message)) :
    SpecUnder fork callee (At CODE message 0 [] .empty gas state substate)
      fun evm => evm.error = none → Inv message.currentTarget evm.state := by
  refine (spec_depD hfork hstatic hsize hsize' hsel hv hown hl hdep hcode hsz hszl hroute
    hdepth hc0 hcL hc10 hcU hg htail
    (fun cl m ch h1 h2 h3 => (hcallee cl m ch h1 h2 h3).1)).consequence (fun _ h => h) ?_
  rintro evm ⟨caller, msg, child, hcal, hfwd, -, -, -, hok, hko⟩ herr
  by_cases he : child.error = none
  · obtain ⟨-, -, -, -, hs, -⟩ := hok he
    obtain ⟨hacc, hI⟩ := hcallee caller msg child hcal hfwd he
    rw [state_incorporateChild] at hs
    rw [hs]
    exact (inv_tail_iff K hacc (addrArg_lt _ _) hI _).mpr (hans caller msg child hcal hfwd he)
  · obtain ⟨-, herr', -⟩ := hko he
    rw [herr] at herr'
    simp at herr'

/-- The counterexample, for every start state with `Inv`: a callee that succeeds with the output
`o`, keeps every word of `C`'s storage, and answers a word other than `balances[a]` at the start
(`hne`). Every run ends with no error, and `Inv` fails at its end. -/
theorem depD_breaks (K : KeccakSep) (hfork : .berlin ≤ fork)
    (hstatic : message.isStatic = false)
    (hsize : 4 ≤ message.data.size) (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0xf3bdc228) (hv : message.value = 0)
    (hown : callerWord message = ownerOf state message.currentTarget)
    (hl : (storageAt state message.currentTarget (listSlot (addrArg message.data 0))).toNat % 256 ≠ 0)
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0) {c : ByteArray}
    (hcode : state.getCode (state.getAccount (upAddr state message)).codeHash = .ok c)
    (hsz : 0 < c.size) (hszl : c.size < 2 ^ 256)
    {r : Route} (hroute : Routes fork state c r)
    (hdepth : message.depth + 1 ≤ STACK_DEPTH_LIMIT) {c0 cL c10 cU : Bool}
    (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hcL : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget
      (listSlot (addrArg message.data 0)) = cL)
    (hc10 : coldIn (preSub substate message) message.currentTarget 10 = c10)
    (hcU : decide (upAddr state message ∉ substate.accessedAddresses) = cU)
    {gas : Nat} (hg : preCostD fork c0 cL c10 cU + 100 + callRD substate state message r ≤ gas)
    (htail : TAIL_MAX fork ≤ gas - preCostD fork c0 cL c10 cU - (callGasD fork gas c0 cL c10 cU (callRD substate state message r)).cost)
    (hI : Inv message.currentTarget state)
    {callee : Evm fork Nat → Message fork → Evm fork Nat → Prop} {o : ByteArray}
    (hans : AnswersD message (upAddr state message) c r (dataB message) o callee)
    (ho : 32 ≤ o.size)
    (hsame : ∀ caller msg child, callee caller msg child →
      SendsVia message (upAddr state message) c r (dataB message) msg →
        hasAccount child.state message.currentTarget ∧
        ∀ n, storageAt child.state message.currentTarget n =
          storageAt caller.state message.currentTarget n)
    (hne : loadWord o 0 32 ≠ storageAt state message.currentTarget (balSlot message)) :
    SpecUnder fork callee (At CODE message 0 [] .empty gas state substate)
      fun evm => evm.error = none ∧ ¬ Inv message.currentTarget evm.state := by
  refine (spec_depD hfork hstatic hsize hsize' hsel hv hown hl hdep hcode hsz hszl hroute
    hdepth hc0 hcL hc10 hcU hg htail
    (fun cl m ch h1 h2 _ => (hsame cl m ch h1 h2).1)).consequence (fun _ h => h) ?_
  rintro evm ⟨caller, msg, child, hcal, hfwd, -, hcs, -, hok, -⟩
  obtain ⟨he, hout⟩ := hans caller msg child hcal hfwd
  obtain ⟨hacc, hst⟩ := hsame caller msg child hcal hfwd
  have hst' : ∀ n, storageAt child.state message.currentTarget n =
      storageAt state message.currentTarget n := by
    intro n
    rw [hst n, hcs, storageAt_callerD]
  obtain ⟨-, herr, -, -, hs, -⟩ := hok he
  rw [state_incorporateChild, hout, resWord_outMemOf (size_memD _) ho] at hs
  refine ⟨by simpa using herr, ?_⟩
  rw [hs]
  refine not_inv_tail K hacc (addrArg_lt _ _) ((inv_congr hst').mpr hI) ?_
  rw [hst']
  exact hne

end UsdtVerify.DepInv
