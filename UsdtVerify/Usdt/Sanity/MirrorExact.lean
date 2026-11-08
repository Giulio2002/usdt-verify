import UsdtVerify.Usdt.Sanity.ProcessExact
import UsdtVerify.Usdt.Sanity.Mirror

/-!
# Sanity: gas-exact deprecated instances under `processRunner` with `MIRROR` (round 31)

docs/AUDIT.md, finding 3. Round 30 instantiated the deprecated exact theorems with
`processRunner` and the upgraded code STOP, which succeeds at every gas. Here the upgraded address
holds `MIRROR` (Evm/Mirror.lean), whose success depends on the gas the CALL gives: it needs
`mirrorCost c = 87 + slotCost c` gas, `c` the coldness of the slot it reads.

From Paris, with `MIRROR` at the upgraded address (no precompile):

- `process_mirror_sends`: a `balanceOf(a)` message that the path sends ends under `processRunner`
  in a frame (never an error), with no error exactly when its gas covers `mirrorCost`; then it
  has that much less gas, answers the word of slot `balSlot message` of the upgraded address in
  the caller's state, and ends with that slot recorded read and accessed;
- `noFailOn_process_mirror`: so `processRunner` meets `NoFailOn` for these messages;
- `hans_gas_process_mirror`: the `hans` of `balanceOf_dep_ok_iff_gas`, with `A` the bound on the
  gas `g` the CALL gives: `mirrorCost ≤ g` and the code after the CALL has its gas;
- `hans_destroy_gas_process_mirror`: the `hans` of `destroyBlackFunds_dep_ok_iff_gas`, with `A`
  stated over the state, the substate and the gas of the caller frame at the CALL;
- `balanceOf_dep_ok_iff_gas_process_mirror` and `destroyBlackFunds_dep_ok_iff_gas_process_mirror`:
  the instances. The second takes `hmirror` (the slot `MIRROR` reads holds, in the start state,
  the word of USDT's `balances[a]`), the hypothesis under which `processRunner` meets
  `HonestBalanceAt` (`honestBalanceAt_process_mirror`); the word that the tail subtracts is then
  USDT's own `balances[a]` in the start state.
-/

namespace UsdtVerify.Sanity

open EthLib.Base (Fork U256 Address)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open Exact Complete Deprecated DeprecatedBalance DeprecatedAllowance DeprecatedTransfer
open DeprecatedTransferFrom DeprecatedDestroy Transfer TransferFrom Owner BlackList DestroySpec

variable {fork : Fork}

/-- The gas `MIRROR` uses when the slot it reads is cold (`c`) or warm. -/
abbrev mirrorCost (c : Bool) : Nat := 87 + slotCost c

/-- `MIRROR` is no delegation indicator, so its route is `none`. -/
theorem route_mirror {S : State.TransactionState} {r : Route} (h : Routes fork S MIRROR r) :
    r = none := by
  rcases r with _ | ⟨d, c'⟩
  · rfl
  · exact absurd h.2.1 (by rw [delegatedAddress_mirror]; exact fun h => by cases h)

/-- From Paris, a `balanceOf(a)` message that a deprecated path sends to an upgraded address
holding `MIRROR` (no precompile), under `processRunner`: the runner returns a frame, which ends with
no error exactly when the message has `mirrorCost` gas for the coldness of `balSlot message` of
the upgraded address in the caller's substate; then the frame has that much less gas, outputs
the word of that slot in the caller's state, and ends in the caller's state with the slot
recorded read and in the caller's substate (as `Substate.child` passes it on) with the slot
accessed. -/
theorem process_mirror_sends (hparis : .paris ≤ fork) {bound : Nat} {message : Message fork}
    {S : State.TransactionState} {ua : Address} {r : Route}
    (hroute : Routes fork S MIRROR r)
    (hnp : Precompiles.isPrecompile fork ua.toU256.toNat = false)
    (caller : Evm fork Nat) {msg : Message fork} (lt : msg.gas < bound)
    (hs : SendsVia message ua MIRROR r (dataB message) msg) :
    ∃ child, processRunner fork bound caller msg lt = .ok child ∧
      (child.1.error = none ↔ mirrorCost (coldIn caller.substate ua (balSlot message)) ≤ msg.gas) ∧
      (child.1.error = none →
        child.1.gas = msg.gas - mirrorCost (coldIn caller.substate ua (balSlot message)) ∧
        child.1.output = wordBytes (storageAt caller.state ua (balSlot message)) ∧
        child.1.state = readSlot caller.state ua (balSlot message) ∧
        child.1.substate = accessSlot caller.substate.child ua (balSlot message)) := by
  obtain rfl := route_mirror hroute
  obtain ⟨-, hmt, htg, hca, hmc, -, hmd, hval, -, -⟩ := hs
  have hpre := precompile_none_of (fork := fork) hnp hca
  have hk : loadWord msg.data 4 32 = addrArg message.data 0 := by
    rw [hmd]; exact loadWord_append_wordBytes SEL_B _
  obtain ⟨child, hc, hiff, hok⟩ := process_mirror_iff hparis caller lt hmc htg hval hpre hk
  rw [hmt] at hiff hok
  exact ⟨child, hc, hiff, hok⟩

/-- From Paris, with `MIRROR` at the upgraded address (no precompile), `processRunner` returns a
frame for every `balanceOf(a)` message the path sends. -/
theorem noFailOn_process_mirror (hparis : .paris ≤ fork) {bound : Nat} {message : Message fork}
    {S : State.TransactionState} {ua : Address} {r : Route}
    (hroute : Routes fork S MIRROR r)
    (hnp : Precompiles.isPrecompile fork ua.toU256.toNat = false)
    {Cl : Evm fork Nat → Message fork → Prop} :
    NoFailOn (processRunner fork bound)
      (fun caller msg => SendsVia message ua MIRROR r (dataB message) msg ∧ Cl caller msg) := by
  intro caller msg lt e hs h
  obtain ⟨child, hc, -⟩ := process_mirror_sends hparis hroute hnp caller lt hs.1
  rw [hc] at h; cases h

/-- The `hans` of `balanceOf_dep_ok_iff_gas` (round 30 form) for `MIRROR`: the forwarded message
ends with no error and leaves `T ≤ K` plus its gas left exactly when the gas `g` the CALL gives
covers `mirrorCost` (coldness taken in the caller's substate `ss` at the CALL) and `T ≤ K` plus
what is left of `g`. -/
theorem hans_gas_process_mirror (hparis : .paris ≤ fork) {bound : Nat} {message : Message fork}
    {S : State.TransactionState} {ua : Address} {r : Route}
    (hroute : Routes fork S MIRROR r)
    (hnp : Precompiles.isPrecompile fork ua.toU256.toNat = false)
    {g : Nat} {st : State.TransactionState} {ss : Substate} (T K : Nat) :
    ∀ caller msg lt child, processRunner fork bound caller msg lt = .ok child →
      SendsVia message ua MIRROR r (dataB message) msg → CallFrom g st ss caller msg →
      (child.1.error = none ∧ T ≤ K + child.1.gas ↔
        mirrorCost (coldIn ss ua (balSlot message)) ≤ g ∧
          T ≤ K + (g - mirrorCost (coldIn ss ua (balSlot message)))) := by
  rintro caller msg lt child hch hs ⟨hg, -, hcss⟩
  obtain ⟨child', hc, hiff, hok⟩ := process_mirror_sends hparis hroute hnp caller lt hs
  rw [hch] at hc; cases hc
  rw [← hg, ← hcss]
  constructor
  · rintro ⟨he, hT⟩
    rw [(hok he).1] at hT
    exact ⟨hiff.1 he, hT⟩
  · rintro ⟨hle, hT⟩
    have he := hiff.2 hle
    exact ⟨he, by rw [(hok he).1]; exact hT⟩

theorem incorporate_state (caller child : Evm fork Nat) :
    (incorporateChild fork caller child).state = child.state := by
  unfold incorporateChild; split <;> rfl

/-- The `hans` of `destroyBlackFunds_dep_ok_iff_gas` (round 30 form) for `MIRROR`: with the gas
`g`, the state `st` and the substate `ss` of the caller frame at the CALL, the forwarded
`balanceOf(a)` ends with no error, with an account of the contract, and with gas for the tail
exactly when `g` covers `mirrorCost`, `st` has an account of the contract, and the gas left
covers the cost and the stipend bound of the tail, computed over `st` with the slot recorded
read, the word of the slot in `st`, and the coldness in `ss` with the slot accessed. -/
theorem hans_destroy_gas_process_mirror (hparis : .paris ≤ fork) {bound : Nat}
    {message : Message fork} {S : State.TransactionState} {ua : Address} {r : Route}
    (hroute : Routes fork S MIRROR r)
    (hnp : Precompiles.isPrecompile fork ua.toU256.toNat = false)
    {g : Nat} {st : State.TransactionState} {ss : Substate} (K : Nat) :
    ∀ caller msg lt child, processRunner fork bound caller msg lt = .ok child →
      SendsVia message ua MIRROR r (dataB message) msg → CallFrom g st ss caller msg →
      (child.1.error = none ∧ hasAccount child.1.state message.currentTarget ∧
          max (tailCost fork (incorporateChild fork caller child.1).state message.currentTarget
              (addrArg message.data 0) (resWord (outMemOf (memD message) child.1.output))
              (coldIn (incorporateChild fork caller child.1).substate message.currentTarget
                (balSlot message))
              (coldIn (accessSlot (incorporateChild fork caller child.1).substate
                message.currentTarget (balSlot message)) message.currentTarget 1))
            (tailStip fork (incorporateChild fork caller child.1).state message.currentTarget
              (addrArg message.data 0)
              (coldIn (incorporateChild fork caller child.1).substate message.currentTarget
                (balSlot message))
              (coldIn (accessSlot (incorporateChild fork caller child.1).substate
                message.currentTarget (balSlot message)) message.currentTarget 1)) ≤
            K + child.1.gas ↔
        mirrorCost (coldIn ss ua (balSlot message)) ≤ g ∧
          hasAccount st message.currentTarget ∧
          max (tailCost fork (readSlot st ua (balSlot message)) message.currentTarget
              (addrArg message.data 0) (storageAt st ua (balSlot message))
              (coldIn (accessSlot ss ua (balSlot message)) message.currentTarget
                (balSlot message))
              (coldIn (accessSlot (accessSlot ss ua (balSlot message))
                message.currentTarget (balSlot message)) message.currentTarget 1))
            (tailStip fork (readSlot st ua (balSlot message)) message.currentTarget
              (addrArg message.data 0)
              (coldIn (accessSlot ss ua (balSlot message)) message.currentTarget
                (balSlot message))
              (coldIn (accessSlot (accessSlot ss ua (balSlot message))
                message.currentTarget (balSlot message)) message.currentTarget 1)) ≤
            K + (g - mirrorCost (coldIn ss ua (balSlot message)))) := by
  rintro caller msg lt child hch hs ⟨hg, hcs, hcss⟩
  obtain ⟨child', hc, hiff, hok⟩ := process_mirror_sends hparis hroute hnp caller lt hs
  rw [hch] at hc; cases hc
  subst hg hcs hcss
  by_cases he : child.1.error = none
  · obtain ⟨hgas, hout, hsta, hsub⟩ := hok he
    have hk : (incorporateChild fork caller child.1).substate.accessedStorageKeys =
        (accessSlot caller.substate ua (balSlot message)).accessedStorageKeys := by
      rw [incorporate_keys _ _ he, hsub]; rfl
    have hw : resWord (outMemOf (memD message) child.1.output) =
        storageAt caller.state ua (balSlot message) := by
      rw [hout, resWord_outMemOf (size_memD message) (by rw [size_wordBytes]; omega),
        loadWord_wordBytes_zero]
    rw [coldIn_congr hk, coldIn_accessSlot_congr hk, incorporate_state, hw, hgas, hsta,
      hasAccount_readSlot_iff]
    exact ⟨fun h => ⟨hiff.1 he, h.2⟩, fun h => ⟨he, h.2⟩⟩
  · constructor
    · rintro ⟨he', -⟩; exact absurd he' he
    · rintro ⟨hle, -⟩; exact absurd (hiff.2 hle) he

/-- **Deprecated balanceOf under `processRunner` with `MIRROR`, every gas from `hg` on (round
31).** From Paris, with the upgraded address holding `MIRROR` (no precompile), `cM` the coldness
of the slot `MIRROR` reads at the CALL, and the hypotheses of `Exact.balanceOf_dep_ok_iff_gas`:
the run succeeds iff the checks hold, the gas the CALL gives covers `mirrorCost cM`, and the gas
left after the CALL plus what `MIRROR` returns of the gas it was given is at least the 126 gas of
the code after the CALL. -/
theorem balanceOf_dep_ok_iff_gas_process_mirror (hparis : .paris ≤ fork)
    {message : Message fork} {state : State.TransactionState} {substate : Substate}
    {gas bound : Nat} {evm : Evm fork Nat}
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x70a08231)
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0)
    (hcode : state.getCode (state.getAccount (upAddr state message)).codeHash = .ok MIRROR)
    {r : Route} (hroute : Routes fork state MIRROR r) {c10 cU cM : Bool}
    (hc10 : coldIn substate message.currentTarget 10 = c10)
    (hcU : decide (upAddr state message ∉ substate.accessedAddresses) = cU)
    (hcM : coldIn (accessSlot substate message.currentTarget 10) (upAddr state message)
      (balSlot message) = cM)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hnp : Precompiles.isPrecompile fork (upAddr state message).toU256.toNat = false)
    (hg : preCostB fork c10 cU + 100 + callR substate state message r ≤ gas) :
    RunsOk fork bound (processRunner fork bound) evm within ↔ ForwardOk message MIRROR ∧
      (mirrorCost cM ≤ (callGasB fork gas c10 cU (callR substate state message r)).subCall ∧
        126 ≤ gas - preCostB fork c10 cU - (callGasB fork gas c10 cU (callR substate state message r)).cost +
          ((callGasB fork gas c10 cU (callR substate state message r)).subCall - mirrorCost cM)) := by
  have h := Exact.balanceOf_dep_ok_iff_gas (Nat.le_trans (by decide) hparis) hsize' hsel hdep hcode
    hroute hc10 hcU start within (by rw [size_MIRROR]; decide) hg
    (hans_gas_process_mirror hparis hroute hnp _ _) (noFailOn_process_mirror hparis hroute hnp)
  obtain rfl := route_mirror hroute
  exact hcM ▸ h

/-- **Deprecated destroyBlackFunds under `processRunner` with `MIRROR`, every gas from `hg` on
(round 31).** From Paris, with the upgraded address holding `MIRROR` (no precompile), `hmirror`
(the slot `MIRROR` reads holds in `state` the word of USDT's `balances[a]`), and the hypotheses of
`Exact.destroyBlackFunds_dep_ok_iff_gas`: the run succeeds iff `DestroyDepGuard` holds, the gas
the CALL gives covers `mirrorCost` (coldness in the substate at the CALL), the state at the CALL
has an account of the contract, and the gas left after the CALL plus what `MIRROR` returns covers
the cost and the stipend bound of the tail, computed over the state at the CALL with the slot
recorded read, USDT's `balances[a]` in `state` as the word subtracted, and the coldness at the
CALL with the slot accessed. -/
theorem destroyBlackFunds_dep_ok_iff_gas_process_mirror (hparis : .paris ≤ fork)
    {message : Message fork} {state : State.TransactionState} {substate : Substate}
    {gas bound : Nat} {evm : Evm fork Nat}
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xf3bdc228)
    (hdep : byte20 (storageAt state message.currentTarget 10) ≠ 0)
    (hcode : state.getCode (state.getAccount (upAddr state message)).codeHash = .ok MIRROR)
    {r : Route} (hroute : Routes fork state MIRROR r) {c0 cL c10 cU : Bool}
    (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hcL : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget
      (listSlot (addrArg message.data 0)) = cL)
    (hc10 : coldIn (preSub substate message) message.currentTarget 10 = c10)
    (hcU : decide (upAddr state message ∉ substate.accessedAddresses) = cU)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hnp : Precompiles.isPrecompile fork (upAddr state message).toU256.toNat = false)
    (hg : preCostD fork c0 cL c10 cU + 100 + callRD substate state message r ≤ gas)
    (hmirror : storageAt state (upAddr state message) (balSlot message) =
      storageAt state message.currentTarget (balSlot message)) :
    RunsOk fork bound (processRunner fork bound) evm within ↔
      DestroyDepGuard state message MIRROR ∧
      (mirrorCost (coldIn (atCallSub (callSubD substate state message) (upAddr state message) r)
          (upAddr state message) (balSlot message)) ≤
          (callGasD fork gas c0 cL c10 cU (callRD substate state message r)).subCall ∧
        hasAccount (atCallState (callStateD state message) (upAddr state message) r
          message.currentTarget) message.currentTarget ∧
        max (tailCost fork (readSlot (atCallState (callStateD state message) (upAddr state message) r
              message.currentTarget) (upAddr state message) (balSlot message))
              message.currentTarget (addrArg message.data 0)
              (storageAt state message.currentTarget (balSlot message))
              (coldIn (accessSlot (atCallSub (callSubD substate state message)
                (upAddr state message) r) (upAddr state message) (balSlot message))
                message.currentTarget (balSlot message))
              (coldIn (accessSlot (accessSlot (atCallSub (callSubD substate state message)
                (upAddr state message) r) (upAddr state message) (balSlot message))
                message.currentTarget (balSlot message)) message.currentTarget 1))
            (tailStip fork (readSlot (atCallState (callStateD state message) (upAddr state message) r
              message.currentTarget) (upAddr state message) (balSlot message))
              message.currentTarget (addrArg message.data 0)
              (coldIn (accessSlot (atCallSub (callSubD substate state message)
                (upAddr state message) r) (upAddr state message) (balSlot message))
                message.currentTarget (balSlot message))
              (coldIn (accessSlot (accessSlot (atCallSub (callSubD substate state message)
                (upAddr state message) r) (upAddr state message) (balSlot message))
                message.currentTarget (balSlot message)) message.currentTarget 1)) ≤
          gas - preCostD fork c0 cL c10 cU -
            (callGasD fork gas c0 cL c10 cU (callRD substate state message r)).cost +
            ((callGasD fork gas c0 cL c10 cU (callRD substate state message r)).subCall -
              mirrorCost (coldIn (atCallSub (callSubD substate state message)
                (upAddr state message) r) (upAddr state message) (balSlot message)))) := by
  have h := Exact.destroyBlackFunds_dep_ok_iff_gas (Nat.le_trans (by decide) hparis) hsize' hsel
    hdep hcode hroute hc0 hcL hc10 hcU start within (by rw [size_MIRROR]; decide) hg
    (hans_destroy_gas_process_mirror hparis hroute hnp _) (noFailOn_process_mirror hparis hroute hnp)
  obtain rfl := route_mirror hroute
  have hw : storageAt (atCallState (callStateD state message) (upAddr state message) none
      message.currentTarget) (upAddr state message) (balSlot message) =
      storageAt state message.currentTarget (balSlot message) := by
    rw [← hmirror]
    exact (sameView_recordAccountRead (sameView_recordAccountRead (sameView_recordAccountRead
      (sameView_readSlot (sameView_readSlot (sameView_readSlot (SameView.refl state) _ _) _ _)
        _ _) _) _) _).1 _ _
  rw [hw] at h
  exact h

end UsdtVerify.Sanity
