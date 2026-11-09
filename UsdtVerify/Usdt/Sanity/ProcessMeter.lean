import UsdtVerify.Usdt.Sanity.Process
import UsdtVerify.Usdt.Sanity.Mirror
import UsdtVerify.Usdt.Invariant.DepMeter
import UsdtVerify.Usdt.Security.DepMeter

/-!
# Sanity: EthLib's runner over the EIP-8037 meter meets the runner assumptions (round 41)

docs/AUDIT.md, fourth audit, finding U2: no instance of `KeepsInvAtS`, `HonestBalanceAtS` or
`KeepsAtS` was shown. Here the upgraded address holds the one byte STOP (`STOP_CODE`) and is no
precompile, and the runner is EthLib's `processRunner` over `StateGasMeter`.

- `step_stopS`: one step of STOP over `StateGasMeter` stops the frame and moves the pc.
- `process_stopS`: from Paris, a message that runs `STOP_CODE` at a target with no value and no
  precompile, run by `processRunner` over `StateGasMeter`, ends with no error in the state it
  starts from.
- `keepsInvAtS_process_stop`: from Paris, `processRunner` at any bound meets `KeepsInvAtS`.
- `keepsAtS_process_stop`: from Paris, it meets `KeepsAtS … R` for every reflexive relation `R`,
  so the runner assumptions of the five `_call_allS` theorems (`BalKept`, `ProtKept`,
  `ListedNoDec`, `AllowKept`, `SupplyKept`, all reflexive).
- `process_mirrorS`: from Paris, a message that runs `MIRROR` (Evm/Mirror.lean) at a target with
  no value and no precompile, run by `processRunner` over `StateGasMeter` from any caller frame
  and any reservoir, that ends with no error, returns the word in slot `mapSlot k 2` of its
  current target in the caller's state and ends in the caller's state with that slot recorded
  read. It follows from the run over the meter `Nat` with more gas (`Shadow.shadow_ends`).
- `honestBalanceAtS_process_mirror`: from Paris, when the upgraded address holds `MIRROR`, is no
  precompile, and its slot `balSlot message` holds in `S` the word of USDT's `balances[a]`,
  `processRunner` over `StateGasMeter`, at any bound, meets `HonestBalanceAtS`.

The STOP proofs are those of the reviewer of the fourth audit.

Usdt/Sanity/ProcessMeterR.lean (round 44) has the same instances at every reservoir.
-/

namespace UsdtVerify.Sanity

open EthLib.Base (Fork U256 Address)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open Complete Security Invariant Deprecated DeprecatedBalance DeprecatedDestroy DestroySpec

variable {fork : Fork}

/-- One step of STOP over `StateGasMeter` stops the frame and moves the pc. -/
theorem step_stopS (f : Evm fork StateGasMeter) (hc : f.code = STOP_CODE) (hpc : f.pc = 0) :
    step fork f = .ok (.next (advance { f with running := false })) := by
  have h : f.pc < f.code.size := by rw [hc, hpc]; decide
  have hd : Op.ofByte fork f.code[f.pc] = some .stop := by simp only [hc, hpc]; rfl
  rw [step_of_instruction h hd (by rfl)]
  rfl

/-- From Paris, a message that runs `STOP_CODE` at a target with no value and no precompile, run
by `processRunner` over `StateGasMeter`, ends with no error in the state it starts from. -/
theorem process_stopS (hparis : .paris ≤ fork) {bound : Nat} (caller : Evm fork StateGasMeter)
    {msg : Message fork} (lt : msg.gas < bound) (hcode : msg.code = STOP_CODE)
    {ua : Address} (ht : msg.target = some ua) (hv : msg.value = 0)
    (hpre : precompileAddress fork msg = none)
    {child : { evm : Evm fork StateGasMeter // GasMeter.gasHeld evm.gas ≤ msg.gas }}
    (hch : processRunner fork bound caller msg lt = .ok child) :
    child.1.error = none ∧ child.1.state = caller.state := by
  have hst : startState fork msg caller.state = caller.state := by
    simp only [startState, show ¬fork < Fork.paris from Nat.not_lt.mpr hparis, ite_false]
  have hp : processRunner fork bound caller msg lt =
      processMessage fork msg caller.state caller.substate.child := by
    simp only [processRunner, ht]
  have hran : runFrame (step fork) (step_decreases fork) msg.gas
      (processRunner fork msg.gas)
      (startFrame msg (startState fork msg caller.state) caller.substate.child
        (GasMeter.start msg.gas msg.reservoir : StateGasMeter))
      (Nat.le_of_eq (LawfulGasMeter.gasHeld_start _ _)) =
      .ok (advance { startFrame msg (startState fork msg caller.state) caller.substate.child
        (GasMeter.start msg.gas msg.reservoir : StateGasMeter) with running := false }) := by
    rw [runFrame_of_step_eq_next rfl (step_stopS _ hcode rfl)]
    exact runFrame_of_running_eq_false rfl
  have hmap := processMessage_map_val (fun h => h.2 hv) hpre hran
  rw [← hp, hch] at hmap
  have hc : child.1 = advance { startFrame msg (startState fork msg caller.state)
      caller.substate.child (GasMeter.start msg.gas msg.reservoir : StateGasMeter) with
      running := false } := by
    simp only [Except.map, Except.ok.injEq] at hmap
    rw [hmap]
    rfl
  rw [hc]
  exact ⟨rfl, hst⟩

/-- The calls that `C` sends to an upgraded address holding `STOP_CODE`, which is no precompile,
end under `processRunner` with no error in the caller state. -/
theorem sentVia_process_stopS (hparis : .paris ≤ fork) {bound : Nat}
    {message : Message fork} {S : State.TransactionState}
    (hcode : S.getCode (S.getAccount (upAddr S message)).codeHash = .ok STOP_CODE)
    (hnp : Precompiles.isPrecompile fork (upAddr S message).toU256.toNat = false)
    {caller : Evm fork StateGasMeter} {msg : Message fork} {lt : msg.gas < bound}
    {child : { evm : Evm fork StateGasMeter // GasMeter.gasHeld evm.gas ≤ msg.gas }}
    (hsv : SentVia message S (upAddr S message) (Meter.toNat caller) msg)
    (hch : processRunner fork bound caller msg lt = .ok child) :
    child.1.error = none ∧ child.1.state = caller.state := by
  obtain ⟨c, r, hc, hroute, hsv, _⟩ := sendsVia_of_sentVia hsv
  rw [hcode] at hc
  cases hc
  obtain ⟨-, -, htg, hca, hmc, -, -, hval, -, -⟩ := hsv
  rcases r with _ | ⟨d, c'⟩
  · have hpre : precompileAddress fork msg = none := by
      simp only [precompileAddress, hca, routeAddr, hnp]; rfl
    exact process_stopS hparis caller lt hmc htg hval hpre hch
  · exact absurd hroute.2.1 (by rw [delegatedAddress_stop]; exact fun h => by cases h)

/-- **`processRunner` meets `KeepsInvAtS`.** From Paris, when the upgraded address of `message`
in `S` holds `STOP_CODE` and is no precompile, EthLib's runner over `StateGasMeter`, at any bound,
meets `KeepsInvAtS`. -/
theorem keepsInvAtS_process_stop (hparis : .paris ≤ fork) {bound : Nat}
    {message : Message fork} {S : State.TransactionState}
    (hcode : S.getCode (S.getAccount (upAddr S message)).codeHash = .ok STOP_CODE)
    (hnp : Precompiles.isPrecompile fork (upAddr S message).toU256.toNat = false) :
    KeepsInvAtS (processRunner (Meter := StateGasMeter) fork bound) message S := by
  intro caller msg lt child hsv _ _ hch _ hI
  rw [(sentVia_process_stopS hparis hcode hnp hsv hch).2]
  exact hI

/-- **`processRunner` meets `KeepsAtS`.** From Paris, when the upgraded address of `message` in
`S` holds `STOP_CODE` and is no precompile, EthLib's runner over `StateGasMeter`, at any bound,
meets `KeepsAtS … R` for every reflexive relation `R`. -/
theorem keepsAtS_process_stop (hparis : .paris ≤ fork) {bound : Nat}
    {message : Message fork} {S : State.TransactionState}
    (hcode : S.getCode (S.getAccount (upAddr S message)).codeHash = .ok STOP_CODE)
    (hnp : Precompiles.isPrecompile fork (upAddr S message).toU256.toNat = false)
    {R : State.TransactionState → State.TransactionState → Prop} (hR : ∀ X, R X X) :
    KeepsAtS (processRunner (Meter := StateGasMeter) fork bound) message S
      (upAddr S message) R := by
  intro caller msg lt child hsv _ _ hch _
  rw [(sentVia_process_stopS hparis hcode hnp hsv hch).2]
  exact hR _

/-- **`MIRROR` under `processRunner` over `StateGasMeter`.** From Paris, a message that runs
`MIRROR` at a target, with no value, no precompile and the word `k` at byte 4 of its call data,
run by EthLib's runner over `StateGasMeter` from any caller frame, that ends with no error,
returns the word in slot `mapSlot k 2` of its current target in the caller's state, and ends in
the caller's state with that slot recorded read. -/
theorem process_mirrorS (hparis : .paris ≤ fork) {bound : Nat} (caller : Evm fork StateGasMeter)
    {msg : Message fork} (lt : msg.gas < bound) (hcode : msg.code = MIRROR)
    {ua : Address} (ht : msg.target = some ua) (hv : msg.value = 0)
    (hpre : precompileAddress fork msg = none) {k : U256} (hk : loadWord msg.data 4 32 = k)
    {child : { evm : Evm fork StateGasMeter // GasMeter.gasHeld evm.gas ≤ msg.gas }}
    (hch : processRunner fork bound caller msg lt = .ok child)
    (he : child.1.error = none) :
    child.1.output = wordBytes (storageAt caller.state msg.currentTarget (mapSlot k 2)) ∧
      child.1.state = readSlot caller.state msg.currentTarget (mapSlot k 2) := by
  have hberlin : .berlin ≤ fork := Nat.le_trans (by decide) hparis
  have hst : startState fork msg caller.state = caller.state := by
    simp only [startState, show ¬fork < Fork.paris from Nat.not_lt.mpr hparis, ite_false]
  have hp : processRunner fork bound caller msg lt =
      processMessage fork msg caller.state caller.substate.child := by
    simp only [processRunner, ht]
  generalize hr : runFrame (step fork) (step_decreases fork) msg.gas
      (processRunner fork msg.gas)
      (startFrame msg (startState fork msg caller.state) caller.substate.child
        (GasMeter.start msg.gas msg.reservoir : StateGasMeter))
      (Nat.le_of_eq (LawfulGasMeter.gasHeld_start _ _)) = result
  have hmap := processMessage_map_val (fun h => h.2 hv) hpre hr
  rw [← hp, hch] at hmap
  rcases result with e | s
  · cases hmap
  simp only [Except.map, Except.ok.injEq] at hmap
  have hse : s.error = none := by
    rw [← he, hmap]
    unfold rollbackOnError
    split <;> rfl
  have hc : child.1 = s := by
    rw [hmap]
    unfold rollbackOnError
    simp [hse]
  obtain ⟨G, hE⟩ := Shadow.shadow_ends hberlin hr hse
  have start := Gas.at_addGas (Meter.at_startFrameS hcode (startState fork msg caller.state)
    caller.substate.child (GasMeter.start msg.gas msg.reservoir))
    (Shadow.budget (startFrame msg (startState fork msg caller.state) caller.substate.child
      (GasMeter.start msg.gas msg.reservoir : StateGasMeter)))
  obtain ⟨-, -, ho, -, hs, -⟩ := Complete.ok_exactE (Nat.le_refl _)
    (fun g hg => (mirror_specA hberlin hk rfl hg).toG) start hE hse
  rw [hc]
  rw [hst] at ho hs
  exact ⟨ho, hs⟩

/-- **`HonestBalanceAtS` for `processRunner` with a real code.** From Paris, when the upgraded
address of `message` in `S` holds `MIRROR` and is no precompile, and its slot `balSlot message`
holds in `S` the word that USDT's `balances[a]` holds (`hmirror`), EthLib's runner over
`StateGasMeter`, at any bound, meets `HonestBalanceAtS`. -/
theorem honestBalanceAtS_process_mirror (hparis : .paris ≤ fork) {bound : Nat}
    {message : Message fork} {S : State.TransactionState}
    (hcode : S.getCode (S.getAccount (upAddr S message)).codeHash = .ok MIRROR)
    (hnp : Precompiles.isPrecompile fork (upAddr S message).toU256.toNat = false)
    (hmirror : storageAt S (upAddr S message) (balSlot message) =
      storageAt S message.currentTarget (balSlot message)) :
    HonestBalanceAtS (processRunner (Meter := StateGasMeter) fork bound) message S := by
  intro caller msg lt child hs _ _ hch hmd he
  obtain ⟨c, r, hc, hroute, hsv, hview⟩ := sendsVia_of_sentVia hs
  rw [hcode] at hc
  cases hc
  rcases r with _ | ⟨d, c'⟩
  · obtain ⟨-, hmt, htg, hca, hmc, -, -, hval, -, -⟩ := hsv
    have hpre : precompileAddress fork msg = none := by
      simp only [precompileAddress, hca, routeAddr, hnp]; rfl
    have hk : loadWord msg.data 4 32 = addrArg message.data 0 := by
      rw [hmd]; exact loadWord_append_wordBytes SEL_B _
    obtain ⟨ho, hs⟩ := process_mirrorS hparis caller lt hmc htg hval hpre hk hch he
    have hview' : ReadsAs caller.state S := hview
    rw [ho, hs, resWord_outMemOf (size_memD message) (by rw [size_wordBytes]; omega),
      loadWord_wordBytes_zero, storageAt_readSlot, hmt, storageAt_of_readsAs hview',
      storageAt_of_readsAs hview']
    exact hmirror
  · exact absurd hroute.2.1 (by rw [delegatedAddress_mirror]; exact fun h => by cases h)

end UsdtVerify.Sanity
