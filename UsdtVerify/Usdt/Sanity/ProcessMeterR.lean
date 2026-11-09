import UsdtVerify.Usdt.Sanity.ProcessMeter
import UsdtVerify.Usdt.Invariant.DepMeterR
import UsdtVerify.Usdt.Security.DepMeterR

/-!
# Sanity: EthLib's runner over the EIP-8037 meter meets the runner assumptions at any reservoir (round 44)

Usdt/Sanity/ProcessMeter.lean (round 41) gives the runs. Here the runner assumptions of round 44
hold, stated at any reservoir `r` of the forwarded message (at `r = 0` they are those of round 41). The runner is EthLib's `processRunner` over
`StateGasMeter`.

- `keepsInvAtSR_process_stop`: from Paris, when the upgraded address holds `STOP_CODE` and is no
  precompile, `processRunner` at any bound meets `KeepsInvAtSR` at every reservoir `r`.
- `keepsAtSR_process_stop`: under the same hypotheses it meets `KeepsAtSR … r R` for every `r`
  and every reflexive relation `R`.
- `honestBalanceAtSR_process_mirror`: from Paris, when the upgraded address holds `MIRROR`, is no
  precompile, and its slot `balSlot message` holds in `S` the word of USDT's `balances[a]`,
  `processRunner` at any bound meets `HonestBalanceAtSR` at every reservoir `r`.
-/

namespace UsdtVerify.Sanity

open EthLib.Base (Fork U256 Address)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open Complete Security Invariant Deprecated DeprecatedBalance DeprecatedDestroy DestroySpec

variable {fork : Fork}

/-- **`processRunner` meets `KeepsInvAtSR` at every reservoir.** From Paris, when the upgraded
address of `message` in `S` holds `STOP_CODE` and is no precompile, EthLib's runner over
`StateGasMeter`, at any bound, meets `KeepsInvAtSR … r` for every `r`. -/
theorem keepsInvAtSR_process_stop (hparis : .paris ≤ fork) {bound : Nat}
    {message : Message fork} {S : State.TransactionState}
    (hcode : S.getCode (S.getAccount (upAddr S message)).codeHash = .ok STOP_CODE)
    (hnp : Precompiles.isPrecompile fork (upAddr S message).toU256.toNat = false) (r : Nat) :
    KeepsInvAtSR (processRunner (Meter := StateGasMeter) fork bound) message S r := by
  intro caller msg lt child hsv _ _ hch _ hI
  rw [(sentVia_process_stopS hparis hcode hnp hsv hch).2]
  exact hI

/-- **`processRunner` meets `KeepsAtSR` at every reservoir.** From Paris, when the upgraded
address of `message` in `S` holds `STOP_CODE` and is no precompile, EthLib's runner over
`StateGasMeter`, at any bound, meets `KeepsAtSR … r R` for every `r` and every reflexive relation
`R`. -/
theorem keepsAtSR_process_stop (hparis : .paris ≤ fork) {bound : Nat}
    {message : Message fork} {S : State.TransactionState}
    (hcode : S.getCode (S.getAccount (upAddr S message)).codeHash = .ok STOP_CODE)
    (hnp : Precompiles.isPrecompile fork (upAddr S message).toU256.toNat = false) (r : Nat)
    {R : State.TransactionState → State.TransactionState → Prop} (hR : ∀ X, R X X) :
    KeepsAtSR (processRunner (Meter := StateGasMeter) fork bound) message S
      (upAddr S message) r R := by
  intro caller msg lt child hsv _ _ hch _
  rw [(sentVia_process_stopS hparis hcode hnp hsv hch).2]
  exact hR _

/-- **`HonestBalanceAtSR` for `processRunner` with a real code, at every reservoir.** From Paris,
when the upgraded address of `message` in `S` holds `MIRROR` and is no precompile, and its slot
`balSlot message` holds in `S` the word that USDT's `balances[a]` holds (`hmirror`), EthLib's
runner over `StateGasMeter`, at any bound, meets `HonestBalanceAtSR … r` for every `r`. -/
theorem honestBalanceAtSR_process_mirror (hparis : .paris ≤ fork) {bound : Nat}
    {message : Message fork} {S : State.TransactionState}
    (hcode : S.getCode (S.getAccount (upAddr S message)).codeHash = .ok MIRROR)
    (hnp : Precompiles.isPrecompile fork (upAddr S message).toU256.toNat = false)
    (hmirror : storageAt S (upAddr S message) (balSlot message) =
      storageAt S message.currentTarget (balSlot message)) (r : Nat) :
    HonestBalanceAtSR (processRunner (Meter := StateGasMeter) fork bound) message S
      r := by
  intro caller msg lt child hs _ _ hch hmd he
  obtain ⟨c, rt, hc, hroute, hsv, hview⟩ := sendsVia_of_sentVia hs
  rw [hcode] at hc
  cases hc
  rcases rt with _ | ⟨d, c'⟩
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
