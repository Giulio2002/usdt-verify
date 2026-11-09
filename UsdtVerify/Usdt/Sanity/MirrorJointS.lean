import UsdtVerify.Usdt.Sanity.MirrorStateS
import UsdtVerify.Usdt.Sanity.ProcessMeterR
import UsdtVerify.Usdt.Sanity.ProcessExact

/-!
# Sanity: both runner assumptions of deprecated destroyBlackFunds over the EIP-8037 meter (round 51)

The deprecated theorems over `StateGasMeter` at any reservoir (`inv_call_depR`, `process_stepDR`,
`process_stepDR_inv`) take `KeepsInvAtSR` and `HonestBalanceAtSR` for the same runner, message and
state. Usdt/Sanity/ProcessMeterR.lean proves the first only with `STOP_CODE` at the upgraded
address and the second only with `MIRROR` there. This file proves the first with `MIRROR` too, so
both hold together, and applies `process_stepDR_inv` end to end in the concrete state `S2`.

- `keepsInvAtSR_process_mirror`: from Paris, when the upgraded address holds `MIRROR` and is no
  precompile, `processRunner` over `StateGasMeter` at any bound meets `KeepsInvAtSR` at every
  reservoir `r`.
- `joint_S2_R`: from Paris, in `S2 C H a` (`H` not the empty code hash), for the message `mDO`,
  `processRunner` meets `KeepsInvAtSR` and `HonestBalanceAtSR` at every reservoir `r`.
- `destroy_mirror_stepDR`: from Paris, in `S2 C H a` with `C` no precompile, for the message
  `mDOG` with any gas field `G` and reservoir field `R`, from any substate and any starting meter
  with at least 1000000 and below 2^255 execution gas left, EthLib's `processMessage` over
  `StateGasMeter` ends with no error, and `Inv` holds in its end state. It assumes the keccak
  hypothesis `SepOn` of the call's keys and `StrForm` of slots 7 and 8 of `C` in `S2`.
-/

namespace UsdtVerify.Sanity

open EthLib.Base (Fork U256 Address Hash32)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open Complete Security Invariant Deprecated DeprecatedBalance DeprecatedDestroy DestroySpec

variable {fork : Fork}

/-- **`processRunner` meets `KeepsInvAtSR` with `MIRROR`.** From Paris, when the upgraded address
of `message` in `S` holds `MIRROR` and is no precompile, EthLib's runner over `StateGasMeter`, at
any bound, meets `KeepsInvAtSR` at every reservoir `r`. -/
theorem keepsInvAtSR_process_mirror (hparis : .paris ≤ fork) {bound : Nat}
    {message : Message fork} {S : State.TransactionState}
    (hcode : S.getCode (S.getAccount (upAddr S message)).codeHash = .ok MIRROR)
    (hnp : Precompiles.isPrecompile fork (upAddr S message).toU256.toNat = false) (r : Nat) :
    KeepsInvAtSR (processRunner (Meter := StateGasMeter) fork bound) message S r := by
  intro caller msg lt child hs _ _ hch he hI
  obtain ⟨c, rt, hc, hroute, hsv, -⟩ := sendsVia_of_sentVia hs
  rw [hcode] at hc
  cases hc
  rcases rt with _ | ⟨d, c'⟩
  · obtain ⟨-, -, htg, hca, hmc, -, -, hval, -, -⟩ := hsv
    have hpre : precompileAddress fork msg = none := by
      simp only [precompileAddress, hca, routeAddr, hnp]; rfl
    obtain ⟨-, hst⟩ := process_mirrorS hparis caller lt hmc htg hval hpre rfl hch he
    rw [hst]
    exact (DepInv.inv_congr (fun n => storageAt_readSlot _ _ _ _ _)).2 hI
  · exact absurd hroute.2.1 (by rw [delegatedAddress_mirror]; exact fun h => by cases h)

/-- **Both runner assumptions in `S2`.** From Paris, in `S2 C H a` (`H` not the empty code hash),
for the deprecated destroyBlackFunds message `mDO`, EthLib's runner over `StateGasMeter` at any
bound meets `KeepsInvAtSR` and `HonestBalanceAtSR` at every reservoir `r`. -/
theorem joint_S2_R (hparis : .paris ≤ fork) (b : BlockEnvironment fork)
    (t : TransactionEnvironment fork) (C : Address) (a : U256) (H : Hash32)
    (hH : H ≠ State.EMPTY_CODE_HASH) {bound : Nat} (r : Nat) :
    KeepsInvAtSR (processRunner (Meter := StateGasMeter) fork bound) (mDO b t C a) (S2 C H a) r ∧
      HonestBalanceAtSR (processRunner (Meter := StateGasMeter) fork bound) (mDO b t C a)
        (S2 C H a) r := by
  obtain ⟨-, -, -, -, hup0, -, -, -, -⟩ := process_step_dep_hyps2 hparis b t C a H hH 0
  have hcodeU := hcode_SM (M := mDO b t C a) (C := C) (kvs := KD a) H hH hup0
  have hnp : Precompiles.isPrecompile fork (upAddr (S2 C H a) (mDO b t C a)).toU256.toNat =
      false := by
    rw [hup0]; exact hnp_UA fork
  refine ⟨keepsInvAtSR_process_mirror hparis hcodeU hnp r,
    honestBalanceAtSR_process_mirror hparis hcodeU hnp ?_ r⟩
  rw [hup0, show (mDO b t C a).currentTarget = C from rfl, storageAt_S2 C H a UA (.inr rfl),
    storageAt_S2 C H a C (.inl rfl)]

/-- **`process_stepDR_inv` applied in `S2`.** From Paris, in `S2 C H a` (`H` not the empty code
hash) with `C` no precompile, for the deprecated destroyBlackFunds message `mDOG` with any gas
field `G` and reservoir field `R`, from any substate and any starting meter with at least 1000000
and below 2^255 execution gas left (its held gas at most `G`): EthLib's `processMessage` over
`StateGasMeter` ends with a frame with no error, and `Inv C` holds in its state. Assumes `SepOn`
of the call's keys and `StrForm` of slots 7 and 8 of `C` in `S2`. -/
theorem destroy_mirror_stepDR (hparis : .paris ≤ fork)
    (b : BlockEnvironment fork) (t : TransactionEnvironment fork) (C : Address) (a : U256)
    (ss : Substate) (H : Hash32) (hH : H ≠ State.EMPTY_CODE_HASH)
    (hnp : Precompiles.isPrecompile fork C.toU256.toNat = false) (G R : Nat)
    (meter : StateGasMeter) (hg : 1000000 ≤ meter.gasLeft) (hg' : meter.gasLeft < 2 ^ 255)
    (held : GasMeter.gasHeld meter ≤ (mDOG b t C a G R).gas)
    (K : SepOn (callKeys (mDOG b t C a G R) (S2 C H a)))
    (h7 : StrForm (storageAt (S2 C H a) C 7)) (h8 : StrForm (storageAt (S2 C H a) C 8)) :
    ∃ ended, processMessage fork (mDOG b t C a G R) (S2 C H a) ss meter held = .ok ended ∧
      ended.1.error = none ∧ Invariant.Inv C ended.1.state := by
  obtain ⟨ended, hproc, he⟩ :=
    destroy_mirror_processS hparis b t C a ss H hH hnp G R meter hg hg' held
  have hmem : kD a ∈ callKeys (mDOG b t C a G R) (S2 C H a) := by
    have e : addrArg (mDOG b t C a G R).data 0 = kD a := addr_mDO b t C a
    unfold callKeys
    rw [e]
    exact List.mem_cons_of_mem _ List.mem_cons_self
  have hI : Invariant.Inv C (S2 C H a) := inv_S2 C H a (K.mono (by
    intro x hx
    rw [List.mem_singleton] at hx
    rw [hx]; exact hmem))
  have hsz : (mDOG b t C a G R).data.size < 2 ^ 256 := by
    show (data1 SEL_D a).size < 2 ^ 256; rw [size_data1 size_SEL_D]; decide
  obtain ⟨-, -, -, -, hup0, -, -, -, -⟩ := process_step_dep_hyps2 hparis b t C a H hH 0
  have hup : upAddr (S2 C H a) (mDOG b t C a G R) = UA := hup0
  have hcodeU := hcode_SM (M := mDOG b t C a G R) (C := C) (kvs := KD a) H hH hup
  have hnpU : Precompiles.isPrecompile fork
      (upAddr (S2 C H a) (mDOG b t C a G R)).toU256.toNat = false := by
    rw [hup]; exact hnp_UA fork
  have hdep : byte20 (storageAt (S2 C H a) (mDOG b t C a G R).currentTarget 10) ≠ 0 := by
    show byte20 (storageAt (S2 C H a) C 10) ≠ 0
    rw [slot10_S2]; decide
  have hm : storageAt (S2 C H a) (upAddr (S2 C H a) (mDOG b t C a G R))
      (balSlot (mDOG b t C a G R)) =
      storageAt (S2 C H a) (mDOG b t C a G R).currentTarget (balSlot (mDOG b t C a G R)) := by
    rw [hup, show (mDOG b t C a G R).currentTarget = C from rfl, storageAt_S2 C H a UA (.inr rfl),
      storageAt_S2 C H a C (.inl rfl)]
  have hI' := process_stepDR_inv (message := mDOG b t C a G R) hparis rfl
    (precompile_none_of (fork := fork) hnp rfl) hsz K h7 h8 hdep
    (keepsInvAtSR_process_mirror hparis hcodeU hnpU meter.reservoir)
    (fun _ => honestBalanceAtSR_process_mirror hparis hcodeU hnpU hm meter.reservoir) hproc hI
  exact ⟨ended, hproc, he, hI'⟩

end UsdtVerify.Sanity
