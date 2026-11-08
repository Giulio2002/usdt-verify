import UsdtVerify.Usdt.Sanity.MirrorExact
import UsdtVerify.Usdt.Invariant.Seq
import UsdtVerify.Evm.Sample

/-!
# Sanity: a deprecated state whose upgraded address holds `MIRROR` (round 31)

docs/AUDIT.md, second audit, L4 and I1 (from the reviewer's scratch proofs, restated here). Up to
round 31 every `processRunner` instance took the upgraded code as a hypothesis, and no file built
a deprecated state.

- `keepsInvAt_process_mirror`: from Paris, when the upgraded address holds `MIRROR` and is no
  precompile, `processRunner` meets `KeepsInvAt` (`MIRROR` only reads, so each call it ends with
  no error leaves the storage of the caller state as it was).
- `S1 C H`: a state where `C` and `UA` (address 0x1234) both have the slots `[(10, W)]`, with `W`
  of byte 20 equal to 1 (deprecated) and upgraded address `UA`, and `UA` holds `MIRROR` under the
  code hash `H` (`exists_hash`: some hash is not the empty code hash).
- `balanceOf_mirror_sat`: from Paris and before Glamsterdam, in `S1 C H` with a `balanceOf(a)`
  call from any caller and 1000000 gas, every hypothesis of
  `balanceOf_dep_ok_iff_gas_process_mirror` holds, so its iff holds for `processRunner`.
- `process_step_dep_hyps`: from Paris, for a `destroyBlackFunds(a)` call to `C` in `S1 C H` and
  `processRunner` at any bound, the flag is set, and `KeepsInvAt` and `HonestBalanceAt` (the
  deprecated hypotheses `hkeeps` and `hhonest` of `process_step`) hold together. The slot `MIRROR`
  reads holds the same word as USDT's `balances[a]` because both accounts have the same storage.
-/

namespace UsdtVerify.Sanity

open EthLib.Base (Fork U256 Address toAddressMasked Hash32)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open Complete Deprecated DeprecatedBalance Exact DestroySpec Invariant

variable {fork : Fork}

/-- From Paris, `processRunner` meets `KeepsInvAt` when the upgraded address holds `MIRROR` and is
no precompile. -/
theorem keepsInvAt_process_mirror (hparis : .paris ≤ fork) {bound : Nat}
    {message : Message fork} {S : State.TransactionState}
    (hcode : S.getCode (S.getAccount (upAddr S message)).codeHash = .ok MIRROR)
    (hnp : Precompiles.isPrecompile fork (upAddr S message).toU256.toNat = false) :
    KeepsInvAt (processRunner fork bound) message S := by
  intro caller msg lt child ⟨c, r, hc, hroute, hsv, _⟩ hch he hI
  rw [hcode] at hc
  cases hc
  obtain rfl := route_mirror hroute
  obtain ⟨-, -, htg, hca, hmc, -, -, hval, -, -⟩ := hsv
  have hpre := precompile_none_of (fork := fork) hnp hca
  obtain ⟨-, hs⟩ := process_mirror hparis caller lt hmc htg hval hpre rfl hch he
  rw [hs]
  exact (DepInv.inv_congr (fun n => storageAt_readSlot _ _ _ _ _)).2 hI

/-- Slot 10 of the deprecated state: byte 20 is 1, and the low 160 bits are 0x1234. -/
def W : U256 := BitVec.ofNat 256 (2 ^ 160 + 0x1234)

/-- The upgraded address of the deprecated state. -/
def UA : Address := toAddressMasked (upWord W)

theorem UA_nat : UA.toU256.toNat = 0x1234 := by decide

theorem hnp_UA (fork : Fork) : Precompiles.isPrecompile fork UA.toU256.toNat = false := by
  rw [UA_nat]; unfold Precompiles.isPrecompile; rfl

theorem exists_hash : ∃ H : Hash32, H ≠ State.EMPTY_CODE_HASH := by
  by_cases h : (Vector.replicate 32 (0 : UInt8)) = State.EMPTY_CODE_HASH
  · exact ⟨Vector.replicate 32 1, fun h' => by rw [← h'] at h; exact absurd h (by decide)⟩
  · exact ⟨_, h⟩

/-- `C` and `UA` both have the slots `[(10, W)]`; `UA` holds `MIRROR` with code hash `H`. -/
def S1 (C : Address) (H : Hash32) : State.TransactionState :=
  State.TransactionState.ofBlock
    { preState :=
        { accounts := ((∅ : Std.ExtTreeMap Address State.Account).insert C S_ACCOUNT).insert UA
            ⟨1, 0, H⟩
          storage := ((∅ : State.StorageMap).insert C (slotMap [(10, W)])).insert UA
            (slotMap [(10, W)])
          code := (∅ : Std.ExtTreeMap Hash32 ByteArray).insert H MIRROR }
      accountWrites := ∅
      storageWrites := ∅
      codeWrites := ∅
      storageClears := ∅ }

theorem storageAt_S1 (C : Address) (H : Hash32) (a : Address) (ha : a = C ∨ a = UA) (n : U256) :
    storageAt (S1 C H) a n = ((slotMap [(10, W)])[U256.toBeBytes n]?).getD 0 := by
  rcases ha with rfl | rfl
  · by_cases h : a = UA
    · subst h
      simp [storageAt, S1, State.TransactionState.ofBlock, State.TransactionState.getStorage,
        State.State.getStorage, State.StorageMap.slot]
    · simp [storageAt, S1, State.TransactionState.ofBlock, State.TransactionState.getStorage,
        State.State.getStorage, State.StorageMap.slot, Std.ExtTreeMap.getElem_insert, Ne.symm h]
  · simp [storageAt, S1, State.TransactionState.ofBlock, State.TransactionState.getStorage,
      State.State.getStorage, State.StorageMap.slot]

theorem slot10_S1 (C : Address) (H : Hash32) : storageAt (S1 C H) C 10 = W := by
  rw [storageAt_S1 C H C (.inl rfl)]; simp [slotMap]

theorem up_S1 {M : Message fork} {C : Address} (hC : M.currentTarget = C) (H : Hash32) :
    upAddr (S1 C H) M = UA := by
  show toAddressMasked (upWord (storageAt (S1 C H) M.currentTarget 10)) = UA
  rw [hC, slot10_S1]; rfl

theorem hcode_S1 {M : Message fork} {C : Address} (hC : M.currentTarget = C) (H : Hash32)
    (hH : H ≠ State.EMPTY_CODE_HASH) :
    (S1 C H).getCode ((S1 C H).getAccount (upAddr (S1 C H) M)).codeHash = .ok MIRROR := by
  rw [up_S1 hC]
  simp [S1, State.TransactionState.ofBlock, State.TransactionState.getAccount,
    State.TransactionState.getAccountOptional, State.State.getAccountOptional,
    State.TransactionState.getCode, State.State.getCode, hH]

/-- A `balanceOf(a)` call to `C`. -/
abbrev mB (b : BlockEnvironment fork) (t : TransactionEnvironment fork) (C caller : Address)
    (a : U256) : Message fork :=
  sMsg b t C caller CODE (data1 SEL_B a)

/-- **The hypotheses of `balanceOf_dep_ok_iff_gas_process_mirror` hold together.** From Paris and
before Glamsterdam, in the deprecated state `S1 C H` (`H` not the empty code hash), for a
`balanceOf(a)` call to `C` from any caller with 1000000 gas and any substate, the iff of
`balanceOf_dep_ok_iff_gas_process_mirror` holds for `processRunner`. -/
theorem balanceOf_mirror_sat (hparis : .paris ≤ fork) (hglam : fork < .glamsterdam)
    (b : BlockEnvironment fork) (t : TransactionEnvironment fork) (C caller : Address) (a : U256)
    (ss : Substate) (H : Hash32) (hH : H ≠ State.EMPTY_CODE_HASH) :
    RunsOk fork 1000000 (processRunner fork 1000000)
        (sFrame (mB b t C caller a) (S1 C H) ss 1000000) (Nat.le_refl _) ↔
      ForwardOk (mB b t C caller a) MIRROR ∧
      (mirrorCost (coldIn (accessSlot ss C 10) UA (balSlot (mB b t C caller a))) ≤
          (callGasB fork 1000000 (coldIn ss C 10) (decide (UA ∉ ss.accessedAddresses))
            (callR ss (S1 C H) (mB b t C caller a) none)).subCall ∧
        126 ≤ 1000000 - preCostB fork (coldIn ss C 10) (decide (UA ∉ ss.accessedAddresses)) -
          (callGasB fork 1000000 (coldIn ss C 10) (decide (UA ∉ ss.accessedAddresses))
            (callR ss (S1 C H) (mB b t C caller a) none)).cost +
          ((callGasB fork 1000000 (coldIn ss C 10) (decide (UA ∉ ss.accessedAddresses))
            (callR ss (S1 C H) (mB b t C caller a) none)).subCall -
              mirrorCost (coldIn (accessSlot ss C 10) UA (balSlot (mB b t C caller a))))) := by
  have hberlin : .berlin ≤ fork := Nat.le_trans (by decide) hparis
  have hup := up_S1 (M := mB b t C caller a) (C := C) rfl H
  have h := balanceOf_dep_ok_iff_gas_process_mirror (fork := fork) (message := mB b t C caller a)
    (state := S1 C H) (substate := ss) (gas := 1000000) (bound := 1000000) hparis
    (by show (data1 SEL_B a).size < 2 ^ 256; rw [size_data1 size_SEL_B]; decide)
    (by show selector (data1 SEL_B a) = _; rw [selector_data1 size_SEL_B]; decide)
    (by show byte20 (storageAt (S1 C H) C 10) ≠ 0; rw [slot10_S1]; decide)
    (hcode_S1 (C := C) rfl H hH) (r := none) (fun _ => delegatedAddress_mirror) rfl rfl rfl
    (at_sFrame (mB b t C caller a) rfl _ _ _) (Nat.le_refl _)
    (by rw [hup]; exact hnp_UA fork)
    (by
      simp only [preCostB, callR, routeCost, extCost_of_lt hberlin hglam]
      generalize coldIn ss (mB b t C caller a).currentTarget 10 = c1
      generalize (decide (upAddr (S1 C H) (mB b t C caller a) ∉ ss.accessedAddresses)) = c2
      cases c1 <;> cases c2 <;> decide)
  rw [hup] at h
  exact h

/-- A `destroyBlackFunds(a)` call to `C`. -/
abbrev mD (b : BlockEnvironment fork) (t : TransactionEnvironment fork) (C caller : Address)
    (a : U256) : Message fork :=
  sMsg b t C caller CODE (data1 ⟨#[0xf3, 0xbd, 0xc2, 0x28]⟩ a)

/-- **`KeepsInvAt` and `HonestBalanceAt` together, in a deprecated state.** From Paris, for a
`destroyBlackFunds(a)` call to `C` in `S1 C H` (`H` not the empty code hash) and `processRunner`
at any bound: the flag is set (byte 20 of slot 10 is not 0), and `processRunner` meets
`KeepsInvAt` and `HonestBalanceAt`, the deprecated hypotheses `hkeeps` and `hhonest` of
`process_step`. -/
theorem process_step_dep_hyps (hparis : .paris ≤ fork) (b : BlockEnvironment fork)
    (t : TransactionEnvironment fork) (C caller : Address) (a : U256) (H : Hash32)
    (hH : H ≠ State.EMPTY_CODE_HASH) (g : Nat) :
    byte20 (storageAt (S1 C H) (mD b t C caller a).currentTarget 10) ≠ 0 ∧
    KeepsInvAt (processRunner fork g) (mD b t C caller a) (S1 C H) ∧
    HonestBalanceAt (processRunner fork g) (mD b t C caller a) (S1 C H) := by
  have hc := hcode_S1 (M := mD b t C caller a) (C := C) rfl H hH
  have hnp : Precompiles.isPrecompile fork (upAddr (S1 C H) (mD b t C caller a)).toU256.toNat
      = false := by rw [up_S1 (C := C) rfl]; exact hnp_UA fork
  refine ⟨?_, keepsInvAt_process_mirror hparis hc hnp,
    honestBalanceAt_process_mirror hparis hc hnp ?_⟩
  · show byte20 (storageAt (S1 C H) C 10) ≠ 0
    rw [slot10_S1]; decide
  · show storageAt (S1 C H) (upAddr (S1 C H) (mD b t C caller a)) (balSlot (mD b t C caller a)) =
      storageAt (S1 C H) C (balSlot (mD b t C caller a))
    rw [up_S1 (C := C) rfl, storageAt_S1 C H UA (.inr rfl), storageAt_S1 C H C (.inl rfl)]

end UsdtVerify.Sanity
