import UsdtVerify.Usdt.Sanity.MirrorExact
import UsdtVerify.Usdt.Invariant.Seq
import UsdtVerify.Evm.Sample
import UsdtVerify.Usdt.Sanity.Calls

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
  In `S1` the owner is the zero address and `isBlackListed[a]` is 0, so no destroyBlackFunds
  call there reaches the CALL (docs/AUDIT.md, third audit, T3).

Round 33 (third audit, T3): a state where deprecated destroyBlackFunds reaches the CALL.
- `SM C H kvs`: `C` and `UA` both have the slots `kvs`, `UA` holds `MIRROR`. `S2 C H a` is
  `SM C H (KD a)`: slot 10 deprecated with upgraded address `UA`, the owner `CALLER_A` in slot 0
  (not paused), `isBlackListed[a]` 1, `balances[a]` 1 and (since round 45) `_totalSupply` 1.
  Whatever the keccak slots collide with, `a` is blacklisted and `balances[a]` is not 0
  (`listed_S2`, `bal_S2`).
- `process_step_dep_hyps2`: from Paris, for `destroyBlackFunds(a)` from `CALLER_A`, the flag is
  set, the caller is the owner, `a` is blacklisted, `balances[a]` is not 0, `MIRROR`'s slot holds
  the same word, and `processRunner` meets `KeepsInvAt` and `HonestBalanceAt`.
- `destroy_mirror_runs`: from Paris and before Glamsterdam, with 1000000 gas and any substate,
  that call ends with no error under `processRunner` (`RunsOk`).
- `inv_S2` (round 45): `Inv C (S2 C H a)` under `SepOn [kD a]`, the keccak separation of the one
  key of `S2`. `destroy_mirror_inv`: from Paris and before Glamsterdam, under `SepOn` of the keys
  of that call, `Inv` holds in `S2`, the call ends with no error (`destroy_mirror_runs`), and every
  run of it that ends with no error, at any gas bound, ends in a state where `Inv` holds. The
  separation itself is assumed, not proved.

Usdt/Sanity/MirrorStateS.lean (round 44) runs the same call over the EIP-8037 meter under
`processRunner` (`destroy_mirror_runsS`).
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
  intro caller msg lt child hch hs he hI
  obtain ⟨c, r, hc, hroute, hsv, _⟩ := sendsVia_of_sentVia hs
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
    RunsOk 1000000 (processRunner fork 1000000)
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

/-! ## A deprecated state where destroyBlackFunds reaches the CALL (round 33, third audit T3) -/

open Owner BlackList DeprecatedDestroy

/-- `C` and `UA` both have the slots of `kvs`; `UA` holds `MIRROR` with code hash `H`. -/
def SM (C : Address) (H : Hash32) (kvs : List (U256 × U256)) : State.TransactionState :=
  State.TransactionState.ofBlock
    { preState :=
        { accounts := ((∅ : Std.ExtTreeMap Address State.Account).insert C S_ACCOUNT).insert UA
            ⟨1, 0, H⟩
          storage := ((∅ : State.StorageMap).insert C (slotMap kvs)).insert UA (slotMap kvs)
          code := (∅ : Std.ExtTreeMap Hash32 ByteArray).insert H MIRROR }
      accountWrites := ∅
      storageWrites := ∅
      codeWrites := ∅
      storageClears := ∅ }

theorem storageAt_SM (C : Address) (H : Hash32) (kvs : List (U256 × U256)) (a : Address)
    (ha : a = C ∨ a = UA) (n : U256) :
    storageAt (SM C H kvs) a n = ((slotMap kvs)[U256.toBeBytes n]?).getD 0 := by
  rcases ha with rfl | rfl
  · by_cases h : a = UA
    · subst h
      simp [storageAt, SM, State.TransactionState.ofBlock, State.TransactionState.getStorage,
        State.State.getStorage, State.StorageMap.slot]
    · simp [storageAt, SM, State.TransactionState.ofBlock, State.TransactionState.getStorage,
        State.State.getStorage, State.StorageMap.slot, Std.ExtTreeMap.getElem_insert, Ne.symm h]
  · simp [storageAt, SM, State.TransactionState.ofBlock, State.TransactionState.getStorage,
      State.State.getStorage, State.StorageMap.slot]

theorem slotMap_cons (k v : U256) (kvs : List (U256 × U256)) (n : U256) :
    ((slotMap ((k, v) :: kvs))[U256.toBeBytes n]?).getD 0 =
      if k = n then v else ((slotMap kvs)[U256.toBeBytes n]?).getD 0 := by
  simp only [slotMap, Std.ExtTreeMap.getElem?_insert]
  by_cases h : k = n
  · subst h; simp
  · have h' : ¬ U256.toBeBytes k = U256.toBeBytes n := fun e => h (toBeBytes_inj e)
    simp [h, h']

theorem hasAccount_SM (C : Address) (H : Hash32) (kvs : List (U256 × U256)) :
    hasAccount (SM C H kvs) C := by
  by_cases h : C = UA
  · subst h
    simp [hasAccount, SM, State.TransactionState.ofBlock,
      State.TransactionState.getAccountOptional, State.State.getAccountOptional]
  · simp [hasAccount, SM, State.TransactionState.ofBlock,
      State.TransactionState.getAccountOptional, State.State.getAccountOptional, Ne.symm h]

theorem hcode_SM {M : Message fork} {C : Address} {kvs : List (U256 × U256)} (H : Hash32)
    (hH : H ≠ State.EMPTY_CODE_HASH) (hup : upAddr (SM C H kvs) M = UA) :
    (SM C H kvs).getCode ((SM C H kvs).getAccount (upAddr (SM C H kvs) M)).codeHash =
      .ok MIRROR := by
  rw [hup]
  simp [SM, State.TransactionState.ofBlock, State.TransactionState.getAccount,
    State.TransactionState.getAccountOptional, State.State.getAccountOptional,
    State.TransactionState.getCode, State.State.getCode, hH]

/-- The key of `destroyBlackFunds(a)`: `a` masked to an address. -/
abbrev kD (a : U256) : U256 := bitwiseAnd ADDR_MASK a

/-- The slots of `S2`: slot 10 deprecated with upgraded address `UA`, the owner `CALLER_A` in
slot 0 (not paused), `isBlackListed[a]` 1, `balances[a]` 1 and (since round 45) `_totalSupply`
(slot 1) 1. An earlier pair wins. -/
abbrev KD (a : U256) : List (U256 × U256) :=
  [(10, W), (0, W_A), (listSlot (kD a), 1), (mapSlot (kD a) 2, 1), (1, 1)]

/-- The deprecated state of T3: `C` and `UA` both have the slots `KD a`, `UA` holds `MIRROR`. -/
abbrev S2 (C : Address) (H : Hash32) (a : U256) : State.TransactionState := SM C H (KD a)

/-- `destroyBlackFunds(a)` from the owner `CALLER_A` to `C`. -/
abbrev mDO (b : BlockEnvironment fork) (t : TransactionEnvironment fork) (C : Address)
    (a : U256) : Message fork :=
  mO b t C SEL_D a

theorem addr_mDO (b : BlockEnvironment fork) (t : TransactionEnvironment fork) (C : Address)
    (a : U256) : addrArg (mDO b t C a).data 0 = kD a := by
  show bitwiseAnd ADDR_MASK (wordArg (data1 SEL_D a) 0) = _
  rw [wordArg_data1 size_SEL_D]

theorem storageAt_S2 (C : Address) (H : Hash32) (a : U256) (x : Address) (hx : x = C ∨ x = UA)
    (n : U256) :
    storageAt (S2 C H a) x n =
      if (10 : U256) = n then W else if (0 : U256) = n then W_A else
        if listSlot (kD a) = n then 1 else if mapSlot (kD a) 2 = n then 1 else
          if (1 : U256) = n then 1 else 0 := by
  rw [storageAt_SM C H _ x hx, slotMap_cons, slotMap_cons, slotMap_cons, slotMap_cons,
    slotMap_cons]
  simp [slotMap]

theorem slot10_S2 (C : Address) (H : Hash32) (a : U256) : storageAt (S2 C H a) C 10 = W := by
  rw [storageAt_S2 C H a C (.inl rfl)]; simp

theorem up_S2 {M : Message fork} {C : Address} (hC : M.currentTarget = C) (H : Hash32)
    (a : U256) : upAddr (S2 C H a) M = UA := by
  show toAddressMasked (upWord (storageAt (S2 C H a) M.currentTarget 10)) = UA
  rw [hC, slot10_S2]; rfl

/-- In `S2`, the caller `CALLER_A` is the owner. -/
theorem isOwner_S2 (b : BlockEnvironment fork) (t : TransactionEnvironment fork) (C : Address)
    (H : Hash32) (a : U256) : IsOwner (S2 C H a) (mDO b t C a) := by
  show callerWord (mO b t C SEL_D a) = ownerOf (S2 C H a) C
  rw [callerWord_mO, ownerOf, storageAt_S2 C H a C (.inl rfl)]
  simp only [show ¬ (10 : U256) = 0 by decide, ite_false, ite_true]
  exact mask_W_A.symm

/-- In `S2`, `a` is blacklisted (every collision of the keccak slots gives a nonzero low byte). -/
theorem listed_S2 (C : Address) (H : Hash32) (a : U256) :
    (storageAt (S2 C H a) C (listSlot (kD a))).toNat % 256 ≠ 0 := by
  rw [storageAt_S2 C H a C (.inl rfl)]
  split
  · rw [W]; decide
  · split
    · rw [W_A]; decide
    · simp

/-- In `S2`, `balances[a]` is not 0, at `C` and at `UA`. -/
theorem bal_S2 (C : Address) (H : Hash32) (a : U256) (x : Address) (hx : x = C ∨ x = UA) :
    storageAt (S2 C H a) x (mapSlot (kD a) 2) ≠ 0 := by
  rw [storageAt_S2 C H a x hx]
  split
  · rw [W]; decide
  · split
    · rw [W_A]; decide
    · split
      · decide
      · simp

/-- The sum over the first `n` numbers of a function that is 0 but at `k`, where it is 1. -/
theorem sumTo_indicator (k : Nat) : ∀ n, sumTo (fun i => if i = k then (1 : Int) else 0) n =
    if k < n then 1 else 0
  | 0 => by simp [sumTo]
  | n + 1 => by
    rw [sumTo, sumTo_indicator k n]
    by_cases h1 : k < n
    · have h2 : k < n + 1 := by omega
      have h3 : n ≠ k := by omega
      simp [h1, h2, h3]
    · by_cases h4 : k = n
      · subst h4; simp
      · have h5 : ¬ k < n + 1 := by omega
        have h3 : n ≠ k := fun e => h4 e.symm
        simp [h1, h5, h3]

/-- **`Inv` in `S2` (round 45).** Under the keccak separation `SepOn [kD a]` of the one key of
`S2` (the fixed slots 0..10 are no balance slot; the balance slot of `kD a` is that of no other
address word; the slot of `isBlackListed[kD a]` is no balance slot and not slot 1; the slot of
`allowed[kD a][kD a]` is no balance slot and no fixed slot), the sum of the
balances of `C` in `S2 C H a` is 1 (`balances[kD a]`), which is `_totalSupply`. -/
theorem inv_S2 (C : Address) (H : Hash32) (a : U256) (hsep : SepOn [kD a]) :
    Invariant.Inv C (S2 C H a) := by
  have hk : (kD a).toNat < 2 ^ 160 := mask_lt a
  have hmk : TransferOk.mkey (kD a) = kD a := by simp only [TransferOk.mkey, kD, mask_mask]
  have hU := hsep.uniq (kD a) (by simp) hk
  obtain ⟨hLnb, hL1⟩ := hsep.list (kD a) (by simp)
  have hl : listSlot (kD a) = mapSlot (kD a) 6 := by simp only [listSlot, hmk]
  have hb1 := bal_ne_one hsep.fixed hk
  -- the balances
  have hbal : ∀ i, i < 2 ^ 160 → bal C (S2 C H a) i =
      if i = (kD a).toNat then (1 : Int) else 0 := by
    intro i hi
    have hx : (BitVec.ofNat 256 i).toNat < 2 ^ 160 := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hi
    have h10 : (10 : U256) ≠ mapSlot (BitVec.ofNat 256 i) 2 :=
      nb_fixed hsep.fixed (n := 10) (by decide) _ hx
    have h0 : (0 : U256) ≠ mapSlot (BitVec.ofNat 256 i) 2 :=
      nb_fixed hsep.fixed (n := 0) (by decide) _ hx
    have hL : listSlot (kD a) ≠ mapSlot (BitVec.ofNat 256 i) 2 := by
      rw [hl]; exact hLnb _ hx
    have h1 : (1 : U256) ≠ mapSlot (BitVec.ofNat 256 i) 2 :=
      fun e => bal_ne_one hsep.fixed hx e.symm
    simp only [bal]
    rw [storageAt_S2 C H a C (.inl rfl)]
    simp only [h10, h0, hL, ↓reduceIte]
    by_cases hi' : i = (kD a).toNat
    · subst hi'
      simp only [ofNat_toNat, ↓reduceIte]; rfl
    · have hne : mapSlot (kD a) 2 ≠ mapSlot (BitVec.ofNat 256 i) 2 := by
        intro e
        have := hU _ hx e.symm
        apply hi'
        rw [← this, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      simp only [hne, h1, hi', ↓reduceIte]; rfl
  -- the total
  have htot : tot C (S2 C H a) = 1 := by
    simp only [tot]
    have hL' : listSlot (kD a) ≠ 1 := fun e => hL1 (hl ▸ e)
    rw [storageAt_S2 C H a C (.inl rfl)]
    simp only [show (10 : U256) ≠ 1 by decide, show (0 : U256) ≠ 1 by decide, hL', hb1,
      ↓reduceIte]
    rfl
  unfold Invariant.Inv sumBal
  rw [sumTo_congr _ hbal, sumTo_indicator, htot]
  simp [hk]

/-- **A deprecated destroyBlackFunds that reaches the forward, with `KeepsInvAt` and
`HonestBalanceAt` (third audit, T3).** From Paris, for `destroyBlackFunds(a)` from the owner
`CALLER_A` to `C` in `S2 C H a` (`H` not the empty code hash) and `processRunner` at any bound:
the flag is set, the caller is the owner, `a` is blacklisted, `balances[a]` is not 0 at `C`,
the upgraded address `UA` holds `MIRROR` and its slot `balances[a]` is that of `C`, and
`processRunner` meets `KeepsInvAt` and `HonestBalanceAt`. -/
theorem process_step_dep_hyps2 (hparis : .paris ≤ fork) (b : BlockEnvironment fork)
    (t : TransactionEnvironment fork) (C : Address) (a : U256) (H : Hash32)
    (hH : H ≠ State.EMPTY_CODE_HASH) (g : Nat) :
    byte20 (storageAt (S2 C H a) (mDO b t C a).currentTarget 10) ≠ 0 ∧
    IsOwner (S2 C H a) (mDO b t C a) ∧
    (storageAt (S2 C H a) C (listSlot (addrArg (mDO b t C a).data 0))).toNat % 256 ≠ 0 ∧
    storageAt (S2 C H a) C (balSlot (mDO b t C a)) ≠ 0 ∧
    upAddr (S2 C H a) (mDO b t C a) = UA ∧
    (S2 C H a).getCode ((S2 C H a).getAccount UA).codeHash = .ok MIRROR ∧
    storageAt (S2 C H a) UA (balSlot (mDO b t C a)) = storageAt (S2 C H a) C (balSlot (mDO b t C a)) ∧
    KeepsInvAt (processRunner fork g) (mDO b t C a) (S2 C H a) ∧
    HonestBalanceAt (processRunner fork g) (mDO b t C a) (S2 C H a) := by
  have hup := up_S2 (M := mDO b t C a) (C := C) rfl H a
  have hc := hcode_SM (M := mDO b t C a) (C := C) (kvs := KD a) H hH hup
  have hnp : Precompiles.isPrecompile fork (upAddr (S2 C H a) (mDO b t C a)).toU256.toNat
      = false := by rw [hup]; exact hnp_UA fork
  have hbs : balSlot (mDO b t C a) = mapSlot (kD a) 2 := by
    show mapSlot (addrArg (mDO b t C a).data 0) 2 = _; rw [addr_mDO]
  have hm : storageAt (S2 C H a) UA (balSlot (mDO b t C a)) =
      storageAt (S2 C H a) C (balSlot (mDO b t C a)) := by
    rw [storageAt_S2 C H a UA (.inr rfl), storageAt_S2 C H a C (.inl rfl)]
  refine ⟨?_, isOwner_S2 b t C H a, by rw [addr_mDO]; exact listed_S2 C H a,
    by rw [hbs]; exact bal_S2 C H a C (.inl rfl), hup, by rw [← hup]; exact hc, hm,
    keepsInvAt_process_mirror hparis hc hnp, honestBalanceAt_process_mirror hparis hc hnp ?_⟩
  · show byte20 (storageAt (S2 C H a) C 10) ≠ 0
    rw [slot10_S2]; decide
  · rw [hup]; exact hm

theorem preCostD_le (hberlin : .berlin ≤ fork) (hglam : fork < .glamsterdam) (c0 cL c10 cU : Bool) :
    preCostD fork c0 cL c10 cU ≤ 10400 := by
  simp only [preCostD, extCost_of_lt hberlin hglam]
  cases c0 <;> cases cL <;> cases c10 <;> cases cU <;> decide

/-- With 1000000 gas, before Glamsterdam, the CALL of deprecated destroyBlackFunds gives
`MIRROR` its gas, and the gas after it covers the tail (`TAIL_MAX`), at every coldness. -/
theorem destroy_gas_1M (hberlin : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    (c0 cL c10 cU cM : Bool) :
    mirrorCost cM ≤ (callGasD fork 1000000 c0 cL c10 cU 0).subCall ∧
    TAIL_MAX fork ≤ 1000000 - preCostD fork c0 cL c10 cU -
      (callGasD fork 1000000 c0 cL c10 cU 0).cost +
      ((callGasD fork 1000000 c0 cL c10 cU 0).subCall - mirrorCost cM) := by
  have htw : Fork.tangerineWhistle ≤ fork := Nat.le_trans (by decide) hberlin
  rw [TAIL_MAX_of_lt hglam]
  simp only [callGasD, askedOfD, preCostD, messageCallGas, extCost_of_lt hberlin hglam, ge_iff_le,
    htw, true_and]
  cases c0 <;> cases cL <;> cases c10 <;> cases cU <;> cases cM <;> decide

/-- **A successful deprecated destroyBlackFunds through `MIRROR` (third audit, T3).** From Paris
and before Glamsterdam, in `S2 C H a` (`H` not the empty code hash), `destroyBlackFunds(a)` from
the owner `CALLER_A` to `C` with 1000000 gas and any substate, under `processRunner`: the loop of
the interpreter ends with no error. The run passes the checks, forwards `balanceOf(a)` to `UA`,
and `MIRROR` answers. -/
theorem destroy_mirror_runs (hparis : .paris ≤ fork) (hglam : fork < .glamsterdam)
    (b : BlockEnvironment fork) (t : TransactionEnvironment fork) (C : Address) (a : U256)
    (ss : Substate) (H : Hash32) (hH : H ≠ State.EMPTY_CODE_HASH) :
    RunsOk 1000000 (processRunner fork 1000000)
      (sFrame (mDO b t C a) (S2 C H a) ss 1000000) (Nat.le_refl _) := by
  have hberlin : .berlin ≤ fork := Nat.le_trans (by decide) hparis
  obtain ⟨hdep, hown, hlist, -, hup, -, hm, -, -⟩ :=
    process_step_dep_hyps2 hparis b t C a H hH 0
  have hc := hcode_SM (M := mDO b t C a) (C := C) (kvs := KD a) H hH hup
  have hR : ∀ A, routeCost fork A (none : Route) = 0 := fun _ => rfl
  have h := destroyBlackFunds_dep_ok_iff_gas_process_mirror (fork := fork)
    (message := mDO b t C a) (state := S2 C H a) (substate := ss) (gas := 1000000)
    (bound := 1000000) hparis
    (by show (data1 SEL_D a).size < 2 ^ 256; rw [size_data1 size_SEL_D]; decide)
    (by show selector (data1 SEL_D a) = _; rw [selector_data1 size_SEL_D]; decide)
    hdep hc (r := none) (fun _ => delegatedAddress_mirror) rfl rfl rfl rfl
    (at_sFrame (mDO b t C a) rfl _ _ _) (Nat.le_refl _)
    (by rw [hup]; exact hnp_UA fork)
    (by simp only [callRD, hR]; have := preCostD_le hberlin hglam
          (coldIn ss (mDO b t C a).currentTarget 0)
          (coldIn (accessSlot ss (mDO b t C a).currentTarget 0) (mDO b t C a).currentTarget
            (listSlot (addrArg (mDO b t C a).data 0)))
          (coldIn (preSub ss (mDO b t C a)) (mDO b t C a).currentTarget 10)
          (decide (upAddr (S2 C H a) (mDO b t C a) ∉ ss.accessedAddresses))
        omega)
    (by rw [hup]; exact hm)
  simp only [callRD, hR] at h
  have hg := destroy_gas_1M hberlin hglam (coldIn ss (mDO b t C a).currentTarget 0)
    (coldIn (accessSlot ss (mDO b t C a).currentTarget 0) (mDO b t C a).currentTarget
      (listSlot (addrArg (mDO b t C a).data 0)))
    (coldIn (preSub ss (mDO b t C a)) (mDO b t C a).currentTarget 10)
    (decide (upAddr (S2 C H a) (mDO b t C a) ∉ ss.accessedAddresses))
    (coldIn (atCallSub (callSubD ss (S2 C H a) (mDO b t C a)) (upAddr (S2 C H a) (mDO b t C a))
      none) (upAddr (S2 C H a) (mDO b t C a)) (balSlot (mDO b t C a)))
  refine h.mpr ⟨⟨⟨⟨?_, rfl⟩, by rw [size_MIRROR]; decide, show 0 + 1 ≤ STACK_DEPTH_LIMIT by decide⟩, hown, hlist, rfl⟩, hg.1,
    ?_, Nat.le_trans (tail_le_max hberlin _ _ _ _ _ _) hg.2⟩
  · show 4 ≤ (data1 SEL_D a).size
    rw [size_data1 size_SEL_D]; decide
  · have h0 : hasAccount (readSlot (preState (S2 C H a) (mDO b t C a)) C 10) C :=
      hasAccount_readSlot (hasAccount_readSlot (hasAccount_readSlot (hasAccount_SM C H _)))
    simp only [atCallState, callStateD, routeState, hasAccount,
      State.TransactionState.getAccountOptional_recordAccountRead]
    exact h0

/-- **A deprecated run in `S2` that keeps `Inv` (round 45).** From Paris and before Glamsterdam,
in `S2 C H a` (`H` not the empty code hash), under the keccak separation `SepOn` of the keys of
`destroyBlackFunds(a)` from `CALLER_A` to `C`: `Inv` holds in `S2`, the call with 1000000 gas and
any substate ends with no error under `processRunner`, and every run of it that ends with no
error, at any gas bound, ends in a state where `Inv` holds (`inv_dep_destroy`, with
`KeepsInvAt` and `HonestBalanceAt` from `process_step_dep_hyps2`). -/
theorem destroy_mirror_inv (hparis : .paris ≤ fork) (hglam : fork < .glamsterdam)
    (b : BlockEnvironment fork) (t : TransactionEnvironment fork) (C : Address) (a : U256)
    (ss : Substate) (H : Hash32) (hH : H ≠ State.EMPTY_CODE_HASH)
    (K : SepOn (callKeys (mDO b t C a) (S2 C H a))) :
    Invariant.Inv C (S2 C H a) ∧
    RunsOk 1000000 (processRunner fork 1000000)
      (sFrame (mDO b t C a) (S2 C H a) ss 1000000) (Nat.le_refl _) ∧
    ∀ {g : Nat} (s : Evm fork Nat) (within : GasMeter.gasHeld
        (sFrame (mDO b t C a) (S2 C H a) ss 1000000).gas ≤ g),
      Evm.runFrame (step fork) (step_decreases fork) g (processRunner fork g)
        (sFrame (mDO b t C a) (S2 C H a) ss 1000000) within = .ok s →
      s.error = none → Invariant.Inv C s.state := by
  have hberlin : .berlin ≤ fork := Nat.le_trans (by decide) hparis
  have hmem : kD a ∈ callKeys (mDO b t C a) (S2 C H a) := by
    have e : addrArg (mDO b t C a).data 0 = kD a := addr_mDO b t C a
    unfold callKeys
    rw [e]
    exact List.mem_cons_of_mem _ List.mem_cons_self
  have hI : Invariant.Inv C (S2 C H a) := inv_S2 C H a (K.mono (by
    intro x hx
    rw [List.mem_singleton] at hx
    rw [hx]; exact hmem))
  refine ⟨hI, destroy_mirror_runs hparis hglam b t C a ss H hH, fun {g} s within hrun hok => ?_⟩
  obtain ⟨hdep, -, -, -, -, -, -, hkeeps, hhonest⟩ := process_step_dep_hyps2 hparis b t C a H hH g
  have hsz : (mDO b t C a).data.size < 2 ^ 256 := by
    show (data1 SEL_D a).size < 2 ^ 256; rw [size_data1 size_SEL_D]; decide
  have hsl : selector (mDO b t C a).data = 0xf3bdc228 := by
    show selector (data1 SEL_D a) = _; rw [selector_data1 size_SEL_D]; decide
  have hst : At CODE (mDO b t C a) 0 [] .empty 1000000 (S2 C H a) ss
      (sFrame (mDO b t C a) (S2 C H a) ss 1000000) := at_sFrame (mDO b t C a) rfl _ _ _
  exact inv_dep_destroy (message := mDO b t C a) (state := S2 C H a) (substate := ss)
    (gas := 1000000) (evm := sFrame (mDO b t C a) (S2 C H a) ss 1000000) (bound := g)
    (runChild := processRunner fork g) (s := s) K hberlin hsz hsl hdep hkeeps hhonest hI hst
    within hrun hok

end UsdtVerify.Sanity
