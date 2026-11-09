import UsdtVerify.Usdt.MeterIff
import UsdtVerify.Usdt.Exact.Owner
import UsdtVerify.Usdt.Refill.Owner

/-!
# Exact success conditions of the owner functions over EthLib's EIP-8037 meter

As `Usdt/MeterIff.lean`, for the owner functions not deprecated. From a frame `m` whose `toNat`
is the fresh frame of `CODE` with `gas` gas, reservoir 0, any gas bound and message runner:

- `X_specI`: under the guard of `Usdt/Spec/Guards.lean` and with the gas of `X_iff_gas`, the
  success path over `StepI` (no SSTORE of the path refills).
- `X_ok_sgm`: then the loop over `StateGasMeter` ends with no error and the execution gas left of
  the success path.
- `X_iff_gas_sgm`: the loop over `StateGasMeter` ends with no error if and only if the guard holds
  and the gas is at least the bound of `X_iff_gas`.

The converse direction of each `X_iff_gas_sgm` goes through `runsOk_of_specI`: from a run over
`StateGasMeter` with no error, the run of the meter `Nat` from `toNat m` ends with no error, and
`X_iff_gas` applies to it.

A write refills only when it writes 0 over a word that is not 0 and was 0 at the start of the
transaction. Writes of a word that is not 0 never refill (`refill_of_ne`), nor do additions
without overflow (`refill_add`). The hypotheses on refills, by function:
- none: `pause`, `addBlackList`, `deprecate` (two writes of slot 10, both of a word that is not
  0), `transferOwnership` (a word whose low 160 bits are `a ≠ 0`, or no write for `a = 0`);
- `unpause`: `hnr`, the write of slot 0 with byte 20 cleared;
- `removeBlackList`: `hnr`, the write of `isBlackListed[a]` with its low byte cleared;
- `issue`: `hnrT`, the write of `_totalSupply` (read after the write of `balances[owner]`, which
  may be the same slot). The write of `balances[owner]` adds without overflow;
- `redeem`: `hnrT` (`_totalSupply`) and `hnrO` (`balances[owner]`, read after the first write);
- `setParams`: `hnr3` and `hnr4`, the writes of slots 3 and 4;
- `destroyBlackFunds`: `hnrB` (`balances[a] := 0`) and `hnrT` (`_totalSupply`, read after the
  first write).
-/

namespace UsdtVerify.Exact

open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic hiding SpecG
open UsdtVerify.Gas
open UsdtVerify.Meter
open UsdtVerify.Refill
open UsdtVerify.Shadow
open Complete Owner Admin Pause BlackList Issue SetParams AddrWrite SafeMath
open PauseSpec BlackListSpec IssueSpec SetParamsSpec AddrWriteSpec DestroySpec
open GasCosts

/-- A message runner of the meter `Nat` that fails every message. -/
def failRunner (fork : Fork) (bound : Nat) : MessageRunner fork Nat bound :=
  fun _ _ _ => .error .outOfGas

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate} {bound : Nat} {runChild : MessageRunner fork StateGasMeter bound}
  {m s : Evm fork StateGasMeter} {gas : Nat}

theorem withPaused_one_ne (w : U256) : withPaused w 1 ≠ 0 := by
  intro h
  have := byte20_withPaused w 1 (.inr rfl)
  rw [h] at this
  exact absurd this (by decide)

theorem setLow_one_ne (w : U256) : setLow w 1 ≠ 0 := by
  intro h
  have := lowByte_setLow w 1 (.inr rfl)
  rw [h] at this
  exact absurd this (by decide)

theorem withAddr_ne {w a : U256} (ha : bitwiseAnd ADDR_MASK a ≠ 0) : withAddr w a ≠ 0 := by
  intro h
  have := addr_withAddr w a
  rw [h] at this
  exact ha (this.symm.trans (by decide))

theorem depWord_ne : depWord state message ≠ 0 := by
  intro h
  have h1 := byte20_withAddr (withPaused (storageAt state message.currentTarget 10) 1)
    (addrArg message.data 0)
  rw [byte20_withPaused _ 1 (.inr rfl)] at h1
  simp only [depWord] at h
  rw [h] at h1
  exact absurd h1 (by decide)

/-- The run of the meter `Nat` from `toNat m` that `runsOk_of_specI` gives, as `RunsOk`. -/
theorem runsOk_toNat {P Q : Evm fork Nat → Prop}
    (h : HoareI fork P fun e => e.running = false ∧ Q e) {k : Nat}
    (hp : P (addGas k (toNat m))) (hres : m.gas.reservoir = 0)
    {within : GasMeter.gasHeld m.gas ≤ bound}
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild m within = .ok s)
    (hok : s.error = none) :
    RunsOk fork (toNat m).gas (failRunner fork (toNat m).gas) (toNat m) (Nat.le_refl _) :=
  runsOk_of_specI h hp hres hrun hok _ _

variable (hfork : .berlin ≤ fork) (hsize' : message.data.size < 2 ^ 256)
  (start : At CODE message 0 [] .empty gas state substate (toNat m))
  (hres : m.gas.reservoir = 0)

/-! ## pause -/

section
variable (hsel : selector message.data = 0x8456cb59) {c0 : Bool}
  (hc0 : coldIn substate message.currentTarget 0 = c0)
include hfork hsize' hsel hc0

theorem pause_specI (hG : PauseGuard state message) {g : Nat}
    (hm : max (PAUSE_COST + slotCost c0 + flagCost fork state message 1) (3297 + slotCost c0) ≤
      g) :
    HoareI fork (At CODE message 0 [] .empty g state substate)
      (fun e => e.running = false ∧
        Halted false .empty (g - (PAUSE_COST + slotCost c0 + flagCost fork state message 1))
          e.state e.substate e) := by
  obtain ⟨⟨h4, hv⟩, ⟨hst, hacc⟩, hown, hp⟩ := hG
  obtain ⟨hc, hs⟩ := Nat.max_le.mp hm
  have : slotCost c0 ≤ 2100 := by cases c0 <;> decide
  refine (SpecG.toIW' (spec_pause hfork hst hacc h4 hsize' hsel hv hown hp hc0 hs hc)
    (fun _ _ => rfl) (by simp only [PAUSE_COST]; omega) hacc hc
    (Approve.refill_of_ne (withPaused_one_ne _))).consequence (fun _ h => h) ?_
  rintro e ⟨hr, h1, h2, h3, h4, -, -⟩
  exact ⟨hr, h1, h2, h3, h4, rfl, rfl⟩

include start hres in
/-- **pause over the EIP-8037 meter, with enough gas.** -/
theorem pause_ok_sgm (hG : PauseGuard state message)
    (hm : max (PAUSE_COST + slotCost c0 + flagCost fork state message 1) (3297 + slotCost c0) ≤
      gas) (within : GasMeter.gasHeld m.gas ≤ bound) :
    ∃ s, Evm.runFrame (step fork) (step_decreases fork) bound runChild m within = .ok s ∧
      s.error = none ∧
      s.gas.gasLeft = gas - (PAUSE_COST + slotCost c0 + flagCost fork state message 1) := by
  obtain ⟨s, hs, -, he, -, hg, -⟩ := runFrame_of_specI
    (pause_specI hfork hsize' hsel hc0 hG hm) start hres within
  exact ⟨s, hs, he, hg⟩

include start hres in
/-- **pause over the EIP-8037 meter: the exact success condition.** -/
theorem pause_iff_gas_sgm (within : GasMeter.gasHeld m.gas ≤ bound) :
    RunsOkS fork bound runChild m within ↔ PauseGuard state message ∧
      max (PAUSE_COST + slotCost c0 + flagCost fork state message 1) (3297 + slotCost c0) ≤
        gas := by
  constructor
  · rintro ⟨s, hs, hok⟩
    have hG : PauseGuard state message := by
      obtain ⟨G, hE⟩ := shadow_ends hfork hs hok
      have st' := at_addGas start (budget m)
      obtain ⟨h4, hv, -⟩ := ends_ok_dispatch hfork hsize' st' hE hok
      obtain ⟨hst, hacc, hown, hp, -⟩ := ok_pause hfork hsize' hsel rfl st' hE hok
      exact ⟨⟨h4, hv⟩, ⟨hst, hacc⟩, hown, hp⟩
    exact (pause_iff_gas hfork hsize' start _ hsel hc0).mp (runsOk_toNat
      (pause_specI hfork hsize' hsel hc0 hG (g := gas + max
        (PAUSE_COST + slotCost c0 + flagCost fork state message 1) (3297 + slotCost c0))
        (Nat.le_add_left _ _)) (at_addGas start _) hres hs hok)
  · rintro ⟨hG, hm⟩
    obtain ⟨s, hs, he, -⟩ := pause_ok_sgm hfork hsize' start hres hsel hc0 hG hm within
    exact ⟨s, hs, he⟩

end

/-! ## unpause -/

section
variable (hsel : selector message.data = 0x3f4ba83a) {c0 : Bool}
  (hc0 : coldIn substate message.currentTarget 0 = c0)
  (hnr : sstoreStateRefill fork (originalAt state message.currentTarget 0)
    (storageAt state message.currentTarget 0)
    (withPaused (storageAt state message.currentTarget 0) 0) = 0)
include hfork hsize' hsel hc0 hnr

theorem unpause_specI (hG : UnpauseGuard state message) {g : Nat}
    (hm : max (UNPAUSE_COST + slotCost c0 + flagCost fork state message 0) (3184 + slotCost c0) ≤
      g) :
    HoareI fork (At CODE message 0 [] .empty g state substate)
      (fun e => e.running = false ∧
        Halted false .empty (g - (UNPAUSE_COST + slotCost c0 + flagCost fork state message 0))
          e.state e.substate e) := by
  obtain ⟨⟨h4, hv⟩, ⟨hst, hacc⟩, hown, hp⟩ := hG
  obtain ⟨hc, hs⟩ := Nat.max_le.mp hm
  have : slotCost c0 ≤ 2100 := by cases c0 <;> decide
  refine (SpecG.toIW' (spec_unpause hfork hst hacc h4 hsize' hsel hv hown hp hc0 hs hc)
    (fun _ _ => rfl) (by simp only [UNPAUSE_COST]; omega) hacc hc hnr).consequence
    (fun _ h => h) ?_
  rintro e ⟨hr, h1, h2, h3, h4, -, -⟩
  exact ⟨hr, h1, h2, h3, h4, rfl, rfl⟩

include start hres in
/-- **unpause over the EIP-8037 meter, with enough gas.** -/
theorem unpause_ok_sgm (hG : UnpauseGuard state message)
    (hm : max (UNPAUSE_COST + slotCost c0 + flagCost fork state message 0) (3184 + slotCost c0) ≤
      gas) (within : GasMeter.gasHeld m.gas ≤ bound) :
    ∃ s, Evm.runFrame (step fork) (step_decreases fork) bound runChild m within = .ok s ∧
      s.error = none ∧
      s.gas.gasLeft = gas - (UNPAUSE_COST + slotCost c0 + flagCost fork state message 0) := by
  obtain ⟨s, hs, -, he, -, hg, -⟩ := runFrame_of_specI
    (unpause_specI hfork hsize' hsel hc0 hnr hG hm) start hres within
  exact ⟨s, hs, he, hg⟩

include start hres in
/-- **unpause over the EIP-8037 meter: the exact success condition.** When the write of slot 0
refills nothing (`hnr`). -/
theorem unpause_iff_gas_sgm (within : GasMeter.gasHeld m.gas ≤ bound) :
    RunsOkS fork bound runChild m within ↔ UnpauseGuard state message ∧
      max (UNPAUSE_COST + slotCost c0 + flagCost fork state message 0) (3184 + slotCost c0) ≤
        gas := by
  constructor
  · rintro ⟨s, hs, hok⟩
    have hG : UnpauseGuard state message := by
      obtain ⟨G, hE⟩ := shadow_ends hfork hs hok
      have st' := at_addGas start (budget m)
      obtain ⟨h4, hv, -⟩ := ends_ok_dispatch hfork hsize' st' hE hok
      obtain ⟨hst, hacc, hown, hp, -⟩ := ok_unpause hfork hsize' hsel rfl st' hE hok
      exact ⟨⟨h4, hv⟩, ⟨hst, hacc⟩, hown, hp⟩
    exact (unpause_iff_gas hfork hsize' start _ hsel hc0).mp (runsOk_toNat
      (unpause_specI hfork hsize' hsel hc0 hnr hG (g := gas + max
        (UNPAUSE_COST + slotCost c0 + flagCost fork state message 0) (3184 + slotCost c0))
        (Nat.le_add_left _ _)) (at_addGas start _) hres hs hok)
  · rintro ⟨hG, hm⟩
    obtain ⟨s, hs, he, -⟩ := unpause_ok_sgm hfork hsize' start hres hsel hc0 hnr hG hm within
    exact ⟨s, hs, he⟩

end

/-! ## addBlackList, removeBlackList -/

section
variable {c0 cB : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
  (hcB : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget
    (listSlot (addrArg message.data 0)) = cB)
include hfork hsize' hc0 hcB

theorem addBlackList_specI (hsel : selector message.data = 0x0ecb93c0)
    (hG : OwnerWriteGuard state message) {g : Nat}
    (hm : max (1567 + slotCost c0 + slotCost cB + listCost fork state message 1)
      (2779 + slotCost c0 + slotCost cB) ≤ g) :
    HoareI fork (At CODE message 0 [] .empty g state substate)
      (fun e => e.running = false ∧ Halted false .empty
        (g - (1567 + slotCost c0 + slotCost cB + listCost fork state message 1))
        e.state e.substate e) := by
  obtain ⟨⟨h4, hv⟩, ⟨hst, hacc⟩, hown⟩ := hG
  obtain ⟨hc, hs⟩ := Nat.max_le.mp hm
  have : slotCost c0 ≤ 2100 := by cases c0 <;> decide
  have : slotCost cB ≤ 2100 := by cases cB <;> decide
  refine (SpecG.toIW' (spec_add hfork hst hacc h4 hsize' hsel hv hown hc0 hcB hs hc)
    (getStorage_readSlot _ _ _) (by omega) (hasAccount_readSlot hacc) hc
    (Approve.refill_of_ne (setLow_one_ne _))).consequence (fun _ h => h) ?_
  rintro e ⟨hr, h1, h2, h3, h4, -, -⟩
  exact ⟨hr, h1, h2, h3, h4, rfl, rfl⟩

include start hres in
/-- **addBlackList over the EIP-8037 meter, with enough gas.** -/
theorem addBlackList_ok_sgm (hsel : selector message.data = 0x0ecb93c0)
    (hG : OwnerWriteGuard state message)
    (hm : max (1567 + slotCost c0 + slotCost cB + listCost fork state message 1)
      (2779 + slotCost c0 + slotCost cB) ≤ gas) (within : GasMeter.gasHeld m.gas ≤ bound) :
    ∃ s, Evm.runFrame (step fork) (step_decreases fork) bound runChild m within = .ok s ∧
      s.error = none ∧ s.gas.gasLeft =
        gas - (1567 + slotCost c0 + slotCost cB + listCost fork state message 1) := by
  obtain ⟨s, hs, -, he, -, hg, -⟩ := runFrame_of_specI
    (addBlackList_specI hfork hsize' hc0 hcB hsel hG hm) start hres within
  exact ⟨s, hs, he, hg⟩

include start hres in
/-- **addBlackList over the EIP-8037 meter: the exact success condition.** -/
theorem addBlackList_iff_gas_sgm (hsel : selector message.data = 0x0ecb93c0)
    (within : GasMeter.gasHeld m.gas ≤ bound) :
    RunsOkS fork bound runChild m within ↔ OwnerWriteGuard state message ∧
      max (1567 + slotCost c0 + slotCost cB + listCost fork state message 1)
        (2779 + slotCost c0 + slotCost cB) ≤ gas := by
  constructor
  · rintro ⟨s, hs, hok⟩
    have hG : OwnerWriteGuard state message := by
      obtain ⟨G, hE⟩ := shadow_ends hfork hs hok
      have st' := at_addGas start (budget m)
      obtain ⟨h4, hv, -⟩ := ends_ok_dispatch hfork hsize' st' hE hok
      obtain ⟨hst, hacc, hown, -⟩ := ok_addBlackList hfork hsize' hsel rfl rfl st' hE hok
      exact ⟨⟨h4, hv⟩, ⟨hst, hacc⟩, hown⟩
    exact (addBlackList_iff_gas hfork hsize' start _ hc0 hcB hsel).mp (runsOk_toNat
      (addBlackList_specI hfork hsize' hc0 hcB hsel hG (g := gas + max
        (1567 + slotCost c0 + slotCost cB + listCost fork state message 1)
        (2779 + slotCost c0 + slotCost cB)) (Nat.le_add_left _ _)) (at_addGas start _) hres hs hok)
  · rintro ⟨hG, hm⟩
    obtain ⟨s, hs, he, -⟩ := addBlackList_ok_sgm hfork hsize' start hres hc0 hcB hsel hG hm
      within
    exact ⟨s, hs, he⟩

variable (hnr : sstoreStateRefill fork
  (originalAt state message.currentTarget (listSlot (addrArg message.data 0)))
  (storageAt state message.currentTarget (listSlot (addrArg message.data 0)))
  (setLow (storageAt state message.currentTarget (listSlot (addrArg message.data 0))) 0) = 0)
include hnr

theorem removeBlackList_specI (hsel : selector message.data = 0xe4997dc5)
    (hG : OwnerWriteGuard state message) {g : Nat}
    (hm : max (2095 + slotCost c0 + slotCost cB + listCost fork state message 0)
      (3307 + slotCost c0 + slotCost cB) ≤ g) :
    HoareI fork (At CODE message 0 [] .empty g state substate)
      (fun e => e.running = false ∧ Halted false .empty
        (g - (2095 + slotCost c0 + slotCost cB + listCost fork state message 0))
        e.state e.substate e) := by
  obtain ⟨⟨h4, hv⟩, ⟨hst, hacc⟩, hown⟩ := hG
  obtain ⟨hc, hs⟩ := Nat.max_le.mp hm
  have : slotCost c0 ≤ 2100 := by cases c0 <;> decide
  have : slotCost cB ≤ 2100 := by cases cB <;> decide
  refine (SpecG.toIW' (spec_remove hfork hst hacc h4 hsize' hsel hv hown hc0 hcB hs hc)
    (getStorage_readSlot _ _ _) (by omega) (hasAccount_readSlot hacc) hc hnr).consequence
    (fun _ h => h) ?_
  rintro e ⟨hr, h1, h2, h3, h4, -, -⟩
  exact ⟨hr, h1, h2, h3, h4, rfl, rfl⟩

include start hres in
/-- **removeBlackList over the EIP-8037 meter, with enough gas.** -/
theorem removeBlackList_ok_sgm (hsel : selector message.data = 0xe4997dc5)
    (hG : OwnerWriteGuard state message)
    (hm : max (2095 + slotCost c0 + slotCost cB + listCost fork state message 0)
      (3307 + slotCost c0 + slotCost cB) ≤ gas) (within : GasMeter.gasHeld m.gas ≤ bound) :
    ∃ s, Evm.runFrame (step fork) (step_decreases fork) bound runChild m within = .ok s ∧
      s.error = none ∧ s.gas.gasLeft =
        gas - (2095 + slotCost c0 + slotCost cB + listCost fork state message 0) := by
  obtain ⟨s, hs, -, he, -, hg, -⟩ := runFrame_of_specI
    (removeBlackList_specI hfork hsize' hc0 hcB hnr hsel hG hm) start hres within
  exact ⟨s, hs, he, hg⟩

include start hres in
/-- **removeBlackList over the EIP-8037 meter: the exact success condition.** When the write of
`isBlackListed[a]` refills nothing (`hnr`). -/
theorem removeBlackList_iff_gas_sgm (hsel : selector message.data = 0xe4997dc5)
    (within : GasMeter.gasHeld m.gas ≤ bound) :
    RunsOkS fork bound runChild m within ↔ OwnerWriteGuard state message ∧
      max (2095 + slotCost c0 + slotCost cB + listCost fork state message 0)
        (3307 + slotCost c0 + slotCost cB) ≤ gas := by
  constructor
  · rintro ⟨s, hs, hok⟩
    have hG : OwnerWriteGuard state message := by
      obtain ⟨G, hE⟩ := shadow_ends hfork hs hok
      have st' := at_addGas start (budget m)
      obtain ⟨h4, hv, -⟩ := ends_ok_dispatch hfork hsize' st' hE hok
      obtain ⟨hst, hacc, hown, -⟩ := ok_removeBlackList hfork hsize' hsel rfl rfl st' hE hok
      exact ⟨⟨h4, hv⟩, ⟨hst, hacc⟩, hown⟩
    exact (removeBlackList_iff_gas hfork hsize' start _ hc0 hcB hsel).mp (runsOk_toNat
      (removeBlackList_specI hfork hsize' hc0 hcB hnr hsel hG (g := gas + max
        (2095 + slotCost c0 + slotCost cB + listCost fork state message 0)
        (3307 + slotCost c0 + slotCost cB)) (Nat.le_add_left _ _)) (at_addGas start _) hres hs hok)
  · rintro ⟨hG, hm⟩
    obtain ⟨s, hs, he, -⟩ := removeBlackList_ok_sgm hfork hsize' start hres hc0 hcB hnr hsel hG
      hm within
    exact ⟨s, hs, he⟩

end

/-! ## deprecate, transferOwnership -/

section
variable (hsel : selector message.data = 0x0753c30c) {c0 c10 : Bool}
  (hc0 : coldIn substate message.currentTarget 0 = c0)
  (hc10 : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget 10 = c10)
include hfork hsize' hsel hc0 hc10

/-- The two writes of `deprecate` are of slot 10 and both write a word that is not 0, so neither
refills. -/
theorem deprecate_specI (hG : OwnerWriteGuard state message) {g : Nat}
    (hm : max (1628 + slotCost c0 + slotCost c10 + depCost fork state message)
      (2840 + slotCost c0 + slotCost c10 + Gas.writeCost fork
        (originalAt state message.currentTarget 10) (storageAt state message.currentTarget 10)
        (withPaused (storageAt state message.currentTarget 10) 1) false) ≤ g) :
    HoareI fork (At CODE message 0 [] .empty g state substate)
      (fun e => e.running = false ∧ Halted false .empty
        (g - (1628 + slotCost c0 + slotCost c10 + depCost fork state message))
        e.state e.substate e) := by
  obtain ⟨⟨h4, hv⟩, ⟨hst, hacc⟩, hown⟩ := hG
  obtain ⟨hc, hs⟩ := Nat.max_le.mp hm
  have : slotCost c0 ≤ 2100 := by cases c0 <;> decide
  have : slotCost c10 ≤ 2100 := by cases c10 <;> decide
  have hacc0 := hasAccount_readSlot (n := 0) (other := message.currentTarget) hacc
  have hacc1 := hasAccount_writeSlot (n := 10)
    (v := withPaused (storageAt state message.currentTarget 10) 1) hacc0
  have hend : storageAt (depState state message) message.currentTarget 10 =
      depWord state message := storageAt_writeSlot_self hacc1
  have hS : STORAGE_SET_STATE_GAS = 97920 := rfl
  refine (SpecG.toIS (T := message.currentTarget) (n := 10)
    (spec_deprecate hfork hst hacc h4 hsize' hsel hv hown hc0 hc10 hs hc)
    (fun a k hne => by
      simp only [depState]
      rw [getStorage_writeSlot_ne hacc1 hne, getStorage_writeSlot_ne hacc0 hne]
      rfl)
    (fun _ h => depWord_ne (hend.symm.trans h.2.2))
    (fun hglam => ?_) (fun hglam hn => ?_)).consequence (fun _ h => h) ?_
  · have h1 := writeCost_le_max hglam (originalAt state message.currentTarget 10)
      (storageAt state message.currentTarget 10)
      (withPaused (storageAt state message.currentTarget 10) 1) false
    have h2 := writeCost_le_of_no_create hglam (originalAt state message.currentTarget 10)
      (withPaused (storageAt state message.currentTarget 10) 1) (depWord state message) false
      (fun h => withPaused_one_ne _ h.2.1)
    simp only [depCost, depWord] at hc h1 h2 ⊢
    omega
  · rw [hend] at hn
    have h1 := writeCost_le_of_no_create hglam (originalAt state message.currentTarget 10)
      (storageAt state message.currentTarget 10)
      (withPaused (storageAt state message.currentTarget 10) 1) false
      (fun h => hn ⟨h.1, h.2.1, depWord_ne⟩)
    have h2 := writeCost_le_of_no_create hglam (originalAt state message.currentTarget 10)
      (withPaused (storageAt state message.currentTarget 10) 1) (depWord state message) false
      (fun h => withPaused_one_ne _ h.2.1)
    simp only [depCost, depWord] at hc h1 h2 ⊢
    omega
  · rintro e ⟨hr, h1, h2, h3, h4, -, -⟩
    exact ⟨hr, h1, h2, h3, h4, rfl, rfl⟩

include start hres in
/-- **deprecate over the EIP-8037 meter, with enough gas.** -/
theorem deprecate_ok_sgm (hG : OwnerWriteGuard state message)
    (hm : max (1628 + slotCost c0 + slotCost c10 + depCost fork state message)
      (2840 + slotCost c0 + slotCost c10 + Gas.writeCost fork
        (originalAt state message.currentTarget 10) (storageAt state message.currentTarget 10)
        (withPaused (storageAt state message.currentTarget 10) 1) false) ≤ gas)
    (within : GasMeter.gasHeld m.gas ≤ bound) :
    ∃ s, Evm.runFrame (step fork) (step_decreases fork) bound runChild m within = .ok s ∧
      s.error = none ∧ s.gas.gasLeft =
        gas - (1628 + slotCost c0 + slotCost c10 + depCost fork state message) := by
  obtain ⟨s, hs, -, he, -, hg, -⟩ := runFrame_of_specI
    (deprecate_specI hfork hsize' hsel hc0 hc10 hG hm) start hres within
  exact ⟨s, hs, he, hg⟩

include start hres in
/-- **deprecate over the EIP-8037 meter: the exact success condition.** -/
theorem deprecate_iff_gas_sgm (within : GasMeter.gasHeld m.gas ≤ bound) :
    RunsOkS fork bound runChild m within ↔ OwnerWriteGuard state message ∧
      max (1628 + slotCost c0 + slotCost c10 + depCost fork state message)
        (2840 + slotCost c0 + slotCost c10 + Gas.writeCost fork
          (originalAt state message.currentTarget 10) (storageAt state message.currentTarget 10)
          (withPaused (storageAt state message.currentTarget 10) 1) false) ≤ gas := by
  constructor
  · rintro ⟨s, hs, hok⟩
    have hG : OwnerWriteGuard state message := by
      obtain ⟨G, hE⟩ := shadow_ends hfork hs hok
      have st' := at_addGas start (budget m)
      obtain ⟨h4, hv, -⟩ := ends_ok_dispatch hfork hsize' st' hE hok
      obtain ⟨hst, hacc, hown, -⟩ := ok_deprecate hfork hsize' hsel rfl rfl st' hE hok
      exact ⟨⟨h4, hv⟩, ⟨hst, hacc⟩, hown⟩
    exact (deprecate_iff_gas hfork hsize' start _ hsel hc0 hc10).mp (runsOk_toNat
      (deprecate_specI hfork hsize' hsel hc0 hc10 hG (g := gas + max
        (1628 + slotCost c0 + slotCost c10 + depCost fork state message)
        (2840 + slotCost c0 + slotCost c10 + Gas.writeCost fork
          (originalAt state message.currentTarget 10) (storageAt state message.currentTarget 10)
          (withPaused (storageAt state message.currentTarget 10) 1) false))
        (Nat.le_add_left _ _)) (at_addGas start _) hres hs hok)
  · rintro ⟨hG, hm⟩
    obtain ⟨s, hs, he, -⟩ := deprecate_ok_sgm hfork hsize' start hres hsel hc0 hc10 hG hm within
    exact ⟨s, hs, he⟩

end

section
variable (hsel : selector message.data = 0xf2fde38b) {c0 : Bool}
  (hc0 : coldIn substate message.currentTarget 0 = c0)
include hfork hsize' hsel hc0

/-- The write of `transferOwnership(a)` (only for `a ≠ 0`) writes a word whose low 160 bits are
`a`, so it never refills. -/
theorem transferOwnership_specI (hG : TransferOwnershipGuard state message) {g : Nat}
    (hm : max (ownershipCost fork state message c0) (ownershipStip message c0) ≤ g) :
    HoareI fork (At CODE message 0 [] .empty g state substate)
      (fun e => e.running = false ∧ Halted false .empty
        (g - ownershipCost fork state message c0) e.state e.substate e) := by
  obtain ⟨⟨h4, hv⟩, hown, hw⟩ := hG
  obtain ⟨hc, hs⟩ := Nat.max_le.mp hm
  have : slotCost c0 ≤ 2100 := by cases c0 <;> decide
  by_cases hz : addrArg message.data 0 = 0
  · simp only [ownershipCost, hz, ↓reduceIte] at hc ⊢
    refine (SpecG.toIA (spec_transferOwnership_zero hfork h4 hsize' hsel hv hown hz hc0 hc)
      (by omega) (getStorage_readSlot _ _ _)).consequence (fun _ h => h) ?_
    rintro e ⟨hr, h1, h2, h3, h4, -, -⟩
    exact ⟨hr, h1, h2, h3, h4, rfl, rfl⟩
  · simp only [ownershipCost, ownershipStip, hz, ↓reduceIte] at hc hs ⊢
    obtain ⟨hst, hacc⟩ := hw hz
    refine (SpecG.toIW' (spec_transferOwnership hfork hst hacc h4 hsize' hsel hv hown hz hc0 hs hc)
      (fun _ _ => rfl) (by omega) hacc hc (Approve.refill_of_ne (withAddr_ne
        (by rw [addrArg, mask_mask, ← addrArg]; exact hz)))).consequence (fun _ h => h) ?_
    rintro e ⟨hr, h1, h2, h3, h4, -, -⟩
    exact ⟨hr, h1, h2, h3, h4, rfl, rfl⟩

include start hres in
/-- **transferOwnership over the EIP-8037 meter, with enough gas.** -/
theorem transferOwnership_ok_sgm (hG : TransferOwnershipGuard state message)
    (hm : max (ownershipCost fork state message c0) (ownershipStip message c0) ≤ gas)
    (within : GasMeter.gasHeld m.gas ≤ bound) :
    ∃ s, Evm.runFrame (step fork) (step_decreases fork) bound runChild m within = .ok s ∧
      s.error = none ∧ s.gas.gasLeft = gas - ownershipCost fork state message c0 := by
  obtain ⟨s, hs, -, he, -, hg, -⟩ := runFrame_of_specI
    (transferOwnership_specI hfork hsize' hsel hc0 hG hm) start hres within
  exact ⟨s, hs, he, hg⟩

include start hres in
/-- **transferOwnership over the EIP-8037 meter: the exact success condition.** -/
theorem transferOwnership_iff_gas_sgm (within : GasMeter.gasHeld m.gas ≤ bound) :
    RunsOkS fork bound runChild m within ↔ TransferOwnershipGuard state message ∧
      max (ownershipCost fork state message c0) (ownershipStip message c0) ≤ gas := by
  constructor
  · rintro ⟨s, hs, hok⟩
    have hG : TransferOwnershipGuard state message := by
      obtain ⟨G, hE⟩ := shadow_ends hfork hs hok
      have st' := at_addGas start (budget m)
      obtain ⟨h4, hv, -⟩ := ends_ok_dispatch hfork hsize' st' hE hok
      obtain ⟨hown, -, h⟩ := ok_transferOwnership hfork hsize' hsel rfl st' hE hok
      refine ⟨⟨h4, hv⟩, hown, fun hz => ?_⟩
      rcases h with ⟨h0, -⟩ | ⟨-, hst, hacc, -⟩
      · exact absurd h0 hz
      · exact ⟨hst, hacc⟩
    exact (transferOwnership_iff_gas hfork hsize' start _ hsel hc0).mp (runsOk_toNat
      (transferOwnership_specI hfork hsize' hsel hc0 hG (g := gas + max
        (ownershipCost fork state message c0) (ownershipStip message c0))
        (Nat.le_add_left _ _)) (at_addGas start _) hres hs hok)
  · rintro ⟨hG, hm⟩
    obtain ⟨s, hs, he, -⟩ := transferOwnership_ok_sgm hfork hsize' start hres hsel hc0 hG hm
      within
    exact ⟨s, hs, he⟩

end

/-! ## issue, redeem -/

section
variable {c0 c1 cO : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
  (hc1 : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget 1 = c1)
  (hcO : coldIn (accessSlot (accessSlot substate message.currentTarget 0) message.currentTarget 1)
    message.currentTarget (ownerBal state message.currentTarget) = cO)
include hfork hsize' hc0 hc1 hcO

section
variable (hsel : selector message.data = 0xcc872b66)
  (hnrT : sstoreStateRefill fork (originalAt state message.currentTarget 1)
    (storageAt (issueState1 state message) message.currentTarget 1)
    (add (storageAt (issueState1 state message) message.currentTarget 1)
      (wordArg message.data 0)) = 0)
include hsel hnrT

/-- The write of `balances[owner]` adds without overflow and never refills; the write of
`_totalSupply` refills nothing by `hnrT`. -/
theorem issue_specI (hG : IssueGuard state message) {g : Nat}
    (hm : max (3024 + slotCost c0 + slotCost c1 + slotCost cO + issueCostO fork state message +
        issueCostT fork state message)
      (4248 + slotCost c0 + slotCost c1 + slotCost cO + issueCostO fork state message) ≤ g) :
    HoareI fork (At CODE message 0 [] .empty g state substate)
      (fun e => e.running = false ∧ Halted false .empty
        (g - (3024 + slotCost c0 + slotCost c1 + slotCost cO + issueCostO fork state message +
          issueCostT fork state message)) e.state e.substate e) := by
  obtain ⟨⟨h4, hv⟩, ⟨hst, hacc⟩, hown, h0, hT, hB⟩ := hG
  obtain ⟨hc, hs⟩ := Nat.max_le.mp hm
  refine (spec_issueI hfork hst hacc h4 hsize' hsel hv hown ⟨h0, hT⟩ hB hc0 hc1 hcO hnrT hs
    hc).consequence (fun _ h => h) ?_
  rintro e ⟨hr, h1, h2, h3, h4, -, -⟩
  exact ⟨hr, h1, h2, h3, h4, rfl, rfl⟩

include start hres in
/-- **issue over the EIP-8037 meter, with enough gas.** -/
theorem issue_ok_sgm (hG : IssueGuard state message)
    (hm : max (3024 + slotCost c0 + slotCost c1 + slotCost cO + issueCostO fork state message +
        issueCostT fork state message)
      (4248 + slotCost c0 + slotCost c1 + slotCost cO + issueCostO fork state message) ≤ gas)
    (within : GasMeter.gasHeld m.gas ≤ bound) :
    ∃ s, Evm.runFrame (step fork) (step_decreases fork) bound runChild m within = .ok s ∧
      s.error = none ∧ s.gas.gasLeft = gas - (3024 + slotCost c0 + slotCost c1 + slotCost cO +
        issueCostO fork state message + issueCostT fork state message) := by
  obtain ⟨s, hs, -, he, -, hg, -⟩ := runFrame_of_specI
    (issue_specI hfork hsize' hc0 hc1 hcO hsel hnrT hG hm) start hres within
  exact ⟨s, hs, he, hg⟩

include start hres in
/-- **issue over the EIP-8037 meter: the exact success condition.** When the write of
`_totalSupply` refills nothing (`hnrT`). -/
theorem issue_iff_gas_sgm (within : GasMeter.gasHeld m.gas ≤ bound) :
    RunsOkS fork bound runChild m within ↔ IssueGuard state message ∧
      max (3024 + slotCost c0 + slotCost c1 + slotCost cO + issueCostO fork state message +
        issueCostT fork state message)
        (4248 + slotCost c0 + slotCost c1 + slotCost cO + issueCostO fork state message) ≤ gas := by
  constructor
  · rintro ⟨s, hs, hok⟩
    have hG : IssueGuard state message := by
      obtain ⟨G, hE⟩ := shadow_ends hfork hs hok
      have st' := at_addGas start (budget m)
      obtain ⟨h4, hv, -⟩ := ends_ok_dispatch hfork hsize' st' hE hok
      obtain ⟨hst, hacc, hown, h0, hT, hB, -⟩ := ok_issue hfork hsize' hsel rfl rfl rfl st' hE hok
      exact ⟨⟨h4, hv⟩, ⟨hst, hacc⟩, hown, h0, hT, hB⟩
    exact (issue_iff_gas hfork hsize' start _ hc0 hc1 hcO hsel).mp (runsOk_toNat
      (issue_specI hfork hsize' hc0 hc1 hcO hsel hnrT hG (g := gas + max
        (3024 + slotCost c0 + slotCost c1 + slotCost cO + issueCostO fork state message +
          issueCostT fork state message)
        (4248 + slotCost c0 + slotCost c1 + slotCost cO + issueCostO fork state message))
        (Nat.le_add_left _ _)) (at_addGas start _) hres hs hok)
  · rintro ⟨hG, hm⟩
    obtain ⟨s, hs, he, -⟩ := issue_ok_sgm hfork hsize' start hres hc0 hc1 hcO hsel hnrT hG hm
      within
    exact ⟨s, hs, he⟩

end

section
variable (hsel : selector message.data = 0xdb006a75)
  (hnrT : sstoreStateRefill fork (originalAt state message.currentTarget 1)
    (storageAt state message.currentTarget 1)
    (sub (storageAt state message.currentTarget 1) (wordArg message.data 0)) = 0)
  (hnrO : sstoreStateRefill fork
    (originalAt state message.currentTarget (ownerBal state message.currentTarget))
    (storageAt (redeemState1 state message) message.currentTarget
      (ownerBal state message.currentTarget))
    (sub (storageAt (redeemState1 state message) message.currentTarget
      (ownerBal state message.currentTarget)) (wordArg message.data 0)) = 0)
include hsel hnrT hnrO

/-- Both writes of `redeem` subtract; they refill nothing by `hnrT` and `hnrO`. -/
theorem redeem_specI (hG : RedeemGuard state message) {g : Nat}
    (hm : max (2614 + slotCost c0 + slotCost c1 + slotCost cO + redeemCostT fork state message +
        redeemCostO fork state message)
      (3838 + slotCost c0 + slotCost c1 + slotCost cO + redeemCostT fork state message) ≤ g) :
    HoareI fork (At CODE message 0 [] .empty g state substate)
      (fun e => e.running = false ∧ Halted false .empty
        (g - (2614 + slotCost c0 + slotCost c1 + slotCost cO + redeemCostT fork state message +
          redeemCostO fork state message)) e.state e.substate e) := by
  obtain ⟨⟨h4, hv⟩, ⟨hst, hacc⟩, hown, hT, hB⟩ := hG
  obtain ⟨hc, hs⟩ := Nat.max_le.mp hm
  refine (spec_redeemI hfork hst hacc h4 hsize' hsel hv hown hT hB hc0 hc1 hcO hnrT hnrO hs
    hc).consequence (fun _ h => h) ?_
  rintro e ⟨hr, h1, h2, h3, h4, -, -⟩
  exact ⟨hr, h1, h2, h3, h4, rfl, rfl⟩

include start hres in
/-- **redeem over the EIP-8037 meter, with enough gas.** -/
theorem redeem_ok_sgm (hG : RedeemGuard state message)
    (hm : max (2614 + slotCost c0 + slotCost c1 + slotCost cO + redeemCostT fork state message +
        redeemCostO fork state message)
      (3838 + slotCost c0 + slotCost c1 + slotCost cO + redeemCostT fork state message) ≤ gas)
    (within : GasMeter.gasHeld m.gas ≤ bound) :
    ∃ s, Evm.runFrame (step fork) (step_decreases fork) bound runChild m within = .ok s ∧
      s.error = none ∧ s.gas.gasLeft = gas - (2614 + slotCost c0 + slotCost c1 + slotCost cO +
        redeemCostT fork state message + redeemCostO fork state message) := by
  obtain ⟨s, hs, -, he, -, hg, -⟩ := runFrame_of_specI
    (redeem_specI hfork hsize' hc0 hc1 hcO hsel hnrT hnrO hG hm) start hres within
  exact ⟨s, hs, he, hg⟩

include start hres in
/-- **redeem over the EIP-8037 meter: the exact success condition.** When the writes of
`_totalSupply` (`hnrT`) and `balances[owner]` (`hnrO`) refill nothing. -/
theorem redeem_iff_gas_sgm (within : GasMeter.gasHeld m.gas ≤ bound) :
    RunsOkS fork bound runChild m within ↔ RedeemGuard state message ∧
      max (2614 + slotCost c0 + slotCost c1 + slotCost cO + redeemCostT fork state message +
        redeemCostO fork state message)
        (3838 + slotCost c0 + slotCost c1 + slotCost cO + redeemCostT fork state message) ≤
          gas := by
  constructor
  · rintro ⟨s, hs, hok⟩
    have hG : RedeemGuard state message := by
      obtain ⟨G, hE⟩ := shadow_ends hfork hs hok
      have st' := at_addGas start (budget m)
      obtain ⟨h4, hv, -⟩ := ends_ok_dispatch hfork hsize' st' hE hok
      obtain ⟨hst, hacc, hown, hT, hB, -⟩ := ok_redeem hfork hsize' hsel rfl rfl rfl st' hE hok
      exact ⟨⟨h4, hv⟩, ⟨hst, hacc⟩, hown, hT, hB⟩
    exact (redeem_iff_gas hfork hsize' start _ hc0 hc1 hcO hsel).mp (runsOk_toNat
      (redeem_specI hfork hsize' hc0 hc1 hcO hsel hnrT hnrO hG (g := gas + max
        (2614 + slotCost c0 + slotCost c1 + slotCost cO + redeemCostT fork state message +
          redeemCostO fork state message)
        (3838 + slotCost c0 + slotCost c1 + slotCost cO + redeemCostT fork state message))
        (Nat.le_add_left _ _)) (at_addGas start _) hres hs hok)
  · rintro ⟨hG, hm⟩
    obtain ⟨s, hs, he, -⟩ := redeem_ok_sgm hfork hsize' start hres hc0 hc1 hcO hsel hnrT hnrO hG
      hm within
    exact ⟨s, hs, he⟩

end

end

/-! ## setParams -/

section
variable (hsel : selector message.data = 0xc0324c77) {c0 c3 c9 c4 : Bool}
  (hc0 : coldIn substate message.currentTarget 0 = c0)
  (hc3 : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget 3 = c3)
  (hc9 : coldIn (accessSlot (accessSlot substate message.currentTarget 0) message.currentTarget 3)
    message.currentTarget 9 = c9)
  (hc4 : coldIn (accessSlot (accessSlot (accessSlot substate message.currentTarget 0)
    message.currentTarget 3) message.currentTarget 9) message.currentTarget 4 = c4)
  (hnr3 : sstoreStateRefill fork (originalAt state message.currentTarget 3)
    (storageAt state message.currentTarget 3) (wordArg message.data 0) = 0)
  (hnr4 : sstoreStateRefill fork (originalAt state message.currentTarget 4)
    (storageAt state message.currentTarget 4) (feeWord state message) = 0)
include hfork hsize' hsel hc0 hc3 hc9 hc4 hnr3 hnr4

/-- The writes of slots 3 and 4 refill nothing by `hnr3` and `hnr4`. -/
theorem setParams_specI (hG : SetParamsGuard state message) {g : Nat}
    (hm : max (2425 + paramsCost fork state message c0 c3 c9 c4)
      (3168 + slotCost c0 + Gas.writeCost fork (originalAt state message.currentTarget 3)
        (storageAt state message.currentTarget 3) (wordArg message.data 0) c3 + slotCost c9 +
        50 * exponentBytes (storageAt state message.currentTarget 9) +
        mulCost (wordArg message.data 1)) ≤ g) :
    HoareI fork (At CODE message 0 [] .empty g state substate)
      (fun e => e.running = false ∧ Halted false .empty
        (g - (2425 + paramsCost fork state message c0 c3 c9 c4)) e.state e.substate e) := by
  obtain ⟨⟨h4, hv⟩, ⟨hst, hacc⟩, hown, hb, hmm, hov⟩ := hG
  obtain ⟨hc, hs⟩ := Nat.max_le.mp hm
  refine (spec_setParamsI hfork hst hacc h4 hsize' hsel hv hown hb hmm hov hc0 hc3 hc9 hc4 hnr3
    hnr4 hs hc).consequence (fun _ h => h) ?_
  rintro e ⟨hr, h1, h2, h3, h4, -, -⟩
  exact ⟨hr, h1, h2, h3, h4, rfl, rfl⟩

include start hres in
/-- **setParams over the EIP-8037 meter, with enough gas.** -/
theorem setParams_ok_sgm (hG : SetParamsGuard state message)
    (hm : max (2425 + paramsCost fork state message c0 c3 c9 c4)
      (3168 + slotCost c0 + Gas.writeCost fork (originalAt state message.currentTarget 3)
        (storageAt state message.currentTarget 3) (wordArg message.data 0) c3 + slotCost c9 +
        50 * exponentBytes (storageAt state message.currentTarget 9) +
        mulCost (wordArg message.data 1)) ≤ gas)
    (within : GasMeter.gasHeld m.gas ≤ bound) :
    ∃ s, Evm.runFrame (step fork) (step_decreases fork) bound runChild m within = .ok s ∧
      s.error = none ∧ s.gas.gasLeft = gas - (2425 + paramsCost fork state message c0 c3 c9 c4) := by
  obtain ⟨s, hs, -, he, -, hg, -⟩ := runFrame_of_specI
    (setParams_specI hfork hsize' hsel hc0 hc3 hc9 hc4 hnr3 hnr4 hG hm) start hres within
  exact ⟨s, hs, he, hg⟩

include start hres in
/-- **setParams over the EIP-8037 meter: the exact success condition.** When the writes of slots 3
(`hnr3`) and 4 (`hnr4`) refill nothing. -/
theorem setParams_iff_gas_sgm (within : GasMeter.gasHeld m.gas ≤ bound) :
    RunsOkS fork bound runChild m within ↔ SetParamsGuard state message ∧
      max (2425 + paramsCost fork state message c0 c3 c9 c4)
        (3168 + slotCost c0 + Gas.writeCost fork (originalAt state message.currentTarget 3)
          (storageAt state message.currentTarget 3) (wordArg message.data 0) c3 + slotCost c9 +
          50 * exponentBytes (storageAt state message.currentTarget 9) +
          mulCost (wordArg message.data 1)) ≤ gas := by
  constructor
  · rintro ⟨s, hs, hok⟩
    have hG : SetParamsGuard state message := by
      obtain ⟨G, hE⟩ := shadow_ends hfork hs hok
      have st' := at_addGas start (budget m)
      obtain ⟨h4, hv, -⟩ := ends_ok_dispatch hfork hsize' st' hE hok
      obtain ⟨hst, hacc, hown, hb, hmm, hov, -⟩ :=
        ok_setParams hfork hsize' hsel rfl rfl rfl rfl st' hE hok
      exact ⟨⟨h4, hv⟩, ⟨hst, hacc⟩, hown, hb, hmm, hov⟩
    exact (setParams_iff_gas hfork hsize' start _ hsel hc0 hc3 hc9 hc4).mp (runsOk_toNat
      (setParams_specI hfork hsize' hsel hc0 hc3 hc9 hc4 hnr3 hnr4 hG (g := gas + max
        (2425 + paramsCost fork state message c0 c3 c9 c4)
        (3168 + slotCost c0 + Gas.writeCost fork (originalAt state message.currentTarget 3)
          (storageAt state message.currentTarget 3) (wordArg message.data 0) c3 + slotCost c9 +
          50 * exponentBytes (storageAt state message.currentTarget 9) +
          mulCost (wordArg message.data 1)))
        (Nat.le_add_left _ _)) (at_addGas start _) hres hs hok)
  · rintro ⟨hG, hm⟩
    obtain ⟨s, hs, he, -⟩ := setParams_ok_sgm hfork hsize' start hres hsel hc0 hc3 hc9 hc4 hnr3
      hnr4 hG hm within
    exact ⟨s, hs, he⟩

end

/-! ## destroyBlackFunds, not deprecated -/

section
variable (hsel : selector message.data = 0xf3bdc228)
  (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
  {c0 cL c10 cB c1 : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
  (hcL : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget
    (listSlot (addrArg message.data 0)) = cL)
  (hc10 : coldIn (preSub substate message) message.currentTarget 10 = c10)
  (hcB : coldIn (accessSlot (preSub substate message) message.currentTarget 10)
    message.currentTarget (balSlot message) = cB)
  (hc1 : coldIn (readSub substate message) message.currentTarget 1 = c1)
  (hnrB : sstoreStateRefill fork (originalAt state message.currentTarget (balSlot message))
    (dirty state message) 0 = 0)
  (hnrT : sstoreStateRefill fork (originalAt state message.currentTarget 1)
    (storageAt (state1 state message) message.currentTarget 1)
    (sub (storageAt (state1 state message) message.currentTarget 1) (dirty state message)) = 0)
include hfork hsize' hsel hdep hc0 hcL hc10 hcB hc1 hnrB hnrT

/-- The writes of `balances[a]` (`hnrB`) and `_totalSupply` (`hnrT`) refill nothing. -/
theorem destroyBlackFunds_specI (hG : DestroyBlackFundsGuard state message) {g : Nat}
    (hm : max (2865 + slotCost c0 + slotCost cL + slotCost c10 + slotCost cB + slotCost c1 +
        costB fork state message + costT fork state message)
      (max (3763 + slotCost c0 + slotCost cL + slotCost c10 + slotCost cB)
        (3796 + slotCost c0 + slotCost cL + slotCost c10 + slotCost cB +
          costB fork state message + slotCost c1)) ≤ g) :
    HoareI fork (At CODE message 0 [] .empty g state substate)
      (fun e => e.running = false ∧ Halted false .empty
        (g - (2865 + slotCost c0 + slotCost cL + slotCost c10 + slotCost cB + slotCost c1 +
          costB fork state message + costT fork state message)) e.state e.substate e) := by
  obtain ⟨⟨h4, hv⟩, ⟨hst, hacc⟩, hown, hl⟩ := hG
  obtain ⟨hc, hs⟩ := Nat.max_le.mp hm
  obtain ⟨hs1, hs2⟩ := Nat.max_le.mp hs
  refine (DestroySpec.specI hfork hst hacc h4 hsize' hsel hv hown hl hdep hc0 hcL hc10 hcB hc1
    hnrB hnrT hs1 hs2 hc).consequence (fun _ h => h) ?_
  rintro e ⟨hr, h1, h2, h3, h4, -, -⟩
  exact ⟨hr, h1, h2, h3, h4, rfl, rfl⟩

include start hres in
/-- **destroyBlackFunds over the EIP-8037 meter, with enough gas.** -/
theorem destroyBlackFunds_ok_sgm (hG : DestroyBlackFundsGuard state message)
    (hm : max (2865 + slotCost c0 + slotCost cL + slotCost c10 + slotCost cB + slotCost c1 +
        costB fork state message + costT fork state message)
      (max (3763 + slotCost c0 + slotCost cL + slotCost c10 + slotCost cB)
        (3796 + slotCost c0 + slotCost cL + slotCost c10 + slotCost cB +
          costB fork state message + slotCost c1)) ≤ gas)
    (within : GasMeter.gasHeld m.gas ≤ bound) :
    ∃ s, Evm.runFrame (step fork) (step_decreases fork) bound runChild m within = .ok s ∧
      s.error = none ∧ s.gas.gasLeft = gas - (2865 + slotCost c0 + slotCost cL + slotCost c10 +
        slotCost cB + slotCost c1 + costB fork state message + costT fork state message) := by
  obtain ⟨s, hs, -, he, -, hg, -⟩ := runFrame_of_specI
    (destroyBlackFunds_specI hfork hsize' hsel hdep hc0 hcL hc10 hcB hc1 hnrB hnrT hG hm) start
    hres within
  exact ⟨s, hs, he, hg⟩

include start hres in
/-- **destroyBlackFunds over the EIP-8037 meter: the exact success condition.** Not deprecated,
when the writes of `balances[a]` (`hnrB`) and `_totalSupply` (`hnrT`) refill nothing. -/
theorem destroyBlackFunds_iff_gas_sgm (within : GasMeter.gasHeld m.gas ≤ bound) :
    RunsOkS fork bound runChild m within ↔ DestroyBlackFundsGuard state message ∧
      max (2865 + slotCost c0 + slotCost cL + slotCost c10 + slotCost cB + slotCost c1 +
        costB fork state message + costT fork state message)
        (max (3763 + slotCost c0 + slotCost cL + slotCost c10 + slotCost cB)
          (3796 + slotCost c0 + slotCost cL + slotCost c10 + slotCost cB +
            costB fork state message + slotCost c1)) ≤ gas := by
  constructor
  · rintro ⟨s, hs, hok⟩
    have hG : DestroyBlackFundsGuard state message := by
      obtain ⟨G, hE⟩ := shadow_ends hfork hs hok
      have st' := at_addGas start (budget m)
      obtain ⟨h4, hv, -⟩ := ends_ok_dispatch hfork hsize' st' hE hok
      obtain ⟨hst, hacc, hown, hl, -⟩ :=
        ok_destroyBlackFunds hfork hsize' hsel hdep rfl rfl rfl rfl rfl st' hE hok
      exact ⟨⟨h4, hv⟩, ⟨hst, hacc⟩, hown, hl⟩
    exact (destroyBlackFunds_iff_gas hfork hsize' start _ hsel hdep hc0 hcL hc10 hcB hc1).mp
      (runsOk_toNat (destroyBlackFunds_specI hfork hsize' hsel hdep hc0 hcL hc10 hcB hc1 hnrB hnrT
        hG (g := gas + max (2865 + slotCost c0 + slotCost cL + slotCost c10 + slotCost cB +
          slotCost c1 + costB fork state message + costT fork state message)
          (max (3763 + slotCost c0 + slotCost cL + slotCost c10 + slotCost cB)
            (3796 + slotCost c0 + slotCost cL + slotCost c10 + slotCost cB +
              costB fork state message + slotCost c1)))
        (Nat.le_add_left _ _)) (at_addGas start _) hres hs hok)
  · rintro ⟨hG, hm⟩
    obtain ⟨s, hs, he, -⟩ := destroyBlackFunds_ok_sgm hfork hsize' start hres hsel hdep hc0 hcL
      hc10 hcB hc1 hnrB hnrT hG hm within
    exact ⟨s, hs, he⟩

end

end UsdtVerify.Exact
