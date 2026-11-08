import UsdtVerify.Evm.Iff
import UsdtVerify.Usdt.Spec.Guards
import UsdtVerify.Usdt.Complete.Read
import UsdtVerify.Usdt.Complete.Getters

/-!
# Exact success conditions of the getters

From Berlin, a fresh frame of `CODE` at pc 0 with call data below `2^256` bytes and the
selector of the getter, any gas bound and any message runner.

- `*_ok_iff`: with at least the gas of the success path, the run ends with no error if and
  only if `CallOk` holds (at least 4 bytes of call data, no value).
- `*_low`: with less gas than the success path pays, no run ends with no error.

The getters are decimals, maximumFee, _totalSupply, basisPointsRate, deprecated, paused,
upgradedAddress, owner, getOwner, MAX_UINT, balances, isBlackListed, getBlackListStatus and
allowed; totalSupply, balanceOf and allowance take `hdep` (not deprecated); name and symbol take
`StrForm` of their slot word, and their gas is `strCost`.
-/

namespace UsdtVerify.Exact

open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open UsdtVerify.Gas
open Complete StringsGen

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate} {bound : Nat} {runChild : MessageRunner fork Nat bound}
  {evm : Evm fork Nat} {gas : Nat}

/-- Every run of `CODE` from pc 0 that ends with no error has `CallOk`. -/
theorem callOk_of_run (hfork : .berlin ≤ fork) (hsize' : message.data.size < 2 ^ 256)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) (s : Evm fork Nat)
    (hs : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) : CallOk message :=
  let ⟨h4, hv, _⟩ := runFrame_ok_dispatch hfork hsize' start within hs hok
  ⟨h4, hv⟩

/-- A read path that halts normally under `CallOk`: the run ends with no error exactly when
`CallOk` holds. -/
theorem read_ok_iff {cost : Nat} {out : ByteArray} {st' : State.TransactionState}
    {ss' : Substate} (hfork : .berlin ≤ fork) (hsize' : message.data.size < 2 ^ 256)
    (hspec : CallOk message → SpecG fork (At CODE message 0 [] .empty gas state substate)
      (Halted false out (gas - cost) st' ss'))
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    RunsOk fork bound runChild evm within ↔ CallOk message :=
  runsOk_iff hspec halted_false_ok start within (callOk_of_run hfork hsize' start within)

/-- A read path that halts normally under `CallOk` and pays `cost`: with less gas no run ends
with no error. -/
theorem read_low {cost : Nat} {out : ByteArray} {st' : State.TransactionState}
    {ss' : Substate} (hfork : .berlin ≤ fork) (hsize' : message.data.size < 2 ^ 256)
    (hlt : gas < cost)
    (hspec : CallOk message → ∀ g, cost ≤ g →
      SpecG fork (At CODE message 0 [] .empty g state substate)
        (Halted false out (g - cost) st' ss'))
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    ¬ RunsOk fork bound runChild evm within :=
  not_runsOk_low (Nat.le_refl _) hlt hspec start within (callOk_of_run hfork hsize' start within)

/-! ## The getters of one slot or one mapping entry -/

section

variable (hfork : .berlin ≤ fork) (hsize' : message.data.size < 2 ^ 256)
  (start : At CODE message 0 [] .empty gas state substate evm)
  (within : GasMeter.gasHeld evm.gas ≤ bound) {c : Bool}
include hfork hsize' start

/-- `decimals()` succeeds exactly when `CallOk` holds, with gas `384 + price(slot 9)`. -/
theorem decimals_ok_iff (hsel : selector message.data = 0x313ce567)
    (hc : coldIn substate message.currentTarget 9 = c) (hg : 384 + slotCost c ≤ gas) :
    RunsOk fork bound runChild evm within ↔ CallOk message :=
  read_ok_iff hfork hsize' (fun h => Getters.spec_decimals hfork h.1 hsize' hsel h.2 hc hg)
    start within

theorem decimals_low (hsel : selector message.data = 0x313ce567)
    (hc : coldIn substate message.currentTarget 9 = c) (hg : gas < 384 + slotCost c) :
    ¬ RunsOk fork bound runChild evm within :=
  read_low hfork hsize' hg (fun h _ => Getters.spec_decimals hfork h.1 hsize' hsel h.2 hc)
    start within

/-- `maximumFee()` succeeds exactly when `CallOk` holds, with gas `406 + price(slot 4)`. -/
theorem maximumFee_ok_iff (hsel : selector message.data = 0x35390714)
    (hc : coldIn substate message.currentTarget 4 = c) (hg : 406 + slotCost c ≤ gas) :
    RunsOk fork bound runChild evm within ↔ CallOk message :=
  read_ok_iff hfork hsize' (fun h => Getters.spec_maximumFee hfork h.1 hsize' hsel h.2 hc hg)
    start within

theorem maximumFee_low (hsel : selector message.data = 0x35390714)
    (hc : coldIn substate message.currentTarget 4 = c) (hg : gas < 406 + slotCost c) :
    ¬ RunsOk fork bound runChild evm within :=
  read_low hfork hsize' hg (fun h _ => Getters.spec_maximumFee hfork h.1 hsize' hsel h.2 hc)
    start within

/-- `_totalSupply()` succeeds exactly when `CallOk` holds, with gas `428 + price(slot 1)`. -/
theorem totalSupplyVar_ok_iff (hsel : selector message.data = 0x3eaaf86b)
    (hc : coldIn substate message.currentTarget 1 = c) (hg : 428 + slotCost c ≤ gas) :
    RunsOk fork bound runChild evm within ↔ CallOk message :=
  read_ok_iff hfork hsize' (fun h => Getters.spec_totalSupplyVar hfork h.1 hsize' hsel h.2 hc hg)
    start within

theorem totalSupplyVar_low (hsel : selector message.data = 0x3eaaf86b)
    (hc : coldIn substate message.currentTarget 1 = c) (hg : gas < 428 + slotCost c) :
    ¬ RunsOk fork bound runChild evm within :=
  read_low hfork hsize' hg (fun h _ => Getters.spec_totalSupplyVar hfork h.1 hsize' hsel h.2 hc)
    start within

/-- `basisPointsRate()` succeeds exactly when `CallOk` holds, with gas `758 + price(slot 3)`. -/
theorem basisPointsRate_ok_iff (hsel : selector message.data = 0xdd644f72)
    (hc : coldIn substate message.currentTarget 3 = c) (hg : 758 + slotCost c ≤ gas) :
    RunsOk fork bound runChild evm within ↔ CallOk message :=
  read_ok_iff hfork hsize'
    (fun h => Getters.spec_basisPointsRate hfork h.1 hsize' hsel h.2 hc hg) start within

theorem basisPointsRate_low (hsel : selector message.data = 0xdd644f72)
    (hc : coldIn substate message.currentTarget 3 = c) (hg : gas < 758 + slotCost c) :
    ¬ RunsOk fork bound runChild evm within :=
  read_low hfork hsize' hg
    (fun h _ => Getters.spec_basisPointsRate hfork h.1 hsize' hsel h.2 hc) start within

/-- `deprecated()` succeeds exactly when `CallOk` holds, with gas `350 + price(slot 10)`. -/
theorem deprecated_ok_iff (hsel : selector message.data = 0x0e136b19)
    (hc : coldIn substate message.currentTarget 10 = c) (hg : 350 + slotCost c ≤ gas) :
    RunsOk fork bound runChild evm within ↔ CallOk message :=
  read_ok_iff hfork hsize' (fun h => Getters.spec_deprecated hfork h.1 hsize' hsel h.2 hc hg)
    start within

theorem deprecated_low (hsel : selector message.data = 0x0e136b19)
    (hc : coldIn substate message.currentTarget 10 = c) (hg : gas < 350 + slotCost c) :
    ¬ RunsOk fork bound runChild evm within :=
  read_low hfork hsize' hg (fun h _ => Getters.spec_deprecated hfork h.1 hsize' hsel h.2 hc)
    start within

/-- `paused()` succeeds exactly when `CallOk` holds, with gas `614 + price(slot 0)`. -/
theorem paused_ok_iff (hsel : selector message.data = 0x5c975abb)
    (hc : coldIn substate message.currentTarget 0 = c) (hg : 614 + slotCost c ≤ gas) :
    RunsOk fork bound runChild evm within ↔ CallOk message :=
  read_ok_iff hfork hsize' (fun h => Getters.spec_paused hfork h.1 hsize' hsel h.2 hc hg)
    start within

theorem paused_low (hsel : selector message.data = 0x5c975abb)
    (hc : coldIn substate message.currentTarget 0 = c) (hg : gas < 614 + slotCost c) :
    ¬ RunsOk fork bound runChild evm within :=
  read_low hfork hsize' hg (fun h _ => Getters.spec_paused hfork h.1 hsize' hsel h.2 hc)
    start within

/-- `upgradedAddress()` succeeds exactly when `CallOk` holds, with gas `388 + price(slot 10)`. -/
theorem upgradedAddress_ok_iff (hsel : selector message.data = 0x26976e3f)
    (hc : coldIn substate message.currentTarget 10 = c) (hg : 388 + slotCost c ≤ gas) :
    RunsOk fork bound runChild evm within ↔ CallOk message :=
  read_ok_iff hfork hsize'
    (fun h => Getters.spec_upgradedAddress hfork h.1 hsize' hsel h.2 hc hg) start within

theorem upgradedAddress_low (hsel : selector message.data = 0x26976e3f)
    (hc : coldIn substate message.currentTarget 10 = c) (hg : gas < 388 + slotCost c) :
    ¬ RunsOk fork bound runChild evm within :=
  read_low hfork hsize' hg
    (fun h _ => Getters.spec_upgradedAddress hfork h.1 hsize' hsel h.2 hc) start within

/-- `owner()` succeeds exactly when `CallOk` holds, with gas `652 + price(slot 0)`. -/
theorem owner_ok_iff (hsel : selector message.data = 0x8da5cb5b)
    (hc : coldIn substate message.currentTarget 0 = c) (hg : 652 + slotCost c ≤ gas) :
    RunsOk fork bound runChild evm within ↔ CallOk message :=
  read_ok_iff hfork hsize' (fun h => Getters.spec_owner hfork h.1 hsize' hsel h.2 hc hg)
    start within

theorem owner_low (hsel : selector message.data = 0x8da5cb5b)
    (hc : coldIn substate message.currentTarget 0 = c) (hg : gas < 652 + slotCost c) :
    ¬ RunsOk fork bound runChild evm within :=
  read_low hfork hsize' hg (fun h _ => Getters.spec_owner hfork h.1 hsize' hsel h.2 hc)
    start within

/-- `getOwner()` succeeds exactly when `CallOk` holds, with gas `638 + price(slot 0)`. -/
theorem getOwner_ok_iff (hsel : selector message.data = 0x893d20e8)
    (hc : coldIn substate message.currentTarget 0 = c) (hg : 638 + slotCost c ≤ gas) :
    RunsOk fork bound runChild evm within ↔ CallOk message :=
  read_ok_iff hfork hsize' (fun h => Getters.spec_getOwner hfork h.1 hsize' hsel h.2 hc hg)
    start within

theorem getOwner_low (hsel : selector message.data = 0x893d20e8)
    (hc : coldIn substate message.currentTarget 0 = c) (hg : gas < 638 + slotCost c) :
    ¬ RunsOk fork bound runChild evm within :=
  read_low hfork hsize' hg (fun h _ => Getters.spec_getOwner hfork h.1 hsize' hsel h.2 hc)
    start within

/-- `MAX_UINT()` succeeds exactly when `CallOk` holds, with gas 824. -/
theorem maxUint_ok_iff (hsel : selector message.data = 0xe5b5019a) (hg : 824 ≤ gas) :
    RunsOk fork bound runChild evm within ↔ CallOk message :=
  read_ok_iff hfork hsize' (fun h => Getters.spec_maxUint h.1 hsize' hsel h.2 hg) start within

theorem maxUint_low (hsel : selector message.data = 0xe5b5019a) (hg : gas < 824) :
    ¬ RunsOk fork bound runChild evm within :=
  read_low hfork hsize' hg (fun h _ => Getters.spec_maxUint h.1 hsize' hsel h.2) start within

/-- `balances(a)` succeeds exactly when `CallOk` holds, with gas
`478 + price(balances[a])`. -/
theorem balances_ok_iff (hsel : selector message.data = 0x27e235e3)
    (hc : coldIn substate message.currentTarget (mapSlot (addrArg message.data 0) 2) = c)
    (hg : 478 + slotCost c ≤ gas) :
    RunsOk fork bound runChild evm within ↔ CallOk message :=
  read_ok_iff hfork hsize' (fun h => GettersMap.spec_balances hfork h.1 hsize' hsel h.2 hc hg)
    start within

theorem balances_low (hsel : selector message.data = 0x27e235e3)
    (hc : coldIn substate message.currentTarget (mapSlot (addrArg message.data 0) 2) = c)
    (hg : gas < 478 + slotCost c) :
    ¬ RunsOk fork bound runChild evm within :=
  read_low hfork hsize' hg (fun h _ => GettersMap.spec_balances hfork h.1 hsize' hsel h.2 hc)
    start within

/-- `isBlackListed(a)` succeeds exactly when `CallOk` holds, with gas
`933 + price(isBlackListed[a])`. -/
theorem isBlackListed_ok_iff (hsel : selector message.data = 0xe47d6060)
    (hc : coldIn substate message.currentTarget (mapSlot (addrArg message.data 0) 6) = c)
    (hg : 933 + slotCost c ≤ gas) :
    RunsOk fork bound runChild evm within ↔ CallOk message :=
  read_ok_iff hfork hsize'
    (fun h => GettersMap.spec_isBlackListed hfork h.1 hsize' hsel h.2 hc hg) start within

theorem isBlackListed_low (hsel : selector message.data = 0xe47d6060)
    (hc : coldIn substate message.currentTarget (mapSlot (addrArg message.data 0) 6) = c)
    (hg : gas < 933 + slotCost c) :
    ¬ RunsOk fork bound runChild evm within :=
  read_low hfork hsize' hg
    (fun h _ => GettersMap.spec_isBlackListed hfork h.1 hsize' hsel h.2 hc) start within

/-- `getBlackListStatus(a)` succeeds exactly when `CallOk` holds, with gas
`663 + price(isBlackListed[a])`. -/
theorem getBlackListStatus_ok_iff (hsel : selector message.data = 0x59bf1abe)
    (hc : coldIn substate message.currentTarget (mapSlot (addrArg message.data 0) 6) = c)
    (hg : 663 + slotCost c ≤ gas) :
    RunsOk fork bound runChild evm within ↔ CallOk message :=
  read_ok_iff hfork hsize'
    (fun h => GettersMap.spec_getBlackListStatus hfork h.1 hsize' hsel h.2 hc hg) start within

theorem getBlackListStatus_low (hsel : selector message.data = 0x59bf1abe)
    (hc : coldIn substate message.currentTarget (mapSlot (addrArg message.data 0) 6) = c)
    (hg : gas < 663 + slotCost c) :
    ¬ RunsOk fork bound runChild evm within :=
  read_low hfork hsize' hg
    (fun h _ => GettersMap.spec_getBlackListStatus hfork h.1 hsize' hsel h.2 hc) start within

/-- `allowed(a, b)` succeeds exactly when `CallOk` holds, with gas
`705 + price(allowed[a][b])`. -/
theorem allowed_ok_iff (hsel : selector message.data = 0x5c658165)
    (hc : coldIn substate message.currentTarget (GettersMap.allowSlot message.data) = c)
    (hg : 705 + slotCost c ≤ gas) :
    RunsOk fork bound runChild evm within ↔ CallOk message :=
  read_ok_iff hfork hsize' (fun h => GettersMap.spec_allowed hfork h.1 hsize' hsel h.2 hc hg)
    start within

theorem allowed_low (hsel : selector message.data = 0x5c658165)
    (hc : coldIn substate message.currentTarget (GettersMap.allowSlot message.data) = c)
    (hg : gas < 705 + slotCost c) :
    ¬ RunsOk fork bound runChild evm within :=
  read_low hfork hsize' hg (fun h _ => GettersMap.spec_allowed hfork h.1 hsize' hsel h.2 hc)
    start within

/-! ## totalSupply, balanceOf and allowance, not deprecated -/

variable {c10 : Bool}

/-- `totalSupply()`, not deprecated, succeeds exactly when `CallOk` holds, with gas
`411 + price(slot 10) + price(slot 1)`. -/
theorem totalSupply_ok_iff (hsel : selector message.data = 0x18160ddd)
    (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    (hc10 : coldIn substate message.currentTarget 10 = c10)
    (hc : coldIn substate message.currentTarget 1 = c)
    (hg : TotalSupply.COST + slotCost c10 + slotCost c ≤ gas) :
    RunsOk fork bound runChild evm within ↔ CallOk message :=
  read_ok_iff hfork hsize'
    (fun h => TotalSupply.spec hfork h.1 hsize' hsel h.2 hdep hc10 hc hg) start within

theorem totalSupply_low (hsel : selector message.data = 0x18160ddd)
    (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    (hc10 : coldIn substate message.currentTarget 10 = c10)
    (hc : coldIn substate message.currentTarget 1 = c)
    (hg : gas < TotalSupply.COST + slotCost c10 + slotCost c) :
    ¬ RunsOk fork bound runChild evm within :=
  read_low hfork hsize' hg
    (fun h _ => TotalSupply.spec hfork h.1 hsize' hsel h.2 hdep hc10 hc) start within

/-- `balanceOf(a)`, not deprecated, succeeds exactly when `CallOk` holds, with gas
`831 + price(slot 10) + price(balances[a])`. -/
theorem balanceOf_ok_iff (hsel : selector message.data = 0x70a08231)
    (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    (hc10 : coldIn substate message.currentTarget 10 = c10)
    (hc : coldIn (accessSlot substate message.currentTarget 10) message.currentTarget
      (BalanceOf.balanceSlot message.data) = c)
    (hg : BalanceOf.COST + slotCost c10 + slotCost c ≤ gas) :
    RunsOk fork bound runChild evm within ↔ CallOk message :=
  read_ok_iff hfork hsize'
    (fun h => BalanceOf.spec hfork h.1 hsize' hsel h.2 hdep hc10 hc hg) start within

theorem balanceOf_low (hsel : selector message.data = 0x70a08231)
    (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    (hc10 : coldIn substate message.currentTarget 10 = c10)
    (hc : coldIn (accessSlot substate message.currentTarget 10) message.currentTarget
      (BalanceOf.balanceSlot message.data) = c)
    (hg : gas < BalanceOf.COST + slotCost c10 + slotCost c) :
    ¬ RunsOk fork bound runChild evm within :=
  read_low hfork hsize' hg
    (fun h _ => BalanceOf.spec hfork h.1 hsize' hsel h.2 hdep hc10 hc) start within

/-- `allowance(a, b)`, not deprecated, succeeds exactly when `CallOk` holds, with gas
`1156 + price(slot 10) + price(allowed[a][b])`. -/
theorem allowance_ok_iff (hsel : selector message.data = 0xdd62ed3e)
    (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    (hc10 : coldIn substate message.currentTarget 10 = c10)
    (hc : coldIn (accessSlot substate message.currentTarget 10) message.currentTarget
      (GettersMap.allowSlot message.data) = c)
    (hg : 1156 + slotCost c10 + slotCost c ≤ gas) :
    RunsOk fork bound runChild evm within ↔ CallOk message :=
  read_ok_iff hfork hsize'
    (fun h => GettersMap.spec_allowance hfork h.1 hsize' hsel h.2 hdep hc10 hc hg) start within

theorem allowance_low (hsel : selector message.data = 0xdd62ed3e)
    (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    (hc10 : coldIn substate message.currentTarget 10 = c10)
    (hc : coldIn (accessSlot substate message.currentTarget 10) message.currentTarget
      (GettersMap.allowSlot message.data) = c)
    (hg : gas < 1156 + slotCost c10 + slotCost c) :
    ¬ RunsOk fork bound runChild evm within :=
  read_low hfork hsize' hg
    (fun h _ => GettersMap.spec_allowance hfork h.1 hsize' hsel h.2 hdep hc10 hc) start within

end

/-! ## name() and symbol() -/

/-- The gas of the success path of `name()` (`t = 1`, `e = 643`, `sh = 1010`, slot `k = 7`) or
`symbol()` (`t = 21`, `e = 1083`, `sh = 1450`, slot `k = 8`), for the slot word `w` of a string
whose slot is priced by `c`: `e + price(slot k)` for the empty string (low byte 0), `sh +
price(slot k)` for a short one (low byte not 0 and even), and the cost of the long path (odd
`w`, `w / 2` bytes, read from the slots from `keccak(k)` on). -/
def strCost (t e sh : Nat) (k : U256) (substate : Substate) (C : EthLib.Base.Address) (w : U256)
    (c : Bool) : Nat :=
  if w.toNat % 256 = 0 then e + slotCost c
  else if w.toNat % 2 = 0 then sh + slotCost c
  else 62 + 22 * t + 34 + (102 + slotCost c) + 281 +
    (50 * ((w.toNat / 2 + 31) / 32 - 1) + 96 +
      rdGas (accessSlot substate C k) C (keccak (wordBytes k)) ((w.toNat / 2 + 31) / 32) +
      (mg (128 + 32 * ((w.toNat / 2 + 31) / 32)) - mg 128)) +
    retCost (128 + 32 * ((w.toNat / 2 + 31) / 32)) (w.toNat / 2)

section

variable {t e sh : Nat} {k : U256} {C : EthLib.Base.Address} {w : U256} {c : Bool}

theorem strCost_empty (h : w.toNat % 256 = 0) : strCost t e sh k substate C w c = e + slotCost c :=
  by simp [strCost, h]

theorem strCost_short {n : Nat} (h : w.toNat % 256 = 2 * n) (h1 : 1 ≤ n) :
    strCost t e sh k substate C w c = sh + slotCost c := by
  have h0 : ¬ w.toNat % 256 = 0 := by omega
  have h2 : w.toNat % 2 = 0 := by omega
  simp [strCost, h0, h2]

theorem strCost_long (h : w.toNat % 2 = 1) :
    strCost t e sh k substate C w c = 62 + 22 * t + 34 + (102 + slotCost c) + 281 +
      (50 * ((w.toNat / 2 + 31) / 32 - 1) + 96 +
        rdGas (accessSlot substate C k) C (keccak (wordBytes k)) ((w.toNat / 2 + 31) / 32) +
        (mg (128 + 32 * ((w.toNat / 2 + 31) / 32)) - mg 128)) +
      retCost (128 + 32 * ((w.toNat / 2 + 31) / 32)) (w.toNat / 2) := by
  have h0 : ¬ w.toNat % 256 = 0 := by omega
  have h2 : ¬ w.toNat % 2 = 0 := by omega
  simp only [strCost, h0, h2, ite_false]

end

section

variable (hfork : .berlin ≤ fork) (hsize' : message.data.size < 2 ^ 256)
  (start : At CODE message 0 [] .empty gas state substate evm)
  (within : GasMeter.gasHeld evm.gas ≤ bound) {c : Bool}
include hfork hsize' start

/-- `name()`, for a slot word of `StrForm`, succeeds exactly when `CallOk` holds, with gas
`strCost 1 643 1010 7`. -/
theorem name_ok_iff (hsel : selector message.data = 0x06fdde03)
    (hform : StrForm (storageAt state message.currentTarget 7))
    (hc : coldIn substate message.currentTarget 7 = c)
    (hg : strCost 1 643 1010 7 substate message.currentTarget
      (storageAt state message.currentTarget 7) c ≤ gas) :
    RunsOk fork bound runChild evm within ↔ CallOk message := by
  rcases hform with h0 | ⟨n, hn, h1, h31⟩ | ⟨hodd, h32, hN⟩
  · rw [strCost_empty h0] at hg
    exact read_ok_iff hfork hsize'
      (fun h => spec_nameEmpty hfork h.1 hsize' hsel h.2 h0 hc hg) start within
  · rw [strCost_short hn h1] at hg
    exact read_ok_iff hfork hsize'
      (fun h => Strings.spec_name hfork h.1 hsize' hsel h.2 hn h1 h31 hc hg) start within
  · rw [strCost_long hodd] at hg
    exact read_ok_iff hfork hsize'
      (fun h => spec_nameLong hfork h.1 hsize' hsel h.2 hodd rfl h32 hN hc hg) start within

theorem name_low (hsel : selector message.data = 0x06fdde03)
    (hform : StrForm (storageAt state message.currentTarget 7))
    (hc : coldIn substate message.currentTarget 7 = c)
    (hg : gas < strCost 1 643 1010 7 substate message.currentTarget
      (storageAt state message.currentTarget 7) c) :
    ¬ RunsOk fork bound runChild evm within := by
  rcases hform with h0 | ⟨n, hn, h1, h31⟩ | ⟨hodd, h32, hN⟩
  · rw [strCost_empty h0] at hg
    exact read_low hfork hsize' hg
      (fun h _ => spec_nameEmpty hfork h.1 hsize' hsel h.2 h0 hc) start within
  · rw [strCost_short hn h1] at hg
    exact read_low hfork hsize' hg
      (fun h _ => Strings.spec_name hfork h.1 hsize' hsel h.2 hn h1 h31 hc) start within
  · rw [strCost_long hodd] at hg
    exact read_low hfork hsize' hg
      (fun h _ => spec_nameLong hfork h.1 hsize' hsel h.2 hodd rfl h32 hN hc) start within

/-- `symbol()`, for a slot word of `StrForm`, succeeds exactly when `CallOk` holds, with gas
`strCost 21 1083 1450 8`. -/
theorem symbol_ok_iff (hsel : selector message.data = 0x95d89b41)
    (hform : StrForm (storageAt state message.currentTarget 8))
    (hc : coldIn substate message.currentTarget 8 = c)
    (hg : strCost 21 1083 1450 8 substate message.currentTarget
      (storageAt state message.currentTarget 8) c ≤ gas) :
    RunsOk fork bound runChild evm within ↔ CallOk message := by
  rcases hform with h0 | ⟨n, hn, h1, h31⟩ | ⟨hodd, h32, hN⟩
  · rw [strCost_empty h0] at hg
    exact read_ok_iff hfork hsize'
      (fun h => spec_symbolEmpty hfork h.1 hsize' hsel h.2 h0 hc hg) start within
  · rw [strCost_short hn h1] at hg
    exact read_ok_iff hfork hsize'
      (fun h => Strings.spec_symbol hfork h.1 hsize' hsel h.2 hn h1 h31 hc hg) start within
  · rw [strCost_long hodd] at hg
    exact read_ok_iff hfork hsize'
      (fun h => spec_symbolLong hfork h.1 hsize' hsel h.2 hodd rfl h32 hN hc hg) start within

theorem symbol_low (hsel : selector message.data = 0x95d89b41)
    (hform : StrForm (storageAt state message.currentTarget 8))
    (hc : coldIn substate message.currentTarget 8 = c)
    (hg : gas < strCost 21 1083 1450 8 substate message.currentTarget
      (storageAt state message.currentTarget 8) c) :
    ¬ RunsOk fork bound runChild evm within := by
  rcases hform with h0 | ⟨n, hn, h1, h31⟩ | ⟨hodd, h32, hN⟩
  · rw [strCost_empty h0] at hg
    exact read_low hfork hsize' hg
      (fun h _ => spec_symbolEmpty hfork h.1 hsize' hsel h.2 h0 hc) start within
  · rw [strCost_short hn h1] at hg
    exact read_low hfork hsize' hg
      (fun h _ => Strings.spec_symbol hfork h.1 hsize' hsel h.2 hn h1 h31 hc) start within
  · rw [strCost_long hodd] at hg
    exact read_low hfork hsize' hg
      (fun h _ => spec_symbolLong hfork h.1 hsize' hsel h.2 hodd rfl h32 hN hc) start within

end

end UsdtVerify.Exact
