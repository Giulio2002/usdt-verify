import UsdtVerify.Usdt.Refill.ChainTransfer

/-!
# transferFrom over the EIP-8037 meter: the exact condition and gas through the chain of writes (round 43)

The success paths of `transferFrom(f, t, v)` not deprecated are split at their SSTOREs into cheap
stretches, and `Complete.exactS_write` is applied once per write, then `Complete.exactS_halt`.
There are four paths, by the fee (0 or above 0) and by the allowance `A` read in the state after
the checks (`A = MAX_UINT`: no allowance write; `A ≠ MAX_UINT` and `v ≤ A`: the allowance write
first):

- `transferFrom_max_sgm` (fee 0, `A = MAX_UINT`): writes `balances[f]`, `balances[t]`.
- `transferFrom_sgm` (fee 0, `A ≠ MAX_UINT`): writes the allowance, `balances[f]`, `balances[t]`.
- `transferFromFee_max_sgm` (fee above 0, `A = MAX_UINT`): writes `balances[f]`, `balances[t]`,
  `balances[owner]`.
- `transferFromFee_sgm` (fee above 0, `A ≠ MAX_UINT`): the four writes.

Each: from a frame with any meter, for any gas bound and message runner, under the hypotheses of
`spec_ok` (fee 0) or `spec_feeF` (fee above 0) except the gas, with the branch of the allowance
fixed, the run ends with no error if and only if `wOk` holds for each write from the meter after
the previous one (`wMeter`) and the gas of the tail is at most the execution gas left after the
last write. A refill of one write goes to the reservoir and the spill of the meter that the next
write reads. Every run that ends with no error has the state and substate of the Nat
specification, `gasLeft` plus its gas (`okCostF` or `feeCostF`) equal to `gas` plus the bumps of
the writes (`wBump`), and the meter after the last write for the rest.

No hypothesis on refills or on the reservoir.
-/

namespace UsdtVerify.TransferFrom
open EthLib.Base (Fork U256 Address)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts
open Transfer SafeMath TransferOk
open Complete (wBump wSgm wOk wMeter)
variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate}

/-- From 8648 to the allowance step at 8834 (the reads of the allowance, slot 3 and slot 4, and
the fee of 0). -/
theorem segA (hfork : .berlin ≤ fork)
    {v t f sel : U256} {M : ByteArray} (hM : M.size = 96)
    (hov : v.toNat * (storageAt state message.currentTarget 3).toNat < 2 ^ 256)
    (hfee : feeOf state message v = 0)
    {cA c3 c4 : Bool}
    (hcA : coldIn substate message.currentTarget (allowFrom message f) = cA)
    (hc3 : coldIn (accessSlot substate message.currentTarget (allowFrom message f))
      message.currentTarget 3 = c3)
    (hc4 : coldIn (accessSlot (accessSlot substate message.currentTarget (allowFrom message f))
      message.currentTarget 3) message.currentTarget 4 = c4)
    {gas : Nat} (hg : 361 + slotCost cA + slotCost c3 + slotCost c4 + mulCost v +
      capCost (rawFee state message v) (storageAt state message.currentTarget 4) ≤ gas) :
    Gas.HoareG fork (At CODE message 8648 [0x60, 0, 0, 0, v, t, f, 0x1097, v, t, f, 0x0392, sel] M gas
        state substate)
      (At CODE message 8834 [0x60, 0, 0, allowOf state message f, v, t, f, 0x1097, v, t, f, 0x0392,
          sel] (allowMem message M f)
        (gas - (361 + slotCost cA + slotCost c3 + slotCost c4 + mulCost v +
          capCost (rawFee state message v) (storageAt state message.currentTarget 4)))
        (readsF state message f) (accessF substate message f)) := by
  simp only [rawFee, feeOf] at hfee hg ⊢
  step allowRead hfork (by simp) hcA (by gas_ok) hM
  step feeCall hfork (by simp) hc3 (by gas_ok)
  step mulBlock (by simp) (by valid_dest) (by simpa only [storageAt_readSlot] using hov)
    (by gas_ok)
  at_pc 8802
  step divCall (by simp) (by gas_ok)
  step divBlock (by simp) (by valid_dest) (by decide) (by gas_ok)
  at_pc 8816
  step capBlock hfork (by simp) hc4 (by simp only [storageAt_readSlot]; gas_ok)
  simp only [storageAt_readSlot]
  step Gas.reshapeG (s' := (0x60 : U256) :: 0 :: 0 ::
      storageAt state message.currentTarget (allowFrom message f) :: v :: t :: f ::
      [0x1097, v, t, f, 0x0392, sel]) (by rw [hfee]) rfl rfl
  exact restate rfl rfl rfl (by gas_ok) rfl rfl

/-- At 8834 with `_allowance = A ≠ MAX_UINT` and `v ≤ A`: to the `SSTORE` of the allowance at
9020. -/
theorem allowToW {fee A v t f : U256} {rest : List U256} (hrest : rest.length ≤ 8)
    (hmax : A ≠ MAX_UINT) (hle : v.toNat ≤ A.toNat) {gas : Nat} (hg : 318 ≤ gas) {M : ByteArray}
    (hM : M.size = 96) :
    Gas.HoareG fork (At CODE message 8834 (0x60 :: 0 :: fee :: A :: v :: t :: f :: rest) M gas state
        substate)
      (At CODE message 9020 (allowFrom message f :: sub A v :: sub A v :: 0x60 :: 0 :: fee :: A ::
          v :: t :: f :: rest) (allowMem message M f) (gas - 318) state substate) := by
  have hlt : A.toNat < 2 ^ 256 - 1 := by
    have h1 := A.isLt
    have h2 : A.toNat ≠ MAX_UINT.toNat := fun h => hmax (BitVec.eq_of_toNat_eq h)
    have h3 : MAX_UINT.toNat = 2 ^ 256 - 1 := by decide
    omega
  simp only [allowFrom, allowMem, mkey]
  allow_pre
  exact restate (by decide) rfl rfl (by gas_ok) rfl rfl

/-- At 8834 with `_allowance = MAX_UINT`: no write, on to 9022. -/
theorem allowMax {fee v t f : U256} {rest : List U256} (hrest : rest.length ≤ 8) {gas : Nat}
    (hg : 26 ≤ gas) {M : ByteArray} :
    Gas.HoareG fork (At CODE message 8834 (0x60 :: 0 :: fee :: MAX_UINT :: v :: t :: f :: rest) M
        gas state substate)
      (At CODE message 9022 (0x60 :: 0 :: fee :: MAX_UINT :: v :: t :: f :: rest) M (gas - 26)
        state substate) := by
  step jumpdestR
  step pushR 32 MAX_UINT
  step dupR 4
  step binR 0x10 Local.instruction_lt
  step unR 0x15 instruction_iszero
  step pushR 2 (0x233e : U256)
  step jumpiR (by decide)
  exact (repc (by decide)).seq (Gas.reshapeG rfl rfl (by gas_ok))

/-- At 9125: from the `JUMPDEST` to the `SSTORE` of `balances[_from]` at 9191. -/
theorem debitToWF {nb send fee A v t f : U256} {rest : List U256} (hrest : rest.length ≤ 8)
    {gas : Nat} (hg : 100 ≤ gas) {M : ByteArray} (hM : M.size = 96) :
    Gas.HoareG fork (At CODE message 9125 (nb :: 0x60 :: send :: fee :: A :: v :: t :: f :: rest) M
        gas state substate)
      (At CODE message 9191 (recipientSlot f :: nb :: nb :: 0x60 :: send :: fee :: A :: v :: t ::
          f :: rest) (mapMem M (mkey f) 2) (gas - 100) state substate) := by
  simp only [recipientSlot, mkey]
  debitF_pre
  exact restate (by decide) rfl rfl (by gas_ok) rfl rfl

/-- From 9022 (fee 0) to the `SSTORE` of `balances[_from]` at 9191. -/
theorem toDebitW (hfork : .berlin ≤ fork) {A v t f sel : U256}
    (hbal : v.toNat ≤ (storageAt state message.currentTarget (recipientSlot f)).toNat)
    {cF : Bool} (hcF : coldIn substate message.currentTarget (recipientSlot f) = cF) {gas : Nat}
    (hg : 403 + slotCost cF ≤ gas) {M : ByteArray} (hM : M.size = 96) :
    Gas.HoareG fork (At CODE message 9022 (0x60 :: 0 :: 0 :: A :: v :: t :: f :: [0x1097, v, t, f, 0x0392, sel]) M gas state
        substate)
      (At CODE message 9191 (recipientSlot f ::
          sub (storageAt state message.currentTarget (recipientSlot f)) v ::
          sub (storageAt state message.currentTarget (recipientSlot f)) v ::
          0x60 :: v :: 0 :: A :: v :: t :: f :: [0x1097, v, t, f, 0x0392, sel])
        (mapMem (mapMem M (mkey f) 2) (mkey f) 2) (gas - (403 + slotCost cF))
        (readSlot state message.currentTarget (recipientSlot f))
        (accessSlot substate message.currentTarget (recipientSlot f))) := by
  step sendCall (by simp) (by gas_ok)
  step subBlock (by simp) (by valid_dest) (by simp) (by gas_ok)
  at_pc 9041
  step Gas.reshapeG (s' := v :: (0x60 : U256) :: 0 :: 0 :: A :: v :: t :: f :: [0x1097, v, t, f, 0x0392, sel])
    (by simp [sub]) rfl rfl
  step debitCall hfork (by simp) hcF (by gas_ok) hM
  step subBlock (by simp) (by valid_dest) (by simpa only [storageAt_readSlot] using hbal) (by gas_ok)
  at_pc 9125
  refine Triple.seq (debitToWF (by simp) (by gas_ok) (size_mapMem hM _ _)) ?_
  exact restate rfl rfl rfl (by gas_ok) rfl rfl

/-- At 9274: from the `JUMPDEST` to the `SSTORE` of `balances[_to]` at 9340. -/
theorem creditToWF {nt send fee A v t f : U256} {rest : List U256} (hrest : rest.length ≤ 8)
    {gas : Nat} (hg : 100 ≤ gas) {M : ByteArray} (hM : M.size = 96) :
    Gas.HoareG fork (At CODE message 9274 (nt :: 0x60 :: send :: fee :: A :: v :: t :: f :: rest) M
        gas state substate)
      (At CODE message 9340 (recipientSlot t :: nt :: nt :: 0x60 :: send :: fee :: A :: v :: t ::
          f :: rest) (mapMem M (mkey t) 2) (gas - 100) state substate) := by
  simp only [recipientSlot, mkey]
  step jumpdestR
  step pushR 1 (0x02 : U256)
  step pushR 1 (0 : U256)
  step dupR 8
  at_pc 9280
  step hashTail (by decide) (by simp; omega) hM (by gas_ok)
  at_pc 9338
  step dupR 1
  step swapR 0
  norm
  exact restate (by decide) rfl rfl (by gas_ok) rfl rfl

/-- At 8834 with `_allowance = MAX_UINT` (fee 0): to the `SSTORE` of `balances[_from]` at 9191. -/
theorem maxToDebitW (hfork : .berlin ≤ fork) {v t f sel : U256}
    (hbal : v.toNat ≤ (storageAt state message.currentTarget (recipientSlot f)).toNat)
    {cF : Bool} (hcF : coldIn substate message.currentTarget (recipientSlot f) = cF) {gas : Nat}
    (hg : 429 + slotCost cF ≤ gas) {M : ByteArray} (hM : M.size = 96) :
    Gas.HoareG fork (At CODE message 8834 [0x60, 0, 0, MAX_UINT, v, t, f, 0x1097, v, t, f, 0x0392,
        sel] M gas state substate)
      (At CODE message 9191 (recipientSlot f ::
          sub (storageAt state message.currentTarget (recipientSlot f)) v ::
          sub (storageAt state message.currentTarget (recipientSlot f)) v ::
          [0x60, v, 0, MAX_UINT, v, t, f, 0x1097, v, t, f, 0x0392, sel])
        (mapMem (mapMem M (mkey f) 2) (mkey f) 2) (gas - (429 + slotCost cF))
        (readSlot state message.currentTarget (recipientSlot f))
        (accessSlot substate message.currentTarget (recipientSlot f))) := by
  refine Triple.seq (allowMax (by simp) (by omega)) ?_
  refine (toDebitW hfork hbal hcF (by omega) hM).consequence (fun _ h => h) ?_
  intro e he
  have hx : gas - 26 - (403 + slotCost cF) = gas - (429 + slotCost cF) := by omega
  rw [hx] at he
  exact he

/-- From the `POP` at 9021 after the allowance's `SSTORE` (fee 0) to the `SSTORE` of
`balances[_from]` at 9191. -/
theorem allowToDebitW (hfork : .berlin ≤ fork) {A v t f sel b : U256}
    (hbal : v.toNat ≤ (storageAt state message.currentTarget (recipientSlot f)).toNat)
    {cF : Bool} (hcF : coldIn substate message.currentTarget (recipientSlot f) = cF) {gas : Nat}
    (hg : 405 + slotCost cF ≤ gas) {M : ByteArray} (hM : M.size = 96) :
    Gas.HoareG fork (At CODE message 9021 [b, 0x60, 0, 0, A, v, t, f, 0x1097, v, t, f, 0x0392,
        sel] M gas state substate)
      (At CODE message 9191 (recipientSlot f ::
          sub (storageAt state message.currentTarget (recipientSlot f)) v ::
          sub (storageAt state message.currentTarget (recipientSlot f)) v ::
          [0x60, v, 0, A, v, t, f, 0x1097, v, t, f, 0x0392, sel])
        (mapMem (mapMem M (mkey f) 2) (mkey f) 2) (gas - (405 + slotCost cF))
        (readSlot state message.currentTarget (recipientSlot f))
        (accessSlot substate message.currentTarget (recipientSlot f))) := by
  refine Triple.seq (Gas.Triple.seqL popR (restate (pc' := 9022) (by decide) rfl rfl
    (g' := gas - 2) (by gas_ok) rfl rfl)) ?_
  refine (toDebitW hfork hbal hcF (by omega) hM).consequence (fun _ h => h) ?_
  intro e he
  have hx : gas - 2 - (403 + slotCost cF) = gas - (405 + slotCost cF) := by omega
  rw [hx] at he
  exact he

/-- From the `POP` at 9192 after the `SSTORE` of `balances[_from]` to the `SSTORE` of
`balances[_to]` at 9340 (fee 0). -/
theorem debitToCreditW (hfork : .berlin ≤ fork) {nb A v t f sel : U256} {M : ByteArray}
    (hM : M.size = 96)
    (hto : (storageAt state message.currentTarget (recipientSlot t)).toNat + v.toNat < 2 ^ 256)
    {cT : Bool} (hcT : coldIn substate message.currentTarget (recipientSlot t) = cT) {gas : Nat}
    (hg : 308 + slotCost cT ≤ gas) :
    Gas.HoareG fork (At CODE message 9192 [nb, 0x60, v, 0, A, v, t, f, 0x1097, v, t, f, 0x0392, sel]
        M gas state substate)
      (At CODE message 9340 (recipientSlot t ::
          add (storageAt state message.currentTarget (recipientSlot t)) v ::
          add (storageAt state message.currentTarget (recipientSlot t)) v ::
          [0x60, v, 0, A, v, t, f, 0x1097, v, t, f, 0x0392, sel])
        (mapMem (mapMem M (mkey t) 2) (mkey t) 2) (gas - (308 + slotCost cT))
        (readSlot state message.currentTarget (recipientSlot t))
        (accessSlot substate message.currentTarget (recipientSlot t))) := by
  refine Triple.seq (Gas.Triple.seqL popR (restate (pc' := 9193) (by decide) rfl rfl
    (g' := gas - 2) (by gas_ok) rfl rfl)) ?_
  step creditCall hfork (by simp) (cT := cT) hcT (by gas_ok) hM
  step addBlock (by simp) (by valid_dest) (by simpa using hto) (by gas_ok)
  at_pc 9274
  refine Triple.seq (creditToWF (by simp) (by gas_ok) (size_mapMem hM _ _)) ?_
  exact restate rfl rfl rfl (by gas_ok) rfl rfl

/-- From the `POP` at 9341 after the `SSTORE` of `balances[_to]` (fee 0) to the STOP. -/
theorem creditPostF {nt A v t f sel : U256} (hstatic : message.isStatic = false) {M : ByteArray}
    (hM : M.size = 96) (hptr : loadWord (memoryReadBytes M 64 32) 0 32 = 0x60) {gas : Nat}
    (hg : 1899 ≤ gas) :
    Gas.SpecG fork (At CODE message 9341 [nt, 0x60, v, 0, A, v, t, f, 0x1097, v, t, f, 0x0392, sel]
        M gas state substate)
      (Halted false .empty (gas - 1899) state
        { substate with logs := substate.logs.push (transferLog message.currentTarget
          (bitwiseAnd ADDR_MASK f) (bitwiseAnd ADDR_MASK t) v) }) := by
  step popR
  step pushR 1 (0 : U256)
  step dupR 3
  step binR 0x11 Local.instruction_gt
  step unR 0x15 instruction_iszero
  step pushR 2 (0x25e4 : U256)
  step jumpiR (by decide)
  at_pc 9700
  step logBlock (by simp) hstatic (by gas_ok) hM hptr
  refine (endBlock (by gas_ok)).consequence (fun _ h => h) ?_
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  exact ⟨hr, he, ho, by rw [hgas]; gas_ok, hs, hss⟩

/-- The execution gas from pc 0 to the `SSTORE` of `balances[_from]` in `transferFrom` with a
fee of 0 and `_allowance = MAX_UINT`. -/
abbrev fxP1 (state : State.TransactionState) (message : Message fork)
    (c0 cB c10 cA c3 c4 cF : Bool) : Nat :=
  PRE_COST_F + slotCost c0 + slotCost cB + slotCost c10 + (790 + slotCost cA + slotCost c3 +
    slotCost c4 + slotCost cF + mulCost (valArg message) +
    capCost (rawFee (checkState state message) message (valArg message))
      (storageAt (checkState state message) message.currentTarget 4))

/-- The meter after the write of `balances[_from]` (fee 0, `_allowance = MAX_UINT`). -/
abbrev fxM1 (fork : Fork) (g : StateGasMeter) (state : State.TransactionState)
    (message : Message fork) (c0 cB c10 cA c3 c4 cF : Bool) : StateGasMeter :=
  wMeter fork g (fxP1 state message c0 cB c10 cA c3 c4 cF)
    (originalAt (checkState state message) message.currentTarget (recipientSlot (fromArg message)))
    (balFrom (checkState state message) message (valArg message) (fromArg message))
    (sub (balFrom (checkState state message) message (valArg message) (fromArg message))
      (valArg message)) false

/-- The meter after the write of `balances[_to]` (fee 0, `_allowance = MAX_UINT`). -/
abbrev fxM2 (fork : Fork) (g : StateGasMeter) (state : State.TransactionState)
    (message : Message fork) (c0 cB c10 cA c3 c4 cF cT : Bool) : StateGasMeter :=
  wMeter fork (fxM1 fork g state message c0 cB c10 cA c3 c4 cF) (308 + slotCost cT)
    (originalAt (checkState state message) message.currentTarget (recipientSlot (toArg message)))
    (balTo (checkState state message) message (valArg message) (toArg message) (fromArg message))
    (add (balTo (checkState state message) message (valArg message) (toArg message)
      (fromArg message)) (valArg message)) false

/-- **transferFrom(f, t, v), fee 0, allowance `MAX_UINT`, over the EIP-8037 meter, exactly, at any
reservoir, refills allowed.** Two writes: `balances[f]` then `balances[t]`. The run ends with no
error if and only if the chain condition holds; every run that ends with no error has the state
and substate of `spec_ok`, with `gasLeft + okCostF = gas` plus the two bumps. -/
theorem transferFrom_max_sgm (hfork : .berlin ≤ fork)
    (hstatic : message.isStatic = false) (hacc : hasAccount state message.currentTarget)
    (hlong : 100 ≤ message.data.size) (hsz : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x23b872dd) (hv : message.value = 0)
    (hnp : byte20 (storageAt state message.currentTarget 0) = 0)
    (hnb : (storageAt state message.currentTarget (blackFrom (fromArg message))).toNat % 256 = 0)
    (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    (hov : (valArg message).toNat *
      (storageAt (checkState state message) message.currentTarget 3).toNat < 2 ^ 256)
    (hfee : feeOf (checkState state message) message (valArg message) = 0)
    (hmax : allowOf (checkState state message) message (fromArg message) = MAX_UINT)
    (hbal : (valArg message).toNat ≤
      (balFrom (checkState state message) message (valArg message) (fromArg message)).toNat)
    (hto : (balTo (checkState state message) message (valArg message) (toArg message)
      (fromArg message)).toNat + (valArg message).toNat < 2 ^ 256)
    {c0 cB c10 cA c3 c4 cF cT : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hcB : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget
      (blackFrom (fromArg message)) = cB)
    (hc10 : coldIn (accessSlot (accessSlot substate message.currentTarget 0) message.currentTarget
      (blackFrom (fromArg message))) message.currentTarget 10 = c10)
    (hcA : coldIn (checkSub substate message) message.currentTarget
      (allowFrom message (fromArg message)) = cA)
    (hc3 : coldIn (accessSlot (checkSub substate message) message.currentTarget
      (allowFrom message (fromArg message))) message.currentTarget 3 = c3)
    (hc4 : coldIn (accessSlot (accessSlot (checkSub substate message) message.currentTarget
      (allowFrom message (fromArg message))) message.currentTarget 3) message.currentTarget 4 = c4)
    (hcF : coldIn (allowedSubF fork (checkSub substate message) (checkState state message) message
      (valArg message) (fromArg message)) message.currentTarget (recipientSlot (fromArg message)) =
        cF)
    (hcT : coldIn (accessSlot (allowedSubF fork (checkSub substate message)
      (checkState state message) message (valArg message) (fromArg message)) message.currentTarget
      (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (toArg message)) = cT)
    {gas : Nat} {m : Evm fork StateGasMeter}
    (start : At CODE message 0 [] .empty gas state substate (Meter.toNat m))
    {bound : Nat} {runChild : MessageRunner fork StateGasMeter bound}
    (within : GasMeter.gasHeld m.gas ≤ bound) :
    (Shadow.RunsOkS fork bound runChild m within ↔
      wOk fork m.gas (fxP1 state message c0 cB c10 cA c3 c4 cF)
          (originalAt (checkState state message) message.currentTarget
            (recipientSlot (fromArg message)))
          (balFrom (checkState state message) message (valArg message) (fromArg message))
          (sub (balFrom (checkState state message) message (valArg message) (fromArg message))
            (valArg message)) false ∧
      wOk fork (fxM1 fork m.gas state message c0 cB c10 cA c3 c4 cF) (308 + slotCost cT)
          (originalAt (checkState state message) message.currentTarget
            (recipientSlot (toArg message)))
          (balTo (checkState state message) message (valArg message) (toArg message)
            (fromArg message))
          (add (balTo (checkState state message) message (valArg message) (toArg message)
            (fromArg message)) (valArg message)) false ∧
      1899 ≤ (fxM2 fork m.gas state message c0 cB c10 cA c3 c4 cF cT).gasLeft) ∧
    ∀ s, Evm.runFrame (step fork) (step_decreases fork) bound runChild m within = .ok s →
      s.error = none →
      s.running = false ∧ s.output = .empty ∧
      s.state = creditedF (checkState state message) message (valArg message) (toArg message)
        (fromArg message) ∧
      s.substate = loggedSubF fork (checkSub substate message) (checkState state message) message
        (valArg message) (toArg message) (fromArg message) ∧
      s.gas.gasLeft + okCostF fork state message c0 cB c10 cA c3 c4 cF cT =
        gas + wBump fork m.gas
            (originalAt (checkState state message) message.currentTarget
              (recipientSlot (fromArg message)))
            (balFrom (checkState state message) message (valArg message) (fromArg message))
            (sub (balFrom (checkState state message) message (valArg message) (fromArg message))
              (valArg message)) +
          wBump fork (fxM1 fork m.gas state message c0 cB c10 cA c3 c4 cF)
            (originalAt (checkState state message) message.currentTarget
              (recipientSlot (toArg message)))
            (balTo (checkState state message) message (valArg message) (toArg message)
              (fromArg message))
            (add (balTo (checkState state message) message (valArg message) (toArg message)
              (fromArg message)) (valArg message)) ∧
      s.gas = { fxM2 fork m.gas state message c0 cB c10 cA c3 c4 cF cT with
        gasLeft := s.gas.gasLeft } := by
  have hAF : allowedF (checkState state message) message (valArg message) (fromArg message) =
      readsF (checkState state message) message (fromArg message) := by
    simp only [allowedF, allowState, hmax, ite_true]
  have eS : allowedSubF fork (checkSub substate message) (checkState state message) message
      (valArg message) (fromArg message) = accessF (checkSub substate message) message
        (fromArg message) := by
    simp only [allowedSubF, allowSub, hmax, ite_true]
  have haccS : hasAccount (checkState state message) message.currentTarget :=
    hasAccount_readSlot (hasAccount_readSlot (hasAccount_readSlot hacc))
  have hacc3 : hasAccount (readsF (checkState state message) message (fromArg message))
      message.currentTarget :=
    hasAccount_readSlot (hasAccount_readSlot (hasAccount_readSlot haccS))
  have hacc4 := hasAccount_readSlot (n := recipientSlot (fromArg message))
    (other := message.currentTarget) hacc3
  have hacc5 := hasAccount_writeSlot (n := recipientSlot (fromArg message))
    (v := sub (storageAt (readsF (checkState state message) message (fromArg message))
      message.currentTarget (recipientSlot (fromArg message))) (valArg message)) hacc4
  have hacc6 := hasAccount_readSlot (n := recipientSlot (toArg message))
    (other := message.currentTarget) hacc5
  have ec1' : storageAt (readsF (checkState state message) message (fromArg message))
      message.currentTarget (recipientSlot (fromArg message)) =
      balFrom (checkState state message) message (valArg message) (fromArg message) := by
    simp only [balFrom, hAF]
  have hP : fxP1 state message c0 cB c10 cA c3 c4 cF < 97920 := by
    have := Complete.slotCost_le c0; have := Complete.slotCost_le cB
    have := Complete.slotCost_le c10; have := Complete.slotCost_le cA
    have := Complete.slotCost_le c3; have := Complete.slotCost_le c4
    have := Complete.slotCost_le cF
    have : mulCost (valArg message) ≤ 138 := by unfold mulCost; split <;> omega
    have : capCost (rawFee (checkState state message) message (valArg message))
      (storageAt (checkState state message) message.currentTarget 4) ≤ 108 := by
      unfold capCost; split <;> omega
    simp only [fxP1, PRE_COST_F]; omega
  have hQ : 308 + slotCost cT < 97920 := by have := Complete.slotCost_le cT; omega
  have hpre : ∀ g, fxP1 state message c0 cB c10 cA c3 c4 cF ≤ g → Gas.HoareG fork
      (At CODE message 0 [] .empty g state substate)
      (At CODE message 9191 (recipientSlot (fromArg message) ::
          sub (storageAt (readsF (checkState state message) message (fromArg message))
            message.currentTarget (recipientSlot (fromArg message))) (valArg message) ::
          sub (storageAt (readsF (checkState state message) message (fromArg message))
            message.currentTarget (recipientSlot (fromArg message))) (valArg message) ::
          [0x60, valArg message, 0, MAX_UINT, valArg message, toArg message, fromArg message,
            0x1097, valArg message, toArg message, fromArg message, 0x0392,
            BitVec.ofNat 256 (selector message.data)])
        (mapMem (mapMem (allowMem message (memF message) (fromArg message))
          (mkey (fromArg message)) 2) (mkey (fromArg message)) 2)
        (g - fxP1 state message c0 cB c10 cA c3 c4 cF)
        (readSlot (readsF (checkState state message) message (fromArg message))
          message.currentTarget (recipientSlot (fromArg message)))
        (accessSlot (accessF (checkSub substate message) message (fromArg message))
          message.currentTarget (recipientSlot (fromArg message)))) := by
    intro g hg
    simp only [fxP1] at hg ⊢
    refine Triple.seq (preF hfork hlong hsz hsel hv hnp hnb hdep hc0 hcB hc10
      (Nat.le_trans (Nat.le_add_right _ _) hg)) ?_
    refine Triple.seq (segA (state := checkState state message)
      (substate := checkSub substate message) hfork (size_mapMem size_MEM0 _ _) hov hfee hcA hc3
      hc4 (by omega)) ?_
    rw [hmax]
    refine (maxToDebitW hfork (cF := cF) (by rw [ec1']; exact hbal) (by rw [← eS]; exact hcF) (by omega)
      (size_allowMem (size_mapMem size_MEM0 _ _) _)).consequence (fun _ h => h) ?_
    intro e he
    have hx : g - (PRE_COST_F + slotCost c0 + slotCost cB + slotCost c10) -
        (361 + slotCost cA + slotCost c3 + slotCost c4 + mulCost (valArg message) +
          capCost (rawFee (checkState state message) message (valArg message))
            (storageAt (checkState state message) message.currentTarget 4)) -
        (429 + slotCost cF) = g - (PRE_COST_F + slotCost c0 + slotCost cB + slotCost c10 +
          (790 + slotCost cA + slotCost c3 + slotCost c4 + slotCost cF + mulCost (valArg message) +
          capCost (rawFee (checkState state message) message (valArg message))
            (storageAt (checkState state message) message.currentTarget 4))) := by omega
    rw [hx] at he
    exact he
  have ec2' : storageAt (writeSlot (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message)) =
      balTo (checkState state message) message (valArg message) (toArg message) (fromArg message) := by
    simp only [balTo, debitedF, balFrom, hAF]
  have hcT' : coldIn (storeSub fork (accessSlot (accessF (checkSub substate message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (originalAt (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message))) (storageAt (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message))) (sub (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message)) = cT := by
    rw [coldIn_storeSub, ← eS]; exact hcT
  have hMf : (mapMem (mapMem (allowMem message (memF message) (fromArg message)) (mkey (fromArg message)) 2) (mkey (fromArg message)) 2).size = 96 :=
    size_mapMem (size_mapMem (size_allowMem (size_mapMem size_MEM0 _ _) _) _ _) _ _
  have hmid := fun g (hg : 308 + slotCost cT ≤ g) => debitToCreditW (state := (writeSlot (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) (valArg message))))
    (substate := (storeSub fork (accessSlot (accessF (checkSub substate message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (originalAt (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message))) (storageAt (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message))) (sub (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) (valArg message)))) (nb := (sub (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) (A := MAX_UINT) (v := valArg message) (t := toArg message)
    (f := fromArg message) (sel := BitVec.ofNat 256 (selector message.data)) (M := (mapMem (mapMem (allowMem message (memF message) (fromArg message)) (mkey (fromArg message)) 2) (mkey (fromArg message)) 2)) hfork hMf
    (by rw [ec2']; exact hto) hcT' hg
  have hpost := fun g (hg : 1899 ≤ g) => creditPostF (fork := fork) (message := message)
    (state := (writeSlot (readSlot (writeSlot (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) message.currentTarget (recipientSlot (toArg message)) (add (storageAt (writeSlot (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) (valArg message)))) (substate := (storeSub fork (accessSlot (storeSub fork (accessSlot (accessF (checkSub substate message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (originalAt (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message))) (storageAt (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message))) (sub (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) message.currentTarget (recipientSlot (toArg message)) (originalAt (readSlot (writeSlot (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) message.currentTarget (recipientSlot (toArg message))) (storageAt (readSlot (writeSlot (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) message.currentTarget (recipientSlot (toArg message))) (add (storageAt (writeSlot (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) (valArg message)))) (nt := (add (storageAt (writeSlot (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) (valArg message))) (A := MAX_UINT) (v := valArg message)
    (t := toArg message) (f := fromArg message) (sel := BitVec.ofNat 256 (selector message.data))
    (M := mapMem (mapMem (mapMem (mapMem (allowMem message (memF message) (fromArg message)) (mkey (fromArg message)) 2) (mkey (fromArg message)) 2) (mkey (toArg message)) 2) (mkey (toArg message)) 2) hstatic
    (size_mapMem (size_mapMem hMf _ _) _ _)
    (ptr_mapMem (size_mapMem hMf _ _) (ptr_mapMem hMf (ptr_mapMem (size_mapMem (size_allowMem
      (size_mapMem size_MEM0 _ _) _) _ _) (ptr_mapMem (size_allowMem (size_mapMem size_MEM0 _ _) _)
        (ptr_allowMem (size_mapMem size_MEM0 _ _) (ptr_mapMem size_MEM0 mload_MEM0 _ _) _) _ _) _ _)
        _ _) _ _) hg
  have hx := Complete.exactS_write hfork hpre hP
    (fun _ _ => by simp only [Complete.getStorage_readSlot]) (by code_fact) (by code_fact)
    hstatic hacc4 (coldIn_accessSlot_self _ _ _)
    (Complete.exactS_write hfork hmid hQ (fun _ _ => by simp only [Complete.getStorage_readSlot])
      (by code_fact) (by code_fact) hstatic hacc6 (coldIn_accessSlot_self _ _ _)
      (Complete.exactS_halt hpost (by decide) (fun _ _ => rfl)))
  obtain ⟨hgas, hiff, hend⟩ := hx.run start (runChild := runChild) within
  have eo1 : originalAt (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) =
      originalAt (checkState state message) message.currentTarget (recipientSlot (fromArg message)) := by
    simp only [readsF, originalAt_readSlot]
  have ec1 : storageAt (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) =
      balFrom (checkState state message) message (valArg message) (fromArg message) := by
    rw [storageAt_readSlot]; exact ec1'
  have eo2 : originalAt (readSlot (writeSlot (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) message.currentTarget (recipientSlot (toArg message)) =
      originalAt (checkState state message) message.currentTarget (recipientSlot (toArg message)) := by
    rw [originalAt_readSlot, originalAt_writeSlot hacc4]; simp only [readsF, originalAt_readSlot]
  have ec2 : storageAt (readSlot (writeSlot (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) message.currentTarget (recipientSlot (toArg message)) =
      balTo (checkState state message) message (valArg message) (toArg message) (fromArg message) := by
    rw [storageAt_readSlot]; exact ec2'
  rw [eo2, ec2, ec2', eo1, ec1, ec1'] at hiff
  refine ⟨hiff, fun s hrun hok => ?_⟩
  have hok' := hiff.mp ⟨s, hrun, hok⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := hend s hrun hok
  rw [eo2, ec2, ec2', eo1, ec1, ec1'] at h5
  refine ⟨h1, h2, ?_, ?_, ?_, ?_⟩
  · rw [h3]; simp only [creditedF, debitedF, balTo, balFrom, hAF]
  · rw [h4, eo2, ec2, ec2', eo1, ec1, ec1']
    unfold loggedSubF creditedSubF debitedSubF
    rw [eS]
  · obtain ⟨o1, o2, o3⟩ := hok'
    have e1 := Complete.wMeter_gasLeft o1
    have e2 := Complete.wMeter_gasLeft o2
    have e3 : s.gas.gasLeft = _ := congrArg StateGasMeter.gasLeft h5
    have hac : allowCostF fork (checkState state message) message (valArg message)
        (fromArg message) = 26 := by simp only [allowCostF, allowCost, hmax, ite_true]
    simp only [okCostF, hac, debitCostF, creditCostF, fxP1, fxM1, fxM2, wBump] at e1 e2 e3 o3 ⊢
    omega
  · rw [h5]


/-- The execution gas from pc 0 to the `SSTORE` of the allowance in `transferFrom` with a fee of
0 and `_allowance ≠ MAX_UINT`. -/
abbrev faP0 (state : State.TransactionState) (message : Message fork)
    (c0 cB c10 cA c3 c4 : Bool) : Nat :=
  PRE_COST_F + slotCost c0 + slotCost cB + slotCost c10 + (679 + slotCost cA + slotCost c3 +
    slotCost c4 + mulCost (valArg message) + capCost (rawFee (checkState state message) message (valArg message)) (storageAt (checkState state message) message.currentTarget 4))

/-- The meter after the write of the allowance (fee 0, `_allowance ≠ MAX_UINT`). -/
abbrev faM0 (fork : Fork) (g : StateGasMeter) (state : State.TransactionState)
    (message : Message fork) (c0 cB c10 cA c3 c4 : Bool) : StateGasMeter :=
  wMeter fork g (faP0 state message c0 cB c10 cA c3 c4) (originalAt (checkState state message) message.currentTarget (allowFrom message (fromArg message))) (allowOf (checkState state message) message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message)) false

/-- The meter after the write of `balances[_from]` (fee 0, `_allowance ≠ MAX_UINT`). -/
abbrev faM1 (fork : Fork) (g : StateGasMeter) (state : State.TransactionState)
    (message : Message fork) (c0 cB c10 cA c3 c4 cF : Bool) : StateGasMeter :=
  wMeter fork (faM0 fork g state message c0 cB c10 cA c3 c4) (405 + slotCost cF) (originalAt (checkState state message) message.currentTarget (recipientSlot (fromArg message))) (balFrom (checkState state message) message (valArg message) (fromArg message)) (sub (balFrom (checkState state message) message (valArg message) (fromArg message)) (valArg message)) false

/-- The meter after the write of `balances[_to]` (fee 0, `_allowance ≠ MAX_UINT`). -/
abbrev faM2 (fork : Fork) (g : StateGasMeter) (state : State.TransactionState)
    (message : Message fork) (c0 cB c10 cA c3 c4 cF cT : Bool) : StateGasMeter :=
  wMeter fork (faM1 fork g state message c0 cB c10 cA c3 c4 cF) (308 + slotCost cT) (originalAt (checkState state message) message.currentTarget (recipientSlot (toArg message))) (balTo (checkState state message) message (valArg message) (toArg message) (fromArg message)) (add (balTo (checkState state message) message (valArg message) (toArg message) (fromArg message)) (valArg message)) false

/-- **transferFrom(f, t, v), fee 0, allowance `A ≠ MAX_UINT` with `v ≤ A`, over the EIP-8037
meter, exactly, at any reservoir, refills allowed.** Three writes: the allowance, `balances[f]`,
`balances[t]`. The run ends with no error if and only if the chain condition holds; every run that
ends with no error has the state and substate of `spec_ok`, with `gasLeft + okCostF = gas` plus the
three bumps. -/
theorem transferFrom_sgm (hfork : .berlin ≤ fork)
    (hstatic : message.isStatic = false) (hacc : hasAccount state message.currentTarget)
    (hlong : 100 ≤ message.data.size) (hsz : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x23b872dd) (hv : message.value = 0)
    (hnp : byte20 (storageAt state message.currentTarget 0) = 0)
    (hnb : (storageAt state message.currentTarget (blackFrom (fromArg message))).toNat % 256 = 0)
    (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    (hov : (valArg message).toNat *
      (storageAt (checkState state message) message.currentTarget 3).toNat < 2 ^ 256)
    (hfee : feeOf (checkState state message) message (valArg message) = 0)
    (hmax : allowOf (checkState state message) message (fromArg message) ≠ MAX_UINT)
    (hle : (valArg message).toNat ≤ (allowOf (checkState state message) message (fromArg message)).toNat)
    (hbal : (valArg message).toNat ≤
      (balFrom (checkState state message) message (valArg message) (fromArg message)).toNat)
    (hto : (balTo (checkState state message) message (valArg message) (toArg message)
      (fromArg message)).toNat + (valArg message).toNat < 2 ^ 256)
    {c0 cB c10 cA c3 c4 cF cT : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hcB : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget
      (blackFrom (fromArg message)) = cB)
    (hc10 : coldIn (accessSlot (accessSlot substate message.currentTarget 0) message.currentTarget
      (blackFrom (fromArg message))) message.currentTarget 10 = c10)
    (hcA : coldIn (checkSub substate message) message.currentTarget
      (allowFrom message (fromArg message)) = cA)
    (hc3 : coldIn (accessSlot (checkSub substate message) message.currentTarget
      (allowFrom message (fromArg message))) message.currentTarget 3 = c3)
    (hc4 : coldIn (accessSlot (accessSlot (checkSub substate message) message.currentTarget
      (allowFrom message (fromArg message))) message.currentTarget 3) message.currentTarget 4 = c4)
    (hcF : coldIn (allowedSubF fork (checkSub substate message) (checkState state message) message
      (valArg message) (fromArg message)) message.currentTarget (recipientSlot (fromArg message)) =
        cF)
    (hcT : coldIn (accessSlot (allowedSubF fork (checkSub substate message)
      (checkState state message) message (valArg message) (fromArg message)) message.currentTarget
      (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (toArg message)) = cT)
    {gas : Nat} {m : Evm fork StateGasMeter}
    (start : At CODE message 0 [] .empty gas state substate (Meter.toNat m))
    {bound : Nat} {runChild : MessageRunner fork StateGasMeter bound}
    (within : GasMeter.gasHeld m.gas ≤ bound) :
    (Shadow.RunsOkS fork bound runChild m within ↔
      wOk fork m.gas (faP0 state message c0 cB c10 cA c3 c4) (originalAt (checkState state message) message.currentTarget (allowFrom message (fromArg message))) (allowOf (checkState state message) message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message)) false ∧
      wOk fork (faM0 fork m.gas state message c0 cB c10 cA c3 c4) (405 + slotCost cF) (originalAt (checkState state message) message.currentTarget (recipientSlot (fromArg message))) (balFrom (checkState state message) message (valArg message) (fromArg message)) (sub (balFrom (checkState state message) message (valArg message) (fromArg message)) (valArg message)) false ∧
      wOk fork (faM1 fork m.gas state message c0 cB c10 cA c3 c4 cF) (308 + slotCost cT) (originalAt (checkState state message) message.currentTarget (recipientSlot (toArg message))) (balTo (checkState state message) message (valArg message) (toArg message) (fromArg message)) (add (balTo (checkState state message) message (valArg message) (toArg message) (fromArg message)) (valArg message))
        false ∧
      1899 ≤ (faM2 fork m.gas state message c0 cB c10 cA c3 c4 cF cT).gasLeft) ∧
    ∀ s, Evm.runFrame (step fork) (step_decreases fork) bound runChild m within = .ok s →
      s.error = none →
      s.running = false ∧ s.output = .empty ∧
      s.state = creditedF (checkState state message) message (valArg message) (toArg message)
        (fromArg message) ∧
      s.substate = loggedSubF fork (checkSub substate message) (checkState state message) message
        (valArg message) (toArg message) (fromArg message) ∧
      s.gas.gasLeft + okCostF fork state message c0 cB c10 cA c3 c4 cF cT =
        gas + wBump fork m.gas (originalAt (checkState state message) message.currentTarget (allowFrom message (fromArg message))) (allowOf (checkState state message) message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message)) +
          wBump fork (faM0 fork m.gas state message c0 cB c10 cA c3 c4) (originalAt (checkState state message) message.currentTarget (recipientSlot (fromArg message))) (balFrom (checkState state message) message (valArg message) (fromArg message)) (sub (balFrom (checkState state message) message (valArg message) (fromArg message)) (valArg message)) +
          wBump fork (faM1 fork m.gas state message c0 cB c10 cA c3 c4 cF) (originalAt (checkState state message) message.currentTarget (recipientSlot (toArg message))) (balTo (checkState state message) message (valArg message) (toArg message) (fromArg message)) (add (balTo (checkState state message) message (valArg message) (toArg message) (fromArg message)) (valArg message)) ∧
      s.gas = { faM2 fork m.gas state message c0 cB c10 cA c3 c4 cF cT with
        gasLeft := s.gas.gasLeft } := by
  have hAF : allowedF (checkState state message) message (valArg message) (fromArg message) = (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) := by
    simp only [allowedF, allowState, if_neg hmax]
  have eS : allowedSubF fork (checkSub substate message) (checkState state message) message (valArg message) (fromArg message) =
      storeSub fork (accessF (checkSub substate message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (originalAt (checkState state message) message.currentTarget (allowFrom message (fromArg message))) (allowOf (checkState state message) message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message)) := by
    simp only [allowedSubF, allowSub, if_neg hmax]
  have haccS : hasAccount (checkState state message) message.currentTarget :=
    hasAccount_readSlot (hasAccount_readSlot (hasAccount_readSlot hacc))
  have hacc3 : hasAccount (readsF (checkState state message) message (fromArg message)) message.currentTarget :=
    hasAccount_readSlot (hasAccount_readSlot (hasAccount_readSlot haccS))
  have hacc3w := hasAccount_writeSlot (n := (allowFrom message (fromArg message))) (v := (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) hacc3
  have hacc4 := hasAccount_readSlot (n := (recipientSlot (fromArg message))) (other := message.currentTarget) hacc3w
  have hacc5 := hasAccount_writeSlot (n := (recipientSlot (fromArg message))) (v := (sub (storageAt (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) hacc4
  have hacc6 := hasAccount_readSlot (n := (recipientSlot (toArg message))) (other := message.currentTarget) hacc5
  have eo0 : originalAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) = originalAt (checkState state message) message.currentTarget (allowFrom message (fromArg message)) := by
    simp only [readsF, originalAt_readSlot]
  have ec0 : storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) = (allowOf (checkState state message) message (fromArg message)) := by
    simp only [readsF, storageAt_readSlot, allowOf]
  have ec1' : storageAt (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message)) = balFrom (checkState state message) message (valArg message) (fromArg message) := by
    simp only [balFrom, hAF]
  have hP : faP0 state message c0 cB c10 cA c3 c4 < 97920 := by
    have := Complete.slotCost_le c0; have := Complete.slotCost_le cB
    have := Complete.slotCost_le c10; have := Complete.slotCost_le cA
    have := Complete.slotCost_le c3; have := Complete.slotCost_le c4
    have : mulCost (valArg message) ≤ 138 := by unfold mulCost; split <;> omega
    have : capCost (rawFee (checkState state message) message (valArg message)) (storageAt (checkState state message) message.currentTarget 4) ≤ 108 := by
      unfold capCost; split <;> omega
    simp only [faP0, PRE_COST_F]; omega
  have hQ1 : 405 + slotCost cF < 97920 := by have := Complete.slotCost_le cF; omega
  have hQ2 : 308 + slotCost cT < 97920 := by have := Complete.slotCost_le cT; omega
  have hpre : ∀ g, faP0 state message c0 cB c10 cA c3 c4 ≤ g → Gas.HoareG fork
      (At CODE message 0 [] .empty g state substate)
      (At CODE message 9020 ((allowFrom message (fromArg message)) :: (sub (allowOf (checkState state message) message (fromArg message)) (valArg message)) :: (sub (allowOf (checkState state message) message (fromArg message)) (valArg message)) :: [0x60, 0, 0, (allowOf (checkState state message) message (fromArg message)), (valArg message), toArg message,
          fromArg message, 0x1097, (valArg message), toArg message, fromArg message, 0x0392,
          BitVec.ofNat 256 (selector message.data)])
        (allowMem message (allowMem message (memF message) (fromArg message)) (fromArg message)) (g - faP0 state message c0 cB c10 cA c3 c4) (readsF (checkState state message) message (fromArg message)) (accessF (checkSub substate message) message (fromArg message))) := by
    intro g hg
    simp only [faP0] at hg ⊢
    refine Triple.seq (preF hfork hlong hsz hsel hv hnp hnb hdep hc0 hcB hc10
      (Nat.le_trans (Nat.le_add_right _ _) hg)) ?_
    refine Triple.seq (segA (state := (checkState state message))
      (substate := (checkSub substate message)) hfork (size_mapMem size_MEM0 _ _) hov hfee hcA hc3
      hc4 (by omega)) ?_
    refine (allowToW (by simp) hmax hle (by omega)
      (size_allowMem (size_mapMem size_MEM0 _ _) _)).consequence (fun _ h => h) ?_
    intro e he
    have hx : g - (PRE_COST_F + slotCost c0 + slotCost cB + slotCost c10) -
        (361 + slotCost cA + slotCost c3 + slotCost c4 + mulCost (valArg message) + capCost (rawFee (checkState state message) message (valArg message)) (storageAt (checkState state message) message.currentTarget 4)) - 318 =
        g - (PRE_COST_F + slotCost c0 + slotCost cB + slotCost c10 +
          (679 + slotCost cA + slotCost c3 + slotCost c4 + mulCost (valArg message) + capCost (rawFee (checkState state message) message (valArg message)) (storageAt (checkState state message) message.currentTarget 4))) := by
      omega
    rw [hx] at he
    exact he
  have hcF' : coldIn (storeSub fork (accessF (checkSub substate message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (originalAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message))) (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message))) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message)) = cF := by
    rw [eo0, ec0, ← eS]; exact hcF
  have hM0 : (allowMem message (allowMem message (memF message) (fromArg message)) (fromArg message)).size = 96 := size_allowMem (size_allowMem (size_mapMem size_MEM0 _ _) _) _
  have hmid1 := fun g (hg : 405 + slotCost cF ≤ g) => allowToDebitW (state := (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))))
    (substate := (storeSub fork (accessF (checkSub substate message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (originalAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message))) (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message))) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message)))) (b := (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) (A := (allowOf (checkState state message) message (fromArg message))) (v := (valArg message)) (t := toArg message)
    (f := fromArg message) (sel := BitVec.ofNat 256 (selector message.data)) (M := (allowMem message (allowMem message (memF message) (fromArg message)) (fromArg message))) hfork
    (by rw [ec1']; exact hbal) hcF' hg hM0
  have ec2' : storageAt (writeSlot (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message)) =
      balTo (checkState state message) message (valArg message) (toArg message) (fromArg message) := by
    simp only [balTo, debitedF, balFrom, hAF]
  have hcT' : coldIn (storeSub fork (accessSlot (storeSub fork (accessF (checkSub substate message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (originalAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message))) (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message))) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (originalAt (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message))) (storageAt (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message))) (sub (storageAt (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message)) = cT := by
    rw [coldIn_storeSub, eo0, ec0, ← eS]; exact hcT
  have hMf : (mapMem (mapMem (allowMem message (allowMem message (memF message) (fromArg message)) (fromArg message)) (mkey (fromArg message)) 2) (mkey (fromArg message)) 2).size = 96 := size_mapMem (size_mapMem hM0 _ _) _ _
  have hmid2 := fun g (hg : 308 + slotCost cT ≤ g) => debitToCreditW (state := (writeSlot (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) (valArg message))))
    (substate := (storeSub fork (accessSlot (storeSub fork (accessF (checkSub substate message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (originalAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message))) (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message))) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (originalAt (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message))) (storageAt (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message))) (sub (storageAt (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) (valArg message)))) (nb := (sub (storageAt (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) (A := (allowOf (checkState state message) message (fromArg message))) (v := (valArg message)) (t := toArg message)
    (f := fromArg message) (sel := BitVec.ofNat 256 (selector message.data)) (M := (mapMem (mapMem (allowMem message (allowMem message (memF message) (fromArg message)) (fromArg message)) (mkey (fromArg message)) 2) (mkey (fromArg message)) 2)) hfork hMf
    (by rw [ec2']; exact hto) hcT' hg
  have hP0 : loadWord (memoryReadBytes (allowMem message (allowMem message (memF message) (fromArg message)) (fromArg message)) 64 32) 0 32 = 0x60 :=
    ptr_allowMem (size_allowMem (size_mapMem size_MEM0 _ _) _)
      (ptr_allowMem (size_mapMem size_MEM0 _ _) (ptr_mapMem size_MEM0 mload_MEM0 _ _) _) _
  have hpost := fun g (hg : 1899 ≤ g) => creditPostF (fork := fork) (message := message)
    (state := (writeSlot (readSlot (writeSlot (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) message.currentTarget (recipientSlot (toArg message)) (add (storageAt (writeSlot (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) (valArg message)))) (substate := (storeSub fork (accessSlot (storeSub fork (accessSlot (storeSub fork (accessF (checkSub substate message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (originalAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message))) (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message))) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (originalAt (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message))) (storageAt (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message))) (sub (storageAt (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) message.currentTarget (recipientSlot (toArg message)) (originalAt (readSlot (writeSlot (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) message.currentTarget (recipientSlot (toArg message))) (storageAt (readSlot (writeSlot (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) message.currentTarget (recipientSlot (toArg message))) (add (storageAt (writeSlot (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) (valArg message)))) (nt := (add (storageAt (writeSlot (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) (valArg message))) (A := (allowOf (checkState state message) message (fromArg message))) (v := (valArg message))
    (t := toArg message) (f := fromArg message) (sel := BitVec.ofNat 256 (selector message.data))
    (M := mapMem (mapMem (mapMem (mapMem (allowMem message (allowMem message (memF message) (fromArg message)) (fromArg message)) (mkey (fromArg message)) 2) (mkey (fromArg message)) 2) (mkey (toArg message)) 2) (mkey (toArg message)) 2) hstatic
    (size_mapMem (size_mapMem hMf _ _) _ _)
    (ptr_mapMem (size_mapMem hMf _ _) (ptr_mapMem hMf (ptr_mapMem (size_mapMem hM0 _ _)
      (ptr_mapMem hM0 hP0 _ _) _ _) _ _) _ _) hg
  have hx := Complete.exactS_write hfork hpre hP
    (fun _ _ => by simp only [Complete.getStorage_readSlot]) (by code_fact) (by code_fact)
    hstatic hacc3 (coldIn_accessSlot_false (coldIn_accessSlot_false (coldIn_accessSlot_self _ _ _)))
    (Complete.exactS_write hfork hmid1 hQ1 (fun _ _ => by simp only [Complete.getStorage_readSlot])
      (by code_fact) (by code_fact) hstatic hacc4 (coldIn_accessSlot_self _ _ _)
      (Complete.exactS_write hfork hmid2 hQ2
        (fun _ _ => by simp only [Complete.getStorage_readSlot])
        (by code_fact) (by code_fact) hstatic hacc6 (coldIn_accessSlot_self _ _ _)
        (Complete.exactS_halt hpost (by decide) (fun _ _ => rfl))))
  obtain ⟨hgas, hiff, hend⟩ := hx.run start (runChild := runChild) within
  have eo1 : originalAt (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) = originalAt (checkState state message) message.currentTarget (recipientSlot (fromArg message)) := by
    rw [originalAt_readSlot, originalAt_writeSlot hacc3]; simp only [readsF, originalAt_readSlot]
  have ec1 : storageAt (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) =
      balFrom (checkState state message) message (valArg message) (fromArg message) := by
    rw [storageAt_readSlot]; exact ec1'
  have eo2 : originalAt (readSlot (writeSlot (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) message.currentTarget (recipientSlot (toArg message)) = originalAt (checkState state message) message.currentTarget (recipientSlot (toArg message)) := by
    rw [originalAt_readSlot, originalAt_writeSlot hacc4, originalAt_readSlot,
      originalAt_writeSlot hacc3]
    simp only [readsF, originalAt_readSlot]
  have ec2 : storageAt (readSlot (writeSlot (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) message.currentTarget (recipientSlot (toArg message)) =
      balTo (checkState state message) message (valArg message) (toArg message) (fromArg message) := by
    rw [storageAt_readSlot]; exact ec2'
  rw [eo2, ec2, ec2', eo1, ec1, ec1', eo0, ec0] at hiff
  refine ⟨hiff, fun s hrun hok => ?_⟩
  have hok' := hiff.mp ⟨s, hrun, hok⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := hend s hrun hok
  rw [eo2, ec2, ec2', eo1, ec1, ec1', eo0, ec0] at h5
  refine ⟨h1, h2, ?_, ?_, ?_, ?_⟩
  · rw [h3]; simp only [creditedF, debitedF, balTo, balFrom, hAF]
  · rw [h4, eo2, ec2, ec2', eo1, ec1, ec1', eo0, ec0]
    unfold loggedSubF creditedSubF debitedSubF
    rw [eS]
  · obtain ⟨o0, o1, o2, o3⟩ := hok'
    have e0 := Complete.wMeter_gasLeft o0
    have e1 := Complete.wMeter_gasLeft o1
    have e2 := Complete.wMeter_gasLeft o2
    have e3 : s.gas.gasLeft = _ := congrArg StateGasMeter.gasLeft h5
    have hac : allowCostF fork (checkState state message) message (valArg message) (fromArg message) =
        320 + Gas.writeCost fork (originalAt (checkState state message) message.currentTarget (allowFrom message (fromArg message))) (allowOf (checkState state message) message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message)) false := by
      simp only [allowCostF, allowCost, if_neg hmax]
    simp only [okCostF, hac, debitCostF, creditCostF, faP0, faM0, faM1, faM2,
      wBump] at e0 e1 e2 e3 o3 ⊢
    omega
  · rw [h5]

section Fee

open TransferFee

/-- From 8648 to the allowance step at 8834, with the fee `feeOf state message v` on the stack. -/
theorem segAFee (hfork : .berlin ≤ fork)
    {v t f sel : U256} {M : ByteArray} (hM : M.size = 96)
    (hov : v.toNat * (storageAt state message.currentTarget 3).toNat < 2 ^ 256)
    {cA c3 c4 : Bool}
    (hcA : coldIn substate message.currentTarget (allowFrom message f) = cA)
    (hc3 : coldIn (accessSlot substate message.currentTarget (allowFrom message f))
      message.currentTarget 3 = c3)
    (hc4 : coldIn (accessSlot (accessSlot substate message.currentTarget (allowFrom message f))
      message.currentTarget 3) message.currentTarget 4 = c4)
    {gas : Nat} (hg : 361 + slotCost cA + slotCost c3 + slotCost c4 + mulCost v +
      capCost (rawFee state message v) (storageAt state message.currentTarget 4) ≤ gas) :
    Gas.HoareG fork (At CODE message 8648 [0x60, 0, 0, 0, v, t, f, 0x1097, v, t, f, 0x0392, sel] M gas
        state substate)
      (At CODE message 8834 [0x60, 0, feeOf state message v, allowOf state message f, v, t, f,
          0x1097, v, t, f, 0x0392, sel] (allowMem message M f)
        (gas - (361 + slotCost cA + slotCost c3 + slotCost c4 + mulCost v +
          capCost (rawFee state message v) (storageAt state message.currentTarget 4)))
        (readsF state message f) (accessF substate message f)) := by
  simp only [rawFee, feeOf] at hg ⊢
  step allowRead hfork (by simp) hcA (by gas_ok) hM
  step feeCall hfork (by simp) hc3 (by gas_ok)
  step mulBlock (by simp) (by valid_dest) (by simpa only [storageAt_readSlot] using hov)
    (by gas_ok)
  at_pc 8802
  step divCall (by simp) (by gas_ok)
  step divBlock (by simp) (by valid_dest) (by decide) (by gas_ok)
  at_pc 8816
  step capBlock hfork (by simp) hc4 (by simp only [storageAt_readSlot]; gas_ok)
  simp only [storageAt_readSlot]
  exact restate rfl rfl rfl (by gas_ok) rfl rfl

/-- From 9022 (fee above 0) to the `SSTORE` of `balances[_from]` at 9191. -/
theorem toDebitWFee (hfork : .berlin ≤ fork) {fee A v t f sel : U256}
    (hfv : fee.toNat ≤ v.toNat)
    (hbal : v.toNat ≤ (storageAt state message.currentTarget (recipientSlot f)).toNat)
    {cF : Bool} (hcF : coldIn substate message.currentTarget (recipientSlot f) = cF) {gas : Nat}
    (hg : 403 + slotCost cF ≤ gas) {M : ByteArray} (hM : M.size = 96) :
    Gas.HoareG fork (At CODE message 9022 [0x60, 0, fee, A, v, t, f, 0x1097, v, t, f, 0x0392, sel] M
        gas state substate)
      (At CODE message 9191 (recipientSlot f ::
          sub (storageAt state message.currentTarget (recipientSlot f)) v ::
          sub (storageAt state message.currentTarget (recipientSlot f)) v ::
          [0x60, sub v fee, fee, A, v, t, f, 0x1097, v, t, f, 0x0392, sel])
        (mapMem (mapMem M (mkey f) 2) (mkey f) 2) (gas - (403 + slotCost cF))
        (readSlot state message.currentTarget (recipientSlot f))
        (accessSlot substate message.currentTarget (recipientSlot f))) := by
  step sendCall (by simp) (by gas_ok)
  step subBlock (by simp) (by valid_dest) hfv (by gas_ok)
  at_pc 9041
  step debitCall hfork (by simp) hcF (by gas_ok) hM
  step subBlock (by simp) (by valid_dest) (by simpa only [storageAt_readSlot] using hbal) (by gas_ok)
  at_pc 9125
  refine Triple.seq (debitToWF (by simp) (by gas_ok) (size_mapMem hM _ _)) ?_
  exact restate rfl rfl rfl (by gas_ok) rfl rfl

/-- At 8834 with `_allowance = MAX_UINT` (fee above 0): to the `SSTORE` of `balances[_from]`. -/
theorem maxToDebitWFee (hfork : .berlin ≤ fork) {fee v t f sel : U256}
    (hfv : fee.toNat ≤ v.toNat)
    (hbal : v.toNat ≤ (storageAt state message.currentTarget (recipientSlot f)).toNat)
    {cF : Bool} (hcF : coldIn substate message.currentTarget (recipientSlot f) = cF) {gas : Nat}
    (hg : 429 + slotCost cF ≤ gas) {M : ByteArray} (hM : M.size = 96) :
    Gas.HoareG fork (At CODE message 8834 [0x60, 0, fee, MAX_UINT, v, t, f, 0x1097, v, t, f, 0x0392,
        sel] M gas state substate)
      (At CODE message 9191 (recipientSlot f ::
          sub (storageAt state message.currentTarget (recipientSlot f)) v ::
          sub (storageAt state message.currentTarget (recipientSlot f)) v ::
          [0x60, sub v fee, fee, MAX_UINT, v, t, f, 0x1097, v, t, f, 0x0392, sel])
        (mapMem (mapMem M (mkey f) 2) (mkey f) 2) (gas - (429 + slotCost cF))
        (readSlot state message.currentTarget (recipientSlot f))
        (accessSlot substate message.currentTarget (recipientSlot f))) := by
  refine Triple.seq (allowMax (by simp) (by omega)) ?_
  refine (toDebitWFee hfork hfv hbal hcF (by omega) hM).consequence (fun _ h => h) ?_
  intro e he
  have hx : gas - 26 - (403 + slotCost cF) = gas - (429 + slotCost cF) := by omega
  rw [hx] at he
  exact he

/-- From the `POP` at 9021 after the allowance's `SSTORE` (fee above 0) to the `SSTORE` of
`balances[_from]`. -/
theorem allowToDebitWFee (hfork : .berlin ≤ fork) {fee A v t f sel b : U256}
    (hfv : fee.toNat ≤ v.toNat)
    (hbal : v.toNat ≤ (storageAt state message.currentTarget (recipientSlot f)).toNat)
    {cF : Bool} (hcF : coldIn substate message.currentTarget (recipientSlot f) = cF) {gas : Nat}
    (hg : 405 + slotCost cF ≤ gas) {M : ByteArray} (hM : M.size = 96) :
    Gas.HoareG fork (At CODE message 9021 [b, 0x60, 0, fee, A, v, t, f, 0x1097, v, t, f, 0x0392,
        sel] M gas state substate)
      (At CODE message 9191 (recipientSlot f ::
          sub (storageAt state message.currentTarget (recipientSlot f)) v ::
          sub (storageAt state message.currentTarget (recipientSlot f)) v ::
          [0x60, sub v fee, fee, A, v, t, f, 0x1097, v, t, f, 0x0392, sel])
        (mapMem (mapMem M (mkey f) 2) (mkey f) 2) (gas - (405 + slotCost cF))
        (readSlot state message.currentTarget (recipientSlot f))
        (accessSlot substate message.currentTarget (recipientSlot f))) := by
  refine Triple.seq (Gas.Triple.seqL popR (restate (pc' := 9022) (by decide) rfl rfl
    (g' := gas - 2) (by gas_ok) rfl rfl)) ?_
  refine (toDebitWFee hfork hfv hbal hcF (by omega) hM).consequence (fun _ h => h) ?_
  intro e he
  have hx : gas - 2 - (403 + slotCost cF) = gas - (405 + slotCost cF) := by omega
  rw [hx] at he
  exact he

/-- From the `POP` at 9192 after the `SSTORE` of `balances[_from]` to the `SSTORE` of
`balances[_to]` at 9340 (fee above 0). -/
theorem debitToCreditWFee (hfork : .berlin ≤ fork) {nb send fee A v t f sel : U256}
    {M : ByteArray} (hM : M.size = 96)
    (hto : (storageAt state message.currentTarget (recipientSlot t)).toNat + send.toNat < 2 ^ 256)
    {cT : Bool} (hcT : coldIn substate message.currentTarget (recipientSlot t) = cT) {gas : Nat}
    (hg : 308 + slotCost cT ≤ gas) :
    Gas.HoareG fork (At CODE message 9192 [nb, 0x60, send, fee, A, v, t, f, 0x1097, v, t, f, 0x0392,
        sel] M gas state substate)
      (At CODE message 9340 (recipientSlot t ::
          add (storageAt state message.currentTarget (recipientSlot t)) send ::
          add (storageAt state message.currentTarget (recipientSlot t)) send ::
          [0x60, send, fee, A, v, t, f, 0x1097, v, t, f, 0x0392, sel])
        (mapMem (mapMem M (mkey t) 2) (mkey t) 2) (gas - (308 + slotCost cT))
        (readSlot state message.currentTarget (recipientSlot t))
        (accessSlot substate message.currentTarget (recipientSlot t))) := by
  refine Triple.seq (Gas.Triple.seqL popR (restate (pc' := 9193) (by decide) rfl rfl
    (g' := gas - 2) (by gas_ok) rfl rfl)) ?_
  step creditCall hfork (by simp) (cT := cT) hcT (by gas_ok) hM
  step addBlock (by simp) (by valid_dest) (by simpa using hto) (by gas_ok)
  at_pc 9274
  refine Triple.seq (creditToWF (by simp) (by gas_ok) (size_mapMem hM _ _)) ?_
  exact restate rfl rfl rfl (by gas_ok) rfl rfl

/-- At 9465: from the `JUMPDEST` to the `SSTORE` of `balances[owner]` at 9564 (slot 0 read again,
warm). -/
theorem ownerToWF (hfork : .berlin ≤ fork) {no send fee A v t f : U256} {rest : List U256}
    (hrest : rest.length ≤ 800) (hc0 : coldIn substate message.currentTarget 0 = false)
    {gas : Nat} (hg : 236 ≤ gas) {M : ByteArray} (hM : M.size = 96) :
    Gas.HoareG fork (At CODE message 9465 (no :: 0x60 :: send :: fee :: A :: v :: t :: f :: rest) M
        gas state substate)
      (At CODE message 9564 (ownerSlot (storageAt state message.currentTarget 0) :: no :: no ::
          0x60 :: send :: fee :: A :: v :: t :: f :: rest)
        (mapMem M (mkey (ownerKey (storageAt state message.currentTarget 0))) 2) (gas - 236)
        (readSlot state message.currentTarget 0) (accessSlot substate message.currentTarget 0)) := by
  have hexp : exponentBytes (0 : U256) = 0 := by decide
  simp only [ownerSlot, ownerKey, mkey]
  step jumpdestR
  step pushR 1 (0x02 : U256)
  step pushR 1 (0 : U256)
  step dupR 0
  step pushR 1 (0 : U256)
  step swapR 0
  norm
  step Gas.sloadG hfork (cold := false) (by code_fact) (by code_fact) hc0 (by gas_ok)
  rw [Issue.getStorage_eq]
  step swapR 0
  norm
  step pushR 2 (0x0100 : U256)
  step Gas.expLG (Nat.le_trans (by decide) hfork) (by code_fact) (by code_fact) (by gas_ok)
  step swapR 0
  norm
  step binR 0x04 Local.instruction_div
  step pushR 20 ADDR_MASK
  step binR 0x16 Local.instruction_and
  at_pc 9504
  step hashTailF (by decide) (by simp; omega) hM (by gas_ok)
  at_pc 9562
  step dupR 1
  step swapR 0
  norm
  exact restate (by decide) rfl rfl (by gas_ok) rfl rfl

/-- From the `POP` at 9341 after the `SSTORE` of `balances[_to]` (fee above 0) to the `SSTORE` of
`balances[owner]` at 9564. -/
theorem creditToOwnerW (hfork : .berlin ≤ fork) {nt send fee A v t f sel : U256}
    (hfee : fee ≠ 0) {M : ByteArray} (hM : M.size = 96)
    (hc0 : coldIn substate message.currentTarget 0 = false) {cO : Bool}
    (hcO : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget
      (ownerSlot (storageAt state message.currentTarget 0)) = cO)
    (hown : (storageAt state message.currentTarget
      (ownerSlot (storageAt state message.currentTarget 0))).toNat + fee.toNat < 2 ^ 256)
    {gas : Nat} (hg : 605 + slotCost cO ≤ gas) :
    Gas.HoareG fork (At CODE message 9341 [nt, 0x60, send, fee, A, v, t, f, 0x1097, v, t, f, 0x0392,
        sel] M gas state substate)
      (At CODE message 9564 (ownerSlot (storageAt state message.currentTarget 0) ::
          add (storageAt state message.currentTarget
            (ownerSlot (storageAt state message.currentTarget 0))) fee ::
          add (storageAt state message.currentTarget
            (ownerSlot (storageAt state message.currentTarget 0))) fee ::
          [0x60, send, fee, A, v, t, f, 0x1097, v, t, f, 0x0392, sel])
        (mapMem (mapMem M (mkey (ownerKey (storageAt state message.currentTarget 0))) 2)
          (mkey (ownerKey (storageAt state message.currentTarget 0))) 2)
        (gas - (605 + slotCost cO))
        (readSlot (readSlot (readSlot state message.currentTarget 0) message.currentTarget
          (ownerSlot (storageAt state message.currentTarget 0))) message.currentTarget 0)
        (accessSlot (accessSlot (accessSlot substate message.currentTarget 0) message.currentTarget
          (ownerSlot (storageAt state message.currentTarget 0))) message.currentTarget 0)) := by
  have hpos : 0 < fee.toNat := by
    rcases Nat.eq_zero_or_pos fee.toNat with h | h
    · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h)) hfee
    · exact h
  step popR
  step pushR 1 (0 : U256)
  step dupR 3
  step binR 0x11 Local.instruction_gt
  step unR 0x15 instruction_iszero
  step pushR 2 (0x25e4 : U256)
  step jumpi0R (by simp [greaterThan, isZero, hpos])
  at_pc 9351
  step ownerCallF (cO := cO) hfork rfl (by simp) hc0 hcO (by gas_ok) hM
  step addBlock (by simp) (by valid_dest) hown (by gas_ok)
  at_pc 9465
  refine Triple.seq (ownerToWF hfork (by simp)
    (coldIn_accessSlot_false (coldIn_accessSlot_false hc0)) (by gas_ok)
    (size_mapMem hM _ _)) ?_
  rw [storageAt_readSlot, storageAt_readSlot]
  exact restate rfl rfl rfl (by gas_ok) rfl rfl

/-- From the `POP` at 9565 after the `SSTORE` of `balances[owner]` to the STOP: the two logs. -/
theorem ownerPostF (hfork : .berlin ≤ fork) {no send fee A v t f sel : U256}
    (hstatic : message.isStatic = false) {M : ByteArray} (hM : M.size = 96)
    (hptr : loadWord (memoryReadBytes M 64 32) 0 32 = 0x60)
    (hc0 : coldIn substate message.currentTarget 0 = false) {gas : Nat} (hg : 3839 ≤ gas) :
    Gas.SpecG fork (At CODE message 9565 [no, 0x60, send, fee, A, v, t, f, 0x1097, v, t, f, 0x0392,
        sel] M gas state substate)
      (Halted false .empty (gas - 3839) (readSlot state message.currentTarget 0)
        { ({ accessSlot substate message.currentTarget 0 with
            logs := substate.logs.push (transferLog message.currentTarget (bitwiseAnd ADDR_MASK f)
              (bitwiseAnd ADDR_MASK (ownerKey (storageAt state message.currentTarget 0))) fee) } :
            Substate) with
          logs := (substate.logs.push (transferLog message.currentTarget (bitwiseAnd ADDR_MASK f)
              (bitwiseAnd ADDR_MASK (ownerKey (storageAt state message.currentTarget 0))) fee)).push
            (transferLog message.currentTarget (bitwiseAnd ADDR_MASK f) (bitwiseAnd ADDR_MASK t)
              send) }) := by
  refine Triple.seq (Gas.Triple.seqL popR (restate (pc' := 9566) (by decide) rfl rfl
    (g' := gas - 2) (by gas_ok) rfl rfl)) ?_
  step ownerLogF hfork rfl (by simp) hstatic hc0 (by gas_ok) hM hptr
  step logBlock128F (by simp) hstatic (by gas_ok)
    (by rw [ByteArray.size_append, size_wordBytes]; exact congrArg (· + 32) hM)
    (by rw [read64_append hM]; exact hptr)
  refine (endBlock (by gas_ok)).consequence (fun _ h => h) ?_
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  exact ⟨hr, he, ho, by rw [hgas]; gas_ok, hs, hss⟩


/-- The meter after the write of `balances[_from]` (fee above 0, `_allowance = MAX_UINT`). -/
abbrev gxM1 (fork : Fork) (g : StateGasMeter) (state : State.TransactionState)
    (message : Message fork) (c0 cB c10 cA c3 c4 cF : Bool) : StateGasMeter :=
  wMeter fork g (fxP1 state message c0 cB c10 cA c3 c4 cF) (originalAt (checkState state message) message.currentTarget (recipientSlot (fromArg message))) (balFrom (checkState state message) message (valArg message) (fromArg message)) (sub (balFrom (checkState state message) message (valArg message) (fromArg message)) (valArg message)) false

/-- The meter after the write of `balances[_to]` (fee above 0, `_allowance = MAX_UINT`). -/
abbrev gxM2 (fork : Fork) (g : StateGasMeter) (state : State.TransactionState)
    (message : Message fork) (c0 cB c10 cA c3 c4 cF cT : Bool) : StateGasMeter :=
  wMeter fork (gxM1 fork g state message c0 cB c10 cA c3 c4 cF) (308 + slotCost cT) (originalAt (checkState state message) message.currentTarget (recipientSlot (toArg message))) (balTo (checkState state message) message (valArg message) (toArg message) (fromArg message)) (add (balTo (checkState state message) message (valArg message) (toArg message) (fromArg message)) (sendOf (checkState state message) message (valArg message))) false

/-- The meter after the write of `balances[owner]` (fee above 0, `_allowance = MAX_UINT`). -/
abbrev gxM3 (fork : Fork) (g : StateGasMeter) (state : State.TransactionState)
    (message : Message fork) (c0 cB c10 cA c3 c4 cF cT cO : Bool) : StateGasMeter :=
  wMeter fork (gxM2 fork g state message c0 cB c10 cA c3 c4 cF cT) (605 + slotCost cO) (originalAt (checkState state message) message.currentTarget (ownerSlot (ownerWordF (checkState state message) message (valArg message) (toArg message) (fromArg message)))) (balOF (checkState state message) message (valArg message) (toArg message) (fromArg message)) (add (balOF (checkState state message) message (valArg message) (toArg message) (fromArg message)) (feeOf (checkState state message) message (valArg message))) false

/-- **transferFrom(f, t, v), fee above 0, allowance `MAX_UINT`, over the EIP-8037 meter, exactly,
at any reservoir, refills allowed.** Three writes: `balances[f]`, `balances[t]`,
`balances[owner]`. The run ends with no error if and only if the chain condition holds; every run
that ends with no error has the state and substate of `spec_feeF`, with
`gasLeft + feeCostF = gas` plus the three bumps. -/
theorem transferFromFee_max_sgm (hfork : .berlin ≤ fork)
    (hstatic : message.isStatic = false) (hacc : hasAccount state message.currentTarget)
    (hlong : 100 ≤ message.data.size) (hsz : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x23b872dd) (hv : message.value = 0)
    (hnp : byte20 (storageAt state message.currentTarget 0) = 0)
    (hnb : (storageAt state message.currentTarget (blackFrom (fromArg message))).toNat % 256 = 0)
    (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    (hov : (valArg message).toNat *
      (storageAt (checkState state message) message.currentTarget 3).toNat < 2 ^ 256)
    (hfee : feeOf (checkState state message) message (valArg message) ≠ 0)
    (hfv : (feeOf (checkState state message) message (valArg message)).toNat ≤
      (valArg message).toNat)
    (hmax : allowOf (checkState state message) message (fromArg message) = MAX_UINT)
    (hbal : (valArg message).toNat ≤
      (balFrom (checkState state message) message (valArg message) (fromArg message)).toNat)
    (hto : (balTo (checkState state message) message (valArg message) (toArg message)
      (fromArg message)).toNat +
      (sendOf (checkState state message) message (valArg message)).toNat < 2 ^ 256)
    (hown : (balOF (checkState state message) message (valArg message) (toArg message)
      (fromArg message)).toNat +
      (feeOf (checkState state message) message (valArg message)).toNat < 2 ^ 256)
    {c0 cB c10 cA c3 c4 cF cT cO : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hcB : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget
      (blackFrom (fromArg message)) = cB)
    (hc10 : coldIn (accessSlot (accessSlot substate message.currentTarget 0) message.currentTarget
      (blackFrom (fromArg message))) message.currentTarget 10 = c10)
    (hcA : coldIn (checkSub substate message) message.currentTarget
      (allowFrom message (fromArg message)) = cA)
    (hc3 : coldIn (accessSlot (checkSub substate message) message.currentTarget
      (allowFrom message (fromArg message))) message.currentTarget 3 = c3)
    (hc4 : coldIn (accessSlot (accessSlot (checkSub substate message) message.currentTarget
      (allowFrom message (fromArg message))) message.currentTarget 3) message.currentTarget 4 = c4)
    (hcF : coldIn (allowedSubF fork (checkSub substate message) (checkState state message) message
      (valArg message) (fromArg message)) message.currentTarget (recipientSlot (fromArg message)) =
        cF)
    (hcT : coldIn (accessSlot (allowedSubF fork (checkSub substate message)
      (checkState state message) message (valArg message) (fromArg message)) message.currentTarget
      (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (toArg message)) = cT)
    (hcO : coldIn (creditedSubFeeF fork (checkSub substate message) (checkState state message)
      message (valArg message) (toArg message) (fromArg message)) message.currentTarget
      (ownerSlot (ownerWordF (checkState state message) message (valArg message) (toArg message)
        (fromArg message))) = cO)
    {gas : Nat} {m : Evm fork StateGasMeter}
    (start : At CODE message 0 [] .empty gas state substate (Meter.toNat m))
    {bound : Nat} {runChild : MessageRunner fork StateGasMeter bound}
    (within : GasMeter.gasHeld m.gas ≤ bound) :
    (Shadow.RunsOkS fork bound runChild m within ↔
      wOk fork m.gas (fxP1 state message c0 cB c10 cA c3 c4 cF) (originalAt (checkState state message) message.currentTarget (recipientSlot (fromArg message))) (balFrom (checkState state message) message (valArg message) (fromArg message)) (sub (balFrom (checkState state message) message (valArg message) (fromArg message)) (valArg message)) false ∧
      wOk fork (gxM1 fork m.gas state message c0 cB c10 cA c3 c4 cF) (308 + slotCost cT) (originalAt (checkState state message) message.currentTarget (recipientSlot (toArg message))) (balTo (checkState state message) message (valArg message) (toArg message) (fromArg message)) (add (balTo (checkState state message) message (valArg message) (toArg message) (fromArg message)) (sendOf (checkState state message) message (valArg message))) false ∧
      wOk fork (gxM2 fork m.gas state message c0 cB c10 cA c3 c4 cF cT) (605 + slotCost cO) (originalAt (checkState state message) message.currentTarget (ownerSlot (ownerWordF (checkState state message) message (valArg message) (toArg message) (fromArg message)))) (balOF (checkState state message) message (valArg message) (toArg message) (fromArg message)) (add (balOF (checkState state message) message (valArg message) (toArg message) (fromArg message)) (feeOf (checkState state message) message (valArg message)))
        false ∧
      3839 ≤ (gxM3 fork m.gas state message c0 cB c10 cA c3 c4 cF cT cO).gasLeft) ∧
    ∀ s, Evm.runFrame (step fork) (step_decreases fork) bound runChild m within = .ok s →
      s.error = none →
      s.running = false ∧ s.output = .empty ∧
      s.state = feeStateF (checkState state message) message (valArg message) (toArg message)
        (fromArg message) ∧
      s.substate = feeSubF fork (checkSub substate message) (checkState state message) message
        (valArg message) (toArg message) (fromArg message) ∧
      s.gas.gasLeft + feeCostF fork state message c0 cB c10 cA c3 c4 cF cT cO =
        gas + wBump fork m.gas (originalAt (checkState state message) message.currentTarget (recipientSlot (fromArg message))) (balFrom (checkState state message) message (valArg message) (fromArg message)) (sub (balFrom (checkState state message) message (valArg message) (fromArg message)) (valArg message)) +
          wBump fork (gxM1 fork m.gas state message c0 cB c10 cA c3 c4 cF) (originalAt (checkState state message) message.currentTarget (recipientSlot (toArg message))) (balTo (checkState state message) message (valArg message) (toArg message) (fromArg message)) (add (balTo (checkState state message) message (valArg message) (toArg message) (fromArg message)) (sendOf (checkState state message) message (valArg message))) +
          wBump fork (gxM2 fork m.gas state message c0 cB c10 cA c3 c4 cF cT) (originalAt (checkState state message) message.currentTarget (ownerSlot (ownerWordF (checkState state message) message (valArg message) (toArg message) (fromArg message)))) (balOF (checkState state message) message (valArg message) (toArg message) (fromArg message)) (add (balOF (checkState state message) message (valArg message) (toArg message) (fromArg message)) (feeOf (checkState state message) message (valArg message))) ∧
      s.gas = { gxM3 fork m.gas state message c0 cB c10 cA c3 c4 cF cT cO with gasLeft := s.gas.gasLeft } := by
  have hAF : allowedF (checkState state message) message (valArg message) (fromArg message) = (readsF (checkState state message) message (fromArg message)) := by
    simp only [allowedF, allowState, hmax, ite_true]
  have eS : allowedSubF fork (checkSub substate message) (checkState state message) message (valArg message) (fromArg message) = (accessF (checkSub substate message) message (fromArg message)) := by
    simp only [allowedSubF, allowSub, hmax, ite_true]
  have haccS : hasAccount (checkState state message) message.currentTarget :=
    hasAccount_readSlot (hasAccount_readSlot (hasAccount_readSlot hacc))
  have hacc3 : hasAccount (readsF (checkState state message) message (fromArg message)) message.currentTarget :=
    hasAccount_readSlot (hasAccount_readSlot (hasAccount_readSlot haccS))
  have haccb : hasAccount (readsF (checkState state message) message (fromArg message)) message.currentTarget := hacc3
  have hacc4 := hasAccount_readSlot (n := (recipientSlot (fromArg message))) (other := message.currentTarget) haccb
  have hacc5 := hasAccount_writeSlot (n := (recipientSlot (fromArg message))) (v := (sub (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) hacc4
  have hacc6 := hasAccount_readSlot (n := (recipientSlot (toArg message))) (other := message.currentTarget) hacc5
  have hacc7 := hasAccount_writeSlot (n := (recipientSlot (toArg message))) (v := (add (storageAt (writeSlot (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) (sub (valArg message) (feeOf (checkState state message) message (valArg message))))) hacc6
  have hacc8 : hasAccount (readSlot (readSlot (readSlot (writeSlot (readSlot (writeSlot (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) message.currentTarget (recipientSlot (toArg message)) (add (storageAt (writeSlot (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) (sub (valArg message) (feeOf (checkState state message) message (valArg message))))) message.currentTarget 0) message.currentTarget (ownerSlot (storageAt (writeSlot (readSlot (writeSlot (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) message.currentTarget (recipientSlot (toArg message)) (add (storageAt (writeSlot (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) (sub (valArg message) (feeOf (checkState state message) message (valArg message))))) message.currentTarget 0))) message.currentTarget 0) message.currentTarget :=
    hasAccount_readSlot (hasAccount_readSlot (hasAccount_readSlot hacc7))
  have hacc4' : hasAccount (readSlot (allowedF (checkState state message) message (valArg message) (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget :=
    hasAccount_readSlot (hasAccount_allowState hacc3)
  have hacc5' : hasAccount (readSlot (debitedF (checkState state message) message (valArg message) (fromArg message)) message.currentTarget (recipientSlot (toArg message))) message.currentTarget :=
    hasAccount_readSlot (hasAccount_writeSlot hacc4')
  have horig : ∀ mm, originalAt (creditedFeeF (checkState state message) message (valArg message) (toArg message) (fromArg message)) message.currentTarget mm = originalAt (checkState state message) message.currentTarget mm := by
    intro mm
    rw [originalAt_writeSlot hacc5', originalAt_readSlot, originalAt_writeSlot hacc4',
      originalAt_readSlot, originalAt_allowState hacc3]
    simp only [readsF, originalAt_readSlot]
  have ec1' : storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message)) = balFrom (checkState state message) message (valArg message) (fromArg message) := by
    simp only [balFrom, hAF]
  have ec1 : storageAt (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) =
      balFrom (checkState state message) message (valArg message) (fromArg message) := by
    rw [storageAt_readSlot]; exact ec1'
  have eo1 : originalAt (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) = originalAt (checkState state message) message.currentTarget (recipientSlot (fromArg message)) := by
    simp only [readsF, originalAt_readSlot]
  have ec2' : storageAt (writeSlot (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message)) =
      balTo (checkState state message) message (valArg message) (toArg message) (fromArg message) := by
    simp only [balTo, debitedF, balFrom, hAF]
  have ec2 : storageAt (readSlot (writeSlot (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) message.currentTarget (recipientSlot (toArg message)) =
      balTo (checkState state message) message (valArg message) (toArg message) (fromArg message) := by
    rw [storageAt_readSlot]; exact ec2'
  have eo2 : originalAt (readSlot (writeSlot (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) message.currentTarget (recipientSlot (toArg message)) = originalAt (checkState state message) message.currentTarget (recipientSlot (toArg message)) := by
    rw [originalAt_readSlot, originalAt_writeSlot hacc4, originalAt_readSlot]
    simp only [readsF, originalAt_readSlot]
  have eS5 : (writeSlot (readSlot (writeSlot (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) message.currentTarget (recipientSlot (toArg message)) (add (storageAt (writeSlot (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) (sub (valArg message) (feeOf (checkState state message) message (valArg message))))) = (creditedFeeF (checkState state message) message (valArg message) (toArg message) (fromArg message)) := by
    simp only [creditedFeeF, debitedF, balTo, balFrom, hAF, sendOf]
  have eSS5 : (storeSub fork (accessSlot (storeSub fork (accessSlot (accessF (checkSub substate message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (originalAt (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message))) (storageAt (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message))) (sub (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) message.currentTarget (recipientSlot (toArg message)) (originalAt (readSlot (writeSlot (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) message.currentTarget (recipientSlot (toArg message))) (storageAt (readSlot (writeSlot (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) message.currentTarget (recipientSlot (toArg message))) (add (storageAt (writeSlot (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) (sub (valArg message) (feeOf (checkState state message) message (valArg message))))) = creditedSubFeeF fork (checkSub substate message) (checkState state message) message (valArg message) (toArg message) (fromArg message) := by
    rw [eo2, ec2, ec2', eo1, ec1, ec1']
    unfold creditedSubFeeF debitedSubF
    rw [eS]
  have eo3 : originalAt (readSlot (readSlot (readSlot (writeSlot (readSlot (writeSlot (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) message.currentTarget (recipientSlot (toArg message)) (add (storageAt (writeSlot (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) (sub (valArg message) (feeOf (checkState state message) message (valArg message))))) message.currentTarget 0) message.currentTarget (ownerSlot (storageAt (writeSlot (readSlot (writeSlot (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) message.currentTarget (recipientSlot (toArg message)) (add (storageAt (writeSlot (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) (sub (valArg message) (feeOf (checkState state message) message (valArg message))))) message.currentTarget 0))) message.currentTarget 0) message.currentTarget (ownerSlot (storageAt (writeSlot (readSlot (writeSlot (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) message.currentTarget (recipientSlot (toArg message)) (add (storageAt (writeSlot (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) (sub (valArg message) (feeOf (checkState state message) message (valArg message))))) message.currentTarget 0)) =
      originalAt (checkState state message) message.currentTarget (ownerSlot (ownerWordF (checkState state message) message (valArg message) (toArg message) (fromArg message))) := by
    rw [eS5]; simp only [originalAt_readSlot]; exact horig _
  have ec3 : storageAt (readSlot (readSlot (readSlot (writeSlot (readSlot (writeSlot (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) message.currentTarget (recipientSlot (toArg message)) (add (storageAt (writeSlot (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) (sub (valArg message) (feeOf (checkState state message) message (valArg message))))) message.currentTarget 0) message.currentTarget (ownerSlot (storageAt (writeSlot (readSlot (writeSlot (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) message.currentTarget (recipientSlot (toArg message)) (add (storageAt (writeSlot (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) (sub (valArg message) (feeOf (checkState state message) message (valArg message))))) message.currentTarget 0))) message.currentTarget 0) message.currentTarget (ownerSlot (storageAt (writeSlot (readSlot (writeSlot (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) message.currentTarget (recipientSlot (toArg message)) (add (storageAt (writeSlot (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) (sub (valArg message) (feeOf (checkState state message) message (valArg message))))) message.currentTarget 0)) = balOF (checkState state message) message (valArg message) (toArg message) (fromArg message) := by
    rw [eS5]; simp only [storageAt_readSlot]
  have ec3' : storageAt (writeSlot (readSlot (writeSlot (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) message.currentTarget (recipientSlot (toArg message)) (add (storageAt (writeSlot (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) (sub (valArg message) (feeOf (checkState state message) message (valArg message))))) message.currentTarget (ownerSlot (storageAt (writeSlot (readSlot (writeSlot (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) message.currentTarget (recipientSlot (toArg message)) (add (storageAt (writeSlot (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) (sub (valArg message) (feeOf (checkState state message) message (valArg message))))) message.currentTarget 0)) = balOF (checkState state message) message (valArg message) (toArg message) (fromArg message) := by
    rw [eS5]
  have hP : fxP1 state message c0 cB c10 cA c3 c4 cF < 97920 := by
    have := Complete.slotCost_le c0; have := Complete.slotCost_le cB
    have := Complete.slotCost_le c10; have := Complete.slotCost_le cA
    have := Complete.slotCost_le c3; have := Complete.slotCost_le c4
    have := Complete.slotCost_le cF
    have : mulCost (valArg message) ≤ 138 := by unfold mulCost; split <;> omega
    have : capCost (rawFee (checkState state message) message (valArg message)) (storageAt (checkState state message) message.currentTarget 4) ≤ 108 := by
      unfold capCost; split <;> omega
    simp only [fxP1, PRE_COST_F]; omega
  have hQ1 : 405 + slotCost cF < 97920 := by have := Complete.slotCost_le cF; omega
  have hQ2 : 308 + slotCost cT < 97920 := by have := Complete.slotCost_le cT; omega
  have hQ3 : 605 + slotCost cO < 97920 := by have := Complete.slotCost_le cO; omega
  have hM0 : (allowMem message (memF message) (fromArg message)).size = 96 := size_allowMem (size_mapMem size_MEM0 _ _) _
  have hP0 : loadWord (memoryReadBytes (allowMem message (memF message) (fromArg message)) 64 32) 0 32 = 0x60 :=
    ptr_allowMem (size_mapMem size_MEM0 _ _) (ptr_mapMem size_MEM0 mload_MEM0 _ _) _
  have hpre : ∀ g, fxP1 state message c0 cB c10 cA c3 c4 cF ≤ g → Gas.HoareG fork
      (At CODE message 0 [] .empty g state substate)
      (At CODE message 9191 ((recipientSlot (fromArg message)) :: (sub (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) (valArg message)) :: (sub (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) (valArg message)) :: [0x60, (sub (valArg message) (feeOf (checkState state message) message (valArg message))), (feeOf (checkState state message) message (valArg message)), MAX_UINT, (valArg message),
          toArg message, fromArg message, 0x1097, (valArg message), toArg message, fromArg message, 0x0392,
          BitVec.ofNat 256 (selector message.data)])
        (mapMem (mapMem (allowMem message (memF message) (fromArg message)) (mkey (fromArg message)) 2) (mkey (fromArg message)) 2) (g - fxP1 state message c0 cB c10 cA c3 c4 cF) (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) (accessSlot (accessF (checkSub substate message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message)))) := by
    intro g hg
    simp only [fxP1] at hg ⊢
    refine Triple.seq (preF hfork hlong hsz hsel hv hnp hnb hdep hc0 hcB hc10
      (Nat.le_trans (Nat.le_add_right _ _) hg)) ?_
    refine Triple.seq (segAFee (state := (checkState state message)) (substate := (checkSub substate message)) hfork (size_mapMem size_MEM0 _ _)
      hov hcA hc3 hc4 (by omega)) ?_
    rw [hmax]
    refine (maxToDebitWFee hfork (cF := cF) hfv (by rw [ec1']; exact hbal)
      (by rw [← eS]; exact hcF) (by omega) hM0).consequence (fun _ h => h) ?_
    intro e he
    have hx : g - (PRE_COST_F + slotCost c0 + slotCost cB + slotCost c10) -
        (361 + slotCost cA + slotCost c3 + slotCost c4 + mulCost (valArg message) + capCost (rawFee (checkState state message) message (valArg message)) (storageAt (checkState state message) message.currentTarget 4)) -
        (429 + slotCost cF) = g - (PRE_COST_F + slotCost c0 + slotCost cB + slotCost c10 +
          (790 + slotCost cA + slotCost c3 + slotCost c4 + slotCost cF + mulCost (valArg message) +
          capCost (rawFee (checkState state message) message (valArg message)) (storageAt (checkState state message) message.currentTarget 4))) := by omega
    rw [hx] at he
    exact he
  have hPb : loadWord (memoryReadBytes (allowMem message (memF message) (fromArg message)) 64 32) 0 32 = 0x60 := hP0
  have hMbs : (allowMem message (memF message) (fromArg message)).size = 96 := hM0
  have hMf : (mapMem (mapMem (allowMem message (memF message) (fromArg message)) (mkey (fromArg message)) 2) (mkey (fromArg message)) 2).size = 96 := size_mapMem (size_mapMem hMbs _ _) _ _
  have hPf : loadWord (memoryReadBytes (mapMem (mapMem (allowMem message (memF message) (fromArg message)) (mkey (fromArg message)) 2) (mkey (fromArg message)) 2) 64 32) 0 32 = 0x60 :=
    ptr_mapMem (size_mapMem hMbs _ _) (ptr_mapMem hMbs hPb _ _) _ _
  have hMt : (mapMem (mapMem (mapMem (mapMem (allowMem message (memF message) (fromArg message)) (mkey (fromArg message)) 2) (mkey (fromArg message)) 2) (mkey (toArg message)) 2) (mkey (toArg message)) 2).size = 96 := size_mapMem (size_mapMem hMf _ _) _ _
  have hPt : loadWord (memoryReadBytes (mapMem (mapMem (mapMem (mapMem (allowMem message (memF message) (fromArg message)) (mkey (fromArg message)) 2) (mkey (fromArg message)) 2) (mkey (toArg message)) 2) (mkey (toArg message)) 2) 64 32) 0 32 = 0x60 :=
    ptr_mapMem (size_mapMem hMf _ _) (ptr_mapMem hMf hPf _ _) _ _
  have hMo : (mapMem (mapMem (mapMem (mapMem (mapMem (mapMem (allowMem message (memF message) (fromArg message)) (mkey (fromArg message)) 2) (mkey (fromArg message)) 2) (mkey (toArg message)) 2) (mkey (toArg message)) 2) (mkey (ownerKey (storageAt (writeSlot (readSlot (writeSlot (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) message.currentTarget (recipientSlot (toArg message)) (add (storageAt (writeSlot (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) (sub (valArg message) (feeOf (checkState state message) message (valArg message))))) message.currentTarget 0))) 2) (mkey (ownerKey (storageAt (writeSlot (readSlot (writeSlot (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) message.currentTarget (recipientSlot (toArg message)) (add (storageAt (writeSlot (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) (sub (valArg message) (feeOf (checkState state message) message (valArg message))))) message.currentTarget 0))) 2).size = 96 := size_mapMem (size_mapMem hMt _ _) _ _
  have hPo : loadWord (memoryReadBytes (mapMem (mapMem (mapMem (mapMem (mapMem (mapMem (allowMem message (memF message) (fromArg message)) (mkey (fromArg message)) 2) (mkey (fromArg message)) 2) (mkey (toArg message)) 2) (mkey (toArg message)) 2) (mkey (ownerKey (storageAt (writeSlot (readSlot (writeSlot (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) message.currentTarget (recipientSlot (toArg message)) (add (storageAt (writeSlot (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) (sub (valArg message) (feeOf (checkState state message) message (valArg message))))) message.currentTarget 0))) 2) (mkey (ownerKey (storageAt (writeSlot (readSlot (writeSlot (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) message.currentTarget (recipientSlot (toArg message)) (add (storageAt (writeSlot (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) (sub (valArg message) (feeOf (checkState state message) message (valArg message))))) message.currentTarget 0))) 2) 64 32) 0 32 = 0x60 :=
    ptr_mapMem (size_mapMem hMt _ _) (ptr_mapMem hMt hPt _ _) _ _
  have hcT' : coldIn (storeSub fork (accessSlot (accessF (checkSub substate message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (originalAt (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message))) (storageAt (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message))) (sub (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message)) = cT := by
    rw [coldIn_storeSub, ← eS]; exact hcT
  have hmid2 := fun g (hg : 308 + slotCost cT ≤ g) => debitToCreditWFee (state := (writeSlot (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) (valArg message))))
    (substate := (storeSub fork (accessSlot (accessF (checkSub substate message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (originalAt (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message))) (storageAt (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message))) (sub (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) (valArg message)))) (nb := (sub (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) (send := (sub (valArg message) (feeOf (checkState state message) message (valArg message)))) (fee := (feeOf (checkState state message) message (valArg message))) (A := MAX_UINT) (v := (valArg message))
    (t := toArg message) (f := fromArg message) (sel := BitVec.ofNat 256 (selector message.data))
    (M := (mapMem (mapMem (allowMem message (memF message) (fromArg message)) (mkey (fromArg message)) 2) (mkey (fromArg message)) 2)) hfork hMf (by rw [ec2']; exact hto) hcT' hg
  have hc0' : coldIn (storeSub fork (accessSlot (storeSub fork (accessSlot (accessF (checkSub substate message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (originalAt (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message))) (storageAt (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message))) (sub (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) message.currentTarget (recipientSlot (toArg message)) (originalAt (readSlot (writeSlot (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) message.currentTarget (recipientSlot (toArg message))) (storageAt (readSlot (writeSlot (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) message.currentTarget (recipientSlot (toArg message))) (add (storageAt (writeSlot (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) (sub (valArg message) (feeOf (checkState state message) message (valArg message))))) message.currentTarget 0 = false := (TransferFee.coldIn_storeSub_false (TransferFrom.coldIn_accessSlot_false (TransferFee.coldIn_storeSub_false (TransferFrom.coldIn_accessSlot_false (TransferFrom.coldIn_accessSlot_false (TransferFrom.coldIn_accessSlot_false (TransferFrom.coldIn_accessSlot_false (TransferFrom.coldIn_accessSlot_false (TransferFrom.coldIn_accessSlot_false (coldIn_accessSlot_self _ _ _))))))))))
  have hcO' : coldIn (accessSlot (storeSub fork (accessSlot (storeSub fork (accessSlot (accessF (checkSub substate message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (originalAt (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message))) (storageAt (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message))) (sub (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) message.currentTarget (recipientSlot (toArg message)) (originalAt (readSlot (writeSlot (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) message.currentTarget (recipientSlot (toArg message))) (storageAt (readSlot (writeSlot (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) message.currentTarget (recipientSlot (toArg message))) (add (storageAt (writeSlot (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) (sub (valArg message) (feeOf (checkState state message) message (valArg message))))) message.currentTarget 0) message.currentTarget (ownerSlot (storageAt (writeSlot (readSlot (writeSlot (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) message.currentTarget (recipientSlot (toArg message)) (add (storageAt (writeSlot (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) (sub (valArg message) (feeOf (checkState state message) message (valArg message))))) message.currentTarget 0)) = cO := by
    rw [TransferFee.coldIn_accessSlot_of_warm hc0', eSS5, eS5]; exact hcO
  have hmid3 := fun g (hg : 605 + slotCost cO ≤ g) => creditToOwnerW (state := (writeSlot (readSlot (writeSlot (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) message.currentTarget (recipientSlot (toArg message)) (add (storageAt (writeSlot (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) (sub (valArg message) (feeOf (checkState state message) message (valArg message))))))
    (substate := (storeSub fork (accessSlot (storeSub fork (accessSlot (accessF (checkSub substate message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (originalAt (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message))) (storageAt (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message))) (sub (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) message.currentTarget (recipientSlot (toArg message)) (originalAt (readSlot (writeSlot (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) message.currentTarget (recipientSlot (toArg message))) (storageAt (readSlot (writeSlot (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) message.currentTarget (recipientSlot (toArg message))) (add (storageAt (writeSlot (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) (sub (valArg message) (feeOf (checkState state message) message (valArg message)))))) (nt := (add (storageAt (writeSlot (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) (sub (valArg message) (feeOf (checkState state message) message (valArg message))))) (send := (sub (valArg message) (feeOf (checkState state message) message (valArg message)))) (fee := (feeOf (checkState state message) message (valArg message))) (A := MAX_UINT) (v := (valArg message))
    (t := toArg message) (f := fromArg message) (sel := BitVec.ofNat 256 (selector message.data))
    (M := (mapMem (mapMem (mapMem (mapMem (allowMem message (memF message) (fromArg message)) (mkey (fromArg message)) 2) (mkey (fromArg message)) 2) (mkey (toArg message)) 2) (mkey (toArg message)) 2)) hfork hfee hMt hc0' hcO' (by rw [ec3']; exact hown) hg
  have hpost := fun g (hg : 3839 ≤ g) => ownerPostF (state := (writeSlot (readSlot (readSlot (readSlot (writeSlot (readSlot (writeSlot (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) message.currentTarget (recipientSlot (toArg message)) (add (storageAt (writeSlot (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) (sub (valArg message) (feeOf (checkState state message) message (valArg message))))) message.currentTarget 0) message.currentTarget (ownerSlot (storageAt (writeSlot (readSlot (writeSlot (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) message.currentTarget (recipientSlot (toArg message)) (add (storageAt (writeSlot (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) (sub (valArg message) (feeOf (checkState state message) message (valArg message))))) message.currentTarget 0))) message.currentTarget 0) message.currentTarget (ownerSlot (storageAt (writeSlot (readSlot (writeSlot (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) message.currentTarget (recipientSlot (toArg message)) (add (storageAt (writeSlot (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) (sub (valArg message) (feeOf (checkState state message) message (valArg message))))) message.currentTarget 0)) (add (storageAt (writeSlot (readSlot (writeSlot (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) message.currentTarget (recipientSlot (toArg message)) (add (storageAt (writeSlot (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) (sub (valArg message) (feeOf (checkState state message) message (valArg message))))) message.currentTarget (ownerSlot (storageAt (writeSlot (readSlot (writeSlot (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) message.currentTarget (recipientSlot (toArg message)) (add (storageAt (writeSlot (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) (sub (valArg message) (feeOf (checkState state message) message (valArg message))))) message.currentTarget 0))) (feeOf (checkState state message) message (valArg message))))) (substate := (storeSub fork (accessSlot (accessSlot (accessSlot (storeSub fork (accessSlot (storeSub fork (accessSlot (accessF (checkSub substate message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (originalAt (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message))) (storageAt (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message))) (sub (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) message.currentTarget (recipientSlot (toArg message)) (originalAt (readSlot (writeSlot (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) message.currentTarget (recipientSlot (toArg message))) (storageAt (readSlot (writeSlot (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) message.currentTarget (recipientSlot (toArg message))) (add (storageAt (writeSlot (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) (sub (valArg message) (feeOf (checkState state message) message (valArg message))))) message.currentTarget 0) message.currentTarget (ownerSlot (storageAt (writeSlot (readSlot (writeSlot (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) message.currentTarget (recipientSlot (toArg message)) (add (storageAt (writeSlot (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) (sub (valArg message) (feeOf (checkState state message) message (valArg message))))) message.currentTarget 0))) message.currentTarget 0) message.currentTarget (ownerSlot (storageAt (writeSlot (readSlot (writeSlot (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) message.currentTarget (recipientSlot (toArg message)) (add (storageAt (writeSlot (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) (sub (valArg message) (feeOf (checkState state message) message (valArg message))))) message.currentTarget 0)) (originalAt (readSlot (readSlot (readSlot (writeSlot (readSlot (writeSlot (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) message.currentTarget (recipientSlot (toArg message)) (add (storageAt (writeSlot (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) (sub (valArg message) (feeOf (checkState state message) message (valArg message))))) message.currentTarget 0) message.currentTarget (ownerSlot (storageAt (writeSlot (readSlot (writeSlot (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) message.currentTarget (recipientSlot (toArg message)) (add (storageAt (writeSlot (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) (sub (valArg message) (feeOf (checkState state message) message (valArg message))))) message.currentTarget 0))) message.currentTarget 0) message.currentTarget (ownerSlot (storageAt (writeSlot (readSlot (writeSlot (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) message.currentTarget (recipientSlot (toArg message)) (add (storageAt (writeSlot (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) (sub (valArg message) (feeOf (checkState state message) message (valArg message))))) message.currentTarget 0))) (storageAt (readSlot (readSlot (readSlot (writeSlot (readSlot (writeSlot (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) message.currentTarget (recipientSlot (toArg message)) (add (storageAt (writeSlot (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) (sub (valArg message) (feeOf (checkState state message) message (valArg message))))) message.currentTarget 0) message.currentTarget (ownerSlot (storageAt (writeSlot (readSlot (writeSlot (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) message.currentTarget (recipientSlot (toArg message)) (add (storageAt (writeSlot (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) (sub (valArg message) (feeOf (checkState state message) message (valArg message))))) message.currentTarget 0))) message.currentTarget 0) message.currentTarget (ownerSlot (storageAt (writeSlot (readSlot (writeSlot (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) message.currentTarget (recipientSlot (toArg message)) (add (storageAt (writeSlot (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) (sub (valArg message) (feeOf (checkState state message) message (valArg message))))) message.currentTarget 0))) (add (storageAt (writeSlot (readSlot (writeSlot (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) message.currentTarget (recipientSlot (toArg message)) (add (storageAt (writeSlot (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) (sub (valArg message) (feeOf (checkState state message) message (valArg message))))) message.currentTarget (ownerSlot (storageAt (writeSlot (readSlot (writeSlot (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) message.currentTarget (recipientSlot (toArg message)) (add (storageAt (writeSlot (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) (sub (valArg message) (feeOf (checkState state message) message (valArg message))))) message.currentTarget 0))) (feeOf (checkState state message) message (valArg message)))))
    (no := (add (storageAt (writeSlot (readSlot (writeSlot (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) message.currentTarget (recipientSlot (toArg message)) (add (storageAt (writeSlot (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) (sub (valArg message) (feeOf (checkState state message) message (valArg message))))) message.currentTarget (ownerSlot (storageAt (writeSlot (readSlot (writeSlot (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) message.currentTarget (recipientSlot (toArg message)) (add (storageAt (writeSlot (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) (sub (valArg message) (feeOf (checkState state message) message (valArg message))))) message.currentTarget 0))) (feeOf (checkState state message) message (valArg message)))) (send := (sub (valArg message) (feeOf (checkState state message) message (valArg message)))) (fee := (feeOf (checkState state message) message (valArg message))) (A := MAX_UINT) (v := (valArg message))
    (t := toArg message) (f := fromArg message) (sel := BitVec.ofNat 256 (selector message.data))
    (M := (mapMem (mapMem (mapMem (mapMem (mapMem (mapMem (allowMem message (memF message) (fromArg message)) (mkey (fromArg message)) 2) (mkey (fromArg message)) 2) (mkey (toArg message)) 2) (mkey (toArg message)) 2) (mkey (ownerKey (storageAt (writeSlot (readSlot (writeSlot (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) message.currentTarget (recipientSlot (toArg message)) (add (storageAt (writeSlot (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) (sub (valArg message) (feeOf (checkState state message) message (valArg message))))) message.currentTarget 0))) 2) (mkey (ownerKey (storageAt (writeSlot (readSlot (writeSlot (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) message.currentTarget (recipientSlot (toArg message)) (add (storageAt (writeSlot (readSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) (sub (valArg message) (feeOf (checkState state message) message (valArg message))))) message.currentTarget 0))) 2)) hfork hstatic hMo hPo (TransferFee.coldIn_storeSub_false (coldIn_accessSlot_self _ _ _)) hg
  have hx := Complete.exactS_write hfork hpre hP
    (fun _ _ => by simp only [Complete.getStorage_readSlot]) (by code_fact) (by code_fact)
    hstatic hacc4 (coldIn_accessSlot_self _ _ _)
      (Complete.exactS_write hfork hmid2 hQ2 (fun _ _ => by simp only [Complete.getStorage_readSlot])
        (by code_fact) (by code_fact) hstatic hacc6 (coldIn_accessSlot_self _ _ _)
        (Complete.exactS_write hfork hmid3 hQ3 (fun _ _ => by simp only [Complete.getStorage_readSlot])
          (by code_fact) (by code_fact) hstatic hacc8 (TransferFrom.coldIn_accessSlot_false (coldIn_accessSlot_self _ _ _))
          (Complete.exactS_halt hpost (by decide) (fun _ _ => by simp only [Complete.getStorage_readSlot]))))
  obtain ⟨hgas, hiff, hend⟩ := hx.run start (runChild := runChild) within
  rw [eo3, ec3, ec3', eo2, ec2, ec2', eo1, ec1, ec1'] at hiff
  refine ⟨hiff, fun s hrun hok => ?_⟩
  have hok' := hiff.mp ⟨s, hrun, hok⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := hend s hrun hok
  rw [eo3, ec3, ec3', eo2, ec2, ec2', eo1, ec1, ec1'] at h5
  refine ⟨h1, h2, ?_, ?_, ?_, ?_⟩
  · rw [h3, eS5]
  · rw [h4, eo3, ec3, ec3', eSS5, eS5]
  · obtain ⟨o1, o2, o3, o4⟩ := hok'
    have e1 := Complete.wMeter_gasLeft o1
    have e2 := Complete.wMeter_gasLeft o2
    have e3 := Complete.wMeter_gasLeft o3
    have e4 : s.gas.gasLeft = _ := congrArg StateGasMeter.gasLeft h5
    have hac : allowCostF fork (checkState state message) message (valArg message) (fromArg message) = 26 := by
      simp only [allowCostF, allowCost, hmax, ite_true]
    simp only [feeCostF, hac, debitCostF, creditCostFeeF, ownerCostF, fxP1, gxM1, gxM2, gxM3, sendOf,
      wBump] at e1 e2 e3 e4 o4 ⊢
    omega
  · rw [h5]


/-- The meter after the write of the allowance (fee above 0, `_allowance ≠ MAX_UINT`). -/
abbrev gaM0 (fork : Fork) (g : StateGasMeter) (state : State.TransactionState)
    (message : Message fork) (c0 cB c10 cA c3 c4 : Bool) : StateGasMeter :=
  wMeter fork g (faP0 state message c0 cB c10 cA c3 c4) (originalAt (checkState state message) message.currentTarget (allowFrom message (fromArg message))) (allowOf (checkState state message) message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message)) false

/-- The meter after the write of `balances[_from]` (fee above 0, `_allowance ≠ MAX_UINT`). -/
abbrev gaM1 (fork : Fork) (g : StateGasMeter) (state : State.TransactionState)
    (message : Message fork) (c0 cB c10 cA c3 c4 cF : Bool) : StateGasMeter :=
  wMeter fork (gaM0 fork g state message c0 cB c10 cA c3 c4) (405 + slotCost cF) (originalAt (checkState state message) message.currentTarget (recipientSlot (fromArg message))) (balFrom (checkState state message) message (valArg message) (fromArg message)) (sub (balFrom (checkState state message) message (valArg message) (fromArg message)) (valArg message)) false

/-- The meter after the write of `balances[_to]` (fee above 0, `_allowance ≠ MAX_UINT`). -/
abbrev gaM2 (fork : Fork) (g : StateGasMeter) (state : State.TransactionState)
    (message : Message fork) (c0 cB c10 cA c3 c4 cF cT : Bool) : StateGasMeter :=
  wMeter fork (gaM1 fork g state message c0 cB c10 cA c3 c4 cF) (308 + slotCost cT) (originalAt (checkState state message) message.currentTarget (recipientSlot (toArg message))) (balTo (checkState state message) message (valArg message) (toArg message) (fromArg message)) (add (balTo (checkState state message) message (valArg message) (toArg message) (fromArg message)) (sendOf (checkState state message) message (valArg message))) false

/-- The meter after the write of `balances[owner]` (fee above 0, `_allowance ≠ MAX_UINT`). -/
abbrev gaM3 (fork : Fork) (g : StateGasMeter) (state : State.TransactionState)
    (message : Message fork) (c0 cB c10 cA c3 c4 cF cT cO : Bool) : StateGasMeter :=
  wMeter fork (gaM2 fork g state message c0 cB c10 cA c3 c4 cF cT) (605 + slotCost cO) (originalAt (checkState state message) message.currentTarget (ownerSlot (ownerWordF (checkState state message) message (valArg message) (toArg message) (fromArg message)))) (balOF (checkState state message) message (valArg message) (toArg message) (fromArg message)) (add (balOF (checkState state message) message (valArg message) (toArg message) (fromArg message)) (feeOf (checkState state message) message (valArg message))) false

/-- **transferFrom(f, t, v), fee above 0, allowance `A ≠ MAX_UINT` with `v ≤ A`, over the EIP-8037
meter, exactly, at any reservoir, refills allowed.** Four writes: the allowance, `balances[f]`,
`balances[t]`, `balances[owner]`. The run ends with no error if and only if the chain condition
holds; every run that ends with no error has the state and substate of `spec_feeF`, with
`gasLeft + feeCostF = gas` plus the four bumps. -/
theorem transferFromFee_sgm (hfork : .berlin ≤ fork)
    (hstatic : message.isStatic = false) (hacc : hasAccount state message.currentTarget)
    (hlong : 100 ≤ message.data.size) (hsz : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x23b872dd) (hv : message.value = 0)
    (hnp : byte20 (storageAt state message.currentTarget 0) = 0)
    (hnb : (storageAt state message.currentTarget (blackFrom (fromArg message))).toNat % 256 = 0)
    (hdep : byte20 (storageAt state message.currentTarget 10) = 0)
    (hov : (valArg message).toNat *
      (storageAt (checkState state message) message.currentTarget 3).toNat < 2 ^ 256)
    (hfee : feeOf (checkState state message) message (valArg message) ≠ 0)
    (hfv : (feeOf (checkState state message) message (valArg message)).toNat ≤
      (valArg message).toNat)
    (hmax : allowOf (checkState state message) message (fromArg message) ≠ MAX_UINT)
    (hle : (valArg message).toNat ≤ (allowOf (checkState state message) message (fromArg message)).toNat)
    (hbal : (valArg message).toNat ≤
      (balFrom (checkState state message) message (valArg message) (fromArg message)).toNat)
    (hto : (balTo (checkState state message) message (valArg message) (toArg message)
      (fromArg message)).toNat +
      (sendOf (checkState state message) message (valArg message)).toNat < 2 ^ 256)
    (hown : (balOF (checkState state message) message (valArg message) (toArg message)
      (fromArg message)).toNat +
      (feeOf (checkState state message) message (valArg message)).toNat < 2 ^ 256)
    {c0 cB c10 cA c3 c4 cF cT cO : Bool} (hc0 : coldIn substate message.currentTarget 0 = c0)
    (hcB : coldIn (accessSlot substate message.currentTarget 0) message.currentTarget
      (blackFrom (fromArg message)) = cB)
    (hc10 : coldIn (accessSlot (accessSlot substate message.currentTarget 0) message.currentTarget
      (blackFrom (fromArg message))) message.currentTarget 10 = c10)
    (hcA : coldIn (checkSub substate message) message.currentTarget
      (allowFrom message (fromArg message)) = cA)
    (hc3 : coldIn (accessSlot (checkSub substate message) message.currentTarget
      (allowFrom message (fromArg message))) message.currentTarget 3 = c3)
    (hc4 : coldIn (accessSlot (accessSlot (checkSub substate message) message.currentTarget
      (allowFrom message (fromArg message))) message.currentTarget 3) message.currentTarget 4 = c4)
    (hcF : coldIn (allowedSubF fork (checkSub substate message) (checkState state message) message
      (valArg message) (fromArg message)) message.currentTarget (recipientSlot (fromArg message)) =
        cF)
    (hcT : coldIn (accessSlot (allowedSubF fork (checkSub substate message)
      (checkState state message) message (valArg message) (fromArg message)) message.currentTarget
      (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (toArg message)) = cT)
    (hcO : coldIn (creditedSubFeeF fork (checkSub substate message) (checkState state message)
      message (valArg message) (toArg message) (fromArg message)) message.currentTarget
      (ownerSlot (ownerWordF (checkState state message) message (valArg message) (toArg message)
        (fromArg message))) = cO)
    {gas : Nat} {m : Evm fork StateGasMeter}
    (start : At CODE message 0 [] .empty gas state substate (Meter.toNat m))
    {bound : Nat} {runChild : MessageRunner fork StateGasMeter bound}
    (within : GasMeter.gasHeld m.gas ≤ bound) :
    (Shadow.RunsOkS fork bound runChild m within ↔
      wOk fork m.gas (faP0 state message c0 cB c10 cA c3 c4) (originalAt (checkState state message) message.currentTarget (allowFrom message (fromArg message))) (allowOf (checkState state message) message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message)) false ∧
      wOk fork (gaM0 fork m.gas state message c0 cB c10 cA c3 c4) (405 + slotCost cF) (originalAt (checkState state message) message.currentTarget (recipientSlot (fromArg message))) (balFrom (checkState state message) message (valArg message) (fromArg message)) (sub (balFrom (checkState state message) message (valArg message) (fromArg message)) (valArg message)) false ∧
      wOk fork (gaM1 fork m.gas state message c0 cB c10 cA c3 c4 cF) (308 + slotCost cT) (originalAt (checkState state message) message.currentTarget (recipientSlot (toArg message))) (balTo (checkState state message) message (valArg message) (toArg message) (fromArg message)) (add (balTo (checkState state message) message (valArg message) (toArg message) (fromArg message)) (sendOf (checkState state message) message (valArg message)))
        false ∧
      wOk fork (gaM2 fork m.gas state message c0 cB c10 cA c3 c4 cF cT) (605 + slotCost cO) (originalAt (checkState state message) message.currentTarget (ownerSlot (ownerWordF (checkState state message) message (valArg message) (toArg message) (fromArg message)))) (balOF (checkState state message) message (valArg message) (toArg message) (fromArg message)) (add (balOF (checkState state message) message (valArg message) (toArg message) (fromArg message)) (feeOf (checkState state message) message (valArg message)))
        false ∧
      3839 ≤ (gaM3 fork m.gas state message c0 cB c10 cA c3 c4 cF cT cO).gasLeft) ∧
    ∀ s, Evm.runFrame (step fork) (step_decreases fork) bound runChild m within = .ok s →
      s.error = none →
      s.running = false ∧ s.output = .empty ∧
      s.state = feeStateF (checkState state message) message (valArg message) (toArg message)
        (fromArg message) ∧
      s.substate = feeSubF fork (checkSub substate message) (checkState state message) message
        (valArg message) (toArg message) (fromArg message) ∧
      s.gas.gasLeft + feeCostF fork state message c0 cB c10 cA c3 c4 cF cT cO =
        gas + wBump fork m.gas (originalAt (checkState state message) message.currentTarget (allowFrom message (fromArg message))) (allowOf (checkState state message) message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message)) +
          wBump fork (gaM0 fork m.gas state message c0 cB c10 cA c3 c4) (originalAt (checkState state message) message.currentTarget (recipientSlot (fromArg message))) (balFrom (checkState state message) message (valArg message) (fromArg message)) (sub (balFrom (checkState state message) message (valArg message) (fromArg message)) (valArg message)) +
          wBump fork (gaM1 fork m.gas state message c0 cB c10 cA c3 c4 cF) (originalAt (checkState state message) message.currentTarget (recipientSlot (toArg message))) (balTo (checkState state message) message (valArg message) (toArg message) (fromArg message)) (add (balTo (checkState state message) message (valArg message) (toArg message) (fromArg message)) (sendOf (checkState state message) message (valArg message))) +
          wBump fork (gaM2 fork m.gas state message c0 cB c10 cA c3 c4 cF cT) (originalAt (checkState state message) message.currentTarget (ownerSlot (ownerWordF (checkState state message) message (valArg message) (toArg message) (fromArg message)))) (balOF (checkState state message) message (valArg message) (toArg message) (fromArg message)) (add (balOF (checkState state message) message (valArg message) (toArg message) (fromArg message)) (feeOf (checkState state message) message (valArg message))) ∧
      s.gas = { gaM3 fork m.gas state message c0 cB c10 cA c3 c4 cF cT cO with gasLeft := s.gas.gasLeft } := by
  have hAF : allowedF (checkState state message) message (valArg message) (fromArg message) = (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) := by
    simp only [allowedF, allowState, if_neg hmax]
  have eS : allowedSubF fork (checkSub substate message) (checkState state message) message (valArg message) (fromArg message) =
      storeSub fork (accessF (checkSub substate message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (originalAt (checkState state message) message.currentTarget (allowFrom message (fromArg message))) (allowOf (checkState state message) message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message)) := by
    simp only [allowedSubF, allowSub, if_neg hmax]
  have haccS : hasAccount (checkState state message) message.currentTarget :=
    hasAccount_readSlot (hasAccount_readSlot (hasAccount_readSlot hacc))
  have hacc3 : hasAccount (readsF (checkState state message) message (fromArg message)) message.currentTarget :=
    hasAccount_readSlot (hasAccount_readSlot (hasAccount_readSlot haccS))
  have haccb := hasAccount_writeSlot (n := (allowFrom message (fromArg message))) (v := (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) hacc3
  have hacc4 := hasAccount_readSlot (n := (recipientSlot (fromArg message))) (other := message.currentTarget) haccb
  have hacc5 := hasAccount_writeSlot (n := (recipientSlot (fromArg message))) (v := (sub (storageAt (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) hacc4
  have hacc6 := hasAccount_readSlot (n := (recipientSlot (toArg message))) (other := message.currentTarget) hacc5
  have hacc7 := hasAccount_writeSlot (n := (recipientSlot (toArg message))) (v := (add (storageAt (writeSlot (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) (sub (valArg message) (feeOf (checkState state message) message (valArg message))))) hacc6
  have hacc8 : hasAccount (readSlot (readSlot (readSlot (writeSlot (readSlot (writeSlot (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) message.currentTarget (recipientSlot (toArg message)) (add (storageAt (writeSlot (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) (sub (valArg message) (feeOf (checkState state message) message (valArg message))))) message.currentTarget 0) message.currentTarget (ownerSlot (storageAt (writeSlot (readSlot (writeSlot (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) message.currentTarget (recipientSlot (toArg message)) (add (storageAt (writeSlot (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) (sub (valArg message) (feeOf (checkState state message) message (valArg message))))) message.currentTarget 0))) message.currentTarget 0) message.currentTarget :=
    hasAccount_readSlot (hasAccount_readSlot (hasAccount_readSlot hacc7))
  have hacc4' : hasAccount (readSlot (allowedF (checkState state message) message (valArg message) (fromArg message)) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget :=
    hasAccount_readSlot (hasAccount_allowState hacc3)
  have hacc5' : hasAccount (readSlot (debitedF (checkState state message) message (valArg message) (fromArg message)) message.currentTarget (recipientSlot (toArg message))) message.currentTarget :=
    hasAccount_readSlot (hasAccount_writeSlot hacc4')
  have horig : ∀ mm, originalAt (creditedFeeF (checkState state message) message (valArg message) (toArg message) (fromArg message)) message.currentTarget mm = originalAt (checkState state message) message.currentTarget mm := by
    intro mm
    rw [originalAt_writeSlot hacc5', originalAt_readSlot, originalAt_writeSlot hacc4',
      originalAt_readSlot, originalAt_allowState hacc3]
    simp only [readsF, originalAt_readSlot]
  have eo0 : originalAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) = originalAt (checkState state message) message.currentTarget (allowFrom message (fromArg message)) := by
    simp only [readsF, originalAt_readSlot]
  have ec0 : storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) = (allowOf (checkState state message) message (fromArg message)) := by
    simp only [readsF, storageAt_readSlot, allowOf]
  have ec1' : storageAt (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message)) = balFrom (checkState state message) message (valArg message) (fromArg message) := by
    simp only [balFrom, hAF]
  have ec1 : storageAt (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) =
      balFrom (checkState state message) message (valArg message) (fromArg message) := by
    rw [storageAt_readSlot]; exact ec1'
  have eo1 : originalAt (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) = originalAt (checkState state message) message.currentTarget (recipientSlot (fromArg message)) := by
    rw [originalAt_readSlot, originalAt_writeSlot hacc3]; simp only [readsF, originalAt_readSlot]
  have ec2' : storageAt (writeSlot (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message)) =
      balTo (checkState state message) message (valArg message) (toArg message) (fromArg message) := by
    simp only [balTo, debitedF, balFrom, hAF]
  have ec2 : storageAt (readSlot (writeSlot (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) message.currentTarget (recipientSlot (toArg message)) =
      balTo (checkState state message) message (valArg message) (toArg message) (fromArg message) := by
    rw [storageAt_readSlot]; exact ec2'
  have eo2 : originalAt (readSlot (writeSlot (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) message.currentTarget (recipientSlot (toArg message)) = originalAt (checkState state message) message.currentTarget (recipientSlot (toArg message)) := by
    rw [originalAt_readSlot, originalAt_writeSlot hacc4, originalAt_readSlot]
    rw [originalAt_writeSlot hacc3]; simp only [readsF, originalAt_readSlot]
  have eS5 : (writeSlot (readSlot (writeSlot (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) message.currentTarget (recipientSlot (toArg message)) (add (storageAt (writeSlot (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) (sub (valArg message) (feeOf (checkState state message) message (valArg message))))) = (creditedFeeF (checkState state message) message (valArg message) (toArg message) (fromArg message)) := by
    simp only [creditedFeeF, debitedF, balTo, balFrom, hAF, sendOf]
  have eSS5 : (storeSub fork (accessSlot (storeSub fork (accessSlot (storeSub fork (accessF (checkSub substate message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (originalAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message))) (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message))) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (originalAt (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message))) (storageAt (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message))) (sub (storageAt (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) message.currentTarget (recipientSlot (toArg message)) (originalAt (readSlot (writeSlot (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) message.currentTarget (recipientSlot (toArg message))) (storageAt (readSlot (writeSlot (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) message.currentTarget (recipientSlot (toArg message))) (add (storageAt (writeSlot (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) (sub (valArg message) (feeOf (checkState state message) message (valArg message))))) = creditedSubFeeF fork (checkSub substate message) (checkState state message) message (valArg message) (toArg message) (fromArg message) := by
    rw [eo2, ec2, ec2', eo1, ec1, ec1', eo0, ec0]
    unfold creditedSubFeeF debitedSubF
    rw [eS]
  have eo3 : originalAt (readSlot (readSlot (readSlot (writeSlot (readSlot (writeSlot (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) message.currentTarget (recipientSlot (toArg message)) (add (storageAt (writeSlot (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) (sub (valArg message) (feeOf (checkState state message) message (valArg message))))) message.currentTarget 0) message.currentTarget (ownerSlot (storageAt (writeSlot (readSlot (writeSlot (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) message.currentTarget (recipientSlot (toArg message)) (add (storageAt (writeSlot (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) (sub (valArg message) (feeOf (checkState state message) message (valArg message))))) message.currentTarget 0))) message.currentTarget 0) message.currentTarget (ownerSlot (storageAt (writeSlot (readSlot (writeSlot (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) message.currentTarget (recipientSlot (toArg message)) (add (storageAt (writeSlot (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) (sub (valArg message) (feeOf (checkState state message) message (valArg message))))) message.currentTarget 0)) =
      originalAt (checkState state message) message.currentTarget (ownerSlot (ownerWordF (checkState state message) message (valArg message) (toArg message) (fromArg message))) := by
    rw [eS5]; simp only [originalAt_readSlot]; exact horig _
  have ec3 : storageAt (readSlot (readSlot (readSlot (writeSlot (readSlot (writeSlot (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) message.currentTarget (recipientSlot (toArg message)) (add (storageAt (writeSlot (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) (sub (valArg message) (feeOf (checkState state message) message (valArg message))))) message.currentTarget 0) message.currentTarget (ownerSlot (storageAt (writeSlot (readSlot (writeSlot (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) message.currentTarget (recipientSlot (toArg message)) (add (storageAt (writeSlot (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) (sub (valArg message) (feeOf (checkState state message) message (valArg message))))) message.currentTarget 0))) message.currentTarget 0) message.currentTarget (ownerSlot (storageAt (writeSlot (readSlot (writeSlot (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) message.currentTarget (recipientSlot (toArg message)) (add (storageAt (writeSlot (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) (sub (valArg message) (feeOf (checkState state message) message (valArg message))))) message.currentTarget 0)) = balOF (checkState state message) message (valArg message) (toArg message) (fromArg message) := by
    rw [eS5]; simp only [storageAt_readSlot]
  have ec3' : storageAt (writeSlot (readSlot (writeSlot (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) message.currentTarget (recipientSlot (toArg message)) (add (storageAt (writeSlot (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) (sub (valArg message) (feeOf (checkState state message) message (valArg message))))) message.currentTarget (ownerSlot (storageAt (writeSlot (readSlot (writeSlot (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) message.currentTarget (recipientSlot (toArg message)) (add (storageAt (writeSlot (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) (sub (valArg message) (feeOf (checkState state message) message (valArg message))))) message.currentTarget 0)) = balOF (checkState state message) message (valArg message) (toArg message) (fromArg message) := by
    rw [eS5]
  have hP : faP0 state message c0 cB c10 cA c3 c4 < 97920 := by
    have := Complete.slotCost_le c0; have := Complete.slotCost_le cB
    have := Complete.slotCost_le c10; have := Complete.slotCost_le cA
    have := Complete.slotCost_le c3; have := Complete.slotCost_le c4
    have := Complete.slotCost_le cF
    have : mulCost (valArg message) ≤ 138 := by unfold mulCost; split <;> omega
    have : capCost (rawFee (checkState state message) message (valArg message)) (storageAt (checkState state message) message.currentTarget 4) ≤ 108 := by
      unfold capCost; split <;> omega
    simp only [faP0, PRE_COST_F]; omega
  have hQ1 : 405 + slotCost cF < 97920 := by have := Complete.slotCost_le cF; omega
  have hQ2 : 308 + slotCost cT < 97920 := by have := Complete.slotCost_le cT; omega
  have hQ3 : 605 + slotCost cO < 97920 := by have := Complete.slotCost_le cO; omega
  have hM0 : (allowMem message (memF message) (fromArg message)).size = 96 := size_allowMem (size_mapMem size_MEM0 _ _) _
  have hP0 : loadWord (memoryReadBytes (allowMem message (memF message) (fromArg message)) 64 32) 0 32 = 0x60 :=
    ptr_allowMem (size_mapMem size_MEM0 _ _) (ptr_mapMem size_MEM0 mload_MEM0 _ _) _
  have hpre : ∀ g, faP0 state message c0 cB c10 cA c3 c4 ≤ g → Gas.HoareG fork
      (At CODE message 0 [] .empty g state substate)
      (At CODE message 9020 ((allowFrom message (fromArg message)) :: (sub (allowOf (checkState state message) message (fromArg message)) (valArg message)) :: (sub (allowOf (checkState state message) message (fromArg message)) (valArg message)) :: [0x60, 0, (feeOf (checkState state message) message (valArg message)), (allowOf (checkState state message) message (fromArg message)), (valArg message), toArg message,
          fromArg message, 0x1097, (valArg message), toArg message, fromArg message, 0x0392,
          BitVec.ofNat 256 (selector message.data)])
        (allowMem message (allowMem message (memF message) (fromArg message)) (fromArg message)) (g - faP0 state message c0 cB c10 cA c3 c4) (readsF (checkState state message) message (fromArg message)) (accessF (checkSub substate message) message (fromArg message))) := by
    intro g hg
    simp only [faP0] at hg ⊢
    refine Triple.seq (preF hfork hlong hsz hsel hv hnp hnb hdep hc0 hcB hc10
      (Nat.le_trans (Nat.le_add_right _ _) hg)) ?_
    refine Triple.seq (segAFee (state := (checkState state message)) (substate := (checkSub substate message)) hfork (size_mapMem size_MEM0 _ _)
      hov hcA hc3 hc4 (by omega)) ?_
    refine (allowToW (by simp) hmax hle (by omega) hM0).consequence (fun _ h => h) ?_
    intro e he
    have hx : g - (PRE_COST_F + slotCost c0 + slotCost cB + slotCost c10) -
        (361 + slotCost cA + slotCost c3 + slotCost c4 + mulCost (valArg message) + capCost (rawFee (checkState state message) message (valArg message)) (storageAt (checkState state message) message.currentTarget 4)) - 318 =
        g - (PRE_COST_F + slotCost c0 + slotCost cB + slotCost c10 +
          (679 + slotCost cA + slotCost c3 + slotCost c4 + mulCost (valArg message) + capCost (rawFee (checkState state message) message (valArg message)) (storageAt (checkState state message) message.currentTarget 4))) := by
      omega
    rw [hx] at he
    exact he
  have hcF' : coldIn (storeSub fork (accessF (checkSub substate message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (originalAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message))) (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message))) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message)) = cF := by
    rw [eo0, ec0, ← eS]; exact hcF
  have hMb : (allowMem message (allowMem message (memF message) (fromArg message)) (fromArg message)).size = 96 := size_allowMem hM0 _
  have hmid1 := fun g (hg : 405 + slotCost cF ≤ g) => allowToDebitWFee (state := (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))))
    (substate := (storeSub fork (accessF (checkSub substate message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (originalAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message))) (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message))) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message)))) (b := (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) (fee := (feeOf (checkState state message) message (valArg message))) (A := (allowOf (checkState state message) message (fromArg message))) (v := (valArg message)) (t := toArg message)
    (f := fromArg message) (sel := BitVec.ofNat 256 (selector message.data)) (M := (allowMem message (allowMem message (memF message) (fromArg message)) (fromArg message))) hfork
    hfv (by rw [ec1']; exact hbal) hcF' hg hMb
  have hPb : loadWord (memoryReadBytes (allowMem message (allowMem message (memF message) (fromArg message)) (fromArg message)) 64 32) 0 32 = 0x60 := ptr_allowMem hM0 hP0 _
  have hMbs : (allowMem message (allowMem message (memF message) (fromArg message)) (fromArg message)).size = 96 := size_allowMem hM0 _
  have hMf : (mapMem (mapMem (allowMem message (allowMem message (memF message) (fromArg message)) (fromArg message)) (mkey (fromArg message)) 2) (mkey (fromArg message)) 2).size = 96 := size_mapMem (size_mapMem hMbs _ _) _ _
  have hPf : loadWord (memoryReadBytes (mapMem (mapMem (allowMem message (allowMem message (memF message) (fromArg message)) (fromArg message)) (mkey (fromArg message)) 2) (mkey (fromArg message)) 2) 64 32) 0 32 = 0x60 :=
    ptr_mapMem (size_mapMem hMbs _ _) (ptr_mapMem hMbs hPb _ _) _ _
  have hMt : (mapMem (mapMem (mapMem (mapMem (allowMem message (allowMem message (memF message) (fromArg message)) (fromArg message)) (mkey (fromArg message)) 2) (mkey (fromArg message)) 2) (mkey (toArg message)) 2) (mkey (toArg message)) 2).size = 96 := size_mapMem (size_mapMem hMf _ _) _ _
  have hPt : loadWord (memoryReadBytes (mapMem (mapMem (mapMem (mapMem (allowMem message (allowMem message (memF message) (fromArg message)) (fromArg message)) (mkey (fromArg message)) 2) (mkey (fromArg message)) 2) (mkey (toArg message)) 2) (mkey (toArg message)) 2) 64 32) 0 32 = 0x60 :=
    ptr_mapMem (size_mapMem hMf _ _) (ptr_mapMem hMf hPf _ _) _ _
  have hMo : (mapMem (mapMem (mapMem (mapMem (mapMem (mapMem (allowMem message (allowMem message (memF message) (fromArg message)) (fromArg message)) (mkey (fromArg message)) 2) (mkey (fromArg message)) 2) (mkey (toArg message)) 2) (mkey (toArg message)) 2) (mkey (ownerKey (storageAt (writeSlot (readSlot (writeSlot (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) message.currentTarget (recipientSlot (toArg message)) (add (storageAt (writeSlot (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) (sub (valArg message) (feeOf (checkState state message) message (valArg message))))) message.currentTarget 0))) 2) (mkey (ownerKey (storageAt (writeSlot (readSlot (writeSlot (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) message.currentTarget (recipientSlot (toArg message)) (add (storageAt (writeSlot (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) (sub (valArg message) (feeOf (checkState state message) message (valArg message))))) message.currentTarget 0))) 2).size = 96 := size_mapMem (size_mapMem hMt _ _) _ _
  have hPo : loadWord (memoryReadBytes (mapMem (mapMem (mapMem (mapMem (mapMem (mapMem (allowMem message (allowMem message (memF message) (fromArg message)) (fromArg message)) (mkey (fromArg message)) 2) (mkey (fromArg message)) 2) (mkey (toArg message)) 2) (mkey (toArg message)) 2) (mkey (ownerKey (storageAt (writeSlot (readSlot (writeSlot (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) message.currentTarget (recipientSlot (toArg message)) (add (storageAt (writeSlot (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) (sub (valArg message) (feeOf (checkState state message) message (valArg message))))) message.currentTarget 0))) 2) (mkey (ownerKey (storageAt (writeSlot (readSlot (writeSlot (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) message.currentTarget (recipientSlot (toArg message)) (add (storageAt (writeSlot (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) (sub (valArg message) (feeOf (checkState state message) message (valArg message))))) message.currentTarget 0))) 2) 64 32) 0 32 = 0x60 :=
    ptr_mapMem (size_mapMem hMt _ _) (ptr_mapMem hMt hPt _ _) _ _
  have hcT' : coldIn (storeSub fork (accessSlot (storeSub fork (accessF (checkSub substate message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (originalAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message))) (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message))) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (originalAt (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message))) (storageAt (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message))) (sub (storageAt (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message)) = cT := by
    rw [coldIn_storeSub, eo0, ec0, ← eS]; exact hcT
  have hmid2 := fun g (hg : 308 + slotCost cT ≤ g) => debitToCreditWFee (state := (writeSlot (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) (valArg message))))
    (substate := (storeSub fork (accessSlot (storeSub fork (accessF (checkSub substate message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (originalAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message))) (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message))) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (originalAt (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message))) (storageAt (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message))) (sub (storageAt (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) (valArg message)))) (nb := (sub (storageAt (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) (send := (sub (valArg message) (feeOf (checkState state message) message (valArg message)))) (fee := (feeOf (checkState state message) message (valArg message))) (A := (allowOf (checkState state message) message (fromArg message))) (v := (valArg message))
    (t := toArg message) (f := fromArg message) (sel := BitVec.ofNat 256 (selector message.data))
    (M := (mapMem (mapMem (allowMem message (allowMem message (memF message) (fromArg message)) (fromArg message)) (mkey (fromArg message)) 2) (mkey (fromArg message)) 2)) hfork hMf (by rw [ec2']; exact hto) hcT' hg
  have hc0' : coldIn (storeSub fork (accessSlot (storeSub fork (accessSlot (storeSub fork (accessF (checkSub substate message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (originalAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message))) (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message))) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (originalAt (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message))) (storageAt (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message))) (sub (storageAt (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) message.currentTarget (recipientSlot (toArg message)) (originalAt (readSlot (writeSlot (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) message.currentTarget (recipientSlot (toArg message))) (storageAt (readSlot (writeSlot (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) message.currentTarget (recipientSlot (toArg message))) (add (storageAt (writeSlot (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) (sub (valArg message) (feeOf (checkState state message) message (valArg message))))) message.currentTarget 0 = false := (TransferFee.coldIn_storeSub_false (TransferFrom.coldIn_accessSlot_false (TransferFee.coldIn_storeSub_false (TransferFrom.coldIn_accessSlot_false (TransferFee.coldIn_storeSub_false (TransferFrom.coldIn_accessSlot_false (TransferFrom.coldIn_accessSlot_false (TransferFrom.coldIn_accessSlot_false (TransferFrom.coldIn_accessSlot_false (TransferFrom.coldIn_accessSlot_false (coldIn_accessSlot_self _ _ _)))))))))))
  have hcO' : coldIn (accessSlot (storeSub fork (accessSlot (storeSub fork (accessSlot (storeSub fork (accessF (checkSub substate message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (originalAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message))) (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message))) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (originalAt (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message))) (storageAt (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message))) (sub (storageAt (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) message.currentTarget (recipientSlot (toArg message)) (originalAt (readSlot (writeSlot (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) message.currentTarget (recipientSlot (toArg message))) (storageAt (readSlot (writeSlot (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) message.currentTarget (recipientSlot (toArg message))) (add (storageAt (writeSlot (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) (sub (valArg message) (feeOf (checkState state message) message (valArg message))))) message.currentTarget 0) message.currentTarget (ownerSlot (storageAt (writeSlot (readSlot (writeSlot (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) message.currentTarget (recipientSlot (toArg message)) (add (storageAt (writeSlot (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) (sub (valArg message) (feeOf (checkState state message) message (valArg message))))) message.currentTarget 0)) = cO := by
    rw [TransferFee.coldIn_accessSlot_of_warm hc0', eSS5, eS5]; exact hcO
  have hmid3 := fun g (hg : 605 + slotCost cO ≤ g) => creditToOwnerW (state := (writeSlot (readSlot (writeSlot (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) message.currentTarget (recipientSlot (toArg message)) (add (storageAt (writeSlot (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) (sub (valArg message) (feeOf (checkState state message) message (valArg message))))))
    (substate := (storeSub fork (accessSlot (storeSub fork (accessSlot (storeSub fork (accessF (checkSub substate message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (originalAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message))) (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message))) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (originalAt (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message))) (storageAt (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message))) (sub (storageAt (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) message.currentTarget (recipientSlot (toArg message)) (originalAt (readSlot (writeSlot (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) message.currentTarget (recipientSlot (toArg message))) (storageAt (readSlot (writeSlot (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) message.currentTarget (recipientSlot (toArg message))) (add (storageAt (writeSlot (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) (sub (valArg message) (feeOf (checkState state message) message (valArg message)))))) (nt := (add (storageAt (writeSlot (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) (sub (valArg message) (feeOf (checkState state message) message (valArg message))))) (send := (sub (valArg message) (feeOf (checkState state message) message (valArg message)))) (fee := (feeOf (checkState state message) message (valArg message))) (A := (allowOf (checkState state message) message (fromArg message))) (v := (valArg message))
    (t := toArg message) (f := fromArg message) (sel := BitVec.ofNat 256 (selector message.data))
    (M := (mapMem (mapMem (mapMem (mapMem (allowMem message (allowMem message (memF message) (fromArg message)) (fromArg message)) (mkey (fromArg message)) 2) (mkey (fromArg message)) 2) (mkey (toArg message)) 2) (mkey (toArg message)) 2)) hfork hfee hMt hc0' hcO' (by rw [ec3']; exact hown) hg
  have hpost := fun g (hg : 3839 ≤ g) => ownerPostF (state := (writeSlot (readSlot (readSlot (readSlot (writeSlot (readSlot (writeSlot (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) message.currentTarget (recipientSlot (toArg message)) (add (storageAt (writeSlot (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) (sub (valArg message) (feeOf (checkState state message) message (valArg message))))) message.currentTarget 0) message.currentTarget (ownerSlot (storageAt (writeSlot (readSlot (writeSlot (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) message.currentTarget (recipientSlot (toArg message)) (add (storageAt (writeSlot (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) (sub (valArg message) (feeOf (checkState state message) message (valArg message))))) message.currentTarget 0))) message.currentTarget 0) message.currentTarget (ownerSlot (storageAt (writeSlot (readSlot (writeSlot (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) message.currentTarget (recipientSlot (toArg message)) (add (storageAt (writeSlot (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) (sub (valArg message) (feeOf (checkState state message) message (valArg message))))) message.currentTarget 0)) (add (storageAt (writeSlot (readSlot (writeSlot (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) message.currentTarget (recipientSlot (toArg message)) (add (storageAt (writeSlot (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) (sub (valArg message) (feeOf (checkState state message) message (valArg message))))) message.currentTarget (ownerSlot (storageAt (writeSlot (readSlot (writeSlot (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) message.currentTarget (recipientSlot (toArg message)) (add (storageAt (writeSlot (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) (sub (valArg message) (feeOf (checkState state message) message (valArg message))))) message.currentTarget 0))) (feeOf (checkState state message) message (valArg message))))) (substate := (storeSub fork (accessSlot (accessSlot (accessSlot (storeSub fork (accessSlot (storeSub fork (accessSlot (storeSub fork (accessF (checkSub substate message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (originalAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message))) (storageAt (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message))) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (originalAt (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message))) (storageAt (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message))) (sub (storageAt (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) message.currentTarget (recipientSlot (toArg message)) (originalAt (readSlot (writeSlot (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) message.currentTarget (recipientSlot (toArg message))) (storageAt (readSlot (writeSlot (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) message.currentTarget (recipientSlot (toArg message))) (add (storageAt (writeSlot (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) (sub (valArg message) (feeOf (checkState state message) message (valArg message))))) message.currentTarget 0) message.currentTarget (ownerSlot (storageAt (writeSlot (readSlot (writeSlot (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) message.currentTarget (recipientSlot (toArg message)) (add (storageAt (writeSlot (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) (sub (valArg message) (feeOf (checkState state message) message (valArg message))))) message.currentTarget 0))) message.currentTarget 0) message.currentTarget (ownerSlot (storageAt (writeSlot (readSlot (writeSlot (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) message.currentTarget (recipientSlot (toArg message)) (add (storageAt (writeSlot (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) (sub (valArg message) (feeOf (checkState state message) message (valArg message))))) message.currentTarget 0)) (originalAt (readSlot (readSlot (readSlot (writeSlot (readSlot (writeSlot (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) message.currentTarget (recipientSlot (toArg message)) (add (storageAt (writeSlot (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) (sub (valArg message) (feeOf (checkState state message) message (valArg message))))) message.currentTarget 0) message.currentTarget (ownerSlot (storageAt (writeSlot (readSlot (writeSlot (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) message.currentTarget (recipientSlot (toArg message)) (add (storageAt (writeSlot (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) (sub (valArg message) (feeOf (checkState state message) message (valArg message))))) message.currentTarget 0))) message.currentTarget 0) message.currentTarget (ownerSlot (storageAt (writeSlot (readSlot (writeSlot (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) message.currentTarget (recipientSlot (toArg message)) (add (storageAt (writeSlot (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) (sub (valArg message) (feeOf (checkState state message) message (valArg message))))) message.currentTarget 0))) (storageAt (readSlot (readSlot (readSlot (writeSlot (readSlot (writeSlot (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) message.currentTarget (recipientSlot (toArg message)) (add (storageAt (writeSlot (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) (sub (valArg message) (feeOf (checkState state message) message (valArg message))))) message.currentTarget 0) message.currentTarget (ownerSlot (storageAt (writeSlot (readSlot (writeSlot (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) message.currentTarget (recipientSlot (toArg message)) (add (storageAt (writeSlot (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) (sub (valArg message) (feeOf (checkState state message) message (valArg message))))) message.currentTarget 0))) message.currentTarget 0) message.currentTarget (ownerSlot (storageAt (writeSlot (readSlot (writeSlot (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) message.currentTarget (recipientSlot (toArg message)) (add (storageAt (writeSlot (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) (sub (valArg message) (feeOf (checkState state message) message (valArg message))))) message.currentTarget 0))) (add (storageAt (writeSlot (readSlot (writeSlot (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) message.currentTarget (recipientSlot (toArg message)) (add (storageAt (writeSlot (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) (sub (valArg message) (feeOf (checkState state message) message (valArg message))))) message.currentTarget (ownerSlot (storageAt (writeSlot (readSlot (writeSlot (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) message.currentTarget (recipientSlot (toArg message)) (add (storageAt (writeSlot (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) (sub (valArg message) (feeOf (checkState state message) message (valArg message))))) message.currentTarget 0))) (feeOf (checkState state message) message (valArg message)))))
    (no := (add (storageAt (writeSlot (readSlot (writeSlot (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) message.currentTarget (recipientSlot (toArg message)) (add (storageAt (writeSlot (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) (sub (valArg message) (feeOf (checkState state message) message (valArg message))))) message.currentTarget (ownerSlot (storageAt (writeSlot (readSlot (writeSlot (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) message.currentTarget (recipientSlot (toArg message)) (add (storageAt (writeSlot (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) (sub (valArg message) (feeOf (checkState state message) message (valArg message))))) message.currentTarget 0))) (feeOf (checkState state message) message (valArg message)))) (send := (sub (valArg message) (feeOf (checkState state message) message (valArg message)))) (fee := (feeOf (checkState state message) message (valArg message))) (A := (allowOf (checkState state message) message (fromArg message))) (v := (valArg message))
    (t := toArg message) (f := fromArg message) (sel := BitVec.ofNat 256 (selector message.data))
    (M := (mapMem (mapMem (mapMem (mapMem (mapMem (mapMem (allowMem message (allowMem message (memF message) (fromArg message)) (fromArg message)) (mkey (fromArg message)) 2) (mkey (fromArg message)) 2) (mkey (toArg message)) 2) (mkey (toArg message)) 2) (mkey (ownerKey (storageAt (writeSlot (readSlot (writeSlot (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) message.currentTarget (recipientSlot (toArg message)) (add (storageAt (writeSlot (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) (sub (valArg message) (feeOf (checkState state message) message (valArg message))))) message.currentTarget 0))) 2) (mkey (ownerKey (storageAt (writeSlot (readSlot (writeSlot (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) message.currentTarget (recipientSlot (toArg message)) (add (storageAt (writeSlot (readSlot (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) message.currentTarget (recipientSlot (fromArg message)) (sub (storageAt (writeSlot (readsF (checkState state message) message (fromArg message)) message.currentTarget (allowFrom message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message))) message.currentTarget (recipientSlot (fromArg message))) (valArg message))) message.currentTarget (recipientSlot (toArg message))) (sub (valArg message) (feeOf (checkState state message) message (valArg message))))) message.currentTarget 0))) 2)) hfork hstatic hMo hPo (TransferFee.coldIn_storeSub_false (coldIn_accessSlot_self _ _ _)) hg
  have hx := Complete.exactS_write hfork hpre hP
    (fun _ _ => by simp only [Complete.getStorage_readSlot]) (by code_fact) (by code_fact)
    hstatic hacc3 (TransferFrom.coldIn_accessSlot_false (TransferFrom.coldIn_accessSlot_false (coldIn_accessSlot_self _ _ _)))
    (Complete.exactS_write hfork hmid1 hQ1 (fun _ _ => by simp only [Complete.getStorage_readSlot])
      (by code_fact) (by code_fact) hstatic hacc4 (coldIn_accessSlot_self _ _ _)
      (Complete.exactS_write hfork hmid2 hQ2 (fun _ _ => by simp only [Complete.getStorage_readSlot])
        (by code_fact) (by code_fact) hstatic hacc6 (coldIn_accessSlot_self _ _ _)
        (Complete.exactS_write hfork hmid3 hQ3 (fun _ _ => by simp only [Complete.getStorage_readSlot])
          (by code_fact) (by code_fact) hstatic hacc8 (TransferFrom.coldIn_accessSlot_false (coldIn_accessSlot_self _ _ _))
          (Complete.exactS_halt hpost (by decide) (fun _ _ => by simp only [Complete.getStorage_readSlot])))))
  obtain ⟨hgas, hiff, hend⟩ := hx.run start (runChild := runChild) within
  rw [eo3, ec3, ec3', eo2, ec2, ec2', eo1, ec1, ec1', eo0, ec0] at hiff
  refine ⟨hiff, fun s hrun hok => ?_⟩
  have hok' := hiff.mp ⟨s, hrun, hok⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := hend s hrun hok
  rw [eo3, ec3, ec3', eo2, ec2, ec2', eo1, ec1, ec1', eo0, ec0] at h5
  refine ⟨h1, h2, ?_, ?_, ?_, ?_⟩
  · rw [h3, eS5]
  · rw [h4, eo3, ec3, ec3', eSS5, eS5]
  · obtain ⟨o0, o1, o2, o3, o4⟩ := hok'
    have e0 := Complete.wMeter_gasLeft o0
    have e1 := Complete.wMeter_gasLeft o1
    have e2 := Complete.wMeter_gasLeft o2
    have e3 := Complete.wMeter_gasLeft o3
    have e4 : s.gas.gasLeft = _ := congrArg StateGasMeter.gasLeft h5
    have hac : allowCostF fork (checkState state message) message (valArg message) (fromArg message) =
        320 + Gas.writeCost fork (originalAt (checkState state message) message.currentTarget (allowFrom message (fromArg message))) (allowOf (checkState state message) message (fromArg message)) (sub (allowOf (checkState state message) message (fromArg message)) (valArg message)) false := by
      simp only [allowCostF, allowCost, if_neg hmax]
    simp only [feeCostF, hac, debitCostF, creditCostFeeF, ownerCostF, faP0, gaM0, gaM1, gaM2, gaM3, sendOf,
      wBump] at e0 e1 e2 e3 e4 o4 ⊢
    omega
  · rw [h5]

end Fee

end UsdtVerify.TransferFrom
