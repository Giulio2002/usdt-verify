import EthLib.Execution.Proofs.Evm.Call.StaticMessage
import EthLib.Execution.Proofs.Evm.MemorySize

/-!
# LOCAL: every message keeps the block of the state

GENERIC GAP. Nothing here is specific to USDT; each lemma holds for every code.

EthLib proves that a message keeps the block of its state (`parent`) only for static messages
(`processMessage_static`). This file proves it for every message from any fork: every step of
any frame, static or not, every run of a frame under a runner that keeps the block, and
`processMessage` and `processCreateMessage` themselves, by induction on the gas of the message.

So EthLib's `getStorage_restoreTxState` applies to the rollback of every failed message:
`processMessage_failed_getStorage` gives that a message that ends with an error leaves every
storage word of every address as it was before the message.
-/

namespace UsdtVerify.Local

open EthLib
open EthLib.Base (Address Bytes32 Fork U256 toAddressMasked)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.State (TransactionState)

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-! ## The writes of the state -/

theorem parent_incrementNonce {tx tx' : TransactionState} {address : Address}
    (h : tx.incrementNonce fork address = .ok tx') : tx'.parent = tx.parent :=
  parent_modifyState h

theorem parent_setAccountBalance {tx tx' : TransactionState} {address : Address} {amount : U256}
    (h : tx.setAccountBalance fork address amount = .ok tx') : tx'.parent = tx.parent :=
  parent_modifyState h

theorem parent_createEther {tx tx' : TransactionState} {address : Address} {amount : U256}
    (h : tx.createEther fork address amount = .ok tx') : tx'.parent = tx.parent :=
  parent_modifyState h

theorem parent_setCode {tx tx' : TransactionState} {address : Address} {code : ByteArray}
    (h : tx.setCode fork address code = .ok tx') : tx'.parent = tx.parent := by
  unfold TransactionState.setCode at h
  rw [parent_modifyState h]
  split <;> rfl

theorem parent_selfdestructTransfer {tx tx' : TransactionState} {originator beneficiary : Address}
    (h : selfdestructTransfer fork tx originator beneficiary = .ok tx') :
    tx'.parent = tx.parent := by
  unfold selfdestructTransfer at h
  split at h
  · obtain ⟨mid, h1, h⟩ := Base.bind_ok_iff.mp h
    split at h
    · exact (parent_setAccountBalance h).trans (parent_moveEther h1)
    · cases h
      exact parent_moveEther h1
  · obtain ⟨mid, h1, h⟩ := Base.bind_ok_iff.mp h
    exact (parent_setAccountBalance h).trans (parent_createEther h1)

theorem parent_prepareCreation {tx tx' : TransactionState} {address : Address}
    (h : prepareCreation fork tx address = .ok tx') : tx'.parent = tx.parent := by
  unfold prepareCreation at h
  split at h
  · exact (parent_incrementNonce (Base.mapError_ok_iff.mp h) :)
  · cases h
    rfl

/-! ## The instructions that give the next frame -/

omit [GasMeter Meter] in
theorem parent_of_sameContext {a b : Evm fork Meter} (h : SameContext a b) :
    b.state.parent = a.state.parent := by
  rw [h.state]

/-- SSTORE keeps the block, static frame or not. -/
theorem parent_sstoreStep {evm after : Evm fork Meter} (h : sstoreStep evm = .ok after) :
    after.state.parent = evm.state.parent := by
  unfold sstoreStep at h
  split at h
  · simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  obtain ⟨⟨k, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨n, e2⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  have c2 : e2.state.parent = evm.state.parent := by
    rw [(popWord_sameContext h2).state, (popWord_sameContext h1).state]
  simp only [] at h
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h
  · rcases hpair : accessStorageKey e2 e2.message.currentTarget (U256.toBeBytes k) with
      ⟨cold, e3⟩
    have ha : e3.state.parent = e2.state.parent := by
      have := (staticStep_accessStorageKey e2 e2.message.currentTarget (U256.toBeBytes k)).parent
      rwa [hpair] at this
    simp only [hpair] at h
    rcases keepReads_eq_ok h with h | ⟨e, rfl⟩
    · obtain ⟨e4, h4, h⟩ := Base.bind_ok_iff.mp h
      obtain ⟨e5, h5, h⟩ := Base.bind_ok_iff.mp h
      have m5 : e5.state.parent = evm.state.parent := by
        rw [(chargeStateGas_sameContext h5).state, (chargeGas_sameContext h4).state]
        exact ha.trans c2
      split at h
      · simp [throw, throwThe, MonadExceptOf.throw] at h
      · obtain ⟨st, hst, h⟩ := Base.bind_ok_iff.mp h
        cases h
        exact (TransactionState.parent_setStorage (Base.mapError_ok_iff.mp hst)).trans m5
    · exact ha.trans c2

/-- TSTORE keeps the block. -/
theorem parent_tstoreStep {evm after : Evm fork Meter} (h : tstoreStep evm = .ok after) :
    after.state.parent = evm.state.parent := by
  obtain ⟨⟨_, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e2⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨e3, h3, h⟩ := Base.bind_ok_iff.mp h
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h
  · cases h
    show e3.state.parent = _
    rw [(chargeGas_sameContext h3).state, (popWord_sameContext h2).state,
      (popWord_sameContext h1).state]

/-- SELFDESTRUCT keeps the block, static frame or not. -/
theorem parent_selfdestructStep {evm after : Evm fork Meter}
    (h : selfdestructStep fork evm = .ok after) : after.state.parent = evm.state.parent := by
  unfold selfdestructStep at h
  by_cases hs : fork ≥ .glamsterdam ∧ evm.message.isStatic = true
  · simp only [hs, and_self, ↓reduceIte] at h
    cases h
  simp only [hs, ↓reduceIte] at h
  obtain ⟨⟨w, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  dsimp only at h
  rcases hacc : accessAddress e1 (toAddressMasked w) with ⟨cold, e2⟩
  simp only [hacc] at h
  have ha : e2.state.parent = e1.state.parent := by
    have := (staticStep_accessAddress e1 (toAddressMasked w)).parent
    rwa [hacc] at this
  obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
  have c : (recordAccountRead e2 (toAddressMasked w)).state.parent = evm.state.parent := by
    show e2.state.parent = _
    rw [ha, (popWord_sameContext h1).state]
  rcases keepReads_eq_ok h with h | ⟨e, rfl⟩
  · obtain ⟨e3, h3, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨e4, h4, h⟩ := Base.bind_ok_iff.mp h
    have m4 : e4.state.parent = evm.state.parent := by
      rw [(chargeStateGas_sameContext h4).state, (chargeGas_sameContext h3).state]
      exact c
    unfold finishSelfdestruct at h
    split at h
    · cases h
    · obtain ⟨st, hst, h⟩ := Base.bind_ok_iff.mp h
      cases h
      exact (parent_selfdestructTransfer (Base.mapError_ok_iff.mp hst)).trans m4
  · exact c

/-- Each instruction that gives the next frame keeps the block, static frame or not. -/
theorem parent_instruction {op : Op}
    {run : Evm fork Meter → Except EvmError (Evm fork Meter)} {evm after : Evm fork Meter}
    (hrun : instruction fork op = some run) (h : run evm = .ok after) :
    after.state.parent = evm.state.parent := by
  unfold instruction at hrun
  rcases orElse_eq_some hrun with hf | hrun
  · exact parent_of_sameContext (stackOnlyStep_sameContext hf h)
  rcases orElse_eq_some hrun with hf | hrun
  · exact parent_of_sameContext (controlFlowStep_sameContext hf h)
  rcases orElse_eq_some hrun with hf | hrun
  · exact parent_of_sameContext (memoryDataStep_sameContext hf h)
  rcases orElse_eq_some hrun with hf | hrun
  · exact (staticStep_returnOpStep hf h).parent
  rcases orElse_eq_some hrun with hf | hrun
  · exact parent_of_sameContext (environmentStep_sameContext hf h)
  rcases orElse_eq_some hrun with hf | hrun
  · exact (staticStep_accountStep hf h).parent
  rcases orElse_eq_some hrun with hf | hrun
  · cases op <;> simp only [storageStep, Option.some.injEq, reduceCtorEq] at hf
    case sload => subst hf; exact (staticStep_sloadStep h).parent
    case sstore => subst hf; exact parent_sstoreStep h
  rcases orElse_eq_some hrun with hf | hrun
  · cases op <;> simp only [transientStorageStep, reduceCtorEq] at hf <;> split at hf <;>
      simp only [Option.some.injEq, reduceCtorEq] at hf <;> subst hf
    · exact parent_of_sameContext (tloadStep_sameContext h)
    · exact parent_tstoreStep h
  rcases orElse_eq_some hrun with hf | hf
  · cases op <;> simp only [logOpStep, Option.some.injEq, reduceCtorEq] at hf
    subst hf
    obtain ⟨_, -, -, -, hs, -⟩ := logStep_eq_ok h
    rw [hs]
  · cases op <;> simp only [selfdestructOpStep, Option.some.injEq, reduceCtorEq] at hf
    subst hf
    exact parent_selfdestructStep h

/-! ## The calls and the creations -/

/-- What a step gives, for the block: the next frame keeps it; a child is sent from a frame that
keeps it, and the frame that resumes keeps it when the child ended with the caller's block. -/
def PResult (evm : Evm fork Meter) : StepResult fork Meter → Prop
  | .next after => after.state.parent = evm.state.parent
  | .child caller _ resume => caller.state.parent = evm.state.parent ∧
      ∀ child after, resume child = .ok after → child.state.parent = caller.state.parent →
        after.state.parent = evm.state.parent

omit [GasMeter Meter] in
theorem PResult.lift {evm evm' : Evm fork Meter} {result : StepResult fork Meter}
    (h : evm'.state.parent = evm.state.parent) (r : PResult evm' result) :
    PResult evm result := by
  cases result with
  | next after => exact (r : _ = _).trans h
  | child caller message resume =>
    obtain ⟨c, m⟩ := r
    exact ⟨c.trans h, fun child after hres p => (m child after hres p).trans h⟩

/-- The caller that resumes after a call has the state of the child. -/
theorem state_resumeCall {caller child after : Evm fork Meter} {newAccount : Nat}
    {outputStart outputSize : U256}
    (h : resumeCall fork caller newAccount outputStart outputSize child = .ok after) :
    after.state = child.state := by
  obtain ⟨e, h1, h⟩ := Base.bind_ok_iff.mp h
  cases h
  have hp := pushWord_sameContext h1
  show e.state = child.state
  rw [hp.state]
  split <;> simp [state_incorporateChild, refillStateGas]

/-- The creator that resumes after a creation has the state of the child. -/
theorem state_resumeCreate {caller child after : Evm fork Meter} {newAccount : Nat}
    {address : Address} (h : resumeCreate fork caller newAccount address child = .ok after) :
    after.state = child.state := by
  obtain ⟨e, h1, h⟩ := Base.bind_ok_iff.mp h
  cases h
  have hp := pushWord_sameContext h1
  show e.state = child.state
  rw [hp.state]
  split <;> simp [state_incorporateChild, refillStateGas]

theorem pResult_genericCall {evm : Evm fork Meter} {message : Message fork}
    {newAccount : Nat} {outputStart outputSize : U256} {result : StepResult fork Meter}
    (h : genericCall evm message newAccount outputStart outputSize = .ok result) :
    PResult evm result := by
  unfold genericCall at h
  dsimp only at h
  split at h
  · obtain ⟨after, hs, rfl⟩ := Base.map_ok_iff.mp h
    exact (staticStep_skipCall hs).parent
  · cases h
    exact ⟨rfl, fun child after hres p => (congrArg TransactionState.parent
      (state_resumeCall hres)).trans p⟩

theorem pResult_finishCall {kind : CallKind} {call : CallOperands} {callee : Callee}
    {subCall newAccount expandBy : Nat} {evm : Evm fork Meter} {result : StepResult fork Meter}
    (h : finishCall kind call callee subCall newAccount expandBy evm = .ok result) :
    PResult evm result := by
  unfold finishCall at h
  split at h
  · cases h
  dsimp only at h
  split at h
  · obtain ⟨after, hs, rfl⟩ := Base.map_ok_iff.mp h
    exact (staticStep_skipCall hs).parent
  · refine PResult.lift ?_ (pResult_genericCall h)
    rfl

theorem pResult_callStep {kind : CallKind} {evm : Evm fork Meter}
    {result : StepResult fork Meter} (h : callStep kind evm = .ok result) :
    PResult evm result := by
  unfold callStep at h
  obtain ⟨⟨call, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  have c1 := (staticStep_popCallOperands h1).1
  dsimp only at h
  split at h
  · simp only [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
    cases h
  rcases hacc : accessAddress e1 call.address with ⟨cold, e2⟩
  simp only [hacc] at h
  have ha : StaticStep e1 e2 := by
    have := staticStep_accessAddress e1 call.address
    rwa [hacc] at this
  have s3 : StaticStep evm (recordAccountRead e2 call.address) :=
    (c1.trans ha).trans (staticStep_recordAccountRead e2 call.address)
  obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
  rcases keepReads_eq_ok h with h | ⟨e, rfl⟩
  · obtain ⟨⟨callee, e4⟩, h4, h⟩ := Base.bind_ok_iff.mp h
    have s4 : StaticStep evm e4 := s3.trans (staticStep_accessDelegation h4)
    dsimp only at h
    rcases keepReads_eq_ok h with h | ⟨e, rfl⟩
    · obtain ⟨⟨subCall, e5⟩, h5, h⟩ := Base.bind_ok_iff.mp h
      have s5 : StaticStep evm e5 := s4.trans (staticStep_payCall h5)
      exact PResult.lift s5.parent (pResult_finishCall h)
    · exact (s4.trans (staticStep_exceptionalHalt _ _)).parent
  · exact (s3.trans (staticStep_exceptionalHalt _ _)).parent

theorem pResult_launchCreate {evm : Evm fork Meter} {value : U256} {initCode : ByteArray}
    {salt : Option U256} {result : StepResult fork Meter}
    (h : launchCreate evm value initCode salt = .ok result) : PResult evm result := by
  unfold launchCreate at h
  dsimp only at h
  split at h
  · obtain ⟨after, hs, rfl⟩ := Base.map_ok_iff.mp h
    exact (staticStep_skipCall hs).parent
  obtain ⟨address, -, h⟩ := Base.bind_ok_iff.mp h
  have c0 : (recordAccountRead (accessAddress (recordAccountRead
      { evm with returnData := .empty } evm.message.currentTarget) address).2
      address).state.parent = evm.state.parent :=
    ((staticStep_accessAddress _ _).trans (staticStep_recordAccountRead _ _)).parent
  rcases keepReads_eq_ok h with hr | ⟨e, rfl⟩
  · obtain ⟨e1, h1, hr⟩ := Base.bind_ok_iff.mp hr
    obtain ⟨e2, h2, hr⟩ := Base.bind_ok_iff.mp hr
    obtain ⟨state, hst, hr⟩ := Base.bind_ok_iff.mp hr
    have m2 : e2.state.parent = evm.state.parent := by
      rw [(chargeGas_sameContext h2).state, (chargeStateGas_sameContext h1).state]
      exact c0
    have ms : state.parent = evm.state.parent :=
      (parent_incrementNonce (Base.mapError_ok_iff.mp hst)).trans m2
    split at hr
    · cases hr
      exact ⟨ms, fun child after hres p => (congrArg TransactionState.parent
        (state_resumeCreate hres)).trans (p.trans ms)⟩
    · obtain ⟨e3, h3, hr⟩ := Base.bind_ok_iff.mp hr
      cases hr
      show e3.state.parent = _
      rw [(pushWord_sameContext h3).state]
      exact ms
  · exact c0

theorem pResult_createStep {create2 : Bool} {evm : Evm fork Meter}
    {result : StepResult fork Meter} (h : createStep create2 evm = .ok result) :
    PResult evm result := by
  unfold createStep at h
  by_cases hs : fork ≥ .glamsterdam ∧ evm.message.isStatic = true
  · simp [hs, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  rw [ite_eq_right_of_eq_false _ _ (eq_false hs)] at h
  obtain ⟨⟨_, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e2⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e3⟩, h3, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨salt, e4⟩, h4, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨e5, h5, h⟩ := Base.bind_ok_iff.mp h
  have m4 : e4.state = e3.state := by
    unfold popSalt at h4
    split at h4
    · obtain ⟨⟨_, e⟩, he, h4⟩ := Base.bind_ok_iff.mp h4
      cases h4
      exact (popWord_sameContext he).state
    · cases h4
      rfl
  have m5 : e5.state.parent = evm.state.parent := by
    rw [(chargeGasAndMemory_sameContext h5).state, m4, (popWord_sameContext h3).state,
      (popWord_sameContext h2).state, (popWord_sameContext h1).state]
  unfold genericCreate at h
  split at h
  · cases h
  split at h
  · cases h
  exact PResult.lift m5 (pResult_launchCreate h)

theorem pResult_messageInstruction {op : Op}
    {run : Evm fork Meter → Except EvmError (StepResult fork Meter)} {evm : Evm fork Meter}
    {result : StepResult fork Meter} (hrun : messageInstruction fork op = some run)
    (h : run evm = .ok result) : PResult evm result := by
  unfold messageInstruction at hrun
  cases hc : callInstruction (Meter := Meter) fork op with
  | some call =>
    simp only [hc, HOrElse.hOrElse, OrElse.orElse, Option.orElse, Option.some.injEq] at hrun
    subst hrun
    cases op <;> simp only [callInstruction, Option.some.injEq, reduceCtorEq] at hc
    all_goals first
      | (subst hc; exact pResult_callStep h)
      | (split at hc
         · simp only [Option.some.injEq] at hc
           subst hc
           exact pResult_callStep h
         · cases hc)
  | none =>
    simp only [hc, HOrElse.hOrElse, OrElse.orElse, Option.orElse] at hrun
    cases op <;> simp only [createInstruction, Option.some.injEq, reduceCtorEq] at hrun
    all_goals first
      | (subst hrun; exact pResult_createStep h)
      | (split at hrun
         · simp only [Option.some.injEq] at hrun
           subst hrun
           exact pResult_createStep h
         · cases hrun)

/-- Every step of every frame, static or not, keeps the block (`PResult`). -/
theorem pResult_step {evm : Evm fork Meter} {result : StepResult fork Meter}
    (h : step fork evm = .ok result) : PResult evm result := by
  unfold step at h
  split at h
  · dsimp only at h
    split at h
    · cases h
    · split at h
      · rename_i hop
        cases hr : ‹Evm fork Meter → Except EvmError (Evm fork Meter)› evm with
        | error => simp [hr, Functor.map, Except.map] at h
        | ok after =>
          simp only [hr, Functor.map, Except.map, Except.ok.injEq] at h
          subst h
          exact parent_instruction hop hr
      · split at h
        · rename_i hcall
          exact pResult_messageInstruction hcall h
        · cases h
  · simp only [stopStep, Functor.map, Except.map, Except.ok.injEq] at h
    subst h
    exact parent_of_sameContext (controlFlowStep_sameContext (op := .stop) rfl rfl)

/-! ## A run of a frame -/

/-- A run of a frame keeps the block, when its runner ends every message with the block of the
frame that sent it. -/
theorem parent_runFrame [LawfulGasMeter Meter] {bound : Nat} {runChild : MessageRunner fork Meter bound}
    (runs : ∀ {caller : Evm fork Meter} {message : Message fork} {lt : message.gas < bound}
      {c : Evm fork Meter} {used : GasMeter.gasHeld c.gas ≤ message.gas},
      runChild caller message lt = .ok ⟨c, used⟩ → c.state.parent = caller.state.parent)
    {evm after : Evm fork Meter} {within : GasMeter.gasHeld evm.gas ≤ bound}
    (h : runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok after) :
    after.state.parent = evm.state.parent := by
  fun_induction runFrame (step fork) (step_decreases fork) bound runChild evm within
  case case1 => cases h
  case case2 => cases h; rfl
  case case3 =>
    rename_i result _ ih
    exact (ih h).trans (pResult_step result)
  case case4 => cases h
  case case5 => cases h
  case case6 => cases h; rfl
  case case7 =>
    obtain ⟨c0, hres⟩ := pResult_step ‹step fork _ = .ok (.child _ _ _)›
    have p := runs ‹runChild _ _ _ = .ok _›
    have n := hres _ _ (by assumption) p
    rename_i ih
    exact (ih h).trans n
  case case8 => cases h; rfl

/-! ## Messages -/

/-- The deposit of the code keeps the block of the frame that ends the init code. -/
theorem parent_depositCode {snapshot : TransactionState} {evm after : Evm fork Meter}
    (h : depositCode fork snapshot evm = .ok after) :
    after.state.parent = evm.state.parent := by
  unfold depositCode at h
  dsimp only at h
  split at h
  · cases h
    rfl
  split at h
  · cases h
    rfl
  split at h
  · cases h
    rfl
  split at h
  · cases h
    split <;> rfl
  split at h
  · cases h
    rfl
  obtain ⟨st, hst, h⟩ := Base.bind_ok_iff.mp h
  cases h
  exact parent_setCode (Base.mapError_ok_iff.mp hst)

/-- The state that a message starts its frame from has the block of the state it is sent from. -/
theorem parent_startState (message : Message fork) (state : TransactionState) :
    (startState fork message state).parent = state.parent := by
  unfold startState
  split
  · exact TransactionState.parent_touchAccount _ _
  · rfl

/-- The rollback of a failed frame keeps the block of that frame. -/
theorem parent_rollbackOnError (snapshot : TransactionState) (evm : Evm fork Meter) :
    (rollbackOnError snapshot evm).state.parent = evm.state.parent := by
  unfold rollbackOnError
  split <;> rfl

/-- Every message and every creation keeps the block of the state, from any fork: by induction on
the gas of the message. -/
theorem parent_process [LawfulGasMeter Meter] (n : Nat) :
    (∀ (message : Message fork) (state : TransactionState) (substate : Substate) (meter : Meter)
      (held : GasMeter.gasHeld meter ≤ message.gas), message.gas = n →
      ∀ ended, processMessage fork message state substate meter held = .ok ended →
        ∃ last : Evm fork Meter, ended.val = rollbackOnError state last ∧
          last.state.parent = state.parent) ∧
    (∀ (message : Message fork) (state : TransactionState) (substate : Substate) (meter : Meter)
      (held : GasMeter.gasHeld meter ≤ message.gas), message.gas = n →
      ∀ ended, processCreateMessage fork message state substate meter held = .ok ended →
        ended.val.state.parent = state.parent) := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    have pm : ∀ (message : Message fork) (state : TransactionState) (substate : Substate)
        (meter : Meter) (held : GasMeter.gasHeld meter ≤ message.gas), message.gas = n →
        ∀ ended, processMessage fork message state substate meter held = .ok ended →
          ∃ last : Evm fork Meter, ended.val = rollbackOnError state last ∧
            last.state.parent = state.parent := by
      intro message state substate meter held hn ended h
      rw [processMessage] at h
      obtain ⟨ended0, hdo, rolled⟩ := Base.map_ok_iff.mp h
      have hst := parent_startState message state
      have core : ended0.val.state.parent = state.parent := by
        dsimp only at hdo
        split at hdo
        all_goals obtain ⟨state1, hm, hdo⟩ := Base.bind_ok_iff.mp hdo
        all_goals
          have hp1 : state1.parent = state.parent := by
            first
            | exact (parent_moveEther (Base.mapError_ok_iff.mp hm)).trans hst
            | (cases hm; exact hst)
          rcases hpa : precompileAddress fork message with _ | addr
          · simp only [hpa] at hdo
            split at hdo
            · cases hdo
            · rename_i after hrun
              cases hdo
              refine (parent_runFrame ?_ hrun).trans hp1
              intro caller' message' lt c used hrun'
              split at hrun'
              · obtain ⟨last, hl, hp⟩ :=
                  (ih message'.gas (by omega)).1 message' caller'.state _ _ _ rfl ⟨c, used⟩ hrun'
                have hl' : c = rollbackOnError caller'.state last := hl
                rw [hl', parent_rollbackOnError]
                exact hp
              · exact (ih message'.gas (by omega)).2 message' caller'.state _ _ _ rfl ⟨c, used⟩
                  hrun'
          · simp only [hpa] at hdo
            split at hdo
            · cases hdo
              exact hp1
            · split at hdo
              · rename_i after hrp
                cases hdo
                exact (staticStep_runPrecompile hrp).parent.trans hp1
              · cases hdo
                exact hp1
      have hval := congrArg Subtype.val rolled
      simp only at hval
      exact ⟨ended0.val, hval.symm, core⟩
    refine ⟨pm, ?_⟩
    intro message state substate meter held hn ended h
    rw [processCreateMessage] at h
    obtain ⟨prepared, hp, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨⟨evm, used⟩, hrun, h⟩ := Base.bind_ok_iff.mp h
    dsimp only at h
    split at h
    · cases h
    · cases h
      exact (parent_depositCode ‹depositCode _ _ _ = .ok _›).trans
        (by
          obtain ⟨last, hl, hp'⟩ := pm message prepared substate meter held hn _ hrun
          have hl' : evm = rollbackOnError prepared last := hl
          rw [hl', parent_rollbackOnError]
          exact hp'.trans (parent_prepareCreation hp))

/-- Every message keeps the block of the state, from any fork. -/
theorem parent_processMessage [LawfulGasMeter Meter] {message : Message fork}
    {state : TransactionState} {substate : Substate} {meter : Meter}
    {held : GasMeter.gasHeld meter ≤ message.gas} {ended}
    (h : processMessage fork message state substate meter held = .ok ended) :
    ended.val.state.parent = state.parent := by
  obtain ⟨last, hl, hp⟩ := (parent_process message.gas).1 message state substate meter held rfl ended h
  rw [hl, parent_rollbackOnError]
  exact hp

/-- A message that ends with an error leaves every storage word of every address as it was in
the state it was sent from: the rollback restores that state, and the run kept its block, so
EthLib's `getStorage_restoreTxState` applies. From any fork, whatever the code of the message. -/
theorem processMessage_failed_getStorage [LawfulGasMeter Meter] {message : Message fork}
    {state : TransactionState} {substate : Substate} {meter : Meter}
    {held : GasMeter.gasHeld meter ≤ message.gas} {ended}
    (h : processMessage fork message state substate meter held = .ok ended)
    (herr : ended.val.error ≠ none) (address : Address) (key : Bytes32) :
    ended.val.state.getStorage address key = state.getStorage address key := by
  obtain ⟨last, hl, hp⟩ := (parent_process message.gas).1 message state substate meter held rfl ended h
  rw [hl] at herr ⊢
  unfold rollbackOnError at herr ⊢
  split
  · exact TransactionState.getStorage_restoreTxState hp address key
  · rename_i hn
    simp only [hn] at herr
    simp only [Option.isSome_iff_ne_none, ne_eq, Decidable.not_not] at hn
    exact absurd hn herr

/-- The interpreter's runner (calls by `processMessage`, creations by `processCreateMessage`)
ends every message with the block of the frame that sent it. -/
theorem parent_runner [LawfulGasMeter Meter] {bound : Nat} {caller : Evm fork Meter}
    {message : Message fork} {lt : message.gas < bound} {c : Evm fork Meter}
    {used : GasMeter.gasHeld c.gas ≤ message.gas}
    (h : (match message.target with
      | some _ => processMessage fork message caller.state caller.substate.child
      | none => processCreateMessage fork message caller.state caller.substate.child :
        Except EvmError { evm : Evm fork Meter // GasMeter.gasHeld evm.gas ≤ message.gas }) =
      .ok ⟨c, used⟩) :
    c.state.parent = caller.state.parent := by
  have _ := lt
  split at h
  · obtain ⟨last, hl, hp⟩ := (parent_process message.gas).1 message caller.state _ _ _ rfl ⟨c, used⟩ h
    have hl' : c = rollbackOnError caller.state last := hl
    rw [hl', parent_rollbackOnError]
    exact hp
  · exact (parent_process message.gas).2 message caller.state _ _ _ rfl ⟨c, used⟩ h

end UsdtVerify.Local
