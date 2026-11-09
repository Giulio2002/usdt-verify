import UsdtVerify.Usdt.MeterOwner

/-!
# The owner functions over EthLib's EIP-8037 meter, at any reservoir

As `ok_approve_any` (Usdt/MeterIff.lean), for the ten owner functions not deprecated. From a frame
`m` over `StateGasMeter` whose `toNat` is the fresh frame of `CODE` with `gas` gas, at any
reservoir, for any gas bound and message runner, SSTORE refills allowed:

- `ok_X_any`: a run of the loop that ends with no error meets the condition of the function in
  Usdt/Spec/Guards.lean, its output is empty, and its state and substate (the logs included) are
  those of the success path of `ok_X` (Usdt/Complete/Owner.lean) over the meter `Nat`.

With `X_ok_dom` (Usdt/Exact/Owner.lean) and the exact forms of Usdt/Refill/OwnerS.lean and
Usdt/Refill/ChainOwner.lean, which take the condition as hypotheses, this gives both directions of
the success condition at any reservoir.
These theorems say nothing about the gas left at the end; `X_gas_any` (Usdt/MeterGas.lean) does.
-/

namespace UsdtVerify.Exact

open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic hiding SpecG
open UsdtVerify.Gas
open UsdtVerify.Meter
open UsdtVerify.Shadow
open Complete Owner Admin Pause BlackList Issue SetParams AddrWrite SafeMath
open PauseSpec BlackListSpec IssueSpec SetParamsSpec AddrWriteSpec DestroySpec

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate} {bound : Nat} {runChild : MessageRunner fork StateGasMeter bound}
  {m s : Evm fork StateGasMeter} {gas : Nat}

section
variable (hfork : .berlin ≤ fork) (hsize' : message.data.size < 2 ^ 256)
  (start : At CODE message 0 [] .empty gas state substate (toNat m))
  {within : GasMeter.gasHeld m.gas ≤ bound}
  (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild m within = .ok s)
  (hok : s.error = none)
include hfork hsize' start hrun hok

/-- **pause over the EIP-8037 meter, any reservoir.** A run that ends with no error meets
`PauseGuard`; its output is empty, and its state and substate are those of `ok_pause`. -/
theorem ok_pause_any (hsel : selector message.data = 0x8456cb59) :
    PauseGuard state message ∧ s.output = .empty ∧
      s.state = writeSlot state message.currentTarget 0
          (withPaused (storageAt state message.currentTarget 0) 1) ∧
      s.substate = { storeSub fork substate message.currentTarget 0
            (originalAt state message.currentTarget 0) (storageAt state message.currentTarget 0)
            (withPaused (storageAt state message.currentTarget 0) 1) with
          logs := substate.logs.push (log0 message.currentTarget PAUSE_TOPIC) } := by
  obtain ⟨G, hE⟩ := shadow_ends hfork hrun hok
  have st' := at_addGas start (budget m)
  obtain ⟨h4, hv, -⟩ := ends_ok_dispatch hfork hsize' st' hE hok
  obtain ⟨hst, hacc, hown, hp, ho, -, hS, hSS⟩ := ok_pause hfork hsize' hsel rfl st' hE hok
  exact ⟨⟨⟨h4, hv⟩, ⟨hst, hacc⟩, hown, hp⟩, ho, hS, hSS⟩

/-- **unpause over the EIP-8037 meter, any reservoir.** A run that ends with no error meets
`UnpauseGuard`; its output is empty, and its state and substate are those of `ok_unpause`. -/
theorem ok_unpause_any (hsel : selector message.data = 0x3f4ba83a) :
    UnpauseGuard state message ∧ s.output = .empty ∧
      s.state = writeSlot state message.currentTarget 0
          (withPaused (storageAt state message.currentTarget 0) 0) ∧
      s.substate = { storeSub fork substate message.currentTarget 0
            (originalAt state message.currentTarget 0) (storageAt state message.currentTarget 0)
            (withPaused (storageAt state message.currentTarget 0) 0) with
          logs := substate.logs.push (log0 message.currentTarget UNPAUSE_TOPIC) } := by
  obtain ⟨G, hE⟩ := shadow_ends hfork hrun hok
  have st' := at_addGas start (budget m)
  obtain ⟨h4, hv, -⟩ := ends_ok_dispatch hfork hsize' st' hE hok
  obtain ⟨hst, hacc, hown, hp, ho, -, hS, hSS⟩ := ok_unpause hfork hsize' hsel rfl st' hE hok
  exact ⟨⟨⟨h4, hv⟩, ⟨hst, hacc⟩, hown, hp⟩, ho, hS, hSS⟩

/-- **addBlackList over the EIP-8037 meter, any reservoir.** A run that ends with no error meets
`OwnerWriteGuard`; its output is empty, and its state and substate are those of
`ok_addBlackList`. -/
theorem ok_addBlackList_any (hsel : selector message.data = 0x0ecb93c0) :
    OwnerWriteGuard state message ∧ s.output = .empty ∧
      s.state = listState state message 1 ∧
      s.substate = listSub fork substate state message 1 ADDED_TOPIC := by
  obtain ⟨G, hE⟩ := shadow_ends hfork hrun hok
  have st' := at_addGas start (budget m)
  obtain ⟨h4, hv, -⟩ := ends_ok_dispatch hfork hsize' st' hE hok
  obtain ⟨hst, hacc, hown, ho, -, hS, hSS⟩ := ok_addBlackList hfork hsize' hsel rfl rfl st' hE hok
  exact ⟨⟨⟨h4, hv⟩, ⟨hst, hacc⟩, hown⟩, ho, hS, hSS⟩

/-- **removeBlackList over the EIP-8037 meter, any reservoir.** A run that ends with no error
meets `OwnerWriteGuard`; its output is empty, and its state and substate are those of
`ok_removeBlackList`. -/
theorem ok_removeBlackList_any (hsel : selector message.data = 0xe4997dc5) :
    OwnerWriteGuard state message ∧ s.output = .empty ∧
      s.state = listState state message 0 ∧
      s.substate = listSub fork substate state message 0 REMOVED_TOPIC := by
  obtain ⟨G, hE⟩ := shadow_ends hfork hrun hok
  have st' := at_addGas start (budget m)
  obtain ⟨h4, hv, -⟩ := ends_ok_dispatch hfork hsize' st' hE hok
  obtain ⟨hst, hacc, hown, ho, -, hS, hSS⟩ :=
    ok_removeBlackList hfork hsize' hsel rfl rfl st' hE hok
  exact ⟨⟨⟨h4, hv⟩, ⟨hst, hacc⟩, hown⟩, ho, hS, hSS⟩

/-- **issue over the EIP-8037 meter, any reservoir.** A run that ends with no error meets
`IssueGuard`; its output is empty, and its state and substate are those of `ok_issue`. -/
theorem ok_issue_any (hsel : selector message.data = 0xcc872b66) :
    IssueGuard state message ∧ s.output = .empty ∧
      s.state = issueState state message ∧ s.substate = issueSub fork substate state message := by
  obtain ⟨G, hE⟩ := shadow_ends hfork hrun hok
  have st' := at_addGas start (budget m)
  obtain ⟨h4, hv, -⟩ := ends_ok_dispatch hfork hsize' st' hE hok
  obtain ⟨hst, hacc, hown, h0, hT, hB, ho, -, hS, hSS⟩ :=
    ok_issue hfork hsize' hsel rfl rfl rfl st' hE hok
  exact ⟨⟨⟨h4, hv⟩, ⟨hst, hacc⟩, hown, h0, hT, hB⟩, ho, hS, hSS⟩

/-- **redeem over the EIP-8037 meter, any reservoir.** A run that ends with no error meets
`RedeemGuard`; its output is empty, and its state and substate are those of `ok_redeem`. -/
theorem ok_redeem_any (hsel : selector message.data = 0xdb006a75) :
    RedeemGuard state message ∧ s.output = .empty ∧
      s.state = redeemState state message ∧ s.substate = redeemSub fork substate state message := by
  obtain ⟨G, hE⟩ := shadow_ends hfork hrun hok
  have st' := at_addGas start (budget m)
  obtain ⟨h4, hv, -⟩ := ends_ok_dispatch hfork hsize' st' hE hok
  obtain ⟨hst, hacc, hown, hT, hB, ho, -, hS, hSS⟩ :=
    ok_redeem hfork hsize' hsel rfl rfl rfl st' hE hok
  exact ⟨⟨⟨h4, hv⟩, ⟨hst, hacc⟩, hown, hT, hB⟩, ho, hS, hSS⟩

/-- **setParams over the EIP-8037 meter, any reservoir.** A run that ends with no error meets
`SetParamsGuard`; its output is empty, and its state and substate are those of
`ok_setParams`. -/
theorem ok_setParams_any (hsel : selector message.data = 0xc0324c77) :
    SetParamsGuard state message ∧ s.output = .empty ∧
      s.state = paramsState state message ∧ s.substate = paramsSub fork substate state message := by
  obtain ⟨G, hE⟩ := shadow_ends hfork hrun hok
  have st' := at_addGas start (budget m)
  obtain ⟨h4, hv, -⟩ := ends_ok_dispatch hfork hsize' st' hE hok
  obtain ⟨hst, hacc, hown, hb, hmm, hov, ho, -, hS, hSS⟩ :=
    ok_setParams hfork hsize' hsel rfl rfl rfl rfl st' hE hok
  exact ⟨⟨⟨h4, hv⟩, ⟨hst, hacc⟩, hown, hb, hmm, hov⟩, ho, hS, hSS⟩

/-- **deprecate over the EIP-8037 meter, any reservoir.** A run that ends with no error meets
`OwnerWriteGuard`; its output is empty, and its state and substate are those of
`ok_deprecate`. -/
theorem ok_deprecate_any (hsel : selector message.data = 0x0753c30c) :
    OwnerWriteGuard state message ∧ s.output = .empty ∧
      s.state = depState state message ∧ s.substate = depSub fork substate state message := by
  obtain ⟨G, hE⟩ := shadow_ends hfork hrun hok
  have st' := at_addGas start (budget m)
  obtain ⟨h4, hv, -⟩ := ends_ok_dispatch hfork hsize' st' hE hok
  obtain ⟨hst, hacc, hown, ho, -, hS, hSS⟩ := ok_deprecate hfork hsize' hsel rfl rfl st' hE hok
  exact ⟨⟨⟨h4, hv⟩, ⟨hst, hacc⟩, hown⟩, ho, hS, hSS⟩

/-- **transferOwnership over the EIP-8037 meter, any reservoir.** A run that ends with no error
meets `TransferOwnershipGuard`; its output is empty, and its state and substate are those of
`ok_transferOwnership`: for the address 0 only slot 0 is read, otherwise slot 0 is written. -/
theorem ok_transferOwnership_any (hsel : selector message.data = 0xf2fde38b) :
    TransferOwnershipGuard state message ∧ s.output = .empty ∧
      ((addrArg message.data 0 = 0 ∧
        s.state = readSlot state message.currentTarget 0 ∧
        s.substate = accessSlot substate message.currentTarget 0) ∨
      (addrArg message.data 0 ≠ 0 ∧
        s.state = writeSlot state message.currentTarget 0
          (withAddr (storageAt state message.currentTarget 0) (addrArg message.data 0)) ∧
        s.substate = storeSub fork substate message.currentTarget 0
          (originalAt state message.currentTarget 0) (storageAt state message.currentTarget 0)
          (withAddr (storageAt state message.currentTarget 0) (addrArg message.data 0)))) := by
  obtain ⟨G, hE⟩ := shadow_ends hfork hrun hok
  have st' := at_addGas start (budget m)
  obtain ⟨h4, hv, -⟩ := ends_ok_dispatch hfork hsize' st' hE hok
  obtain ⟨hown, ho, h⟩ := ok_transferOwnership hfork hsize' hsel rfl st' hE hok
  refine ⟨⟨⟨h4, hv⟩, hown, fun hz => ?_⟩, ho, ?_⟩
  · rcases h with ⟨h0, -⟩ | ⟨-, hst, hacc, -⟩
    · exact absurd h0 hz
    · exact ⟨hst, hacc⟩
  · rcases h with ⟨h0, -, hS, hSS⟩ | ⟨h0, -, -, -, hS, hSS⟩
    · exact .inl ⟨h0, hS, hSS⟩
    · exact .inr ⟨h0, hS, hSS⟩

/-- **destroyBlackFunds over the EIP-8037 meter, any reservoir.** Not deprecated (byte 20 of slot
10 is 0). A run that ends with no error meets `DestroyBlackFundsGuard`; its output is empty, and
its state and substate are those of `ok_destroyBlackFunds`. -/
theorem ok_destroyBlackFunds_any (hsel : selector message.data = 0xf3bdc228)
    (hdep : byte20 (storageAt state message.currentTarget 10) = 0) :
    DestroyBlackFundsGuard state message ∧ s.output = .empty ∧
      s.state = destroyState state message ∧
      s.substate = destroySub fork substate state message := by
  obtain ⟨G, hE⟩ := shadow_ends hfork hrun hok
  have st' := at_addGas start (budget m)
  obtain ⟨h4, hv, -⟩ := ends_ok_dispatch hfork hsize' st' hE hok
  obtain ⟨hst, hacc, hown, hl, ho, -, hS, hSS⟩ :=
    ok_destroyBlackFunds hfork hsize' hsel hdep rfl rfl rfl rfl rfl st' hE hok
  exact ⟨⟨⟨h4, hv⟩, ⟨hst, hacc⟩, hown, hl⟩, ho, hS, hSS⟩

end

end UsdtVerify.Exact
