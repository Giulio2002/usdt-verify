import UsdtVerify.Functions.TotalSupply
import UsdtVerify.Functions.Strings
import UsdtVerify.Functions.DeprecatedAllowance
import UsdtVerify.Functions.Fallback
import UsdtVerify.Functions.DeprecatedDestroy
import UsdtVerify.Functions.BalanceOf
import UsdtVerify.Functions.Transfer
import UsdtVerify.Functions.TransferSuccess
import UsdtVerify.Functions.ApproveSpec
import UsdtVerify.Functions.ApproveRevert
import UsdtVerify.Functions.TransferFromSpec
import UsdtVerify.Functions.TransferFeeSpec
import UsdtVerify.Functions.TransferFault
import UsdtVerify.Functions.TransferFaults
import UsdtVerify.Functions.TransferFromFault
import UsdtVerify.Functions.TransferFromFeeSpec
import UsdtVerify.Functions.DeprecatedTransfer
import UsdtVerify.Functions.DeprecatedTransferFrom
import UsdtVerify.Functions.TransferFromFault2
import UsdtVerify.Summary
import UsdtVerify.Functions.Nonpayable
import UsdtVerify.Functions.PauseSpec
import UsdtVerify.Functions.BlackListSpec
import UsdtVerify.Functions.IssueSpec
import UsdtVerify.Functions.SetParamsSpec
import UsdtVerify.Functions.AddrWriteSpec
import UsdtVerify.Functions.Destroy
import UsdtVerify.Functions.DestroySpec
import UsdtVerify.Functions.GettersMap
import UsdtVerify.Functions.RunFrames
import UsdtVerify.Functions.Deprecated
import UsdtVerify.Functions.DeprecatedBalance

/-! # Test: the axioms of the main theorems (printed at build time). -/

#print axioms UsdtVerify.TotalSupply.runFrame_spec
#print axioms UsdtVerify.BalanceOf.runFrame_spec
#print axioms UsdtVerify.Transfer.runFrame_paused
#print axioms UsdtVerify.Transfer.runFrame_blacklisted
#print axioms UsdtVerify.Transfer.runFrame_short
#print axioms UsdtVerify.TransferOk.spec_ok
#print axioms UsdtVerify.TransferOk.runFrame_ok
#print axioms UsdtVerify.Approve.spec_zero
#print axioms UsdtVerify.Approve.spec_set
#print axioms UsdtVerify.Approve.runFrame_revert
#print axioms UsdtVerify.TransferFrom.spec_ok
#print axioms UsdtVerify.TransferFrom.runFrame_ok
#print axioms UsdtVerify.TransferFee.spec_fee
#print axioms UsdtVerify.TransferFee.runFrame_fee
#print axioms UsdtVerify.TransferOk.spec_low
#print axioms UsdtVerify.TransferOk.runFrame_low
#print axioms UsdtVerify.TransferOk.spec_mulOv
#print axioms UsdtVerify.TransferOk.spec_feeGt
#print axioms UsdtVerify.TransferOk.spec_toOv
#print axioms UsdtVerify.TransferOk.spec_ownerOv
#print axioms UsdtVerify.TransferFrom.spec_paused
#print axioms UsdtVerify.TransferFrom.spec_blacklisted
#print axioms UsdtVerify.TransferFrom.spec_short
#print axioms UsdtVerify.TransferFrom.spec_allowLow
#print axioms UsdtVerify.TransferFrom.spec_balLow
#print axioms UsdtVerify.TransferFrom.spec_mulOv
#print axioms UsdtVerify.TransferFrom.spec_feeF
#print axioms UsdtVerify.TransferFrom.runFrame_feeF
#print axioms UsdtVerify.TransferFrom.spec_feeGtF
#print axioms UsdtVerify.TransferFrom.spec_toOvF
#print axioms UsdtVerify.TransferFrom.spec_ownerOvF
#print axioms UsdtVerify.Summary.transfer_ok_effects
#print axioms UsdtVerify.Summary.transferFrom_ok_effects
#print axioms UsdtVerify.Summary.transfer_fee_effects
#print axioms UsdtVerify.Summary.transferFrom_fee_effects
#print axioms UsdtVerify.TransferOk.runFrame_mulOv
#print axioms UsdtVerify.TransferOk.runFrame_feeGt
#print axioms UsdtVerify.TransferOk.runFrame_toOv
#print axioms UsdtVerify.TransferOk.runFrame_ownerOv
#print axioms UsdtVerify.TransferFrom.runFrame_paused
#print axioms UsdtVerify.TransferFrom.runFrame_blacklisted
#print axioms UsdtVerify.TransferFrom.runFrame_short
#print axioms UsdtVerify.TransferFrom.runFrame_allowLow
#print axioms UsdtVerify.TransferFrom.runFrame_balLow
#print axioms UsdtVerify.TransferFrom.runFrame_mulOv
#print axioms UsdtVerify.TransferFrom.runFrame_feeGtF
#print axioms UsdtVerify.TransferFrom.runFrame_toOvF
#print axioms UsdtVerify.TransferFrom.runFrame_ownerOvF
#print axioms UsdtVerify.Approve.runFrame_zero
#print axioms UsdtVerify.Approve.runFrame_set
#print axioms UsdtVerify.Summary.transfer_ok_conserves
#print axioms UsdtVerify.Summary.transfer_fee_conserves
#print axioms UsdtVerify.Summary.transferFrom_ok_conserves
#print axioms UsdtVerify.Summary.transferFrom_fee_conserves
#print axioms UsdtVerify.Deprecated.spec_dep
#print axioms UsdtVerify.Deprecated.spec_dep_answers
#print axioms UsdtVerify.Deprecated.spec_dep_fails
#print axioms UsdtVerify.Deprecated.runFrame_dep_answers
#print axioms UsdtVerify.Deprecated.runFrame_dep_process
#print axioms UsdtVerify.Deprecated.spec_depNoCode
#print axioms UsdtVerify.DeprecatedBalance.spec_depB
#print axioms UsdtVerify.DeprecatedBalance.spec_depB_answers
#print axioms UsdtVerify.DeprecatedBalance.spec_depB_fails
#print axioms UsdtVerify.DeprecatedBalance.runFrame_depB_process
#print axioms UsdtVerify.DeprecatedBalance.spec_depBNoCode
#print axioms UsdtVerify.DeprecatedTransfer.spec_depT
#print axioms UsdtVerify.DeprecatedTransfer.spec_depT_succeeds
#print axioms UsdtVerify.DeprecatedTransfer.spec_depT_fails
#print axioms UsdtVerify.DeprecatedTransfer.runFrame_depT_process
#print axioms UsdtVerify.DeprecatedTransfer.spec_depTNoCode
#print axioms UsdtVerify.DeprecatedTransfer.spec_depA
#print axioms UsdtVerify.DeprecatedTransfer.spec_depA_succeeds
#print axioms UsdtVerify.DeprecatedTransfer.spec_depA_fails
#print axioms UsdtVerify.DeprecatedTransfer.runFrame_depA_process
#print axioms UsdtVerify.DeprecatedTransfer.spec_depANoCode
#print axioms UsdtVerify.DeprecatedTransferFrom.spec_depF
#print axioms UsdtVerify.DeprecatedTransferFrom.spec_depF_succeeds
#print axioms UsdtVerify.DeprecatedTransferFrom.spec_depF_fails
#print axioms UsdtVerify.DeprecatedTransferFrom.runFrame_depF_process
#print axioms UsdtVerify.DeprecatedTransferFrom.spec_depFNoCode
#print axioms UsdtVerify.Nonpayable.spec
#print axioms UsdtVerify.Nonpayable.runFrame_spec
#print axioms UsdtVerify.PauseSpec.spec_pause
#print axioms UsdtVerify.PauseSpec.spec_unpause
#print axioms UsdtVerify.PauseSpec.spec_pause_notOwner
#print axioms UsdtVerify.PauseSpec.spec_unpause_notOwner
#print axioms UsdtVerify.PauseSpec.spec_pause_paused
#print axioms UsdtVerify.PauseSpec.spec_unpause_notPaused
#print axioms UsdtVerify.Pause.byte20_withPaused
#print axioms UsdtVerify.Pause.owner_withPaused
#print axioms UsdtVerify.Pause.bit_withPaused
#print axioms UsdtVerify.BlackListSpec.spec_add
#print axioms UsdtVerify.BlackListSpec.spec_remove
#print axioms UsdtVerify.BlackListSpec.spec_add_notOwner
#print axioms UsdtVerify.BlackListSpec.spec_remove_notOwner
#print axioms UsdtVerify.BlackListSpec.listState_flag
#print axioms UsdtVerify.BlackListSpec.listState_other
#print axioms UsdtVerify.Admin.bit_setLow
#print axioms UsdtVerify.IssueSpec.spec_issue
#print axioms UsdtVerify.IssueSpec.spec_redeem
#print axioms UsdtVerify.IssueSpec.spec_issue_notOwner
#print axioms UsdtVerify.IssueSpec.spec_redeem_notOwner
#print axioms UsdtVerify.IssueSpec.spec_issue_req1
#print axioms UsdtVerify.IssueSpec.spec_issue_req2
#print axioms UsdtVerify.IssueSpec.spec_redeem_req1
#print axioms UsdtVerify.IssueSpec.spec_redeem_req2
#print axioms UsdtVerify.IssueSpec.issue_effects
#print axioms UsdtVerify.IssueSpec.redeem_effects
#print axioms UsdtVerify.SetParamsSpec.spec_setParams
#print axioms UsdtVerify.SetParamsSpec.spec_notOwner
#print axioms UsdtVerify.SetParamsSpec.spec_bpHigh
#print axioms UsdtVerify.SetParamsSpec.spec_feeHigh
#print axioms UsdtVerify.SetParamsSpec.params_effects
#print axioms UsdtVerify.AddrWriteSpec.spec_deprecate
#print axioms UsdtVerify.AddrWriteSpec.spec_deprecate_notOwner
#print axioms UsdtVerify.AddrWriteSpec.deprecate_effects
#print axioms UsdtVerify.AddrWriteSpec.spec_transferOwnership
#print axioms UsdtVerify.AddrWriteSpec.spec_transferOwnership_zero
#print axioms UsdtVerify.AddrWriteSpec.spec_transferOwnership_notOwner
#print axioms UsdtVerify.AddrWriteSpec.transferOwnership_effects
#print axioms UsdtVerify.Destroy.spec_notOwner
#print axioms UsdtVerify.Destroy.spec_notListed
#print axioms UsdtVerify.DestroySpec.spec
#print axioms UsdtVerify.DestroySpec.runFrame_spec
#print axioms UsdtVerify.DestroySpec.destroy_effects
#print axioms UsdtVerify.Getters.spec_slot
#print axioms UsdtVerify.Getters.spec_decimals
#print axioms UsdtVerify.Getters.spec_maximumFee
#print axioms UsdtVerify.Getters.spec_totalSupplyVar
#print axioms UsdtVerify.Getters.spec_basisPointsRate
#print axioms UsdtVerify.Getters.spec_maxUint
#print axioms UsdtVerify.Getters.spec_flag
#print axioms UsdtVerify.Getters.spec_deprecated
#print axioms UsdtVerify.Getters.spec_paused
#print axioms UsdtVerify.Getters.spec_upgradedAddress
#print axioms UsdtVerify.Getters.spec_owner
#print axioms UsdtVerify.Getters.spec_getOwner
#print axioms UsdtVerify.GettersMap.spec_balances
#print axioms UsdtVerify.GettersMap.spec_isBlackListed
#print axioms UsdtVerify.GettersMap.spec_getBlackListStatus
#print axioms UsdtVerify.GettersMap.spec_allowed
#print axioms UsdtVerify.GettersMap.spec_allowance
#print axioms UsdtVerify.memoryReadBytes_write_rev
#print axioms UsdtVerify.PauseSpec.runFrame_pause
#print axioms UsdtVerify.BlackListSpec.runFrame_add
#print axioms UsdtVerify.IssueSpec.runFrame_issue
#print axioms UsdtVerify.IssueSpec.runFrame_redeem
#print axioms UsdtVerify.SetParamsSpec.runFrame_setParams
#print axioms UsdtVerify.AddrWriteSpec.runFrame_deprecate
#print axioms UsdtVerify.AddrWriteSpec.runFrame_transferOwnership
#print axioms UsdtVerify.Destroy.runFrame_notListed
#print axioms UsdtVerify.Getters.runFrame_slot
#print axioms UsdtVerify.GettersMap.runFrame_allowance
#print axioms UsdtVerify.Strings.spec_str
#print axioms UsdtVerify.Strings.spec_name
#print axioms UsdtVerify.Strings.spec_symbol
#print axioms UsdtVerify.Strings.spec_name_tether
#print axioms UsdtVerify.Strings.spec_symbol_usdt
#print axioms UsdtVerify.Strings.runFrame_name
#print axioms UsdtVerify.Strings.runFrame_symbol
#print axioms UsdtVerify.DeprecatedAllowance.spec_depAl
#print axioms UsdtVerify.DeprecatedAllowance.spec_depAl_answers
#print axioms UsdtVerify.DeprecatedAllowance.spec_depAl_fails
#print axioms UsdtVerify.DeprecatedAllowance.runFrame_depAl_process
#print axioms UsdtVerify.DeprecatedAllowance.spec_depAlNoCode
#print axioms UsdtVerify.DeprecatedAllowance.runFrame_depAlNoCode
#print axioms UsdtVerify.Fallback.spec_unknown
#print axioms UsdtVerify.Fallback.spec_short
#print axioms UsdtVerify.Fallback.runFrame_unknown
#print axioms UsdtVerify.Fallback.runFrame_short
#print axioms UsdtVerify.DeprecatedDestroy.spec_depD
#print axioms UsdtVerify.DeprecatedDestroy.spec_depD_answers
#print axioms UsdtVerify.DeprecatedDestroy.spec_depD_fails
#print axioms UsdtVerify.DeprecatedDestroy.runFrame_depD_process
#print axioms UsdtVerify.DeprecatedDestroy.spec_depDNoCode
#print axioms UsdtVerify.DeprecatedDestroy.runFrame_depDNoCode
#print axioms UsdtVerify.DeprecatedDestroy.tailD
