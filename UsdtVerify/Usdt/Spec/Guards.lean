import UsdtVerify.Evm.Storage

/-!
# When each function succeeds, in plain terms

Each condition below is the exact success condition of a function: the theorems of
`Usdt/Exact/` prove that, with the gas of the success path, the run ends with no error if and
only if the condition holds.

- `CallOk`: the call data has at least 4 bytes and the call has no value.
  Every function of the table is nonpayable, so every success condition contains it.
  Each getter (name and symbol under `StrForm`, totalSupply, balanceOf and allowance when not
  deprecated) succeeds exactly when `CallOk` holds.
-/

namespace UsdtVerify

open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm

variable {fork : Fork}

/-- The call data has at least 4 bytes and the call has no value. -/
def CallOk (message : Message fork) : Prop := 4 ≤ message.data.size ∧ message.value = 0

end UsdtVerify
