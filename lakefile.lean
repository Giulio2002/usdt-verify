import Lake
open Lake DSL

/-! Properties of the deployed USDT runtime bytecode, proved with EthLib. -/

package «UsdtVerify» where

require EthLib from git "https://github.com/ethereum/EthLib" @ "d4d422780db5d668b06d3fc2782ae7bca21074e1"

@[default_target]
lean_lib «UsdtVerify» where
