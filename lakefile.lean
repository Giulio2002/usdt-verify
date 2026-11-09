import Lake
open Lake DSL

/-! Properties of the deployed USDT runtime bytecode, proved with EthLib. -/

package «UsdtVerify» where

require EthLib from git "https://github.com/ethereum/EthLib" @ "bc16ee428baf03295ef3622c30c9c901bae1444a"

@[default_target]
lean_lib «UsdtVerify» where
