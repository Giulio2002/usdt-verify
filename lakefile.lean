import Lake
open Lake DSL

/-! Properties of the deployed USDT runtime bytecode, proved with EthLib. -/

package «UsdtVerify» where

require EthLib from git "https://github.com/ethereum/EthLib" @ "fd3457dbfbf2118fd5d05fab5b42ffaafa07f28d"

@[default_target]
lean_lib «UsdtVerify» where
