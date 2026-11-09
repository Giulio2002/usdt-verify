import Lake
open Lake DSL

/-! Properties of the deployed USDT runtime bytecode, proved with EthLib. -/

package «UsdtVerify» where

require EthLib from git "https://github.com/ethereum/EthLib" @ "62dbd687dfa0a10641cf24e35c2572d3039bad55"

@[default_target]
lean_lib «UsdtVerify» where
