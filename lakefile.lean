import Lake
open Lake DSL

/-! Properties of the deployed USDT runtime bytecode, proved with EthLib. -/

package «UsdtVerify» where

require EthLib from git "https://github.com/ethereum/EthLib" @ "0c34dc0010f6ff1b3d5f1c7614af10faa85fb685"

@[default_target]
lean_lib «UsdtVerify» where
