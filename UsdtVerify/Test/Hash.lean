import UsdtVerify.Code
import EthLib.Execution.Evm.Instructions.Keccak

/-!
# Test: the embedded bytecode is the fetched one

The build runs these checks; a failing check is an error of the build.

They are tests, run by the interpreter, not theorems.

- The bytes of `CODE` are the bytes of `data/usdt.runtime.hex`.
- The Keccak-256 hash of `CODE` is the hash recorded in `data/SOURCE.md`.
-/

namespace UsdtVerify.Test

open EthLib.Execution.Evm

/-- The Keccak-256 hash of the runtime bytecode, from `scripts/keccak.py`. -/
def EXPECTED_HASH : String := "b44fb4e949d0f78f87f79ee46428f23a2a5713ce6fc6e0beb3dda78c2ac1ea55"

/-- Lowercase hexadecimal of a list of bytes. -/
def hexOf (bytes : List UInt8) : String :=
  String.join (bytes.map fun b =>
    let d := fun (n : Nat) => if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)
    String.ofList [d (b.toNat / 16), d (b.toNat % 16)])

#eval show IO Unit from do
  let hex ← IO.FS.readFile "data/usdt.runtime.hex"
  let expected := hex.trimAscii.toString
  let got := hexOf CODE.toList
  unless got == expected do
    throw (IO.userError "CODE differs from data/usdt.runtime.hex")
  unless CODE.size == 11075 do
    throw (IO.userError "CODE has the wrong size")
  let h := hexOf (EthLib.Base.U256.toBeBytes (keccak CODE)).toList
  unless h == EXPECTED_HASH do
    throw (IO.userError s!"keccak256 of CODE is {h}")
  IO.println s!"CODE: {CODE.size} bytes, keccak256 {h}"

end UsdtVerify.Test
