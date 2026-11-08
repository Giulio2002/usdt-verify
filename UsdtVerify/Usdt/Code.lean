import UsdtVerify.Usdt.Code.Bytes
import EthLib.Execution.Proofs.Evm.Logic.NatCode

/-!
# The deployed USDT runtime bytecode

`CODE` is the runtime bytecode of the contract at 0xdAC17F958D2ee523a2206206994597C13D831ec7.

It is stored as one natural number (EthLib's `Logic/NatCode.lean`, #1238).

`CODE` is irreducible, so no proof unfolds it; proofs use only the lemmas below.
-/

namespace UsdtVerify

open EthLib.Execution.Evm Logic.NatCode

/-- The byte at index `i` of the bytecode, or 0 past its end. -/
abbrev codeByte (i : Nat) : UInt8 := natByte CODE_NAT CODE_SIZE i

/-- The runtime bytecode of USDT. -/
@[irreducible] def CODE : ByteArray := ofNat CODE_NAT CODE_SIZE

theorem CODE_eq : CODE = ofNat CODE_NAT CODE_SIZE := by unfold CODE; rfl

theorem size_CODE : CODE.size = CODE_SIZE := by rw [CODE_eq, size_ofNat]

theorem getElem_CODE (i : Nat) (h : i < CODE.size) : CODE[i] = codeByte i := by
  revert h
  rw [CODE_eq]
  exact getElem_ofNat _ _ i

theorem byteAt_CODE (i : Nat) : EthLib.Base.byteAt CODE i = codeByte i := by
  rw [CODE_eq, byteAt_ofNat]

/-- A position that the walk from 0 reaches, holding JUMPDEST, is a valid jump destination. -/
theorem valid_CODE {d : Nat} (ht : d < CODE_SIZE) (hw : walk CODE_NAT CODE_SIZE CODE_SIZE 0 d = true)
    (hb : codeByte d = 0x5b) : isValidJumpDest (validJumpDestinations CODE) d = true := by
  rw [CODE_eq]
  exact valid_of_walk hw hb

end UsdtVerify
