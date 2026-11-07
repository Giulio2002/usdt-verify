import UsdtVerify.Spec.Calldata

/-!
# The dispatcher of USDT

- At 0, `60 60 60 40 52` writes the word 0x60 at offset 0x40 of memory (the free memory pointer).
- At 5, `60 04 36 10 61 01 96 57` jumps to 0x196 when the call data has fewer than 4 bytes.
- At 13, the code divides the call data word at 0 by `2 ^ 224` and masks it to 32 bits.
- At 54, a table of 32 entries compares that selector with each key and jumps to its function.
-/

namespace UsdtVerify

open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate}

/-- The memory after the first write: 96 bytes, with the word 0x60 at offset 0x40. -/
def MEM0 : ByteArray := memoryWrite (memoryExtend .empty 96) 64 (wordBytes 0x60)

/-- The code before the table: from a call of 4 bytes or more, it computes the selector. -/
theorem prelude (hsize : 4 ≤ message.data.size) (hsize' : message.data.size < 2 ^ 256)
    {gas : Nat} (hg : 62 ≤ gas) :
    Hoare fork (At CODE message 0 [] .empty gas state substate)
      (At CODE message 54 [BitVec.ofNat 256 (selector message.data)] MEM0 (gas - 62) state
        substate) := by
  have hext : extendMemory ByteArray.empty.size [((BitVec.ofNat 256 (0x40 : UInt8).toNat : U256),
      (32 : U256))] = ⟨9, 96⟩ := by decide
  step push1R 0x60
  step push1R 0x40
  step mstore (by code_fact) (by code_fact) (by simp only [hext]; omega)
  step reshape rfl (by rw [hext]) (show _ = gas - 18 by simp only [hext]; omega)
  step push1R 0x04
  step Logic.calldatasize (by code_fact) (by code_fact) (by gas_ok) (by stk_ok)
  step binR 0x10 Local.instruction_lt
  step pushR 2 0x0196
  refine Triple.seq (Logic.jumpi_of_eq_zero (by code_fact) (by code_fact) (by gas_ok) ?_) ?_
  · have h4 : (BitVec.ofNat 256 (UInt8.toNat 4) : U256).toNat = 4 := by decide
    simp only [lessThan, h4, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsize']
    split <;> first | omega | rfl
  step push1R 0x00
  step calldataload (by code_fact) (by code_fact) (by gas_ok)
  step pushR 29 (BitVec.ofNat 256 (2 ^ 224))
  step swapR 0
  step binR 0x04 Local.instruction_div
  step pushR 4 (BitVec.ofNat 256 0xffffffff)
  step binR 0x16 Local.instruction_and
  refine reshape ?_ (by rfl) (by gas_ok)
  have h0 : (BitVec.ofNat 256 (UInt8.toNat 0) : U256).toNat = 0 := by decide
  simp only [h0, List.cons.injEq, and_true]
  exact selector_word message.data

end UsdtVerify
