import EthLib.Execution.Proofs.Evm.Machine.Memory

/-!
# GENERIC: a read across two adjacent writes made in reverse order

Solidity's public mapping getters write the base slot at 32 first and the key at 0 second; the
read of the 64 bytes gives the key then the base. EthLib's `memoryReadBytes_memoryWrite_memoryWrite`
covers the writes in address order only.
-/

namespace UsdtVerify

open EthLib.Execution.Evm
open EthLib.Base (byteAt byteAt_append byteAt_of_size_le eq_of_byteAt)

/-- GENERIC: a read across two adjacent writes, the higher one made first. -/
theorem memoryReadBytes_write_rev {memory a b : ByteArray} {s : Nat}
    (hw : s + a.size + b.size ≤ memory.size) :
    memoryReadBytes (memoryWrite (memoryWrite memory (s + a.size) b) s a) s (a.size + b.size) =
      a ++ b := by
  have h1 : (memoryWrite memory (s + a.size) b).size = memory.size := size_memoryWrite (by omega)
  have h2 : (memoryWrite (memoryWrite memory (s + a.size) b) s a).size = memory.size := by
    rw [size_memoryWrite (by omega), h1]
  apply eq_of_byteAt
  · rw [size_memoryReadBytes (by omega), ByteArray.size_append]
  intro i
  rw [byteAt_memoryReadBytes (by omega), byteAt_memoryWrite (by omega),
    byteAt_memoryWrite (by omega), byteAt_append]
  by_cases hi : i < a.size
  · rw [ite_eq_left (show i < a.size + b.size by omega), ite_eq_left (show s ≤ s + i ∧ s + i < s + a.size
      from ⟨by omega, by omega⟩), ite_eq_left hi]
    congr 1
    omega
  · by_cases hj : i < a.size + b.size
    · rw [ite_eq_left hj, ite_eq_right (show ¬(s ≤ s + i ∧ s + i < s + a.size) by omega),
        ite_eq_left (show s + a.size ≤ s + i ∧ s + i < s + a.size + b.size from ⟨by omega, by omega⟩),
        ite_eq_right hi]
      congr 1
      omega
    · rw [ite_eq_right hj, ite_eq_right hi, byteAt_of_size_le (by omega)]

end UsdtVerify
