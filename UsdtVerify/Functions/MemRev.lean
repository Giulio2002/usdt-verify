import UsdtVerify.Functions.Common

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
  · rw [if_pos (show i < a.size + b.size by omega), if_pos (show s ≤ s + i ∧ s + i < s + a.size
      from ⟨by omega, by omega⟩), if_pos hi]
    congr 1
    omega
  · by_cases hj : i < a.size + b.size
    · rw [if_pos hj, if_neg (show ¬(s ≤ s + i ∧ s + i < s + a.size) by omega),
        if_pos (show s + a.size ≤ s + i ∧ s + i < s + a.size + b.size from ⟨by omega, by omega⟩),
        if_neg hi]
      congr 1
      omega
    · rw [if_neg hj, if_neg hi, byteAt_of_size_le (by omega)]

end UsdtVerify
