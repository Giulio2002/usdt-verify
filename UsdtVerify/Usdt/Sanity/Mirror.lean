import UsdtVerify.Evm.Mirror
import UsdtVerify.Usdt.Invariant.All

/-!
# Sanity: `HonestBalanceAt` for EthLib's `processRunner` with a real upgraded code (round 30)

docs/AUDIT.md, finding 2. `HonestBalanceAt runChild message S` (Invariant/All.lean) asks that
every call the code of USDT makes from `S` to the upgraded address with the data of
`balanceOf(a)` (`dataB message`), when it ends with no error, writes at 0x60 the word that the
child's end state holds in USDT's own `balances[a]` slot (`balSlot message`).

Here the upgraded address holds `MIRROR` (Evm/Mirror.lean), 25 bytes of bytecode that answer
`balanceOf(a)` with the word in slot `keccak(a ++ 2)` of its OWN storage. It reads its own storage,
not USDT's, so its answer is honest only when its storage mirrors USDT's for the queried slot.
That is the hypothesis `hmirror` on the start state `S`:

`storageAt S (upAddr S message) (balSlot message) = storageAt S message.currentTarget (balSlot message)`.

- `honestBalanceAt_process_mirror`: from Paris, when the upgraded address of `message` in `S`
  holds `MIRROR`, is no precompile, and `hmirror` holds, `processRunner` at any bound meets
  `HonestBalanceAt … message S`. Every gas is covered: a call that runs out of gas ends with an
  error and `HonestBalanceAt` asks nothing of it; one that ends with no error answers the word
  (`process_mirror`).

The caller frames are those of `SentVia` (their state reads as `S`, so it has the storage of `S`),
so the word
the child reads is the word of `S`; the child only reads, so USDT's slot in its end state is the
slot of `S`.
-/

namespace UsdtVerify.Sanity

open EthLib.Base (Fork U256 Address)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open Complete Deprecated DeprecatedBalance DeprecatedDestroy DestroySpec

variable {fork : Fork}

theorem loadWord_wordBytes_zero (w : U256) : loadWord (wordBytes w) 0 32 = w := by
  have h := loadWord_append_wordBytes ByteArray.empty w
  rwa [ByteArray.empty_append] at h

/-- **`HonestBalanceAt` for `processRunner` with a real code.** From Paris, when the upgraded
address of `message` in `S` holds `MIRROR` and is no precompile, and its slot `balSlot message`
holds in `S` the word that USDT's `balances[a]` holds (`hmirror`), `processRunner` at any bound
meets `HonestBalanceAt`. -/
theorem honestBalanceAt_process_mirror (hparis : .paris ≤ fork) {bound : Nat}
    {message : Message fork} {S : State.TransactionState}
    (hcode : S.getCode (S.getAccount (upAddr S message)).codeHash = .ok MIRROR)
    (hnp : Precompiles.isPrecompile fork (upAddr S message).toU256.toNat = false)
    (hmirror : storageAt S (upAddr S message) (balSlot message) =
      storageAt S message.currentTarget (balSlot message)) :
    HonestBalanceAt (processRunner fork bound) message S := by
  intro caller msg lt child hs hch hmd he
  obtain ⟨c, r, hc, hroute, hsv, hview⟩ := sendsVia_of_sentVia hs
  rw [hcode] at hc
  cases hc
  rcases r with _ | ⟨d, c'⟩
  · obtain ⟨-, hmt, htg, hca, hmc, -, -, hval, -, -⟩ := hsv
    have hpre : precompileAddress fork msg = none := by
      simp only [precompileAddress, hca, routeAddr, hnp]; rfl
    have hk : loadWord msg.data 4 32 = addrArg message.data 0 := by
      rw [hmd]; exact loadWord_append_wordBytes SEL_B _
    obtain ⟨ho, hs⟩ := process_mirror hparis caller lt hmc htg hval hpre hk hch he
    rw [ho, hs, resWord_outMemOf (size_memD message) (by rw [size_wordBytes]; omega),
      loadWord_wordBytes_zero, storageAt_readSlot, hmt,
      storageAt_of_readsAs hview, storageAt_of_readsAs hview]
    exact hmirror
  · exact absurd hroute.2.1 (by rw [delegatedAddress_mirror]; exact fun h => by cases h)

end UsdtVerify.Sanity
