import EthLib.Execution.Proofs.Evm.Logic.Rules

/-!
# LOCAL: EXTCODESIZE at every fork from Berlin

GENERIC GAP. EthLib's `Logic.extcodesize` (at the pin) holds from Berlin to before Glamsterdam,
with the price 2600 cold / 100 warm. This rule holds from Berlin on, Glamsterdam included, with
the price of the fork, `externalBaseCost fork cold` (from Glamsterdam, EIP-8038: the access plus a
warm access, 100, for the read of the code). Before Glamsterdam it is EthLib's rule
(`Logic.externalBaseCost_of_berlin`).

The proof follows EthLib's `extcodesize` line for line.
-/

namespace UsdtVerify.Local

open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic

variable {fork : Fork} {code : ByteArray} {message : Message fork} {pc : Nat}
  {memory : ByteArray} {gas : Nat} {state : State.TransactionState} {substate : Substate}

/-- From Berlin (Glamsterdam included), EXTCODESIZE pushes the size of the code of an account.

The address is the low 20 bytes of the word, and the state holds the code `c` of its account.
It pays `externalBaseCost fork cold`, accesses the address and records the read of the account. -/
theorem extcodesize (hfork : .berlin ≤ fork) {word : U256}
    {rest : List U256} {cold : Bool} {c : ByteArray} (hlt : pc < code.size)
    (hbyte : code[pc] = 0x3b)
    (hcode : state.getCode (state.getAccount (EthLib.Base.toAddressMasked word)).codeHash = .ok c)
    (hcold : decide (EthLib.Base.toAddressMasked word ∉ substate.accessedAddresses) = cold)
    (hgas : externalBaseCost fork cold ≤ gas) :
    Hoare fork (At code message pc (word :: rest) memory gas state substate)
      (At code message (pc + 1) (BitVec.ofNat 256 c.size :: rest) memory
        (gas - externalBaseCost fork cold)
        (state.recordAccountRead (EthLib.Base.toAddressMasked word))
        { substate with
          accessedAddresses :=
            substate.accessedAddresses.insert (EthLib.Base.toAddressMasked word) }) := by
  apply At.rule hlt hbyte (ofByte_of_decode (op := .extcodesize) rfl (Fork.frontier_le _)) rfl
  rintro evm ⟨hc, hj, hm, hpc, hst, hmem, hg, hrun, herr, hout, hs, hss⟩
  have found : accountCode evm (EthLib.Base.toAddressMasked word) = .ok c := by
    simp [accountCode, hs, hcode, Except.mapError]
  rw [extcodesizeStep_of_accountCode hst found]
  simp only [accessAddress, hfork, ↓reduceIte, hss, hcold, hg, charge_nat hgas]
  exact ⟨_, rfl, hc, hj, hm, by simp [hpc], rfl, hmem, rfl, hrun, herr, hout, by simp [hs],
    by simp⟩

end UsdtVerify.Local
