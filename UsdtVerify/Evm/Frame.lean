import UsdtVerify.Evm.Write

/-!
# Which slots a change of state may write

For any code: `Writes C W S S'` says that every slot of the account `C` outside the set `W`
holds the same word in `S'` as in `S`. `NoDec C k S S'` says that the word of slot `k` of `C`
is not smaller in `S'` than in `S` (as a number). Both are reflexive and transitive, hold over
a read (`readSlot`), and over a write (`writeSlot`) of a slot in `W` (for `Writes`) or of a slot
other than `k`, or of `k` with `old + d` and no wrap (for `NoDec`).
-/

namespace UsdtVerify

open EthLib.Base (U256 Address)
open EthLib.Execution
open EthLib.Execution.Evm

variable {C : Address} {W W' : U256 → Prop} {S S' S'' : State.TransactionState}

/-- Every slot of `C` outside `W` holds the same word in `S'` as in `S`. -/
def Writes (C : Address) (W : U256 → Prop) (S S' : State.TransactionState) : Prop :=
  ∀ n, ¬ W n → storageAt S' C n = storageAt S C n

theorem Writes.refl (C : Address) (W : U256 → Prop) (S : State.TransactionState) :
    Writes C W S S := fun _ _ => rfl

theorem Writes.trans (h1 : Writes C W S S') (h2 : Writes C W S' S'') : Writes C W S S'' :=
  fun n hn => (h2 n hn).trans (h1 n hn)

theorem Writes.mono (h : Writes C W S S') (hW : ∀ n, W n → W' n) : Writes C W' S S' :=
  fun n hn => h n (fun hw => hn (hW n hw))

theorem Writes.of_same (h : ∀ n, storageAt S' C n = storageAt S C n) : Writes C W S S' :=
  fun n _ => h n

theorem Writes.read (c : Address) (m : U256) : Writes C W S (readSlot S c m) :=
  fun n _ => storageAt_readSlot S c C m n

theorem Writes.write (hacc : hasAccount S C) {m : U256} (hm : W m) (v : U256) :
    Writes C W S (writeSlot S C m v) :=
  fun _ hn => storageAt_writeSlot_of_ne hacc (fun e => hn (e ▸ hm))

/-- The word of slot `k` of `C` is not smaller in `S'` than in `S`. -/
def NoDec (C : Address) (k : U256) (S S' : State.TransactionState) : Prop :=
  (storageAt S C k).toNat ≤ (storageAt S' C k).toNat

theorem NoDec.refl (C : Address) (k : U256) (S : State.TransactionState) : NoDec C k S S :=
  Nat.le_refl _

theorem NoDec.trans {k : U256} (h1 : NoDec C k S S') (h2 : NoDec C k S' S'') :
    NoDec C k S S'' := Nat.le_trans h1 h2

theorem NoDec.read {k : U256} (c : Address) (m : U256) : NoDec C k S (readSlot S c m) := by
  unfold NoDec; rw [storageAt_readSlot]; exact Nat.le_refl _

theorem NoDec.of_writes {k : U256} (h : Writes C W S S') (hk : ¬ W k) : NoDec C k S S' := by
  unfold NoDec; rw [h k hk]; exact Nat.le_refl _

theorem NoDec.write_ne {k m : U256} (hacc : hasAccount S C) (hne : k ≠ m) (v : U256) :
    NoDec C k S (writeSlot S C m v) := by
  unfold NoDec; rw [storageAt_writeSlot_of_ne hacc hne]; exact Nat.le_refl _

/-- A write of `old + d` (no wrap) into slot `m` does not decrease any slot. -/
theorem NoDec.write_add {k m d : U256} (hacc : hasAccount S C)
    (h : (storageAt S C m).toNat + d.toNat < 2 ^ 256) :
    NoDec C k S (writeSlot S C m (add (storageAt S C m) d)) := by
  by_cases hk : k = m
  · subst hk
    unfold NoDec
    rw [storageAt_writeSlot_self hacc]
    simp only [add, BitVec.toNat_add, Nat.mod_eq_of_lt h]
    omega
  · exact NoDec.write_ne hacc hk _

theorem NoDec.rd {k : U256} (h : NoDec C k S S') (c : Address) (m : U256) :
    NoDec C k S (readSlot S' c m) := h.trans (NoDec.read c m)

theorem NoDec.wr_ne {k m : U256} (h : NoDec C k S S') (hacc : hasAccount S' C) (hne : k ≠ m)
    (v : U256) : NoDec C k S (writeSlot S' C m v) := h.trans (NoDec.write_ne hacc hne v)

/-- A write of `w + d` (no wrap) where `w` is the word of the slot: no slot decreases. -/
theorem NoDec.wr_add {k m w d : U256} (h : NoDec C k S S') (hacc : hasAccount S' C)
    (hw : w = storageAt S' C m) (hov : w.toNat + d.toNat < 2 ^ 256) :
    NoDec C k S (writeSlot S' C m (add w d)) := by
  subst hw; exact h.trans (NoDec.write_add hacc hov)

end UsdtVerify
