import UsdtVerify.Evm.Runners
import UsdtVerify.Evm.Write
import UsdtVerify.Evm.Calldata

/-!
# Sample states, messages and call data

For any code. Used to show that the hypotheses of a specification can hold together.

- `sState C kvs`: a transaction state over a block with no writes, whose state before the block
  has one account, at `C` (nonce 1, balance 0, no code), and at `C` the slots of the list `kvs`
  (an earlier pair wins). `hasAccount_sState`; `storageAt_sState_nil`, `storageAt_sState_cons`:
  the word of a slot.
- `sMsg b t C caller code data`: the message from `caller` to `C` that runs `code` on `data`, with
  no value, depth 0, not static, the block `b` and the transaction `t`.
- `sFrame M S ss g`: the frame that `M` starts in the state `S`, with gas `g`; `at_sFrame`.
- Call data: `selector_append`, `loadWord_append_wordBytes_append`; `data1 sel a`, `data2 sel a b`
  (a 4-byte selector and one or two argument words) and their size, selector and words.
- `slotCost_le`.
-/

namespace UsdtVerify

open EthLib.Base (Fork U256 Address Bytes32 byteAt natToBytes)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic

variable {fork : Fork}

/-! ## States -/

/-- The slots of a list of pairs (slot, word); an earlier pair wins. -/
def slotMap : List (U256 × U256) → Std.ExtTreeMap Bytes32 U256
  | [] => ∅
  | (k, v) :: kvs => (slotMap kvs).insert (U256.toBeBytes k) v

/-- The account of `sState`: nonce 1, balance 0, no code. -/
def S_ACCOUNT : State.Account := ⟨1, 0, State.EMPTY_CODE_HASH⟩

/-- A state with one account, at `C`, whose slots are those of `kvs` (every other slot 0). -/
def sState (C : Address) (kvs : List (U256 × U256)) : State.TransactionState :=
  State.TransactionState.ofBlock
    { preState :=
        { accounts := (∅ : Std.ExtTreeMap Address State.Account).insert C S_ACCOUNT
          storage := (∅ : State.StorageMap).insert C (slotMap kvs)
          code := ∅ }
      accountWrites := ∅
      storageWrites := ∅
      codeWrites := ∅
      storageClears := ∅ }

theorem hasAccount_sState (C : Address) (kvs : List (U256 × U256)) :
    hasAccount (sState C kvs) C := by
  simp [hasAccount, sState, State.TransactionState.ofBlock,
    State.TransactionState.getAccountOptional, State.State.getAccountOptional]

theorem storageAt_sState (C : Address) (kvs : List (U256 × U256)) (n : U256) :
    storageAt (sState C kvs) C n = ((slotMap kvs)[U256.toBeBytes n]?).getD 0 := by
  simp [storageAt, sState, State.TransactionState.ofBlock, State.TransactionState.getStorage,
    State.State.getStorage, State.StorageMap.slot]

theorem storageAt_sState_nil (C : Address) (n : U256) : storageAt (sState C []) C n = 0 := by
  rw [storageAt_sState]; simp [slotMap]

theorem toBeBytes_inj {a b : U256} (h : U256.toBeBytes a = U256.toBeBytes b) : a = b := by
  have := congrArg EthLib.Base.U256.fromBeBytes h
  rwa [EthLib.Base.U256.fromBeBytes_toBeBytes, EthLib.Base.U256.fromBeBytes_toBeBytes] at this

theorem storageAt_sState_cons (C : Address) (k v : U256) (kvs : List (U256 × U256)) (n : U256) :
    storageAt (sState C ((k, v) :: kvs)) C n =
      if k = n then v else storageAt (sState C kvs) C n := by
  rw [storageAt_sState, storageAt_sState]
  simp only [slotMap, Std.ExtTreeMap.getElem?_insert]
  by_cases h : k = n
  · subst h; simp
  · have h' : ¬ U256.toBeBytes k = U256.toBeBytes n := fun e => h (toBeBytes_inj e)
    simp [h, h']

/-! ## Messages and frames -/

/-- The message from `caller` to `C` that runs `code` on `data`: no value, depth 0, not static,
gas 0 (the frame's gas is set apart), the block `b` and the transaction `t`. -/
def sMsg (b : BlockEnvironment fork) (t : TransactionEnvironment fork) (C caller : Address)
    (code data : ByteArray) : Message fork where
  blockEnv := b
  txEnv := t
  caller := caller
  target := some C
  currentTarget := C
  gas := 0
  value := 0
  data := data
  codeAddress := some C
  code := code
  depth := 0
  shouldTransferValue := true
  isStatic := false
  disablePrecompiles := false

/-- The frame that `M` starts in the state `S` and substate `ss`, with gas `g`. -/
def sFrame (M : Message fork) (S : State.TransactionState) (ss : Substate) (g : Nat) :
    Evm fork Nat :=
  startFrame M S ss g

theorem at_sFrame {code : ByteArray} (M : Message fork) (hc : M.code = code)
    (S : State.TransactionState) (ss : Substate) (g : Nat) :
    At code M 0 [] .empty g S ss (sFrame M S ss g) := by
  subst hc
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## Call data -/

/-- The selector reads the first four bytes only. -/
theorem selector_append {A : ByteArray} (B : ByteArray) (h : 4 ≤ A.size) :
    selector (A ++ B) = selector A := by
  have hb : ∀ i, i < 4 → byteAt (A ++ B) i = byteAt A i := by
    intro i hi
    have h1 : i < (A ++ B).size := by rw [ByteArray.size_append]; omega
    have h2 : i < A.size := by omega
    simp only [byteAt, h1, h2, ↓reduceDIte]
    exact ByteArray.getElem_append_left h2
  simp only [selector, hb 0 (by omega), hb 1 (by omega), hb 2 (by omega), hb 3 (by omega)]

/-- The word at `A.size` of `A ++ wordBytes w ++ B` is `w`. -/
theorem loadWord_append_wordBytes_append (A B : ByteArray) (w : U256) :
    loadWord (A ++ wordBytes w ++ B) A.size 32 = w := by
  have hw := size_wordBytes w
  have hl : (List.range 32).map (fun i => byteAt (A ++ wordBytes w ++ B) (A.size + i)) =
      (wordBytes w).data.toList := by
    apply List.ext_getElem
    · simp only [List.length_map, List.length_range, Array.length_toList]
      rw [ByteArray.size_data, hw]
    · intro i h1 h2
      simp only [List.getElem_map, List.getElem_range, Array.getElem_toList]
      have hi : i < 32 := by simpa using h1
      have hlt : A.size + i < (A ++ wordBytes w ++ B).size := by
        rw [ByteArray.size_append, ByteArray.size_append, hw]; omega
      have hlt' : A.size + i < (A ++ wordBytes w).size := by
        rw [ByteArray.size_append, hw]; omega
      simp only [byteAt, hlt, ↓reduceDIte]
      rw [ByteArray.getElem_append_left hlt', ByteArray.getElem_append_right (by omega)]
      simp only [Nat.add_sub_cancel_left]
      rfl
  have bytes : (wordBytes w).data.toList = natToBytes 32 w.toNat :=
    EthLib.Base.U256.toList_toBeBytes w
  have small : w.toNat < 256 ^ 32 := by
    have := w.isLt
    rwa [show (2 : Nat) ^ 256 = 256 ^ 32 by decide] at this
  rw [loadWord, bufferRead, hl, bytes, EthLib.Base.bytesToNat_natToBytes_of_lt small]
  apply BitVec.eq_of_toNat_eq
  simp

/-- A 4-byte selector and one argument word. -/
def data1 (sel : ByteArray) (a : U256) : ByteArray := sel ++ wordBytes a

/-- A 4-byte selector and two argument words. -/
def data2 (sel : ByteArray) (a b : U256) : ByteArray := sel ++ wordBytes a ++ wordBytes b

variable {sel : ByteArray}

theorem size_data1 (hs : sel.size = 4) (a : U256) : (data1 sel a).size = 36 := by
  simp [data1, ByteArray.size_append, size_wordBytes, hs]

theorem size_data2 (hs : sel.size = 4) (a b : U256) : (data2 sel a b).size = 68 := by
  simp [data2, ByteArray.size_append, size_wordBytes, hs]

theorem selector_data1 (hs : sel.size = 4) (a : U256) : selector (data1 sel a) = selector sel :=
  selector_append _ (by simp [hs])

theorem selector_data2 (hs : sel.size = 4) (a b : U256) :
    selector (data2 sel a b) = selector sel := by
  rw [data2, selector_append _ (by rw [ByteArray.size_append, hs]; omega),
    selector_append _ (by simp [hs])]

theorem wordArg_data1 (hs : sel.size = 4) (a : U256) : wordArg (data1 sel a) 0 = a := by
  have := loadWord_append_wordBytes sel a
  rwa [hs] at this

theorem wordArg_data2_1 (hs : sel.size = 4) (a b : U256) : wordArg (data2 sel a b) 1 = b := by
  have := loadWord_append_wordBytes (sel ++ wordBytes a) b
  rwa [ByteArray.size_append, hs, size_wordBytes] at this

/-- A 4-byte selector and three argument words. -/
def data3 (sel : ByteArray) (a b c : U256) : ByteArray :=
  sel ++ wordBytes a ++ wordBytes b ++ wordBytes c

theorem size_data3 (hs : sel.size = 4) (a b c : U256) : (data3 sel a b c).size = 100 := by
  simp [data3, ByteArray.size_append, size_wordBytes, hs]

theorem selector_data3 (hs : sel.size = 4) (a b c : U256) :
    selector (data3 sel a b c) = selector sel := by
  rw [data3, selector_append _ (by simp only [ByteArray.size_append, hs]; omega),
    selector_append _ (by rw [ByteArray.size_append, hs]; omega),
    selector_append _ (by simp [hs])]

theorem wordArg_data3_2 (hs : sel.size = 4) (a b c : U256) : wordArg (data3 sel a b c) 2 = c := by
  have := loadWord_append_wordBytes (sel ++ wordBytes a ++ wordBytes b) c
  rwa [ByteArray.size_append, ByteArray.size_append, hs, size_wordBytes] at this

theorem addrArg_data3_0 (hs : sel.size = 4) (a b c : U256) :
    addrArg (data3 sel a b c) 0 = bitwiseAnd ADDR_MASK a := by
  have := loadWord_append_wordBytes_append sel (wordBytes b ++ wordBytes c) a
  rw [hs, ← ByteArray.append_assoc] at this
  show bitwiseAnd ADDR_MASK (loadWord (sel ++ wordBytes a ++ wordBytes b ++ wordBytes c) 4 32) = _
  rw [this]

/-- A write keeps a bound on every word of an account that the written word meets. -/
theorem le_writeSlot {X : State.TransactionState} {C : Address} {k v : U256} {B : Nat}
    (hacc : hasAccount X C) (hX : ∀ n, (storageAt X C n).toNat ≤ B) (hv : v.toNat ≤ B) (n : U256) :
    (storageAt (writeSlot X C k v) C n).toNat ≤ B := by
  by_cases h : n = k
  · subst h; rw [storageAt_writeSlot_self hacc]; exact hv
  · rw [storageAt_writeSlot_of_ne hacc h]; exact hX n

theorem slotCost_le (c : Bool) : slotCost c ≤ 2100 := by cases c <;> decide

end UsdtVerify
