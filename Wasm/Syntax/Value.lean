/- Encoding of defintion WASM's value defintion:
    https://webassembly.github.io/spec/core/syntax/values.html
-/
import Wasm.Util
import Numbers
open Numbers

namespace Wasm.Syntax.Value

-- TODO: actually do floating point
def FloatN (n : Nat) := Float

def Byte := UInt8

-- use this structure to ensure there's always a byte
inductive Bytes
| fst : Byte → Bytes
| cons : Byte → Bytes → Bytes

def Bytes.length (bytes : Bytes) : Nat :=
  match bytes with
  | .fst _ => 1
  | .cons _ bs => Nat.succ (length bs)

theorem Bytes.zero_lt_length : 0 < Bytes.length bytes := by
  cases bytes <;> simp [Bytes.length]

theorem Bytes.length_cons : Bytes.length (.cons b bs) = Nat.succ (Bytes.length bs) := by
  rw [Bytes.length]

theorem Bytes.length_fst : Bytes.length (.fst b) = 1 := by rw [Bytes.length]

def Bytes.reverse (bytes : Bytes) : Bytes :=
  match bytes with
  | .fst b     => .fst b
  | .cons b bs => rev bs (.fst b)
where rev (bytes acc : Bytes) : Bytes :=
  match bytes with
  | .fst b => .cons b acc
  | .cons b bs => rev bs (.cons b acc)

theorem Bytes.length_rev : ∀ acc, Bytes.length (reverse.rev bytes acc) = Bytes.length bytes + Bytes.length acc := by
  induction bytes
  case fst b =>
    simp [reverse.rev, length_cons, length_fst, Nat.succ_eq_one_add]
  case cons b bs ih =>
    intro acc
    simp [reverse.rev, ih, length_cons, length_cons, Nat.succ_add_eq_succ_add]

theorem Bytes.length_reverse : Bytes.length (Bytes.reverse bytes) = Bytes.length bytes := by
  cases bytes <;> simp [reverse]
  case cons b bs => simp [length_rev, length_fst, length_cons]

def Bytes.last (bytes : Bytes) : Byte :=
  match bytes with
  | .fst b => b
  | .cons _ bs => last bs

def Bytes.drop_last (bytes : Bytes) (h₁ : Bytes.length bytes > 1) : Bytes :=
  match h₂ : bytes.reverse with
  | .fst b => by
    rw [←Bytes.length_reverse, h₂] at h₁
    contradiction
  | .cons _ bs => bs.reverse

-- theorem Bytes.length_drop_last (h₁ : Bytes.length bs = n)
    -- : Bytes.length (Bytes.drop_last (.cons b bs) h₂) = n := by
  -- simp [drop_last]
  -- split
  -- . contradiction
  -- .
    -- sorry

-- def Bytes.last (bytes : Bytes) (_ : bytes = .cons b bs) : Byte :=
  -- match bytes with
  -- | .fst _ => by contradiction
  -- | .cons _b₂ (.fst b₁) => b₁
  -- | .cons _b₂ (.cons b₁ bs₁) => @Bytes.last b₁ bs₁ (.cons b₁ bs₁) (by simp)
-- 
-- def Bytes.drop_last (bytes : Bytes) (_ : bytes = .cons b bs) : Bytes :=
  -- match bytes with
  -- | .fst _ => by contradiction
  -- | .cons b₂ (.fst _b₁) => .fst b₂
  -- | .cons b₂ (.cons b₁ bs₁) =>
    -- .cons b₂ (@Bytes.drop_last b₁ bs₁ (.cons b₁ bs₁) (by simp))
-- 
-- theorem Bytes.length_drop_last
    -- : Bytes.length (Bytes.drop_last (.cons b bs) h) = Bytes.length bs := by
  -- cases bs <;> rw [drop_last]
  -- case fst _ => rfl
  -- case cons x y =>
    -- rw [Bytes.length_cons, Bytes.length_cons, Nat.succ_inj']
    -- induction y <;> rw [drop_last]
    -- case fst _ => simp [Bytes.length_fst]
    -- case cons i j ih =>
      -- sorry

-- least significant byte is at the end of the list
def Unsigned.toBytes (n : { i // 0 < i }) (v : Unsigned n) : Bytes :=
  if h : n.val ≤ 8
  then .fst (UInt8.ofNat (v.toNat % 256))
  else
    let next := ⟨n.val - 8, Nat.zero_lt_sub_of_lt (Nat.lt_of_not_le h)⟩
    .cons (UInt8.ofNat (v.toNat % 256)) (toBytes next (Unsigned.ofNat (v.toNat >>> 8)))
termination_by toBytes n v => n.val
decreasing_by
  simp_wf
  apply Nat.lt_iff_le_and_ne.mp (Nat.lt_of_not_le h)
    |>.left
    |> Nat.sub_lt_self (Nat.zero_lt_succ 7)

-- likewise, least significant byte is at the end of the list
def Unsigned.ofBytes (lst : Bytes)
    : Unsigned ⟨ 8 * lst.length
               , Nat.mul_lt_mul_of_pos_left Bytes.zero_lt_length (Nat.zero_lt_succ 7)
               ⟩ :=
  match lst with
  | .fst b    => Unsigned.ofNat b.toNat
  | .cons b bs =>
    let res := Unsigned.ofBytes bs
    Unsigned.ofNat ((res.toNat <<< 8) + b.toNat)

structure Name where
  value : String
  maxLength : value.length < Vec.max_length

end Syntax.Value

theorem Vec.index (v : Vec α) (i : Fin v.length) : Unsigned32 := by
  have h := i.isLt
  have h' := v.maxLen
  have h'' := Nat.lt_trans h h'
  exact ⟨i.val, h''⟩
