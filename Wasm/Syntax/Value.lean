/- Encoding of defintion WASM's value defintion:
    https://webassembly.github.io/spec/core/syntax/values.html
-/
import Mathlib
import Wasm.Util

namespace Wasm.Syntax.Value


def Unsigned (n : {i : Nat // 0 < i}) := Fin (2 ^ n)
instance : Inhabited (Unsigned n) := ⟨0, by simp⟩

namespace Unsigned

def ofNat (u : Nat) : Unsigned n := Fin.ofNat' u zero_lt_two_pow
def toNat (u : Unsigned n) : Nat := u.val

def MAX_VALUE   : Unsigned n  := ofNat (2 ^ n - 1)
def MIN_VALUE   : Unsigned n  := ofNat 0
def MAX (n : { i // 0 < i }) : Nat := 2 ^ n.val
def MIN (_ : { i // 0 < i }) : Nat := 0

def toInt (i : Unsigned n) : Int := i.toNat
def toUInt32 (i : Unsigned ⟨32, by simp⟩) : UInt32 := UInt32.ofNat' (i.toNat) (by
  have h : 4294967296 = 2 ^ 32 := by simp
  rw [UInt32.size, h, toNat]
  exact i.isLt
)
def ofInt (i : Int) : Unsigned n := ofNat (i.toNat)
def ofInt? (i : Int) : Option (Unsigned n) :=
  let size := 2 ^ (n : Nat)
  if i < size then i.toNat'.map .ofNat else .none

instance : OfNat (Unsigned n) m where
  ofNat := Unsigned.ofNat m
instance : Coe (Unsigned ⟨32, by simp⟩) Int := ⟨toInt⟩
instance : Coe (Unsigned ⟨32, by simp⟩) UInt32 := ⟨toUInt32⟩
instance : Coe (Unsigned ⟨64, by simp⟩) Int := ⟨toInt⟩
instance : Repr (Unsigned n) := ⟨reprPrec ∘ toNat⟩

nonrec def toString : Unsigned n → String := toString ∘ toNat
instance : ToString (Unsigned n) := ⟨toString⟩

nonrec def compare (i j : Unsigned n) : Ordering := compare i.val j.val
instance : Ord (Unsigned n)  := ⟨compare⟩
instance : LT  (Unsigned n)  := ltOfOrd
instance : LE  (Unsigned n)  := leOfOrd

def deq (i j : Unsigned n) :=
  match decEq i.val j.val with
  | isTrue h  => isTrue (Fin.eq_of_val_eq h)
  | isFalse h => isFalse (Fin.ne_of_val_ne h)
instance : DecidableEq (Unsigned n) := deq

end Unsigned


/- Derived to a generic bit size from C0deine -/
def Signed (n : {i : Nat // 0 < i}) := Unsigned n
instance : Inhabited (Signed n) := ⟨0, Nat.pos_pow_of_pos n (Nat.zero_lt_succ 1)⟩

namespace Signed

@[inline] def ofUnsignedN : Unsigned n → Signed n :=
  cast (by unfold Signed; rfl) id
@[inline] def toUnsignedN : Signed n → Unsigned n :=
  cast (by unfold Signed; rfl) id

def MAX_VALUE : Signed n  := ofUnsignedN <| .ofNat (2^(n - 1) - 1)
def MIN_VALUE : Signed n  := ofUnsignedN <| .ofNat (2^(n - 1))

def toInt (i : Signed n) : Int :=
  if i.toUnsignedN < MIN_VALUE.toUnsignedN
  then i.toUnsignedN.toNat -- i pos
  else i.toUnsignedN.toInt - 2 ^ (n.val)

def ofInt? (i : Int) : Option (Signed n) :=
  let offset := i + (2 ^ (n - 1) : Nat)
  if h : 0 ≤ offset && offset < Unsigned.MAX n then
    let offset : Signed n := ⟨offset.natAbs, by
      simp at *
      have := Int.natAbs_lt_natAbs_of_nonneg_of_lt h.1 h.2
      rw [Unsigned.MAX] at *
      exact this⟩
    .some <| ofUnsignedN (Unsigned.ofNat (offset.val + (2 ^ (n - 1))))
  else
    none

def ofInt (i : Int) : Signed n :=
  let offset := i + (2 ^ (n - 1) : Nat)
  if h : 0 ≤ offset && offset < Unsigned.MAX n then
    let offset : Unsigned n := ⟨offset.natAbs, by
      simp at *
      have := Int.natAbs_lt_natAbs_of_nonneg_of_lt h.1 h.2
      rw [Unsigned.MAX] at *
      exact this⟩
    ofUnsignedN (Unsigned.ofNat (offset.val + (2 ^ (n - 1))))
  else
    ⟨0, by simp⟩

def ofNat? (n : Nat) : Option (Signed m) := ofInt? n
instance : OfNat (Signed n) m := ⟨.ofUnsignedN <| .ofNat m⟩

instance : Coe (Signed ⟨32, by simp⟩) Int := ⟨toInt⟩
instance : Coe (Signed ⟨32, by simp⟩) UInt32 := ⟨Unsigned.toUInt32⟩
instance : Coe (Signed ⟨64, by simp⟩) Int := ⟨toInt⟩
instance : Repr (Signed n) := ⟨reprPrec ∘ toInt⟩

nonrec def toString : Signed n → String := toString ∘ toInt
instance : ToString (Signed n) := ⟨toString⟩


def deq (i j : Signed n) :=
  match decEq i.val j.val with
  | isTrue h  => isTrue (Fin.eq_of_val_eq h)
  | isFalse h => isFalse (Fin.ne_of_val_ne h)

instance : DecidableEq (Signed n) := deq

nonrec def compare (i j : Signed n) : Ordering :=
  let i := i.toInt
  let j := j.toInt
  if i < (Signed.MIN_VALUE : Signed n).toInt then -- i pos
    if j < (Signed.MIN_VALUE : Signed n).toInt
    then compare i j -- j pos
    else .gt -- j neg
  else -- i neg
    if j < (Signed.MIN_VALUE : Signed n).toInt
    then .lt -- j pos
    else compare i j -- j neg

instance : Ord (Signed n)  := ⟨compare⟩
instance : LT  (Signed n)  := ltOfOrd
instance : LE  (Signed n)  := leOfOrd

end Signed

@[inline] def Unsigned8     := Unsigned ⟨8, by simp⟩
@[inline] def Unsigned16    := Unsigned ⟨16, by simp⟩
@[inline] def Unsigned32    := Unsigned ⟨32, by simp⟩
@[inline] def Unsigned64    := Unsigned ⟨64, by simp⟩
@[inline] def Signed8       := Signed ⟨8, by simp⟩
@[inline] def Signed16      := Signed ⟨16, by simp⟩
@[inline] def Signed32      := Signed ⟨32, by simp⟩
@[inline] def Signed64      := Signed ⟨64, by simp⟩

instance : ToString Unsigned32 := ⟨Unsigned.toString⟩

@[inline] def Uninterpreted := Unsigned -- 'iN' in the reference

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

theorem Vec.index (v : Vec α) (i : Fin v.length) : Syntax.Value.Unsigned32 := by
  have h := i.isLt
  have h' := v.maxLen
  have h'' := Nat.lt_trans h h'
  exact ⟨i.val, h''⟩
