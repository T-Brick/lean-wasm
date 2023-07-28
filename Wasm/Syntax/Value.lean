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

-- least significant byte is at the end of the list
def Unsigned.toBytes (n : { i // 0 < i })  (v : Unsigned n) : List Byte :=
  if h : n.val ≤ 8
  then UInt8.ofNat (v.toNat % 256) :: []
  else
    let next := ⟨n.val - 8, Nat.zero_lt_sub_of_lt (Nat.lt_of_not_le h)⟩
    UInt8.ofNat (v.toNat % 256) :: toBytes next (Unsigned.ofNat (v.toNat >>> 8))
termination_by toBytes n v => n.val
decreasing_by
  simp_wf
  apply Nat.lt_iff_le_and_ne.mp (Nat.lt_of_not_le h)
    |>.left
    |> Nat.sub_lt_self (Nat.zero_lt_succ 7)

def Unsigned.ofBytes (lst : List Byte) (h : lst.length > 0)
    : Unsigned ⟨8 * lst.length, Nat.mul_lt_mul_of_pos_left h (Nat.zero_lt_succ 7)⟩ :=
  match lst with
  | []       => by contradiction
  | x::[]    => Unsigned.ofNat x.toNat
  | y::x::xs =>
    let res := Unsigned.ofBytes (x::xs) (by
      rw [List.length_cons]; exact Nat.zero_lt_succ (List.length (xs))
    )
    Unsigned.ofNat ((res.toNat <<< 8) + y.toNat)

theorem Unsigned.length_toBytes : List.length (Unsigned.toBytes n v) = (n.val + 7) / 8 := by
  rw [Unsigned.toBytes]
  sorry

-- theorem Unsigned.ofBytes_toBytes (v : Unsigned n) : 



structure Name where
  value : String
  maxLength : value.length < Vec.max_length

end Syntax.Value

theorem Vec.index (v : Vec α) (i : Fin v.length) : Syntax.Value.Unsigned32 := by
  have h := i.isLt
  have h' := v.maxLen
  have h'' := Nat.lt_trans h h'
  exact ⟨i.val, h''⟩
