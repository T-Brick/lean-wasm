import Std
import Mathlib.Data.List.Basic
import Wasm.AuxDefs

namespace Wasm

def Vec.max_length : Nat := Nat.pow 2 32

structure Vec (α : Type u) where
  list : List α
  maxLen : list.length < Vec.max_length
deriving DecidableEq

namespace Vec

nonrec def toString [ToString α] (v : Vec α) : String :=
  String.intercalate " " (v.list.map toString)

def nil : Vec α := ⟨[], by simp⟩
def single : α → Vec α := (⟨[·], by simp⟩)

instance : Coe (Vec α) (List α)          := ⟨fun v => v.list⟩
instance : Inhabited (Vec α)             := ⟨nil⟩
instance [ToString α] : ToString (Vec α) := ⟨toString⟩
instance [Repr α] : Repr (Vec α)         := ⟨fun v => reprPrec v.list⟩

def length_cons (x : α)
                (xs : Vec α)
                (h : xs.list.length + 1 < Vec.max_length)
                : (res : Vec α) ×' (res.list.length = xs.list.length + 1) :=
  let res := ⟨x :: xs.list, h⟩
  ⟨res, by rw [List.length_cons]⟩

def cons (x : α) (xs : Vec α) (h : xs.list.length + 1 < Vec.max_length) : Vec α :=
  Vec.length_cons x xs h |>.fst

def length_append (xs : Vec α) (ys : Vec α)
           (h : xs.list.length + ys.list.length < Vec.max_length)
           : (res : Vec α )
             ×' (res.list.length = xs.list.length + ys.list.length) :=
  let res := ⟨xs.list ++ ys.list, by rw [List.length_append]; exact h⟩
  ⟨res, by rw [List.length_append]⟩

def append (xs : Vec α) (ys : Vec α)
           (h : xs.list.length + ys.list.length < Vec.max_length)
           : Vec α :=
  length_append xs ys h |>.fst

def map (f : α → β) (v : Vec α) : Vec β :=
  ⟨v.list.map f, by
    rw [List.length_map]
    exact v.maxLen
  ⟩

def reverse (v : Vec α) : Vec α := ⟨v.list.reverse, by simp [v.maxLen]⟩

@[inline] def length (v : Vec α) := v.list.length
@[inline] def get (v : Vec α) (i : Fin v.length) := v.list.get i
@[inline] def set (v : Vec α) (i : Fin v.length) (x : α) : Vec α :=
  ⟨v.list.set i x, by rw [List.length_set]; exact v.maxLen⟩

end Vec
