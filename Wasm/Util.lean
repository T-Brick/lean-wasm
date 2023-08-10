import Std

namespace Wasm

def String.concatWith [ToString α] (c : String) : List α → String
  | .nil => ""
  | .cons x .nil => toString x
  | .cons x (.cons y ys) =>
    String.append (String.append (toString x) c) (concatWith c (.cons y ys))


def Vec.max_length : Nat := Nat.pow 2 32

structure Vec (α : Type u) where
  list : List α
  maxLen : list.length < Vec.max_length

namespace Vec

nonrec def toString [ToString α] (v : Vec α) : String :=
  String.concatWith " " v.list

def nil : Vec α := ⟨[], by simp⟩

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

def map (f : α → β) (v : Vec α) : Vec β := ⟨v.list.map f, by
    rw [List.length_map]
    exact v.maxLen
  ⟩

@[inline] def length (v : Vec α) := v.list.length
@[inline] def get (v : Vec α) (i : Fin v.length) := v.list.get i
@[inline] def set (v : Vec α) (i : Fin v.length) (x : α) : Vec α :=
  ⟨v.list.set i x, by rw [List.length_set]; exact v.maxLen⟩

end Vec

theorem lt_left_add {a b c : Nat} (h₁ : a + b < c) : a < c := by
  induction b with
  | zero => exact h₁
  | succ n ih =>
    have h₂ := Nat.lt_succ_of_lt h₁
    rw [Nat.add_succ] at h₂
    have h₃ := Nat.lt_of_succ_lt_succ h₂
    apply ih h₃

theorem lt_add_left {a b c : Nat} (h : a + b < c) : b < c := by
  rw [Nat.add_comm] at h
  apply lt_left_add h


theorem le_trans_lt {a b c : Nat} (h₁ : a ≤ b) (h₂ : b < c) : a < c := by
  cases h₁ with
  | refl   => exact h₂
  | step h => apply Nat.lt_trans (Nat.lt_succ_of_le h) h₂

theorem two_pow_succ_pred : Nat.succ (Nat.pred (2 ^ n)) = 2 ^ n :=
  Nat.lt_iff_le_and_ne.mp (Nat.pos_pow_of_pos n (Nat.zero_lt_succ 1))
    |>.right
    |>.symm
    |> Nat.succ_pred

theorem zero_lt_two_pow {n : Nat} : 0 < 2 ^ n := by
  exact Nat.pos_pow_of_pos n ((Nat.zero_lt_succ 1))
