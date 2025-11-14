import Wasm.AuxDefs

namespace Wasm

def Vec.max_length : Nat := Nat.pow 2 32

abbrev Vec (α : Type u) := {list : List α // list.length < Vec.max_length}
instance [DecidableEq α] : DecidableEq (Vec α) := inferInstance

namespace Vec

@[reducible] def list : Vec α → List α := (·.val)
@[reducible] def maxLen (self : Vec α) : List.length self.list < Vec.max_length :=
  self.property

nonrec def toString [ToString α] (v : Vec α) : String :=
  String.intercalate " " (v.list.map toString)

def nil : Vec α := ⟨[], by simp [max_length]⟩
def single : α → Vec α := (⟨[·], by simp [max_length]⟩)

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
def mapM {m : Type u → Type v} [Monad m] {α : Type w} {β : Type u}
    (f : α → m β) (v : Vec α) : m (Vec β) := do
  return ⟨ ← v.list.mapM f
         , sorry
         ⟩

def reverse (v : Vec α) : Vec α := ⟨v.list.reverse, by simp [v.maxLen]⟩

@[inline, simp] def length (v : Vec α) := v.list.length
@[inline, simp] def get (v : Vec α) (i : Fin v.length) := v.list.get i
@[inline, simp] def set (v : Vec α) (i : Fin v.length) (x : α) : Vec α :=
  ⟨v.list.set i x, by rw [List.length_set]; exact v.maxLen⟩

@[simp] def tl? (v : Vec α) : Option (Vec α) :=
  match h : v.list with
  | [] => .none
  | x :: xs =>
    .some ⟨xs, by
      have := v.maxLen
      rw [h, List.length, Nat.add_comm] at this
      linarith
    ⟩

@[simp] def tl (v : Vec α) (len : v.length > 0) : Vec α :=
  match h : v.list with
  | [] => by simp [length, h] at len
  | x :: xs =>
    ⟨xs, by
      have := v.maxLen
      rw [h, List.length, Nat.add_comm] at this
      linarith
    ⟩

theorem length_lt_tl_length {v : Vec α} {len : v.length > 0}
    : v.length > (tl v len).length := by
  sorry

def join (v : Vec (Vec α)) : Option (Vec α) :=
  match h₁ : v.list with
  | []      => .some Vec.nil
  | x :: xs => do
    have len : v.length > 0 := by simp [length, h₁]
    have := length_lt_tl_length (v := v) (len := len)

    let res ← Vec.join (v.tl len)
    if h₂ : res.length + x.length < Vec.max_length then
      return Vec.append x res (by simp [Nat.add_comm] at h₂; exact h₂)
    else none
termination_by v.length

@[inline] def dropLast (v : Vec α) : Vec α :=
  ⟨ v.list.dropLast, by
    have := v.property
    simp [Vec.list, Vec.max_length] at *
    cases h : List.length v.val <;> (simp [h] at *; try linarith)
  ⟩

@[inline] def getLastD (v : Vec α) : α → α := v.list.getLastD

end Vec
