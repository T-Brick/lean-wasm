import Std
import Mathlib.Data.List.Basic

theorem Nat.lt_left_add {a b c : Nat} (h₁ : a + b < c) : a < c := by
  induction b with
  | zero => exact h₁
  | succ n ih =>
    have h₂ := Nat.lt_succ_of_lt h₁
    rw [Nat.add_succ] at h₂
    have h₃ := Nat.lt_of_succ_lt_succ h₂
    apply ih h₃

theorem Nat.lt_add_left {a b c : Nat} (h : a + b < c) : b < c := by
  rw [Nat.add_comm] at h
  apply lt_left_add h


theorem Nat.le_trans_lt {a b c : Nat} (h₁ : a ≤ b) (h₂ : b < c) : a < c := by
  cases h₁ with
  | refl   => exact h₂
  | step h => apply Nat.lt_trans (Nat.lt_succ_of_le h) h₂

theorem Nat.two_pow_succ_pred : Nat.succ (Nat.pred (2 ^ n)) = 2 ^ n :=
  Nat.lt_iff_le_and_ne.mp (Nat.pos_pow_of_pos n (Nat.zero_lt_succ 1))
    |>.right
    |>.symm
    |> Nat.succ_pred

theorem Nat.zero_lt_two_pow {n : Nat} : 0 < 2 ^ n := by
  exact Nat.pos_pow_of_pos n ((Nat.zero_lt_succ 1))

theorem List.length_ofFn {f : Fin n → α} : List.length (List.ofFn f) = n := by
  simp [List.ofFn]


def String.concatWith [ToString α] (str : String) (list : List α) : String :=
  String.intercalate str (list.map toString)

@[simp] def Nat.sub_lt_sub {k m n : Nat} (h₁ : n < k) (h₂ : k ≤ m)
    : m - k < m - n := by
  apply Or.elim (Nat.le_iff_lt_or_eq.mp h₂) <;> intro h₂
  . exact Nat.sub_lt_sub_left (Nat.lt_trans h₁ h₂) h₁
  . simp [*] at *; exact h₁
