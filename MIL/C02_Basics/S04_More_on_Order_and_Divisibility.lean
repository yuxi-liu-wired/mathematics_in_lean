import MIL.Common
import Mathlib.Data.Real.Basic

namespace C02S04

section
variable (a b c d : ℝ)

#check (min_le_left a b : min a b ≤ a)
#check (min_le_right a b : min a b ≤ b)
#check (le_min : c ≤ a → c ≤ b → c ≤ min a b)

example : min a b = min b a := by
  apply le_antisymm
  · show min a b ≤ min b a
    apply le_min
    · apply min_le_right
    apply min_le_left
  · show min b a ≤ min a b
    apply le_min
    · apply min_le_right
    apply min_le_left

example : min a b = min b a := by
  have h : ∀ x y : ℝ, min x y ≤ min y x := by
    intro x y
    apply le_min
    apply min_le_right
    apply min_le_left
  apply le_antisymm
  apply h
  apply h

example : min a b = min b a := by
  apply le_antisymm
  repeat
    apply le_min
    apply min_le_right
    apply min_le_left

example : max a b = max b a := by
  apply le_antisymm
  repeat
    apply max_le
    apply le_max_right
    apply le_max_left


example : min (min a b) c = min a (min b c) := by
  apply le_antisymm
  . show min (min a b) c ≤ min a (min b c)
    apply le_min
    . show min (min a b) c ≤ a
      refine min_le_of_left_le ?_
      exact min_le_left a b
    . show min (min a b) c ≤ min b c
      refine min_le_min_right c ?_
      exact min_le_right a b

  . show min a (min b c) ≤ min (min a b) c
    apply le_min
    . show min a (min b c) ≤ min a b
      refine min_le_min_left a ?_
      exact min_le_left b c
    . show min a (min b c) ≤ c
      refine min_le_of_right_le ?_
      exact min_le_right b c


theorem aux : min a b + c ≤ min (a + c) (b + c) := by
  apply le_min
  . show min a b + c ≤ a + c
    simp [min_le_left]
  . show min a b + c ≤ b + c
    simp [min_le_left]

example : min a b + c = min (a + c) (b + c) := by
  have h: min (a + c) (b + c) + -c ≤ min a b := by
    simp [aux]
  apply le_antisymm
  . show min a b + c ≤ min (a + c) (b + c)
    apply aux
  . show min (a + c) (b + c) ≤ min a b + c
    linarith

#check (abs_add : ∀ a b : ℝ, |a + b| ≤ |a| + |b|)

example : |a| - |b| ≤ |a - b| := by
  have h: |a| ≤ |a - b| + |b| :=
    calc |a| = |a - b + b| := by rw [sub_add_cancel]
         _ ≤ |a - b| + |b| := by apply abs_add
  linarith
end

section
variable (w x y z : ℕ)

example (h₀ : x ∣ y) (h₁ : y ∣ z) : x ∣ z :=
  dvd_trans h₀ h₁

example : x ∣ y * x * z := by
  apply dvd_mul_of_dvd_left
  apply dvd_mul_left

example : x ∣ x ^ 2 := by
   apply dvd_mul_left

example (h : x ∣ w) : x ∣ y * (x * z) + x ^ 2 + w ^ 2 := by
  apply dvd_add
  . show x ∣ y * (x * z) + x ^ 2
    apply dvd_add
    . show x ∣ y * (x * z)
      apply dvd_mul_of_dvd_right
      apply dvd_mul_right
    . show x ∣ x ^ 2
      apply dvd_mul_left
  . show x ∣ w ^ 2
    apply dvd_mul_of_dvd_left
    simp [h]
end

section
variable (m n : ℕ)

#check (Nat.gcd_zero_right n : Nat.gcd n 0 = n)
#check (Nat.gcd_zero_left n : Nat.gcd 0 n = n)
#check (Nat.lcm_zero_right n : Nat.lcm n 0 = 0)
#check (Nat.lcm_zero_left n : Nat.lcm 0 n = 0)

example : Nat.gcd m n = Nat.gcd n m := by
  sorry
end
