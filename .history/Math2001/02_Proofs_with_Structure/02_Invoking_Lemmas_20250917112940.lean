/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

example {x : ℚ} (hx : 3 * x = 2) : x ≠ 1 := by
  apply ne_of_lt
  calc
    x = 3 * x / 3 := by ring
    _ = 2 / 3 := by rw [hx]
    _ < 1 := by numbers

example {y : ℝ} : y ^ 2 + 1 ≠ 0 := by sorry


example {a b : ℝ} (h1 : a ^ 2 + b ^ 2 = 0) : a ^ 2 = 0 := by
  apply le_antisymm
  calc
    a ^ 2 ≤ a ^ 2 + b ^ 2 := by extra
    _ = 0 := h1
  extra


/-! # Exercises -/


example {m : ℤ} (hm : m + 1 = 5) : 3 * m ≠ 6 := by
  sorry

example {s : ℚ} (h1 : 3 * s ≤ -6) (h2 : 2 * s ≥ -4) : s = -2 := by
  sorry

example {x : ℝ} (h1 : x^2-3*x+2=0) : x = 1 ∨ x = 2:= by
  have h2: (x-1)*(x-2) = 0 :=
    calc
      (x-1)*(x-2) = x^2 - 3*x+2 := by ring
      _ = 0 := by rw[h1]
  have h3: (x-1) = 0 ∨ (x-2) = 0 := eq_zero_or_eq_zero_of_mul_eq_zero h2
  left
  obtain h4 | h5 := h3
  calc
    x = 1 := by addarith[h4]
