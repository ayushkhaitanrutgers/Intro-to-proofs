/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init


example {x y : ℤ} (h : 2 * x - y = 4 ∧ y - x + 1 = 2) : x = 5 := by
  obtain ⟨h1, h2⟩ := h
  calc
    x = 2 * x - y + (y - x + 1) - 1 := by ring
    _ = 4 + 2 - 1 := by rw [h1, h2]
    _ = 5 := by ring


example {p : ℚ} (hp : p ^ 2 ≤ 8) : p ≥ -5 := by
  have hp' : -3 ≤ p ∧ p ≤ 3 := by
    apply abs_le_of_sq_le_sq' --this changes the goal
    calc
      p ^ 2 ≤ 9 := by addarith [hp]
      _ = 3 ^ 2 := by numbers
    numbers
  obtain ⟨ h1, h2⟩ := hp'
  addarith[h1]



example {a b : ℝ} (h1 : a - 5 * b = 4) (h2 : b + 2 = 3) : a = 9 ∧ b = 1 := by
  have h3 : b = 1 := by
    calc
      b
        = (b+2)-2 := by ring
      _ = 3 -2 := by rw[h2]
      _ = 1 := by numbers
  have h4 : a = 9 := by
    calc
      a = a - 5*b + 5*b := by ring
      _ = 4 + 5*1 := by rw[h1,h3]
      _ = 9 := by numbers
  constructor
  apply h4
  apply h3


example {a b : ℝ} (h1 : a - 5 * b = 4) (h2 : b + 2 = 3) : a = 9 ∧ b = 1 := by
  have hb : b = 1 := by addarith [h2]
  constructor
  · calc
      a = 4 + 5 * b := by addarith [h1]
      _ = 4 + 5 * 1 := by rw [hb]
      _ = 9 := by ring
  · apply hb


example {a b : ℝ} (h1 : a ^ 2 + b ^ 2 = 0) : a = 0 ∧ b = 0 := by
  have h2 : a ^ 2 = 0 := by
    apply le_antisymm
    calc
      a^2
        ≤ a^2 + b^2 := by extra
      _ = 0 := by rw[h1]
    exact sq_nonneg a
  constructor
  exact pow_eq_zero h2
  have h3 : b^2 =0 := by
    apply le_antisymm
    calc
      b^2
        ≤ a^2 + b^2 := by extra
      _ = 0 := by rw[h1]
    exact sq_nonneg b
  exact pow_eq_zero h3





/-! # Exercises -/


example {a b : ℚ} (H : a ≤ 1 ∧ a + b ≤ 3) : 2 * a + b ≤ 4 := by
  obtain ⟨ h1, h2⟩ := H
  calc
    2*a + b
      = a + (a + b):= by ring
    _ ≤ 1 + 3 := by rel[h1,h2]
    _ = 4 := by numbers

example {r s : ℝ} (H : r + s ≤ 1 ∧ r - s ≤ 5) : 2 * r ≤ 6 := by
  sorry

example {m n : ℤ} (H : n ≤ 8 ∧ m + 5 ≤ n) : m ≤ 3 := by
  obtain ⟨ h1, h2⟩ := H
  calc
    m
      = (m+5)-5 := by ring
    _ ≤ n-5 := by 

example {p : ℤ} (hp : p + 2 ≥ 9) : p ^ 2 ≥ 49 ∧ 7 ≤ p := by
  have h1 : p ≥ 7 := by
    addarith[hp]
  constructor
  calc
    p^2 = p * p := by ring
    _ ≥ 7 * 7 := by rel[h1]
    _ = 49 := by numbers
  rel[h1]

example {a : ℚ} (h : a - 1 ≥ 5) : a ≥ 6 ∧ 3 * a ≥ 10 := by
  sorry

example {x y : ℚ} (h : x + y = 5 ∧ x + 2 * y = 7) : x = 3 ∧ y = 2 := by
  obtain ⟨ h1, h2⟩ := h
  constructor
  calc
    x
      = 2*(x+y)-(x+2*y):= by ring
    _ = 2*5-7 := by rw[h1,h2]
    _ = 3 := by ring
  calc
    y
      = (x+2*y)-(x+y) := by ring
    _ = 7-5 := by rw[h1,h2]
    _ = 2 := by numbers

example {a b : ℝ} (h1 : a * b = a) (h2 : a * b = b) :
    a = 0 ∧ b = 0 ∨ a = 1 ∧ b = 1 := by
  have h3 : a*(b-1)=0 := by
    calc
      a*(b-1)
        = a*b -a := by ring
      _ = a - a := by rw[h1]
      _ = 0 := by ring
  rw[mul_eq_zero] at h3
  obtain ha | hb := h3
  have h4 : (a-1)*b=0 := by
    calc
      (a-1)*b = a*b -b := by ring
      _ = b - b := by rw[h2]
      _ = 0 := by ring
  rw[mul_eq_zero] at h4
  obtain h5 | h6 := h4
  left
  constructor
  apply ha
  have : b = 0 := by
    calc
      b
        = a * b := by rw[h2]
      _ = 0*b := by rw[ha]
      _ = 0 := by ring
  apply this
  left
  constructor
  apply ha
  apply h6
  have : b = 1 := by
    calc
      b = (b-1)+1 := by ring
      _ = 0+1 := by rw[hb]
      _ = 1 := by numbers
  have hc: a = 1 := by
    calc
      a
        = a*b := by rw[h1]
      _ = b := by rw[h2]
      _ = 1 := by rw[this]
  right
  constructor
  apply hc
  apply this
