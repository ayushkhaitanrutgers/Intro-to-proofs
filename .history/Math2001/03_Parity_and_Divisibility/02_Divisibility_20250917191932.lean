/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Tactic.GCongr
import Library.Basic

math2001_init


example : (11 : ℕ) ∣ 88 := by
  dsimp [(· ∣ ·)]
  use 8
  numbers


example : (-2 : ℤ) ∣ 6 := by
  dsimp[(· ∣ ·)]
  use -3
  numbers

example {a b : ℤ} (hab : a ∣ b) : a ∣ b ^ 2 + 2 * b := by
  obtain ⟨k, hk⟩ := hab
  use k * (a * k + 2)
  calc
    b ^ 2 + 2 * b = (a * k) ^ 2 + 2 * (a * k) := by rw [hk]
    _ = a * (k * (a * k + 2)) := by ring


example {a b c : ℕ} (hab : a ∣ b) (hbc : b ^ 2 ∣ c) : a ^ 2 ∣ c := by
  obtain ⟨ k1, hk1⟩ := hab
  obtain ⟨ k2, hk2⟩ := hbc
  use k1^2 * k2
  calc
    c = b^2 * k2 := by rw[hk2]
    _ = (a*k1)^2*k2 := by rw[hk1]
    _ = a^2 * (k1^2 * k2) := by ring


example {x y z : ℕ} (h : x * y ∣ z) : x ∣ z := by
  obtain ⟨ k, hk⟩ := h
  use y*k
  rw[hk]
  ring

example : ¬(5 : ℤ) ∣ 12 := by
  apply Int.not_dvd_of_exists_lt_and_lt
  use 2
  constructor
  · numbers -- show `5 * 2 < 12`
  · numbers -- show `12 < 5 * (2 + 1)`


example {a b : ℕ} (hb : 0 < b) (hab : a ∣ b) : a ≤ b := by
  obtain ⟨k, hk⟩ := hab
  have H1 :=
    calc
      0 < b := hb
      _ = a * k := hk
  cancel a at H1
  have H : 1 ≤ k := H1
  calc
    a = a * 1 := by ring
    _ ≤ a * k := by rel [H]
    _ = b := by rw [hk]


example {a b : ℕ} (hab : a ∣ b) (hb : 0 < b) : 0 < a := by
  obtain ⟨ k, hk⟩ := hab
  have : 0 < a*k := by
    calc
      0 < b := hb
      _ = a * k := hk
  cancel k at this

/-! # Exercises -/


example (t : ℤ) : t ∣ 0 := by
  dsimp[(· ∣ ·)]
  use 0
  ring

example : ¬(3 : ℤ) ∣ -10 := by
  apply Int.not_dvd_of_exists_lt_and_lt
  use -4
  constructor
  numbers
  numbers


example {x y : ℤ} (h : x ∣ y) : x ∣ 3 * y - 4 * y ^ 2 := by
  sorry

example {m n : ℤ} (h : m ∣ n) : m ∣ 2 * n ^ 3 + n := by
  sorry

example {a b : ℤ} (hab : a ∣ b) : a ∣ 2 * b ^ 3 - b ^ 2 + 3 * b := by
  sorry

example {k l m : ℤ} (h1 : k ∣ l) (h2 : l ^ 3 ∣ m) : k ^ 3 ∣ m := by
  sorry

example {p q r : ℤ} (hpq : p ^ 3 ∣ q) (hqr : q ^ 2 ∣ r) : p ^ 6 ∣ r := by
  dsimp [(· ∣ ·)] at *
  obtain ⟨ a, ha⟩ := hpq
  obtain ⟨ h, hb⟩ := hqr
  use a^2*h
  calc
    r
      = q^2*h := by rw[hb]
    _ = ()
example : ∃ n : ℕ, 0 < n ∧ 9 ∣ 2 ^ n - 1 := by
  use 6
  constructor
  exact Nat.succ_pos 5
  dsimp[(· ∣ · )]
  use 7
  numbers

example : ∃ a b : ℤ, 0 < b ∧ b < a ∧ a - b ∣ a + b := by
  use 3
  use 2
  constructor
  exact Int.pos_of_sign_eq_one rfl
  constructor
  exact (cmp_eq_gt_iff 3 2).mp rfl
  dsimp[(· ∣ ·)]
  use 5
  numbers
