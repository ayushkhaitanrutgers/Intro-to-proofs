/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Theory.ModEq.Defs

math2001_init

namespace Int


example : ∃! a : ℝ, 3 * a + 1 = 7 := by
  use 2
  dsimp
  constructor
  · numbers
  intro y hy
  calc
    y = (3 * y + 1 - 1) / 3 := by ring
    _ = (7 - 1) / 3 := by rw [hy]
    _ = 2 := by numbers


example : ∃! x : ℚ, ∀ a, a ≥ 1 → a ≤ 3 → (a - x) ^ 2 ≤ 1 := by
  use 2
  dsimp
  constructor
  intro a ha hb
  have hc : -1 ≤ (a-2) := by sorry
  have hd : (a-2) ≤ 1 := by sorry
  have he: (a-2)^2 ≤ 1^2 := sq_le_sq' hc hd
  calc
    (a-2)^2 ≤ 1^2 := by rel[he]
    _ = 1 := by ring
  intro h ha


example {x : ℚ} (hx : ∃! a : ℚ, a ^ 2 = x) : x = 0 := by
  obtain ⟨a, ha1, ha2⟩ := hx
  have h1 : -a = a
  · apply ha2
    calc
      (-a) ^ 2 = a ^ 2 := by ring
      _ = x := ha1
  have h2 :=
    calc
      a = (a - -a) / 2 := by ring
      _ = (a - a) / 2 := by rw [h1]
      _ = 0 := by ring
  calc
    x = a ^ 2 := by rw [ha1]
    _ = 0 ^ 2 := by rw [h2]
    _ = 0 := by ring


example : ∃! r : ℤ, 0 ≤ r ∧ r < 5 ∧ 14 ≡ r [ZMOD 5] := by
  use 4
  dsimp
  constructor
  · constructor
    · numbers
    constructor
    · numbers
    use 2
    numbers
  intro r hr
  obtain ⟨hr1, hr2, q, hr3⟩ := hr
  have :=
    calc
      5 * 1 < 14 - r := by addarith [hr2]
      _ = 5 * q := by rw [hr3]
  cancel 5 at this
  have :=
    calc
      5 * q = 14 - r := by rw [hr3]
      _ < 5 * 3 := by addarith [hr1]
  cancel 5 at this
  interval_cases q
  addarith [hr3]

/-! # Exercises -/


example : ∃! x : ℚ, 4 * x - 3 = 9 := by
  use 3
  dsimp
  constructor
  numbers
  intro y hy
  calc
    y = ((4*y-3) + 3)/4 := by ring
    _ = (9+3)/4 := by rw[hy]
    _ = 12/4 := by numbers
    _ = 3 := by numbers

example : ∃! n : ℕ, ∀ a, n ≤ a := by
  use 0
  dsimp
  constructor
  exact fun a ↦ Nat.zero_le a
  intro a h
  exact Nat.le_zero.mp (h 0)


example : ∃! r : ℤ, 0 ≤ r ∧ r < 3 ∧ 11 ≡ r [ZMOD 3] := by
  use 2
  dsimp
  constructor
  constructor
  numbers
  constructor
  numbers
  dsimp[Int.ModEq] at *
  dsimp[(· ∣ ·)]
  use 3
  numbers
  intro a ha
  obtain ⟨ hb, hc, hd⟩ := ha
  interval_cases a
  exfalso
  dsimp[Int.ModEq] at *
  dsimp[(· ∣ ·)] at *
  obtain ⟨ e, he⟩ := hd
  have h : 11 - 0 ≠ 3*e := by sorry
  exact h he

  exfalso
  dsimp[Int.ModEq] at *
  dsimp[(· ∣ ·)] at *
  obtain ⟨ e, he⟩ := hd
  have h : 11 - 1 ≠ 3*e := by sorry
  exact h he

  rfl
