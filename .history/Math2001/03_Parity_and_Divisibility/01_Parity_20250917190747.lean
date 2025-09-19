/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Library.Basic

math2001_init

open Int


example : Odd (7 : ℤ) := by
  dsimp [Odd]
  use 3
  numbers


example : Odd (-3 : ℤ) := by
  dsimp[Odd]
  use -2
  numbers

example {n : ℤ} (hn : Odd n) : Odd (3 * n + 2) := by
  dsimp [Odd] at *
  obtain ⟨k, hk⟩ := hn
  use 3 * k + 2
  calc
    3 * n + 2 = 3 * (2 * k + 1) + 2 := by rw [hk]
    _ = 2 * (3 * k + 2) + 1 := by ring


example {n : ℤ} (hn : Odd n) : Odd (7 * n - 4) := by
  dsimp[Odd] at *
  obtain ⟨ k, hk⟩ := hn
  use 7*k+1
  calc
    7 * n - 4
      = 7 * (2 * k + 1) - 4 := by rw[hk]
    _ = 2 * (7 * k + 1) + 1 := by ring

example {x y : ℤ} (hx : Odd x) (hy : Odd y) : Odd (x + y + 1) := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  use a + b + 1
  calc
    x + y + 1 = 2 * a + 1 + (2 * b + 1) + 1 := by rw [ha, hb]
    _ = 2 * (a + b + 1) + 1 := by ring


example {x y : ℤ} (hx : Odd x) (hy : Odd y) : Odd (x * y + 2 * y) := by
  dsimp[Odd] at *
  obtain ⟨ k1, hk1⟩ := hx
  obtain ⟨ k2, hk2⟩ := hy
  use 2*k1*k2 + k1 + 3*k2 + 1
  calc
    x * y + 2 * y
      = (2*k1+1)*(2*k2+1) + 2*(2*k2+1) := by rw[hk1,hk2]
    _ = 2*(2*k1*k2 + k1 + 3*k2 + 1) + 1 := by ring

--(2a+1)(2b+1)+2(2b+1) = 4ab+2a+2b+1+4b+2= 4ab + 2a+ 6b+3 = 2(2ab + a + 3b+1)+2
example {m : ℤ} (hm : Odd m) : Even (3 * m - 5) := by
  dsimp[Odd] at *
  dsimp[Even]
  obtain ⟨ k, hk⟩ := hm
  use 3*k - 1
  calc
    3*m-5
      = 3*(2*k+1)-5 := by rw[hk]
    _ = 2*(3*k-1) := by ring

example {n : ℤ} (hn : Even n) : Odd (n ^ 2 + 2 * n - 5) := by
  sorry

example (n : ℤ) : Even (n ^ 2 + n + 4) := by
  obtain hn | hn := Int.even_or_odd n
  · obtain ⟨x, hx⟩ := hn
    use 2 * x ^ 2 + x + 2
    calc
      n ^ 2 + n + 4 = (2 * x) ^ 2 + 2 * x + 4 := by rw [hx]
      _ = 2 * (2 * x ^ 2 + x + 2) := by ring
  · obtain ⟨x, hx⟩ := hn
    use 2 * x ^ 2 + 3 * x + 3
    calc
      n ^ 2 + n + 4 = (2 * x + 1) ^ 2 + (2 * x + 1) + 4 := by rw [hx]
      _ = 2 * (2 * x ^ 2 + 3 * x + 3) := by ring

/-! # Exercises -/


example : Odd (-9 : ℤ) := by
  dsimp[Odd] at *
  use -5
  numbers

example : Even (26 : ℤ) := by
  sorry

example {m n : ℤ} (hm : Odd m) (hn : Even n) : Odd (n + m) := by
  dsimp[Odd, Even] at *
  obtain ⟨ a, ha⟩ := hm
  obtain ⟨ b, hb⟩ := hn
  use a+b
  calc
    m+n = (2*a+1)+(2*b) := by rw[hm,hn]

example {p q : ℤ} (hp : Odd p) (hq : Even q) : Odd (p - q - 4) := by
  sorry

example {a b : ℤ} (ha : Even a) (hb : Odd b) : Even (3 * a + b - 3) := by
  sorry

example {r s : ℤ} (hr : Odd r) (hs : Odd s) : Even (3 * r - 5 * s) := by
  sorry

example {x : ℤ} (hx : Odd x) : Odd (x ^ 3) := by
  dsimp[Odd] at *
  obtain ⟨ k, hk⟩ := hx
  use 4*k^3 + 6*k^2 + 3*k
  rw[hk]
  ring

-- (2k+1)^3 = 8k^3 + 12k^2 + 6k + 1 = 2(4k^3 + 6k^2+3k)+1

example {n : ℤ} (hn : Odd n) : Even (n ^ 2 - 3 * n + 2) := by
  sorry

example {a : ℤ} (ha : Odd a) : Odd (a ^ 2 + 2 * a - 4) := by
  sorry

example {p : ℤ} (hp : Odd p) : Odd (p ^ 2 + 3 * p - 5) := by
  sorry

example {x y : ℤ} (hx : Odd x) (hy : Odd y) : Odd (x * y) := by
  sorry

example (n : ℤ) : Odd (3 * n ^ 2 + 3 * n - 1) := by
  obtain ha | ha := Int.even_or_odd n
  dsimp[Even] at *
  obtain ⟨ k, hk⟩ := ha
  use 6*k^2+3*k-1
  rw[hk]
  ring
  dsimp[Odd]at *
  obtain ⟨ k, hk⟩ := ha
  sorry

--12k^2+6k-1=2(6k^2+3k-1)+1

example (n : ℤ) : ∃ m ≥ n, Odd m := by
  dsimp[Odd] at *
  obtain ha | ha := Int.even_or_odd n
  dsimp[Even] at *
  obtain ⟨ k, hk⟩ := ha
  use n+1
  constructor
  exact le.intro 1 rfl
  use k
  rw[hk]
  dsimp[Odd] at *
  obtain ⟨ k, hk⟩ := ha
  use n
  constructor
  exact Int.le_refl n
  use k
  rw[hk]


example (a b c : ℤ) : Even (a - b) ∨ Even (a + c) ∨ Even (b - c) := by
  obtain h1 | h2 := Int.even_or_odd a
  obtain h3 | h4 := Int.even_or_odd b
  obtain h5 | h6 := Int.even_or_odd c
  left
  dsimp[Even] at *
  obtain ⟨ k1, hk1⟩ := h1
  obtain ⟨ k2, hk2⟩ := h3
  use k1 - k2
  rw[hk1,hk2]
  ring
  sorry
  sorry
  sorry



--
