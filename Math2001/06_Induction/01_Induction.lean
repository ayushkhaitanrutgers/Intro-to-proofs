/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.ModEq

math2001_init

namespace Nat


example (n : ℕ) : 2 ^ n ≥ n + 1 := by
  simple_induction n with k IH --IH is the induction hypothesis
  · -- base case
    numbers
  · -- inductive step
    calc 2 ^ (k + 1) = 2 * 2 ^ k := by ring
      _ ≥ 2 * (k + 1) := by rel [IH]
      _ = (k + 1 + 1) + k := by ring
      _ ≥ k + 1 + 1 := by extra


example (n : ℕ) : Even n ∨ Odd n := by
  simple_induction n with k h
  left
  dsimp[Even] at *
  use 0
  numbers
  obtain h1 | h2 := h
  right
  dsimp[Even] at *
  obtain ⟨ k1, h1⟩ := h1
  dsimp[Odd] at *
  use k1
  rw[h1]
  dsimp[Odd,Even] at *
  obtain ⟨ k1, h1⟩ := h2
  left
  use k1+1
  rw[h1]
  ring

example {a b d : ℤ} (h : a ≡ b [ZMOD d]) (n : ℕ) : a ^ n ≡ b ^ n [ZMOD d] := by
  dsimp[Int.ModEq] at *
  simple_induction n with k h1
  use 0
  ring
  obtain ⟨ l, hl⟩ := h1
  obtain ⟨ p,hp⟩ := h
  use b * l + a^k * p
  --a^{k+1}-b^{k+1}=(a^k-b^k)(a+b)-ba^k+ab^k = (a^k-b^k)(a+b)+a(b^k-a^k)+a^{k}(a-b)
  calc
    a^(k+1)-b^(k+1)
      = (a^k-b^k) * b + a^k * (a-b) := by ring
    _ = (d * l) * b + a ^ k * (d * p) := by rw[hl,hp]
    _ = d * (b * l + a^k * p) := by ring





example (n : ℕ) : 4 ^ n ≡ 1 [ZMOD 15] ∨ 4 ^ n ≡ 4 [ZMOD 15] := by
  simple_induction n with k IH
  · -- base case
    left
    numbers
  · -- inductive step
    obtain hk | hk := IH
    · right
      calc (4:ℤ) ^ (k + 1) = 4 * 4 ^ k := by ring
        _ ≡ 4 * 1 [ZMOD 15] := by rel [hk]
        _ = 4 := by numbers
    · left
      calc (4:ℤ) ^ (k + 1) = 4 * 4 ^ k := by ring
        _ ≡ 4 * 4 [ZMOD 15] := by rel [hk]
        _ = 15 * 1 + 1 := by numbers
        _ ≡ 1 [ZMOD 15] := by extra


example {n : ℕ} (hn : 2 ≤ n) : (3:ℤ) ^ n ≥ 2 ^ n + 5 := by
  induction_from_starting_point n, hn with k hk IH
  · -- base case
    numbers
  · -- inductive step
    calc (3:ℤ) ^ (k + 1) = 2 * 3 ^ k + 3 ^ k := by ring
      _ ≥ 2 * (2 ^ k + 5) + 3 ^ k := by rel [IH]
      _ = 2 ^ (k + 1) + 5 + (5 + 3 ^ k) := by ring
      _ ≥ 2 ^ (k + 1) + 5 := by extra


example : forall_sufficiently_large n : ℕ, 2 ^ n ≥ n ^ 2 := by
  dsimp
  use 4
  intro n hn
  induction_from_starting_point n, hn with k hk IH
  · -- base case
    sorry
  · -- inductive step
    sorry

example : forall_sufficiently_large n : ℕ, 2 ^ n ≥ n ^ 2 := by
  dsimp
  use 4
  intro n hn
  induction_from_starting_point n, hn with k hk IH
  numbers
  have h1 : k^2 ≥ 2*k+1 := by
    sorry
  calc
    2^(k+1) = 2^k * 2 := by ring
    _ ≥ k^2 * 2 := by rel[IH]
    _ = k^2 + k^2 := by ring
    _ ≥ k^2 + (2*k + 1) := by rel[h1]
    _ = (k+1)^2 := by ring


/-! # Exercises -/


example (n : ℕ) : 3 ^ n ≥ n ^ 2 + n + 1 := by
  simple_induction n with k h
  numbers
  calc
    3^(k+1)
      = 3^k * 3 := by ring
    _ ≥ (k^2+k+1)*3 := by rel[h]
    _ = (k^2 + 2 * k + 1) + (k + 1) + 1 + 2*k^2 := by ring
    _ ≥ (k^2 + 2*k + 1) + (k+1) + 1 := by extra
    _ = (k+1)^2 + (k+1) + 1 := by ring


example {a : ℝ} (ha : -1 ≤ a) (n : ℕ) : (1 + a) ^ n ≥ 1 + n * a := by
  simple_induction n with k hk
  calc
    (1+a)^0 = 1 := by ring
    _ ≥ 1 := by numbers
    _ = 1 + 0 * a := by ring
  -- (1+a)^{k+1} = (1+a)^k*(1+a) ≥ (1+k*a)*(1+a)≥ 1+k*a + a
  have : 1 + a ≥ 0 := by addarith[ha]
  calc
    (1+a)^(k+1) = (1+a)^k*(1+a) := by ring
      _ ≥ (1 + ↑k * a) * (1+a) := by rel[hk]
      _ = (1 + ↑k * a) + a + ↑k * a^2 := by ring
      _ = (1 + (↑k + 1) * a ) + ↑k * a^2 := by ring
      _ ≥ (1 + (↑k + 1) * a ) := by extra

example (n : ℕ) : 5 ^ n ≡ 1 [ZMOD 8] ∨ 5 ^ n ≡ 5 [ZMOD 8] := by
  sorry

example (n : ℕ) : 6 ^ n ≡ 1 [ZMOD 7] ∨ 6 ^ n ≡ 6 [ZMOD 7] := by
  sorry

example (n : ℕ) :
    4 ^ n ≡ 1 [ZMOD 7] ∨ 4 ^ n ≡ 2 [ZMOD 7] ∨ 4 ^ n ≡ 4 [ZMOD 7] := by
  sorry

example : forall_sufficiently_large n : ℕ, (3:ℤ) ^ n ≥ 2 ^ n + 100 := by
  dsimp
  sorry

example : forall_sufficiently_large n : ℕ, 2 ^ n ≥ n ^ 2 + 4 := by
  dsimp
  use 5
  intro x hx
  induction_from_starting_point x, hx with k hk IH
  numbers
  have hc : (2 * k - 2 * k) = 0 := by exact Nat.sub_self (2 * k)
  calc
    2^(k+1) = 2^k*2 := by ring
    _ ≥ (k^2+4) * 2 := by rel[IH]
    _ = 2*k^2 + 8 := by ring
    _ = (k^2 + 1 + 4) + (k^2 + 3) + 0 := by ring
    _ = (k^2 + 1 + 4) + (k^2 + 3) + (2 * k - 2 * k) := by rw[hc]
    _ = ((k^2+2*k+1) + 4) + (k^2-2*k + 1) + 2 := by sorry
    _ = ((k+1)^2 + 4) + (k-1)^2 + 2 := by sorry
    _ ≥ (k+1)^2 + 4 + 2 := by extra
    _ ≥ (k+1)^2 + 4 := by extra



example : forall_sufficiently_large n : ℕ, 2 ^ n ≥ n ^ 3 := by
  dsimp
  sorry

theorem Odd.pow {a : ℕ} (ha : Odd a) (n : ℕ) : Odd (a ^ n) := by
  dsimp[Odd] at *
  obtain ⟨ k, hk⟩ := ha
  simple_induction n with p IH
  use 0
  ring
  obtain ⟨ l, hl⟩ := IH
  --4kl+2k+2l+1=2(2kl+k+l)+1
  use 2*k*l+k+l
  calc
    a^(p+1)=a^p*a := by ring
    _ = (2*l+1)*(2*k+1) := by rw[hl,hk]
    _ = 2 * (2*k * l + k + l) + 1 := by ring

theorem Nat.even_of_pow_even {a n : ℕ} (ha : Even (a ^ n)) : Even a := by
  sorry
