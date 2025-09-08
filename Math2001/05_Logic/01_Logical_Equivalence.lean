/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Library.Basic

math2001_init
set_option pp.funBinderTypes true


example {P Q : Prop} (h1 : P ∨ Q) (h2 : ¬ Q) : P := by
  obtain hP | hQ := h1
  · apply hP
  · contradiction


example (P Q : Prop) : P → (P ∨ ¬ Q) := by
  intro hP
  left
  apply hP


#truth_table ¬(P ∧ ¬ Q)


example (P : Prop) : (P ∨ P) ↔ P := by
  constructor
  · intro h
    obtain h1 | h2 := h
    · apply h1
    · apply h2
  · intro h
    left
    apply h



example (P Q R : Prop) : (P ∧ (Q ∨ R)) ↔ ((P ∧ Q) ∨ (P ∧ R)) := by
  constructor
  · intro h
    obtain ⟨h1, h2 | h2⟩ := h
    · left
      constructor
      · apply h1
      · apply h2
    · right
      constructor
      · apply h1
      · apply h2
  · intro h
    obtain h1 | h2 := h
    constructor
    obtain ⟨ hp, hq⟩ := h1
    apply hp
    obtain ⟨hp, hq⟩ := h1
    left
    apply hq
    constructor
    obtain ⟨ h1, h2⟩ := h2
    apply h1
    obtain ⟨ h1, h2⟩ := h2
    right
    apply h2

#truth_table P ∧ (Q ∨ R)
#truth_table (P ∧ Q) ∨ (P ∧ R)


example {P Q : α → Prop} (h1 : ∀ x : α, P x) (h2 : ∀ x : α, Q x) :
    ∀ x : α, P x ∧ Q x := by
  intro x
  constructor
  · apply h1
  · apply h2



example {P : α → β → Prop} (h : ∃ x : α, ∀ y : β, P x y) :
    ∀ y : β, ∃ x : α, P x y := by
  obtain ⟨x, hx⟩ := h
  intro y
  use x
  apply hx

example {P : α → β → Prop} (h : ∃ x : α, ∀ y : β, P x y) :
    ∀ y : β, ∃ x : α, P x y := by
    obtain ⟨ x, hx⟩ := h
    intro y
    use x
    apply hx




example (P : α → Prop) : ¬ (∃ x, P x) ↔ ∀ x, ¬ P x := by
  constructor
  · intro h a ha
    have : ∃ x, P x
    · use a
      apply ha
    contradiction
  · intro h h'
    obtain ⟨x, hx⟩ := h'
    have : ¬ P x := h x
    contradiction


/-! # Exercises -/


example {P Q : Prop} (h : P ∧ Q) : P ∨ Q := by
  obtain ⟨h1, h2⟩ := h
  left
  apply h1

example {P Q R : Prop} (h1 : P → Q) (h2 : P → R) (h3 : P) : Q ∧ R := by
  constructor
  · exact h1 h3
  · exact h2 h3

example (P : Prop) : ¬(P ∧ ¬ P) := by
  intro h
  obtain ⟨ h1, h2⟩ := h
  contradiction

example {P Q : Prop} (h1 : P ↔ ¬ Q) (h2 : Q) : ¬ P := by
  obtain ⟨ ha, hb ⟩ := h1
  intro h
  apply ha h
  apply h2

example {P Q : Prop} (h1 : P ∨ Q) (h2 : Q → P) : P := by
  obtain ha | hb := h1
  apply ha
  apply h2 hb


example {P Q R : Prop} (h : P ↔ Q) : (P ∧ R) ↔ (Q ∧ R) := by
  obtain ⟨ ha, hb ⟩ := h
  constructor
  intro h
  obtain ⟨ h1, h2⟩ := h
  constructor
  apply ha h1
  apply h2
  intro h
  obtain ⟨ h1, h2⟩ := h
  constructor
  apply hb h1
  apply h2



example (P : Prop) : (P ∧ P) ↔ P := by
  constructor
  intro h
  obtain ⟨ h1, h2⟩ := h
  apply h1
  intro h
  constructor
  apply h
  apply h

example (P Q : Prop) : (P ∨ Q) ↔ (Q ∨ P) := by
  constructor
  intro h
  obtain h1 | h2 := h
  right
  apply h1
  left
  apply h2
  intro h
  obtain h1 | h2 := h
  right
  apply h1
  left
  apply h2

example (P Q : Prop) : ¬(P ∨ Q) ↔ (¬P ∧ ¬Q) := by
  constructor
  intro h
  constructor
  intro h1
  have : P ∨ Q := by
    left
    apply h1
  contradiction
  intro h1
  have : P ∨ Q := by
    right
    apply h1
  contradiction
  intro h
  intro h1
  obtain ⟨ ha, hb ⟩ := h
  obtain hc | hd := h1
  contradiction
  contradiction

example {P Q : α → Prop} (h1 : ∀ x, P x → Q x) (h2 : ∀ x, P x) : ∀ x, Q x := by
  intro x
  have ha : P x := by apply h2
  have hb : P x → Q x := by apply h1
  apply hb ha


example {P Q : α → Prop} (h : ∀ x, P x ↔ Q x) : (∃ x, P x) ↔ (∃ x, Q x) := by
  constructor
  intro h1
  obtain ⟨ x, hx⟩ := h1
  have ha : P x ↔ Q x := by apply h
  obtain ⟨ hc, hd⟩ := ha
  use x
  apply hc hx
  intro h1
  obtain ⟨ x, hx⟩ := h1
  obtain ⟨ hc, hd⟩ := h x
  use x
  apply hd hx



example (P : α → β → Prop) : (∃ x y, P x y) ↔ ∃ y x, P x y := by
  constructor
  intro h
  obtain ⟨ x, y, h⟩ := h
  use y
  use x
  apply h
  intro h
  obtain ⟨ y, x, hx⟩ := h
  use x
  use y
  apply hx

  /-

-/
example (P : α → β → Prop) : (∀ x y, P x y) ↔ ∀ y x, P x y := by
  constructor
  intro h
  intro y x
  have : P x y := by
    apply h
  apply this
  intro h
  intro x y
  apply h

example (P : α → Prop) (Q : Prop) : ((∃ x, P x) ∧ Q) ↔ ∃ x, (P x ∧ Q) := by
  constructor
  intro h
  obtain ⟨ h1, h2 ⟩ := h
  obtain ⟨ x, hx⟩ := h1
  use x
  constructor
  apply hx
  apply h2
  intro h
  obtain ⟨ x, hx⟩ := h
  constructor
  use x
  obtain ⟨ h1, h2⟩ := hx
  apply h1
  obtain ⟨ h1, h2⟩ := hx
  apply h2
  
