import Mathlib.Data.Real.Basic

/-
## What is a proof?

We will do something similar to natural deduction.
-/

def Bound (f : ℝ → ℝ) (b : ℝ) : Prop := ∀ x : ℝ, f x ≤ b

def Bounded (f : ℝ → ℝ) : Prop := ∃ b : ℝ, Bound f b

theorem bounded_add : ∀ f g : ℝ → ℝ, Bounded f ∧ Bounded g → Bounded (f+g) := by
  rintro f g ⟨⟨a, hfa⟩, ⟨b, hfb⟩⟩
  use a + b
  intro x
  show f x + g x ≤ a + b
  apply add_le_add
  · exact hfa x
  · exact hfb x


variable {A B : Type}

def OneToOne (f : A → B) : Prop := ∀ x y : A, x ≠ y → f x ≠ f y

def Onto (f : A → B) : Prop := ∀ z : B, ∃ x : A, f x = z

def Bijective (f : A → B) : Prop := OneToOne f ∧ Onto f

def Equipollent (A B : Type) : Prop := ∃ f : A → B, Bijective f

theorem homework1 : (∃ f : A → B, OneToOne f) ∧ (∃ g : B → A, OneToOne g) → Equipollent A B := by
  sorry
