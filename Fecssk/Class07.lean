import Mathlib.Data.Real.Irrational
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-

### Natural deduction for propositional logic

Judgements have the form `Γ ⊢ φ` where `Γ` is a set of formulas and `φ` is a formula.
Syntax: `Γ ⊢ φ` (`Γ` derives `φ`)
Semantics: For all interpretations `v` [if all formulas in `Γ` are true in `v` then `φ` is true in `v`].
Formal system for natural deduction defines "meta ⊢" such: ⊢ `(Γ ⊢ φ)`

`Γ ∪ {φ}` is written `Γ, φ`
                                                                  `Γ ⊢ ⊤`
---------- (ax)                ------- (True intro)               ------- (False elim)
`Γ, φ ⊢ φ`                     `Γ ⊢ ⊤`                            `Γ ⊢ φ`

`Γ ⊢ φ ∧ ψ`                     `Γ ⊢ φ ∧ ψ`                    `Γ ⊢ φ`       `Γ ⊢ ψ`
----------- (And elim)          ----------- (And elim)         --------------------- (And intro)
`Γ ⊢ φ`                         `Γ ⊢ ψ`                             `Γ ⊢ φ ∧ ψ`

`Γ ⊢ φ ∨ ψ`     `Γ, φ ⊢ χ`     `Γ, φ ⊢ χ`
----------------------------------------- (Or elim)
                  `Γ ⊢ χ`

TODO (Or intro (two rules)) (Not elim (instance of MP)) (Not intro) (Impl elim (MP)) (Impl intro)

-/

example (P Q : Prop) : (P → Q) → (¬Q → ¬P) := by
  intro hpq -- (Impl intro)
  intro hnq -- (Impl intro)
  intro hp  -- (Not intro)
  apply hnq -- (Not elim)
  apply hpq -- (Impl elim)
  exact hp  -- (ax)

/-

Homework #1: prove transitivity of implication.

The system above is called NJ (Natural deduction, Intuitionistic).
When we add the excluded middle, we get MK (Natural deduction, Classical).

Theorem: There exist two irrational numbers (`a b ∉ ℚ`) such that
one to the power of the other is a rational number (`a^b ∈ ℚ`).

-/

lemma sqrt2_pow_sqrt2_pow_sqrt2 :
  (Real.sqrt 2 ^ Real.sqrt 2) ^ Real.sqrt 2 = Real.sqrt 2 ^ (Real.sqrt 2 * Real.sqrt 2) :=
by
  sorry

lemma sqrt2_mul_sqrt2 : Real.sqrt 2 * Real.sqrt 2 = ↑(2 : ℕ) :=
by
  sorry

lemma sqrt2_pow_2 : Real.sqrt 2 ^ (2 : ℕ) = (2 : ℝ) :=
by
  sorry

-- OK the calculations with reals are awkward...
theorem irrational_pow_irrational_can_be_rational :
  ∃ a b : ℝ, Irrational a ∧ Irrational b ∧ ¬Irrational (a ^ b) :=
  --                                       ∃ q : ℚ, Real.rpow a b = ↑q
by
  by_cases hyp : Irrational (Real.rpow (Real.sqrt 2) (Real.sqrt 2))
  · use (Real.sqrt 2) ^ (Real.sqrt 2), Real.sqrt 2
    constructor
    · exact hyp
    constructor
    · exact irrational_sqrt_two
    rw [sqrt2_pow_sqrt2_pow_sqrt2, sqrt2_mul_sqrt2, sqrt2_pow_2]
    apply Nat.not_irrational
  · use Real.sqrt 2, Real.sqrt 2
    exact ⟨irrational_sqrt_two, irrational_sqrt_two, hyp⟩

/-

#### Kripke semanitics

Kripke semanitics for which NJ is sound and complete.
Classically: `v : P → Bool`
Intuitionistically: `m = (W, ≤, w₀, v : W × P → Bool)`
`W` is a "set of classical worlds" with preorder `≤` and initial world `w₀` such that:
`∀ w, ∀ w', ∀ p, w ≤ w' → v w p ≤ v w' p`

Intuitionistic interpretation:
`m ⊨ φ` iff `m ⊢[w₀] φ`
`m ⊨[w] ⊥` is false
`m ⊨[w] φ` iff `v w p = true`
`m ⊨[w] φ → ψ` iff `∀ w', w ≤ w' ∧ m ⊨[w'] φ → m ⊨[w'] ψ`

There must be a model where excluded middle does not hold.
`w₀` --> (`¬p`) --(≤)--> (`p`)


### Sequent calculus

Gentzen calculus LK

A judgement has the form `Γ ⊢ Δ` (sets on both sides).
LHS is interpreted conjunctively.
RHS is interpreted disjunctively.
Semantics:
`v ⊨ (Γ ⊢ Δ)` iff [if all formulas in `Γ` are true in `v` then some fomula in `Δ` is true in `v`]

Rules:

------------- (ax)          ---------- (True intro)         ---------- (False elim)
`Γ, φ ⊢ φ, Δ`               `Γ ⊢ ⊤, Δ`                      `Γ, ⊥ ⊢ Δ`

`Γ, φ, ψ  ⊢ Δ`             `Γ, φ ⊢ Δ`      `Γ, ψ ⊢ Δ`
--------------             --------------------------
`Γ, φ ∧ ψ ⊢ Δ`                   `Γ ⊢ φ ∧ ψ, Δ`

`Γ  ⊢ φ, ψ, Δ`             `Γ, φ ⊢ Δ`      `Γ, ψ ⊢ Δ`
--------------             --------------------------
`Γ ⊢ φ ∨ ψ, Δ`                   `Γ, φ ∨ ψ ⊢ Δ`

`Γ  ⊢ φ, Δ`       `Γ, φ  ⊢ Δ`
-----------       -----------
`Γ, ¬φ ⊢ Δ`       `Γ ⊢ ¬φ, Δ`

`Γ ⊢ φ, Δ`    `Γ, ψ ⊢ Δ`           `Γ, φ ⊢ ψ, Δ`
------------------------          ---------------
    `Γ, φ → ψ  ⊢ Δ`               `Γ ⊢  φ → ψ, Δ`

Homework #2: prove transitivity of implication in LK.

Here we can actually prove `⊢ p ∨ ¬p`

Homework #3: prove excluded middle in LK.

LK is sound and complete for classsical propositional logic.

-/
