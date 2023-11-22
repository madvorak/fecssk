
/-

### Proof systems for propositional logic

We now talk about three proof systems:
• Hilbert            `  ⊢ φ`
• Natural deduction  `Γ ⊢ φ`
• Grentzen           `Γ ⊢ Δ`

We now talk abou three decision procedures (either for validity or for satisfiability).

#### Branching

`Γ[⊥]` unsat            `Γ[⊤]` unsat
------------------------------------         ------------
            `Γ[p]` unsat                     `Γ, ⊥` unsat

If we don't derive `⊥` then it is satisfiable.

#### Resolution

`Γ, C₁, C₂, C₁[⊥]∨C₂[⊥]` unsat
------------------------------
`Γ, C₁[p], C₂[¬p]` unsat

#### Unit resolution, combined with branching (DPLL)

Branching has lower priority.

Unit resolution (`l` is a literal):

`Γ, C[⊥]` unsat
-------------------
`Γ, l, C[¬l]` unsat

Example: `p ∨ q ∨ r , ¬p ∨ ¬q ∨ ¬r , ¬p ∨ q ∨ r , ¬ q ∨ r , q ∨ ¬r`
First we branch on `r`.
TODO
It is satisfied by `p=⊥, q=⊤, r=⊤`.

Horn clause is a clause with at most one positive literal.
We can view them as implications where LHS is a conjunction of positive propositions.
`¬p ∨ ¬q`     ↔ `p ∧ q → ⊥`
`¬p ∨ ¬q ∨ r` ↔ `p ∧ q → r`
`r`           ↔ `  ⊤   → r`

### Metatheorems

#### Compactness

Countable set `Γ` of formulas is satisfiable iff every finite subset of `Γ` is satisfiable.

#### Craig's interpolation

`⊢ φ → ψ` iff there exists a third formula `χ` (the "interpolant") which only uses
nonlogical symbols (in propositional logic, it is propositions only) that occur in
both `φ` and `ψ` such that `⊢ φ → χ` and `⊢ χ → ψ`.

##### Homework

How hard is it to compute interpolants in propositional logic?

#### Cut elimination

##### Cut rule in NK / NJ

`Γ ⊢ φ`       `Γ, φ ⊢ ψ`
------------------------
       `Γ ⊢ ψ`

##### Cut rule in LK:

`Γ ⊢ φ, Δ`       `Γ, φ ⊢ Δ`
---------------------------
          `Γ ⊢ Δ`

##### Eliminating the cuts

If a judgement can be proved with the cut rule, it can also be proved without the cut rule.
In fact, it is "iff"; the other direction is trivial.
Of course, the proof may become longer (introducing a lemma `φ` often helps in practice).
It is a purely syntactic metatheorem. We cannot use deduction to prove it.


# First-order logic

Propositional logic with quantifiers `∀` and `∃`.
Also called "predicate logic", but we call it FOL.

## Syntax

### Nonlogical symbols ("signature")

(1) finite set of variables `X = {x, y, z, ...}`
(2) finite set of function symbols `F = {f, g, h, ...}`
(3) finite set of predicate symbols `P = {p, q, r, ...}`

Each function symbol has a fixed "arity" (number of arguments), which can be zero (constant).
Dtto predicate symbols (arity 0 gives propositions).

### Logical symbols

(1) connectives (`⊥`, `⊤`, `¬`, `∧`, `∨`, `→`)
(2) quantifiers (`∀`, `∃`)

We don't add parentheses to the symbols; we will talk about syntax trees;
only if we want to write them down as strings, we add parentheses (as few as possible).

A change of bound variables does not change the abstract syntax tree (same in abstract syntax).

Terms: `t` := `f₀` | `fₙ (t₁, ..., tₙ)`
Formulas: `φ` := `p₀` | `pₙ (t₁, ..., tₙ)` | `⊥` | `⊤` | `¬φ` | `φ ∨ φ` | `φ ∧ φ` | `φ → φ` | `∀x, φ` | `∃x, φ`

When we write `∀x, φ`, every occurence of `x` is boundy in `φ`.
A variable that is not bound is called free.

### Safe substitution

`∀x, ∃y, y ≥ x + 1`
If we want to substitute `y²` for `x`, we must first rename `y` to `z` and then substitute.
`∀x, ∃z, z ≥ x + 1`
`∃z, z ≥ y² + 1`

-/
