/-

## First-order theories

### Free theory

Equality and uniterpreted function and predicate symbols

Signature: `=` (binary predicate), `f`, `g`, `h`, ..., `p`, `q`, `r`, ...

Axioms: `=` is equivalence; congruence for functions and predicates

Undecidable. Incomplete.

#### Quantifier-free fragment

Given quantifier-free formula `φ`, is `φ` T-satisfiable?
Satisfiability is NP-complete (like for propositional logic).
Quantifier-free confunction is solvable in O(`n * log n`) using
so-called congruence closure (in O(`n`) for propositional logic).

#### Homework

Given a union-find algorithm, write a subquadratic congruence-closure algorithm.

### Theory of groups

Undecidable. Incomplete.

#### Quantifier-free fragment

Homework?

### Theory of natural numbers

Signature: `=` (binary predicate), `0`, `1`, `+`, `*`

Gödel proved it cannot be RE axiomatized.

Peano arithmetic is undecidable and incomplete.
Even Peano's quantifier-free fragment is undecidable.

Without `*` Presburger arithmetic.
Presburger arithmetic is decidable (3EXPTIME) and complete.
Satisfiability of quantifier-free conjunction is in NP (probably in P).

#### Homework

Give a formula in Presburger arithmetic that has no quantifier-free equivalent.

### Theory of real numbers

Signature: `=` (binary predicate), `0`, `1`, `+`, `-`, `*`, `≤`

#### Axioms

Field.
Nontrivial.
Order.
`∀x, ∃y, x = y * y ∨ -x = y * y`
Infinitely many axioms in the form, for all odd `n`: `∀x₁, ..., ∀xₙ, ∃y, y^n TODO = 0`

### Theory of linear arithmetic

Signature: `=` (binary predicate), `0`, `1`, `+`, `-`, `≤`

#### Axioms

`≤` is antisymmetric, transitive, total
`+` is associative, commutative, identity `0`, has inverses
`≤` respects `+`
Infinitely many axioms in the form, for all non-zero natural numbers `n`: `∀x, n • x = 0 → x = O`
Infinitely many axioms in the form, for all non-zero natural numbers `n`: `∀x, ∃y, x = n • y`

-/
