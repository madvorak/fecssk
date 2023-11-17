/-

You can examine satisfiability purely semantically (try all possible interpretations; is one of them a model?).

When we talk about rules, we talk about syntax.

## Formal system

Formal system `F` is a set of rules.
Rule is a finite set of (formulas) premises `p₀`, ..., `pₖ` and (a formula called) conclusion `c`.
We usually have infinitely many rules but only finitely many different rule schemata.
For example, schema `φ → φ` gives infinitely many rules like `p₃ → p₃`.
Axiom is a rule without premises.
Proof (derivation):
[linear view] finite sequence of formulas `φ₀`, ..., `φₙ` such that every formula in the sequence is
· either an axiom (can be viewed as a special case of the following)
· or the conclusion of a rule whose premises occur earlier in the sequence.
Formal system equipped with semantics is called a logic.

Tree view (inductive definition) is usually better in practice.
Linear view is usually easier to meta theorems.

Theorem is a formula that occurs in a proof.
`⊢ φ` ... "φ is a theorem (of the formal system F)" (has a proof) [syntax]
`⊨ φ` ... "φ is valid (φ is tautology)" (is true in all models) [semantics]
Most of logic is about establishing `⊢ φ` iff `⊨ φ`.

Rule `R` is sound iff [if all premises of `R` are valid, then the conclusion of `R` is valid].
Formal system `F` is sound iff all rules are sound (or equivalently, every theorem is valid).
Formal system `F` is complete iff every valid formula is a theorem.
Formal system `F` is consistent unless `⊢ ⊥` (or equivalently, there exists a formula that is not a theorem).
Rule `R` is derivable in `F` iff [∀ formulas `φ`, `F ∪ {R}`-under-turnstile `φ` iff  `F`-under-turnstile `φ`].
Rule `R` is admissible in `F` iff `F ∪ {R}` is still consistent.
Formula `φ` is expressible in a logic `L` iff [∃ formula `ψ` of `L` such that ∀ interpretations `v`
  `⟦φ⟧ᵥ = ⟦ψ⟧ᵥ`].
For example `φ₁ ∧ φ₂` is expressible using only `¬` and `∨` (de Morgan) as `ψ = ¬ (¬φ₁ ∨ ¬φ₂)`.

We can enumerate all theorems by systematically enumerating all possible proofs.
The proof is a witness for validity.
Sound formal system gives a sound procedure for validity (but not necessarily complete).
Sound complete formal system gives a sound semi-complete procedure for validity (may not terminate on inputs
that represent a formula that is not valid).
To get a decision procedure (sound and complete procedure for validity), we need both
(1) sound complete formal system for validity, and
(2) sound complete formal system for satisfiability (to define a formal system for satisfiability,
    replace "formulas" (`φ` is valid) by "judgements" (`φ` is satisfiable);
    all axioms are satisfiable, all rules go from satisfiables to satisfiable).
For every input `φ`, one of them will eventually terminate.
Conclude; either `φ` is valid, or `¬φ` is satisfiable (which means that `φ` is not valid).
If both a set and its complement are recursively-enumerable, the set is recursive (decidable).

Example (formal system for unsatisfiability):

`Γ[⊥]` unsat            `Γ[⊤]` unsat
------------------------------------
            `Γ[p]` unsat

### Hilbert formal system for propositional logic

Hilbert system uses connectives `→` and `¬`.
Hilbert system has three axioms and one rule.

Rule (modus ponens):

`φ`     `φ → ψ`
---------------
    `ψ`

Axioms:

(K) `φ → ψ → φ`
(S) `(φ → ψ → χ) → ((φ → ψ) → (φ → χ))`
(em) `(¬φ → ¬ψ) → (ψ → φ)`

Metatheorem: Hilbert system is sound and complete for propositional logic.
Corollary: Hilbert system is consistent.

Example (prove `φ → φ` in Hilbert system):

(K) `φ → (ψ → φ) → φ`
(S) `(φ → (ψ → φ) → φ) → ((φ → ψ → φ) → (φ → φ))`
(MP) `(φ → ψ → φ) → (φ → φ)`
(K) `φ → ψ → φ`
(MP) `φ → φ`

-/

section Hilbert

axiom _imp : Prop → Prop → Prop
axiom _not : Prop → Prop
infixr:40 " ⇒ " => _imp
prefix:99 " ⌝ " => _not

axiom MP {φ ψ : Prop} (_ : φ) (_ : φ ⇒ ψ) : ψ
axiom K (φ ψ : Prop) : φ ⇒ (ψ ⇒ φ)
axiom S (φ ψ χ : Prop) : (φ ⇒ ψ ⇒ χ) ⇒ ((φ ⇒ ψ) ⇒ (φ ⇒ χ))
axiom EM (φ ψ : Prop) : (⌝φ ⇒ ⌝ψ) ⇒ (ψ ⇒ φ)


example (a b : Prop) :=
  have h1 := K a b
  have h2 := K a (b ⇒ a)
  have h3 := S a (b ⇒ a) a
  have h4 := MP h2 h3
  show a ⇒ a
        from MP h1 h4

example (a b c : Prop) :=
  have h1 := K (b ⇒ c) a
  have h2 := S a b c
  have h3 := K ((a ⇒ b ⇒ c) ⇒ ((a ⇒ b) ⇒ (a ⇒ c))) (b ⇒ c)
  have h4 := MP h2 h3
  have h5 := S (b ⇒ c) (a ⇒ b ⇒ c) ((a ⇒ b) ⇒ (a ⇒ c))
  have h6 := MP h4 h5
  show (b ⇒ c) ⇒ (a ⇒ b) ⇒ (a ⇒ c)
        from MP h1 h6

end Hilbert

/-

Notation: `Γ ⊢ φ` means `F ∪ {Γ}`-under-turnstile `φ` (the set of formulas `Γ` is used as added axioms)
Metatheorem ("deduction theorem"):
`Γ ⊢ φ → ψ` iff `Γ, φ ⊢ ψ`
Metaproof:
"=>": One application of modus ponens.
"<=":
Assume `ψ` has a proof `π` using axioms `Γ`, `φ`, (K), (S), (em).
Show `φ → ψ` has a proof using `Γ`, (K), (S), (em).
Induction on length `n` of `π`.
Case `n=1`: `ψ` must be an axiom.
Either `ψ ∈ Γ ∪ {K, S, em}` so we prove it by (K),
or `ψ = φ` so we use `⊢ φ → φ` as derived above.
Case `n>1`: `ψ` is the result of an application of modus ponens.
We have `χ` and `χ → ψ`, both of which were derived from `Γ, φ` in fewer steps.
Induction hypothesis gives us `Γ ⊢ φ → χ` and `Γ ⊢ φ → χ → ψ`.
We use (S) in the form `(φ → χ → ψ) → (φ → χ) → (φ → ψ)` and apply modus ponens twice,
resulting in `φ → ψ` derived from `Γ` only.

-/
