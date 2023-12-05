/-

## First-order resolution

It was the first attempt to automate theorem proving (not successful).

We want to prove `⊨ φ` for closed `φ`.
Step 0. Negate; show `¬φ` is unsatisfiable.
Step 1. Bring `¬φ` into prenex form (all quantifiers are in front).
Step 2. Bring `φ` into conjunctive normal form.
Step 3. Skolemization gets rid of `∃`s.
Step 4. Drop `∀`s.
Step 5. Resolution with unification.

-/
