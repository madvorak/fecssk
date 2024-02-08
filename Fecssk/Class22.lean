/-

We talked about temporal logics.
There was μ-calculus:
`φ := p | ¬φ | φ ∧ φ | μ X. φ(x) | x | ∃◯ φ`
Talking about `μ X. φ(x)`:
Every free occurence of `x` in `φ` is within an even number of negations
(otherwise φ would not be monotonic, hence there would be no fixpoint).

CTL (branching-time temporal logic):
`φ := p | ¬φ | φ ∧ φ | ∃◯ φ | ∃ (φ 𝒰 φ)`

LTL (linear-time temporal logic):
`φ := p | ¬φ | φ ∧ φ | ◯ φ | φ 𝒰 φ`

KS (Kripke Structure):
`K = (S, →, ⟦⟧), s ∈ S`
`s ⊨[K] φ iff ∃ s₀ → s₁ → ... → s₀ = s ∧ s₀s₁s₂... ⊨ φ`

CTL is less expressive than μ-calculus.
LTL is less expressive than μ-calculus.
CTL and LTL are incomparable.
`∀◇ p ∉` LTL
`∃□◇ p ∉` CTL
`μ X. p ∨ ∃◯ ∃◯ X ∉` CTL, LTL

Model-checking problem: given KS K ad state `S` of `K` ("the system/model")
and a formula φ ("the specification"), does `s ⊨[K] φ`?

For μ-calculus, we have a model-checking algorithm.
It is the fixpoint iteration.
`O( |K| ^ d )` where `d` is the "alternation depth"
(# of nested quantiier switches between `μ` and `ν`) in `φ`
(`d ∈ O( |φ| )`).

For CTL we also do fixpoint iteration. CTL has alternation depth `O( |K| ⬝ |φ| )`.

For LTL, we convert `φ` into an ω-automaton (finite automaton over infinite word).
The converting step is `O( 2 ^ |φ| )`.
Then check property of `K x A φ`.
States of `A φ` are subformulas of `φ`.
In total we have `O( |K| ⬝ 2 ^ |φ| )`.

CCS (textual syntax for LTS):
Example (producer-consumer):

`P = a b P`
`C = b- c C`
`F = (ν b) P || C`

## Petri nets

Original Petri nets will be called PN.

P/T (Place-Transition net)
N = (P, T)
P ... places
T ... transitions
A ... actions
Marking m : P → ℕ
Marking is the same as multiset of places.
M ... set of markings
T ⊆ M × A × M

Net N → LTS T_N = (S, →)
What are the states of the label transition system? Markings!
S = M_N
→ = T_N
T_N may be infinite (and it usually is) for finite N.

Example (semicounter):
Single state, increment, decrement.
L_S = { `t` ∈ {inc, dec}* | every prefix of `t` contains as #inc ≥ #dec }

We are all familiar with the Chomsky hierarchy.
Regular ⊂ ContextFree ⊂ ContextSensitive ⊂ RecursivelyEnumerable
(finite)  (pushdown)    (linear-bounded)   (Turing machines)

We can draw a concurrent computational hierarchy.
PN₀ = Regular ⊂ PN₁ = BPP ⊂ PN₂ = CCS
BPP is CCS without `ν`.
Which CCS were we talking about exactly?

### PN₀
P finite
T finite
`|•t| = 1` and `|t•| ≤ 1`
For every transition `t`, if `(m, a, m') ∈ t` then `•t = m` and `t• = m'`.

### PN₁
(parallel composition of FA)
P finite
T finite
`|•t| = 1`

### PN₂
P finite
T finite
`1 ≤ |•t| ≤ 2`
`|•t|=2` then actual label is `τ`

Theorem: PN₂ ≃ CCS

-/
