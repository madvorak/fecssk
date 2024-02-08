/-

[[c]] ⊆ Σ → Σ

[[skip]] = λσ, σ
[[assert b]] = λσ, if [[b]]σ then σ else fail

Operationally:

⟨b, σ⟩ ↓ ⊤
-------------
⟨assert b,σ⟩ ↓ σ

⟨b, σ⟩ ↓ ⊥
-------------
⟨assert b,σ⟩ ↓ fail

wlp(skip, ψ) = ψ
wlp(assert b, ψ) = b ∧ ψ

In nondeterministic settings, the symbol `↓` means "can reach".

{ b ∧ ψ } assert b { ψ }

We change program semantics to:
[[c]] ⊆ Σ × (Σ ∪ {fail, ⊥})

[[assume b]] = { (σ,σ') | σ ⊨ b ∧ σ = σ' }

We define:
wlp(c,ψ) = { σ | ∀ σ', (σ,σ') ∈ [[c]] → σ' ⊨ ψ }

wlp(assume b, ψ) = (b => ψ)

{ b => ψ } assume b { ψ }

[[abort]] = λσ, fail
[[havoc b]] = { (σ,σ') | σ' ⊨ b }
Alternative: if σ ⊨ b then σ' = σ else σ' ⊨ b

## Dijkstra's guarded commands

### Syntax

gc := b → c | gc ∣ gc
c := skip | abort | x := a | c; c | if gc fi | do gc od

### Example

Euclid's GCD algorithm:
do
    x > y → x := x - y
  ∣
    y > x → y := y - x
od

Many nondeterministic algorithms are more elegant than their deterministic version,
which has to arbitrarily choose one determination.

### Semantics

⟨b, σ⟩ ↓ ⊤       ⟨c, σ⟩ ↓ σ'
----------------------------
     ⟨b → c, σ⟩ ↓ σ'

   ⟨gc₁, σ⟩ ↓ σ'
-------------------
⟨gc₁ ∣ gc₂, σ⟩ ↓ σ'

   ⟨gc₂, σ⟩ ↓ σ'
-------------------
⟨gc₁ ∣ gc₂, σ⟩ ↓ σ'

⟨gc₁, σ⟩ ↓ fail    ⟨gc₂, σ⟩ ↓ fail
----------------------------------
      ⟨gc₁ ∣ gc₂, σ⟩ ↓ fail

4 more rules

## Homework

c := skip | x := a | c;c | b? | cpc | c∗
copy `a` and `b` from previous languages

`b?` is the same as `assume b`
`cpc` is alternative
`c∗` is like Kleene star (iterace 0 or more times)

Give:
(1) operational rules
(2) denotational def of [[c]]
(3) wlp def or Hoare rules

[[c∗]] = lfp F ... what is `F`?

## Parallelism

Paralellism is arbitrary nondeterministic interleaving.of atomic actions.

x := 0 || x := 1 is either (x := 0; x := 1) or (x := 1; x := 0)

(1) nondeterministic
(2) noncompositional
(3) nontermination as the usual case (reactive programs)

Concurrency Theory / Process Algebra (we wanna add || to languages)

There were dozens of process algebras in the 1990s.

### CCS (Calculus of Communicating Systems) by Milner

processes: P, Q, ...
nil: 0 (like skip)
atomic actions: a, b, ... ∈ A
prefix: a.P (like sequencing)
alternative: P p Q
process def: C = P    (hat on top of =)

Iterate = a.Iterate

They are sequential processes.
Sequentil processes are action-labeled directed graphs (labeled transition systems).
Any digraph can be encoded as a sequential process.

parallelism: P || Q

Every action comes as a pair of input action and output action.
We write input actions as letters and output actions as letters with bar.

restriction: (νa) P

### SOS (Structured Operational Semantics)

We now prefer single-step semantics.

-------------
a.P --(a)-> P

  P --(a)-> P'
----------------
P p Q --(a)-> P'

  Q --(a)-> Q'
----------------
P p Q --(a)-> Q'

TODO =hat

     P --(a)-> P'
----------------------
P || Q --(a)-> P' || Q

     Q --(a)-> Q'
----------------------
P || Q --(a)-> P || Q'

     P --(b)-> P'
---------------------- a ≠ b, a⊼ ≠ b
(νa) P --(b)-> (νa) P'

We can imagine (νa) as a quantifier.

-/
