import Mathlib.Tactic.Have

/-

## Set S is defined inductively by a set R of rules:
`S` is the smallest set that is forward-closed under `R`, i.e.,
`S` is the smallest `X` such that
  `∀ r ∈ R, ∀ x ∈ conclusions r, premises r ⊆ X → x ∈ X`

### Examples of inductive definitions:

Natural numbers:
                                   x
                       ---        ---
                        0         S x

Finite words:
                                     x
                       ---        ------ a ∈ Σ
                        ε         a :: x

Finite binary trees:
                                    x    y
                       ---        ---------- a ∈ Σ
                        ε         Tree a x y

### Induction on S:
In order to show `∀ x, x ∈ S → G x`
it suffices to show that `G` is forward-closed.
For each rule `r` and conclusion `x` of `r`,
assume for each premise `y` of `r` we have `G y`,
show `G x`.

## Set S is defined coinductively by a set R of rules:
`S is the largest set that is backward-closed under `R`, i.e.,
`S` is the largest `X` such that
  `∀ r ∈ R, ∀ x ∈ conclusions r, x ∈ X → premises r ⊆ X`

### Examples of coinductive definitions:

Infinite words:
                          x
                       ------ a ∈ Σ
                       a :: x

Infinite binary trees:
                         x    y
                       ---------- a ∈ Σ
                       Tree a x y

### Coinduction on S:
In order to show `∀ x, K x → x ∈ S`
it suffices to show that `K` is backward-closed.
For each rule `r` and conclusion `x` of `r`,
assume assume `K x`,
show for each premise `y` of `r` that `K y`.


### Example: induction and coinduction in programming

We have alphabet `Σ` with linear order `≤`.

∀ y ∈ Σ∗, merge ε y = y

∀ x ∈ Σ∗, merge x ε = x

∀ x ∈ Σ∗, ∀ y ∈ Σ∗, ∀ a ∈ Σ, ∀ b ∈ Σ,
  merge (a::x) (b::y) = if a ≤ b
                        then a :: merge x (b::y)
                        else b :: merge (a::x) y

For a string-processing program, keep all the rules (induction).
For a stream-processing program, keep only the last rule (coinduction).


## Generalization of induction hypotheses

-/

variable {α : Type}


-- ### Concatenating lists

def cat : List α → List α → List α
| [ ]   , y => y
| a :: x, y => a :: cat x y

theorem cat_assoc (x y z : List α) :
  cat (cat x y) z = cat x (cat y z) :=
by
  induction x with
  | nil => rfl
  | cons a s ih =>
    dsimp only [cat]
    exact congrArg (a :: ·) ih

theorem cat_nil (x : List α) :
  cat x [] = x :=
by
  induction x with
  | nil => rfl
  | cons a s ih =>
    dsimp only [cat]
    exact congrArg (a :: ·) ih


-- ### Reversing lists

def rev : List α → List α
| [ ]    => [ ]
| a :: x => cat (rev x) [a]

def r : List α → List α → List α
| [ ]   , y => y
| a :: x, y => r x (a :: y)

theorem rev_eq_r (x : List α) :
  rev x = r x [] :=
by
  -- starting by `induction x` would get us into a blind alley
  have generalized : ∀ x y : List α, cat (rev x) y = r x y
  · clear x
    intro x
    -- here `intro y` would get us into another blind alley
    induction x with
    | nil =>
      intro y
      rfl
    | cons a u ih =>
      intro y
      dsimp only [rev, r]
      specialize ih (a :: y)
      rw [cat_assoc]
      exact ih
  specialize generalized x []
  rw [cat_nil] at generalized
  exact generalized


-- ### Sorting lists

variable [LE α] [@DecidableRel α (· ≤ ·)]

def merge : List α → List α → List α
| [ ]   , y      => y
| x     , [ ]    => x
| a :: x, b :: y => if a ≤ b
                    then a :: merge x (b :: y)
                    else b :: merge (a :: x) y
termination_by merge x y => x.length + y.length

def split : List α → List α × List α
| [ ]         => ([ ], [ ])
| [ a ]       => ([a], [ ])
| a :: b :: s => let (x, y) := split s;
                 (a :: x, b :: y)

def mergesort : List α → List α
| [ ]         => [ ]
| [a]         => [a]
| a :: b :: s => let (x, y) := split (a :: b :: s);
                 have hxl : x.length < s.length.succ.succ :=
                 by -- TODO prove for termination
                   sorry
                 have hyl : y.length < s.length.succ.succ :=
                 by -- TODO prove for termination
                   sorry
                 merge (mergesort x) (mergesort y) -- the "body"
-- the compiler needs the following hint to stay here
termination_by mergesort l => l.length


#eval mergesort [3, 5, 7, 1, 9, 5, 0, 2, 4, 6, 8] -- 0..9 with 5 twice

def sorted : List α → Prop
| [ ]         => True
| [_]         => True
| a :: b :: _ => a ≤ b


/- ## Homework No.1
TODO we probably need to assume a total order (`≤` is a linear ordering on `α`) -/
theorem mergesort_sorts (x : List α) :
  sorted (mergesort x) :=
by
  sorry -- prove this by well-founded induction

/- ## Homework No.2
Define `permutation x y : Prop` for `(x y : List α)` and prove:
`∀ x, permutation x (mergesort x)` -/


/- ## Homework No.3
A ... living beings
`∀ x, human x ^^^ monkey x`
`∀ x y, x > y ↔ ∃ z, parent z y ∧ x > z`
`>` is well founded
Prove: [theorem will be sent by e-mail]
-/
