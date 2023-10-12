import Mathlib.Data.Real.EReal

/-
The table on the blackboard mostly corresponds to the first table here:
https://github.com/madvorak/lean4-tactics
Just move the left-most column to the right-most end.

Differences from the above-mentioned table:

If we want to show `G₁ ∨ G₂`, we can either
assume `¬G₁` and show `G₂`
or
assume `¬G₂` and show `G₁`

For `¬` we `push_neg` ...
`¬ ∀ x` = `∃ x, ¬`
`¬ ∃ x` = `∀ x, ¬`
`¬ (G₁ ∨ G₂)` = `¬G₁ ∧ ¬G₂`
`¬ (G₁ ∧ G₂)` = `¬G₁ ∨ ¬G₂`
`¬¬G` = `G`
(from left to right is more useful)


## Lattices and fixpoints

We drew Hasse diagrams on the blackboard [omitted here].
-/

variable {A B : Type}

def Relation (A : Type) : Type := A → A → Prop -- Set (A × A)

def Reflexiv (R : Relation A) : Prop := ∀ x : A, R x x

def Antisymmetric (R : Relation A) : Prop := ∀ x y : A, R x y ∧ R y x → x = y

def Transitiv (R : Relation A) : Prop := ∀ x y z : A, R x y ∧ R y z → R x z

def PartialOrdr (R : Relation A) : Prop := Reflexiv R ∧ Antisymmetric R ∧ Transitiv R

example : PartialOrdr Nat.le := by
  constructor
  · intro x
    exact Nat.le.refl
  constructor
  · rintro x y ⟨hxy, hyx⟩
    exact Nat.le_antisymm hxy hyx
  · rintro x y z ⟨hxy, hyz⟩
    exact Nat.le_trans hxy hyz

example : PartialOrdr (fun X Y : Set A => X ⊆ Y) := by
  constructor
  · intro X
    exact Eq.subset rfl
  constructor
  · rintro X Y ⟨hXY, hYX⟩
    exact Set.Subset.antisymm hXY hYX
  · rintro X Y Z ⟨hXY, hYZ⟩
    exact Set.Subset.trans hXY hYZ

def Information : Relation (EReal × EReal) :=
  fun x y : (EReal × EReal) => x.fst ≤ y.fst ∧ x.snd ≥ y.snd

lemma information_po : PartialOrdr Information := by
  constructor
  · simp [Reflexiv, Information]
  constructor
  · rintro x y ⟨hxy, hyx⟩
    simp [Information] at hxy hyx
    cases' hxy with xfst ysnd
    cases' hyx with yfst xsnd
    sorry -- TODO
  · rintro x y z ⟨hxy, hyz⟩
    simp_all [Information]
    sorry -- TODO

structure Poset where
  R : Relation A
  po : PartialOrdr R

def InformationPoset : @Poset (EReal × EReal) := Poset.mk Information information_po

def Monoton (R : Relation A) (F : A → A) : Prop := ∀ x y : A, R x y → R (F x) (F y)

def Fixpoint (F : A → A) (x : A) : Prop := F x = x

def UpperBound (A' : Set A) (R : Relation A) (x : A) : Prop := ∀ y ∈ A', R y x
def LowerBound (A' : Set A) (R : Relation A) (x : A) : Prop := ∀ y ∈ A', R x y

def LeastUpperBound (A' : Set A) (R : Relation A) (x : A) : Prop :=
  UpperBound A' R x ∧ ∀ y : A, UpperBound A' R y → R y x

def GreatestLowerBound (A' : Set A) (R : Relation A) (x : A) : Prop :=
  LowerBound A' R x ∧ ∀ y : A, UpperBound A' R y → R x y

-- TODOs :
-- let `(B : Set ℕ)` if `B` is finite then `LeastUpperBound B` is `max B` else `LeastUpperBound B` doesn't exist
-- let `(B : Set ℕ with inf)` ... is `inf`
-- information poset has `[-inf, +inf]` as its

def CompleteLattic (R : Relation A) : Prop :=
  ∀ B : Set A, (∃ x, LeastUpperBound B R x) ∧ (∃ x, GreatestLowerBound B R x)

-- if A,≤ is a complete lattice, then `LeastUpperBound A` is `⊤` and `GreatestLowerBound A` is `⊥`
-- if A,≤ is a complete lattice, then `LeastUpperBound ∅` is `⊥` and `GreatestLowerBound A` is `⊤`
