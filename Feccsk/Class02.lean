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

def Relation (A : Type) : Type := A → A → Prop -- basically a notation for R ⊆ A²

def Reflexiv {A : Type} (R : Relation A) : Prop := ∀ x : A, R x x

def Antisymmetric {A : Type} (R : Relation A) : Prop := ∀ x y : A, R x y ∧ R y x → x = y

def Transitiv {A : Type} (R : Relation A) : Prop := ∀ x y z : A, R x y ∧ R y z → R x z

def PartialOrdr {A : Type} (R : Relation A) : Prop := Reflexiv R ∧ Antisymmetric R ∧ Transitiv R

example : PartialOrdr Nat.le := by -- about (ℕ, ≤)
  constructor
  · intro x
    exact Nat.le.refl
  constructor
  · rintro x y ⟨hxy, hyx⟩
    exact Nat.le_antisymm hxy hyx
  · rintro x y z ⟨hxy, hyz⟩
    exact Nat.le_trans hxy hyz

example {A : Type} : PartialOrdr (@Set.Subset A) := by -- about (𝒫(A), ⊆)
  constructor
  · intro X
    exact Eq.subset rfl
  constructor
  · rintro X Y ⟨hXY, hYX⟩
    exact Set.Subset.antisymm hXY hYX
  · rintro X Y Z ⟨hXY, hYZ⟩
    exact Set.Subset.trans hXY hYZ

structure Poset (A : Type) where
  R : Relation A
  po : PartialOrdr R

@[simp]
def Information : Relation (EReal × EReal) :=
  fun x y : (EReal × EReal) => x.fst ≤ y.fst ∧ x.snd ≥ y.snd

lemma information_po : PartialOrdr Information := by
  constructor
  · simp [Reflexiv]
  constructor
  · rintro x y ⟨hxy, hyx⟩
    unfold Information at hxy hyx
    cases' hxy with hxfst hxsnd
    cases' hyx with hyfst hysnd
    ext
    · exact le_antisymm hxfst hyfst
    · exact le_antisymm hysnd hxsnd
  · rintro x y z ⟨hxy, hyz⟩
    unfold Information at *
    cases' hxy with xyfst xysnd
    cases' hyz with yzfst yzsnd
    constructor
    · exact le_trans xyfst yzfst
    · exact ge_trans xysnd yzsnd

@[simp]
def InformationPoset : Poset (EReal × EReal) := Poset.mk Information information_po

@[simp]
def Set.UpperBound {α : Type} (A : Set α) (R : Relation α) (x : α) : Prop :=
  ∀ y ∈ A, R y x

@[simp]
def Set.LowerBound {α : Type} (A : Set α) (R : Relation α) (x : α) : Prop :=
  ∀ y ∈ A, R x y

def Set.LeastUpperBound {α : Type} (A : Set α) (R : Relation α) (x : α) : Prop :=
  A.UpperBound R x ∧ ∀ y : α, A.UpperBound R y → R x y

def Set.GreatestLowerBound {α : Type} (A : Set α) (R : Relation α) (x : α) : Prop :=
  A.LowerBound R x ∧ ∀ y : α, A.LowerBound R y → R y x

def Poset.LeastUpperBound {α : Type} (P : Poset α) (x : α) : Prop :=
  Set.univ.LeastUpperBound P.R x

def Poset.GreatestLowerBound {α : Type} (P : Poset α) (x : α) : Prop :=
  Set.univ.GreatestLowerBound P.R x

-- TODO (didn't catch, but not needed for the homework):
-- let `(B : Set ℕ)` if `B` is finite then ???
-- let `(B : Set ENat)` ...

example : InformationPoset.GreatestLowerBound (⊥, ⊤) := by -- the term `(⊥, ⊤)` represents [-∞, ∞]
  constructor
  · simp
  · intro y hy
    simp at hy
    specialize hy ⊥ ⊤
    simp_all

def CompletLattice {A : Type} (P : Poset A) : Prop :=
  ∀ B : Set A, (∃ x, B.LeastUpperBound P.R x) ∧ (∃ x, B.GreatestLowerBound P.R x)

-- TODO (didn't catch, but not needed for the homework):
-- if `A` is a complete lattice, then `LeastUpperBound A` is `⊤` and `GreatestLowerBound A` is `⊥` (def?)
-- if `A` is a complete lattice, then `LeastUpperBound ∅` is `⊥` and `GreatestLowerBound ∅` is `⊤` (lemma?)

def Monoton {A : Type} (R : Relation A) (F : A → A) : Prop :=
  ∀ x y : A, R x y → R (F x) (F y)

def Fixpoint {A : Type} (F : A → A) (x : A) : Prop :=
  F x = x

theorem KnasterTarskiFixpoint {A : Type} {P : Poset A} {F : A → A}
    (hP : CompletLattice P) (hF : Monoton P.R F) :
    (∃ z, { x : A | P.R x (F x) }.LeastUpperBound P.R z ∧
      Fixpoint F z ∧ (setOf (Fixpoint F)).UpperBound P.R z ∧
      ∀ z' : A, Fixpoint F z' ∧ (setOf (Fixpoint F)).UpperBound P.R z' →
        z' = z) ∧
    (∃ a, { x : A | P.R (F x) x }.GreatestLowerBound P.R a ∧
      Fixpoint F a ∧ (setOf (Fixpoint F)).LowerBound P.R a ∧
      ∀ a' : A, Fixpoint F a' ∧ (setOf (Fixpoint F)).LowerBound P.R a' →
        a' = a) := by
  sorry -- homework #2
