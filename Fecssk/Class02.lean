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


# Lattices and fixpoints

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

@[simp]
def Set.LeastUpperBound {α : Type} (A : Set α) (R : Relation α) (x : α) : Prop :=
  A.UpperBound R x ∧ ∀ y : α, A.UpperBound R y → R x y

@[simp]
def Set.GreatLowerBound {α : Type} (A : Set α) (R : Relation α) (x : α) : Prop :=
  A.LowerBound R x ∧ ∀ y : α, A.LowerBound R y → R y x

@[simp]
def Poset.LeastUpperBound {α : Type} (P : Poset α) (x : α) : Prop :=
  Set.univ.LeastUpperBound P.R x

@[simp]
def Poset.GreatLowerBound {α : Type} (P : Poset α) (x : α) : Prop :=
  Set.univ.GreatLowerBound P.R x

-- TODO (didn't catch, but not needed for the homework):
-- let `(B : Set ℕ)` if `B` is finite then ???
-- let `(B : Set ENat)` ...

example : InformationPoset.GreatLowerBound (⊥, ⊤) := by -- the term `(⊥, ⊤)` represents [-∞, ∞]
  constructor
  · simp
  · intro y hy
    simp at hy
    specialize hy ⊥ ⊤
    simp_all

def CompleteLatice {A : Type} (P : Poset A) : Prop :=
  ∀ B : Set A, (∃ x, B.LeastUpperBound P.R x) ∧ (∃ x, B.GreatLowerBound P.R x)

@[simp]
noncomputable def CompleteLatice.supre {A : Type} {P : Poset A} (hP : CompleteLatice P) (S : Set A) : A :=
  Classical.choose (hP S).1 -- `hP.supre S` denotes `⊔S` in given complete lattice

@[simp]
noncomputable def CompleteLatice.infim {A : Type} {P : Poset A} (hP : CompleteLatice P) (S : Set A) : A :=
  Classical.choose (hP S).2 -- `hP.infim S` denotes `⊓S` in given complete lattice

lemma CompleteLatice.supre_is_LUB {A : Type} {P : Poset A} (hP : CompleteLatice P) (S : Set A) :
    S.LeastUpperBound P.R (hP.supre S) := by
  apply Classical.choose_spec

lemma CompleteLatice.infim_is_GLB {A : Type} {P : Poset A} (hP : CompleteLatice P) (S : Set A) :
    S.GreatLowerBound P.R (hP.infim S) := by
  apply Classical.choose_spec

@[simp]
noncomputable def CompleteLatice.top {A : Type} {P : Poset A} (hP : CompleteLatice P) : A :=
  Classical.choose (hP Set.univ).1 -- `hP.top` denotes `⊤` in given complete lattice

@[simp]
noncomputable def CompleteLatice.bot {A : Type} {P : Poset A} (hP : CompleteLatice P) : A :=
  Classical.choose (hP Set.univ).2 -- `hP.bot` denotes `⊥` in given complete lattice

lemma CompleteLatice.top_is_LUB {A : Type} {P : Poset A} (hP : CompleteLatice P) :
    P.LeastUpperBound hP.top := by
  apply Classical.choose_spec

lemma CompleteLatice.bot_is_GLB {A : Type} {P : Poset A} (hP : CompleteLatice P) :
    P.GreatLowerBound hP.bot := by
  apply Classical.choose_spec

lemma CompleteLatice.supre_empty_is_bot {A : Type} {P : Poset A} (hP : CompleteLatice P) :
    hP.supre ∅ = hP.bot := by
  simp_all

lemma CompleteLatice.infim_empty_is_top {A : Type} {P : Poset A} (hP : CompleteLatice P) :
    hP.infim ∅ = hP.top := by
  simp_all

def Monoton {A : Type} (R : Relation A) (F : A → A) : Prop :=
  ∀ x y : A, R x y → R (F x) (F y)

def UniqueMember {A : Type} (S : Set A) (a : A) : Prop :=
  a ∈ S ∧ ∀ b ∈ S, b = a

def Fixpoint {A : Type} (F : A → A) (x : A) : Prop :=
  F x = x

def Prefixpoint {A : Type} (R : Relation A) (F : A → A) (x : A) : Prop :=
  R x (F x)

def Posfixpoint {A : Type} (R : Relation A) (F : A → A) (x : A) : Prop :=
  R (F x) x

lemma prefixpoint_of_fixpoint {A : Type} (P : Poset A) {F : A → A} {x : A}
    (fpx : Fixpoint F x) :
    Prefixpoint P.R F x := by
  unfold Prefixpoint
  unfold Fixpoint at fpx
  rw [fpx]
  apply P.po.left

lemma posfixpoint_of_fixpoint {A : Type} (P : Poset A) {F : A → A} {x : A}
    (fpx : Fixpoint F x) :
    Posfixpoint P.R F x := by
  unfold Posfixpoint
  unfold Fixpoint at fpx
  rw [fpx]
  apply P.po.left

lemma fixpoint_of_pre_pos {A : Type} (P : Poset A) {F : A → A} {x : A}
    (preF : Prefixpoint P.R F x) (posF : Posfixpoint P.R F x) :
    Fixpoint F x := by
  apply P.po.right.left
  exact ⟨posF, preF⟩

def GreatFixpoint {A : Type} (P : Poset A) (F : A → A) : Set A :=
  Fixpoint F ∩ (setOf (Fixpoint F)).UpperBound P.R

def LeastFixpoint {A : Type} (P : Poset A) (F : A → A) : Set A :=
  Fixpoint F ∩ (setOf (Fixpoint F)).LowerBound P.R

theorem fixpointKnasterTarski {A : Type} {P : Poset A} {F : A → A}
    (hP : CompleteLatice P) (hF : Monoton P.R F) :
    -- the least upper bound of all prefixpoints (ŷ) is the (unique) great fixpoint
    UniqueMember (GreatFixpoint P F) (hP.supre (setOf (Prefixpoint P.R F))) ∧
    -- the great lower bound of all posfixpoints (ẑ) is the (unique) least fixpoint
    UniqueMember (LeastFixpoint P F) (hP.infim (setOf (Posfixpoint P.R F))) :=
by
  rcases P.po with ⟨refle, antis, tranz⟩
  have glb := hP.infim_is_GLB (setOf (Posfixpoint P.R F))
  have lub := hP.supre_is_LUB (setOf (Prefixpoint P.R F))
  set y := hP.supre (setOf (Prefixpoint P.R F))
  set z := hP.infim (setOf (Posfixpoint P.R F))
  sorry -- homework #2
