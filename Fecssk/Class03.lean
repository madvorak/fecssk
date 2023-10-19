import Fecssk.Class02
import Mathlib.Data.Stream.Init


def SupreContinuous {A : Type} {P : Poset A} (hP : CompleteLatice P) (F : A → A) : Prop :=
  ∀ s : ℕ → A, (∀ n : ℕ, P.R (s n) (s n.succ)) →
    F (hP.supre { s n | n : ℕ }) = hP.supre { F (s n) | n : ℕ }

def InfimContinuous {A : Type} {P : Poset A} (hP : CompleteLatice P) (F : A → A) : Prop :=
  ∀ s : ℕ → A, (∀ n : ℕ, P.R (s n.succ) (s n)) →
    F (hP.infim { s n | n : ℕ }) = hP.infim { F (s n) | n : ℕ }

lemma CompleteLatice.supre_pair {A : Type} {P : Poset A} (hP : CompleteLatice P) (a b : A) :
    P.R a b ↔ hP.supre {a, b} = b := by
  obtain ⟨upb, lea⟩ := hP.supre_is_LUB {a, b}
  constructor
  · intro hab
    apply P.po.right.left
    constructor
    · apply lea
      simp [Set.UpperBound]
      constructor
      · exact hab
      · apply P.po.left
    · exact upb b (by simp)
  · intro supr
    rw [supr] at upb
    exact upb a (by simp)

lemma CompleteLatice.infim_pair {A : Type} {P : Poset A} (hP : CompleteLatice P) (a b : A) :
    P.R a b ↔ hP.infim {a, b} = a := by
  obtain ⟨lwb, gre⟩ := hP.infim_is_GLB {a, b}
  constructor
  · intro hab
    apply P.po.right.left
    constructor
    · exact lwb a (by simp)
    · apply gre
      simp [Set.UpperBound]
      constructor
      · apply P.po.left
      · exact hab
  · intro infm
    rw [infm] at lwb
    exact lwb b (by simp)

lemma monoton_of_supreContinuous {A : Type} {P : Poset A} {hP : CompleteLatice P} {F : A → A}
    (suprec : SupreContinuous hP F) :
    Monoton P.R F := by
  intro x y hxy
  specialize suprec
    (fun i => match i with
      | .zero => x
      | .succ _ => y
    )
    (by
      intro n
      cases n with
      | zero => convert hxy
      | succ n => convert P.po.left y
    )
  have supr : F (hP.supre {x, y}) = hP.supre {F x, F y}
  · convert suprec using 1 <;>
    · congr
      ext a
      simp only [Set.mem_singleton_iff, Set.mem_insert_iff, Set.mem_setOf_eq]
      constructor
      · intro hyp
        cases hyp with
        | inl hax =>
          use 0
          simp [hax]
        | inr hay =>
          use 1
          simp [hay]
      · rintro ⟨n, hyp⟩
        cases n with
        | zero =>
          left
          exact hyp.symm
        | succ n =>
          right
          exact hyp.symm
  rw [hP.supre_pair] at hxy ⊢
  rw [hxy] at supr
  rw [← supr]

lemma monoton_of_infimContinuous {A : Type} {P : Poset A} {hP : CompleteLatice P} {F : A → A}
    (infimc : InfimContinuous hP F) :
    Monoton P.R F := by
  intro x y hxy
  specialize infimc
    (fun i => match i with
      | .zero => y
      | .succ _ => x
    )
    (by
      intro n
      cases n with
      | zero => convert hxy
      | succ n => convert P.po.left x
    )
  have infm : F (hP.infim {x, y}) = hP.infim {F x, F y}
  · convert infimc using 1 <;>
    · congr
      ext a
      simp only [Set.mem_singleton_iff, Set.mem_insert_iff, Set.mem_setOf_eq]
      constructor
      · intro hyp
        cases hyp with
        | inl hax =>
          use 1
          simp [hax]
        | inr hay =>
          use 0
          simp [hay]
      · rintro ⟨n, hyp⟩
        cases n with
        | zero =>
          right
          exact hyp.symm
        | succ n =>
          left
          exact hyp.symm
  rw [hP.infim_pair] at hxy ⊢
  rw [hxy] at infm
  rw [← infm]

-- ## Homework #3

theorem leastFixpoint_of_supreContinuous {A : Type} {P : Poset A} {F : A → A}
    (hP : CompleteLatice P) (hF : SupreContinuous hP F) :
    LeastFixpoint P F (hP.supre { F^[i] hP.bot | i : ℕ }) :=
by
  sorry -- homework #3 (part 1)

theorem greatFixpoint_of_infimContinuous {A : Type} {P : Poset A} {F : A → A}
    (hP : CompleteLatice P) (hF : InfimContinuous hP F) :
    GreatFixpoint P F (hP.infim { F^[i] hP.top | i : ℕ }) :=
by
  sorry -- homework #3 (part 2)


-- ## Homework #4

namespace infinite_words

abbrev IW := Stream' (Fin 2)

-- Let `S` be the largest `X ⊆ 𝒫({0,1}^ω)` such that `X ⊆ 01X ∪ 10X`.

def S : Set IW := fun w =>
  ∃ X : Set IW, -- Alex Keizer's union-of-all-prefixpoints trick!
    w ∈ X ∧
    X ⊆ (Stream'.cons 0 '' (Stream'.cons 1 '' X)) ∪ (Stream'.cons 1 '' (Stream'.cons 0 '' X))

-- Prove `∀ x : {0,1}^ω` , `x ∈ S` ↔ every finite prefix of `x` of even length has #`0` = #`1`.

example : ∀ x : IW, x ∈ S ↔ ∀ n : ℕ, (x.take (2*n)).count 0 = (x.take (2*n)).count 1 := by
  intro x
  constructor
  · sorry
  · intro hyp
    -- Mario Carneiro's co-induction trick!
    refine ⟨{ x | ∀ n : ℕ, (x.take (2*n)).count 0 = (x.take (2*n)).count 1 }, hyp, ?_⟩
    sorry

end infinite_words
