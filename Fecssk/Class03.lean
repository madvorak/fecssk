import Fecssk.Class02


def SupreContinuous {A : Type} {P : Poset A} (hP : CompleteLatice P) (F : A → A) : Prop :=
  ∀ s : ℕ → A, (∀ n : ℕ, P.R (s n) (s n.succ)) →
    F (hP.supre { s n | n : ℕ }) = hP.supre { F (s n) | n : ℕ }

def InfimContinuous {A : Type} {P : Poset A} (hP : CompleteLatice P) (F : A → A) : Prop :=
  ∀ s : ℕ → A, (∀ n : ℕ, P.R (s n.succ) (s n)) →
    F (hP.infim { s n | n : ℕ }) = hP.infim { F (s n) | n : ℕ }

lemma CompleteLatice.supre_pair {A : Type} {P : Poset A} (hP : CompleteLatice P) (a b : A) :
    hP.supre {a, b} = b ↔ P.R a b := by
  obtain ⟨upp, lea⟩ := hP.supre_is_LUB {a, b}
  constructor
  · intro supr
    rw [supr] at upp
    exact upp a (by simp)
  · intro hab
    apply P.po.right.left
    constructor
    · apply lea
      simp [Set.UpperBound]
      constructor
      · exact hab
      · apply P.po.left
    · exact upp b (by simp)

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
  rw [show CompleteLatice.supre hP {x, y} = y by rwa [hP.supre_pair x y]] at supr
  rw [← hP.supre_pair]
  exact supr.symm

-- ## Homework #3

theorem leastFixpoint_of_supreContinuous {A : Type} {P : Poset A} {F : A → A}
    (hP : CompleteLatice P) (hF : SupreContinuous hP F) :
    LeastFixpoint P F (hP.supre { F^[i] hP.bot | i : ℕ }) := by
  sorry -- homework #3 (part 1)

theorem greatFixpoint_of_infimContinuous {A : Type} {P : Poset A} {F : A → A}
    (hP : CompleteLatice P) (hF : InfimContinuous hP F) :
    GreatFixpoint P F (hP.infim { F^[i] hP.top | i : ℕ }) := by
  sorry -- homework #3 (part 2)


-- ## Homework #4

-- Let `S` be the largest `X ⊆ 𝒫({0,1}^ω)` such that `X ⊆ 01X ∪ 10X`.
-- Prove `∀ x : {0,1}^ω` , `x ∈ S` ↔ every finite prefix of `x` of even length has #`0` = #`1`.
-- We need to prove `←` by coïnduction on `S` and prove `→` by induction on `ℕ` (prefix lengths).
