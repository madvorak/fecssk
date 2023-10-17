import Fecssk.Class02


def SupreContinuous {A : Type} {P : Poset A} (hP : CompleteLatice P) (F : A → A) : Prop :=
  ∀ s : ℕ → A, (∀ n : ℕ, P.R (s n) (s n.succ)) →
    F (hP.supre { s n | n : ℕ }) = hP.supre { F (s n) | n : ℕ }

def InfimContinuous {A : Type} {P : Poset A} (hP : CompleteLatice P) (F : A → A) : Prop :=
  ∀ s : ℕ → A, (∀ n : ℕ, P.R (s n.succ) (s n)) →
    F (hP.infim { s n | n : ℕ }) = hP.infim { F (s n) | n : ℕ }

-- ## Homework #3

theorem greatFixpoint_of_supreContinuous {A : Type} {P : Poset A} {F : A → A}
    (hP : CompleteLatice P) (hF : SupreContinuous hP F) :
    GreatFixpoint P F (hP.supre { F^[i] hP.bot | i : ℕ }) := by
  sorry -- homework #3a

theorem leastFixpoint_of_infimContinuous {A : Type} {P : Poset A} {F : A → A}
    (hP : CompleteLatice P) (hF : InfimContinuous hP F) :
    LeastFixpoint P F (hP.infim { F^[i] hP.bot | i : ℕ }) := by
  sorry -- homework #3b


-- ## Homework #4

-- Let `S` be the largest `X ⊆ 𝒫({0,1}^ω)` such that `X ⊆ 01X ∪ 10X`.
-- Prove `∀ x : {0,1}^ω` , `x ∈ S` ↔ every finite prefix of `x` of even length has #`0` = #`1`.
-- We need to prove `←` by coïnduction on `S` and prove `→` by induction on `ℕ` (prefix lengths).
