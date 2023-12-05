import Fecssk.Class06

section Hilbert

-- TODO generalize `Prop` to FOL formulas
axiom _all_ : Char → Prop → Prop
prefix:30 " Ɐ " => _all_
abbrev _exists_ (x : Char) (φ : Prop) := ((Ɐx) (φ ⇒ F)) ⇒ F
prefix:30 " Ǝ " => _exists_
-- note `→` vs `⇒` and `∀` vs `Ɐ` and `∃` vs `Ǝ`
-- in symbols above, always, the former is recognized by Lean, the latter is for Hilbert proofs

axiom _1 (φ : Prop) (x : Char) : ((Ɐx) φ) ⇒ φ -- TODO replacement of `x` by a term
axiom _2 (φ ψ : Prop) (x : Char) : ((Ɐx) (φ ⇒ ψ)) ⇒ ((Ɐx) φ) ⇒ ((Ɐx) ψ)
axiom _3 (φ : Prop) (x : Char) : φ ⇒ ((Ɐx) φ)

end Hilbert
