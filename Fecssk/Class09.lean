import Fecssk.Class06

section Hilbert

-- TODO generalize `Prop` to FOL
axiom _all_ : Char → Prop → Prop
prefix:99 " Ɐ " => _all_
-- note `→` vs `⇒` and `¬` vs `⌝` and `∀` vs `Ɐ`
-- above always, the former is recognized by Lean, the latter is for Hilbert proofs

axiom _1 (φ t : Prop) (x : Char) : ((Ɐx) φ) ⇒ φ -- TODO replacement of `x` by a term
axiom _2 (φ ψ : Prop) (x : Char) : ((Ɐx) (φ ⇒ ψ)) ⇒ ((Ɐx) φ) ⇒ ((Ɐx) ψ)
axiom _3 (φ t : Prop) (x : Char) : φ ⇒ ((Ɐx) φ)

end Hilbert
