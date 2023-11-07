/-
# Propositional (boolean) logic

Syntax → proof theory

Semantics → model theory
-/

def boolGate (n : Nat) : Type := (Fin n → Bool) → Bool

def boolTop : boolGate 0 := fun _ => true

def boolBot : boolGate 0 := fun _ => false

def boolNot : boolGate 1 := fun x => !(x 0)

def boolAnd : boolGate 2 := fun x => x 0 && x 1

def boolOri : boolGate 2 := fun x => x 0 || x 1

def boolEqi : boolGate 2 := fun x => x 0 == x 1

def boolImp : boolGate 2 := fun x => !(x 0) || x 1

-- Homework: show that resolution is sound and complete.
