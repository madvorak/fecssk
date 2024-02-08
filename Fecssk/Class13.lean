prelude

variable {α : Type}

def Tru := λ x : α => λ _ : α => x
def Fal := λ _ : α => λ x : α => x

def _0_ := λ (f : α → α) => λ (x : α) => x
def _1_ := λ (f : α → α) => λ (x : α) => f x
def _2_ := λ (f : α → α) => λ (x : α) => f (f x)
def _3_ := λ (f : α → α) => λ (x : α) => f (f (f x))
def _4_ := λ (f : α → α) => λ (x : α) => f (f (f (f x)))
def Suc := λ (n : (α → α) → α → α) => λ (f : α → α) => λ (x : α) => (f (n f x) : α)

#check @Suc α _2_
#check @_3_ α
