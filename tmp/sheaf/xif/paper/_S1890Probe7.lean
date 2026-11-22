import Mathlib.CategoryTheory.Comma.Basic
open CategoryTheory

namespace T6
variable (n : Nat)
def foo3 : Nat := n
#check @foo3
theorem foo4 : True := by have h : Nat := n; trivial
end T6

namespace T7
variable {A : Type} [Category A]
variable (sq : ∀ (x : A), x = x)
def foo5 (X : A) : X = X := sq X
#check @foo5
end T7

namespace T8
variable {A : Type} [Category A]
variable (sq : ∀ (x : A), x = x)
theorem foo6 (X : A) : X = X := by exact sq X
#check @foo6
end T8
