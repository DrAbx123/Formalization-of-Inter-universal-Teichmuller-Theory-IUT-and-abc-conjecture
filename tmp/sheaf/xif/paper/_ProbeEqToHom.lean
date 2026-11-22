import Mathlib
open CategoryTheory
example {C : Type*} [Category C] (X : C) : eqToHom (by simp : X = X) = 𝟙 X := by simp
example {C : Type*} [Category C] (X : C) (h : X = X) : eqToHom h = 𝟙 X := by simp