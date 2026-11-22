import Mathlib.Logic.Equiv.Basic
import Mathlib.CategoryTheory.Category.Basic
noncomputable section
universe u
namespace LeanFormal.IUT.XiFPaper.S2867CastEqHelperActual

/-- cast along a self-equality is identity. -/
theorem cast_self_eq {α : Sort u} (h : α = α) (a : α) : cast h a = a := by
  cases h
  rfl

#check cast_self_eq

#print axioms cast_self_eq


end LeanFormal.IUT.XiFPaper.S2867CastEqHelperActual
