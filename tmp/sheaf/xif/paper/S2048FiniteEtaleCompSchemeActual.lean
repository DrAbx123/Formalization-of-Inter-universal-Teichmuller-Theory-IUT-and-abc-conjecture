import tmp.sheaf.xif.paper.S2046FiniteEtaleAPIGapActual
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! # S2048: scheme-level finite-etale composition (API step 3)

Implements the scheme-level closure needed by the pasted projection of the
composition API: Mathlib has `IsFinite` and `Etale` stable under composition,
so `IsFinite f ∧ Etale f` and `IsFinite g ∧ Etale g` give the same for `f ≫ g`.

The remaining stack-level APIs (presentation composition, TwoPullbackWitness
pasting, iso-invariance, toA certificate) are not faked here; see S2046/S2042
reports for the exact missing lemma list.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2048FiniteEtaleCompSchemeActual

open AlgebraicGeometry

universe u
variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- Scheme-level composition of finite-etale morphisms. -/
theorem S2048_isFinite_and_etale_comp
    [IsFinite f] [Etale f] [IsFinite g] [Etale g] :
    IsFinite (CategoryTheory.CategoryStruct.comp f g) ∧ Etale (CategoryTheory.CategoryStruct.comp f g) :=
  ⟨inferInstance, inferInstance⟩

/-- The same closure as a single `Prop`-free pair, for the pasted projection. -/
theorem S2048_isFinite_and_etale_comp_apply
    [IsFinite f] [Etale f] [IsFinite g] [Etale g] :
    IsFinite (CategoryTheory.CategoryStruct.comp f g) := by
  infer_instance

#print axioms S2048_isFinite_and_etale_comp
#print axioms S2048_isFinite_and_etale_comp_apply

end LeanFormal.IUT.XiFPaper.S2048FiniteEtaleCompSchemeActual

end
