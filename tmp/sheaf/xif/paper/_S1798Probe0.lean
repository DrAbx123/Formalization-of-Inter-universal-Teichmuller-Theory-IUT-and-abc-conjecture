import Mathlib.RingTheory.Etale.Finite
import Mathlib.CategoryTheory.Galois.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
import Mathlib.CategoryTheory.Limits.FintypeCat
import Mathlib.CategoryTheory.Limits.Yoneda
import Mathlib.RingTheory.Etale.Field
import Mathlib.FieldTheory.AlgebraicClosure

noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace S1798P0

variable (K : Type) [Field K]

abbrev D : Type 1 := CommAlgCat.FiniteEtale.{0} K
abbrev C : Type 1 := D Kᵒᵖ
abbrev Om : D K := CommAlgCat.FiniteEtale.of K (AlgebraicClosure K)
abbrev F : C K ⥤ FintypeCat.{0} := CommAlgCat.FiniteEtale.fiber K (AlgebraicClosure K)

-- check the coyoneda identification
#check @coyoneda
example : (C K)ᵒᵖ = D K := rfl

def G : C K ⥤ Type := coyoneda.obj (C := C K) (Om K)

example (A : D K) : (F K ⋙ FintypeCat.incl).obj (Opposite.op A) = (G K).obj (Opposite.op A) := rfl

-- natural iso? try Iso.refl
example : F K ⋙ FintypeCat.incl ≅ G K := Iso.refl _

-- preservation via coyoneda
example : PreservesLimitsOfShape WalkingCospan (F K ⋙ FintypeCat.incl) := by
  haveI : PreservesLimitsOfShape WalkingCospan (G K) := inferInstance
  exact preservesLimitsOfShape_of_natIso (Iso.refl _)

example : PreservesLimitsOfShape WalkingCospan (F K) := by
  apply preservesLimitsOfShape_of_reflects_of_preserves (G := FintypeCat.incl)
  haveI : PreservesLimitsOfShape WalkingCospan (G K) := inferInstance
  exact preservesLimitsOfShape_of_natIso (Iso.refl _)

example : PreservesLimitsOfShape (Discrete PEmpty.{1}) (F K) := by
  apply preservesLimitsOfShape_of_reflects_of_preserves (G := FintypeCat.incl)
  haveI : PreservesLimitsOfShape (Discrete PEmpty.{1}) (G K) := inferInstance
  exact preservesLimitsOfShape_of_natIso (Iso.refl _)

end S1798P0
