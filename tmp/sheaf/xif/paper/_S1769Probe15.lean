import Mathlib.RingTheory.Etale.Finite
import Mathlib.CategoryTheory.Galois.Basic
import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.CategoryTheory.Limits.Preserves.Finite

noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace S1769Probe

abbrev E (K : Type) [Field K] :
    (CommAlgCat.FiniteEtale.{0} (AlgebraicClosure K))ᵒᵖ ⥤ FintypeCat.{0} :=
  CommAlgCat.FiniteEtale.fiber (AlgebraicClosure K) (AlgebraicClosure K)

variable {K : Type} [Field K]
example : (E K).IsEquivalence := by infer_instance
example : PreservesLimits (E K) := by infer_instance
example : PreservesLimitsOfShape WalkingCospan (E K) := by infer_instance
example : PreservesFiniteCoproducts (E K) := by infer_instance
example : Functor.PreservesEpimorphisms (E K) := by infer_instance
example : PreservesColimitsOfShape (SingleObj (Equiv.Perm (Fin 2))) (E K) := by infer_instance

end S1769Probe