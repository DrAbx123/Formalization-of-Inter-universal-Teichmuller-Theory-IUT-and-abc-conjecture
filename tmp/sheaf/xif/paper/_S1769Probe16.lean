import Mathlib.RingTheory.Etale.Finite
import Mathlib.CategoryTheory.Galois.Basic
import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks

noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace S1769Probe

abbrev C (K : Type) [Field K] : Type 1 := (CommAlgCat.FiniteEtale.{0} K)ᵒᵖ
abbrev bc (K : Type) [Field K] : CommAlgCat.FiniteEtale.{0} K ⥤ CommAlgCat.FiniteEtale.{0} (AlgebraicClosure K) :=
  CommAlgCat.FiniteEtale.baseChange K (AlgebraicClosure K)
abbrev E (K : Type) [Field K] : (CommAlgCat.FiniteEtale.{0} (AlgebraicClosure K))ᵒᵖ ⥤ FintypeCat.{0} :=
  CommAlgCat.FiniteEtale.fiber (AlgebraicClosure K) (AlgebraicClosure K)

variable {K : Type} [Field K]
example (h : PreservesLimitsOfShape WalkingCospan (bc K).op) :
    PreservesLimitsOfShape WalkingCospan ((bc K).op ⋙ E K) := by
  haveI := h
  haveI : PreservesLimitsOfShape WalkingCospan (E K) := inferInstance
  infer_instance

example (h : PreservesFiniteProducts (bc K)) : PreservesFiniteCoproducts ((bc K).op ⋙ E K) := by
  haveI := h
  haveI : PreservesFiniteCoproducts (bc K).op := preservesFiniteCoproducts_op (bc K)
  haveI : PreservesFiniteCoproducts (E K) := inferInstance
  infer_instance

end S1769Probe