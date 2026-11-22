
import Mathlib.RingTheory.Etale.Finite
import Mathlib.CategoryTheory.Galois.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.FieldTheory.AbsoluteGaloisGroup

noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace S1769Probe

abbrev C (K : Type) [Field K] : Type 1 := (CommAlgCat.FiniteEtale.{0} K)ᵒᵖ

abbrev F (K : Type) [Field K] : C K ⥤ FintypeCat.{0} := CommAlgCat.FiniteEtale.fiber K (AlgebraicClosure K)

variable {K : Type} [Field K] [PreGaloisCategory (C K)]

example : PreservesLimitsOfShape (Discrete PEmpty.{1}) (F K) := by infer_instance
example : PreservesLimitsOfShape WalkingCospan (F K) := by infer_instance
example : PreservesFiniteCoproducts (F K) := by infer_instance
example : Functor.PreservesEpimorphisms (F K) := by infer_instance
example (G : Type) [Group G] [Finite G] : PreservesColimitsOfShape (SingleObj G) (F K) := by infer_instance
example : (F K).ReflectsIsomorphisms := by infer_instance

end S1769Probe
