import Mathlib.RingTheory.Etale.Finite
import Mathlib.CategoryTheory.Galois.Basic
import Mathlib.CategoryTheory.Functor.ReflectsIso.Basic
import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Etale.Field

noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace S1769Probe

abbrev C (K : Type) [Field K] : Type 1 := (CommAlgCat.FiniteEtale.{0} K)ᵒᵖ
abbrev D (K : Type) [Field K] : Type 1 := (CommAlgCat.FiniteEtale.{0} (AlgebraicClosure K))ᵒᵖ

variable {K : Type} [Field K]

abbrev F (K : Type) [Field K] : C K ⥤ FintypeCat.{0} := CommAlgCat.FiniteEtale.fiber K (AlgebraicClosure K)

abbrev bc (K : Type) [Field K] : CommAlgCat.FiniteEtale.{0} K ⥤ CommAlgCat.FiniteEtale.{0} (AlgebraicClosure K) :=
  CommAlgCat.FiniteEtale.baseChange K (AlgebraicClosure K)

abbrev E (K : Type) [Field K] : D K ⥤ FintypeCat.{0} :=
  CommAlgCat.FiniteEtale.fiber (AlgebraicClosure K) (AlgebraicClosure K)

example : (E K).IsEquivalence := by infer_instance
example : (E K).ReflectsIsomorphisms := by infer_instance

def alpha (K : Type) [Field K] : F K ≅ (bc K).op ⋙ E K :=
  CommAlgCat.FiniteEtale.fiberIsoBaseChangeFiber (R := K) (Ω := AlgebraicClosure K) (S := AlgebraicClosure K)

end S1769Probe