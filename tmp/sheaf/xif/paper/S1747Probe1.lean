import Mathlib.RingTheory.Etale.Finite
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Artinian.Module
import Mathlib.CategoryTheory.Galois.Basic

open CategoryTheory

universe u

namespace S1747Probe

variable (K : Type) [Field K]

example (A : CommAlgCat.FiniteEtale.{0} K) : IsReduced A :=
  Algebra.FormallyUnramified.isReduced_of_field K A

noncomputable example (A : CommAlgCat.FiniteEtale.{0} K) (m : MaximalSpectrum A) :
    Field (A ⧸ m.asIdeal) :=
  Ideal.Quotient.field m.asIdeal

example (A : CommAlgCat.FiniteEtale.{0} K) (m : MaximalSpectrum A) :
    Algebra.Etale K (A ⧸ m.asIdeal) := by
  letI : Field (A ⧸ m.asIdeal) := Ideal.Quotient.field m.asIdeal
  haveI : IsReduced A := Algebra.FormallyUnramified.isReduced_of_field K A
  refine { formallyEtale := ?_, finitePresentation := ?_ }
  · exact (Algebra.FormallyEtale.iff_isSeparable K (A ⧸ m.asIdeal)).mpr inferInstance
  · exact (Algebra.FinitePresentation.of_finiteType (R := K)).mp inferInstance

example (A : CommAlgCat.FiniteEtale.{0} K) : IsSemisimpleRing A := by
  haveI : IsReduced A := Algebra.FormallyUnramified.isReduced_of_field K A
  exact IsArtinianRing.isSemisimpleRing_of_isReduced A

end S1747Probe
