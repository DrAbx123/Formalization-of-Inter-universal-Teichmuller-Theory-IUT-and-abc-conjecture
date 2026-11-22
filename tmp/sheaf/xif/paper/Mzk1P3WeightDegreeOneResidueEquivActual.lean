import tmp.sheaf.xif.paper.Mzk1C17ResidueFieldEquivActual
import tmp.sheaf.xif.paper.Mzk1P3WeightDegreeOneActual
import Mathlib.Tactic

/-! # CONDITIONAL: ResidueFieldEquiv + UNRAM + FINITE + AGREE => weight=1 -/

noncomputable section
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P3WeightDegreeOneResidueEquivActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.ProcessionNormalizationWeightsActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.Mzk1C17ResidueFieldEquivActual
open LeanFormal.IUT.XiFPaper.Mzk1P3WeightDegreeOneActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Residue-field equivalence at a native bad place gives relative residue degree one. -/
theorem relativeResidueDegree_eq_one_of_residueFieldEquiv
    (b : Bad (nativePlaceSelection T))
    (h : ResidueFieldEquiv
      (p := (comap (k := T.arithmetic.Fmod) (nativeBadToKPlace T b)).maximalIdeal.asIdeal)
      (P := (nativeBadToKPlace T b).maximalIdeal.asIdeal)) :
    relativeResidueDegree (k := T.arithmetic.Fmod) (nativeBadToKPlace T b) = 1 := by
  unfold relativeResidueDegree
  exact inertiaDeg'_eq_one_of_residueFieldEquiv h

/-- ResidueFieldEquiv + UNRAM + FINITE + AGREE => nativeBadLocalWeight=1. -/
theorem nativeBadLocalWeight_eq_one_of_residueEquiv_unram
    (b : Bad (nativePlaceSelection T))
    (hfinite : Module.Finite
      ((comap (k := T.arithmetic.Fmod) (nativeBadToKPlace T b)).maximalIdeal.adicCompletionIntegers
        T.arithmetic.Fmod)
      ((nativeBadToKPlace T b).maximalIdeal.adicCompletionIntegers T.arithmetic.K))
    (hagree : localDataAgreesWithPlaceData (k := T.arithmetic.Fmod) (nativeBadToKPlace T b))
    (hunram : relativeRamificationIndex (k := T.arithmetic.Fmod) (nativeBadToKPlace T b) = 1)
    (hres : ResidueFieldEquiv
      (p := (comap (k := T.arithmetic.Fmod) (nativeBadToKPlace T b)).maximalIdeal.asIdeal)
      (P := (nativeBadToKPlace T b).maximalIdeal.asIdeal)) :
    nativeBadLocalWeight T b = 1 :=
  nativeBadLocalWeight_eq_one_of_unram_residue (l := l) T b hfinite hagree hunram
    (relativeResidueDegree_eq_one_of_residueFieldEquiv (l := l) T b hres)

#check relativeResidueDegree_eq_one_of_residueFieldEquiv
#check nativeBadLocalWeight_eq_one_of_residueEquiv_unram
end LeanFormal.IUT.XiFPaper.Mzk1P3WeightDegreeOneResidueEquivActual
end
