import tmp.sheaf.xif.paper.Mzk1P3FLTCompletionInputActual
import tmp.sheaf.xif.paper.Mzk1P3AgreeDegreeActual
import tmp.sheaf.xif.paper.Mzk1P3WeightDegreeOneActual
import Mathlib.Tactic

/-! # CONDITIONAL: FLT finrank=1 => relativeCompletionDegree=1 => weight=1 -/

noncomputable section
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P3WeightDegreeOneFinrankActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.ProcessionNormalizationWeightsActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.Mzk1P3AgreeDegreeActual
open LeanFormal.IUT.XiFPaper.Mzk1P3FLTCompletionInputActual
open LeanFormal.IUT.XiFPaper.Mzk1P3WeightDegreeOneActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- FLT finrank input with finrank=1 gives relativeCompletionDegree=1. -/
theorem relativeCompletionDegree_eq_one_of_FLT_finrank_one
    (b : Bad (nativePlaceSelection T))
    (hFLT : FLTCompletionFinrankInput (k := T.arithmetic.Fmod) (nativeBadToKPlace T b))
    (hfin : Module.finrank
      ((comap (k := T.arithmetic.Fmod) (nativeBadToKPlace T b)).maximalIdeal.adicCompletion
        T.arithmetic.Fmod)
      ((nativeBadToKPlace T b).maximalIdeal.adicCompletion T.arithmetic.K) = 1) :
    relativeCompletionDegree (k := T.arithmetic.Fmod) (nativeBadToKPlace T b) = 1 := by
  rw [relativeCompletionDegree_eq_finrank_of_FLT (k := T.arithmetic.Fmod)
    (nativeBadToKPlace T b) hFLT, hfin]

/-- FLT finrank input + FINITE + AGREE + finrank=1 gives weight=1. -/
theorem nativeBadLocalWeight_eq_one_of_FLT_finrank_one
    (b : Bad (nativePlaceSelection T))
    (hfinite : Module.Finite
      ((comap (k := T.arithmetic.Fmod) (nativeBadToKPlace T b)).maximalIdeal.adicCompletionIntegers
        T.arithmetic.Fmod)
      ((nativeBadToKPlace T b).maximalIdeal.adicCompletionIntegers T.arithmetic.K))
    (hagree : localDataAgreesWithPlaceData (k := T.arithmetic.Fmod) (nativeBadToKPlace T b))
    (hFLT : FLTCompletionFinrankInput (k := T.arithmetic.Fmod) (nativeBadToKPlace T b))
    (hfin : Module.finrank
      ((comap (k := T.arithmetic.Fmod) (nativeBadToKPlace T b)).maximalIdeal.adicCompletion
        T.arithmetic.Fmod)
      ((nativeBadToKPlace T b).maximalIdeal.adicCompletion T.arithmetic.K) = 1) :
    nativeBadLocalWeight T b = 1 := by
  have hrel : relativeCompletionDegree (k := T.arithmetic.Fmod)
      (nativeBadToKPlace T b) = 1 := by
    rw [relativeCompletionDegree_eq_finrank_of_FLT (k := T.arithmetic.Fmod)
      (nativeBadToKPlace T b) hFLT, hfin]
  exact nativeBadLocalWeight_eq_one_of_relativeDegree_one (l := l) T b
    hfinite hagree hrel

#check relativeCompletionDegree_eq_one_of_FLT_finrank_one
#check nativeBadLocalWeight_eq_one_of_FLT_finrank_one
end LeanFormal.IUT.XiFPaper.Mzk1P3WeightDegreeOneFinrankActual
end
