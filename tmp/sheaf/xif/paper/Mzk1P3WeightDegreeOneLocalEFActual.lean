import tmp.sheaf.xif.paper.Mzk1P3WeightDegreeOneActual
import Mathlib.Tactic

/-! # CONDITIONAL: local e=1 and local f=1 imply weight=1 -/

noncomputable section
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P3WeightDegreeOneLocalEFActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.ProcessionNormalizationWeightsActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.Mzk1P3WeightDegreeOneActual
open LeanFormal.IUT.XiFPaper.Mzk1P3DictQWeightDegreeActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Local e=1 and local f=1, plus FINITE+AGREE, give local completion degree one. -/
theorem localCompletionDegree_eq_one_of_local_unram_residue
    (b : Bad (nativePlaceSelection T))
    (hfinite : Module.Finite
      ((comap (k := T.arithmetic.Fmod) (nativeBadToKPlace T b)).maximalIdeal.adicCompletionIntegers
        T.arithmetic.Fmod)
      ((nativeBadToKPlace T b).maximalIdeal.adicCompletionIntegers T.arithmetic.K))
    (hagree : localDataAgreesWithPlaceData (k := T.arithmetic.Fmod) (nativeBadToKPlace T b))
    (he : localRamificationIndex (k := T.arithmetic.Fmod) (nativeBadToKPlace T b) = 1)
    (hf : localInertiaDegree (k := T.arithmetic.Fmod) (nativeBadToKPlace T b) = 1) :
    localCompletionDegree T.arithmetic (nativeBadToKPlace T b) = 1 := by
  have hrel : relativeCompletionDegree (k := T.arithmetic.Fmod)
      (nativeBadToKPlace T b) = 1 := by
    unfold relativeCompletionDegree
    rw [← hagree.1, ← hagree.2, he, hf]
  exact localCompletionDegree_eq_one_of_relativeDegree_one (l := l) T b hfinite hagree hrel

/-- Local e=1 and local f=1, plus FINITE+AGREE, give nativeBadLocalWeight=1. -/
theorem nativeBadLocalWeight_eq_one_of_local_unram_residue
    (b : Bad (nativePlaceSelection T))
    (hfinite : Module.Finite
      ((comap (k := T.arithmetic.Fmod) (nativeBadToKPlace T b)).maximalIdeal.adicCompletionIntegers
        T.arithmetic.Fmod)
      ((nativeBadToKPlace T b).maximalIdeal.adicCompletionIntegers T.arithmetic.K))
    (hagree : localDataAgreesWithPlaceData (k := T.arithmetic.Fmod) (nativeBadToKPlace T b))
    (he : localRamificationIndex (k := T.arithmetic.Fmod) (nativeBadToKPlace T b) = 1)
    (hf : localInertiaDegree (k := T.arithmetic.Fmod) (nativeBadToKPlace T b) = 1) :
    nativeBadLocalWeight T b = 1 :=
  nativeBadLocalWeight_eq_one_of_degree_eq_one (l := l) T b
    (localCompletionDegree_eq_one_of_local_unram_residue (l := l) T b
      hfinite hagree he hf)

#check localCompletionDegree_eq_one_of_local_unram_residue
#check nativeBadLocalWeight_eq_one_of_local_unram_residue
end LeanFormal.IUT.XiFPaper.Mzk1P3WeightDegreeOneLocalEFActual
end
