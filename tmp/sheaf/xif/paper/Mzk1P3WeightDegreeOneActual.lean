import tmp.sheaf.xif.paper.Mzk1P3AgreeDegreeActual
import tmp.sheaf.xif.paper.Mzk1P3DictQWeightDegreeActual
import tmp.sheaf.xif.paper.VbadPlaceIndexingActual
import Mathlib.Tactic

/-! # CONDITIONAL: GAP-PC-WEIGHT from UNRAM/RESIDUE + AGREE/FINITE -/

noncomputable section
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P3WeightDegreeOneActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.ProcessionNormalizationWeightsActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.Mzk1P3AgreeDegreeActual
open LeanFormal.IUT.XiFPaper.Mzk1P3DictQWeightDegreeActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Relative degree one implies actual local completion degree one. -/
theorem localCompletionDegree_eq_one_of_relativeDegree_one
    (b : Bad (nativePlaceSelection T))
    (hfinite : Module.Finite
      ((comap (k := T.arithmetic.Fmod) (nativeBadToKPlace T b)).maximalIdeal.adicCompletionIntegers
        T.arithmetic.Fmod)
      ((nativeBadToKPlace T b).maximalIdeal.adicCompletionIntegers T.arithmetic.K))
    (hagree : localDataAgreesWithPlaceData (k := T.arithmetic.Fmod) (nativeBadToKPlace T b))
    (hrel : relativeCompletionDegree (k := T.arithmetic.Fmod) (nativeBadToKPlace T b) = 1) :
    localCompletionDegree T.arithmetic (nativeBadToKPlace T b) = 1 := by
  rw [localCompletionDegree_eq_relativeCompletionDegree_of_agree T.arithmetic
    (nativeBadToKPlace T b) hfinite hagree, hrel]

/-- Relative completion degree one gives nativeBadLocalWeight one. -/
theorem nativeBadLocalWeight_eq_one_of_relativeDegree_one
    (b : Bad (nativePlaceSelection T))
    (hfinite : Module.Finite
      ((comap (k := T.arithmetic.Fmod) (nativeBadToKPlace T b)).maximalIdeal.adicCompletionIntegers
        T.arithmetic.Fmod)
      ((nativeBadToKPlace T b).maximalIdeal.adicCompletionIntegers T.arithmetic.K))
    (hagree : localDataAgreesWithPlaceData (k := T.arithmetic.Fmod) (nativeBadToKPlace T b))
    (hrel : relativeCompletionDegree (k := T.arithmetic.Fmod) (nativeBadToKPlace T b) = 1) :
    nativeBadLocalWeight T b = 1 :=
  nativeBadLocalWeight_eq_one_of_degree_eq_one (l := l) T b
    (localCompletionDegree_eq_one_of_relativeDegree_one (l := l) T b hfinite hagree hrel)

/-- GAP-PC-WEIGHT from UNRAM + RESIDUE + AGREE + FINITE. -/
theorem nativeBadLocalWeight_eq_one_of_unram_residue
    (b : Bad (nativePlaceSelection T))
    (hfinite : Module.Finite
      ((comap (k := T.arithmetic.Fmod) (nativeBadToKPlace T b)).maximalIdeal.adicCompletionIntegers
        T.arithmetic.Fmod)
      ((nativeBadToKPlace T b).maximalIdeal.adicCompletionIntegers T.arithmetic.K))
    (hagree : localDataAgreesWithPlaceData (k := T.arithmetic.Fmod) (nativeBadToKPlace T b))
    (hunram : relativeRamificationIndex (k := T.arithmetic.Fmod) (nativeBadToKPlace T b) = 1)
    (hresidue : relativeResidueDegree (k := T.arithmetic.Fmod) (nativeBadToKPlace T b) = 1) :
    nativeBadLocalWeight T b = 1 := by
  have hrel : relativeCompletionDegree (k := T.arithmetic.Fmod)
      (nativeBadToKPlace T b) = 1 := by
    rw [relativeCompletionDegree_eq_one_iff]
    exact ⟨hunram, hresidue⟩
  exact nativeBadLocalWeight_eq_one_of_relativeDegree_one (l := l) T b
    hfinite hagree hrel

#check localCompletionDegree_eq_one_of_relativeDegree_one
#check nativeBadLocalWeight_eq_one_of_relativeDegree_one
#check nativeBadLocalWeight_eq_one_of_unram_residue
end LeanFormal.IUT.XiFPaper.Mzk1P3WeightDegreeOneActual
end
