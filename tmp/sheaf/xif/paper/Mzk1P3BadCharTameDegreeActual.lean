import tmp.sheaf.xif.paper.Mzk1P3WeightDegreeOneActual
import Mathlib.Tactic

/-! # GAP: tame local degree-one fragments (BADCHAR-DEG) -/

noncomputable section
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P3BadCharTameDegreeActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.ProcessionNormalizationWeightsActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.Mzk1P3WeightDegreeOneActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Tame local data: UNRAM=1 + RESIDUE=1 gives relative completion degree one. -/
theorem relativeCompletionDegree_eq_one_of_unram_residue
    (b : Bad (nativePlaceSelection T))
    (hunram : relativeRamificationIndex (k := T.arithmetic.Fmod) (nativeBadToKPlace T b) = 1)
    (hresidue : relativeResidueDegree (k := T.arithmetic.Fmod) (nativeBadToKPlace T b) = 1) :
    relativeCompletionDegree (k := T.arithmetic.Fmod) (nativeBadToKPlace T b) = 1 := by
  rw [relativeCompletionDegree_eq_one_iff]
  exact ⟨hunram, hresidue⟩

/-- Tame local data gives actual local completion degree one (FINITE+AGREE). -/
theorem localCompletionDegree_eq_one_of_unram_residue
    (b : Bad (nativePlaceSelection T))
    (hfinite : Module.Finite
      ((comap (k := T.arithmetic.Fmod) (nativeBadToKPlace T b)).maximalIdeal.adicCompletionIntegers
        T.arithmetic.Fmod)
      ((nativeBadToKPlace T b).maximalIdeal.adicCompletionIntegers T.arithmetic.K))
    (hagree : localDataAgreesWithPlaceData (k := T.arithmetic.Fmod) (nativeBadToKPlace T b))
    (hunram : relativeRamificationIndex (k := T.arithmetic.Fmod) (nativeBadToKPlace T b) = 1)
    (hresidue : relativeResidueDegree (k := T.arithmetic.Fmod) (nativeBadToKPlace T b) = 1) :
    localCompletionDegree T.arithmetic (nativeBadToKPlace T b) = 1 :=
  localCompletionDegree_eq_one_of_relativeDegree_one (l := l) T b hfinite hagree
    (relativeCompletionDegree_eq_one_of_unram_residue (l := l) T b hunram hresidue)

#check relativeCompletionDegree_eq_one_of_unram_residue
#check localCompletionDegree_eq_one_of_unram_residue
end LeanFormal.IUT.XiFPaper.Mzk1P3BadCharTameDegreeActual
end
