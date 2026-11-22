import tmp.sheaf.xif.paper.VbadPlaceIndexingActual
import tmp.sheaf.xif.paper.ProcessionNormalizationWeightsActual
import Mathlib.Tactic

/-! # GAP: nativeBadLocalWeight=1 is exactly localCompletionDegree=1 -/

noncomputable section
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P3DictQWeightDegreeActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.ProcessionNormalizationWeightsActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Weight one is exactly local completion degree one (GAP-PC-WEIGHT form). -/
theorem nativeBadLocalWeight_eq_one_iff_degree_eq_one
    (b : Bad (nativePlaceSelection T)) :
    nativeBadLocalWeight T b = 1 ↔
      localCompletionDegree T.arithmetic (nativeBadToKPlace T b) = 1 := by
  unfold nativeBadLocalWeight localNormalizedWeight
  rw [inv_eq_one]
  constructor
  · intro h
    exact_mod_cast h
  · intro h
    rw [h]
    norm_num

/-- Weight one from degree one. -/
theorem nativeBadLocalWeight_eq_one_of_degree_eq_one
    (b : Bad (nativePlaceSelection T))
    (h : localCompletionDegree T.arithmetic (nativeBadToKPlace T b) = 1) :
    nativeBadLocalWeight T b = 1 :=
  (nativeBadLocalWeight_eq_one_iff_degree_eq_one (l := l) T b).mpr h

#check nativeBadLocalWeight_eq_one_iff_degree_eq_one
#check nativeBadLocalWeight_eq_one_of_degree_eq_one
end LeanFormal.IUT.XiFPaper.Mzk1P3DictQWeightDegreeActual
end
