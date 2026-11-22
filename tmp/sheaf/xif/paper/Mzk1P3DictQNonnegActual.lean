import tmp.sheaf.xif.paper.Mzk1P3DictQCoeffActual
import tmp.sheaf.xif.paper.GlobalQVFamThetaHullScalarActual
import tmp.sheaf.xif.paper.BaseQLogVolumeActual
import Mathlib.Tactic

/-! # GREEN: nativeQArith is nonnegative -/

noncomputable section
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P3DictQNonnegActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.Mzk1P3DictQCoeffActual
open LeanFormal.IUT.XiFPaper.Mzk1P3DictBArithActual
open LeanFormal.IUT.XiFPaper.GlobalQVFamThetaHullScalarActual
open LeanFormal.IUT.XiFPaper.BaseQLogVolumeActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.ProcessionNormalizationWeightsActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- nativeQArith is a sum of nonnegative weighted base-q magnitudes. -/
theorem nativeQArith_nonneg : 0 <= nativeQArith T := by
  rw [nativeQArith_eq_weighted_sum]
  apply Finset.sum_nonneg
  intro b _
  have hw : 0 <= nativeBadLocalWeight T b := by
    unfold nativeBadLocalWeight localNormalizedWeight
    exact inv_nonneg.mpr (Nat.cast_nonneg _)
  exact mul_nonneg hw (le_of_lt (baseQLogMagnitude_pos T b))

#check nativeQArith_nonneg
end LeanFormal.IUT.XiFPaper.Mzk1P3DictQNonnegActual
end
