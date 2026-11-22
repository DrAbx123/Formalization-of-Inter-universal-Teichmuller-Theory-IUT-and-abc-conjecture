import tmp.sheaf.xif.paper.Mzk1P3DictQCoeffActual
import Mathlib.Tactic

/-! # GAP: exact weighted-minus-unweighted q difference -/

noncomputable section
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P3DictQWeightDiffActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.Mzk1P3DictQCoeffActual
open LeanFormal.IUT.XiFPaper.Mzk1P3DictBArithActual
open LeanFormal.IUT.XiFPaper.BaseQLogVolumeActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- nativeQArith - baseQTotal = sum (weight-1)*baseQLogMagnitude. -/
theorem nativeQArith_sub_baseQTotal_eq :
    nativeQArith T - baseQTotalLogMagnitude T =
      ∑ b : Bad (nativePlaceSelection T),
        (nativeBadLocalWeight T b - 1) * baseQLogMagnitude T b := by
  rw [nativeQArith_eq_weighted_sum, baseQTotalLogMagnitude_eq_sum,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- QHALF is exactly the vanishing of the weighted difference. -/
theorem gap_QHALF_iff_weighted_diff_zero :
    GAP_PC_QHALF (l := l) T <->
      (∑ b : Bad (nativePlaceSelection T),
        (nativeBadLocalWeight T b - 1) * baseQLogMagnitude T b) = 0 := by
  unfold GAP_PC_QHALF
  constructor
  · intro h
    rw [← nativeQArith_sub_baseQTotal_eq (l := l) T]
    exact sub_eq_zero.mpr h
  · intro hzero
    have hsub : nativeQArith T - baseQTotalLogMagnitude T = 0 := by
      rw [nativeQArith_sub_baseQTotal_eq (l := l) T]
      exact hzero
    exact sub_eq_zero.mp hsub

#check nativeQArith_sub_baseQTotal_eq
#check gap_QHALF_iff_weighted_diff_zero
end LeanFormal.IUT.XiFPaper.Mzk1P3DictQWeightDiffActual
end
