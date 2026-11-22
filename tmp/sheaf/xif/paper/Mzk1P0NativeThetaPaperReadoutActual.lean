/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1P0NativeComparisonLatticeActual
import tmp.sheaf.xif.paper.Mzk1HullUBPaperVRawBindingActual
import tmp.sheaf.xif.paper.S1915ThetaHullA0Actual
import Mathlib.Tactic
/-! #1 paper-faithful theta side: global q readout vs s1915ClosedForm -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P0NativeThetaPaperReadoutActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionFieldScalingActual
open LeanFormal.IUT.XiFPaper.Mzk1P0NativeComparisonLatticeActual
open LeanFormal.IUT.XiFPaper.Mzk1HullUBPaperVRawBindingActual
open LeanFormal.IUT.XiFPaper.S1915ThetaHullA0Actual
open scoped BigOperators
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
/-- Global native q readout: sum of the per-bad-place q readings. -/
noncomputable def nativeQReadoutGlobal : Real :=
  ∑ b : Bad (nativePlaceSelection T), nativeQReadout T b
/-- Per-block: global q readout is at most the sum of log lambda radii. -/
theorem nativeQReadoutGlobal_le_sum_log_radius :
    nativeQReadoutGlobal T ≤
      ∑ b : Bad (nativePlaceSelection T),
        Real.log (rootImageRadius T b : Real) := by
  unfold nativeQReadoutGlobal
  apply Finset.sum_le_sum
  intro b _
  have h := nativeQReadout_le_log_lambda T b
  have hlam : Real.log ‖(rootThetaFieldLambda T b : rootNormedExtension T b)‖ =
      Real.log (rootImageRadius T b : Real) := by
    rw [rootImageRadius_eq_norm_fieldLambda]
  rwa [hlam] at h
/-- Paper closed form in sum form. -/
theorem s1915ClosedForm_eq_one_add_sum :
    s1915ClosedForm T = 1 + ∑ b : Bad (nativePlaceSelection T),
      (s1915LocalDegree T b : Real) * Real.log (rootImageRadius T b : Real) :=
  paperV_eq_sum_add_beta T
/-- Net constant slack: sum (d_b-1)(-log r_b). -/
noncomputable def paperNetSlack : Real :=
  ∑ b : Bad (nativePlaceSelection T),
    ((s1915LocalDegree T b : Real) - 1) * (-Real.log (rootImageRadius T b : Real))
/-- If the net constant slack is at most 1, the global q readout is at most
the paper closed form. -/
theorem nativeQReadoutGlobal_le_s1915ClosedForm_of_slack
    (hslack : paperNetSlack T ≤ 1) :
    nativeQReadoutGlobal T ≤ s1915ClosedForm T := by
  let A : Real := ∑ b : Bad (nativePlaceSelection T),
    Real.log (rootImageRadius T b : Real)
  let D : Real := ∑ b : Bad (nativePlaceSelection T),
    (s1915LocalDegree T b : Real) * Real.log (rootImageRadius T b : Real)
  have hA : nativeQReadoutGlobal T ≤ A := by
    simpa [A] using nativeQReadoutGlobal_le_sum_log_radius T
  have hclosed : s1915ClosedForm T = 1 + D := by
    simpa [D] using s1915ClosedForm_eq_one_add_sum T
  have hAD : 1 + D - A = 1 - paperNetSlack T := by
    unfold paperNetSlack A D
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    rw [Finset.sum_sub_distrib]
    ring_nf
  have hAclosed : A ≤ 1 + D := by
    have hzero : 0 ≤ 1 + D - A := by
      rw [hAD]
      linarith
    linarith
  exact le_trans hA (by linarith)
end LeanFormal.IUT.XiFPaper.Mzk1P0NativeThetaPaperReadoutActual
end