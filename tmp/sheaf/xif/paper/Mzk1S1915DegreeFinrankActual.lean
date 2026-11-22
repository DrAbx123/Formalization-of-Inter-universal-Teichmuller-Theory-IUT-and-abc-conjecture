/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.S1915ThetaHullA0Actual
import tmp.sheaf.xif.paper.PaperRootExtensionThetaHullAuditActual
import Mathlib.Tactic

/-! # GAP-P7-BALL-MASS: `s1915LocalDegree = finrank` (definitional) -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1S1915DegreeFinrankActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S1915ThetaHullA0Actual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullAuditActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- `s1915LocalDegree` is definitionally the local degree `[K_b : Q_p]`. -/
theorem s1915LocalDegree_eq_finrank
    (b : Bad (nativePlaceSelection T)) :
    s1915LocalDegree T b =
      Module.finrank ℚ_[qVFamTensorP T b] (rootNormedExtension T b) := rfl

/-- Real-valued form of the local degree identity. -/
theorem s1915LocalDegree_eq_finrank_real
    (b : Bad (nativePlaceSelection T)) :
    (s1915LocalDegree T b : ℝ) =
      (Module.finrank ℚ_[qVFamTensorP T b] (rootNormedExtension T b) : ℝ) := by
  rw [s1915LocalDegree_eq_finrank T b]

/-- The S1915 closed form with the degree written as `finrank`. -/
theorem s1915ClosedForm_eq_finrank :
    s1915ClosedForm T =
      1 + ∑ b : Bad (nativePlaceSelection T),
        (Module.finrank ℚ_[qVFamTensorP T b] (rootNormedExtension T b) : ℝ) *
          Real.log (rootImageRadius T b : ℝ) := by
  unfold s1915ClosedForm
  rfl

end LeanFormal.IUT.XiFPaper.Mzk1S1915DegreeFinrankActual