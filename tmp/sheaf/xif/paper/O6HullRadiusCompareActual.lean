/- Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. -/
import tmp.sheaf.xif.paper.ArchimedeanMetricBoundActual
import tmp.sheaf.xif.paper.CrossNormLogVolumeActual

/-! O6 hull-radius comparison file: the C3 packet normalization (dimension * log p)
side by side with the 06 archimedean metric factor ((n-1)*log 2) and the 08
cross-norm log-volume. All imported from the two reference files; no new axioms. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.O6HullRadiusCompareActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.ArchimedeanMetricBoundActual
open LeanFormal.IUT.XiFPaper.CrossNormLogVolumeActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.S3137C3LogShellPacketNormalizedLogVolumeActual
open scoped BigOperators

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}

/-- The O6 p-adic hull-radius normalization constant: dimension * log p. -/
def c3HullRadiusNormalization
    (C3 : SourcePilotRegionData (l := l) (V := V) I) : Real :=
  (c3TensorBlockDimension C3 : Real) * Real.log (C3.p : Real)

theorem c3HullRadiusNormalization_constructed
    (C3 : SourcePilotRegionData (l := l) (V := V) I) :
    c3HullRadiusNormalization C3 =
      (c3TensorBlockDimension C3 : Real) * Real.log (C3.p : Real) := rfl

theorem c3HullRadiusNormalization_eq_log_p_pow
    (C3 : SourcePilotRegionData (l := l) (V := V) I) :
    c3HullRadiusNormalization C3 =
      Real.log ((C3.p : Real) ^ (c3TensorBlockDimension C3 : Nat)) := by
  unfold c3HullRadiusNormalization
  rw [Real.log_pow]

theorem c3HullRadiusNormalization_nonneg
    (C3 : SourcePilotRegionData (l := l) (V := V) I) :
    0 <= c3HullRadiusNormalization C3 := by
  unfold c3HullRadiusNormalization
  have hp : (1 : Real) < (C3.p : Real) := by
    exact_mod_cast C3.hp.out.one_lt
  have hlog : 0 <= Real.log (C3.p : Real) := Real.log_nonneg hp.le
  exact mul_nonneg (Nat.cast_nonneg _) hlog

/-- The archimedean 06 bound factor contributes (n-1) * log 2 to log-volume. -/
theorem archimedeanMetricBound_log_reuse (n : Nat) (x : Real) (hx : 0 < x) :
    Real.log (archimedeanMetricBound n x) =
      ((n - 1 : Nat) : Real) * Real.log 2 + Real.log x :=
  archimedeanMetricBound_log n x hx

variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- The 08 cross-norm lemma at the actual root theta values. -/
theorem o6_thetaLogVolume_eq_crossNorm (j : SignedLabel l.value) :
    Real.log ‖(rootNormedThetaValueInL T b j : rootNormedExtension T b)‖ =
      (gaussExponent j.1 : Real) * Real.log ‖rootNormedElement T b‖ :=
  rootTheta_crossNormLogVolume T b j

/-- The O6 hull-radius comparison data: p-adic normalization vs the
archimedean factor and the cross-norm log-volume law. -/
structure O6HullRadiusCompareData
    (C3 : SourcePilotRegionData (l := l) (V := V) I) where
  dimension : Nat
  dimension_eq : dimension = c3TensorBlockDimension C3
  pAdicNormalization : Real
  pAdicNormalization_eq : pAdicNormalization = c3HullRadiusNormalization C3
  archimedeanFactor : Real
  archimedeanFactor_eq : archimedeanFactor = Real.log 2

noncomputable def o6HullRadiusCompareData
    (C3 : SourcePilotRegionData (l := l) (V := V) I) :
    O6HullRadiusCompareData C3 where
  dimension := c3TensorBlockDimension C3
  dimension_eq := rfl
  pAdicNormalization := c3HullRadiusNormalization C3
  pAdicNormalization_eq := rfl
  archimedeanFactor := Real.log 2
  archimedeanFactor_eq := rfl

theorem o6HullRadiusCompareData_constructed
    (C3 : SourcePilotRegionData (l := l) (V := V) I) :
    (o6HullRadiusCompareData C3).dimension = c3TensorBlockDimension C3 ∧
    (o6HullRadiusCompareData C3).pAdicNormalization =
      c3HullRadiusNormalization C3 := by
  refine ⟨rfl, rfl⟩

end LeanFormal.IUT.XiFPaper.O6HullRadiusCompareActual