import tmp.sheaf.n8.closure.EtaActualComparisonDivisorAttempt
import tmp.sheaf.n8.closure.C9QPilotRegion

/-!
# O3 actual comparison data: decisive source-object gap

Actual qO endpoint: Q = qORegionLogVolume X = qPilotSignedLog X < 0.

The tensor hull/nnLattice endpoint is available only as a separate candidate
(different carrier/normalization); no production theorem identifies it with the
O3 target h.  More decisively, production has no actual local comparison source
object from qO to the tensor target carrying the multiplier divisor A and
effective zero Z.  Without that source object, kappa,S cannot be actual.

This file records the exact O3 gap and the actual Q endpoint.  No arbitrary h,
A, Z, kappa or S is instantiated.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.checkUnivs false
set_option linter.overlappingInstances false
set_option linter.unusedVariables false

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.EtaVaryingCalibrationQOActual
open LeanFormal.IUT.N8Closure.EtaQRegionRepresentation
open LeanFormal.IUT.N8Closure.C9QPilotRegion

namespace LeanFormal.IUT.N8Closure.O3ActualComparisonData

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- Actual qO endpoint Q. -/
noncomputable def O3Q : ℝ := qORegionLogVolume X

theorem O3Q_eq_qPilotSignedLog : O3Q X = qPilotSignedLog X :=
  qORegionLogVolume_eq_qPilotSignedLog X

theorem O3Q_neg : O3Q X < 0 := by
  rw [O3Q_eq_qPilotSignedLog X]
  exact qPilotSignedLog_neg X

/-- Exact O3 data contract.  Q is actual; h,A,Z,kappa,S must come from an
actual source comparison object (not supplied). -/
structure O3ComparisonData (X : N8NativeInput l) where
  h : ℝ
  Q : ℝ
  A : ℝ
  Z : ℝ
  kappa : ℝ
  S : ℝ
  d : ℕ
  Q_eq : Q = O3Q X
  kappa_eq_A : kappa = A
  S_eq_Z : S = Z
  identity : h - (d : ℝ) * Q = S - kappa
  S_nonneg : 0 ≤ S

/-- Exact missing source object: production must supply an actual local
comparison morphism from qO to the tensor hull/nnLattice target, together with
actual multiplier divisor A and effective zero Z. -/
def MissingO3SourceComparisonObject (X : N8NativeInput l) : Prop :=
  Nonempty (O3ComparisonData X)

/-- Consumer contract: any actual O3 data satisfy the degree identity. -/
theorem identity_of_actualComparisonData
    (D : O3ComparisonData X) :
    D.h - (D.d : ℝ) * D.Q = D.S - D.kappa :=
  D.identity

end LeanFormal.IUT.N8Closure.O3ActualComparisonData
