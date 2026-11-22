import tmp.sheaf.n8.closure.EtaNnLatticeImageActual
import tmp.sheaf.n8.closure.EtaOrbitNonnegativeBounded
import tmp.sheaf.n8.closure.EtaActualComparisonDivisorAttempt
import tmp.sheaf.n8.closure.EtaTensorZpSubmoduleLatticeActual

/-!
# O3 constructed comparison: actual h/Q candidates, exact A/Z law gap

Actual candidates:

* Q = qORegionLogVolume X (actual qO endpoint).
* hTensor = log tensorHaar X (nnLattice X gNonIntegral 1), actual tensor
  hull/nnLattice Haar log-volume.
* The actual tensor Z_p lattices LuSub,LvSub and edgeZp edge exist, but there is
  no production finite-index/multiplier-divisor comparison identifying the qO
  multiplier A with the tensor edge lattice index and no actual effective zero Z.

Thus the model law h - d Q = S - kappa is not derivable from the actual data.
A,Z are left as missing comparison-source fields; no constant is fabricated.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.checkUnivs false
set_option linter.overlappingInstances false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.C9QPilotRegion
open LeanFormal.IUT.N8Closure.EtaQRegionRepresentation
open LeanFormal.IUT.N8Closure.EtaVaryingCalibrationQOActual
open LeanFormal.IUT.N8Closure.EtaTensorHullMeasureActual
open LeanFormal.IUT.N8Closure.EtaNnLatticeImageActual
open LeanFormal.IUT.N8Closure.EtaTensorGraphEdgeActual
open LeanFormal.IUT.N8Closure.EtaTensorLatticeImageActual
open LeanFormal.IUT.N8Closure.EtaTensorZpSubmoduleLatticeActual
open LeanFormal.IUT.N8Closure.EtaTensorNaturalityActual
open LeanFormal.IUT.N8Closure.EtaTensorAutomorphismActual3
open LeanFormal.IUT.N8Closure.EtaUniformizerRelationActual
open LeanFormal.IUT.N8Closure.EtaTensorGraphCertificateActual
open LeanFormal.IUT.N8Closure.EtaGeneralQHaarScalingActual
open LeanFormal.IUT.N8Closure.EtaOrbitNonnegativeBounded
open LeanFormal.IUT.N8Closure.EtaActualComparisonDivisorAttempt
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.NumberFieldFinitePlace
open ABCBridge.N8.C3TensorTargetCorrection
open MeasureTheory
open scoped BigOperators NNReal ENNReal Pointwise NormedField TensorProduct

namespace LeanFormal.IUT.N8Closure.O3ConstructedComparison

variable {l : PrimeGeFive} (X : N8NativeInput l)
local instance : Fact (Nat.Prime (nativePrime X)) := nativePrimeFact X

/-- Actual qO endpoint. -/
noncomputable def O3Q : ℝ := qORegionLogVolume X

theorem O3Q_neg : O3Q X < 0 := by
  rw [O3Q, qORegionLogVolume_eq_qPilotSignedLog X]
  exact qPilotSignedLog_neg X

/-- Actual tensor hull/nnLattice Haar log-volume candidate. -/
noncomputable def O3HTensor : ℝ :=
  Real.log (tensorHaar X (nnLattice X (gNonIntegral X) 1)).toReal

theorem O3Q_eq : O3Q X = qORegionLogVolume X := rfl

theorem O3HTensor_eq : O3HTensor X =
    Real.log (tensorHaar X (nnLattice X (gNonIntegral X) 1)).toReal := rfl

/-- Actual endpoint part of O3; A,Z are missing comparison-source fields, not
constants. -/
structure O3EndpointCandidates (X : N8NativeInput l) where
  h : ℝ
  Q : ℝ
  d : ℕ
  h_eq : h = O3HTensor X
  Q_eq : Q = O3Q X
  d_eq : d = 1

/-- Exact missing comparison divisors A,Z and model law. -/
structure O3MissingDivisors (C : O3EndpointCandidates X) where
  A : ℝ
  Z : ℝ
  kappa : ℝ
  S : ℝ
  kappa_eq_A : kappa = A
  S_eq_Z : S = Z
  identity : C.h - (C.d : ℝ) * C.Q = S - kappa
  S_nonneg : 0 ≤ S

/-- Exact missing source object: actual comparison morphism identifying qO and
tensor-edge lattice comparison, yielding actual A,Z and the law. -/
def MissingO3ComparisonMorphism (X : N8NativeInput l) : Prop :=
  ∃ C : O3EndpointCandidates X, Nonempty (O3MissingDivisors X C)

end LeanFormal.IUT.N8Closure.O3ConstructedComparison
