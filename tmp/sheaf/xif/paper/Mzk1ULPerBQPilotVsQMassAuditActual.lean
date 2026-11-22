/- AUDIT: R1 chain — is `perBQPilotLog` the paper `qPilotMass(cPFullFiber)`?

  Definitions used:
  * `perBQPilotLog T b = qPilotClassicalLog (places) tuple addHaar
      (rootNormCoefficient T b) (rootNormScalingData T b)`
    with `rootNormCoefficient = qVFamNormalizedCoefficientFamily` and (supply version)
    `qVFamNormalizedCoefficient = -logb_p ||q_normalized||`.
  * `qPilotMass cP = -(cP/(2*l)) * log p`.
  * `qPilotClassicalLog ... = -((sum_i cNorm_i) * log p)` [qPilotClassicalLog_eq].
  * the tensor index is `qVFamTensorV = Unit`, so the sum over i is one term.
  Verdict proved here: `perBQPilotLog = qPilotMass cP` iff `cP = 2*l*cNorm`;
  in particular `perBQPilotLog = qPilotMass (cPFullFiber)` iff `cPFullFiber = 2*l*cNorm`.
  With `cNorm = order/e` [qVFamNormalizedCoefficient_eq_order_div_e] this is `e = 2*l`
  under `cPFullFiber = order`, so the two are NOT equal in general: exact mismatch
  factor `2*l/e`.  `perBThetaHullLog` = `rootThetaHullLog` with `cRoot = cNorm/(2l)`
  (single-label root hull); the paper Theta uses the Gaussian `j^2`-weighted coefficients
  `qVFamPaperThetaTensorCoefficient`, so it is NOT the paper Theta either.
  No stub, no sorry/axiom. -/
import tmp.sheaf.xif.paper.PaperLevelXiFTargetProofActual
import tmp.sheaf.xif.paper.Mzk1ULR1QPilotMassBasicActual
import tmp.sheaf.xif.paper.S3131CoefficientReductionActual
import tmp.sheaf.xif.paper.Mzk1ULR1CPrimeFiberActual
import Mathlib.Tactic

noncomputable section
set_option maxHeartbeats 2000000
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1ULPerBQPilotVsQMassAuditActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual
open LeanFormal.IUT.XiFPaper.RootNormalizedContainmentActual
open LeanFormal.IUT.XiFPaper.RootHullContainmentInequalityActual
open LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetProofActual
open LeanFormal.IUT.XiFPaper.Mzk1ULR1QPilotMassBasicActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open MeasureTheory

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]

/-- `perBQPilotLog = -(cNorm) * log p`: the tensor index is `Unit`. -/
theorem perBQPilotLog_eq {b : Bad (nativePlaceSelection T)} :
    perBQPilotLog (l := l) T b =
      -(qVFamNormalizedCoefficient (l := l) T b) *
        Real.log (qVFamTensorP (l := l) T b : ℝ) := by
  unfold perBQPilotLog rootNormCoefficient
  have h := qPilotClassicalLog_eq (l := l) (T := T) (b := b)
    (qVFamTensorPlaces T b) qVFamTensorTuple (Measure.addHaar)
    (rootNormCoefficient (l := l) T b) (rootNormScalingData (l := l) T b)
  simpa [qVFamNormalizedCoefficientFamily] using h

/-- `qPilotMass cP = -(cP/(2l)) * log p`. -/
theorem qPilotMass_eq' {b : Bad (nativePlaceSelection T)} (cP : ℝ) :
    qPilotMass (l := l) T b cP =
      (-(cP / (2 * (l.value : ℝ)))) * Real.log (qVFamTensorP (l := l) T b : ℝ) :=
  qPilotMass_eq (l := l) T b cP

/-- log p is nonzero for the actual prime p of the tensor block. -/
theorem log_qVFamTensorP_ne_zero {b : Bad (nativePlaceSelection T)} :
    Real.log (qVFamTensorP (l := l) T b : ℝ) ≠ 0 := by
  have hprime : Nat.Prime (qVFamTensorP (l := l) T b) :=
    Fact.out (p := Nat.Prime (qVFamTensorP (l := l) T b))
  have hp1 : (1 : ℝ) < (qVFamTensorP (l := l) T b : ℝ) := by
    exact_mod_cast hprime.one_lt
  exact ne_of_gt (Real.log_pos hp1)

/-- **Exact audit equivalence**: `perBQPilotLog = qPilotMass cP ↔ cP = 2*l*cNorm`. -/
theorem perBQPilotLog_eq_qPilotMass_iff {b : Bad (nativePlaceSelection T)} (cP : ℝ) :
    perBQPilotLog (l := l) T b = qPilotMass (l := l) T b cP ↔
      cP = (2 * (l.value : ℝ)) * qVFamNormalizedCoefficient (l := l) T b := by
  rw [perBQPilotLog_eq, qPilotMass_eq']
  have hlog := log_qVFamTensorP_ne_zero (l := l) (T := T) (b := b)
  have h2l : (2 * (l.value : ℝ)) ≠ 0 := by
    have hpos : (0 : ℝ) < (l.value : ℝ) := by exact_mod_cast l.prime.pos
    positivity
  constructor
  · intro h
    have h1 : qVFamNormalizedCoefficient (l := l) T b * Real.log (qVFamTensorP (l := l) T b : ℝ) =
        (cP / (2 * (l.value : ℝ))) * Real.log (qVFamTensorP (l := l) T b : ℝ) := by
      linarith
    have h2 : qVFamNormalizedCoefficient (l := l) T b = cP / (2 * (l.value : ℝ)) :=
      mul_right_cancel₀ hlog h1
    field_simp [h2l] at h2
    linarith
  · intro h
    rw [h]
    field_simp [h2l]
    ring

#print axioms perBQPilotLog_eq
#print axioms perBQPilotLog_eq_qPilotMass_iff

end LeanFormal.IUT.XiFPaper.Mzk1ULPerBQPilotVsQMassAuditActual