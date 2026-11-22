import tmp.sheaf.xif.paper.BadPlacePaperConstantsActual
import tmp.sheaf.xif.paper.QVFamNormalizedCoefficientBridgeActual
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotBaseChange
import tmp.sheaf.xif.paper.VbadPlaceIndexingActual

/-! # Actual source normalization data for the qVFamily coefficient

S13 uses the normalized-supply coefficient

  c_norm = -logb_p ||qVFamily||_normalized

while the paper root coefficient is order(qVFamily)/(2l).  This file packages
the exact correction

  delta = c_norm - order(qVFamily)

as actual source normalization data, proves the exact q-side and Theta-side
correction terms, and proves that c_norm = order iff delta = 0.  The correction
is NOT silently dropped: it appears once on the qPilot side and with the
1/(2l) root factor on the Theta side.

No sorry/axiom/True/PUnit. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.BadPlaceNormalizationSourceActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedCoefficientBridgeActual
open LeanFormal.IUT.ArithmeticQPilotBaseChange
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperConstantsActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (b : Bad (nativePlaceSelection T))

/-- Actual source normalization data: c_norm, order, and the correction. -/
structure SourceNormalizationData where
  cNorm : Real
  cNorm_eq : cNorm = QVFamNormalizedGeneratorSupplyActual.qVFamNormalizedCoefficient T b
  order : Real
  order_eq : order = ((qVFamily T b).order : Real)
  correction : Real
  correction_eq : correction = cNorm - order
  cNorm_eq_order_add : cNorm = order + correction
  correction_mul_logp :
    correction * Real.log (qVFamTensorP T b : Real) =
      order * (Real.log (residueNormBase (qVFamTensorPlace T b)) -
        Real.log (qVFamTensorP T b : Real)) - Real.log (qVFamNormRatio T b)

/-- The actual source normalization data. -/
noncomputable def sourceNormalizationData :
    SourceNormalizationData T b where
  cNorm := QVFamNormalizedGeneratorSupplyActual.qVFamNormalizedCoefficient T b
  cNorm_eq := rfl
  order := ((qVFamily T b).order : Real)
  order_eq := rfl
  correction := normalizedOrderCorrection T b
  correction_eq := rfl
  cNorm_eq_order_add := by
    unfold normalizedOrderCorrection
    ring
  correction_mul_logp := by
    unfold normalizedOrderCorrection
    have hbridge :
        QVFamNormalizedGeneratorSupplyActual.qVFamNormalizedCoefficient T b *
            Real.log (qVFamTensorP T b : Real) =
          ((qVFamily T b).order : Real) *
              Real.log (residueNormBase (qVFamTensorPlace T b)) -
            Real.log (qVFamNormRatio T b) :=
      qVFamNormalizedCoefficient_mul_log_eq_order_mul_log_residueNormBase_sub_log_ratio T b
    nlinarith [hbridge]

/-- The correction is zero exactly when c_norm equals the qVFamily order. -/
theorem sourceNormalization_correction_zero_iff :
    normalizedOrderCorrection T b = 0 ↔
      QVFamNormalizedGeneratorSupplyActual.qVFamNormalizedCoefficient T b =
        ((qVFamily T b).order : Real) := by
  unfold normalizedOrderCorrection
  constructor <;> intro h <;> linarith

/-- S13 half coefficient equals the paper root coefficient iff the correction
vanishes. -/
theorem s13HalfCoefficient_eq_paperRootCoefficient_iff :
    s13HalfCoefficient T b = paperRootCoefficient T b ↔
      normalizedOrderCorrection T b = 0 := by
  rw [s13HalfCoefficient_eq_paperRootCoefficient_add_correction]
  constructor
  · intro h
    have hdiv : normalizedOrderCorrection T b / (2 * l.value : Real) = 0 := by
      linarith
    have htwo : (2 * l.value : Real) ≠ 0 := by
      exact_mod_cast Nat.mul_ne_zero (by norm_num) l.prime.ne_zero
    exact (div_eq_zero_iff.mp hdiv).resolve_right htwo
  · intro h
    rw [h, zero_div, add_zero]

/-- qPilot-side coefficient: c_norm = order + correction. -/
theorem qPilotCoefficient_eq_order_add_correction :
    QVFamNormalizedGeneratorSupplyActual.qVFamNormalizedCoefficient T b =
      ((qVFamily T b).order : Real) + normalizedOrderCorrection T b :=
  (sourceNormalizationData T b).cNorm_eq_order_add

/-- Theta-side root coefficient: c_norm/(2l) = order/(2l) + correction/(2l). -/
theorem thetaRootCoefficient_eq_paperRoot_add_correction :
    s13HalfCoefficient T b =
      paperRootCoefficient T b +
        normalizedOrderCorrection T b / (2 * l.value : Real) := by
  rw [s13HalfCoefficient_eq_paperRootCoefficient_add_correction]

/-- Exact q-side correction contribution to the weighted qPilot scalar. -/
theorem weightedQPilotCorrectionTerm :
    (∑ b : Bad (nativePlaceSelection T),
        nativeBadLocalWeight T b *
          (QVFamNormalizedGeneratorSupplyActual.qVFamNormalizedCoefficient T b *
            Real.log (qVFamTensorP T b : Real))) -
      (∑ b : Bad (nativePlaceSelection T),
        nativeBadLocalWeight T b *
          (((qVFamily T b).order : Real) *
            Real.log (qVFamTensorP T b : Real))) =
    ∑ b : Bad (nativePlaceSelection T),
      nativeBadLocalWeight T b *
        (normalizedOrderCorrection T b * Real.log (qVFamTensorP T b : Real)) := by
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro b _
  unfold normalizedOrderCorrection
  ring

/-- Exact Theta-side correction contribution, with the 1/(2l) root factor. -/
theorem weightedThetaCorrectionTerm :
    (∑ b : Bad (nativePlaceSelection T),
        nativeBadLocalWeight T b *
          ((QVFamNormalizedGeneratorSupplyActual.qVFamNormalizedCoefficient T b /
              (2 * l.value : Real)) * Real.log (qVFamTensorP T b : Real))) -
      (∑ b : Bad (nativePlaceSelection T),
        nativeBadLocalWeight T b *
          ((((qVFamily T b).order : Real) / (2 * l.value : Real)) *
            Real.log (qVFamTensorP T b : Real))) =
    ∑ b : Bad (nativePlaceSelection T),
      nativeBadLocalWeight T b *
        ((normalizedOrderCorrection T b / (2 * l.value : Real)) *
          Real.log (qVFamTensorP T b : Real)) := by
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro b _
  unfold normalizedOrderCorrection
  ring

end LeanFormal.IUT.XiFPaper.BadPlaceNormalizationSourceActual
