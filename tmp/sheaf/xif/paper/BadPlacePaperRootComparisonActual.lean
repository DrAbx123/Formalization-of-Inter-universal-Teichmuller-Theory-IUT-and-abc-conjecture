import tmp.sheaf.xif.paper.BadPlaceNormalizationSourceActual

/-! # S13 weighted comparison against paper root constants

This file connects the S13 weighted qPilot/Theta comparison to the paper root
constant order(q_v)/(2l).  The qPilot coefficient is c_norm = order + delta and
the Theta root coefficient is c_norm/(2l) = order/(2l) + delta/(2l), with
delta = normalizedOrderCorrection.

The weighted correction sums are explicitly defined; the exact identities show
that the q-side correction and the Theta-side correction are symmetric up to
the 2l root factor: (2l) * thetaCorrection = qCorrection.  Nothing is silently
dropped.

No sorry/axiom/True/PUnit. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.BadPlacePaperRootComparisonActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperConstantsActual
open LeanFormal.IUT.XiFPaper.BadPlaceNormalizationSourceActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- S13 qPilot coefficient scalar weighted with native local weights. -/
noncomputable def s13QPilotCoefficientSum : Real :=
  ∑ b : Bad (nativePlaceSelection T),
    nativeBadLocalWeight T b *
      (QVFamNormalizedGeneratorSupplyActual.qVFamNormalizedCoefficient T b *
        Real.log (qVFamTensorP T b : Real))

/-- Paper qPilot coefficient scalar: order(q_v), not the normalized correction. -/
noncomputable def paperQPilotCoefficientSum : Real :=
  ∑ b : Bad (nativePlaceSelection T),
    nativeBadLocalWeight T b *
      (((qVFamily T b).order : Real) * Real.log (qVFamTensorP T b : Real))

/-- S13 Theta root coefficient scalar: c_norm/(2l). -/
noncomputable def s13ThetaCoefficientSum : Real :=
  ∑ b : Bad (nativePlaceSelection T),
    nativeBadLocalWeight T b *
      ((QVFamNormalizedGeneratorSupplyActual.qVFamNormalizedCoefficient T b /
          (2 * l.value : Real)) * Real.log (qVFamTensorP T b : Real))

/-- Paper Theta root coefficient scalar: order(q_v)/(2l). -/
noncomputable def paperThetaCoefficientSum : Real :=
  ∑ b : Bad (nativePlaceSelection T),
    nativeBadLocalWeight T b *
      ((((qVFamily T b).order : Real) / (2 * l.value : Real)) *
        Real.log (qVFamTensorP T b : Real))

/-- Weighted q-side correction sum delta * log p. -/
noncomputable def qCorrectionSum : Real :=
  ∑ b : Bad (nativePlaceSelection T),
    nativeBadLocalWeight T b *
      (normalizedOrderCorrection T b * Real.log (qVFamTensorP T b : Real))

/-- Weighted Theta-side correction sum (delta/(2l)) * log p. -/
noncomputable def thetaCorrectionSum : Real :=
  ∑ b : Bad (nativePlaceSelection T),
    nativeBadLocalWeight T b *
      ((normalizedOrderCorrection T b / (2 * l.value : Real)) *
        Real.log (qVFamTensorP T b : Real))

/-- q-side exact relation to paper root constants. -/
theorem s13QPilotCoefficientSum_eq_paper_add_correction :
    s13QPilotCoefficientSum T = paperQPilotCoefficientSum T + qCorrectionSum T := by
  unfold s13QPilotCoefficientSum paperQPilotCoefficientSum qCorrectionSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b _
  unfold normalizedOrderCorrection
  ring

/-- Theta-side exact relation to paper root constants. -/
theorem s13ThetaCoefficientSum_eq_paper_add_correction :
    s13ThetaCoefficientSum T =
      paperThetaCoefficientSum T + thetaCorrectionSum T := by
  unfold s13ThetaCoefficientSum paperThetaCoefficientSum thetaCorrectionSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b _
  unfold normalizedOrderCorrection
  ring

/-- Symmetric 2l relation between the two correction sums. -/
theorem twoL_mul_thetaCorrectionSum_eq_qCorrectionSum :
    (2 * l.value : Real) * thetaCorrectionSum T = qCorrectionSum T := by
  unfold thetaCorrectionSum qCorrectionSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  have htwo : (2 * l.value : Real) ≠ 0 := by
    exact_mod_cast Nat.mul_ne_zero (by norm_num) l.prime.ne_zero
  have hl : (l.value : Real) ≠ 0 := by
    exact_mod_cast l.prime.ne_zero
  field_simp [htwo, hl]

/-- Exact decomposition of the S13 weighted comparison into paper-root
comparison plus the correction difference. -/
theorem weightedComparison_correction_decomposition :
    s13ThetaCoefficientSum T - s13QPilotCoefficientSum T =
      (paperThetaCoefficientSum T - paperQPilotCoefficientSum T) +
        (thetaCorrectionSum T - qCorrectionSum T) := by
  rw [s13ThetaCoefficientSum_eq_paper_add_correction,
    s13QPilotCoefficientSum_eq_paper_add_correction]
  ring

/-- The q-side paper comparison is unchanged by the correction iff the q-side
correction sum vanishes. -/
theorem s13Q_eq_paper_iff_qCorrection_zero :
    s13QPilotCoefficientSum T = paperQPilotCoefficientSum T ↔
      qCorrectionSum T = 0 := by
  rw [s13QPilotCoefficientSum_eq_paper_add_correction]
  constructor <;> intro h <;> linarith

/-- The Theta-side paper comparison is unchanged by the correction iff the
Theta-side correction sum vanishes. -/
theorem s13Theta_eq_paper_iff_thetaCorrection_zero :
    s13ThetaCoefficientSum T = paperThetaCoefficientSum T ↔
      thetaCorrectionSum T = 0 := by
  rw [s13ThetaCoefficientSum_eq_paper_add_correction]
  constructor <;> intro h <;> linarith

/-- If the 2l factor is nonzero, q-side correction zero is equivalent to
Theta-side correction zero; neither side may be silently dropped alone. -/
theorem qCorrection_zero_iff_thetaCorrection_zero :
    qCorrectionSum T = 0 ↔ thetaCorrectionSum T = 0 := by
  have htwo : (2 * l.value : Real) ≠ 0 := by
    exact_mod_cast Nat.mul_ne_zero (by norm_num) l.prime.ne_zero
  constructor
  · intro h
    have hmul := twoL_mul_thetaCorrectionSum_eq_qCorrectionSum T
    rw [h, mul_eq_zero] at hmul
    exact hmul.resolve_left htwo
  · intro h
    have hmul := twoL_mul_thetaCorrectionSum_eq_qCorrectionSum T
    rw [h, mul_zero] at hmul
    exact hmul.symm

end LeanFormal.IUT.XiFPaper.BadPlacePaperRootComparisonActual
