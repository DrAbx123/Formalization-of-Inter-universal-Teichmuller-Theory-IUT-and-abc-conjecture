import tmp.sheaf.xif.paper.BadPlaceRationalDegreeFactorActual

/-! # Paper-normalized comparison on the bad-place product

The normalized supply coefficient c_norm is defined by a normalized norm,
while the paper coefficient is the qVFamily order normalized by the actual
residue-norm logarithm.  This file constructs the actual paper-normalized
coefficient

  paperCoefficient_b = order_b * log(residueNormBase F-place_b) / log p_b,

which contains the rational degree factor explicitly, and proves

  c_norm_b = paperCoefficient_b - log(qVFamNormRatio_b)/log p_b.

Thus the rational degree is absorbed into the paper coefficient, not left as an
arbitrary correction.  The final comparison is restated in paper-normalized
form plus only the norm-ratio correction.

No degree=1 assumption. No sorry/axiom/True/PUnit. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.BadPlacePaperNormalizedComparisonActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedCoefficientBridgeActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperConstantsActual
open LeanFormal.IUT.XiFPaper.BadPlaceNormalizationSourceActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootComparisonActual
open LeanFormal.IUT.XiFPaper.BadPlaceCorrectionControlActual
open LeanFormal.IUT.XiFPaper.BadPlaceRationalDegreeActual
open LeanFormal.IUT.XiFPaper.BadPlaceRationalDegreeFactorActual
open LeanFormal.IUT.XiFPaper.BadPlaceNormalizedSourceHypothesisActual
open LeanFormal.IUT.XiFPaper.PaperBadPlaceTensorGeometryActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.ArithmeticQPilotBaseChange

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (b : Bad (nativePlaceSelection T))

/-- Actual paper-normalized qVFamily coefficient: order times the full
residue-norm log divided by log p_b. -/
noncomputable def paperNormalizedCoefficient : Real :=
  ((qVFamily T b).order : Real) *
    (Real.log (residueNormBase (qVFamTensorPlace T b)) /
      Real.log (qVFamTensorP T b : Real))

/-- The paper coefficient contains the rational degree factor explicitly. -/
theorem paperNormalizedCoefficient_eq_degree_factor :
    paperNormalizedCoefficient T b =
      ((qVFamily T b).order : Real) * rationalDegreeFactor T b *
        (Real.log (qVFamTensorRationalBaseNorm T b) /
          Real.log (qVFamTensorP T b : Real)) := by
  unfold paperNormalizedCoefficient
  rw [logResidueNormBase_eq_degreeFactor_mul_baseLog]
  ring

/-- c_norm equals the paper-normalized coefficient minus the normalized/default
norm-ratio correction. -/
theorem c_norm_eq_paperCoefficient_sub_normRatio :
    QVFamNormalizedGeneratorSupplyActual.qVFamNormalizedCoefficient T b =
      paperNormalizedCoefficient T b -
        Real.log (qVFamNormRatio T b) /
          Real.log (qVFamTensorP T b : Real) := by
  have hlog : Real.log (qVFamTensorP T b : Real) ≠ 0 := by
    apply Real.log_ne_zero_of_pos_of_ne_one
    · exact_mod_cast (Fact.out : Nat.Prime (qVFamTensorP T b)).pos
    · exact_mod_cast (Fact.out : Nat.Prime (qVFamTensorP T b)).ne_one
  unfold paperNormalizedCoefficient
  have hbridge := qVFamNormalizedCoefficient_mul_log_eq_order_mul_log_residueNormBase_sub_log_ratio T b
  field_simp [hlog]
  linarith

/-- Paper-normalized qPilot coefficient scalar. -/
noncomputable def paperNormalizedQPilotSum : Real :=
  ∑ b : Bad (nativePlaceSelection T),
    nativeBadLocalWeight T b *
      (paperNormalizedCoefficient T b * Real.log (qVFamTensorP T b : Real))

/-- Paper-normalized Theta root coefficient scalar. -/
noncomputable def paperNormalizedThetaSum : Real :=
  ∑ b : Bad (nativePlaceSelection T),
    nativeBadLocalWeight T b *
      ((paperNormalizedCoefficient T b / (2 * l.value : Real)) *
        Real.log (qVFamTensorP T b : Real))

/-- Norm-ratio correction sum on the q side. -/
noncomputable def normRatioCorrectionSum : Real :=
  ∑ b : Bad (nativePlaceSelection T),
    nativeBadLocalWeight T b * Real.log (qVFamNormRatio T b)

/-- Norm-ratio correction sum on the Theta root side. -/
noncomputable def halfNormRatioCorrectionSum : Real :=
  ∑ b : Bad (nativePlaceSelection T),
    nativeBadLocalWeight T b * (Real.log (qVFamNormRatio T b) / (2 * l.value : Real))

/-- Exact S13 q-side decomposition into paper coefficient minus norm-ratio. -/
theorem s13Q_eq_paperNormalized_sub_normRatio :
    s13QPilotCoefficientSum T =
      paperNormalizedQPilotSum T - normRatioCorrectionSum T := by
  unfold s13QPilotCoefficientSum paperNormalizedQPilotSum normRatioCorrectionSum
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro b _
  have h := c_norm_eq_paperCoefficient_sub_normRatio T b
  have hlog : Real.log (qVFamTensorP T b : Real) ≠ 0 := by
    apply Real.log_ne_zero_of_pos_of_ne_one
    · exact_mod_cast (Fact.out : Nat.Prime (qVFamTensorP T b)).pos
    · exact_mod_cast (Fact.out : Nat.Prime (qVFamTensorP T b)).ne_one
  have hmul :
      QVFamNormalizedGeneratorSupplyActual.qVFamNormalizedCoefficient T b *
          Real.log (qVFamTensorP T b : Real) =
        paperNormalizedCoefficient T b * Real.log (qVFamTensorP T b : Real) -
          Real.log (qVFamNormRatio T b) := by
    have hh := h
    field_simp [hlog] at hh
    linarith
  rw [hmul]
  ring

/-- Exact S13 Theta-side decomposition into paper coefficient minus half
norm-ratio. -/
theorem s13Theta_eq_paperNormalized_sub_halfNormRatio :
    s13ThetaCoefficientSum T =
      paperNormalizedThetaSum T - halfNormRatioCorrectionSum T := by
  unfold s13ThetaCoefficientSum paperNormalizedThetaSum halfNormRatioCorrectionSum
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro b _
  have h := c_norm_eq_paperCoefficient_sub_normRatio T b
  have hlog : Real.log (qVFamTensorP T b : Real) ≠ 0 := by
    apply Real.log_ne_zero_of_pos_of_ne_one
    · exact_mod_cast (Fact.out : Nat.Prime (qVFamTensorP T b)).pos
    · exact_mod_cast (Fact.out : Nat.Prime (qVFamTensorP T b)).ne_one
  have hmul :
      QVFamNormalizedGeneratorSupplyActual.qVFamNormalizedCoefficient T b *
          Real.log (qVFamTensorP T b : Real) =
        paperNormalizedCoefficient T b * Real.log (qVFamTensorP T b : Real) -
          Real.log (qVFamNormRatio T b) := by
    have hh := h
    field_simp [hlog] at hh
    linarith
  have htwo : (2 * l.value : Real) ≠ 0 := by
    exact_mod_cast Nat.mul_ne_zero (by norm_num) l.prime.ne_zero
  have hmul2 :
      (QVFamNormalizedGeneratorSupplyActual.qVFamNormalizedCoefficient T b /
          (2 * l.value : Real)) * Real.log (qVFamTensorP T b : Real) =
        (paperNormalizedCoefficient T b / (2 * l.value : Real)) *
            Real.log (qVFamTensorP T b : Real) -
          Real.log (qVFamNormRatio T b) / (2 * l.value : Real) := by
    have hdiv := congrArg (fun x : Real => x / (2 * l.value : Real)) hmul
    field_simp [htwo] at hdiv ⊢
    linarith
  rw [hmul2]
  ring

/-- Final comparison in paper-normalized form plus only the norm-ratio
correction; the rational degree is inside the paper coefficient. -/
theorem s13Comparison_iff_paperNormalized_add_normRatio :
    (s13ThetaCoefficientSum T ≤ s13QPilotCoefficientSum T) ↔
      (paperNormalizedThetaSum T ≤
        paperNormalizedQPilotSum T +
          (halfNormRatioCorrectionSum T - normRatioCorrectionSum T)) := by
  rw [s13Theta_eq_paperNormalized_sub_halfNormRatio,
    s13Q_eq_paperNormalized_sub_normRatio]
  constructor <;> intro h <;> linarith

end LeanFormal.IUT.XiFPaper.BadPlacePaperNormalizedComparisonActual
