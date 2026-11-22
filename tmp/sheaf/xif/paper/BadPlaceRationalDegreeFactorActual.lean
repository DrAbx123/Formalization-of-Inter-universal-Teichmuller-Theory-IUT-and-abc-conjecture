import tmp.sheaf.xif.paper.BadPlaceRationalDegreeActual

/-! # Rational degree as an explicit normalization factor

qVFamTensorPlace is an arbitrary F-place over the bad base place, not a
Q-rational place.  Nothing in the source structure forces
qVFamTensorRationalDegree = 1.  This file therefore inserts the actual rational
degree into the correction and the final paper comparison as an explicit
normalization factor, and records the exact condition under which the
normalized-source hypothesis fails when the degree is > 1.

NO assumption degree = 1 is made.

No sorry/axiom/True/PUnit. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.BadPlaceRationalDegreeFactorActual

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
open LeanFormal.IUT.XiFPaper.BadPlaceNormalizedSourceHypothesisActual
open LeanFormal.IUT.XiFPaper.QVFamTensorBlockAlignmentActual
open LeanFormal.IUT.XiFPaper.PaperBadPlaceTensorGeometryActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.ArithmeticQPilotBaseChange

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (b : Bad (nativePlaceSelection T))

/-- The actual rational residue degree as a real normalization factor. -/
noncomputable def rationalDegreeFactor : Real :=
  (qVFamTensorRationalDegree T b : Real)

theorem rationalDegreeFactor_pos : 0 < rationalDegreeFactor T b := by
  unfold rationalDegreeFactor
  exact_mod_cast qVFamTensorRationalDegree_pos T b

theorem rationalDegreeFactor_ne_zero : rationalDegreeFactor T b ≠ 0 :=
  ne_of_gt (rationalDegreeFactor_pos T b)

/-- The degree-factor form of the actual F-place log formula. -/
theorem logResidueNormBase_eq_degreeFactor_mul_baseLog :
    Real.log (residueNormBase (qVFamTensorPlace T b)) =
      rationalDegreeFactor T b *
        Real.log (qVFamTensorRationalBaseNorm T b) := by
  unfold rationalDegreeFactor
  exact log_qVFamTensorPlace_eq_rationalDegree_mul_baseLog T b

/-- qCorrectionSum with the rational degree factor made explicit. -/
theorem qCorrectionSum_eq_degree_sourceTerm :
    qCorrectionSum T =
      ∑ b : Bad (nativePlaceSelection T),
        nativeBadLocalWeight T b *
          (((qVFamily T b).order : Real) *
              (rationalDegreeFactor T b *
                  Real.log (qVFamTensorRationalBaseNorm T b) -
                Real.log (qVFamTensorP T b : Real)) -
            Real.log (qVFamNormRatio T b)) := by
  rw [qCorrectionSum_eq_sourceTerm]
  apply Finset.sum_congr rfl
  intro b _
  rw [logResidueNormBase_eq_degreeFactor_mul_baseLog]

/-- If the actual obstruction holds and the rational degree is > 1, the
normalized-source condition (2) fails at b. -/
theorem condition2_fails_of_obstruction_degree_gt_one
    (hobs : qVFamTensorRationalPrimeLogObstruction T b)
    (hdeg : 1 < qVFamTensorRationalDegree T b) :
    ¬ (Real.log (residueNormBase (qVFamTensorPlace T b)) =
        Real.log (qVFamTensorP T b : Real)) := by
  intro hlog
  have hlogp : Real.log (qVFamTensorP T b : Real) ≠ 0 := by
    apply Real.log_ne_zero_of_pos_of_ne_one
    · exact_mod_cast (Fact.out : Nat.Prime (qVFamTensorP T b)).pos
    · exact_mod_cast (Fact.out : Nat.Prime (qVFamTensorP T b)).ne_one
  have hdeg_real : (1 : Real) < (qVFamTensorRationalDegree T b : Real) := by
    exact_mod_cast hdeg
  have hdeg_nat : qVFamTensorRationalDegree T b = 1 :=
    (logResidueNormBase_eq_logP_iff_degree_one_of_obstruction T b hobs).mp hlog
  have hdeg_eq : (qVFamTensorRationalDegree T b : Real) = 1 := by
    exact_mod_cast hdeg_nat
  linarith

/-- Exact degree > 1 source condition: in this situation the paper's
normalized-source identification cannot be assumed. -/
structure RationalDegreeGreaterOneSource : Prop where
  obstruction : qVFamTensorRationalPrimeLogObstruction T b
  degree_gt_one : 1 < qVFamTensorRationalDegree T b

theorem normalizedSourceHypothesis_fails_of_degreeGtOne
    (hsrc : RationalDegreeGreaterOneSource T b) :
    ¬ (∀ b : Bad (nativePlaceSelection T),
      qVFamNormRatio T b = 1 ∧
        Real.log (residueNormBase (qVFamTensorPlace T b)) =
          Real.log (qVFamTensorP T b : Real)) := by
  intro h
  exact condition2_fails_of_obstruction_degree_gt_one T b
    hsrc.obstruction hsrc.degree_gt_one (h b).2

/-- Final comparison with the rational degree factor explicit on the q side. -/
theorem s13Comparison_iff_paperComparison_add_degreeCorrection :
    (s13ThetaCoefficientSum T ≤ s13QPilotCoefficientSum T) ↔
      (paperThetaCoefficientSum T ≤
        paperQPilotCoefficientSum T +
          ((∑ b : Bad (nativePlaceSelection T),
              nativeBadLocalWeight T b *
                (((qVFamily T b).order : Real) *
                    (rationalDegreeFactor T b *
                        Real.log (qVFamTensorRationalBaseNorm T b) -
                      Real.log (qVFamTensorP T b : Real)) -
                  Real.log (qVFamNormRatio T b))) - thetaCorrectionSum T)) := by
  rw [s13Comparison_iff_paperComparison_add_correction]
  rw [qCorrectionSum_eq_degree_sourceTerm]

end LeanFormal.IUT.XiFPaper.BadPlaceRationalDegreeFactorActual
