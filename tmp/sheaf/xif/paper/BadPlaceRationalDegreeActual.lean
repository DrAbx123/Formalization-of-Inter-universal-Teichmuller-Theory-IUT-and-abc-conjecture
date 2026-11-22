import tmp.sheaf.xif.paper.BadPlaceNormalizedSourceHypothesisActual

/-! # Rational residue degree of the qVFamily F-place

This file inspects qVFamTensorRationalDegree = localResidueDegree (k := Q)
of the actual qVFamily F-place.  The actual log formula is

  log(residueNormBase F-place) = rationalDegree * log(baseResidueNorm).

Consequently the rational-prime log obstruction is exactly

  log p_b = log(baseResidueNorm),

not an assertion of degree one.  We do NOT fake rationalDegree = 1; instead we
prove the exact obstruction/base-log equivalence and the failure criterion, and
keep the S58 normalized-source reduction conditional.

No sorry/axiom/True/PUnit. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.BadPlaceRationalDegreeActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamTensorBlockAlignmentActual
open LeanFormal.IUT.XiFPaper.BadPlaceNormalizedSourceHypothesisActual
open LeanFormal.IUT.XiFPaper.BadPlaceCorrectionControlActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootComparisonActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedCoefficientBridgeActual
open LeanFormal.IUT.XiFPaper.PaperBadPlaceTensorGeometryActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.ArithmeticQPilotBaseChange

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (b : Bad (nativePlaceSelection T))

/-- The rational degree is the actual inertia degree over Q. -/
theorem qVFamTensorRationalDegree_eq_inertiaDeg :
    qVFamTensorRationalDegree T b =
      (comap (k := ℚ) (qVFamTensorPlace T b)).maximalIdeal.asIdeal.inertiaDeg'
        (qVFamTensorPlace T b).maximalIdeal.asIdeal := rfl

/-- The rational degree is positive. -/
theorem qVFamTensorRationalDegree_pos :
    0 < qVFamTensorRationalDegree T b :=
  localResidueDegree_pos (k := ℚ) (qVFamTensorPlace T b)

/-- The actual base residue norm at the contracted rational place. -/
noncomputable def qVFamTensorRationalBaseNorm : Real :=
  residueNormBase (comap (k := ℚ) (qVFamTensorPlace T b))

/-- Actual log formula for the qVFamily F-place over Q. -/
theorem log_qVFamTensorPlace_eq_rationalDegree_mul_baseLog :
    Real.log (residueNormBase (qVFamTensorPlace T b)) =
      (qVFamTensorRationalDegree T b : Real) *
        Real.log (qVFamTensorRationalBaseNorm T b) := by
  unfold qVFamTensorRationalBaseNorm
  exact log_residueNormBase_eq_residueDegree_mul (k := ℚ) (qVFamTensorPlace T b)

/-- The actual rational-prime log obstruction is exactly the equality of the
rational prime log with the base residue-norm log. -/
theorem qVFamTensorRationalPrimeLogObstruction_iff_baseLog_eq :
    qVFamTensorRationalPrimeLogObstruction T b ↔
      Real.log (qVFamTensorP T b : Real) =
        Real.log (qVFamTensorRationalBaseNorm T b) := by
  unfold qVFamTensorRationalPrimeLogObstruction
  rw [log_qVFamTensorPlace_eq_rationalDegree_mul_baseLog (l := l) T b]
  have hd : (qVFamTensorRationalDegree T b : Real) ≠ 0 := by
    exact_mod_cast (ne_of_gt (qVFamTensorRationalDegree_pos T b))
  constructor
  · intro h
    exact mul_left_cancel₀ hd h
  · intro h
    rw [h]

/-- Failure criterion: if the base residue log differs from log p_b, the actual
rational-prime obstruction fails. -/
theorem qVFamTensorRationalPrimeLogObstruction_false_of_baseLog_ne
    (h : Real.log (qVFamTensorRationalBaseNorm T b) ≠
      Real.log (qVFamTensorP T b : Real)) :
    ¬ qVFamTensorRationalPrimeLogObstruction T b := by
  intro hobs
  exact h ((qVFamTensorRationalPrimeLogObstruction_iff_baseLog_eq T b).mp hobs).symm

/-- Under the actual obstruction, rational degree one is necessary for the
normalized-source condition (2). -/
theorem rationalDegree_one_of_obstruction_and_condition2
    (hobs : qVFamTensorRationalPrimeLogObstruction T b)
    (hlog : Real.log (residueNormBase (qVFamTensorPlace T b)) =
      Real.log (qVFamTensorP T b : Real)) :
    qVFamTensorRationalDegree T b = 1 :=
  (logResidueNormBase_eq_logP_iff_degree_one_of_obstruction T b hobs).mp hlog

/-- The S58 normalized-source hypothesis is not asserted; under the actual
obstruction it is equivalent to rational degree one plus the q-side
coefficient equality. -/
theorem normalizedSourceHypothesis_iff_degree_one_and_ratioCondition
    (hobs : ∀ b : Bad (nativePlaceSelection T),
      qVFamTensorRationalPrimeLogObstruction T b) :
    NormalizedSourceHypothesis T ↔
      (∀ b : Bad (nativePlaceSelection T), qVFamTensorRationalDegree T b = 1) ∧
        (∀ b : Bad (nativePlaceSelection T),
          QVFamNormalizedGeneratorSupplyActual.qVFamNormalizedCoefficient T b *
              Real.log (qVFamTensorP T b : Real) =
            ((qVFamily T b).order : Real) *
              Real.log (residueNormBase (qVFamTensorPlace T b))) := by
  constructor
  · intro h
    refine ⟨fun b => ?_, fun b => ?_⟩
    · exact rationalDegree_one_of_obstruction_and_condition2 T b (hobs b) (h b).2
    · exact (qVFamNormRatio_eq_one_iff T b).mp (h b).1
  · rintro ⟨hdeg, hratio⟩
    exact normalizedSourceHypothesis_of_ratio_and_obstruction_degree T hratio hobs hdeg

/-- The actual correction bound remains available when the hypothesis is not
derived. -/
theorem correction_bound_remaining :
    |qCorrectionSum T| ≤
      ∑ b : Bad (nativePlaceSelection T),
        nativeBadLocalWeight T b *
          ((qVFamily T b).order *
              |Real.log (residueNormBase (qVFamTensorPlace T b)) -
                Real.log (qVFamTensorP T b : Real)| +
            |Real.log (qVFamNormRatio T b)|) :=
  abs_qCorrectionSum_le T

end LeanFormal.IUT.XiFPaper.BadPlaceRationalDegreeActual
