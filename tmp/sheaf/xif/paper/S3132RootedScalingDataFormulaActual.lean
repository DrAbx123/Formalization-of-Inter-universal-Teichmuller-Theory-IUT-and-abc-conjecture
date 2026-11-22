import tmp.sheaf.xif.paper.BadPlacePaperRootThetaHullActual
import tmp.sheaf.xif.paper.S3132RootedScalingDataTrivialActual
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

noncomputable section
open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual
open LeanFormal.IUT.XiFPaper.QVFamRootFactorCorrectionActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.S3131CanonicalRootedQCActual
open LeanFormal.IUT.XiFPaper.S3136NativeHaarFamilyActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.RootNormalizedContainmentActual
open LeanFormal.IUT.XiFPaper.RootHullContainmentInequalityActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
open LeanFormal.IUT.XiFPaper.S3132VFormScalingReductionActual
open LeanFormal.IUT.XiFPaper.S3132RootedScalingDataTrivialActual

namespace LeanFormal.IUT.XiFPaper.S3132RootedScalingDataFormulaActual

/-!
# RootedScalingDecomposition from the paper hull formula gap (TREASURE reuse)

Reuses the existing treasure file BadPlacePaperRootThetaHullActual
(paperRootThetaHullLog / paperRootThetaFormulaLog / PaperRootHullFormulaGap /
paperRootThetaHullLog_eq_formula_of_gap / paperRootThetaFormulaScalar).

Given the exact per-place paper-hull formula gap (the hull is a fractional-lattice
multiple of the holomorphic lattice, IUT III Prop 3.9(i) normalization), the
rooted log-volume is the explicit formula -(sum_i c_i)*log(p).  This is the log of
the scalar p^(-sum_i c_i), hence (R1) RootedScalingDecomposition holds with an EXPLICIT
concrete scalar, and the canonical rooted readout equals the weighted formula
scalar paperRootThetaFormulaScalar.

Source: IUT III, Proposition 3.9, (i), corpus 6838-6860; Remark 3.9.5, (i),
corpus 7652-7680.  EXACT REMAINING DATA: identification of the half coefficient family c_norm/(2l)
-/

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]

/-- The explicit formula scalar p^(-sum c) at a bad place. -/
noncomputable def paperFormulaScalar (b : Bad (nativePlaceSelection T)) : ℝ :=
  (qVFamTensorP T b : ℝ) ^
    (-(∑ _ : qVFamTensorV, qVFamPaperRootCoefficient T b))

/-- The paper formula log is the log of the explicit formula scalar. -/
theorem paperRootThetaFormulaLog_eq_log_paperFormulaScalar
    (b : Bad (nativePlaceSelection T)) :
    paperRootThetaFormulaLog T b = Real.log (paperFormulaScalar T b) := by
  unfold paperRootThetaFormulaLog paperFormulaScalar
  have hp : (0 : ℝ) < (qVFamTensorP T b : ℝ) := by
    unfold qVFamTensorP
    exact_mod_cast (completionRationalPrime (qVFamTensorPlace T b)).property.pos
  rw [Real.log_rpow hp]
  ring

/-- **RootedScalingDecomposition with the EXPLICIT concrete scalar**, from the
per-place paper-hull formula gap data plus the coefficient identification hc. -/
theorem rootedScalingDecomposition_of_paperGap
    (hc : ∀ b : Bad (nativePlaceSelection T),
      rootHalfCoefficient (l := l) T b = paperRootCoefficientFamily T b)
    (G : ∀ b : Bad (nativePlaceSelection T), PaperRootHullFormulaGap T b) :
    RootedScalingDecomposition T (fun b => Measure.addHaar) (paperFormulaScalar T) := by
  intro b
  rw [hc b]
  show paperRootThetaHullLog T b Measure.addHaar = Real.log (paperFormulaScalar T b)
  rw [paperRootThetaHullLog_eq_formula_of_gap T b Measure.addHaar (G b)]
  exact paperRootThetaFormulaLog_eq_log_paperFormulaScalar T b

#check paperFormulaScalar
#check paperRootThetaFormulaLog_eq_log_paperFormulaScalar
#check rootedScalingDecomposition_of_paperGap

end LeanFormal.IUT.XiFPaper.S3132RootedScalingDataFormulaActual
end