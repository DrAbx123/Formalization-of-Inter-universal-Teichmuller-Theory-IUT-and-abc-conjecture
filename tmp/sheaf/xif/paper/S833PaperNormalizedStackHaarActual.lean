import tmp.sheaf.xif.paper.S832DFactorAbsorptionAuditActual

noncomputable section
open scoped BigOperators NNReal ENNReal
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S833PaperNormalizedStackHaarActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S799LeastLambdaOPaperTargetActual
open LeanFormal.IUT.XiFPaper.S823StackHaarNormalizedActual
open LeanFormal.IUT.XiFPaper.S782FiniteRootStackExtensionActual
open LeanFormal.IUT.XiFPaper.S809PaperLeastHullRootStackBridgeActual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-- Numeric scalar d^{-1} times the normalized stack Haar. -/
noncomputable def paperNormalizedRootStackHaar (d : Nat) :
    Measure (rootStackExtension (l := l) T b) :=
  ENNReal.ofReal ((d : Real)⁻¹) • normalizedRootStackHaar (l := l) T b

/-- Root-ball log for the numeric d^{-1}-scaled Haar. -/
noncomputable def paperNormalizedRootStackRootBallLog (d : Nat) : Real :=
  Real.log
    ((paperNormalizedRootStackHaar (l := l) T b d
      (Metric.closedBall (0 : rootStackExtension (l := l) T b)
        ‖(stackRootUnit (l := l) T b :
          rootStackExtension (l := l) T b)‖)).toReal)

/-- Exact mass formula for the normalized root ball: mass = exp(d * L). -/
def NormalizedRootBallMassFormula (d : Nat) : Prop :=
  (normalizedRootStackHaar (l := l) T b
    (Metric.closedBall (0 : rootStackExtension (l := l) T b)
      ‖(stackRootUnit (l := l) T b :
        rootStackExtension (l := l) T b)‖)).toReal =
    Real.exp ((d : Real) * paperQPilotLogLeast (l := l) T b)

/-- The actual d^{-1}-scaled root-ball log. -/
theorem paperNormalizedRootStackRootBallLog_eq
    (d : Nat) (hd : 0 < d)
    (h : NormalizedRootBallMassFormula (l := l) T b d) :
    paperNormalizedRootStackRootBallLog (l := l) T b d =
      (d : Real) * paperQPilotLogLeast (l := l) T b - Real.log (d : Real) := by
  unfold paperNormalizedRootStackRootBallLog paperNormalizedRootStackHaar
  rw [Measure.smul_apply, smul_eq_mul]
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (inv_nonneg.mpr (Nat.cast_nonneg d))]
  rw [h]
  rw [Real.log_mul]
  · rw [Real.log_exp, Real.log_inv]
    ring
  · exact inv_ne_zero (by exact_mod_cast (ne_of_gt hd))
  · exact (Real.exp_pos _).ne'

/-- The numeric d^{-1} scaling does not by itself give the paper qPilot log;
the exact equation is d*L - log d = L. -/
theorem paperNormalizedRootStackRootBallLog_eq_paper_iff
    (d : Nat) (hd : 0 < d)
    (h : NormalizedRootBallMassFormula (l := l) T b d) :
    paperNormalizedRootStackRootBallLog (l := l) T b d =
        paperQPilotLogLeast (l := l) T b ↔
      (d : Real) * paperQPilotLogLeast (l := l) T b - Real.log (d : Real) =
        paperQPilotLogLeast (l := l) T b := by
  rw [paperNormalizedRootStackRootBallLog_eq (l := l) T b d hd h]

/-- Exact correction factor that would make the root-ball log equal paperQPilotLogLeast. -/
noncomputable def paperRootStackHaarCorrectionFactor (d : Nat) : Real :=
  Real.exp ((1 - (d : Real)) * paperQPilotLogLeast (l := l) T b)

/-- The correction-factor-scaled Haar. -/
noncomputable def paperRootStackHaarCorrected (d : Nat) :
    Measure (rootStackExtension (l := l) T b) :=
  ENNReal.ofReal (paperRootStackHaarCorrectionFactor (l := l) T b d) •
    normalizedRootStackHaar (l := l) T b

/-- With the exact correction factor, the root-ball log is the paper qPilot log. -/
theorem paperRootStackHaarCorrected_rootBallLog
    (d : Nat) (hd : 0 < d)
    (h : NormalizedRootBallMassFormula (l := l) T b d) :
    Real.log
      ((paperRootStackHaarCorrected (l := l) T b d
        (Metric.closedBall (0 : rootStackExtension (l := l) T b)
          ‖(stackRootUnit (l := l) T b :
            rootStackExtension (l := l) T b)‖)).toReal) =
      paperQPilotLogLeast (l := l) T b := by
  unfold paperRootStackHaarCorrected paperRootStackHaarCorrectionFactor
  rw [Measure.smul_apply, smul_eq_mul]
  rw [ENNReal.toReal_mul]
  rw [ENNReal.toReal_ofReal (le_of_lt (Real.exp_pos _))]
  rw [h]
  rw [Real.log_mul (Real.exp_pos _).ne' (Real.exp_pos _).ne']
  rw [Real.log_exp, Real.log_exp]
  ring

/-- Audit target: paper normalization determines the correction factor. -/
def PaperNormalizationDeterminesCorrectionFactor (d : Nat) : Prop :=
  paperRootStackHaarCorrectionFactor (l := l) T b d = 1

end LeanFormal.IUT.XiFPaper.S833PaperNormalizedStackHaarActual

end
