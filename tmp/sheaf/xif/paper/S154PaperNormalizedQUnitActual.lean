import tmp.sheaf.xif.paper.S64DependentThetaHullActual
import tmp.sheaf.xif.paper.RootNormalizedContainmentActual
import tmp.sheaf.xif.paper.QVFamNormalizedCoefficientBridgeActual

/-!
# S154: qPilot side in the same normalized mu_log

The qPilot side is defined directly from the normalized norm:

  qVFamNormalizedQPilotLog
    = - sum_b weight_b * log ||qVFamily_b||_normalized.

This is the same normalized mu_log used by the per-b normalized q-pilot region.
It equals the existing global qPilot scalar, and therefore the uncorrected
paper-normalized comparison follows from the per-b normalized qPilot <= Theta
hull inequality.  No norm-ratio correction and no QVFamNormInstanceGap is used.
The latter remains only diagnostic.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S154PaperNormalizedQUnitActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedCoefficientBridgeActual
open LeanFormal.IUT.XiFPaper.RootNormalizedContainmentActual
open LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetProofActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.S64DependentThetaHullActual
open LeanFormal.IUT.ArithmeticQPilotBaseChange
open MeasureTheory

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]

/-- qPilot side directly in the normalized mu_log of qVFamNormalizedNorm. -/
noncomputable def qVFamNormalizedQPilotLog : Real :=
  ∑ b : Bad (nativePlaceSelection T),
    nativeBadLocalWeight T b * Real.log (qVFamNormalizedNorm T b)

/-- Per-b qPilot scalar is the negative normalized coefficient times log p. -/
theorem perBQPilotLog_eq_neg_cNorm_mul_logp
    (b : Bad (nativePlaceSelection T)) :
    perBQPilotLog T b =
      -qVFamNormalizedCoefficient T b *
        Real.log (qVFamTensorP T b : Real) := by
  unfold perBQPilotLog
  rw [qPilotNormLog_eq (T := T) (b := b)]
  unfold rootNormCoefficient qVFamNormalizedCoefficientFamily
  simp

/-- The normalized qPilot log is the existing global qPilot scalar. -/
theorem qVFamNormalizedQPilotLog_eq_globalQPilotLog :
    qVFamNormalizedQPilotLog T = globalQPilotLog T := by
  unfold qVFamNormalizedQPilotLog globalQPilotLog
  apply Finset.sum_congr rfl
  intro b _
  rw [perBQPilotLog_eq_neg_cNorm_mul_logp T b]
  have h := qVFamNormalizedCoefficient_mul_log_eq_neg_log_norm T b
  have h' : -qVFamNormalizedCoefficient T b *
      Real.log (qVFamTensorP T b : Real) =
      Real.log (qVFamNormalizedNorm T b) := by
    linarith
  rw [h']

/-- The actual normalized qPilot value is the normalized mu_log sum. -/
theorem qVFamNormalizedQPilotLog_eq_normalizedMuLog :
    qVFamNormalizedQPilotLog T =
      ∑ b : Bad (nativePlaceSelection T),
        nativeBadLocalWeight T b * Real.log (qVFamNormalizedNorm T b) := by
  rfl

/-- Uncorrected paper-normalized comparison, with both sides in the same
normalized qPilot mu_log. -/
def PaperNormalizedUncorrectedComparison : Prop :=
  qVFamNormalizedQPilotLog T ≤ globalThetaHullLog T

/-- The uncorrected paper-normalized comparison is proved from the actual
per-b normalized qPilot <= root hull inequality. -/
theorem paperNormalizedUncorrectedComparison :
    PaperNormalizedUncorrectedComparison T := by
  unfold PaperNormalizedUncorrectedComparison
  rw [qVFamNormalizedQPilotLog_eq_globalQPilotLog]
  exact globalQPilotLog_le_globalThetaHullLog T

/-- Diagnostic only: the norm-instance gap is not a dependency of the
uncorrected comparison. -/
def QVFamNormInstanceGapDiagnosticOnly
    (b : Bad (nativePlaceSelection T)) : Prop :=
  QVFamNormInstanceGap T b

end LeanFormal.IUT.XiFPaper.S154PaperNormalizedQUnitActual

end
