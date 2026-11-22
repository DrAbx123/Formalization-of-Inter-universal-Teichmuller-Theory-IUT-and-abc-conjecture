import tmp.sheaf.xif.paper.S838QVFamilyDivisibilityActual
import tmp.sheaf.xif.paper.S827PaperValueGroupNormCardActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S840QVFamRamificationAuditActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamRootFactorCorrectionActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.S819PaperRootCompletionGeneratorActual
open LeanFormal.IUT.XiFPaper.S827PaperValueGroupNormCardActual
open LeanFormal.IUT.XiFPaper.S838QVFamilyDivisibilityActual
open LeanFormal.IUT.LocalFieldLogarithm

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-- Exact trivial-ramification condition for the qVFamily completion. -/
def QVFamRamificationExponentOne : Prop :=
  paperRamificationExponent (l := l) T b = 1

/-- The ramification exponent is always positive. -/
theorem qVFamRamificationExponent_pos :
    0 < paperRamificationExponent (l := l) T b := by
  unfold paperRamificationExponent
  exact logShellRamificationExponent_pos

/-- S838: e=1 gives the paper root value-group no-go. -/
theorem paperRootValueGroupNoGo_of_qVFam_e_one
    (he : QVFamRamificationExponentOne (l := l) T b) :
    PaperRootValueGroupNoGo (l := l) T b :=
  paperRootValueGroupNoGo_of_e_one (l := l) T b he

/-- Exact alignment condition between the log-shell exponent and the relative
ramification index.  This is not proved in the current tree. -/
def QVFamRamificationAlignment : Prop :=
  paperRamificationExponent (l := l) T b =
    relativeRamificationIndex (k := ℚ) (paperValueGroupPlace (l := l) T b)

/-- The exact condition for deciding e=1 through the relative index. -/
theorem qVFam_e_one_iff_relativeIndex_one
    (h : QVFamRamificationAlignment (l := l) T b) :
    QVFamRamificationExponentOne (l := l) T b ↔
      relativeRamificationIndex (k := ℚ) (paperValueGroupPlace (l := l) T b) = 1 := by
  unfold QVFamRamificationExponentOne QVFamRamificationAlignment at *
  rw [h]

/-- Exact minimal datum: the relative ramification index at the actual
qVFamTensorPlace is one. -/
def QVFamRelativeRamificationOne : Prop :=
  relativeRamificationIndex (k := ℚ) (paperValueGroupPlace (l := l) T b) = 1

end LeanFormal.IUT.XiFPaper.S840QVFamRamificationAuditActual

end
