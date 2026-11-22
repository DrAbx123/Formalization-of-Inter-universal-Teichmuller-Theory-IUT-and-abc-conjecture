import tmp.sheaf.xif.paper.S706ThetaPilotHullLogActual
import tmp.sheaf.xif.paper.S766QPilot2LNormalizationActual
import tmp.sheaf.xif.paper.QVFamRootFactorCorrectionActual
import tmp.sheaf.xif.paper.QPilotZeroLocusDivisorActual

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S773RootCorrectedPaperTargetActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S706ThetaPilotHullLogActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamRootFactorCorrectionActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]

/-- Root-corrected paper q-pilot magnitude: classical degree divided by 2l. -/
noncomputable def rootCorrectedQPilotMagnitude : Real :=
  -globalQPilotLog T / (2 * (l.value : Real))

/-- Root-corrected paper target: |log Theta| <= |log q| with the 2l-corrected
q-pilot magnitude. -/
def RootCorrectedThetaQpilotComparison : Prop :=
  thetaPilotMagnitude T ≤ rootCorrectedQPilotMagnitude T

/-- Exact equivalent signed form of the root-corrected comparison. -/
theorem rootCorrectedComparison_iff_signed :
    RootCorrectedThetaQpilotComparison T ↔
      globalQPilotLog T ≤ (2 * (l.value : Real)) * globalThetaPilotHullLog T := by
  unfold RootCorrectedThetaQpilotComparison rootCorrectedQPilotMagnitude
    thetaPilotMagnitude globalThetaPilotHullLog globalQPilotLog
  have hl : (0 : Real) < (l.value : Real) := by exact_mod_cast l.prime.pos
  have h2 : (0 : Real) < 2 * (l.value : Real) := by positivity
  constructor
  · intro h
    have h' := (le_div_iff₀ h2).mp h
    linarith
  · intro h
    rw [le_div_iff₀ h2]
    linarith

/-- Conditional root-corrected target from the exact 2l hull inequality. -/
theorem rootCorrectedComparison_of_twoL_hull
    (h : globalQPilotLog T ≤
      (2 * (l.value : Real)) * globalThetaPilotHullLog T) :
    RootCorrectedThetaQpilotComparison T :=
  (rootCorrectedComparison_iff_signed T).mpr h

/-- Exact gap of the root-corrected target. -/
def RootCorrectedThetaQpilotGap : Prop :=
  globalQPilotLog T ≤ (2 * (l.value : Real)) * globalThetaPilotHullLog T

/-- Paper root Theta coefficient is j^2 * order / (2l). -/
theorem paperThetaCoefficient_eq_root (b : Bad (nativePlaceSelection T))
    (j : SignedLabel l.value) :
    qVFamPaperThetaTensorCoefficient T b j =
      ((gaussExponent j.1).toNat : Real) *
        (((qVFamily T b).order : Real) / (2 * (l.value : Real))) := by
  unfold qVFamPaperThetaTensorCoefficient qVFamPaperRootCoefficient
  ring

end LeanFormal.IUT.XiFPaper.S773RootCorrectedPaperTargetActual
end