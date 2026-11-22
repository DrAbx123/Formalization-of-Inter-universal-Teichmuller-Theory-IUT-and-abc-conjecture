import tmp.sheaf.xif.paper.S773RootCorrectedPaperTargetActual
import tmp.sheaf.xif.paper.S706ThetaPilotHullLogActual

/-! # S781: sign/2l gap between S706 and S773

S706 gives qPilotLog ≤ thetaHullLog.  S773's corrected target is
qPilotLog ≤ 2l * thetaHullLog, which is strictly stronger for nonpositive
thetaHullLog and 2l > 1.  The actual inequality therefore does not imply it.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S781TwoLTargetGapActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]

/-- S773 signed 2l target, with all instances explicit. -/
def TwoLTarget (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))]
    [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
    [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)] : Prop :=
  S706ThetaPilotHullLogActual.globalQPilotLog T ≤
    (2 * (l.value : Real)) *
      S706ThetaPilotHullLogActual.globalThetaPilotHullLog T

/-- S706 actual inequality. -/
theorem actualQPilotLeTheta :
    S706ThetaPilotHullLogActual.globalQPilotLog T ≤
      S706ThetaPilotHullLogActual.globalThetaPilotHullLog T :=
  PaperLevelXiFTargetProofActual.globalQPilotLog_le_globalThetaHullLog T

/-- Pure real counterexample: q ≤ θ does not imply q ≤ (2l)θ for l ≥ 5. -/
theorem actualInequality_does_not_imply_twoLTarget_real :
    ¬ (∀ q θ : Real, q ≤ θ →
        q ≤ (2 * (l.value : Real)) * θ) := by
  intro h
  have hq : (-3 : Real) ≤ (-2 : Real) := by norm_num
  have ht := h (-3) (-2) hq
  have hl : (2 : Real) ≤ 2 * (l.value : Real) := by
    have h5 : (5 : Real) ≤ l.value := by exact_mod_cast l.ge_five
    nlinarith
  nlinarith

/-- Exact target proposition. -/
def TwoLTargetGap : Prop :=
  TwoLTarget T

def TwoLTargetGapRequired : Prop :=
  TwoLTargetGap T

/-- Conditional target from an explicit 2l inequality. -/
theorem twoLTarget_of_explicit
    (h : S706ThetaPilotHullLogActual.globalQPilotLog T ≤
      (2 * (l.value : Real)) *
        S706ThetaPilotHullLogActual.globalThetaPilotHullLog T) :
    TwoLTarget T :=
  h

end LeanFormal.IUT.XiFPaper.S781TwoLTargetGapActual
end
