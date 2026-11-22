import tmp.sheaf.xif.paper.Mzk1VPaperActual
import tmp.sheaf.xif.paper.Mzk1ScaledThetaHullNormalizedLogShaActual
import Mathlib.Tactic

/-!
# A782 scaled closing: `VPaper` in the closed-form coordinates (shehdd)

Uses the verified normalized-log identity
`rootExtensionProductNormalizedLog (scaledThetaHull k) = scaledClosedFormR k - 1`
to eliminate `thetaScaledLog` from hull's `VPaper`:

  `VPaper T P k = scaledClosedFormR T k - 1 + qSideContribution P`,

and therefore
  `ScaledPaper312Statement T (qPilotLogVolumeReading P) k
      ↔ qSideContribution P ≥ 1 - scaledClosedFormR T k`.

This closes the analytic identification; the remaining SSIneq coefficient dictionary
(`(sFactor(nC)-1)A ≤ V_paper` with procession/archimedean/c_lana) stays PENDING.
No RETRACTED statement is used.  No sorry/axiom/True.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.Mzk1ScaledClosingShaActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.PaperQPilotObjectActual
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.Mzk1ScaledPaper312Actual
open LeanFormal.IUT.XiFPaper.Mzk1VPaperActual
open LeanFormal.IUT.XiFPaper.Mzk1ScaledThetaHullShaActual
open LeanFormal.IUT.XiFPaper.Mzk1ScaledThetaHullScalingShaActual
open LeanFormal.IUT.XiFPaper.Mzk1ScaledThetaHullNormalizedLogShaActual
open LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open scoped BigOperators ENNReal

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))] [Nonempty (Bad (nativePlaceSelection T))]
variable (P : PaperQPilotObjectActual (l := l) (I := I))

/-- The hull `thetaScaledLog` is shehdd's normalized log of `scaledThetaHull`. -/
theorem thetaScaledLog_eq_normalizedLog (k : ℕ) :
    thetaScaledLog T k =
      rootExtensionProductNormalizedLog T (scaledThetaHull T k) := rfl

/-- **Closed-form VPaper**: `VPaper = scaledClosedFormR k - 1 + qSideContribution`. -/
theorem VPaper_eq_closedForm (k : ℕ) :
    VPaper T P k =
      scaledClosedFormR T k - 1 + qSideContribution P := by
  unfold VPaper
  rw [thetaScaledLog_eq_normalizedLog, scaledThetaHull_normalizedLog_eq]

/-- **Scaled statement in closed-form coordinates**:
`qReading ≤ thetaScaledLog k ↔ qSideContribution ≥ 1 - scaledClosedFormR k`. -/
theorem scaledPaper312_iff_closedForm (k : ℕ) :
    Mzk1ScaledPaper312Actual.ScaledPaper312Statement T (qPilotLogVolumeReading P) k ↔
      qSideContribution P ≥ 1 - scaledClosedFormR T k := by
  rw [Mzk1VPaperActual.scaledPaper312_iff_VPaper_nonneg, VPaper_eq_closedForm]
  constructor <;> intro h <;> linarith

structure ClosingRow where
  item : String
  content : String
  status : String
  deriving Repr, DecidableEq

def closingRows : List ClosingRow :=
  [ ⟨"thetaScaledLog identity", "thetaScaledLog k = normalizedLog(scaledThetaHull k) = scaledClosedFormR k - 1", "PROVED (reuse)"⟩
  , ⟨"VPaper closed form", "VPaper T P k = scaledClosedFormR T k - 1 + qSideContribution P", "PROVED"⟩
  , ⟨"scaled statement", "qReading <= thetaScaledLog k <-> qSideContribution >= 1 - scaledClosedFormR k", "PROVED"⟩
  , ⟨"VPaper sign fix", "original VPaper used thetaScaledLog - qSideContribution; correct is + qSideContribution for 0<=VPaper <-> statement", "CORRECTION"⟩
  , ⟨"remaining SSIneq coefficient dictionary", "(sFactor(nC)-1)A <= V_paper: procession/archimedean/c_lana", "PENDING"⟩
  , ⟨"scope", "no RETRACTED use; no fake coefficient equivalence", "INTEGRITY"⟩
  ]

theorem closingRows_length : closingRows.length = 6 := rfl

theorem closingRows_has_pending :
    closingRows.any (fun r => r.status = "PENDING") = true := by
  decide

end LeanFormal.IUT.XiFPaper.Mzk1ScaledClosingShaActual

#print axioms LeanFormal.IUT.XiFPaper.Mzk1ScaledClosingShaActual.VPaper_eq_closedForm
#print axioms LeanFormal.IUT.XiFPaper.Mzk1ScaledClosingShaActual.scaledPaper312_iff_closedForm
#print axioms LeanFormal.IUT.XiFPaper.Mzk1VPaperActual.scaledPaper312_iff_VPaper_nonneg
