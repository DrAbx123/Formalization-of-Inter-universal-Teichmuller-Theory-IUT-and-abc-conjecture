import tmp.sheaf.xif.paper.Mzk1ResolvedRequirementAcceptanceShaActual
import tmp.sheaf.xif.paper.Mzk1Cor312SignedMagnitudeChecksActual
import tmp.sheaf.xif.paper.Mzk1XiEContainmentRequirementActual

/-!
# shehdd A596/A599 strict-chain summary (thin re-export)

Thin re-exports of the resolved strict chain: signed/magnitude equivalences,
`C_Theta >= -1`, and the non-vacuous xi-e requirement signed inequalities.
(Canonical names `Mzk1StrictChainSummaryActual` etc. are mainline-exclusive;
this file uses the shehdd `Sha` suffix.)

No sorry, axiom, True or placeholder.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1StrictChainSummaryShaActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.Mzk1KummerRealizationActual
open LeanFormal.IUT.XiFPaper.Mzk1XiEContainmentRequirementActual
open LeanFormal.IUT.XiFPaper.Mzk1Cor312SignedMagnitudeChecksActual

theorem summary_signed_iff {qMag thetaMag : Real} :
    -thetaMag ≤ -qMag ↔ qMag ≤ thetaMag :=
  signed_ineq_iff_magnitude

theorem summary_signed_strict_iff {qMag thetaMag : Real} :
    -thetaMag < -qMag ↔ qMag < thetaMag :=
  signed_strict_iff_magnitude

theorem summary_ctheta_ge {qMag C : Real} (hq : 0 < qMag)
    (h : -qMag ≤ C * qMag) : -1 ≤ C :=
  CTheta_ge_neg_one_of_signed hq h

theorem summary_requirement_strict {α : Type} {vol : Set α → Real}
    (D : XiEContainmentRequirement α vol) :
    requirementSignedQ D < requirementSignedTheta D :=
  requirement_strict_signed D

theorem summary_requirement_weak {α : Type} {vol : Set α → Real}
    (D : XiEContainmentRequirement α vol) :
    requirementSignedQ D ≤ requirementSignedTheta D :=
  requirement_signed_inequality D

theorem summary_accepted_strict {l : PrimeGeFive}
    (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))] (R : PaperKummerReading T) :
    R.qReading < R.thetaReading :=
  paperKummerReading_strict T R

end LeanFormal.IUT.XiFPaper.Mzk1StrictChainSummaryShaActual
