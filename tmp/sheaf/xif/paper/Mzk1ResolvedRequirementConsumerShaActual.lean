import tmp.sheaf.xif.paper.Mzk1ResolvedRequirementAcceptanceShaActual

/-!
# A589 resolved-acceptance consumer (shehdd)

Consumer projections of `resolvedRequirementAcceptance`: the resolved xi-e
requirement yields the Cor 3.12 signed conclusion for arbitrary real IPL/SHE/APT
evidence, and the accepted paper strict inequality.

No sorry, axiom, True or placeholder.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1ResolvedRequirementConsumerShaActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.Mzk1KummerRealizationActual
open LeanFormal.IUT.XiFPaper.Mzk1XiEContainmentRequirementActual
open LeanFormal.IUT.XiFPaper.Mzk1ResolvedRequirementAcceptanceShaActual

universe u

theorem resolved_requirement_cor312 {α : Type u} {vol : Set α → Real}
    (D : XiEContainmentRequirement α vol)
    (hqneg : requirementSignedQ D < 0)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt) :
    Cor312Conclusion (requirementContract D hqneg ipl hipl she hshe apt hapt) :=
  (resolvedRequirementAcceptance).requirement_cor312 D hqneg ipl hipl she hshe apt hapt

theorem resolved_requirement_strict {α : Type u} {vol : Set α → Real}
    (D : XiEContainmentRequirement α vol) :
    requirementSignedQ D < requirementSignedTheta D :=
  (resolvedRequirementAcceptance).requirement_strict D

theorem resolved_accepted_strict {l : PrimeGeFive}
    (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))] (R : PaperKummerReading T) :
    R.qReading < R.thetaReading :=
  paperKummerReading_strict T R

end LeanFormal.IUT.XiFPaper.Mzk1ResolvedRequirementConsumerShaActual
