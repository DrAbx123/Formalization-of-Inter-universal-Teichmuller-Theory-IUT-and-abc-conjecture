import tmp.sheaf.xif.paper.Mzk1Cor312AcceptanceFinalActual
import tmp.sheaf.xif.paper.Mzk1Cor312AcceptanceResolvedV2
import tmp.sheaf.xif.paper.Mzk1AcceptanceEvidenceBundleActual
import tmp.sheaf.xif.paper.Mzk1Cor312AcceptanceGreenSummaryActual

/-! # Cor 3.12 acceptance green bundle (wrap-up) -/

namespace LeanFormal.IUT.XiFPaper.Mzk1Cor312AcceptanceGreenBundleActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.Mzk1PositiveMeasureQRegionProofActual
open LeanFormal.IUT.XiFPaper.Mzk1XiEContainmentRequirementActual
open LeanFormal.IUT.XiFPaper.Mzk1Cor312AcceptanceFinalActual
open LeanFormal.IUT.XiFPaper.Mzk1Cor312AcceptanceResolvedV2
open LeanFormal.IUT.XiFPaper.Mzk1Cor312FinalAssemblyActual
open LeanFormal.IUT.XiFPaper.Mzk1KummerRealizationActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData l)

/-- Green bundle resolved path (V3): strict_measure derived from positive Haar. -/
theorem bundle_resolved [Fintype (Bad (nativePlaceSelection T))]
    (D : PositiveQRegionHaarStrict T)
    (hqneg : requirementSignedQ (resolvedRequirement T D) < 0)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt) :
    Cor312Conclusion
      (requirementContract (resolvedRequirement T D) hqneg ipl hipl she hshe apt hapt) :=
  acceptanceFinal_resolved T D hqneg ipl hipl she hshe apt hapt

/-- Green bundle paper path (final assembly). -/
theorem bundle_paper [Fintype (Bad (nativePlaceSelection T))]
    (R : PaperKummerReading T)
    (hqneg : requirementSignedQ (requirementOfReading T R) < 0)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt) :
    Cor312Conclusion (cor312Contract_final T R hqneg ipl hipl she hshe apt hapt) :=
  acceptanceFinal_paper T R hqneg ipl hipl she hshe apt hapt

/-- Green bundle: axiom payload for the two acceptance conclusions. -/
#print axioms bundle_resolved
#print axioms bundle_paper

end LeanFormal.IUT.XiFPaper.Mzk1Cor312AcceptanceGreenBundleActual
