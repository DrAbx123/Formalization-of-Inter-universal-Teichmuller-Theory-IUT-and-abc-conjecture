import tmp.sheaf.xif.paper.PaperXiFSpec
import tmp.sheaf.xif.paper.QPilotObjectActual
import tmp.sheaf.xif.paper.QPilotIdentificationActual
import tmp.sheaf.xif.paper.QPilotScalarIdentificationActual
import tmp.sheaf.xif.paper.QPilotIdentificationConstruction
import tmp.sheaf.xif.paper.OneColumnActual
import tmp.sheaf.xif.paper.IQCarrierObligationsActual
import tmp.sheaf.xif.paper.SHEMissingActual
import tmp.sheaf.xif.paper.IndActionsActual
import tmp.sheaf.xif.paper.ThetaHullActual
import tmp.sheaf.xif.paper.ThetaHullIdentificationActual
import tmp.sheaf.xif.paper.SignedHullLogActual
import tmp.sheaf.xif.paper.SignedHullNormalizationActual
import tmp.sheaf.xif.paper.HullPacketActual
import tmp.sheaf.xif.paper.PaperIQCarrierActual
import tmp.sheaf.xif.paper.OModuleActual
import tmp.sheaf.xif.paper.DeterminantLogVolumeActual
import tmp.sheaf.xif.paper.IndeterminaciesActual
import tmp.sheaf.xif.paper.SHELandingActual
import tmp.sheaf.xif.paper.SHEOutputActual
import tmp.sheaf.xif.paper.IPLAPTActual
import tmp.sheaf.xif.paper.ThetaLinkActual
import tmp.sheaf.xif.paper.ThetaLinkLogKummerActual
import tmp.sheaf.xif.PaperXiFInclusion
import tmp.sheaf.xif.PaperCertificate
import tmp.sheaf.xif.paper.PaperXiFTheorem
import tmp.sheaf.xif.paper.PaperXiFProof
import tmp.sheaf.xif.paper.PaperXiFUnconditional

/-! # Paper-level xi-f compile gate and consumer surface

This file imports the actual paper-level modules together and checks the
central declarations. It is an assembly/consumer gate, not a new axiom or
a value-layer surrogate. The source identifications recorded as structure
fields remain exact obligations.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.CompileGate

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.XiFPaper

#check paperXiF
#check paperSignedLog
#check paperHullRay
#check PaperXiFScalarData
#check LeanFormal.IUT.XiFPaper.Proof.paperXiF_of_thetaLink
#check LeanFormal.IUT.XiFPaper.Proof.paperXiFResult_of_obligations
#check LeanFormal.IUT.XiFPaper.PaperUnconditionalData
#check LeanFormal.IUT.XiFPaper.paperXiF_conditional_status
#check LeanFormal.IUT.N8Closure.PaperQPilotObjectActual.signedQPilotLogVolume_eq_paperQPilotLogVolume
#check LeanFormal.IUT.N8Closure.PaperQPilotObjectActual.signedQPilotLogVolume_eq_neg_abs_qParameter
#check LeanFormal.IUT.N8Closure.PaperQPilotIdentificationActual.qPilotIdentificationActualOfCanonical
#check LeanFormal.IUT.N8Closure.PaperQPilotObjectActual.sourceOneColumnActual
#check LeanFormal.IUT.N8Closure.PaperQPilotObjectActual.paperQPilotObjectActualOfNumberField
#check LeanFormal.IUT.N8Closure.PaperIQCarrierActual.image_subset_c6Hull_of_obligations
#check LeanFormal.IUT.N8Closure.PaperIQCarrierActual.paperIQCarrierActualOfObligations
#check LeanFormal.IUT.Theorem311Source.SHELandingActual.paperSHEMissing_actual
#check LeanFormal.IUT.XiFPaper.paperIndActionsMissing_actual

/-- Assembly surface: the paper-level conditional xi-f theorem is available
from the explicit Theta-link identification. This is a re-export, not a new
mathematical assumption. -/
theorem paperXiF_assembly_conditional
    {l : PrimeGeFive} {V : Type uv}
    {Label : Type uL} {Choice : Type uC} [AddGroup Label] [Preorder Choice]
    {I : OriginalInput l V}
    {G : Type uG} [Group G] [TopologicalSpace G]
    {envStrip : FPrimeStrip V}
    {X : Type uX} {label : Type uLabel} [Fintype label] [Nonempty label]
    {O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip}
    {P : PaperSignedHull X label}
    {C3 : SourcePilotRegionData I}
    (L : LeanFormal.IUT.XiFPaper.ThetaLink.ThetaLinkActual O P C3)
    (hlink : L.link_identification) :
    paperXiF (paperQParameter C3) P.signedHullLogVolume :=
  LeanFormal.IUT.XiFPaper.Proof.paperXiF_of_thetaLink L hlink

end CompileGate
end XiFPaper
end LeanFormal.IUT

end