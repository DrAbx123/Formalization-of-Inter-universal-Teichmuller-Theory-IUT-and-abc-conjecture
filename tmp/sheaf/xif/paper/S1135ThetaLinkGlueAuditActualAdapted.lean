import tmp.sheaf.xif.paper.ThetaLinkLogKummerActual
import tmp.sheaf.xif.paper.S1125ThetaLinkAuditActual
import tmp.sheaf.xif.PaperXiFInclusion
import tmp.sheaf.xif.paper.S1133PaperLVExGluingActualAdapted

/-! # S1135: Theta-link labels / rho / glue audit

Audit only; no new link, label action, rho, or glue object.

Findings:
* The three Theta-link files contain no V/W label object and no rho/glue map.
  They use: V = source finite-place type; label/Label = paper finite label
  index; SignedLabel l.value = Theta label; FPrimeStrip V = strip vertices.
* ThetaLinkLogKummerActual supplies actual source carriers (one-column Kummer
  card, link factorization, Kummer/evaluation square, qPilot strip, signed
  image/hull volumes) but the link/square/comparison are exact structure fields.
* S1125 records that the gluing isomorphism is absent; its exact minimum is
  GlobalKummerTensorPacketIsoRequired.
* PaperXiFInclusion uses only scalar q-pilot/signed-hull data plus an exact
  link_identification/implies_inclusion; no label action or glue enters.
* S1133 supplies scalar rho = R/lambda and glue = R/rho as pure arithmetic,
  conditional on exact R <= S, R >= 0, rho > 1.  It is not a Theta-link/gluing
  isomorphism and cannot replace the exact link identification.

Answer to 'can one use only scalar rho?': for the xi-f inclusion, yes only the
scalar qPilotLogVolume/signedHullLogVolume are consumed, but that is because the
link comparison is an exact input; scalar rho is not a substitute for the
Theta-link/gluing identification.  For LVEx gluing, scalar rho/glue is actual
arithmetic only given the exact R <= S input. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1135ThetaLinkGlueAuditActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.ThetaLinkLogKummerActual
open LeanFormal.IUT.XiFPaper.S1125ThetaLinkAuditActual
open LeanFormal.IUT.XiFPaper.S1133PaperLVExGluingActualAdapted

universe ua uv upi umon ui uG uV
variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable (G : Type uG) [Group G] [TopologicalSpace G]

#check OneColumnLogKummerData
#check QPilotLinkIdentification
#check ThetaLinkFactorizationData
#check ThetaLinkSquareData
#check SignedHullComparison
#check ThetaLinkLogKummerActual
#check thetaLinkLogKummer_qPilotLogVolume_eq
#check thetaLinkLogKummer_signedComparison
#check S1125GluingExactMinimum
#check PaperXiFSourceLink
#check PaperXiFInclusion
#check PaperXiFInclusion.qPilot_mem_ray
#check PaperXiFInclusion.qPilot_le_signedHull
#check paperRho
#check paperGlue
#check paperGlue_le_R
#check paperGlue_le_S
#check S1133ExactInput

end LeanFormal.IUT.XiFPaper.S1135ThetaLinkGlueAuditActualAdapted
end
