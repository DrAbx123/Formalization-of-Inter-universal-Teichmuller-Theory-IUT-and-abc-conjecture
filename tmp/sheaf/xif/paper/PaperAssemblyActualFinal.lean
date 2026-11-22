import tmp.sheaf.xif.paper.QPilotObjectFromSource
import tmp.sheaf.xif.paper.OneColumnActual
import tmp.sheaf.xif.paper.ArithmeticLineBundleActual
import tmp.sheaf.xif.paper.PaperLineBundleCarrierBase
import tmp.sheaf.xif.paper.IPLAPTDataActual
import tmp.sheaf.xif.paper.PaperThetaLinkDataActual
import tmp.sheaf.xif.paper.PaperThetaLinkNontrivial
import tmp.sheaf.xif.paper.SignedHullNormalizationBridge
import tmp.sheaf.xif.paper.HaarThetaAverageProof
import tmp.sheaf.xif.paper.SHEOperationsFromSource
import tmp.sheaf.xif.paper.SHEAlgorithmFromSource
import tmp.sheaf.xif.paper.APTComparisonFromSource
import tmp.sheaf.xif.paper.ThetaLinkActual
import tmp.sheaf.xif.paper.ThetaLinkFromSource
import tmp.sheaf.xif.paper.IQCarrierFromSource
import tmp.sheaf.xif.paper.SHEOutputAlignmentActual
import tmp.sheaf.xif.paper.SHEProcessionLandingProof
import tmp.sheaf.xif.paper.ProcessionAlignmentActual

/-!
# Actual xi-f paper assembly: final conditional gate

This file is a gate, not a new proof. It imports the actual xi-f modules and
#checks their production/conditional declarations, together with the exact
missing-object primitives. No new theorem/axiom is introduced.

WRITE-ONLY: no lake is run in this task.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.PaperAssemblyActualFinal

/-! ## Actual Q-pilot / one-column declarations -/
#check LeanFormal.IUT.N8Closure.PaperQPilotObjectActual.paperQPilotObjectOfSource
#check LeanFormal.IUT.N8Closure.PaperQPilotObjectActual.paperQPilotObjectOfNumberFieldSource
#check LeanFormal.IUT.N8Closure.PaperQPilotObjectActual.qPilotIdentificationOfNumberFieldSource
#check LeanFormal.IUT.N8Closure.PaperQPilotObjectActual.sourceOneColumnActual
namespace LeanFormal.IUT.N8Closure.PaperQPilotObjectActual
#check LeanFormal.IUT.N8Closure.PaperQPilotObjectActual.sourceOneColumnActual
end LeanFormal.IUT.N8Closure.PaperQPilotObjectActual

/-! ## Actual arithmetic line bundle -/
#check LeanFormal.IUT.XiFPaperArithmeticLineBundle.PaperArithmeticLineBundleActual
#check LeanFormal.IUT.XiFPaperArithmeticLineBundle.actualUnitLineBundleData
#check LeanFormal.IUT.XiFPaperArithmeticLineBundle.unitLocalizationMap

namespace LeanFormal.IUT.XiFPaperArithmeticLineBundle
#check LeanFormal.IUT.XiFPaperArithmeticLineBundle.actualUnitLineBundleData
end LeanFormal.IUT.XiFPaperArithmeticLineBundle

namespace LeanFormal.IUT.XiFPaperArithmeticLineBundle.PaperArithmeticLineBundleActual
#check LeanFormal.IUT.XiFPaperArithmeticLineBundle.PaperArithmeticLineBundleActual.rank_one
end LeanFormal.IUT.XiFPaperArithmeticLineBundle.PaperArithmeticLineBundleActual

namespace LeanFormal.IUT.Theorem311Source.IPLAPTDataActual
#check LeanFormal.IUT.Theorem311Source.IPLAPTDataActual.selfIplActual
#check LeanFormal.IUT.Theorem311Source.IPLAPTDataActual.selfKummerEvaluationActual
end LeanFormal.IUT.Theorem311Source.IPLAPTDataActual

namespace LeanFormal.IUT.XiFPaper.PaperThetaLinkDataActual
#check LeanFormal.IUT.XiFPaper.PaperThetaLinkDataActual.selfPaperThetaLinkData
end LeanFormal.IUT.XiFPaper.PaperThetaLinkDataActual

namespace LeanFormal.IUT.XiFPaper.PaperThetaLinkNontrivial
#check @LeanFormal.IUT.XiFPaper.PaperThetaLinkNontrivial.NontrivialThetaLinkActual.toPaperThetaLinkData
#check LeanFormal.IUT.XiFPaper.PaperThetaLinkNontrivial.NontrivialThetaLinkActual
end LeanFormal.IUT.XiFPaper.PaperThetaLinkNontrivial

namespace LeanFormal.IUT.XiFPaper
#check paperProcessionNormalizationComparison
#check hnormal_of_paperComparison
#check ExactMissingHaarThetaFactorization
end LeanFormal.IUT.XiFPaper

namespace LeanFormal.IUT.Theorem311Source.SHEOperationsFromSource
#check LeanFormal.IUT.Theorem311Source.SHEOperationsFromSource.actualSHEOperation
#check LeanFormal.IUT.Theorem311Source.SHEOperationsFromSource.actualSHEOperation_landing
#check LeanFormal.IUT.Theorem311Source.SHEOperationsFromSource.paperSHEMissing_actual
end LeanFormal.IUT.Theorem311Source.SHEOperationsFromSource

namespace LeanFormal.IUT.Theorem311Source.SHEAlgorithmFromSource
#check LeanFormal.IUT.Theorem311Source.SHEAlgorithmFromSource.actualSourceAlgorithm
#check LeanFormal.IUT.Theorem311Source.SHEAlgorithmFromSource.actualSourceAlgorithm_nontrivial
end LeanFormal.IUT.Theorem311Source.SHEAlgorithmFromSource

namespace LeanFormal.IUT.Theorem311Source.APTComparisonFromSource
#check LeanFormal.IUT.Theorem311Source.APTComparisonFromSource.actualTwoColumnComparison
#check LeanFormal.IUT.Theorem311Source.APTComparisonFromSource.actualTwoColumnComparison_nontrivial
#check LeanFormal.IUT.Theorem311Source.APTComparisonFromSource.actualAPTStatement_of_landing
end LeanFormal.IUT.Theorem311Source.APTComparisonFromSource

namespace LeanFormal.IUT.XiFPaper.ThetaLink
#check LeanFormal.IUT.XiFPaper.ThetaLink.thetaLinkComparisonData
#check LeanFormal.IUT.XiFPaper.ThetaLink.thetaLinkXiFMembership
#check LeanFormal.IUT.XiFPaper.ThetaLink.thetaLinkCertificate
end LeanFormal.IUT.XiFPaper.ThetaLink

namespace LeanFormal.IUT.XiFPaper.ThetaLinkFromSource
#check LeanFormal.IUT.XiFPaper.ThetaLinkFromSource.ActualThetaLink
#check LeanFormal.IUT.XiFPaper.ThetaLinkFromSource.actualThetaLink
#check LeanFormal.IUT.XiFPaper.ThetaLinkFromSource.actualThetaLink_xiFInequality
#check LeanFormal.IUT.XiFPaper.ThetaLinkFromSource.MissingSourceComparison
end LeanFormal.IUT.XiFPaper.ThetaLinkFromSource

namespace LeanFormal.IUT.N8Closure.PaperIQCarrierActual
#check LeanFormal.IUT.N8Closure.PaperIQCarrierActual.actualIQCarrierDischarges
#check LeanFormal.IUT.N8Closure.PaperIQCarrierActual.actualMissingFields
#check LeanFormal.IUT.N8Closure.PaperIQCarrierActual.actualIQCarrierFieldStatus
end LeanFormal.IUT.N8Closure.PaperIQCarrierActual

namespace LeanFormal.IUT.Theorem311Source.SHEOutputAlignmentActual
#check LeanFormal.IUT.Theorem311Source.SHEOutputAlignmentActual.OutputCarrierAlignment
#check LeanFormal.IUT.Theorem311Source.SHEOutputAlignmentActual.SHELandingForProcessionChoice
end LeanFormal.IUT.Theorem311Source.SHEOutputAlignmentActual

namespace LeanFormal.IUT.Theorem311Source.SHEProcessionLandingProof
#check LeanFormal.IUT.Theorem311Source.SHEProcessionLandingProof.ProcessionChoiceLanding
#check LeanFormal.IUT.Theorem311Source.SHEProcessionLandingProof.SourceProcessionAlignmentPrimitive
end LeanFormal.IUT.Theorem311Source.SHEProcessionLandingProof

namespace LeanFormal.IUT.Theorem311Source.ProcessionAlignmentActual
#check LeanFormal.IUT.Theorem311Source.ProcessionAlignmentActual.ProcessionAlignment
end LeanFormal.IUT.Theorem311Source.ProcessionAlignmentActual

/- Exact missing objects recorded by the gate:
1. ProcessionChoice output alignment/landing:
   ProcessionAlignment, OutputCarrierAlignment, SHELandingForProcessionChoice,
   SHELandingForAlgorithmOutput.
2. Q-pilot/log identification and arithmetic line-bundle source identification;
3. Theta-link missing source comparison (`MissingSourceComparison`);
4. Haar/Theta factorization (`ExactMissingHaarThetaFactorization`);
5. IQ carrier O-module/compactness/unit/log-volume missing fields
   (`actualMissingFields`).
No new theorem/axiom is introduced; only existing actual/conditional
declarations and their exact missing primitives are checked. -/

end LeanFormal.IUT.XiFPaper.PaperAssemblyActualFinal

end
