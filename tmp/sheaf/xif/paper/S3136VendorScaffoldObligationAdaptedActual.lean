import tmp.sheaf.xif.paper.S3136VendorCor312SchemaAdaptedActual

/-! # Stage-4 host: vendor-scaffold obligation provider (adapted)

SOURCE: vendor/promachina/snapshots/1fa6387f11fb6dc67eb618b8138e6bc64f56b039/Iut/Stage1/IUTSourceScaffold.lean
(source reference only, not importable): IUTSourceObligationProvider, comparisonData,
stage1Comparison, corollary312, audit. Adapted here as a provider record bundling the
model Cor 3.12 comparison data with its endpoint inequality, in the shape of the model
SourceDefinition31Data assembly obligations.

Source anchors: IUT III, Corollary 3.12; IUT I, Definition 3.1 (source obligation
staging).

LABEL: prerequisite component adapted from vendor (source cited, no import); NOT a claim
of the numerical bridge. Registry frozen; new file only. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S3136VendorScaffoldObligationAdaptedActual

open LeanFormal.IUT.XiFPaper.S3136VendorCor312SchemaAdaptedActual

/-- The adapted source obligation provider: the model Cor 3.12 comparison data plus its
endpoint payload (vendor IUTSourceObligationProvider shape adaptation). -/
structure LGPModelObligationProvider where
  comparison : LGPModelCor312ComparisonData

namespace LGPModelObligationProvider

/-- The theta pilot of the obligation provider. -/
def thetaPilot (P : LGPModelObligationProvider) : LGPPilotLogVolume :=
  P.comparison.thetaPilot

/-- The q pilot of the obligation provider. -/
def qPilot (P : LGPModelObligationProvider) : LGPPilotLogVolume :=
  P.comparison.qPilot

/-- The Cor 3.12 endpoint payload of the obligation provider. -/
theorem corollary312 (P : LGPModelObligationProvider) :
    LGPModelCor312Inequality P.thetaPilot P.qPilot :=
  LGPModelCor312ComparisonData.corollary312 P.comparison

/-- The public audit payload (vendor publicAudit adaptation). -/
theorem publicAudit (P : LGPModelObligationProvider) :
    P.comparison.qSigned ≤ P.comparison.thetaSigned ∧
      LGPModelCor312Inequality P.thetaPilot P.qPilot :=
  LGPModelCor312ComparisonData.publicAudit P.comparison

end LGPModelObligationProvider

#check LGPModelObligationProvider
#check LGPModelObligationProvider.corollary312
#check LGPModelObligationProvider.publicAudit

end LeanFormal.IUT.XiFPaper.S3136VendorScaffoldObligationAdaptedActual
end