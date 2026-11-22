/-! # Stage-4 host: index of paper-input artifacts for the paper route

Data-only index of all paper-input/statement artifacts produced in this stream,
for mainline's paper-input statement file and FINAL-STATUS cross references.

LABEL: index (data). Registry frozen; new file only. -/

namespace LeanFormal.IUT.XiFPaper.S3136PaperInputIndexActual

structure LGPInputArtifactRow where
  artifact : String
  file : String
  declarationOrCount : String
  purpose : String

def lgpPaperInputIndex : List LGPInputArtifactRow :=
  [ ⟨"GenEll exact statements", "S3136GenEllPaperStatementsActual", "lgpGenEllStatements (8 rows)", "input statement ledger"⟩,
    ⟨"GenEll/[Mzk1] statement details", "S3136GenEllStatementDetailsActual", "lgpGenEllStatementDetails (10 rows)", "detailed citations for statement file"⟩,
    ⟨"(c) source classification", "S3136RegionEstimateSourceClassificationActual", "lgpRegionEstimateSourceClassification (10 rows; 5 classA)", "class A/B table for (c)"⟩,
    ⟨"(c) IV hypothesis map", "S3136IVClassBHypothesisMapActual", "lgpIVClassBHypothesisMap (8 rows)", "constructible pieces -> IV hypotheses"⟩,
    ⟨"IUT IV Thm 1.10 constants", "S3136IVThm110ConstantsActual", "lgpDStarMod/lgpEStarMod/lgpCThetaShape/lgpThm110DisplayShape", "class A constant arithmetic + display shapes"⟩,
    ⟨"BD-class chain tool", "S3136BDClassChainToolActual", "IsBDLe/IsBDEq + lemmas", "class A BD-class composition"⟩,
    ⟨"Cor 2.2 (i) chain instance", "S3136Cor22BDChainInstanceActual", "LGPCor22ChainData.composite", "class A Cor 2.2 (i) composition"⟩,
    ⟨"GenEll Thm 2.1 equivalence shape", "S3136GenEllReductionShapeActual", "LGPGenEllEquivalence/lgpGenEll_reduction", "reduction statement hook"⟩,
    ⟨"Theta-pilot data shape", "S3136ThetaPilotDataShapeActual", "LGPThetaPilotData/lgpCor312LogQ", "Cor 3.12 shape hook"⟩,
    ⟨"statement hooks", "S3136PaperInputStatementHooksActual", "LGPTheoremAShape/LGPGenEllThm21Shape", "definitional shapes using IsBDLe"⟩ ]

theorem lgpPaperInputIndex_length : lgpPaperInputIndex.length = 10 := rfl

#check lgpPaperInputIndex
#check lgpPaperInputIndex_length

end LeanFormal.IUT.XiFPaper.S3136PaperInputIndexActual