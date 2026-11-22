set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# STEP 0 prior-art: (hand-written endgame rows only; content mirrors coord/ENDGAME-DEPENDENCY-LEDGER.md A39 and mainline's pasted H3 row) -> no new proof.

# Theta-side endgame rows (corrected, for FINAL-STATUS/endgame ledger paste)

Registry frozen 14041.  These rows are DATA records; no closure claims.
-/

namespace LeanFormal.IUT.XiFPaper.S3132ThetaSideEndgameRowsActual

/-- One endgame dependency row. -/
structure EndgameRow where
  id : String
  statement : String
  evidence : String
  status : String

/-- Corrected Theta-side endgame rows H1-H6. -/
def thetaSideEndgameRows : List EndgameRow :=
  [ { id := "H1", statement := "concrete clause data LGPModelSourceClauseMissing / LGPConcreteClauseData",
      evidence := "S3136ModelSourceClauseActual; S3136ModelClauseWitnessAdapterActual (stage4)",
      status := "DATA residual" }
  , { id := "H2", statement := "weighted rooted identity R2: sourceVFormLogVolume = sum_b w_b * rootThetaHullLog_b",
      evidence := "S3132ThetaSideSharpResidualReducedActual (sharp residual = R2 exactly); R1 free via S3132RootedScalingDataTrivialActual",
      status := "sharp residual (paper log-volume dictionary)" }
  , { id := "H3", statement := "CORRECTED: order/(2l) = e * rootHalfCoefficient; c_norm = order iff e = 1; hc is e=1 specialization, NOT paper-faithful; R2 uses rootHalfCoefficient and needs no hc",
      evidence := "S3131CoefficientReductionActual:150; S826CNormOrderRamificationActual:64; S3132RootedCoefficientCorrectionActual (CITABLE 162986)",
      status := "superseded 'hc DATA' wording; precise row adopted" }
  , { id := "H4", statement := "hull-volume <= theta",
      evidence := "S3132ThetaSideHullSlotWiringActual; adapts CertificateHullWiring:106/272 + CardAMPL:78/94/116/125",
      status := "certificate-hull/AMPL boundary (CardQCMPComparison:50-68); not proved" }
  , { id := "H5", statement := "q-side signed comparison",
      evidence := "S3132ThetaSideQSideSlotWiringActual; adapts SourceQSideComparison:88/96/125/140/184",
      status := "explicit hypothesis (q-side stream)" }
  , { id := "H6", statement := "[GenEll] transfer",
      evidence := "S3132IVGenEllShadowAdapterActual; [GenEll] Theorem 2.1 (corpus) reduction, NOT proof of ABC",
      status := "explicit field" } ]

/-- The endgame rows list has six entries. -/
theorem thetaSideEndgameRows_length : thetaSideEndgameRows.length = 6 := rfl

/-- The frozen registry pin recorded with the rows. -/
def thetaSideEndgamePin : Nat := 14041

/-- The recorded pin. -/
theorem thetaSideEndgamePin_eq : thetaSideEndgamePin = 14041 := rfl

#check EndgameRow
#check thetaSideEndgameRows
#check thetaSideEndgameRows_length
#check thetaSideEndgamePin_eq

end LeanFormal.IUT.XiFPaper.S3132ThetaSideEndgameRowsActual