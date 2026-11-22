import tmp.sheaf.xif.paper.Mzk1AcceptanceIntegrationActual
import tmp.sheaf.xif.paper.Mzk1Stage4HqnegCleanGateActual
import tmp.sheaf.xif.paper.Mzk1Cor312FinalCThetaActual

/-! # Mzk1Stage4A618AuditProofActual (stage4 lane; A618 proof-carrying audit)

A625 module: the A618 audit as PROOFS (compile-time gates), separate from the log-only
`#print axioms` summary: each final-chain gate is re-derived here so the audit is
proof-carrying, and the axiom sets are printed for record.  No new mathematics.
Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Stage4A618AuditProofActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1KummerTransportActual
open LeanFormal.IUT.XiFPaper.Mzk1KummerRealizationActual
open LeanFormal.IUT.XiFPaper.Mzk1XiEContainmentRequirementActual
open LeanFormal.IUT.XiFPaper.Mzk1Cor312FinalAssemblyActual
open LeanFormal.IUT.XiFPaper.Mzk1AcceptanceIntegrationActual
open LeanFormal.IUT.XiFPaper.Mzk1Stage4HqnegCleanGateActual
open LeanFormal.IUT.XiFPaper.Mzk1Cor312FinalCThetaActual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.S1929LiteralIQCarrierActual
open LeanFormal.IUT.XiFPaper.Mzk1QPilotSHEDoubleImageActual
open scoped BigOperators

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Audit proof 1: target slot matches the paper Theta reading. -/
theorem audit_target_matches (R : PaperKummerReading T) :
    requirementSignedTheta (requirementOfReading T R) = R.thetaReading :=
  target_matches_paper T R

/-- Audit proof 2: no definitional vacuity in the q slot. -/
theorem audit_no_defeq_vacuity (R : PaperKummerReading T) :
    requirementSignedQ (requirementOfReading T R) = R.qReading :=
  no_defeq_vacuity T R

/-- Audit proof 3: the accepted bundle yields the Cor 3.12 conclusion. -/
theorem audit_accepted (D : KummerXiERealization T)
    (hqneg : Real.log (D.vol {qPilotInThetaCarrier T}) < 0)
    (ipl : Prop) (hipl : ipl) (apt : Prop) (hapt : apt) :
    Cor312Conclusion (acceptedBundle T D hqneg ipl hipl apt hapt).contract :=
  accepted_cor312 T D hqneg ipl hipl apt hapt

/-- Audit proof 4: the clean hqneg gate conclusion. -/
theorem audit_clean_gate (D : KummerXiERealization T)
    (hqneg : HqnegHypothesis T D)
    (ipl : Prop) (hipl : ipl) (apt : Prop) (hapt : apt) :
    Cor312Conclusion (acceptedBundle T D hqneg ipl hipl apt hapt).contract :=
  clean_gate_cor312 T D hqneg ipl hipl apt hapt

#print axioms audit_target_matches
#print axioms audit_no_defeq_vacuity
#print axioms audit_accepted
#print axioms audit_clean_gate

#check audit_target_matches
#check audit_no_defeq_vacuity
#check audit_accepted
#check audit_clean_gate

end LeanFormal.IUT.XiFPaper.Mzk1Stage4A618AuditProofActual
end
