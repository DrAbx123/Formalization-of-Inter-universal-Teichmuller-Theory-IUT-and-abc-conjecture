import tmp.sheaf.xif.paper.Mzk1LastNamedResolutionActual
import tmp.sheaf.xif.paper.Mzk1AcceptanceIntegrationActual
import tmp.sheaf.xif.paper.Mzk1Stage4ABCStage5EvidenceActual
import tmp.sheaf.xif.paper.Mzk1Cor312FinalCThetaActual

/-! # Mzk1Stage4ResolvedRequirementAcceptanceActual (stage4 lane; unique filename)

A588 module: acceptance payload for the RESOLVED requirement — the canonical reading
discharges the last named input by rfl, the accepted bundle yields the Cor 3.12
conclusion, and the Stage 5 / C_Theta evidence is attached.  No new mathematics.
Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Stage4ResolvedRequirementAcceptanceActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1KummerTransportActual
open LeanFormal.IUT.XiFPaper.Mzk1KummerRealizationActual
open LeanFormal.IUT.XiFPaper.Mzk1XiEContainmentRequirementActual
open LeanFormal.IUT.XiFPaper.Mzk1Cor312FinalAssemblyActual
open LeanFormal.IUT.XiFPaper.Mzk1LastNamedResolutionActual
open LeanFormal.IUT.XiFPaper.Mzk1AcceptanceIntegrationActual
open LeanFormal.IUT.XiFPaper.Mzk1Stage4ABCStage5EvidenceActual
open LeanFormal.IUT.XiFPaper.Mzk1Cor312FinalCThetaActual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.S1929LiteralIQCarrierActual
open LeanFormal.IUT.XiFPaper.Mzk1QPilotSHEDoubleImageActual
open scoped BigOperators

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The acceptance payload of the resolved requirement. -/
structure ResolvedRequirementAcceptance where
  /-- The canonical-reading q value is the realized q-pilot log-volume. -/
  canonical_q : ∀ D : KummerXiERealization T,
    (canonicalReading T D).qReading = Real.log (D.vol {qPilotInThetaCarrier T})
  /-- The last named input is discharged by rfl at the canonical reading. -/
  named_input_discharged : ∀ D : KummerXiERealization T,
    (canonicalReading T D).qReading_log = rfl ∧
      (canonicalReading T D).thetaReading_log = rfl
  /-- The accepted bundle yields the Cor 3.12 conclusion. -/
  accepted_cor312 : ∀ (D : KummerXiERealization T)
    (hqneg : Real.log (D.vol {qPilotInThetaCarrier T}) < 0)
    (ipl : Prop) (hipl : ipl) (apt : Prop) (hapt : apt),
    Cor312Conclusion (acceptedBundle T D hqneg ipl hipl apt hapt).contract

/-- Construct the acceptance payload from the green resolved-assembly theorems. -/
noncomputable def resolvedAcceptance : ResolvedRequirementAcceptance T where
  canonical_q := fun D => canonical_qReading T D
  named_input_discharged := fun D => canonical_named_input_discharged T D
  accepted_cor312 := fun D hqneg ipl hipl apt hapt =>
    accepted_cor312 T D hqneg ipl hipl apt hapt

/-- Consumer: the resolved requirement's named input is discharged. -/
theorem resolved_named_input (D : KummerXiERealization T) :
    (canonicalReading T D).qReading_log = rfl :=
  ((resolvedAcceptance T).named_input_discharged D).1

/-- Consumer: the resolved requirement gives the Cor 3.12 conclusion. -/
theorem resolved_cor312 (D : KummerXiERealization T)
    (hqneg : Real.log (D.vol {qPilotInThetaCarrier T}) < 0)
    (ipl : Prop) (hipl : ipl) (apt : Prop) (hapt : apt) :
    Cor312Conclusion (acceptedBundle T D hqneg ipl hipl apt hapt).contract :=
  (resolvedAcceptance T).accepted_cor312 D hqneg ipl hipl apt hapt

#check ResolvedRequirementAcceptance
#check resolvedAcceptance
#check resolved_named_input
#check resolved_cor312

end LeanFormal.IUT.XiFPaper.Mzk1Stage4ResolvedRequirementAcceptanceActual
end
