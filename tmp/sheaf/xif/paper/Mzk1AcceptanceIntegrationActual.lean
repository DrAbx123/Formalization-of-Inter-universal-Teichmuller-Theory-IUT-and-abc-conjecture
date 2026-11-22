import tmp.sheaf.xif.paper.Mzk1LastNamedResolutionActual
import tmp.sheaf.xif.paper.Mzk1Cor312FinalAssemblyActual

/-! # Mzk1AcceptanceIntegrationActual — resolved acceptance bundle

A561 module (no new mathematics): integrates the RESOLVED acceptance (canonical reading,
last named input discharged by rfl) into a single accepted bundle: the final contract,
its Cor 3.12 conclusion, and the paper-reading slot match.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1AcceptanceIntegrationActual

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
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.S1929LiteralIQCarrierActual
open LeanFormal.IUT.XiFPaper.Mzk1QPilotSHEDoubleImageActual
open scoped BigOperators

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The accepted Cor 3.12 bundle at the canonical reading. -/
structure AcceptedCor312 (D : KummerXiERealization T)
    (hqneg : Real.log (D.vol {qPilotInThetaCarrier T}) < 0)
    (ipl : Prop) (hipl : ipl) (apt : Prop) (hapt : apt) where
  /-- The accepted StepXI contract. -/
  contract : StepXIContract
  /-- The Cor 3.12 conclusion for it. -/
  conclusion : Cor312Conclusion contract
  /-- The contract theta slot equals the paper theta reading. -/
  target_eq_reading :
    contract.thetaSigned = (canonicalReading T D).thetaReading

/-- Construct the accepted bundle from the genuine volumes + canonical reading. -/
noncomputable def acceptedBundle (D : KummerXiERealization T)
    (hqneg : Real.log (D.vol {qPilotInThetaCarrier T}) < 0)
    (ipl : Prop) (hipl : ipl) (apt : Prop) (hapt : apt) :
    AcceptedCor312 T D hqneg ipl hipl apt hapt where
  contract :=
    cor312Contract_final T (canonicalReading T D)
      (by rw [no_defeq_vacuity T (canonicalReading T D)]; exact hqneg)
      ipl hipl (SHEArrowStatement T) (sheArrowStatement_proved T) apt hapt
  conclusion :=
    canonical_cor312 T D hqneg ipl hipl apt hapt
  target_eq_reading :=
    target_matches_paper T (canonicalReading T D)

/-- Acceptance: the bundle's conclusion is the Cor 3.12 conclusion. -/
theorem accepted_cor312 (D : KummerXiERealization T)
    (hqneg : Real.log (D.vol {qPilotInThetaCarrier T}) < 0)
    (ipl : Prop) (hipl : ipl) (apt : Prop) (hapt : apt) :
    Cor312Conclusion (acceptedBundle T D hqneg ipl hipl apt hapt).contract :=
  (acceptedBundle T D hqneg ipl hipl apt hapt).conclusion

/-- Acceptance: the bundle target matches the paper theta reading. -/
theorem accepted_target (D : KummerXiERealization T)
    (hqneg : Real.log (D.vol {qPilotInThetaCarrier T}) < 0)
    (ipl : Prop) (hipl : ipl) (apt : Prop) (hapt : apt) :
    (acceptedBundle T D hqneg ipl hipl apt hapt).contract.thetaSigned =
      (canonicalReading T D).thetaReading :=
  (acceptedBundle T D hqneg ipl hipl apt hapt).target_eq_reading

#check AcceptedCor312
#check acceptedBundle
#check accepted_cor312
#check accepted_target

end LeanFormal.IUT.XiFPaper.Mzk1AcceptanceIntegrationActual
end
