import tmp.sheaf.xif.paper.Mzk1LastNamedResolutionActual
import tmp.sheaf.xif.paper.Mzk1Cor312FinalAssemblyActual

/-! # Mzk1AcceptanceResolvedActual — acceptance on the RESOLVED (canonical-reading) assembly

A559 module (no new mathematics): the accepted form of the Cor 3.12 conclusion after the
last named input (paper 1-column reading identification) has been resolved at the
canonical reading (`Mzk1LastNamedResolutionActual`).  Assumption table:
* `hqneg : log (vol {q-pilot image}) < 0`  — the paper's |log q| > 0 for the realized
  q-pilot volume (an inequality, not a named identification);
* IPL/SHE/APT data; SHE is the proved `sheArrowStatement_proved`.
Everything else (q/Theta readings, comparison) is proved.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1AcceptanceResolvedActual

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

/-- Acceptance 1: the canonical-reading q value is the realized q-pilot log-volume. -/
theorem acceptance_qReading (D : KummerXiERealization T) :
    (canonicalReading T D).qReading = Real.log (D.vol {qPilotInThetaCarrier T}) :=
  canonical_qReading T D

/-- Acceptance 2: the last named input is discharged by rfl at the canonical reading. -/
theorem acceptance_named_input_resolved (D : KummerXiERealization T) :
    (canonicalReading T D).qReading_log = rfl ∧
      (canonicalReading T D).thetaReading_log = rfl :=
  canonical_named_input_discharged T D

/-- Acceptance 3: the resolved assembly gives the Cor 3.12 conclusion,
under only the paper q-pilot negativity (and SHE from the proved arrow). -/
theorem acceptance_cor312 (D : KummerXiERealization T)
    (hqneg : Real.log (D.vol {qPilotInThetaCarrier T}) < 0)
    (ipl : Prop) (hipl : ipl) (apt : Prop) (hapt : apt) :
    Cor312Conclusion
      (cor312Contract_final T (canonicalReading T D)
        (by
          rw [no_defeq_vacuity T (canonicalReading T D)]
          exact hqneg)
        ipl hipl (SHEArrowStatement T) (sheArrowStatement_proved T) apt hapt) :=
  canonical_cor312 T D hqneg ipl hipl apt hapt

/-- Acceptance 4: the Theta slot matches the paper reading. -/
theorem acceptance_thetaReading (D : KummerXiERealization T) :
    requirementSignedTheta (requirementOfReading T (canonicalReading T D)) =
      (canonicalReading T D).thetaReading :=
  target_matches_paper T (canonicalReading T D)

#check acceptance_qReading
#check acceptance_named_input_resolved
#check acceptance_cor312
#check acceptance_thetaReading

end LeanFormal.IUT.XiFPaper.Mzk1AcceptanceResolvedActual
end
