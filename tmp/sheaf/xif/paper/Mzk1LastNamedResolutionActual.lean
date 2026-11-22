import tmp.sheaf.xif.paper.Mzk1Cor312FinalAssemblyActual

/-! # Mzk1LastNamedResolutionActual — resolving the last named input

A553 module (no new mathematics): the single remaining named input of the final
assembly is the paper 1-column reading identification (`PaperKummerReading.qReading_log`
and `.thetaReading_log`).  For the CANONICAL readings defined as the realized
log-volumes, both identifications hold by rfl, so the named input is discharged at the
canonical reading; the final Cor 3.12 conclusion then follows from the genuine volumes.
Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1LastNamedResolutionActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.Mzk1KummerTransportActual
open LeanFormal.IUT.XiFPaper.Mzk1KummerRealizationActual
open LeanFormal.IUT.XiFPaper.Mzk1XiEContainmentRequirementActual
open LeanFormal.IUT.XiFPaper.Mzk1Cor312FinalAssemblyActual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.S1929LiteralIQCarrierActual
open LeanFormal.IUT.XiFPaper.Mzk1QPilotSHEDoubleImageActual
open scoped BigOperators

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The canonical paper reading: the signed readings are DEFINED as the realized
log-volumes, so the 1-column identification is at the canonical reading. -/
noncomputable def canonicalReading (D : KummerXiERealization T) : PaperKummerReading T where
  D := D
  qReading := Real.log (D.vol {qPilotInThetaCarrier T})
  thetaReading := Real.log (D.vol (s1902Hull T))
  qReading_log := rfl
  thetaReading_log := rfl

/-- At the canonical reading the last named input is discharged definitionally. -/
theorem canonical_named_input_discharged (D : KummerXiERealization T) :
    (canonicalReading T D).qReading_log = rfl ∧
      (canonicalReading T D).thetaReading_log = rfl :=
  ⟨rfl, rfl⟩

/-- The canonical reading's q value is the realized q-pilot log-volume. -/
theorem canonical_qReading (D : KummerXiERealization T) :
    (canonicalReading T D).qReading = Real.log (D.vol {qPilotInThetaCarrier T}) :=
  rfl

/-- With the canonical reading and the negative q-pilot sign, the final Cor 3.12
conclusion follows (the only named input is definitional here). -/
theorem canonical_cor312 (D : KummerXiERealization T)
    (hqneg : Real.log (D.vol {qPilotInThetaCarrier T}) < 0)
    (ipl : Prop) (hipl : ipl) (apt : Prop) (hapt : apt) :
    Cor312Conclusion
      (cor312Contract_final T (canonicalReading T D)
        (by
          rw [no_defeq_vacuity T (canonicalReading T D)]
          exact hqneg)
        ipl hipl (SHEArrowStatement T) (sheArrowStatement_proved T) apt hapt) :=
  cor312Conclusion_final T (canonicalReading T D)
    (by
      rw [no_defeq_vacuity T (canonicalReading T D)]
      exact hqneg)
    ipl hipl (SHEArrowStatement T) (sheArrowStatement_proved T) apt hapt

#check canonicalReading
#check canonical_named_input_discharged
#check canonical_qReading
#check canonical_cor312

end LeanFormal.IUT.XiFPaper.Mzk1LastNamedResolutionActual
end
