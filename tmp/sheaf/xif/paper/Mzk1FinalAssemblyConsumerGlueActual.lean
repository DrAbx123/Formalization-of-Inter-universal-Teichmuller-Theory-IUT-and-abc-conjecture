import tmp.sheaf.xif.paper.Mzk1Cor312FinalAssemblyActual
import tmp.sheaf.xif.paper.Mzk1Cor312FinalCThetaActual

/-! # Mzk1FinalAssemblyConsumerGlueActual — consumer forms of the final 3.12 assembly

A535 consumer module (no new mathematics): aligns with the mainline final assembly
(Mzk1Cor312FinalAssemblyActual: requirementOfReading / no_defeq_vacuity /
target_matches_paper / genuine_logVolume_inequality_SHE / cor312Contract_final /
cor312Conclusion_final) and exposes the contract slots plus the C_Theta >= -1
conclusion from the paper reading data.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1FinalAssemblyConsumerGlueActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1KummerTransportActual
open LeanFormal.IUT.XiFPaper.Mzk1KummerRealizationActual
open LeanFormal.IUT.XiFPaper.Mzk1XiEContainmentRequirementActual
open LeanFormal.IUT.XiFPaper.Mzk1Cor312FinalAssemblyActual
open LeanFormal.IUT.XiFPaper.Mzk1Cor312FinalCThetaActual
open LeanFormal.IUT.XiFPaper.Mzk1SignedCor312ContractActual
open LeanFormal.IUT.XiFPaper.Mzk1QPilotSHEDoubleImageActual
open scoped BigOperators

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The paper q-reading is the signed q-pilot value of the final requirement. -/
theorem signedQ_eq_reading (R : PaperKummerReading T) :
    requirementSignedQ (requirementOfReading T R) = R.qReading :=
  no_defeq_vacuity T R

/-- The paper theta-reading is the signed Theta-pilot value. -/
theorem signedTheta_eq_reading (R : PaperKummerReading T) :
    requirementSignedTheta (requirementOfReading T R) = R.thetaReading :=
  target_matches_paper T R

/-- Sign transport: the requirement's q slot is negative iff the paper reading is. -/
theorem signedQ_neg_iff (R : PaperKummerReading T) :
    requirementSignedQ (requirementOfReading T R) < 0 ↔ R.qReading < 0 := by
  rw [signedQ_eq_reading T R]

/-- The final contract's q slot is the paper q-reading (hence negative). -/
theorem finalContract_q_negative (R : PaperKummerReading T) (hqneg : R.qReading < 0)
    (ipl : Prop) (hipl : ipl) (apt : Prop) (hapt : apt) :
    (cor312Contract_final T R
      (by rw [signedQ_eq_reading T R]; exact hqneg)
      ipl hipl (SHEArrowStatement T) (sheArrowStatement_proved T) apt hapt).qSigned < 0 := by
  unfold cor312Contract_final requirementContract signedCor312Contract
  rw [signedQ_eq_reading T R]
  exact hqneg

/-- The final contract's q <= target comparison. -/
theorem finalContract_q_le_target (R : PaperKummerReading T) (hqneg : R.qReading < 0)
    (ipl : Prop) (hipl : ipl) (apt : Prop) (hapt : apt) :
    (cor312Contract_final T R
      (by rw [signedQ_eq_reading T R]; exact hqneg)
      ipl hipl (SHEArrowStatement T) (sheArrowStatement_proved T) apt hapt).qSigned <=
    (cor312Contract_final T R
      (by rw [signedQ_eq_reading T R]; exact hqneg)
      ipl hipl (SHEArrowStatement T) (sheArrowStatement_proved T) apt hapt).targetSigned :=
  (cor312Contract_final T R _ ipl hipl _ _ apt hapt).q_le_target

/-- The final contract's target <= theta comparison (genuine xi-e inequality). -/
theorem finalContract_target_le_theta (R : PaperKummerReading T) (hqneg : R.qReading < 0)
    (ipl : Prop) (hipl : ipl) (apt : Prop) (hapt : apt) :
    (cor312Contract_final T R
      (by rw [signedQ_eq_reading T R]; exact hqneg)
      ipl hipl (SHEArrowStatement T) (sheArrowStatement_proved T) apt hapt).targetSigned <=
    (cor312Contract_final T R
      (by rw [signedQ_eq_reading T R]; exact hqneg)
      ipl hipl (SHEArrowStatement T) (sheArrowStatement_proved T) apt hapt).thetaSigned :=
  (cor312Contract_final T R _ ipl hipl _ _ apt hapt).target_le_theta

/-- The final Cor 3.12 conclusion with the proved SHE evidence. -/
theorem final_cor312_she (R : PaperKummerReading T) (hqneg : R.qReading < 0)
    (ipl : Prop) (hipl : ipl) (apt : Prop) (hapt : apt) :
    Cor312Conclusion
      (cor312Contract_final T R
        (by rw [signedQ_eq_reading T R]; exact hqneg)
        ipl hipl (SHEArrowStatement T) (sheArrowStatement_proved T) apt hapt) :=
  cor312Conclusion_final T R
    (by rw [signedQ_eq_reading T R]; exact hqneg)
    ipl hipl (SHEArrowStatement T) (sheArrowStatement_proved T) apt hapt

/-- The constant conclusion C_Theta >= -1 from the paper reading data. -/
theorem final_cTheta_ge_neg_one (R : PaperKummerReading T) (hqneg : R.qReading < 0) :
    -1 <= R.thetaReading / (-R.qReading) :=
  Mzk1Cor312FinalCThetaActual.final_cTheta_ge_neg_one T R hqneg

#check signedQ_eq_reading
#check signedTheta_eq_reading
#check finalContract_q_negative
#check finalContract_q_le_target
#check finalContract_target_le_theta
#check final_cor312_she
#check final_cTheta_ge_neg_one

end LeanFormal.IUT.XiFPaper.Mzk1FinalAssemblyConsumerGlueActual
end
