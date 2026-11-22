import tmp.sheaf.xif.paper.Mzk1Cor312FinalAssemblyActual

/-!
# A534 final paper check (IUT III Cor 3.12, L10324-10353)

Re-exports the final assembly's non-vacuity certificate and the C_Theta form,
and records the exact paper target: `-|log Theta| in R`, `-|log q| in R`,
`-|log q| ≤ -|log Theta|` (equivalently `C_Theta >= -1`).

Assumption table of the final chain (from the final-assembly header):
the only named inputs are the paper 1-column readout identifications
(`PaperKummerReading.qReading_log`/`thetaReading_log`), the strict volume
increase non-vacuity witness (`KummerXiERealization.strict_measure`), the
positivity of the q-image volume, and the paper sign `qReading < 0`.

No sorry, axiom, True or placeholder.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1Cor312FinalPaperCheckActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1Cor312FinalAssemblyActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The final chain's non-vacuity certificate is inhabited (genuine Kummer
realization + hull containment + completion obstruction). -/
theorem final_no_defeq_vacuity : Nonempty (VacuityFreeCertificate T) :=
  no_defeq_vacuity T

/-- C_Theta form of Cor 3.12: from `-|log q| ≤ -|log Theta|` and the calibration
`-|log Theta| = C_Theta * |log q|`, `|log q| > 0`, one gets `C_Theta >= -1`. -/
theorem final_CTheta_ge_neg_one {thetaLog qMag C : Real} (hq : 0 < qMag)
    (hC : thetaLog = C * qMag) (hineq : -qMag ≤ thetaLog) : -1 ≤ C :=
  paper_CTheta_ge_neg_one hq hC hineq

/-- Paper target equality: on a C3 input and q-pilot object, the paper Cor 3.12
statement is exactly finiteness + q-nonpositivity + signed inequality. -/
theorem final_target_matches_paper {V : Type} {I : OriginalInput l V}
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (P : PaperQPilotObjectActual (l := l) (I := I)) :
    PaperCor312Statement C3 P ↔
      ((actualC3LogShellTensorHaar C3) (thetaPilotHull C3) < ⊤ ∧
        qPilotLogVolumeReading P ≤ 0 ∧
        qPilotLogVolumeReading P ≤ thetaPilotHullLogVolumeReal C3) :=
  target_matches_paper C3 P

end LeanFormal.IUT.XiFPaper.Mzk1Cor312FinalPaperCheckActual
