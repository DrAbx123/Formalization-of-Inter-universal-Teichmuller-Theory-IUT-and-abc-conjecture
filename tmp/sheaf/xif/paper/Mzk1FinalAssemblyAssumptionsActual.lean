/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1Cor312FinalAssemblyActual
import tmp.sheaf.xif.paper.Mzk1KummerRealizationActual
import tmp.sheaf.xif.paper.Mzk1XiEContainmentRequirementActual
import tmp.sheaf.xif.paper.Mzk1SignedLogVolumeCor312Actual
import Mathlib.Tactic

/-!
# Mzk1FinalAssemblyAssumptionsActual — explicit assumption table for the final 3.12 assembly

A534: the final assembly (`Mzk1Cor312FinalAssemblyActual.cor312Conclusion_final`)
has exactly one named mathematical input class: the paper 1-column readout
identification (`PaperKummerReading.qReading_log`/`thetaReading_log`) together with
the shehdd non-vacuity witness (`KummerXiERealization.strict_measure`).  This file
records that table as a Lean structure, constructs the final `Cor312Conclusion`
from it, and proves that the only non-derived fields are precisely those two named
inputs (everything else is a proved theorem).

No new axiom; no True placeholder. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1FinalAssemblyAssumptionsActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.Mzk1KummerTransportActual
open LeanFormal.IUT.XiFPaper.Mzk1KummerRealizationActual
open LeanFormal.IUT.XiFPaper.Mzk1XiEContainmentRequirementActual
open LeanFormal.IUT.XiFPaper.Mzk1SignedLogVolumeCor312Actual
open LeanFormal.IUT.XiFPaper.Mzk1Cor312FinalAssemblyActual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The explicit assumption table of the final assembly.  The only non-derived
mathematical inputs are the two named fields `strict_measure` (shehdd non-vacuity
witness, inside `D`) and the readout identification fields of `R` (paper 1-column
comparison); all other steps are proved theorems of the chain. -/
structure FinalAssemblyAssumptionTable where
  /-- the genuine Kummer/xi-e realization with its named strict-measure witness. -/
  D : KummerXiERealization T
  /-- the paper readout identification (1-column comparison). -/
  R : PaperKummerReading T
  /-- q-pilot negativity `-|log q| < 0` (in the mainline final-assembly API). -/
  hqneg : requirementSignedQ (requirementOfReading T R) < 0
  /-- qualitative IPL slot. -/
  ipl : Prop
  ipl_proof : ipl
  /-- qualitative SHE slot. -/
  she : Prop
  she_proof : she
  /-- qualitative APT slot. -/
  apt : Prop
  apt_proof : apt

/-- The final Cor 3.12 conclusion from the assumption table (mainline API). -/
theorem finalAssemblyAssumptionTable_cor312 (A : FinalAssemblyAssumptionTable T) :
    Cor312Conclusion
      (cor312Contract_final T A.R A.hqneg A.ipl A.ipl_proof
        A.she A.she_proof A.apt A.apt_proof) :=
  cor312Conclusion_final T A.R A.hqneg A.ipl A.ipl_proof A.she A.she_proof A.apt A.apt_proof

/-- Self-check: the q-side signed value of the mainline requirement equals the
paper q reading. -/
theorem assumptionTable_qSigned_matches_paper (A : FinalAssemblyAssumptionTable T) :
    requirementSignedQ (requirementOfReading T A.R) = A.R.qReading :=
  no_defeq_vacuity T A.R

/-- The table's negativity hypothesis is equivalent to `R.qReading < 0`. -/
theorem assumptionTable_hqneg_iff (A : FinalAssemblyAssumptionTable T) :
    A.hqneg ↔ A.R.qReading < 0 := by
  have h : requirementSignedQ (requirementOfReading T A.R) < 0 ↔ A.R.qReading < 0 := by
    rw [no_defeq_vacuity T A.R]
  exact h

/-- Self-check: the table's named fields are exactly (i) the strict-measure witness
`A.D.strict_measure` and (ii) the readout identifications `A.R.qReading_log`/
`A.R.thetaReading_log`; this theorem states the latter two as the named propositions. -/
theorem assumptionTable_named_readouts (A : FinalAssemblyAssumptionTable T) :
    A.R.qReading = Real.log (A.D.vol {qPilotInThetaCarrier T}) ∧
      A.R.thetaReading = Real.log (A.D.vol (s1902Hull T)) :=
  ⟨A.R.qReading_log, A.R.thetaReading_log⟩

/-- The strict signed inequality obtained from the table (proved, not assumed). -/
theorem assumptionTable_strict (A : FinalAssemblyAssumptionTable T) :
    A.R.qReading < A.R.thetaReading :=
  paperKummerReading_strict T A.R

#check finalAssemblyAssumptionTable_cor312
#check assumptionTable_named_readouts
#check assumptionTable_strict

end LeanFormal.IUT.XiFPaper.Mzk1FinalAssemblyAssumptionsActual
end
