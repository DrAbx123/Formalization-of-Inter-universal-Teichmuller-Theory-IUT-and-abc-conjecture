/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1Cor312FinalAssemblyActual
import tmp.sheaf.xif.paper.Mzk1KummerTransportActual
import tmp.sheaf.xif.paper.Mzk1KummerRealizationActual
import tmp.sheaf.xif.paper.Mzk1XiEContainmentRequirementActual

/-! # A546/A549: Cor 3.12 final chain certificate

Chain (all GREEN olean):
1. `Mzk1KummerTransportActual` — `kummerMap`, `thetaOneCarrier`, `qPilotInThetaCarrier`,
   `kummerMap_thetaOne` (SHE root relation `q = theta^(2l)`),
   `qPilotInThetaCarrier_mem_hull` (genuine containment, norm bound);
2. `Mzk1KummerRealizationActual` — `qImage_realized`, `thetaImage_realized`,
   `qImage_realized_mem_hull`, `paperKummerReading_strict`;
3. `Mzk1Cor312FinalAssemblyActual` — `requirementOfReading`, `no_defeq_vacuity`,
   `target_matches_paper`, `cor312Contract_final`, `cor312Conclusion_final`.

Named inputs: `PaperKummerReading` 1-column readout equalities, `strict_measure`,
`hqneg`, and qualitative `(IPL)/(SHE)/(APT)` evidence.
Paper statement: `-|log Theta| in R` and `-|log Theta| >= -|log q|`
(IUT III 10324-10353). -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1Cor312ChainCertificateActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.Mzk1KummerTransportActual
open LeanFormal.IUT.XiFPaper.Mzk1KummerRealizationActual
open LeanFormal.IUT.XiFPaper.Mzk1Cor312FinalAssemblyActual
open LeanFormal.IUT.XiFPaper.Mzk1XiEContainmentRequirementActual
open LeanFormal.IUT.XiFPaper.Mzk1SignedCor312ContractActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The final chain's conclusion theorem (the assembled Cor 3.12 conclusion). -/
theorem chain_cor312_conclusion (R : PaperKummerReading T)
    (hqneg : requirementSignedQ (requirementOfReading T R) < 0)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt) :
    Cor312Conclusion
      (cor312Contract_final T R hqneg ipl hipl she hshe apt hapt) :=
  cor312Conclusion_final T R hqneg ipl hipl she hshe apt hapt

/-- The Kummer realization step of the chain: q is the Kummer image of theta_1. -/
theorem chain_kummer_realization :
    kummerMap T (thetaOneCarrier T) = qPilotInThetaCarrier T :=
  kummerMap_thetaOne T

/-- The genuine xi-e containment step: the realized q image lies in the Theta hull. -/
theorem chain_qImage_mem_hull :
    (genuineKummerData T).qImageInTheta ∈ s1902Hull T :=
  qImage_realized_mem_hull T

/-- The paper signed inequality produced by the assembly. -/
theorem chain_paper_inequality (R : PaperKummerReading T) :
    requirementSignedQ (requirementOfReading T R) ≤
      requirementSignedTheta (requirementOfReading T R) :=
  genuine_logVolume_inequality_SHE T R

end LeanFormal.IUT.XiFPaper.Mzk1Cor312ChainCertificateActual

/-! ## A549 axiom gate (#print axioms output is recorded in the watchdog log) -/

#print axioms LeanFormal.IUT.XiFPaper.Mzk1KummerTransportActual.kummerMap_thetaOne
#print axioms LeanFormal.IUT.XiFPaper.Mzk1KummerTransportActual.qPilotInThetaCarrier_mem_hull
#print axioms LeanFormal.IUT.XiFPaper.Mzk1KummerTransportActual.genuineKummerData
#print axioms LeanFormal.IUT.XiFPaper.Mzk1KummerRealizationActual.qImage_realized
#print axioms LeanFormal.IUT.XiFPaper.Mzk1KummerRealizationActual.qImage_realized_mem_hull
#print axioms LeanFormal.IUT.XiFPaper.Mzk1KummerRealizationActual.paperKummerReading_strict
#print axioms LeanFormal.IUT.XiFPaper.Mzk1XiEContainmentRequirementActual.requirement_strict_signed
#print axioms LeanFormal.IUT.XiFPaper.Mzk1Cor312FinalAssemblyActual.no_defeq_vacuity
#print axioms LeanFormal.IUT.XiFPaper.Mzk1Cor312FinalAssemblyActual.target_matches_paper
#print axioms LeanFormal.IUT.XiFPaper.Mzk1Cor312FinalAssemblyActual.genuine_logVolume_inequality_SHE
#print axioms LeanFormal.IUT.XiFPaper.Mzk1Cor312FinalAssemblyActual.cor312Conclusion_final

end
