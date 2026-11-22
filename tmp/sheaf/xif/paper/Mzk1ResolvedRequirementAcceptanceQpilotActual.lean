/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1XiEContainmentRequirementActual
import tmp.sheaf.xif.paper.Mzk1Cor312FinalAssemblyActual
import tmp.sheaf.xif.paper.Mzk1PositiveMeasureSignedConsumerActual
import Mathlib.Tactic

/-! # Mzk1ResolvedRequirementAcceptanceQpilotActual — resolved requirement acceptance

A588 (qpilot lane): acceptance object for a resolved `XiEContainmentRequirement`:
the signed readouts, strict signed inequality, strict measure field, and the
Cor 3.12 contract are all available as proved fields; a concrete instance is
built from a paper Kummer reading via the final assembly. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.Mzk1ResolvedRequirementAcceptanceQpilotActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1929LiteralIQCarrierActual
open LeanFormal.IUT.XiFPaper.Mzk1XiEContainmentRequirementActual
open LeanFormal.IUT.XiFPaper.Mzk1Cor312FinalAssemblyActual
open LeanFormal.IUT.XiFPaper.Mzk1KummerTransportActual
open LeanFormal.IUT.XiFPaper.Mzk1KummerRealizationActual

variable {α : Type*} {vol : Set α → Real}

/-- The resolved requirement acceptance object (every field proved). -/
structure ResolvedRequirementAcceptance (D : XiEContainmentRequirement α vol) where
  q_pos : 0 < vol D.qRegion
  strict_measure : vol D.qRegion < vol D.hullRegion
  strict_signed : requirementSignedQ D < requirementSignedTheta D
  signed_inequality : requirementSignedQ D ≤ requirementSignedTheta D
  contract_cor312 : ∀ (hqneg : requirementSignedQ D < 0)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt),
    Cor312Conclusion (requirementContract D hqneg ipl hipl she hshe apt hapt)

/-- The resolved requirement acceptance, constructed for every requirement. -/
noncomputable def resolvedRequirementAcceptance
    (D : XiEContainmentRequirement α vol) : ResolvedRequirementAcceptance D where
  q_pos := D.q_pos
  strict_measure := D.strict_measure
  strict_signed := requirement_strict_signed D
  signed_inequality := requirement_signed_inequality D
  contract_cor312 := by
    intro hqneg ipl hipl she hshe apt hapt
    exact requirement_cor312 D hqneg ipl hipl she hshe apt hapt

/-- Concrete resolved acceptance from a paper Kummer reading (final assembly). -/
theorem resolvedRequirement_of_reading
    {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))]
    (R : PaperKummerReading T)
    (hqneg : requirementSignedQ (requirementOfReading T R) < 0)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt) :
    Cor312Conclusion
      (cor312Contract_final T R hqneg ipl hipl she hshe apt hapt) :=
  cor312Conclusion_final T R hqneg ipl hipl she hshe apt hapt

#check resolvedRequirementAcceptance
#check resolvedRequirement_of_reading

end LeanFormal.IUT.XiFPaper.Mzk1ResolvedRequirementAcceptanceQpilotActual
end
