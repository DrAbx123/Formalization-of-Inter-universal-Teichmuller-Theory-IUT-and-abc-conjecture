/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1ABCEntryQpilotActual
import tmp.sheaf.xif.paper.Mzk1ABCEntryGap2QpilotActual
import tmp.sheaf.xif.paper.Mzk1AxiomGateActual
import Mathlib.Tactic
import tmp.sheaf.xif.paper.S1929LiteralIQCarrierActual
import tmp.sheaf.xif.paper.Mzk1Cor312FinalAssemblyActual
import tmp.sheaf.xif.paper.Mzk1KummerTransportActual
import tmp.sheaf.xif.paper.Mzk1XiEContainmentRequirementActual
import tmp.sheaf.xif.paper.Mzk1KummerRealizationActual

/-! # Mzk1ABCStage5AxiomGatePayloadActual — ABC/Stage5 axiom gate + evidence payload

A574 (qpilot lane, own name):
* `#print axioms` gate for the ABC bridge and the final Cor 3.12 assembly;
* `ABCStage5Evidence` payload structure: height bound, ABC conclusion, Gap-2
  region bound, and the final Cor 3.12 conclusion, all as proved fields.
 -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1ABCStage5AxiomGatePayloadActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1KummerRealizationActual
open LeanFormal.IUT.XiFPaper.Mzk1XiEContainmentRequirementActual
open LeanFormal.IUT.XiFPaper.Mzk1KummerTransportActual
open LeanFormal.IUT.XiFPaper.Mzk1Cor312FinalAssemblyActual
open LeanFormal.IUT.XiFPaper.S1929LiteralIQCarrierActual
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.Mzk1ABCEntryQpilotActual
open LeanFormal.IUT.XiFPaper.Mzk1ABCEntryGap2QpilotActual
open LeanFormal.IUT.XiFPaper.Mzk1AxiomGateActual

/-! ### Axiom gates (machine output) -/

#print axioms LeanFormal.IUT.XiFPaper.Mzk1ABCEntryQpilotActual.abcEntry_heightBound
#print axioms LeanFormal.IUT.XiFPaper.Mzk1ABCEntryQpilotActual.abcEntry_abcConjecture
#print axioms LeanFormal.IUT.XiFPaper.Mzk1ABCEntryGap2QpilotActual.gap2_regionVolume_bound
#print axioms LeanFormal.IUT.XiFPaper.Mzk1ABCEntryGap2QpilotActual.gap2_additive_contract
#print axioms LeanFormal.IUT.XiFPaper.Mzk1Cor312FinalAssemblyActual.cor312Conclusion_final

/-! ### Evidence payload -/

/-- The ABC/Stage5 evidence payload: the conditional bridge outputs plus the final
Cor 3.12 conclusion are all available as proved fields. -/
structure ABCStage5Evidence where
  /-- the Cor 3.12 -> ABC height bound (bridge interface as input). -/
  heightBound : Cor312ToABCBridgeInterface.{0} →
    ∀ epsilon : Real, 0 < epsilon → ∃ A : Real,
      ∀ a b c : Nat, IsABCTriple a b c →
        Height.logHeight₁ (abcRationalPoint a c) ≤
          (1 + epsilon) * arithmeticWeight (abcRationalPoint a c) + A
  /-- the conditional ABC conclusion from the bridge interface. -/
  abcConjecture : Cor312ToABCBridgeInterface.{0} → ABCConjecture
  /-- the Gap-2 region-volume bound for every comparison datum. -/
  gap2RegionBound : ∀ {X : Type} {W : IQHullLogVolumeInterface X}
    {epsilon : Real} (C : Cor312EpsilonArithmeticComparison W epsilon),
    ∃ D : Real, ∀ a b c : Nat, IsABCTriple a b c →
      (W.logVolume (C.comparisonRegion a b c)).toReal ≤
        (1 + epsilon) * arithmeticWeight (abcRationalPoint a c) +
          (W.logVolume W.hull).toReal + D
  /-- the final Cor 3.12 conclusion payload. -/
  cor312Payload : ∀ {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))]
    (R : PaperKummerReading T)
    (hqneg : requirementSignedQ (requirementOfReading T R) < 0)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt),
    Cor312Conclusion (cor312Contract_final T R hqneg ipl hipl she hshe apt hapt)

/-- The constructed evidence payload (all fields proved). -/
noncomputable def abcStage5Evidence : ABCStage5Evidence where
  heightBound := fun D => abcEntry_heightBound D
  abcConjecture := fun D => abcEntry_abcConjecture D
  gap2RegionBound := fun {X} {W} {epsilon} C => gap2_regionVolume_bound C
  cor312Payload := by
    intro l T inst R hqneg ipl hipl she hshe apt hapt
    exact cor312Conclusion_final T R hqneg ipl hipl she hshe apt hapt

#check abcStage5Evidence

end LeanFormal.IUT.XiFPaper.Mzk1ABCStage5AxiomGatePayloadActual
end
