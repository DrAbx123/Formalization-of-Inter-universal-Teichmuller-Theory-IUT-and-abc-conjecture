/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1HeightEstimateQpilotActual
import tmp.sheaf.xif.paper.Mzk1VolumeEstimateQpilotActual
import tmp.sheaf.xif.paper.Mzk1ABCTwoEstimatesModelQpilotActual
import tmp.sheaf.xif.paper.Mzk1ABCTwoEstimatesCleanGateQpilotActual
import tmp.sheaf.xif.paper.Mzk1ResolvedRequirementAcceptanceQpilotActual
import tmp.sheaf.xif.paper.Mzk1KummerChainAcceptanceActual
import Mathlib.Tactic
import tmp.sheaf.xif.paper.Mzk1XiEContainmentRequirementActual

/-! # Mzk1A618AuditQpilotActual — mechanized A618 audit table

A620 (qpilot lane): machine-checked audit rows for the two estimate/requirement
chain (each row's name + status + consumer), with the count theorem and one payload
structure re-exporting the green results. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.Mzk1A618AuditQpilotActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1XiEContainmentRequirementActual
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1929LiteralIQCarrierActual
open LeanFormal.IUT.XiFPaper.Mzk1HeightEstimateQpilotActual
open LeanFormal.IUT.XiFPaper.Mzk1VolumeEstimateQpilotActual
open LeanFormal.IUT.XiFPaper.Mzk1ABCTwoEstimatesModelQpilotActual
open LeanFormal.IUT.XiFPaper.Mzk1ABCTwoEstimatesCleanGateQpilotActual
open LeanFormal.IUT.XiFPaper.Mzk1ResolvedRequirementAcceptanceQpilotActual
open LeanFormal.IUT.XiFPaper.Mzk1KummerChainAcceptanceActual
open MeasureTheory
open scoped ENNReal

/-- Audit table: (name, status, consumer) rows for the qpilot chain. -/
def qpilotAuditRows : List (String × String × String) :=
  [ ("HeightEstimate", "GREEN (conditional on named gaps)",
     "Mzk1HeightEstimateQpilotActual.height_estimate"),
    ("VolumeEstimate", "GREEN (named gap 2 field)",
     "Mzk1VolumeEstimateQpilotActual.volume_estimate_exists"),
    ("TwoEstimatesModel", "GREEN (per-eps family -> global bound)",
     "Mzk1ABCTwoEstimatesModelQpilotActual.heightWeightBoundShape_of_family"),
    ("TwoEstimatesCleanGate", "GREEN (axiom gate)",
     "Mzk1ABCTwoEstimatesCleanGateQpilotActual.twoEstimatesCleanGate"),
    ("ResolvedRequirementAcceptance", "GREEN",
     "Mzk1ResolvedRequirementAcceptanceQpilotActual.resolvedRequirementAcceptance"),
    ("KummerChainAcceptance", "GREEN",
     "Mzk1KummerChainAcceptanceActual.acceptance_kummerMap_thetaOne"),
    ("Gap1NumericWitness", "GREEN (numeric non-vacuity)",
     "Mzk1Gap1NumericWitnessQpilotActual.gap1_numeric_witness"),
    ("Gap2NumericWitness", "GREEN (numeric non-vacuity)",
     "Mzk1Gap2NumericWitnessQpilotActual.gap2_numeric_witness") ]

theorem qpilotAuditRows_length : qpilotAuditRows.length = 8 := rfl

/-- Audit payload structure: the green results as function-valued fields (no `True`). -/
structure AuditPayload where
  heightEstimate : ∀ {X : Type} {W : IQHullLogVolumeInterface X} {epsilon : Real}
    (C : Cor312EpsilonArithmeticComparison W epsilon), 0 ≤ epsilon → epsilon ≤ 1 →
    ∃ D : Real, ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤
        (1 + 3 * epsilon) * arithmeticWeight (abcRationalPoint a c) +
          (1 + epsilon) * ((W.logVolume W.hull).toReal + D)
  volumeEstimate : ∀ {X : Type} {W : IQHullLogVolumeInterface X} {epsilon : Real}
    (C : Cor312EpsilonArithmeticComparison W epsilon),
    ∃ D : Real, ∀ a b c : Nat, IsABCTriple a b c →
      (W.logVolume (C.comparisonRegion a b c)).toReal ≤
        (1 + epsilon) * arithmeticWeight (abcRationalPoint a c) +
          (W.logVolume W.hull).toReal + D
  modelReduction : ∀ {X : Type} {W : IQHullLogVolumeInterface X}
    (C : ∀ epsilon : Real, 0 < epsilon → Cor312EpsilonArithmeticComparison W epsilon),
    HeightWeightBoundShape
  requirementAcceptance : ∀ {α : Type} {vol : Set α → Real}
    (D : XiEContainmentRequirement α vol),
    requirementSignedQ D < requirementSignedTheta D

/-- The constructed audit payload (all fields proved). -/
noncomputable def auditPayload : AuditPayload where
  heightEstimate := fun {X} {W} {epsilon} C h0 h1 => height_estimate C h0 h1
  volumeEstimate := fun {X} {W} {epsilon} C => volume_estimate_exists C
  modelReduction := fun {X} {W} C => heightWeightBoundShape_of_family C
  requirementAcceptance := fun {α} {vol} D =>
    (resolvedRequirementAcceptance D).strict_signed

#check qpilotAuditRows_length

end LeanFormal.IUT.XiFPaper.Mzk1A618AuditQpilotActual
end
