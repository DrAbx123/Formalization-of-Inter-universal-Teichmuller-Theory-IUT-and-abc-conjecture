/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1HeightEstimateQpilotActual
import tmp.sheaf.xif.paper.Mzk1VolumeEstimateQpilotActual
import tmp.sheaf.xif.paper.Mzk1ABCTwoEstimatesModelQpilotActual
import tmp.sheaf.xif.paper.Mzk1ResolvedRequirementAcceptanceQpilotActual
import Mathlib.Tactic

/-! # Mzk1A618ProofQpilotActual — A618 audit proofs in a separate file

A625 (qpilot lane): the A618 audit components as standalone proof declarations
(separate from the audit table file), with their axiom gates. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.Mzk1A618ProofQpilotActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1HeightEstimateQpilotActual
open LeanFormal.IUT.XiFPaper.Mzk1VolumeEstimateQpilotActual
open LeanFormal.IUT.XiFPaper.Mzk1ABCTwoEstimatesModelQpilotActual
open LeanFormal.IUT.XiFPaper.Mzk1ResolvedRequirementAcceptanceQpilotActual
open LeanFormal.IUT.XiFPaper.Mzk1XiEContainmentRequirementActual
open MeasureTheory
open scoped ENNReal

universe u

/-- A618 proof 1: the height estimate is available (bridge data as input). -/
theorem a618_heightEstimate {X : Type u} {W : IQHullLogVolumeInterface X}
    {epsilon : Real} (C : Cor312EpsilonArithmeticComparison W epsilon)
    (h0 : 0 ≤ epsilon) (h1 : epsilon ≤ 1) :
    ∃ D : Real, ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤
        (1 + 3 * epsilon) * arithmeticWeight (abcRationalPoint a c) +
          (1 + epsilon) * ((W.logVolume W.hull).toReal + D) :=
  height_estimate C h0 h1

/-- A618 proof 2: the volume estimate is available. -/
theorem a618_volumeEstimate {X : Type u} {W : IQHullLogVolumeInterface X}
    {epsilon : Real} (C : Cor312EpsilonArithmeticComparison W epsilon) :
    ∃ D : Real, ∀ a b c : Nat, IsABCTriple a b c →
      (W.logVolume (C.comparisonRegion a b c)).toReal ≤
        (1 + epsilon) * arithmeticWeight (abcRationalPoint a c) +
          (W.logVolume W.hull).toReal + D :=
  volume_estimate_exists C

/-- A618 proof 3: the model-level reduction to the global height-weight bound. -/
theorem a618_modelReduction {X : Type u} {W : IQHullLogVolumeInterface X}
    (C : ∀ epsilon : Real, 0 < epsilon → Cor312EpsilonArithmeticComparison W epsilon) :
    HeightWeightBoundShape :=
  heightWeightBoundShape_of_family C

/-- A618 proof 4: resolved requirement strict signed inequality. -/
theorem a618_requirementStrict {α : Type} {vol : Set α → Real}
    (D : XiEContainmentRequirement α vol) :
    requirementSignedQ D < requirementSignedTheta D :=
  (resolvedRequirementAcceptance D).strict_signed

/-! ### Axiom gates -/

#print axioms a618_heightEstimate
#print axioms a618_volumeEstimate
#print axioms a618_modelReduction
#print axioms a618_requirementStrict

#check a618_heightEstimate

end LeanFormal.IUT.XiFPaper.Mzk1A618ProofQpilotActual
end
