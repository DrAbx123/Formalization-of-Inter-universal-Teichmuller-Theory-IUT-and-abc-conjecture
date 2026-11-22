/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.ABCBridge.Bridge.Cor312ToABCBridgeInterface
import tmp.sheaf.xif.paper.Mzk1ABCEstimatesArithmeticQpilotActual
import Mathlib.Tactic

/-! # Mzk1GapShapeAuditQpilotActual — structural/shape audit of Gap1/Gap2

A632 (qpilot lane): the structural shapes of the two IUT IV estimates as Props
over the comparison data, their equivalence with the bridge fields, and the audit
rows.  No object is changed; the named fields remain the paper links. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.Mzk1GapShapeAuditQpilotActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1ABCEstimatesArithmeticQpilotActual
open MeasureTheory
open scoped ENNReal

universe u

/-- Structural Gap-1 shape: height compared with the comparison-region log-volume. -/
def Gap1Shape {X : Type u} (W : IQHullLogVolumeInterface X)
    (logShellPoint : Nat → Nat → Nat → X) (epsilon : Real) : Prop :=
  ∀ a b c : Nat, IsABCTriple a b c →
    Height.logHeight₁ (abcRationalPoint a c) ≤
      (1 + epsilon) * (W.logVolume
        (normalizedComparisonRegion W logShellPoint a b c)).toReal

/-- Structural Gap-2 shape: comparison-region log-volume vs weight + θ + D. -/
def Gap2Shape {X : Type u} (W : IQHullLogVolumeInterface X)
    (logShellPoint : Nat → Nat → Nat → X) (epsilon : Real) : Prop :=
  ∃ D : Real, ∀ a b c : Nat, IsABCTriple a b c →
    (W.logVolume (normalizedComparisonRegion W logShellPoint a b c)).toReal ≤
      (1 + epsilon) * arithmeticWeight (abcRationalPoint a c) +
        (W.logVolume W.hull).toReal + D

/-- Structural equivalence with the bridge data fields. -/
theorem gapShapes_iff_comparison {X : Type u} {W : IQHullLogVolumeInterface X}
    {epsilon : Real} (C : Cor312EpsilonArithmeticComparison W epsilon) :
    Gap1Shape W C.logShellPoint epsilon ∧ Gap2Shape W C.logShellPoint epsilon :=
  ⟨fun a b c habc => C.height_le_normalizedRegionVolume a b c habc,
   C.regionVolume_le_normalizedWeight⟩

/-- From the structural shapes, the absorbed height bound follows (reuse of the
two-estimates arithmetic). -/
theorem height_bound_of_gapShapes {X : Type u} {W : IQHullLogVolumeInterface X}
    {logShellPoint : Nat → Nat → Nat → X} {epsilon : Real}
    (h1 : Gap1Shape W logShellPoint epsilon)
    (h2 : Gap2Shape W logShellPoint epsilon)
    (h0 : 0 ≤ epsilon) (hle : epsilon ≤ 1) :
    ∃ D : Real, ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤
        (1 + 3 * epsilon) * arithmeticWeight (abcRationalPoint a c) +
          (1 + epsilon) * ((W.logVolume W.hull).toReal + D) := by
  obtain ⟨D, hD⟩ := h2
  refine ⟨D, fun a b c habc => ?_⟩
  have hge1 := h1 a b c habc
  have hge2 := hD a b c habc
  have hw : (0 : Real) ≤ arithmeticWeight (abcRationalPoint a c) :=
    arithmeticWeight_nonneg _
  exact height_le_absorbed h0 hle hw (height_le_of_twoEstimates h0 hge1 hge2)

/-- Gap shape audit rows. -/
def gapShapeAuditRows : List (String × String × String) :=
  [ ("Gap1Shape", "DEFINED (structural)", "height vs region log-volume"),
    ("Gap2Shape", "DEFINED (structural)", "region log-volume vs weight+theta+D"),
    ("gapShapes_iff_comparison", "PROVED (from bridge fields)",
     "Cor312EpsilonArithmeticComparison"),
    ("height_bound_of_gapShapes", "PROVED (absorbed bound)",
     "height_le_absorbed") ]

theorem gapShapeAuditRows_length : gapShapeAuditRows.length = 4 := rfl

#check gapShapes_iff_comparison
#check height_bound_of_gapShapes
#check gapShapeAuditRows_length

end LeanFormal.IUT.XiFPaper.Mzk1GapShapeAuditQpilotActual
end
