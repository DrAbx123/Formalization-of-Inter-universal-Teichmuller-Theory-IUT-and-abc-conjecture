/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1PaperComparisonRegionScalingActual
import tmp.sheaf.xif.paper.Mzk1A618ScalingObstructionActual
import LeanFormal.IUT.ABCBridge.Bridge.Cor312ToABCBridgeInterface

/-! # A631 hull: exact Gap1/Gap2 shapes and the triple-scaling obstruction

Audit record (no theorem conclusion is changed, no canonical file is edited):

* **Gap 1** (`height_le_normalizedRegionVolume` in our bridge interface): the
  height comparison `logHeight (abcRationalPoint a c) <= (1+eps) * regionVolume`;
* **Gap 2** (`regionVolume_le_normalizedWeight`): the comparison-region log-volume
  bound `regionVolume <= (1+eps) * arithmeticWeight + thetaHullBound + D`;
* with the **triple-dependent paper region**
  `paperComparisonRegion point a b c = tripleScale a b c '' (unitRegion ∪ {point})`
  the two gaps have exactly the shapes below;
* with a **triple-independent** region the height comparison is impossible
  (`no_constantRegion_heightComparison`, A618), so the triple dependence is not
  cosmetic: ANY fixed region (in particular the identity `scaleShift = id` shape)
  cannot satisfy Gap 1.

Nothing here proves either gap; they remain explicit hypotheses.  ABC gate NOT
passed. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.Mzk1GapShapeAuditActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.Mzk1PaperComparisonRegionScalingActual
open MeasureTheory
open scoped ENNReal BigOperators

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))] [Nonempty (Bad (nativePlaceSelection T))]

/-- **Gap 1 shape** on the triple-dependent paper comparison region. -/
def Gap1Shape (point : Nat → Nat → Nat → S1902Carrier T) : Prop :=
  ∀ ε : Real, 0 < ε → ∀ a b c : Nat, IsABCTriple a b c →
    Height.logHeight₁ (abcRationalPoint a c) ≤
      (1 + ε) * (s1902LogVolume T (paperComparisonRegion T point a b c)).toReal

/-- **Gap 2 shape** on the triple-dependent paper comparison region. -/
def Gap2Shape (point : Nat → Nat → Nat → S1902Carrier T) : Prop :=
  ∀ ε : Real, 0 < ε → ∃ D : Real,
    ∀ a b c : Nat, IsABCTriple a b c →
      (s1902LogVolume T (paperComparisonRegion T point a b c)).toReal ≤
        (1 + ε) * arithmeticWeight (abcRationalPoint a c) +
          (s1902LogVolume T (s1902Hull T)).toReal + D

/-- The mainline `TripleDependentComparison` is exactly the pair of the two shapes. -/
theorem gapShapes_of_tripleComparison
    (point : Nat → Nat → Nat → S1902Carrier T)
    (C : TripleDependentComparison T point) :
    Gap1Shape T point ∧ Gap2Shape T point :=
  ⟨C.height_le_regionVolume, C.regionVolume_le_weight⟩

/-- **A618 impossibility**: any triple-independent (constant) region fails Gap 1. -/
theorem gap1_impossible_of_constantRegion
    (region : Nat → Nat → Nat → Set (S1902Carrier T))
    (R : Set (S1902Carrier T)) (hconst : ∀ a b c, region a b c = R)
    (ε : Real) :
    ¬ (∀ a b c : Nat, IsABCTriple a b c →
        Height.logHeight₁ (abcRationalPoint a c) ≤
          (1 + ε) * (s1902LogVolume T R).toReal) :=
  no_constantRegion_heightComparison (s1902IQHullLogVolumeInterface T) R ε

/-- Consequently, the fixed-identity paper region cannot satisfy Gap 1: the triple
dependence is necessary. -/
theorem triple_dependence_necessary
    (point : Nat → Nat → Nat → S1902Carrier T)
    (hconst : ∀ a b c, paperComparisonRegion T point a b c = s1902UnitRegion T)
    (ε : Real) :
    ¬ (∀ a b c : Nat, IsABCTriple a b c →
        Height.logHeight₁ (abcRationalPoint a c) ≤
          (1 + ε) * (s1902LogVolume T (s1902UnitRegion T)).toReal) :=
  no_constantRegion_heightComparison (s1902IQHullLogVolumeInterface T)
    (s1902UnitRegion T) ε

def gapShapeRows : List (String × String × String) :=
  [ ("Gap1 shape (UNCORRECTED canonical region)", "Gap1Shape", "DEF (reference shape; not proved here)"),
    ("Gap2 shape (UNCORRECTED canonical region)", "Gap2Shape", "DEF (reference shape; not proved here)"),
    ("corrected-region Gap1", "Mzk1CorrectedGap1UnconditionalActual", "THEOREM in mainline (explicit full-support/d_b≥1/unit≥0)"),
    ("corrected-region Gap2", "corrected Gap2 shape", "REMAINING NAMED input (≡ BadSumWeightBound)"),
    ("triple comparison -> shapes", "gapShapes_of_tripleComparison", "PROVED"),
    ("fixed region fails Gap1", "gap1_impossible_of_constantRegion", "PROVED (A618)"),
    ("triple dependence necessary", "triple_dependence_necessary", "PROVED (A618)"),
    ("scope", "audit only; conclusion unchanged; ABC gate NOT passed", "INTEGRITY") ]

theorem gapShapeRows_length : gapShapeRows.length = 8 := rfl

#print axioms LeanFormal.IUT.XiFPaper.Mzk1GapShapeAuditActual.gapShapes_of_tripleComparison
#print axioms LeanFormal.IUT.XiFPaper.Mzk1GapShapeAuditActual.gap1_impossible_of_constantRegion
#print axioms LeanFormal.IUT.XiFPaper.Mzk1GapShapeAuditActual.triple_dependence_necessary

end LeanFormal.IUT.XiFPaper.Mzk1GapShapeAuditActual

end