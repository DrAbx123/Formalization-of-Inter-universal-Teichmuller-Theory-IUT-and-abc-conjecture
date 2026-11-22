/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1A618ScalingObstructionActual
import tmp.sheaf.xif.paper.Mzk1GapStructuralConsequencesActual
import tmp.sheaf.xif.paper.Mzk1RegionNecessitySummaryActual
import tmp.sheaf.xif.paper.Mzk1LanaBridgeAuditActual
import tmp.sheaf.xif.paper.Mzk1PaperComparisonRegionScalingActual
import tmp.sheaf.xif.paper.Mzk1S1902BridgeInterfaceActual

/-!
# A638 PAPER REGION NECESSITY — FINAL AUDIT (mainline)

One theorem packaging the region-necessity audit:
(a) A618 obstruction: with `scaleShift = id` and the triple-independent unit region the
    height comparison fails (`identity_scaleShift_obstruction`);
(b) Gap 1 structural lemmas: any region satisfying Gap 1 has unbounded log-volume, and
    Gap 1 is impossible for a region contained in the finite hull
    (`gap1_forces_unbounded_regionVolume`, `gap1_impossible_of_region_in_finite_hull`);
(c) on the canonical triple-dependent region, `TripleDependentComparison` is equivalent
    to the pair of gap shapes (`Gap1Prop ∧ Gap2Prop`);
(d) those gap shapes imply `ABCConjecture` through the green normalized-volume
    reduction (`abc_of_tripleComparison`);
(e) lana bridge audit status: the external lana repository proves IUT IV Theorem 1.10
    local estimates but its Corollary 3.12 boundary is the SAME unproved hypothesis
    (`lanaAuditRows.length = 11`);
(f) **scope**: gaps NOT proved; ABC gate NOT passed; no canonical object changed.

All `#print axioms` gates below cover only local theorems. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal
namespace IUT
namespace XiFPaper
namespace Mzk1PaperRegionNecessityFinalActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open Mzk1A618ScalingObstructionActual
open LeanFormal.IUT.XiFPaper.Mzk1GapStructuralConsequencesActual
open LeanFormal.IUT.XiFPaper.Mzk1RegionNecessitySummaryActual
open Mzk1LanaBridgeAuditActual
open LeanFormal.IUT.XiFPaper.Mzk1PaperComparisonRegionScalingActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))] [Nonempty (Bad (nativePlaceSelection T))]

/-- (c) backward: the two gap shapes assemble the canonical comparison record. -/
def tripleComparisonOfGapProps
    (point : Nat → Nat → Nat → S1902Carrier T)
    (h1 : Gap1Prop (s1902IQHullLogVolumeInterface T)
      (paperComparisonRegion T point))
    (h2 : Gap2Prop (s1902IQHullLogVolumeInterface T)
      (paperComparisonRegion T point)) :
    TripleDependentComparison T point where
  height_le_regionVolume := h1
  regionVolume_le_weight := h2

/-- (c) forward: the canonical comparison record gives the two gap shapes. -/
theorem gapPropsOfTripleComparison
    (point : Nat → Nat → Nat → S1902Carrier T)
    (C : TripleDependentComparison T point) :
    Gap1Prop (s1902IQHullLogVolumeInterface T)
        (paperComparisonRegion T point) ∧
      Gap2Prop (s1902IQHullLogVolumeInterface T)
        (paperComparisonRegion T point) :=
  gaps_of_tripleComparison T point C

/-- (d) the two gap shapes imply `ABCConjecture` (through the green reduction). -/
theorem abc_of_gapProps
    (point : Nat → Nat → Nat → S1902Carrier T)
    (h1 : Gap1Prop (s1902IQHullLogVolumeInterface T)
      (paperComparisonRegion T point))
    (h2 : Gap2Prop (s1902IQHullLogVolumeInterface T)
      (paperComparisonRegion T point)) : ABCConjecture :=
  abc_of_tripleComparison T point (tripleComparisonOfGapProps T point h1 h2)

/-- **FINAL REGION-NECESSITY AUDIT (a)-(f)**, as a single conjunction. -/
theorem paperRegionNecessityFinal
    (point : Nat → Nat → Nat → S1902Carrier T) (epsilon : ℝ)
    {X : Type*} (W : IQHullLogVolumeInterface X)
    (region : Nat → Nat → Nat → Set X)
    (hfin : W.logVolume W.hull < ⊤)
    (hsub : ∀ a b c : Nat, IsABCTriple a b c → region a b c ⊆ W.hull) :
    (¬ (∀ a b c : Nat, IsABCTriple a b c →
        Height.logHeight₁ (abcRationalPoint a c) ≤
          (1 + epsilon) * (s1902LogVolume T (s1902UnitRegion T)).toReal)) ∧
      (Gap1Prop W region →
        (∀ B : ℝ, ∃ a b c : Nat, IsABCTriple a b c ∧
          B < (W.logVolume (region a b c)).toReal)) ∧
      (¬ Gap1Prop W region) ∧
      (Nonempty (TripleDependentComparison T point) ↔
        (Gap1Prop (s1902IQHullLogVolumeInterface T)
            (paperComparisonRegion T point) ∧
          Gap2Prop (s1902IQHullLogVolumeInterface T)
            (paperComparisonRegion T point))) ∧
      ((Gap1Prop (s1902IQHullLogVolumeInterface T)
          (paperComparisonRegion T point) ∧
        Gap2Prop (s1902IQHullLogVolumeInterface T)
          (paperComparisonRegion T point)) → ABCConjecture) ∧
      (Mzk1LanaBridgeAuditActual.lanaAuditRows.length = 11) :=
  ⟨identity_scaleShift_obstruction T epsilon,
   gap1_forces_unbounded_regionVolume W region,
   gap1_impossible_of_region_in_finite_hull W hfin region hsub,
   ⟨fun h => gapPropsOfTripleComparison T point (Classical.choice h),
     fun h => ⟨tripleComparisonOfGapProps T point h.1 h.2⟩⟩,
   fun h => abc_of_gapProps T point h.1 h.2,
   lanaAuditRows_length⟩

/-- (f) scope record: the audit does not prove the gaps. -/
def scopeRecord : List String :=
  [ "gaps NOT proved",
    "ABC gate NOT passed",
    "no canonical object changed" ]

theorem scopeRecord_length : scopeRecord.length = 3 := rfl

end Mzk1PaperRegionNecessityFinalActual
end XiFPaper
end IUT
end LeanFormal

end

/-! ### Axiom gates (top level; local theorems only) -/

#print axioms LeanFormal.IUT.XiFPaper.Mzk1PaperRegionNecessityFinalActual.paperRegionNecessityFinal
#print axioms LeanFormal.IUT.XiFPaper.Mzk1PaperRegionNecessityFinalActual.abc_of_gapProps
#print axioms LeanFormal.IUT.XiFPaper.Mzk1PaperRegionNecessityFinalActual.gapPropsOfTripleComparison
#print axioms LeanFormal.IUT.XiFPaper.Mzk1PaperRegionNecessityFinalActual.scopeRecord_length