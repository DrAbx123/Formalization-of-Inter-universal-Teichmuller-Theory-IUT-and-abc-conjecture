/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1PaperComparisonRegionScalingActual
import tmp.sheaf.xif.paper.Mzk1A618ScalingObstructionActual
import tmp.sheaf.xif.paper.Mzk1S1902BridgeInterfaceActual

/-!
# A626 scaling AUDIT SUMMARY (mainline)

One-page machine audit of the triple-dependent comparison-region design:
* `Mzk1A618ScalingObstructionActual.identity_scaleShift_obstruction`: the actual hull
  interface (`scaleShift = id`) with a triple-independent region cannot satisfy the
  height comparison (unbounded ABC heights);
* `Mzk1PaperComparisonRegionScalingActual`: `tripleScale`/`paperComparisonRegion`
  with the two IUT IV Thm 1.10 inequalities as explicit epsilon-form fields, and
  `abc_of_tripleComparison` deriving `ABCConjecture` through the green generic
  reduction;
* `Mzk1S1902BridgeInterfaceActual`: canonical concrete bridge on the real S1902
  carrier (`hullData := s1902IQHullLogVolumeInterface T`).

No object changed; no estimate claimed.  ABC gate NOT passed. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1ScalingAuditSummaryActual

open LeanFormal.IUT
open Mzk1A618ScalingObstructionActual
open LeanFormal.IUT.XiFPaper.Mzk1PaperComparisonRegionScalingActual
open LeanFormal.IUT.XiFPaper.Mzk1S1902BridgeInterfaceActual

/-- Audit rows: object, proof status, integrity note. -/
def scalingAuditRows : List (String × String × String) :=
  [ ("A618 obstruction", "identity_scaleShift_obstruction", "PROVED (unbounded heights)"),
    ("triple scaling", "tripleScale", "DEF (a+b+c+1 multiple)"),
    ("paper region shape", "paperComparisonRegion_shape", "PROVED (rfl)"),
    ("Gap1 height comparison", "TripleDependentComparison.height_le_regionVolume", "NAMED"),
    ("Gap2 region volume", "TripleDependentComparison.regionVolume_le_weight", "NAMED"),
    ("conditional ABC", "abc_of_tripleComparison", "PROVED (from two named fields)"),
    ("canonical bridge", "s1902Bridge / s1902Bridge_abc", "PROVED; Gate1/Gate2 named params"),
    ("scope", "ABC gate NOT passed", "INTEGRITY") ]

theorem scalingAuditRows_length : scalingAuditRows.length = 8 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1ScalingAuditSummaryActual

end
/-! ### Axiom gates (top level) -/

#print axioms Mzk1A618ScalingObstructionActual.identity_scaleShift_obstruction
#print axioms LeanFormal.IUT.XiFPaper.Mzk1PaperComparisonRegionScalingActual.abc_of_tripleComparison
#print axioms LeanFormal.IUT.XiFPaper.Mzk1S1902BridgeInterfaceActual.s1902Bridge_abc