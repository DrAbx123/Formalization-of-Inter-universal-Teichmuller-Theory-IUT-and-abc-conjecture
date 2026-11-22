/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Quantifiers
import tmp.sheaf.xif.paper.S1902ActualThetaHullActual
import LeanFormal.IUT.ABCBridge.Bridge.Cor312ToABCBridgeInterface

/-!
# A618 scaling obstruction (machine-checked; mainline)

The actual S1902 hull interface has `scaleShift = id`.  If the comparison region is
then triple-independent (e.g. the identity scaling applied to a fixed unit region, or
any region that ignores the point datum), the height comparison is FALSE:
`no_constantRegion_heightComparison` (green bridge module) shows, for any fixed region
`R` and any `ε`, that `Height.logHeight₁ (abcRationalPoint a c) <= (1+ε) * logVolume R`
cannot hold on all ABC triples, because the heights of `abcRationalPoint a c` are
unbounded (`abcRationalPoint_logHeight_unbounded`) while the right-hand side is a
fixed constant.

This is why the metric paper comparison region must depend on the triple
(`Mzk1PaperComparisonRegionScalingActual.tripleScale`): the fixed-`scaleShift = id`
shape cannot support the height comparison.

Nothing here changes any object or claims any estimate; ABC gate NOT passed. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace Mzk1A618ScalingObstructionActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))] [Nonempty (Bad (nativePlaceSelection T))]

set_option maxHeartbeats 1000000 in
/-- **A618 obstruction**: with the actual hull interface (`scaleShift = id`) and the
  triple-independent unit region, no height comparison can hold. -/
theorem identity_scaleShift_obstruction (epsilon : ℝ) :
    ¬ (∀ a b c : Nat, IsABCTriple a b c →
        Height.logHeight₁ (abcRationalPoint a c) ≤
          (1 + epsilon) * (s1902LogVolume T (s1902UnitRegion T)).toReal) :=
  no_constantRegion_heightComparison (s1902IQHullLogVolumeInterface T)
    (s1902UnitRegion T) epsilon

end Mzk1A618ScalingObstructionActual

end

/-! ### Axiom gate (top level) -/

#print axioms Mzk1A618ScalingObstructionActual.identity_scaleShift_obstruction
