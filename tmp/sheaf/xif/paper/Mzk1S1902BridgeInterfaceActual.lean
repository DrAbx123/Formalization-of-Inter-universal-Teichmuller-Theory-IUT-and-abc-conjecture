/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.ABCBridge.Bridge.Cor312ToABCBridgeInterface
import tmp.sheaf.xif.paper.S1902ActualThetaHullActual

/-!
# A614 S1902 BRIDGE INTERFACE (mainline)

Construct the `Cor312ToABCBridgeInterface` with the REAL paper objects:
* `carrier := S1902Carrier T`;
* `hullData := s1902IQHullLogVolumeInterface T` (the concrete S1902 hull/measure interface
  from the hull lane);
* `epsilonComparison` uses the concrete comparison region and the real
  `(s1902IQHullLogVolumeInterface T).logVolume`, with the two IUT IV Thm 1.10 inequalities kept as
  **explicit hypothesis parameters** (`hheight` = Gap 1 height comparison,
  `hvolume` = Gap 2 region volume bound).

No object is changed and nothing unproved is hidden: the remaining named content is
exactly the two concrete inequalities.  ABC gate NOT passed. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1S1902BridgeInterfaceActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))] [Nonempty (Bad (nativePlaceSelection T))]

/-- **The concrete S1902 bridge data**: the carrier and hull data are the real paper
  objects; the two IUT IV Thm 1.10 inequalities are explicit parameters. -/
noncomputable def s1902Bridge
    (logShellPoint : Nat → Nat → Nat → S1902Carrier T)
    (hheight : ∀ epsilon : ℝ, 0 < epsilon → ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤
        (1 + epsilon) *
          ((s1902IQHullLogVolumeInterface T).logVolume
            (normalizedComparisonRegion (s1902IQHullLogVolumeInterface T) logShellPoint a b c)).toReal)
    (hvolume : ∀ epsilon : ℝ, 0 < epsilon → ∃ D : ℝ,
      ∀ a b c : Nat, IsABCTriple a b c →
        ((s1902IQHullLogVolumeInterface T).logVolume
            (normalizedComparisonRegion (s1902IQHullLogVolumeInterface T) logShellPoint a b c)).toReal ≤
          (1 + epsilon) * arithmeticWeight (abcRationalPoint a c) +
            ((s1902IQHullLogVolumeInterface T).logVolume (s1902IQHullLogVolumeInterface T).hull).toReal + D) :
    Cor312ToABCBridgeInterface where
  carrier := S1902Carrier T
  hullData := s1902IQHullLogVolumeInterface T
  epsilonComparison := fun epsilon hepsilon =>
    { logShellPoint := logShellPoint
      height_le_normalizedRegionVolume := hheight epsilon hepsilon
      regionVolume_le_normalizedWeight := hvolume epsilon hepsilon }

/-- **Conditional ABC from the concrete S1902 bridge interface.** -/
theorem s1902Bridge_abc
    (logShellPoint : Nat → Nat → Nat → S1902Carrier T)
    (hheight : ∀ epsilon : ℝ, 0 < epsilon → ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤
        (1 + epsilon) *
          ((s1902IQHullLogVolumeInterface T).logVolume
            (normalizedComparisonRegion (s1902IQHullLogVolumeInterface T) logShellPoint a b c)).toReal)
    (hvolume : ∀ epsilon : ℝ, 0 < epsilon → ∃ D : ℝ,
      ∀ a b c : Nat, IsABCTriple a b c →
        ((s1902IQHullLogVolumeInterface T).logVolume
            (normalizedComparisonRegion (s1902IQHullLogVolumeInterface T) logShellPoint a b c)).toReal ≤
          (1 + epsilon) * arithmeticWeight (abcRationalPoint a c) +
            ((s1902IQHullLogVolumeInterface T).logVolume (s1902IQHullLogVolumeInterface T).hull).toReal + D) :
    ABCConjecture :=
  cor312ToABCBridge_abcConjecture (s1902Bridge T logShellPoint hheight hvolume)

end LeanFormal.IUT.XiFPaper.Mzk1S1902BridgeInterfaceActual

end
/-! ### Axiom gate (top level) -/

#print axioms LeanFormal.IUT.XiFPaper.Mzk1S1902BridgeInterfaceActual.s1902Bridge_abc
