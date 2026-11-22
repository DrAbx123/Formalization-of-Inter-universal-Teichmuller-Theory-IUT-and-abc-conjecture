import tmp.sheaf.xif.paper.Mzk1S1902IQHullInterfaceActual
import tmp.sheaf.xif.paper.Mzk1ABCTwoEstimatesRealModelShaActual
import tmp.sheaf.xif.paper.Mzk1ABCBridgeHeightRegionActual

/-!
# shehdd A617 canonical S1902 hullData → concrete bridge/comparison region (Sha)

Uses hull's green canonical concrete instance
`Mzk1S1902IQHullInterfaceActual.s1902IQHullInterface T :
IQHullLogVolumeInterface (S1902Carrier T)` together with the concrete comparison
point `fun _ _ _ => 0`, and feeds the real-model Gap 1 / Gap 2 wiring.

This Sha file is supplementary to canonical hull/mainline bridge files; it imports
the green hull instance read-only and does not overwrite canonical files.
No sorry/axiom/True.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1S1902CanonicalBridgeShaActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.Mzk1S1902IQHullInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1ABCTwoEstimatesRealModelShaActual
open LeanFormal.IUT.XiFPaper.Mzk1ABCBridgeHeightRegionActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))] [Nonempty (Bad (nativePlaceSelection T))]

/-- Canonical concrete hullData instance (re-export, read-only use). -/
noncomputable def canonicalHullData : IQHullLogVolumeInterface (S1902Carrier T) :=
  s1902IQHullInterface T

/-- Concrete comparison-region family on the canonical instance. -/
noncomputable def canonicalComparisonPoint : Nat → Nat → Nat → S1902Carrier T :=
  fun _ _ _ => 0

/-- The canonical instance's hull is the actual S1902 hull (and equals the raw
normalized interface's hull). -/
theorem canonicalHullData_hull_eq :
    (canonicalHullData T).hull = s1902Hull T :=
  rfl

theorem canonicalHullData_hull_eq_raw :
    (canonicalHullData T).hull = (s1902IQHullLogVolumeInterface T).hull :=
  rfl

/-- Canonical image union is the q-pilot singleton, contained in the actual hull. -/
theorem canonicalHullData_imageSet_subset :
    (canonicalHullData T).imageSet ⊆ s1902Hull T :=
  (canonicalHullData T).imageSet_subset_hull

/-- Concrete real-model estimates on the canonical hullData. -/
noncomputable def canonicalRealEstimates
    (Gap1 : ∀ ε : Real, 0 < ε →
      HeightRegionGap1Data (canonicalHullData T) (canonicalComparisonPoint T) ε)
    (Gap2 : ∀ ε : Real, 0 < ε → ∃ D0 : Real,
      ∀ a b c : Nat, IsABCTriple a b c →
        ((canonicalHullData T).logVolume
          (normalizedComparisonRegion (canonicalHullData T) (canonicalComparisonPoint T) a b c)).toReal ≤
            (1 + ε) * arithmeticWeight (abcRationalPoint a c) +
              ((canonicalHullData T).logVolume (canonicalHullData T).hull).toReal + D0) :
    LeanFormal.IUT.XiFPaper.Mzk1ABCTwoEstimatesShaActual.ABCTwoEstimates :=
  realABCTwoEstimates (canonicalHullData T) (canonicalComparisonPoint T) Gap1 Gap2

/-- Conditional ABC from canonical S1902 hullData + Gap1 + Gap2. -/
theorem canonical_concrete_abc
    (Gap1 : ∀ ε : Real, 0 < ε →
      HeightRegionGap1Data (canonicalHullData T) (canonicalComparisonPoint T) ε)
    (Gap2 : ∀ ε : Real, 0 < ε → ∃ D0 : Real,
      ∀ a b c : Nat, IsABCTriple a b c →
        ((canonicalHullData T).logVolume
          (normalizedComparisonRegion (canonicalHullData T) (canonicalComparisonPoint T) a b c)).toReal ≤
            (1 + ε) * arithmeticWeight (abcRationalPoint a c) +
              ((canonicalHullData T).logVolume (canonicalHullData T).hull).toReal + D0) :
    ABCConjecture :=
  abc_of_realGap1Gap2 (canonicalHullData T) (canonicalComparisonPoint T) Gap1 Gap2

end LeanFormal.IUT.XiFPaper.Mzk1S1902CanonicalBridgeShaActual
