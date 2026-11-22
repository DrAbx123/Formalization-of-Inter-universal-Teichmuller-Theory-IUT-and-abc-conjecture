import tmp.sheaf.xif.paper.S1902ActualThetaHullActual
import tmp.sheaf.xif.paper.Mzk1ABCTwoEstimatesRealModelShaActual
import tmp.sheaf.xif.paper.Mzk1ABCBridgeHeightRegionActual

/-!
# shehdd A614 S1902 concrete hullData instance and concrete bridge (Sha)

Concrete instance of the Cor 3.12 hull interface:
`s1902IQHullLogVolumeInterface T : IQHullLogVolumeInterface (S1902Carrier T)`
(actual image set, actual hull, actual normalized Haar log-volume, actual unit
region, identity scale shift).  Using the concrete comparison-region family
`logShellPoint := fun _ _ _ => 0`, the two named Gap packages give:
* the real `ABCTwoEstimates` object (our A612 real-model wiring);
* a concrete `Cor312ToABCBridgeInterface`;
* conditional `ABCConjecture`.

Only Gap 1 (`height_le_normalizedRegionVolume`) and Gap 2 remain named; no
`logVolume := arithmeticWeight` substitution, no sorry/axiom/True.
-/

-- A615 SUPPLEMENTARY (shehdd Sha variant): canonical files are hull's
-- `Mzk1S1902IQHullInterfaceActual` (hullData instance) and mainline's
-- `Mzk1S1902BridgeInterfaceActual` (concrete bridge).  This file is independent
-- supplementary evidence; it never overwrites/imports-by-patch those canonical files.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1S1902ConcreteBridgeShaActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.Mzk1ABCTwoEstimatesRealModelShaActual
open LeanFormal.IUT.XiFPaper.Mzk1ABCBridgeHeightRegionActual

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Concrete S1902 hullData instance for the Cor 3.12 interface. -/
noncomputable def s1902HullData : IQHullLogVolumeInterface (S1902Carrier T) :=
  s1902IQHullLogVolumeInterface T

/-- Concrete comparison-region family: the zero point of the S1902 carrier. -/
noncomputable def s1902ComparisonPoint : Nat → Nat → Nat → S1902Carrier T :=
  fun _ _ _ => 0

/-- Concrete real-model estimates from the two Gap packages on the S1902 carrier. -/
noncomputable def s1902RealEstimates
    (Gap1 : ∀ ε : Real, 0 < ε →
      HeightRegionGap1Data (s1902HullData T) (s1902ComparisonPoint T) ε)
    (Gap2 : ∀ ε : Real, 0 < ε → ∃ D0 : Real,
      ∀ a b c : Nat, IsABCTriple a b c →
        ((s1902HullData T).logVolume
          (normalizedComparisonRegion (s1902HullData T) (s1902ComparisonPoint T) a b c)).toReal ≤
            (1 + ε) * arithmeticWeight (abcRationalPoint a c) +
              ((s1902HullData T).logVolume (s1902HullData T).hull).toReal + D0) :
    LeanFormal.IUT.XiFPaper.Mzk1ABCTwoEstimatesShaActual.ABCTwoEstimates :=
  realABCTwoEstimates (s1902HullData T) (s1902ComparisonPoint T) Gap1 Gap2

/-- Concrete comparison-region bridge interface from the two Gap packages. -/
noncomputable def s1902ConcreteBridge
    (Gap1 : ∀ ε : Real, 0 < ε →
      HeightRegionGap1Data (s1902HullData T) (s1902ComparisonPoint T) ε)
    (Gap2 : ∀ ε : Real, 0 < ε → ∃ D0 : Real,
      ∀ a b c : Nat, IsABCTriple a b c →
        ((s1902HullData T).logVolume
          (normalizedComparisonRegion (s1902HullData T) (s1902ComparisonPoint T) a b c)).toReal ≤
            (1 + ε) * arithmeticWeight (abcRationalPoint a c) +
              ((s1902HullData T).logVolume (s1902HullData T).hull).toReal + D0) :
    Cor312ToABCBridgeInterface :=
  bridgeInterfaceOfHeightRegionGap1 (S1902Carrier T) (s1902HullData T)
    (s1902ComparisonPoint T) Gap1 Gap2

/-- Conditional ABC from the two Gap packages on the concrete S1902 carrier. -/
theorem s1902_concrete_abc
    (Gap1 : ∀ ε : Real, 0 < ε →
      HeightRegionGap1Data (s1902HullData T) (s1902ComparisonPoint T) ε)
    (Gap2 : ∀ ε : Real, 0 < ε → ∃ D0 : Real,
      ∀ a b c : Nat, IsABCTriple a b c →
        ((s1902HullData T).logVolume
          (normalizedComparisonRegion (s1902HullData T) (s1902ComparisonPoint T) a b c)).toReal ≤
            (1 + ε) * arithmeticWeight (abcRationalPoint a c) +
              ((s1902HullData T).logVolume (s1902HullData T).hull).toReal + D0) :
    ABCConjecture :=
  abc_of_realGap1Gap2 (s1902HullData T) (s1902ComparisonPoint T) Gap1 Gap2

/-- Conditional ABC via the concrete bridge interface. -/
theorem s1902_concrete_abc_of_bridge
    (Gap1 : ∀ ε : Real, 0 < ε →
      HeightRegionGap1Data (s1902HullData T) (s1902ComparisonPoint T) ε)
    (Gap2 : ∀ ε : Real, 0 < ε → ∃ D0 : Real,
      ∀ a b c : Nat, IsABCTriple a b c →
        ((s1902HullData T).logVolume
          (normalizedComparisonRegion (s1902HullData T) (s1902ComparisonPoint T) a b c)).toReal ≤
            (1 + ε) * arithmeticWeight (abcRationalPoint a c) +
              ((s1902HullData T).logVolume (s1902HullData T).hull).toReal + D0) :
    ABCConjecture :=
  cor312ToABCBridgeInterface_abcConjecture_of_nonempty
    ⟨s1902ConcreteBridge T Gap1 Gap2⟩

end LeanFormal.IUT.XiFPaper.Mzk1S1902ConcreteBridgeShaActual
