import tmp.sheaf.xif.paper.GlobalThetaPilotPossibleImageGeometryActual
import tmp.sheaf.xif.paper.GlobalThetaPilotPossibleImagesActual
import tmp.sheaf.xif.paper.GlobalIQHullThetaPilotActual

-- Actual bad-place / global Theta-pilot place comparison data
--
-- Constructs the actual base-place and positive theta-value components of the
-- comparison from the geometry layer, and the actual value-group candidate in
-- the product of the bad-place value groups. The missing source map from
-- bad places to the transport GlobalThetaPilotCarrier / per-V ThetaPilotPoint
-- strip places is recorded as an exact obstruction, not fabricated.
-- WRITE-ONLY: no local lake/lean.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.GlobalThetaPilotPlaceComparisonActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.GlobalThetaPilotLogVolumeActual
open LeanFormal.IUT.XiFPaper.GlobalThetaPilotPossibleImageGeometryActual
open LeanFormal.IUT.XiFPaper.GlobalThetaPilotPossibleImagesActual
open LeanFormal.IUT.XiFPaper.GlobalIQHullThetaPilotActual

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

-- Actual base-place component of the comparison.
noncomputable def badToBasePlace (b : Bad (nativePlaceSelection T)) :
    NumberField.FinitePlace T.arithmetic.Fmod :=
  b.1

-- Actual value-group candidate at the bad places: the positive theta values
-- mapped into the product of the actual local value groups.
noncomputable def globalThetaPilotValueGroupCandidate
    (j : SignedLabel l.value) :
    (Bad (nativePlaceSelection T) → Multiplicative Real) :=
  fun b => Multiplicative.ofAdd
    (Real.log (globalThetaPilotThetaValue T b j))

-- Actual value-group possible-image set.
noncomputable def globalThetaPilotValueGroupPossibleImages :
    Set (Bad (nativePlaceSelection T) → Multiplicative Real) :=
  Set.range (globalThetaPilotValueGroupCandidate T)

theorem globalThetaPilotValueGroupCandidate_mem
    (j : SignedLabel l.value) :
    globalThetaPilotValueGroupCandidate T j ∈
      globalThetaPilotValueGroupPossibleImages T :=
  ⟨j, rfl⟩

-- Exact missing place comparison: a map from the actual bad places to the
-- transport GlobalThetaPilotCarrier / per-V ThetaPilotPoint strip places that
-- carries the actual value-group candidate. The data are explicit; no map is
-- fabricated.
structure GlobalThetaPilotPlaceComparisonData where
  carrier : Type
  toCarrier : Bad (nativePlaceSelection T) → carrier
  stripPlace : Bad (nativePlaceSelection T) → carrier
  candidateImage : SignedLabel l.value → Bad (nativePlaceSelection T) → carrier
  candidateImage_eq : ∀ j b, candidateImage j b = toCarrier b

def GlobalThetaPilotPlaceComparisonObstruction : Prop :=
  Nonempty (GlobalThetaPilotPlaceComparisonData (l := l) T)

-- Exact missing map to the per-V ThetaPilotPoint carrier, stated separately.
structure GlobalThetaPilotThetaPilotPlaceMap (V : Type) where
  carrier : Type
  toThetaPilotCarrier : Bad (nativePlaceSelection T) → V → carrier
  compatible : Prop

def GlobalThetaPilotThetaPilotPlaceMapObstruction (V : Type) : Prop :=
  Nonempty (GlobalThetaPilotThetaPilotPlaceMap (l := l) T V)

#check badToBasePlace
#check globalThetaPilotValueGroupCandidate
#check globalThetaPilotValueGroupPossibleImages
#check globalThetaPilotValueGroupCandidate_mem
#check GlobalThetaPilotPlaceComparisonData
#check GlobalThetaPilotPlaceComparisonObstruction
#check GlobalThetaPilotThetaPilotPlaceMapObstruction

end LeanFormal.IUT.XiFPaper.GlobalThetaPilotPlaceComparisonActual

end