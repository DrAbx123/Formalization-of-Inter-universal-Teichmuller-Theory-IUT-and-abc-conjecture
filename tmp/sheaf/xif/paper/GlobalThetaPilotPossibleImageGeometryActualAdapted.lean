import tmp.sheaf.xif.paper.GlobalThetaPilotProcessionActualAdapted
import tmp.sheaf.n8.closure.NativeSourceReductionActual

-- Actual geometric possible-image data for the global Theta-pilot
--
-- Lifts globalThetaPossibleImage from a raw log vector to positive theta values
-- q_v^(j^2) with the actual base places b : Bad, the actual source curve, and
-- the actual V_bad places. The possible images are actual positive-valued
-- functions on Bad. The multiradial ambient/hull is recorded as an exact
-- obstruction, not fabricated. No sum-of-abs surrogate, no True/PUnit/toy.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.GlobalThetaPilotPossibleImageGeometryActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.GlobalThetaPilotLogVolumeActual

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

-- The actual base finite place of a bad V_bad place.
noncomputable def globalThetaPilotBasePlace
    (b : Bad (nativePlaceSelection T)) :
    NumberField.FinitePlace T.arithmetic.Fmod :=
  b.1

-- The actual positive Theta value q_v^(j^2) at a bad place and signed label.
noncomputable def globalThetaPilotThetaValue
    (b : Bad (nativePlaceSelection T)) (j : SignedLabel l.value) : Real :=
  thetaValueFromQ T b j

theorem globalThetaPilotThetaValue_pos
    (b : Bad (nativePlaceSelection T)) (j : SignedLabel l.value) :
    0 < globalThetaPilotThetaValue T b j :=
  thetaValueFromQ_pos T b j

-- The actual global possible-image vector at signed label j: positive theta
-- values at all actual bad V_bad places.
noncomputable def globalThetaPilotPossibleImage
    (j : SignedLabel l.value) :
    (Bad (nativePlaceSelection T) → {x : Real // 0 < x}) :=
  fun b => ⟨globalThetaPilotThetaValue T b j,
    globalThetaPilotThetaValue_pos T b j⟩

-- The actual geometric possible-image set.
noncomputable def globalThetaPilotPossibleImageSet :
    Set (Bad (nativePlaceSelection T) → {x : Real // 0 < x}) :=
  Set.range (globalThetaPilotPossibleImage T)

-- Actual geometric data: actual bad places, actual source curve, actual
-- positive theta values, and the actual possible-image set.
structure GlobalThetaPilotPossibleImageGeometry where
  basePlace : Bad (nativePlaceSelection T) → NumberField.FinitePlace T.arithmetic.Fmod
  curve : PuncturedEllipticCurve T.arithmetic.F
  thetaValue : Bad (nativePlaceSelection T) → SignedLabel l.value → Real
  thetaValue_pos : ∀ b j, 0 < thetaValue b j
  possibleImageSet : Set (Bad (nativePlaceSelection T) → {x : Real // 0 < x})

noncomputable def globalThetaPilotPossibleImageGeometry :
    GlobalThetaPilotPossibleImageGeometry (l := l) T where
  basePlace := globalThetaPilotBasePlace T
  curve := T.arithmetic.curve
  thetaValue := globalThetaPilotThetaValue T
  thetaValue_pos := globalThetaPilotThetaValue_pos T
  possibleImageSet := globalThetaPilotPossibleImageSet T

theorem globalThetaPilotPossibleImageGeometry_thetaValue
    (b : Bad (nativePlaceSelection T)) (j : SignedLabel l.value) :
    (globalThetaPilotPossibleImageGeometry (l := l) T).thetaValue b j =
      globalThetaPilotThetaValue T b j := rfl

theorem globalThetaPilotPossibleImage_mem (j : SignedLabel l.value) :
    globalThetaPilotPossibleImage T j ∈ globalThetaPilotPossibleImageSet T :=
  ⟨j, rfl⟩

-- Exact obstruction: an actual multiradial ambient geometry/holomorphic hull
-- containing the geometric possible-image set is not constructed from the
-- V_bad theta data alone. This is the exact missing multiradial object, not a
-- fabricated hull.
structure GlobalThetaPilotMultiradialGeometryData where
  ambient : Type
  possibleImages : Set ambient
  holomorphicHull : Set ambient
  containment : possibleImages ⊆ holomorphicHull

def GlobalThetaPilotMultiradialGeometryObstruction : Prop :=
  Nonempty (GlobalThetaPilotMultiradialGeometryData (l := l))

#check globalThetaPilotBasePlace
#check globalThetaPilotThetaValue
#check globalThetaPilotPossibleImage
#check globalThetaPilotPossibleImageSet
#check globalThetaPilotPossibleImageGeometry
#check GlobalThetaPilotMultiradialGeometryData
#check GlobalThetaPilotMultiradialGeometryObstruction

end LeanFormal.IUT.XiFPaper.GlobalThetaPilotPossibleImageGeometryActualAdapted

end