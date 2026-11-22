import tmp.sheaf.xif.paper.GlobalIQHullInterfaceActual
import tmp.sheaf.xif.paper.GlobalThetaPilotPossibleImageGeometryActual

/-! # Theta-pilot hull on GlobalIQAmbient: actual unit region and exact obstruction

GlobalIQHullInterfaceActual supplies, on the actual global completion-packet
tensor

  GlobalIQAmbient C3 j,

the actual global unit region globalIQUnitRegion C3 j, its actual compactness,
the actual additive Haar measure globalIQHaar C3 j, and the actual Haar
log-volume.

GlobalThetaPilotPossibleImageGeometryActual supplies the actual qside
possible-image set

  globalThetaPilotPossibleImageSet T
    : Set (Bad (nativePlaceSelection T) -> {x : Real // 0 < x}).

There is no actual transport from this qside image carrier into
GlobalIQAmbient C3 j in the tree.  Consequently the Theta-pilot hull and its
compactness on GlobalIQAmbient are not constructed, and no normalized hull
log-volume is fabricated.  This file records the exact required hull/transport
data using the actual global unit region/Haar.

No [0,1] box and no F_l^x function-space carrier is used.  No sorry, axiom,
True, or PUnit. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.PaperThetaPilotHullOnGlobalIQNormalizedActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.XiFPaper.GlobalIQHullInterfaceActual
open LeanFormal.IUT.XiFPaper.GlobalThetaPilotPossibleImageGeometryActual
open MeasureTheory

universe ua uv upi umon ui u

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable [forall i, Fintype (C3.tensorPlaceIndex i)]
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (j : Nat)

/-- The actual qside possible-image carrier. -/
abbrev QSidePossibleImageCarrier : Type :=
  Bad (nativePlaceSelection T) -> {x : Real // 0 < x}

/-- The actual qside possible-image set. -/
abbrev qSidePossibleImageSet : Set (QSidePossibleImageCarrier (T := T)) :=
  globalThetaPilotPossibleImageSet T

/-- Exact missing transport from the qside possible-image carrier into the
global IQ tensor ambient, compatible with the Theta values and the global unit
region. -/
structure QSideToGlobalIQTransport where
  toGlobal : QSidePossibleImageCarrier (T := T) -> GlobalIQAmbient (C3 := C3) j
  image_identification : Prop
  haar_compat : Prop

/-- Exact Theta-pilot hull data on GlobalIQAmbient, with the actual global unit
region and Haar normalization containment. -/
structure GlobalIQThetaPilotHullData where
  transport : QSideToGlobalIQTransport (C3 := C3) (T := T) j
  imageSet : Set (GlobalIQAmbient (C3 := C3) j)
  imageSet_eq : imageSet = transport.toGlobal '' qSidePossibleImageSet (T := T)
  hull : Set (GlobalIQAmbient (C3 := C3) j)
  image_subset_hull : imageSet ⊆ hull
  hull_compact : IsCompact hull
  hull_subset_unitRegion :
    hull ⊆ (globalIQUnitRegion (C3 := C3) j : Set (GlobalIQAmbient (C3 := C3) j))
  unitRegion_measure_positive :
    0 < globalIQHaar (C3 := C3) j (globalIQUnitRegion (C3 := C3) j)
  unitRegion_measure_lt_top :
    globalIQHaar (C3 := C3) j (globalIQUnitRegion (C3 := C3) j) < ⊤

/-- Exact obstruction: the qside-to-GlobalIQ transport and the resulting hull
data are required; no inhabitant is asserted. -/
def GlobalIQThetaPilotHullNormalizationRequired : Prop :=
  Nonempty (GlobalIQThetaPilotHullData (C3 := C3) (T := T) j)

/-- Actual global IQ unit-region compactness is available. -/
theorem globalIQUnitRegion_compact_available :
    IsCompact (globalIQUnitRegion (C3 := C3) j) :=
  globalIQUnitRegion_compact C3 j

/-- Conditional actual raw hull Haar log-volume once the exact hull data is
supplied.  This is the actual Haar log-volume, not a normalized paper
log-volume. -/
noncomputable def globalIQThetaPilotHullRawLogVolume
    (H : GlobalIQThetaPilotHullData (C3 := C3) (T := T) j) : Real :=
  (globalIQLogVolume C3 j H.hull).toReal

end LeanFormal.IUT.XiFPaper.PaperThetaPilotHullOnGlobalIQNormalizedActual

end
