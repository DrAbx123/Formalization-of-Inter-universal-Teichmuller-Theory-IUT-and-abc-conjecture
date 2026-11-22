import tmp.sheaf.xif.paper.C3LogShellTensorHolomorphicHullActual
import tmp.sheaf.xif.paper.C3LogShellTensorPacketActual

/-! # Weak actual Theta-pilot hull log-volume candidate

This is the weak object requested for the direct inequality route.  On the
actual C3 log-shell tensor block it uses:

* the actual tensor integral region of local log-shells as the unit/Theta
  container;
* the actual least lambda-O holomorphic hull of that region;
* the actual additive Haar measure and Haar log-volume of the C3 tensor packet.

It does not compare carriers, does not prove a unit-region normalization
equivalence, and does not identify this weak container with the paper's full
multiradial Theta-pilot hull.  It provides the actual real quantity
weakThetaHullLogVolume that can be used in a direct inequality.

No [0,1] box, no F_l^x function-space carrier, no fake normalized log-volume,
no sorry/axiom/True/PUnit. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.WeakThetaHullLogVolumeActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorHolomorphicHullActual
open MeasureTheory

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{0, uv, upi, umon, ui} l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

/-- The actual weak Theta hull container: the C3 tensor integral region of
local log-shells. -/
abbrev weakThetaHullRegion : Set (HullBlock C3) :=
  actualUnitRegion C3

/-- The actual least lambda-O hull of the weak Theta region. -/
noncomputable def weakThetaHull : Set (HullBlock C3) :=
  actualHolomorphicHull C3 (weakThetaHullRegion C3)

/-- The weak hull is exactly the actual tensor region. -/
theorem weakThetaHull_eq_region :
    weakThetaHull C3 = weakThetaHullRegion C3 :=
  actualHolomorphicHull_unitRegion_eq C3

/-- The actual Haar measure on the weak hull block. -/
noncomputable def weakThetaHullHaar : Measure (HullBlock C3) :=
  actualC3LogShellTensorHaar C3

/-- The actual Haar log-volume of the weak Theta hull. -/
noncomputable def weakThetaHullLogVolume : Real :=
  (haarLogVolume (weakThetaHullHaar C3) (weakThetaHull C3)).toReal

/-- The weak hull log-volume equals the actual C3 tensor log-volume. -/
theorem weakThetaHullLogVolume_eq_tensor :
    weakThetaHullLogVolume C3 =
      actualC3LogShellTensorLogVolume C3 := by
  unfold weakThetaHullLogVolume actualC3LogShellTensorLogVolume
  rw [weakThetaHull_eq_region]
  rfl

/-- The actual weak hull container is compact. -/
theorem weakThetaHull_compact :
    IsCompact (weakThetaHull C3) := by
  rw [weakThetaHull_eq_region]
  exact actualC3LogShellTensorRegion_compact (I := I) C3

/-- The actual weak hull data package. -/
structure WeakThetaHullLogVolumeData where
  block : Type
  block_eq : block = HullBlock C3
  hull : Set block
  hull_eq : hull = weakThetaHull C3
  hull_compact : IsCompact hull
  haar : Measure block
  haar_eq : haar = weakThetaHullHaar C3
  logVolume : Real
  logVolume_eq : logVolume = weakThetaHullLogVolume C3

/-- The actual weak hull log-volume data. -/
noncomputable def weakThetaHullLogVolumeData :
    WeakThetaHullLogVolumeData (I := I) C3 where
  block := HullBlock C3
  block_eq := rfl
  hull := weakThetaHull C3
  hull_eq := rfl
  hull_compact := weakThetaHull_compact (I := I) C3
  haar := weakThetaHullHaar C3
  haar_eq := rfl
  logVolume := weakThetaHullLogVolume C3
  logVolume_eq := rfl

end LeanFormal.IUT.XiFPaper.WeakThetaHullLogVolumeActual

end
