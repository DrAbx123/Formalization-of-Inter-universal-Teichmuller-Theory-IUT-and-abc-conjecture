import tmp.sheaf.n8.closure.SourceThetaToIQ
import tmp.sheaf.n8.closure.C6ActualIQData
import tmp.sheaf.n8.closure.C6NormalizedTensorHaar
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceHullCompactnessReduction
import Mathlib.MeasureTheory.Measure.Haar.Basic

/-! # Paper IQ carrier actual: C6IQ interface and exact missing fields

This file realizes the `IQHullLogVolumeInterface` on the *actual* C6 IQ
carrier `C6IQCarrier C3.tensorPlaces C3.tensorTuple`, using
`SourceThetaToIQ` (C3 theta image/landing) and `C6ActualIQData.actual`
(actual canonical hull, actual Haar log-volume, actual unit-region interface).

## Actual content

* `IQCarrier C3` is the actual C6 arithmetic tensor tuple block.
* `SourceThetaToIQ.image C3 D n` is the actual source theta image set.
* `C6ActualIQData.actual ... .iqInterface` is the actual
  `IQHullLogVolumeInterface`: canonical hull, Haar log-volume, monotonicity,
  unit-region finiteness and scaling normalization (with the actual R1
  unit-region/scaling placeholder recorded by that interface).
* `actualIQInterface` constructs the interface with the *source* theta image
  as `imageSet`, the actual C6 canonical hull as `hull`, and the actual C6
  Haar log-volume/unit-region/scaling fields. It is conditional exactly on
  `imageSet subset hull` (the C7 theta-containment donor), which is not
  derivable from C3/T11 alone.

## Exact missing fields (not assumed, not proved)

* `image_hull_realization`: source theta image lies in the C6 canonical hull
  (C7 theta-containment donor).
* `OModule_layer`: the literal `O`-module/compactness structure of
  `IQ(S+_{j+1}; n,circ D^vdash_{vQ})`; the current C6 interface is a measure
  interface, not the paper's O-module carrier.
* `compactness`: compactness of the literal `1,circ U_{j,vQ}` carrier; the
  C6 block has a finite Haar measure but not the paper's compact topological
  `IQ` carrier.
* `unitRegion_normalization`: the paper's unit region is the ring-of-integers
  log-shell region, whereas the actual C6 interface's unit region is the
  canonical hull (R1 placeholder).
* `logVolume_normalization`: the paper's procession-normalized mono-analytic
  signed log-volume, not merely the C6 Haar log-volume.
* `literal_IQ_carrier`: the identification of the C6 tensor block with the
  literal `IQ(S+_{j+1}; n,circ D^vdash_{vQ})` label.

No `PUnit`, `True`, `sorry`, or axiom is used. The structure is an exact
obligation surface; no `Nonempty` of the paper object is asserted. In
particular, no false 'unitRegion logVolume = 1' theorem is claimed: the C6
interface supplies only finiteness, not the paper's normalization.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT
namespace N8Closure
namespace PaperIQCarrierActual

open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.SourceThetaToIQ
open LeanFormal.IUT.N8C6ActualIQ
open LeanFormal.IUT.NumberFieldFinitePlace
open MeasureTheory

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}

/-- The actual C6 IQ carrier attached to a C3 tensor tuple. -/
abbrev C6IQCarrierOf (C3 : SourcePilotRegionData (l := l) (V := V) I) : Type (max ua uv) :=
  IQCarrier C3

variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (D : SourceThetaIQInterface (I := I) C3)
variable (n : ThetaPilotCarrier l)
variable [MeasurableSpace (C6IQCarrierOf C3)]
variable [BorelSpace (C6IQCarrierOf C3)]
variable (mu : Measure (C6IQCarrierOf C3))
variable [Measure.IsAddHaarMeasure mu]

set_option maxHeartbeats 4000000

/-- The actual C6 hull is the arithmetic-tuple canonical hull. -/
theorem actualC6_hull_eq_canonical :
    (C6ActualIQData.actual C3.tensorPlaces C3.tensorTuple mu).hull =
      arithmeticTupleCanonicalHull C3.tensorPlaces C3.tensorTuple :=
  rfl

/-- The actual C6 interface's hull is the actual C6 hull. -/
theorem actualC6_iqInterface_hull_eq :
    (C6ActualIQData.actual C3.tensorPlaces C3.tensorTuple mu).iqInterface.hull =
      (C6ActualIQData.actual C3.tensorPlaces C3.tensorTuple mu).hull := by
  dsimp [C6ActualIQData.actual]
  rw [arithmeticTupleIQHullLogVolumeInterface_hull]

/-- The actual C6 interface, conditional on the exact theta-containment donor
`image subset hull`. All other fields are actual C6 interface data. -/
def actualIQInterface
    (hImage : SourceThetaToIQ.image (I := I) C3 D n ⊆
      (C6ActualIQData.actual C3.tensorPlaces C3.tensorTuple mu).hull) :
    IQHullLogVolumeInterface (C6IQCarrierOf C3) :=
  let B := C6ActualIQData.actual C3.tensorPlaces C3.tensorTuple mu
  have hh : B.iqInterface.hull = B.hull :=
    actualC6_iqInterface_hull_eq C3 mu
  { imageSet := SourceThetaToIQ.image (I := I) C3 D n
    hull := B.hull
    imageSet_subset_hull := hImage
    logVolume := B.iqInterface.logVolume
    logVolume_mono := B.iqInterface.logVolume_mono
    unitRegion := B.iqInterface.unitRegion
    scaleShift := B.iqInterface.scaleShift
    hull_subset_scaleShift := by
      rw [← hh]
      exact B.iqInterface.hull_subset_scaleShift
    unitRegion_logVolume_lt_top := B.iqInterface.unitRegion_logVolume_lt_top
    scaleShift_unitRegion_logVolume_le := B.iqInterface.scaleShift_unitRegion_logVolume_le }

@[simp] theorem actualIQInterface_imageSet
    (hImage : SourceThetaToIQ.image (I := I) C3 D n ⊆
      (C6ActualIQData.actual C3.tensorPlaces C3.tensorTuple mu).hull) :
    (actualIQInterface C3 D n mu hImage).imageSet =
      SourceThetaToIQ.image (I := I) C3 D n := rfl

@[simp] theorem actualIQInterface_hull
    (hImage : SourceThetaToIQ.image (I := I) C3 D n ⊆
      (C6ActualIQData.actual C3.tensorPlaces C3.tensorTuple mu).hull) :
    (actualIQInterface C3 D n mu hImage).hull =
      (C6ActualIQData.actual C3.tensorPlaces C3.tensorTuple mu).hull := rfl

theorem actualIQInterface_image_subset_hull
    (hImage : SourceThetaToIQ.image (I := I) C3 D n ⊆
      (C6ActualIQData.actual C3.tensorPlaces C3.tensorTuple mu).hull) :
    (actualIQInterface C3 D n mu hImage).imageSet ⊆
      (actualIQInterface C3 D n mu hImage).hull :=
  hImage

theorem actualIQInterface_hull_logVolume_lt_top
    (hImage : SourceThetaToIQ.image (I := I) C3 D n ⊆
      (C6ActualIQData.actual C3.tensorPlaces C3.tensorTuple mu).hull) :
    (actualIQInterface C3 D n mu hImage).logVolume
      (actualIQInterface C3 D n mu hImage).hull < ⊤ :=
  IQHullLogVolumeInterface.hull_logVolume_lt_top
    (actualIQInterface C3 D n mu hImage)

theorem actualIQInterface_imageSet_logVolume_le_hull
    (hImage : SourceThetaToIQ.image (I := I) C3 D n ⊆
      (C6ActualIQData.actual C3.tensorPlaces C3.tensorTuple mu).hull) :
    (actualIQInterface C3 D n mu hImage).logVolume
      (actualIQInterface C3 D n mu hImage).imageSet ≤
    (actualIQInterface C3 D n mu hImage).logVolume
      (actualIQInterface C3 D n mu hImage).hull :=
  IQHullLogVolumeInterface.imageSet_logVolume_le_hull
    (actualIQInterface C3 D n mu hImage)

theorem actualIQInterface_unitRegion_logVolume_lt_top
    (hImage : SourceThetaToIQ.image (I := I) C3 D n ⊆
      (C6ActualIQData.actual C3.tensorPlaces C3.tensorTuple mu).hull) :
    (actualIQInterface C3 D n mu hImage).logVolume
      (actualIQInterface C3 D n mu hImage).unitRegion < ⊤ :=
  (actualIQInterface C3 D n mu hImage).unitRegion_logVolume_lt_top

theorem actualIQInterface_scaleShift_unitRegion_le
    (hImage : SourceThetaToIQ.image (I := I) C3 D n ⊆
      (C6ActualIQData.actual C3.tensorPlaces C3.tensorTuple mu).hull) :
    (actualIQInterface C3 D n mu hImage).logVolume
      ((actualIQInterface C3 D n mu hImage).scaleShift ''
        (actualIQInterface C3 D n mu hImage).unitRegion) ≤
    (actualIQInterface C3 D n mu hImage).logVolume
      (actualIQInterface C3 D n mu hImage).unitRegion :=
  (actualIQInterface C3 D n mu hImage).scaleShift_unitRegion_logVolume_le

/-- The exact missing fields of the literal paper IQ carrier. These are
obligations, not assumptions: no proof of any field is included. -/
structure PaperIQCarrierMissingFields where
  /-- Source theta image containment in the C6 canonical hull (C7 donor). -/
  image_hull_realization : Prop
  /-- Literal O-module/compactness structure of the IQ carrier. -/
  OModule_layer : Prop
  /-- Compactness of the literal `1,circ U_{j,vQ}` carrier. -/
  compactness : Prop
  /-- Unit region is the paper's ring-of-integers/log-shell region. -/
  unitRegion_normalization : Prop
  /-- Log-volume is the paper's procession-normalized signed log-volume. -/
  logVolume_normalization : Prop
  /-- C6 tensor block = literal `IQ(S+; n,circ D^vdash)` carrier. -/
  literal_IQ_carrier : Prop

/-- The actual paper IQ-carrier surface. It carries the actual C6IQ interface,
its exact source-image and hull identifications, and the missing literal-IQ
fields. No inhabitant is asserted. -/
structure PaperIQCarrierActual
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (D : SourceThetaIQInterface (I := I) C3)
    (n : ThetaPilotCarrier l)
    [MeasurableSpace (C6IQCarrierOf C3)]
    [BorelSpace (C6IQCarrierOf C3)]
    (mu : Measure (C6IQCarrierOf C3))
    [Measure.IsAddHaarMeasure mu] where
  /-- The actual IQHullLogVolumeInterface on the C6 IQ carrier. -/
  interface : IQHullLogVolumeInterface (C6IQCarrierOf C3)
  /-- Its image set is the actual source theta image. -/
  interface_imageSet_eq :
    interface.imageSet = SourceThetaToIQ.image (I := I) C3 D n
  /-- Its hull is the actual C6 canonical hull. -/
  interface_hull_eq :
    interface.hull = (C6ActualIQData.actual C3.tensorPlaces C3.tensorTuple mu).hull
  /-- The exact missing literal-IQ fields. -/
  missing : PaperIQCarrierMissingFields

namespace PaperIQCarrierActual

variable {C3 : SourcePilotRegionData (l := l) (V := V) I}
variable {D : SourceThetaIQInterface (I := I) C3}
variable {n : ThetaPilotCarrier l}
variable [MeasurableSpace (C6IQCarrierOf C3)]
variable [BorelSpace (C6IQCarrierOf C3)]
variable {mu : Measure (C6IQCarrierOf C3)}
variable [Measure.IsAddHaarMeasure mu]

theorem imageSet_eq_source (A : PaperIQCarrierActual (I := I) C3 D n mu) :
    A.interface.imageSet = SourceThetaToIQ.image (I := I) C3 D n :=
  A.interface_imageSet_eq

theorem hull_eq_c6 (A : PaperIQCarrierActual (I := I) C3 D n mu) :
    A.interface.hull =
      (C6ActualIQData.actual C3.tensorPlaces C3.tensorTuple mu).hull :=
  A.interface_hull_eq

theorem imageSet_subset_hull (A : PaperIQCarrierActual (I := I) C3 D n mu) :
    A.interface.imageSet ⊆ A.interface.hull :=
  A.interface.imageSet_subset_hull

theorem hull_logVolume_lt_top (A : PaperIQCarrierActual (I := I) C3 D n mu) :
    A.interface.logVolume A.interface.hull < ⊤ :=
  IQHullLogVolumeInterface.hull_logVolume_lt_top A.interface

theorem imageSet_logVolume_le_hull (A : PaperIQCarrierActual (I := I) C3 D n mu) :
    A.interface.logVolume A.interface.imageSet ≤
      A.interface.logVolume A.interface.hull :=
  IQHullLogVolumeInterface.imageSet_logVolume_le_hull A.interface

theorem unitRegion_logVolume_lt_top (A : PaperIQCarrierActual (I := I) C3 D n mu) :
    A.interface.logVolume A.interface.unitRegion < ⊤ :=
  A.interface.unitRegion_logVolume_lt_top

end PaperIQCarrierActual

end PaperIQCarrierActual
end N8Closure
end LeanFormal.IUT

end
