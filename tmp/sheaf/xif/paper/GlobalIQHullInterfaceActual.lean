import tmp.sheaf.xif.paper.LiteralIQCarrierConstructionActual
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceHullCompactnessReduction
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceIQHullInterface
import LeanFormal.IUT.IUTIII.Theorem311.SourceOriginalInput

/-!
# Global IQ hull interface: actual constructible part

The global ambient is the actual tensor packet of j+1 completion packets:

  GlobalIQAmbient C3 j = LiteralIQAmbient C3 j
                       = ArithmeticPacketTensor (literalIQPlaces C3 j).

On this global carrier the following objects are actual and constructed here:

* the global unit region literalIQUnitRegion C3 j;
* the actual additive Haar measure literalIQHaar C3 j;
* the global Haar log-volume haarLogVolume (literalIQHaar C3 j);
* monotonicity of the global log-volume;
* compactness of the global unit region.

The global Theta-pilot imageSet/hull, the lambda-scaling scaleShift and the
Haar containment/normalization fields are not supplied by the current global
tensor carrier alone.  They are recorded as exact missing fields; no finite C6
interface is used or renamed as global.

No PUnit/True, arbitrary data, axiom or sorry is used.
-/

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

namespace LeanFormal.IUT.XiFPaper.GlobalIQHullInterfaceActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.XiFPaper.LiteralIQCarrierConstruction
open MeasureTheory

variable {l : PrimeGeFive} {V : Type}
variable {I : OriginalInput.{0, 0, 0, 0, 0} l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable [forall i, Fintype (C3.tensorPlaceIndex i)]

/-- The actual global ambient tensor packet at level j. -/
abbrev GlobalIQAmbient (j : Nat) : Type :=
  LiteralIQAmbient C3 j

noncomputable instance globalIQMeasurableSpace (j : Nat) :
    MeasurableSpace (GlobalIQAmbient C3 j) :=
  inferInstanceAs (MeasurableSpace (LiteralIQAmbient C3 j))

/-- Actual global unit region at level j. -/
def globalIQUnitRegion (j : Nat) : Set (GlobalIQAmbient C3 j) :=
  literalIQUnitRegion C3 j

/-- Actual global additive Haar measure at level j. -/
noncomputable def globalIQHaar (j : Nat) :
    Measure (GlobalIQAmbient C3 j) :=
  literalIQHaar C3 j

/-- The Haar measure is an actual additive Haar measure. -/
instance globalIQHaar_isAddHaar (j : Nat) :
    Measure.IsAddHaarMeasure (globalIQHaar C3 j) := by
  unfold globalIQHaar literalIQHaar
  infer_instance

/-- Actual global Haar log-volume on regions of the global ambient. -/
noncomputable def globalIQLogVolume (j : Nat) :
    Set (GlobalIQAmbient C3 j) → ENNReal :=
  fun S => haarLogVolume (globalIQHaar C3 j) S

/-- The global log-volume is the actual Haar log-volume. -/
theorem globalIQLogVolume_eq (j : Nat) (S : Set (GlobalIQAmbient C3 j)) :
    globalIQLogVolume C3 j S = haarLogVolume (globalIQHaar C3 j) S := rfl

/-- Monotonicity of the actual global Haar log-volume. -/
theorem globalIQLogVolume_mono (j : Nat) {S T : Set (GlobalIQAmbient C3 j)}
    (hST : S ⊆ T) :
    globalIQLogVolume C3 j S ≤ globalIQLogVolume C3 j T :=
  haarLogVolume_mono (μ := globalIQHaar C3 j) hST

/-- The actual global unit region is compact. -/
theorem globalIQUnitRegion_compact (j : Nat) :
    IsCompact (globalIQUnitRegion C3 j) :=
  isCompact_arithmeticTensorLogRegion (literalIQPlaces C3 j)

/-- The actual global unit region is exactly the tensor integral region. -/
theorem globalIQUnitRegion_eq (j : Nat) :
    globalIQUnitRegion C3 j =
      arithmeticTensorLogRegion (literalIQPlaces C3 j) := rfl

/-- Actual constructible part of the global IQ hull interface. -/
structure GlobalIQHullConstructiblePart (j : Nat) where
  unitRegion : Set (GlobalIQAmbient C3 j)
  unitRegion_eq : unitRegion = globalIQUnitRegion C3 j
  logVolume : Set (GlobalIQAmbient C3 j) → ENNReal
  logVolume_eq : logVolume = globalIQLogVolume C3 j
  logVolume_mono : ∀ {S T : Set (GlobalIQAmbient C3 j)}, S ⊆ T →
    logVolume S ≤ logVolume T
  unitRegion_compact : IsCompact unitRegion

/-- The actual constructible part on the global tensor ambient. -/
noncomputable def globalIQHullConstructiblePart (j : Nat) :
    GlobalIQHullConstructiblePart C3 j where
  unitRegion := globalIQUnitRegion C3 j
  unitRegion_eq := rfl
  logVolume := globalIQLogVolume C3 j
  logVolume_eq := rfl
  logVolume_mono := globalIQLogVolume_mono C3 j
  unitRegion_compact := globalIQUnitRegion_compact C3 j

/-- Exact missing global hull fields: global Theta-pilot image set and hull,
their containment, the lambda-scaling, and its unit-region normalization. -/
structure GlobalIQHullMissingFields
    (P : GlobalIQHullConstructiblePart C3 j) where
  imageSet : Set (GlobalIQAmbient C3 j)
  hull : Set (GlobalIQAmbient C3 j)
  imageSet_subset_hull : imageSet ⊆ hull
  scaleShift : GlobalIQAmbient C3 j → GlobalIQAmbient C3 j
  hull_subset_scaleShift : hull ⊆ scaleShift '' P.unitRegion
  unitRegion_logVolume_lt_top : P.logVolume P.unitRegion < ⊤
  scaleShift_unitRegion_logVolume_le :
    P.logVolume (scaleShift '' P.unitRegion) ≤ P.logVolume P.unitRegion

/-- Exact obstruction: the global IQ hull interface requires the global
Theta-pilot image/hull and lambda-scaling fields not supplied by the tensor
ambient alone. -/
def GlobalIQHullInterfaceObstruction (j : Nat) : Prop :=
  Nonempty (GlobalIQHullMissingFields C3 (globalIQHullConstructiblePart C3 j))

/-- Conditional full global IQHullLogVolumeInterface from the actual
constructible part plus the exact missing global image/hull/scaling fields. -/
noncomputable def globalIQHullInterfaceOfMissing (j : Nat)
    (M : GlobalIQHullMissingFields C3 (globalIQHullConstructiblePart C3 j)) :
    IQHullLogVolumeInterface (GlobalIQAmbient C3 j) where
  imageSet := M.imageSet
  hull := M.hull
  imageSet_subset_hull := M.imageSet_subset_hull
  logVolume := globalIQLogVolume C3 j
  logVolume_mono := globalIQLogVolume_mono C3 j
  unitRegion := globalIQUnitRegion C3 j
  scaleShift := M.scaleShift
  hull_subset_scaleShift := by
    simpa [globalIQHullConstructiblePart] using M.hull_subset_scaleShift
  unitRegion_logVolume_lt_top := by
    simpa [globalIQHullConstructiblePart] using M.unitRegion_logVolume_lt_top
  scaleShift_unitRegion_logVolume_le := by
    simpa [globalIQHullConstructiblePart] using M.scaleShift_unitRegion_logVolume_le

/-- The conditional interface's log-volume is the actual global Haar
log-volume. -/
theorem globalIQHullInterfaceOfMissing_logVolume (j : Nat)
    (M : GlobalIQHullMissingFields C3 (globalIQHullConstructiblePart C3 j)) :
    (globalIQHullInterfaceOfMissing C3 j M).logVolume =
      globalIQLogVolume C3 j := rfl

end LeanFormal.IUT.XiFPaper.GlobalIQHullInterfaceActual

end

