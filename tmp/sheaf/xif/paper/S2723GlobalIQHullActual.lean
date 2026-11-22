import tmp.sheaf.xif.paper.S2718LiteralDDataActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceArithmeticIQTensor
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceIQHullInterface
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceHullCompactnessReduction

noncomputable section
open scoped BigOperators
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2723GlobalIQHullActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.Theorem311Source.SourceProcessionCapsule
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.XiFPaper.S2718LiteralDDataActual
open MeasureTheory

variable {l : PrimeGeFive} {V : Type}
variable {I : OriginalInput.{0, 0, 0, 0, 0} l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable [forall i, Fintype (C3.tensorPlaceIndex i)]

/-- The global index of the literal IQ carrier: capsule label times the
literal place index `LiteralPlace = Sigma C3.tensorIndex, tensorPlaceIndex`. -/
abbrev GlobalIQIndex (j : Nat) : Type :=
  Capsule j × LiteralPlace (I := I) C3 PUnit.unit

/-- The actual global place family: each literal place is the actual C3 tensor
place.  The inner family is `PUnit` because the literal place already contains
the C3 tensor place index. -/
abbrev GlobalIQPlaceIndex (j : Nat) :
    GlobalIQIndex (C3 := C3) j → Type := fun _ => PUnit

def globalIQPlaces (j : Nat) :
    (x : GlobalIQIndex (C3 := C3) j) →
      GlobalIQPlaceIndex (C3 := C3) j x →
        FinitePlaceAtPrime I.initial.arithmetic.Fmod C3.p :=
  fun x _ => C3.tensorPlaces x.2.1 x.2.2

/-- The actual global IQ ambient tensor packet over the literal place family. -/
abbrev GlobalIQAmbient (j : Nat) : Type :=
  ArithmeticPacketTensor (globalIQPlaces (C3 := C3) j)

local instance globalIQAmbientMeasurableSpace (j : Nat) :
    MeasurableSpace (GlobalIQAmbient (C3 := C3) j) := borel _

local instance globalIQAmbientBorelSpace (j : Nat) :
    BorelSpace (GlobalIQAmbient (C3 := C3) j) := ⟨rfl⟩

/-- The actual global unit region: the tensor integral region of completion
packets at the literal places. -/
def globalIQUnitRegion (j : Nat) :
    Set (GlobalIQAmbient (C3 := C3) j) :=
  arithmeticTensorLogRegion (globalIQPlaces (C3 := C3) j)

theorem globalIQUnitRegion_compact (j : Nat) :
    IsCompact (globalIQUnitRegion (C3 := C3) j) :=
  isCompact_arithmeticTensorLogRegion _

/-- The actual global additive Haar measure on the global IQ ambient. -/
noncomputable def globalIQHaar (j : Nat) :
    Measure (GlobalIQAmbient (C3 := C3) j) := Measure.addHaar

instance globalIQHaar_isAddHaar (j : Nat) :
    Measure.IsAddHaarMeasure (globalIQHaar (C3 := C3) j) := by
  unfold globalIQHaar
  infer_instance

/-- The actual global Haar log-volume functional. -/
noncomputable def globalIQLogVolume (j : Nat) :
    Set (GlobalIQAmbient (C3 := C3) j) → ENNReal :=
  fun S => haarLogVolume (globalIQHaar (C3 := C3) j) S

theorem globalIQLogVolume_mono (j : Nat)
    {S T : Set (GlobalIQAmbient (C3 := C3) j)} (hST : S ⊆ T) :
    globalIQLogVolume (C3 := C3) j S ≤ globalIQLogVolume (C3 := C3) j T :=
  haarLogVolume_mono (μ := globalIQHaar (C3 := C3) j) hST

/-- The actual global log-shell point: the identity point of the tensor packet. -/
def globalIQLogShellPoint (j : Nat) :
    GlobalIQAmbient (C3 := C3) j := 1

theorem globalIQLogShellPoint_mem_unitRegion (j : Nat) :
    globalIQLogShellPoint (C3 := C3) j ∈ globalIQUnitRegion (C3 := C3) j :=
  one_mem_arithmeticTensorLogRegion _

/-- The global hull used by the interface: the actual tensor integral region.
This is the global counterpart of the actual C3 least lambda-O hull, whose
unit-region hull is the unit region itself. -/
def globalIQHull (j : Nat) :
    Set (GlobalIQAmbient (C3 := C3) j) :=
  globalIQUnitRegion (C3 := C3) j

theorem globalIQUnitRegion_logVolume_lt_top (j : Nat) :
    globalIQLogVolume (C3 := C3) j (globalIQUnitRegion (C3 := C3) j) < ⊤ := by
  have hfin : globalIQHaar (C3 := C3) j
      (globalIQUnitRegion (C3 := C3) j) < ⊤ :=
    IsCompact.measure_lt_top (globalIQUnitRegion_compact (I := I) C3 j)
  unfold globalIQLogVolume
  rw [haarLogVolume_of_lt_top hfin]
  exact ENNReal.ofReal_lt_top

/-- The actual global IQ hull log-volume interface on the literal carrier. -/
noncomputable def globalIQHullInterface (j : Nat) :
    IQHullLogVolumeInterface (GlobalIQAmbient (C3 := C3) j) where
  imageSet := globalIQUnitRegion (C3 := C3) j
  hull := globalIQHull (C3 := C3) j
  imageSet_subset_hull := subset_rfl
  logVolume := globalIQLogVolume (C3 := C3) j
  logVolume_mono := globalIQLogVolume_mono (I := I) C3 j
  unitRegion := globalIQUnitRegion (C3 := C3) j
  scaleShift := id
  hull_subset_scaleShift := by
    intro x hx
    exact ⟨x, hx, rfl⟩
  unitRegion_logVolume_lt_top := globalIQUnitRegion_logVolume_lt_top (I := I) C3 j
  scaleShift_unitRegion_logVolume_le := by
    simpa [globalIQHull] using
      (le_refl (globalIQLogVolume (C3 := C3) j (globalIQUnitRegion (C3 := C3) j)))

theorem globalIQHullInterface_logVolume (j : Nat)
    (S : Set (GlobalIQAmbient (C3 := C3) j)) :
    (globalIQHullInterface (C3 := C3) j).logVolume S =
      globalIQLogVolume (C3 := C3) j S := rfl

theorem globalIQHullInterface_hull (j : Nat) :
    (globalIQHullInterface (C3 := C3) j).hull =
      globalIQHull (C3 := C3) j := rfl

#check GlobalIQIndex
#check globalIQPlaces
#check GlobalIQAmbient
#check globalIQHaar
#check globalIQLogVolume
#check globalIQLogShellPoint
#check globalIQLogShellPoint_mem_unitRegion
#check globalIQHull
#check globalIQHullInterface
#print axioms globalIQLogShellPoint_mem_unitRegion
#print axioms globalIQHullInterface

end LeanFormal.IUT.XiFPaper.S2723GlobalIQHullActual
end
