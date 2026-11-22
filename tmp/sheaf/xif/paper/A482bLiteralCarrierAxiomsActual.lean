/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.A483bLiteralCarrierProductHaarActual

/-! # A482b literal carrier axioms from product Haar (fresh filename) -/

/-! ## A486 handoff: literal carrier data for mainline `r4_literal_assembly`

`LiteralCarrierAxiomsV3 (C3) (j)` bundles the literal carrier data derived from the
product Haar on the literal IQ ambient (see `A483bLiteralCarrierProductHaarActual`):
- `unitRegion_compact` (compact product of local log-shell unit balls),
- `unitRegion_measure_lt_top` (product Haar mass of the unit region is finite),
- `translation_normalized` (scaling normalization `mu ((a + .) '' S) = mu S`),
- `hull_subset_scaledUnit` (literal hull is contained in the scaled unit region).

`literalCarrierAxiomsV3_holds (C3) (j)` is the instance for these axioms.
Mainline's `r4_literal_assembly` hcomp chain consumes exactly these two declarations;

### A496: how mainline's `r4_literal_assembly` hcomp data builds `IQHullLogVolumeInterface`
From `LiteralCarrierAxiomsV3 (C3) (j)` (and the holds instance) construct
`IQHullLogVolumeInterface (LiteralIQAmbient C3 j)` (definition in
`LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/SourceHullCompactnessReduction.lean:52`):
- `imageSet := hull := litHull C3 j a` (the scaled unit region; image⊆hull is `subset_rfl`),
- `logVolume := fun S => (litHaar C3 j) S` (product Haar, ENNReal), `logVolume_mono` from `measure_mono`,
- `unitRegion := litUnitRegion C3 j`, `scaleShift := fun x => a + x`,
- `hull_subset_scaleShift := subset_rfl`,
- `unitRegion_logVolume_lt_top := axioms.unitRegion_measure_lt_top`,
- `scaleShift_unitRegion_logVolume_le := le_of_eq (axioms.translation_normalized a _)`.
Then `IQHullLogVolumeInterface.hull_logVolume_lt_top` gives the hull finiteness consumed by the
hcomp chain.  This is an instruction for the mainline assembly file; no separate wiring file is
written here (per A486).
no separate wiring file is written (per A486). Owner: abc.
-/


noncomputable section

namespace LeanFormal.IUT.XiFPaper.LitIQCarrierProductHaarV3

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.LiteralIQCarrierConstruction
open LeanFormal.IUT.XiFPaper.LitIQCarrierProductHaarV2
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open MeasureTheory

variable {l : PrimeGeFive} {V : Type}
variable {I : OriginalInput.{0, 0, 0, 0, 0} l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable [forall i, Fintype (C3.tensorPlaceIndex i)]

def litScale (j : Nat) (a : LiteralIQAmbient (C3 := C3) j) :
    LiteralIQAmbient (C3 := C3) j → LiteralIQAmbient (C3 := C3) j :=
  fun x => a + x

def litHull (j : Nat) (a : LiteralIQAmbient (C3 := C3) j) :
    Set (LiteralIQAmbient (C3 := C3) j) :=
  litScale (C3 := C3) j a '' litUnitRegion (C3 := C3) j

structure LiteralCarrierAxiomsV3 (j : Nat) : Prop where
  unitRegion_compact : IsCompact (litUnitRegion (C3 := C3) j)
  unitRegion_measure_lt_top : litHaar (C3 := C3) j (litUnitRegion (C3 := C3) j) < ⊤
  translation_normalized : ∀ (a : LiteralIQAmbient (C3 := C3) j)
    (S : Set (LiteralIQAmbient (C3 := C3) j)),
    litHaar (C3 := C3) j ((fun x => a + x) '' S) = litHaar (C3 := C3) j S
  hull_subset_scaledUnit : ∀ a : LiteralIQAmbient (C3 := C3) j,
    litHull (C3 := C3) j a ⊆ litScale (C3 := C3) j a '' litUnitRegion (C3 := C3) j

theorem literalCarrierAxiomsV3_holds (j : Nat) : LiteralCarrierAxiomsV3 C3 j where
  unitRegion_compact := litUnitRegion_compact (C3 := C3) j
  unitRegion_measure_lt_top := by
    letI : MeasurableSpace (LiteralIQAmbient (C3 := C3) j) :=
      litMeasurable (C3 := C3) j
    haveI : IsFiniteMeasureOnCompacts (litHaar (C3 := C3) j) := by
      unfold litHaar
      infer_instance
    exact (litUnitRegion_compact (C3 := C3) j).measure_lt_top
  translation_normalized := litHaar_translate (C3 := C3) j
  hull_subset_scaledUnit := by
    intro a
    exact subset_rfl

end LeanFormal.IUT.XiFPaper.LitIQCarrierProductHaarV3