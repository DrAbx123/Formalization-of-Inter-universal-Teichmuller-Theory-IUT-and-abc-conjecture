/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.A483bLiteralCarrierProductHaarActual

/-! # A482 literal carrier axioms from product Haar (consumer side) -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.LitIQCarrierProductHaarV2

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.LiteralIQCarrierConstruction
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open MeasureTheory
open LeanFormal.IUT.XiFPaper.LitIQCarrierProductHaarV2

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

structure LiteralCarrierAxioms (j : Nat) : Prop where
  unitRegion_compact : IsCompact (litUnitRegion (C3 := C3) j)
  unitRegion_measure_lt_top : litHaar (C3 := C3) j (litUnitRegion (C3 := C3) j) < ⊤
  translation_normalized : ∀ (a : LiteralIQAmbient (C3 := C3) j)
    (S : Set (LiteralIQAmbient (C3 := C3) j)),
    litHaar (C3 := C3) j ((fun x => a + x) '' S) = litHaar (C3 := C3) j S
  hull_subset_scaledUnit : ∀ a : LiteralIQAmbient (C3 := C3) j,
    litHull (C3 := C3) j a ⊆ litScale (C3 := C3) j a '' litUnitRegion (C3 := C3) j

theorem literalCarrierAxioms_holds (j : Nat) : LiteralCarrierAxioms C3 j where
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

end LeanFormal.IUT.XiFPaper.LitIQCarrierProductHaarV2
