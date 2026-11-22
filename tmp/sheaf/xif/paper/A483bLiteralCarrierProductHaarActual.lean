/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.LiteralIQCarrierConstructionActual
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.PadicLogShellModel
import LeanFormal.IUT.IUTIII.Theorem311.SourceOriginalInput
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceArithmeticIQTensor

/-! # A483b: literal carrier product-Haar facts (fresh filename) -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.LitIQCarrierProductHaarV2

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.LiteralIQCarrierConstruction
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.PadicLogShellModel
open MeasureTheory

variable {l : PrimeGeFive} {V : Type}
variable {I : OriginalInput.{0, 0, 0, 0, 0} l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable [forall i, Fintype (C3.tensorPlaceIndex i)]

def litUnitRegion (j : Nat) : Set (LiteralIQAmbient (C3 := C3) j) :=
  literalIQUnitRegion (C3 := C3) j

theorem litUnitRegion_compact (j : Nat) : IsCompact (litUnitRegion C3 j) :=
  isCompact_arithmeticTensorLogRegion (literalIQPlaces (C3 := C3) j)

@[reducible] def litMeasurable (j : Nat) : MeasurableSpace (LiteralIQAmbient (C3 := C3) j) :=
  borel (LiteralIQAmbient (C3 := C3) j)

def litHaar (j : Nat) : Measure (LiteralIQAmbient (C3 := C3) j) := 
  letI : MeasurableSpace (LiteralIQAmbient (C3 := C3) j) := litMeasurable (C3 := C3) j
  Measure.addHaar

theorem litHaar_translate (j : Nat) (a : LiteralIQAmbient (C3 := C3) j)
    (S : Set (LiteralIQAmbient (C3 := C3) j)) :
    litHaar (C3 := C3) j ((fun x => a + x) '' S) = litHaar (C3 := C3) j S := by
  letI : MeasurableSpace (LiteralIQAmbient (C3 := C3) j) := litMeasurable (C3 := C3) j
  haveI hAdd : Measure.IsAddHaarMeasure (litHaar (C3 := C3) j) := by
    unfold litHaar
    infer_instance
  haveI hInv : Measure.IsAddLeftInvariant (litHaar (C3 := C3) j) :=
    hAdd.toIsAddLeftInvariant
  exact LeanFormal.IUT.PadicLogShellModel.measure_image_add_translate
    (litHaar (C3 := C3) j) a S

end LeanFormal.IUT.XiFPaper.LitIQCarrierProductHaarV2
