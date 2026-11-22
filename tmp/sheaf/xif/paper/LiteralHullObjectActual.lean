/- Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. -/
import tmp.sheaf.xif.paper.A483bLiteralCarrierProductHaarActual
import tmp.sheaf.xif.paper.LiteralIQCarrierConstructionActual

/-! Literal hull object: the unit region of the literal IQ carrier with its
product Haar measure (A483b litUnitRegion/litHaar), compactness, Haar
finiteness and translation invariance. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.LiteralHullObjectActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.XiFPaper.LitIQCarrierProductHaarV2
open LeanFormal.IUT.XiFPaper.LiteralIQCarrierConstruction
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open MeasureTheory

universe u

variable {l : PrimeGeFive} {V : Type}
variable {I : OriginalInput.{0, 0, 0, 0, 0} l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable [forall i, Fintype (C3.tensorPlaceIndex i)]

section LiteralHullInstances

local instance literalHullMeasurableSpace (j : Nat) :
    MeasurableSpace (LiteralIQAmbient (C3 := C3) j) := borel _

local instance literalHullBorelSpace (j : Nat) :
    BorelSpace (LiteralIQAmbient (C3 := C3) j) := ⟨rfl⟩

/-! ## 1. The literal hull object -/

/-- The literal hull region at level j: the actual global tensor unit region. -/
def literalHullObjectRegion (j : Nat) :
    Set (LiteralIQAmbient (C3 := C3) j) :=
  litUnitRegion C3 j

theorem literalHullObjectRegion_constructed (j : Nat) :
    literalHullObjectRegion C3 j = literalIQUnitRegion (C3 := C3) j := rfl

theorem literalHullObjectRegion_compact (j : Nat) :
    IsCompact (literalHullObjectRegion C3 j) :=
  litUnitRegion_compact (C3 := C3) j

theorem literalHullObjectRegion_measure_lt_top (j : Nat) :
    litHaar (C3 := C3) j (literalHullObjectRegion C3 j) < ⊤ := by
  haveI hAdd : Measure.IsAddHaarMeasure (litHaar (C3 := C3) j) := by
    unfold litHaar
    infer_instance
  haveI hFin : IsFiniteMeasureOnCompacts (litHaar (C3 := C3) j) :=
    hAdd.toIsFiniteMeasureOnCompacts
  exact (literalHullObjectRegion_compact (C3 := C3) j).measure_lt_top

theorem literalHullObjectRegion_translate (j : Nat)
    (a : LiteralIQAmbient (C3 := C3) j)
    (S : Set (LiteralIQAmbient (C3 := C3) j)) :
    litHaar (C3 := C3) j ((fun x => a + x) '' S) =
      litHaar (C3 := C3) j S :=
  litHaar_translate (C3 := C3) j a S

/-- The literal hull object: region and compactness of the literal IQ unit region. -/
structure LiteralHullObject
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    [forall i, Fintype (C3.tensorPlaceIndex i)] (j : Nat) where
  region : Set (LiteralIQAmbient (C3 := C3) j)
  region_eq : region = litUnitRegion C3 j
  compact : IsCompact region

variable (j : Nat)

noncomputable def literalHullObject : LiteralHullObject C3 j where
  region := litUnitRegion C3 j
  region_eq := rfl
  compact := litUnitRegion_compact (C3 := C3) j

theorem literalHullObject_constructed :
    (literalHullObject C3 j).region = literalIQUnitRegion (C3 := C3) j ∧
      IsCompact (literalHullObject C3 j).region := by
  refine ⟨rfl, (literalHullObject C3 j).compact⟩

end LiteralHullInstances

end LeanFormal.IUT.XiFPaper.LiteralHullObjectActual