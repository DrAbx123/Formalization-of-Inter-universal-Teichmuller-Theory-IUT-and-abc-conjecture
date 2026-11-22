import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceArithmeticIQTensor
import tmp.sheaf.n8.closure.SourcePilotRegion
import tmp.sheaf.xif.paper.ThetaHullActual
import tmp.sheaf.xif.paper.PaperProcessionNormalization
import LeanFormal.IUT.IUTIII.Theorem311.SourceOriginalInput

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.LiteralIQCarrierConstruction

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.XiFPaperThetaHull
open MeasureTheory
open scoped BigOperators

variable {l : PrimeGeFive} {V : Type}
variable {I : OriginalInput.{0, 0, 0, 0, 0} l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable [forall i, Fintype (C3.tensorPlaceIndex i)]

abbrev LiteralIQIndex (j : Nat) : Type :=
  Fin (j + 1) × C3.tensorIndex

abbrev LiteralIQPlaceIndex (j : Nat) : LiteralIQIndex C3 j -> Type :=
  fun x => C3.tensorPlaceIndex x.2

def literalIQPlaces (j : Nat) :
    (x : LiteralIQIndex C3 j) -> LiteralIQPlaceIndex C3 j x ->
      FinitePlaceAtPrime I.initial.arithmetic.Fmod C3.p :=
  fun x => C3.tensorPlaces x.2

abbrev LiteralIQAmbient (j : Nat) : Type :=
  ArithmeticPacketTensor (literalIQPlaces C3 j)

abbrev LiteralIQCarrier (j : Nat) : Type :=
  arithmeticIQCarrier (literalIQPlaces C3 j)

theorem literalIQCarrier_eq_span (j : Nat) :
    LiteralIQCarrier C3 j = Submodule.span ℚ
      (arithmeticTensorLogRegion (literalIQPlaces C3 j)) := rfl

def literalIQUnitRegion (j : Nat) : Set (LiteralIQAmbient C3 j) :=
  arithmeticTensorLogRegion (literalIQPlaces C3 j)

noncomputable instance literalIQMeasurableSpace (j : Nat) :
    MeasurableSpace (LiteralIQAmbient C3 j) :=
  borel (LiteralIQAmbient C3 j)

noncomputable instance literalIQBorelSpace (j : Nat) :
    BorelSpace (LiteralIQAmbient C3 j) :=
  ⟨rfl⟩

noncomputable def literalIQHaar (j : Nat) : Measure (LiteralIQAmbient C3 j) :=
  Measure.addHaar

instance literalIQHaar_isAddHaar (j : Nat) :
    Measure.IsAddHaarMeasure (literalIQHaar C3 j) := by
  unfold literalIQHaar
  infer_instance

noncomputable def literalIQLocalLogVolume (j : Nat) : Real :=
  Real.log ((literalIQHaar C3 j (literalIQUnitRegion C3 j)).toReal)

noncomputable def literalIQProcessionAverage : Real :=
  (canonicalProcession (l := l)).average
    (fun j : SignedLabel l.value => literalIQLocalLogVolume C3 j.1.natAbs)

structure LiteralIQCarrierData (j : Nat) where
  carrier : Type
  carrier_eq : carrier = LiteralIQCarrier C3 j
  haar : Measure (LiteralIQAmbient C3 j)
  haar_eq : haar = literalIQHaar C3 j
  unitRegion : Set (LiteralIQAmbient C3 j)
  unitRegion_eq : unitRegion = literalIQUnitRegion C3 j

noncomputable def literalIQCarrierData (j : Nat) : LiteralIQCarrierData C3 j where
  carrier := LiteralIQCarrier C3 j
  carrier_eq := rfl
  haar := literalIQHaar C3 j
  haar_eq := rfl
  unitRegion := literalIQUnitRegion C3 j
  unitRegion_eq := rfl

theorem literalIQProcessionAverage_eq :
    literalIQProcessionAverage C3 =
      (canonicalProcession (l := l)).average
        (fun j : SignedLabel l.value => literalIQLocalLogVolume C3 j.1.natAbs) := rfl

#check literalIQHaar
#check literalIQLocalLogVolume
#check literalIQCarrierData
end LeanFormal.IUT.XiFPaper.LiteralIQCarrierConstruction
end