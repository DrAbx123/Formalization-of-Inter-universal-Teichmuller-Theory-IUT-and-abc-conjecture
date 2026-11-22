import tmp.sheaf.xif.paper.SignedHnormalObjectActualAdapted
import tmp.sheaf.xif.paper.SignedUnitFactorThetaActualAdaptedAdapted
import tmp.sheaf.xif.paper.UnitFactorThetaActualAdapted
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceArithmeticTupleHullVolume

/-!
# Actual product-Haar / Fubini object for the signed unit-factor identity

The actual product/Fubini target is

  ArithmeticTupleHullUnitLogVolumeSpec places tuple
    (signedAverage - log(unitReferenceMeasure)).

`arithmeticTupleHullUnitLogVolume_spec` produces the actual spec at the
canonical value `arithmeticTupleHullUnitLogVolume`. Therefore the product
identity is equivalent, by uniqueness of the spec, to the exact scalar
measure identity

  arithmeticTupleHullUnitLogVolume
    = signedAverage - log(unitReferenceMeasure).

This file constructs the actual product-Haar object from that exact missing
scalar identity. No inequality is asserted; the identity itself is not
fabricated. No toy/axiom/sorry. WRITE-ONLY: no lake.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.SignedProductHaarThetaActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8C6ActualIQ
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.PaperThetaMagnitudeSignedActual
open LeanFormal.IUT.XiFPaper.SignedHnormalObjectActualAdapted
open LeanFormal.IUT.XiFPaper.SignedUnitFactorThetaActualAdaptedAdapted
open MeasureTheory
open scoped BigOperators

universe ua uv upi umon ui uK uW

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable {K : Type uK} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {iota : Type uv} [Fintype iota] {W : iota -> Type uW}
variable (places : (i : iota) -> W i -> FinitePlaceAtPrime K p)
variable (tuple : (i : iota) -> W i)
variable [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
variable [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
variable (mu : Measure (ArithmeticTensorTupleBlock places tuple))
variable [Measure.IsAddHaarMeasure mu]

variable (D : SourcePilotRegionDonors (l := l) (V := V) I)

noncomputable abbrev actualSignedC3 :
    SourcePilotRegionData (l := l) (V := V) I :=
  sourceTheaterC3Signed (l := l) (V := V) (I := I) D

noncomputable def actualSignedAverage : Real :=
  (c3ThetaSignedProcession (actualSignedC3 (l := l) (V := V) (I := I) D)).average

def actualUnitLog : Real :=
  arithmeticTupleHullUnitLogVolume places tuple

def actualUnitReferenceMeasure : ENNReal :=
  mu (arithmeticTupleCanonicalUnitReference places tuple)

theorem actualUnitReferenceMeasure_pos :
    0 < actualUnitReferenceMeasure (l := l) places tuple mu :=
  (measure_arithmeticTupleCanonicalRegions_pos_lt_top places tuple mu).2.1

theorem actualUnitReferenceMeasure_lt_top :
    actualUnitReferenceMeasure (l := l) places tuple mu < ⊤ :=
  (measure_arithmeticTupleCanonicalRegions_pos_lt_top places tuple mu).2.2

/-- The actual product-Haar spec target at the signed-average value. -/
def ActualProductHaarSpec : Prop :=
  ArithmeticTupleHullUnitLogVolumeSpec places tuple
    (actualSignedAverage (l := l) (V := V) (I := I) D -
      Real.log (actualUnitReferenceMeasure (l := l) places tuple mu).toReal)

/-- Exact missing scalar measure identity, equivalent to the product spec. -/
def MissingActualProductHaarMeasureIdentity : Prop :=
  actualUnitLog (l := l) places tuple =
    actualSignedAverage (l := l) (V := V) (I := I) D -
      Real.log (actualUnitReferenceMeasure (l := l) places tuple mu).toReal

/-- The scalar measure identity is exactly the product-Haar spec, by the
/-- actual existence/uniqueness of the unit log-volume spec. -/
theorem missingActualProductHaarMeasureIdentity_iff_spec :
    MissingActualProductHaarMeasureIdentity (l := l) (V := V) (I := I)
      places tuple mu D ↔
      ActualProductHaarSpec (l := l) (V := V) (I := I) places tuple mu D := by
  unfold MissingActualProductHaarMeasureIdentity ActualProductHaarSpec
  constructor
  · intro h
    rw [← h]
    exact arithmeticTupleHullUnitLogVolume_spec places tuple
  · intro h
    have huniq := existsUnique_arithmeticTupleHullUnitLogVolume places tuple
    exact huniq.unique (arithmeticTupleHullUnitLogVolume_spec places tuple) h

/-- Actual product-Haar object: actual unit log, unit-reference measure, signed
/-- average, and the product/Fubini spec. -/
structure ActualProductHaarThetaObject where
  unitLog : Real
  unitReferenceMeasure : ENNReal
  unitReferenceMeasure_pos : 0 < unitReferenceMeasure
  unitReferenceMeasure_lt_top : unitReferenceMeasure < ⊤
  signedAverage : Real
  productHaarSpec : ArithmeticTupleHullUnitLogVolumeSpec places tuple
    (signedAverage - Real.log unitReferenceMeasure.toReal)

/-- Construct the actual product-Haar object from the exact missing scalar
/-- measure identity. -/
def actualProductHaarThetaObject
    (h : MissingActualProductHaarMeasureIdentity (l := l) (V := V) (I := I)
      places tuple mu D) :
    ActualProductHaarThetaObject (l := l) places tuple mu where
  unitLog := actualUnitLog (l := l) places tuple
  unitReferenceMeasure := actualUnitReferenceMeasure (l := l) places tuple mu
  unitReferenceMeasure_pos := actualUnitReferenceMeasure_pos (l := l) places tuple mu
  unitReferenceMeasure_lt_top := actualUnitReferenceMeasure_lt_top (l := l) places tuple mu
  signedAverage := actualSignedAverage (l := l) (V := V) (I := I) D
  productHaarSpec := (missingActualProductHaarMeasureIdentity_iff_spec
    (l := l) (V := V) (I := I) places tuple mu D).mp h

/-- The object's unit log is the actual arithmetic-tuple unit log. -/
theorem actualProductHaarThetaObject_unitLog
    (h : MissingActualProductHaarMeasureIdentity (l := l) (V := V) (I := I)
      places tuple mu D) :
    (actualProductHaarThetaObject (l := l) (V := V) (I := I)
      places tuple mu D h).unitLog = actualUnitLog (l := l) places tuple :=
  rfl

#check ActualProductHaarSpec
#check MissingActualProductHaarMeasureIdentity
#check missingActualProductHaarMeasureIdentity_iff_spec
#check ActualProductHaarThetaObject
#check actualProductHaarThetaObject
#check actualProductHaarThetaObject_unitLog

end LeanFormal.IUT.XiFPaper.SignedProductHaarThetaActualAdapted

end
