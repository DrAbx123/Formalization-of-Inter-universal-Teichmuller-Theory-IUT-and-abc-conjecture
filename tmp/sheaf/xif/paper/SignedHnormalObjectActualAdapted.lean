import tmp.sheaf.xif.paper.ThetaProcessionUnconditionalActualAdapted
import tmp.sheaf.xif.paper.SignedUnitFactorThetaActualAdapted
import tmp.sheaf.xif.paper.SignedHnormalActual
import tmp.sheaf.xif.paper.UnitReferenceMeasureActual

/-!
# Actual signed Hnormal / product-Haar object

Uses the actual theta packet, signed procession, and hull carrier from
ThetaProcessionUnconditionalActualAdapted. Constructs the actual unit-factor value
object and the product-Haar specification wrapper. The only missing measure
objects are:

* `MissingSignedProductHaarThetaIdentity`: the actual product/Fubini
  specification of `arithmeticTupleHullUnitLogVolume` with value
  signedAverage - log(unitReference measure);
* `UnitReferenceMeasureGeOne`: the canonical unit-reference normalization.

`SignedHnormal` then follows from these plus the actual unit-factor formula,
by the existing SignedHnormalActual theorem. No inequality is asserted and
no missing object is inhabited. WRITE-ONLY: no lake.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.SignedHnormalObjectActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8C6ActualIQ
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.PaperThetaMagnitudeSignedActual
open LeanFormal.IUT.XiFPaper.SignedUnitFactorThetaActualAdapted
open LeanFormal.IUT.XiFPaper.SignedHnormalActual
open LeanFormal.IUT.XiFPaper.UnitReferenceMeasureActual
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

/-- The actual signed source-theater C3. -/
noncomputable abbrev actualSignedC3 :
    SourcePilotRegionData (l := l) (V := V) I :=
  sourceTheaterC3Signed (l := l) (V := V) (I := I) D

/-- The actual signed theta average. -/
noncomputable def actualSignedAverage : Real :=
  (c3ThetaSignedProcession (actualSignedC3 (l := l) (V := V) (I := I) D)).average

/-- The actual hull unit log-volume object. -/
def actualUnitLog : Real :=
  arithmeticTupleHullUnitLogVolume places tuple

/-- The actual canonical unit-reference Haar measure value. -/
def actualUnitReferenceMeasure : ENNReal :=
  mu (arithmeticTupleCanonicalUnitReference places tuple)

theorem actualUnitReferenceMeasure_pos :
    0 < actualUnitReferenceMeasure (l := l) places tuple mu :=
  unitReference_measure_pos places tuple mu

theorem actualUnitReferenceMeasure_lt_top :
    actualUnitReferenceMeasure (l := l) places tuple mu < ⊤ :=
  unitReference_measure_lt_top places tuple mu

/-- The actual unit-factor value: unit log + log(unit-reference measure). -/
noncomputable def actualSignedUnitFactorValue : Real :=
  actualUnitLog (l := l) places tuple +
    Real.log (actualUnitReferenceMeasure (l := l) places tuple mu).toReal

/-- The exact missing product-Haar specification: the actual unit log-volume
/-- is the signed average minus the unit-reference log. -/
def MissingSignedProductHaarThetaIdentity : Prop :=
  SignedProductHaarThetaIdentity (l := l) (V := V) (I := I)
    (places := places) (tuple := tuple) mu
    (actualSignedC3 (l := l) (V := V) (I := I) D)

/-- Actual unit-factor object packaging the actual unit log, unit-reference
/-- measure, signed average, and the conditional product-Haar specification. -/
structure ActualSignedUnitFactorThetaObject where
  unitLog : Real
  unitReferenceMeasure : ENNReal
  unitReferenceMeasure_pos : 0 < unitReferenceMeasure
  unitReferenceMeasure_lt_top : unitReferenceMeasure < ⊤
  signedAverage : Real
  productHaarSpec : ArithmeticTupleHullUnitLogVolumeSpec places tuple
    (signedAverage - Real.log unitReferenceMeasure.toReal)

/-- Construct the actual object from the exact missing product-Haar identity. -/
def actualSignedUnitFactorThetaObject
    (h : MissingSignedProductHaarThetaIdentity
      (l := l) (V := V) (I := I) (places := places) (tuple := tuple) mu D) :
    ActualSignedUnitFactorThetaObject (l := l) places tuple mu where
  unitLog := actualUnitLog (l := l) places tuple
  unitReferenceMeasure := actualUnitReferenceMeasure (l := l) places tuple mu
  unitReferenceMeasure_pos := actualUnitReferenceMeasure_pos (l := l) places tuple mu
  unitReferenceMeasure_lt_top := actualUnitReferenceMeasure_lt_top (l := l) places tuple mu
  signedAverage := actualSignedAverage (l := l) (V := V) (I := I) D
  productHaarSpec := h

/-- The object's unit-factor value is the actual signed unit-factor value. -/
theorem actualSignedUnitFactorThetaObject_value
    (h : MissingSignedProductHaarThetaIdentity
      (l := l) (V := V) (I := I) (places := places) (tuple := tuple) mu D) :
    (actualSignedUnitFactorThetaObject (l := l) (V := V) (I := I)
      places tuple mu D h).unitLog = actualUnitLog (l := l) places tuple :=
  rfl

/-- Exact missing measure/normalization object, stated separately. -/
def MissingUnitReferenceNormalization : Prop :=
  UnitReferenceMeasureGeOne places tuple mu

/-- The missing unit-factor identity is exactly the product-Haar identity. -/
theorem missingSignedUnitFactor_iff_product
    (h : MissingSignedProductHaarThetaIdentity
      (l := l) (V := V) (I := I) (places := places) (tuple := tuple) mu D) :
    SignedUnitFactorThetaIdentity (l := l) (V := V) (I := I)
      (places := places) (tuple := tuple) mu
      (actualSignedC3 (l := l) (V := V) (I := I) D) :=
  signedUnitFactorThetaIdentity_of_missingProduct
    (l := l) (V := V) (I := I) (places := places) (tuple := tuple) mu
    (actualSignedC3 (l := l) (V := V) (I := I) D) h

#check actualSignedC3
#check actualSignedAverage
#check actualUnitLog
#check actualUnitReferenceMeasure
#check actualSignedUnitFactorValue
#check MissingSignedProductHaarThetaIdentity
#check ActualSignedUnitFactorThetaObject
#check actualSignedUnitFactorThetaObject
#check MissingUnitReferenceNormalization
#check missingSignedUnitFactor_iff_product

end LeanFormal.IUT.XiFPaper.SignedHnormalObjectActualAdapted

end
