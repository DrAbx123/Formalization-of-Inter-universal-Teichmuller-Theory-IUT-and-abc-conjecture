import tmp.sheaf.xif.paper.SignedProductHaarThetaActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceArithmeticTupleHullVolume

/-!
# Unconditional actual product-Haar object

Constructs the actual product-Haar data object unconditionally from the
actual product/Fubini specification of `arithmeticTupleHullUnitLogVolume`
(which has an actual existence/uniqueness theorem), the actual canonical
unit-reference Haar measure, and the actual signed theta average. No scalar
identity is assumed.

The signed product-Haar measure theorem

  arithmeticTupleHullUnitLogVolume
    = signedAverage - log(unitReferenceMeasure)

is recorded as the exact missing measure theorem; only after supplying it is
the signed product-Haar object constructed. No inequality judgments. No
toy/axiom/sorry. WRITE-ONLY: no lake.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.SignedProductHaarUnconditional

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8C6ActualIQ
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.PaperThetaMagnitudeSignedActual
open LeanFormal.IUT.XiFPaper.SignedProductHaarThetaActual
open LeanFormal.IUT.XiFPaper.SignedHnormalObjectActual
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

/-- Actual product-Haar data: actual unit log-volume together with its actual
/-- product/Fubini specification, actual unit-reference measure, and actual
/-- signed average. -/
structure ActualProductHaarData where
  unitLog : Real
  unitLog_spec : ArithmeticTupleHullUnitLogVolumeSpec places tuple unitLog
  unitReferenceMeasure : ENNReal
  unitReferenceMeasure_pos : 0 < unitReferenceMeasure
  unitReferenceMeasure_lt_top : unitReferenceMeasure < ⊤
  signedAverage : Real

/-- The unconditional actual object. -/
def actualProductHaarData : ActualProductHaarData
    (l := l) places tuple mu := by
  classical
  refine
    { unitLog := arithmeticTupleHullUnitLogVolume places tuple
      unitLog_spec := arithmeticTupleHullUnitLogVolume_spec places tuple
      unitReferenceMeasure := mu (arithmeticTupleCanonicalUnitReference places tuple)
      unitReferenceMeasure_pos := ?_
      unitReferenceMeasure_lt_top := ?_
      signedAverage := (c3ThetaSignedProcession
        (sourceTheaterC3Signed (l := l) (V := V) (I := I) D)).average }
  · exact (measure_arithmeticTupleCanonicalRegions_pos_lt_top places tuple mu).2.1
  · exact (measure_arithmeticTupleCanonicalRegions_pos_lt_top places tuple mu).2.2

/-- Exact missing measure theorem: actual product unit log equals signed
/-- average minus unit-reference log. -/
def MissingSignedProductHaarMeasureTheorem : Prop :=
  (actualProductHaarData (l := l) (V := V) (I := I) places tuple mu (D := D)).unitLog =
    (actualProductHaarData (l := l) (V := V) (I := I) places tuple mu (D := D)).signedAverage -
      Real.log
        ((actualProductHaarData (l := l) (V := V) (I := I) places tuple mu (D := D)).unitReferenceMeasure.toReal)

/-- Construct the signed product-Haar object from the exact missing measure
/-- theorem; the object exists unconditionally as data, the signed identity
/-- only after this theorem. -/
def actualSignedProductHaarObject
    (h : MissingSignedProductHaarMeasureTheorem (l := l) (V := V) (I := I)
      places tuple mu D) :
    ActualProductHaarThetaObject (l := l) places tuple mu where
  unitLog := (actualProductHaarData (l := l) (V := V) (I := I) places tuple mu (D := D)).unitLog
  unitReferenceMeasure := (actualProductHaarData (l := l) (V := V) (I := I) places tuple mu (D := D)).unitReferenceMeasure
  unitReferenceMeasure_pos := (actualProductHaarData (l := l) (V := V) (I := I) places tuple mu (D := D)).unitReferenceMeasure_pos
  unitReferenceMeasure_lt_top := (actualProductHaarData (l := l) (V := V) (I := I) places tuple mu (D := D)).unitReferenceMeasure_lt_top
  signedAverage := (actualProductHaarData (l := l) (V := V) (I := I) places tuple mu (D := D)).signedAverage
  productHaarSpec := by
    have hspec := (actualProductHaarData (l := l) (V := V) (I := I) places tuple mu (D := D)).unitLog_spec
    rw [h] at hspec
    exact hspec


end LeanFormal.IUT.XiFPaper.SignedProductHaarUnconditional

end
