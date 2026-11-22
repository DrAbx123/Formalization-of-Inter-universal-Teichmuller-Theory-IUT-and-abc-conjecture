import tmp.sheaf.n8.closure.C6C7C8NamedClosure
import tmp.sheaf.n8.closure.C7UToIQProof
import tmp.sheaf.n8.closure.C8DegreeActual

set_option maxHeartbeats 800000
set_option relaxedAutoImplicit false

/-!
# Wave2 actual C7/C8 attempt

The actual C7 U-to-IQ map and q-pilot hull membership cannot currently be
constructed from the existing actual data: `C7UToIQProof` records their exact
targets with named sorries, and the weak constant `SourceUToIQDonor` does not
satisfy `eval_compat` for a nonconstant `T.thetaImage`.  The C8 Ob3-3
comparison remains the named gap of `C8DegreeActual`.

This file packages the exact attempted objects and the no-go reduction.  It
does not introduce a weak constant map, a free map, or a new comparison
assumption.
-/

noncomputable section

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open MeasureTheory
open ABCBridge.N8.C4Actual
open ABCBridge.N8.C7Actual
open LeanFormal.IUT.N8C6ActualIQ
open LeanFormal.IUT.N8C6.PaperNormalizedVolume
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.SourceThetaToIQ
open LeanFormal.IUT.N8Closure.C7UToIQProof
open LeanFormal.IUT.N8Closure.C8DegreeActual

namespace LeanFormal.IUT.N8Closure.C7C8ActualAttempt

universe ua uv upi umon ui uL uG

variable {l : PrimeGeFive} {V : Type uv}
  {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
  {LAdd : Type uG} [AddGroup LAdd]
  (C3 : SourcePilotRegionData (l := l) (V := V) I)
  (D : SourceWitnessedOutputData (l := l) (V := V) I (Multiplicative LAdd))
  (T : SourceThetaIQInterface (I := I) C3)
  [MeasurableSpace (ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple)]
  [BorelSpace (ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple)]
  (mu : Measure (ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple))
  [Measure.IsAddHaarMeasure mu]
  (n : ThetaPilotCarrier l) (x : I.ThetaPilotPoint D.place.v)

/-- Exact attempted C7 objects at one output state: the actual U-to-IQ map and
the actual q-pilot hull membership. -/
structure ActualC7AtState where
  /-- The exact actual U-to-IQ map target. -/
  uToIQ : ActualSourceUToIQMap (C3 := C3) (D := D) (T := T) (n := n) (x := x)
  /-- The exact actual q-pilot hull membership. -/
  qPilot_mem : ActualQPilotHullMembership (C3 := C3)

/-- Exact C8 Ob3-3 attempted comparison at the C6 IQ hull. -/
structure ActualC8Ob33 (C6 : PaperNormalizedVolumeData C3.tensorPlaces C3.tensorTuple mu)
    (B : C6ActualIQData C3.tensorPlaces C3.tensorTuple mu) : Prop where
  degree_eq : actualArithmeticDegree C6 = B.normalizedLogVolume B.hull

end LeanFormal.IUT.N8Closure.C7C8ActualAttempt

end