import tmp.sheaf.n8.closure.P6Comparison
import tmp.sheaf.n8.closure.C6ActualIQData
import tmp.sheaf.n8.closure.C6ActualIdentification
import tmp.sheaf.n8.closure.O4TargetAlignment
import tmp.sheaf.n8.closure.SourcePilotRegion
import tmp.sheaf.n8.closure.SourceThetaToIQ
import tmp.sheaf.n8.closure.SourceLogKummerRealization
import tmp.sheaf.n8.closure.N8NativeClosure
import Mathlib

/-!
# C6 constructed output / actual ellOut object

The source-allowed output J needs the old-chain source bridge and C2/C3/C4/T11
data; these are packaged explicitly as `P6BridgeDonors`.  The C6 part of J is
filled by the actual C6 data `C6ActualIQData.actual`, so J is not arbitrary.
The actual C6 ellOut object is `J.B.normalizedLogVolume J.region`.  The actual
C6 hull log inequality `iqInterface.logVolume region <= iqInterface.logVolume
hull` follows from hullPoss and the actual monotonicity field.  The
normalizedLogVolume analogue is not available (no monotonicity/identification);
that is the exact C6 no-go.  No arbitrary Theta/J.
-/

noncomputable section

open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.P6Comparison
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.SourceThetaToIQ
open LeanFormal.IUT.N8Closure.SourceLogKummerRealization
open LeanFormal.IUT.N8Closure.NativeClosure
open ABCBridge.N8.C4Actual
open LeanFormal.IUT.N8C6ActualIQ
open LeanFormal.IUT.NumberFieldFinitePlace

namespace LeanFormal.IUT.N8Closure.C6ConstructedOutput

universe ua uv upi umon ui uL

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- Explicit old-chain source donors needed to form a SourceAllowedOutput.
The C6 measure/data are not donors: they are filled by actual C6 data. -/
structure P6BridgeDonors where
  bridge : NativeOldC1Bridge X
  C2 : SourceLogKummerData bridge.input bridge.binding
  C3 : SourcePilotRegionData bridge.input
  D : SourceWitnessedOutputData bridge.input (PaperLabel l)
  T : SourceThetaIQInterface (I := bridge.input) C3
  measurableSpace : MeasurableSpace
    (ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple)
  borelSpace : BorelSpace
    (ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple)
  mu : Measure (ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple)
  addHaar : Measure.IsAddHaarMeasure mu
  n : ThetaPilotCarrier l
  x : bridge.input.ThetaPilotPoint D.place.v
  w : D.Witness n x

/-- Actual C6 data fills the C6 fields; the source donors fill only the
old-chain input/C2/C3/C4/T11/witness fields. -/
noncomputable def sourceAllowedOutputOfDonors (P : P6BridgeDonors X) :
    SourceAllowedOutput X := by
  letI := P.measurableSpace
  letI := P.borelSpace
  letI := P.addHaar
  exact
    { bridge := P.bridge
      C2 := P.C2
      C3 := P.C3
      D := P.D
      T := P.T
      measurableSpace := P.measurableSpace
      borelSpace := P.borelSpace
      mu := P.mu
      addHaar := P.addHaar
      B := C6ActualIQData.actual P.C3.tensorPlaces P.C3.tensorTuple P.mu
      n := P.n
      x := P.x
      w := P.w }

/-- Actual C6 ellOut value object. -/
noncomputable def actualEllOut (J : SourceAllowedOutput X) : ℝ := by
  letI := J.measurableSpace
  letI := J.borelSpace
  letI := J.addHaar
  exact J.ellOut

/-- Actual C6 Theta candidate: the C6 normalized hull readout. -/
noncomputable def actualThetaCandidate (J : SourceAllowedOutput X) : ℝ := by
  letI := J.measurableSpace
  letI := J.borelSpace
  letI := J.addHaar
  exact J.B.normalizedLogVolume J.B.hull

/-- Actual C6 hull log-volume (ENNReal iqInterface). -/
noncomputable def actualHullLogVolume (J : SourceAllowedOutput X) : ENNReal := by
  letI := J.measurableSpace
  letI := J.borelSpace
  letI := J.addHaar
  exact J.B.iqInterface.logVolume J.B.hull

/-- Actual C6 output-region log-volume (ENNReal iqInterface). -/
noncomputable def actualOutputLogVolume (J : SourceAllowedOutput X) : ENNReal := by
  letI := J.measurableSpace
  letI := J.borelSpace
  letI := J.addHaar
  exact J.B.iqInterface.logVolume J.region

/-- h <= Theta in the actual C6 hull-log sense: the output region is contained
in the hull (hullPoss), and the actual C6 iq logVolume is monotone. -/
theorem actualOutputLogVolume_le_hullLogVolume
    (J : SourceAllowedOutput X) (h : J.hullPoss) :
    actualOutputLogVolume X J ≤ actualHullLogVolume X J := by
  letI := J.measurableSpace
  letI := J.borelSpace
  letI := J.addHaar
  exact J.B.iqInterface.logVolume_mono h

end LeanFormal.IUT.N8Closure.C6ConstructedOutput
