import tmp.sheaf.n8.closure.SourceWitnessedOutput
import tmp.sheaf.n8.closure.SourceThetaToIQ
import tmp.sheaf.n8.closure.C6ActualIQData
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceImageHull

set_option maxHeartbeats 400000
set_option relaxedAutoImplicit false

/-!
# C9 paper Values: actual output-region data

For each actual C4 output witness we associate the actual T11 theta-image
region over the C4 choice family, not a singleton, and read its actual C6
normalized log-volume.  `ValuesPaper` is the set of these actual region
readouts with provenance.  No free Real field and no singleton value.
-/

noncomputable section

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.NumberFieldFinitePlace
open MeasureTheory
open ABCBridge.N8.C4Actual
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.SourceThetaToIQ
open LeanFormal.IUT.N8C6ActualIQ

namespace LeanFormal.IUT.N8Closure.C9ValuesPaper

universe ua uv upi umon ui uL

variable {l : PrimeGeFive} {V : Type uv}
  {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
  {Label : Type uL} [Group Label]
  (C3 : SourcePilotRegionData (l := l) (V := V) I)
  (D : SourceWitnessedOutputData (l := l) (V := V) I Label)
  (T : SourceThetaIQInterface (I := I) C3)
  [MeasurableSpace (ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple)]
  [BorelSpace (ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple)]
  (mu : Measure (ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple))
  [Measure.IsAddHaarMeasure mu]
  (B : C6ActualIQData C3.tensorPlaces C3.tensorTuple mu)

/-- The actual output region associated to an actual C4 witness: the actual
T11 theta-image set over the C4 choice family at procession `n`. -/
def outputRegion (n : ThetaPilotCarrier l) (x : I.ThetaPilotPoint D.place.v)
    (_w : D.Witness n x) : Set (C6IQCarrier C3.tensorPlaces C3.tensorTuple) :=
  {y | ∃ c : D.Choice n x, y = T.thetaImage n c}

theorem outputRegion_nonempty (n : ThetaPilotCarrier l)
    (x : I.ThetaPilotPoint D.place.v) (w : D.Witness n x) :
    (outputRegion (I := I) C3 D T n x w).Nonempty := by
  refine ⟨T.thetaImage n zeroSignedLabel, ?_⟩
  exact ⟨zeroSignedLabel, rfl⟩

theorem outputRegion_contains_witness (n : ThetaPilotCarrier l)
    (x : I.ThetaPilotPoint D.place.v) (w : D.Witness n x) :
    T.thetaImage n w.1 ∈ outputRegion (I := I) C3 D T n x w :=
  ⟨w.1, rfl⟩

/-- The actual normalized log-volume readout of the output region, using the
actual C6 normalized log-volume donor. -/
def outputNormalizedLogVolume
    (n : ThetaPilotCarrier l) (x : I.ThetaPilotPoint D.place.v)
    (w : D.Witness n x) : ℝ :=
  B.normalizedLogVolume (outputRegion (I := I) C3 D T n x w)

theorem outputNormalizedLogVolume_eq (n : ThetaPilotCarrier l)
    (x : I.ThetaPilotPoint D.place.v) (w : D.Witness n x) :
    outputNormalizedLogVolume (I := I) C3 D T mu B n x w =
      B.normalizedLogVolume (outputRegion (I := I) C3 D T n x w) := rfl

/-- `ValuesPaper`: actual output-region normalized log-volumes, with the
actual C4 witness retained as provenance. -/
def ValuesPaper : Set ℝ :=
  {v | ∃ (n : ThetaPilotCarrier l) (x : I.ThetaPilotPoint D.place.v)
      (w : D.Witness n x),
      outputNormalizedLogVolume (I := I) C3 D T mu B n x w = v}

theorem mem_valuesPaper_iff (v : ℝ) :
    v ∈ ValuesPaper (I := I) C3 D T mu B ↔
      ∃ (n : ThetaPilotCarrier l) (x : I.ThetaPilotPoint D.place.v)
        (w : D.Witness n x),
        outputNormalizedLogVolume (I := I) C3 D T mu B n x w = v := by
  exact Iff.rfl

end LeanFormal.IUT.N8Closure.C9ValuesPaper

end
