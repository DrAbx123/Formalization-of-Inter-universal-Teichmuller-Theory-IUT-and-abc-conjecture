import tmp.sheaf.n8.closure.C6ConstructedOutput
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedUnitScalingLogVolume
import Mathlib

/-!
# C6 actual ellOut <= Theta

Production has actual `arithmeticTupleNormalizedLogVolume_mono`.  For an actual
C6 source-allowed output, `B.normalizedLogVolume` is exactly
`arithmeticTupleNormalizedLogVolume` (rfl on the actual C6 data).  Therefore
`J.region ⊆ J.B.hull` (hullPoss) plus region positivity and hull finiteness
give `J.ellOut <= J.B.normalizedLogVolume J.B.hull`.  No arbitrary Theta/J.
-/

noncomputable section

open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.P6Comparison
open LeanFormal.IUT.N8Closure.C6ConstructedOutput
open LeanFormal.IUT.N8C6ActualIQ
open LeanFormal.IUT.NumberFieldFinitePlace
open ABCBridge.N8.C4Actual

namespace LeanFormal.IUT.N8Closure.C6ActualEllOutLeTheta

universe ua uv upi umon ui uL

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- The C6 normalized-log-volume field of an actual source-allowed output is
the production arithmetic tensor normalized log-volume. -/
def C6NormalizedLogVolumeActual (J : SourceAllowedOutput X) : Prop := by
  letI := J.measurableSpace
  letI := J.borelSpace
  letI := J.addHaar
  exact J.B.normalizedLogVolume =
    arithmeticTupleNormalizedLogVolume J.C3.tensorPlaces J.C3.tensorTuple J.mu

/-- Actual region positivity and hull finiteness, stated with the C6 instances. -/
def C6RegionPositiveFinite (J : SourceAllowedOutput X) : Prop := by
  letI := J.measurableSpace
  letI := J.borelSpace
  letI := J.addHaar
  exact 0 < J.mu J.region ∧ J.mu J.B.hull < ⊤

/-- Actual ellOut <= actual C6 Theta candidate from hullPoss, the actual C6
normalized-log-volume identity and the actual C6 region positivity/finiteness. -/
theorem actualEllOut_le_actualThetaCandidate
    (J : SourceAllowedOutput X)
    (hHull : J.hullPoss)
    (hB : C6NormalizedLogVolumeActual X J)
    (hPF : C6RegionPositiveFinite X J) :
    actualEllOut X J ≤ actualThetaCandidate X J := by
  letI := J.measurableSpace
  letI := J.borelSpace
  letI := J.addHaar
  have hB' : J.B.normalizedLogVolume =
      arithmeticTupleNormalizedLogVolume J.C3.tensorPlaces J.C3.tensorTuple J.mu := hB
  obtain ⟨hSpos, hTfin⟩ := hPF
  unfold actualEllOut actualThetaCandidate
  rw [show J.ellOut = J.B.normalizedLogVolume J.region from rfl, hB']
  exact arithmeticTupleNormalizedLogVolume_mono
    J.C3.tensorPlaces J.C3.tensorTuple J.mu hHull hSpos hTfin

/-- Actual C6 data fills B; its normalizedLogVolume is the arithmetic tensor
normalized log-volume by rfl. -/
theorem c6NormalizedLogVolumeActual_of_actual
    (P : P6BridgeDonors X) :
    C6NormalizedLogVolumeActual X (sourceAllowedOutputOfDonors X P) := by
  let J := sourceAllowedOutputOfDonors X P
  letI := J.measurableSpace
  letI := J.borelSpace
  letI := J.addHaar
  rfl

end LeanFormal.IUT.N8Closure.C6ActualEllOutLeTheta
