import tmp.sheaf.n8.closure.O4ConstructedHull
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceContractionWlogReduction
import Mathlib

/-!
# O4 hull identity: explicit value-layer counterexample

Under pointwise degree faithfulness of the source realization, the constant
scaling of exponent 1 lies in sourceScalingUnits and has positive log-degree.
Multiplying it by the zero-label theta-pilot image point (which is the unit of
the value point carrier) gives an explicit point of the actual source
holomorphic hull with strictly positive log-degree.  Therefore the via-images
identity (hull volume = image volume) fails.

The pointwise degree-faithfulness hypothesis is not a field of
SourceImageRealization; this is the exact obstruction if it cannot be supplied.
No arbitrary hull or readout is introduced.
-/

noncomputable section

open scoped BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.O4ConstructedHull

namespace LeanFormal.IUT.N8Closure.O4HullIdentityCounterexample

universe ua uv upi umon ui u v w

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
variable (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)

/-- The explicit constant scaling of exponent 1. -/
noncomputable def scalingUnit : I.ThetaPilotPoint v :=
  I.constantThetaPilotPoint v R (Multiplicative.ofAdd (1 : ℝ))

/-- The zero-label theta-pilot image point (the unit of the value point carrier). -/
noncomputable def imagePoint : I.ThetaPilotPoint v :=
  I.sourceThetaPilotPoint v R n (zeroSignedLabel (l := l))

/-- Explicit hull point: scaling times image. -/
noncomputable def hullPoint : I.ThetaPilotPoint v :=
  scalingUnit I v R * imagePoint I v R n

/-- The constant scaling lies in the source scaling units under pointwise
degree faithfulness. -/
theorem scalingUnit_mem_sourceScalingUnits
    (hdeg : ∀ b : ℝ,
      I.logDegreeAt 0 0 v (R.posRealAction (Multiplicative.ofAdd b)) = b) :
    scalingUnit I v R ∈ I.sourceScalingUnits v :=
  I.constantThetaPilotPoint_mem_sourceScalingUnits v R (a := 1) one_ne_zero hdeg

theorem scalingUnit_mem_hull
    (hdeg : ∀ b : ℝ,
      I.logDegreeAt 0 0 v (R.posRealAction (Multiplicative.ofAdd b)) = b) :
    scalingUnit I v R ∈
      (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)) :=
  I.sourceScalingUnits_subset_sourceHolomorphicHull v R n
    (scalingUnit_mem_sourceScalingUnits I v R hdeg)

theorem imagePoint_mem_hull :
    imagePoint I v R n ∈
      (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)) :=
  I.sourceThetaPilotPoint_mem_sourceHolomorphicHull v R n (zeroSignedLabel (l := l))

/-- The explicit hull point lies in the actual holomorphic hull. -/
theorem hullPoint_mem_hull
    (hdeg : ∀ b : ℝ,
      I.logDegreeAt 0 0 v (R.posRealAction (Multiplicative.ofAdd b)) = b) :
    hullPoint I v R n ∈
      (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)) :=
  I.sourceHolomorphicHull_scaling_mem v R n
    (scalingUnit_mem_sourceScalingUnits I v R hdeg)
    (imagePoint_mem_hull I v R n)

/-- The explicit hull point has strictly positive source log-degree. -/
theorem hullPoint_logDegree_pos
    (hdeg : ∀ b : ℝ,
      I.logDegreeAt 0 0 v (R.posRealAction (Multiplicative.ofAdd b)) = b) :
    0 < I.sourceLocalLogDegree v (hullPoint I v R n) := by
  unfold hullPoint scalingUnit imagePoint
  rw [I.sourceLocalLogDegree_mul]
  have hzero : I.sourceThetaPilotPoint v R n (zeroSignedLabel (l := l)) = 1 :=
    I.sourceThetaPilotPoint_zero_eq_one v R n
  rw [hzero, I.sourceLocalLogDegree_one]
  rw [I.sourceLocalLogDegree_constant v R 1 hdeg, mul_one]
  exact_mod_cast sourceVolumeIndex_card_pos l

/-- Decisive value-layer counterexample: under pointwise degree faithfulness,
the via-images identity fails. -/
theorem not_ViaImagesIdentity_of_degreeFaithful
    (hdeg : ∀ b : ℝ,
      I.logDegreeAt 0 0 v (R.posRealAction (Multiplicative.ofAdd b)) = b) :
    ¬ ViaImagesIdentity I v R n :=
  not_viaImagesIdentity_of_hullLogDegree_pos I v R n
    ⟨hullPoint I v R n, hullPoint_mem_hull I v R n hdeg,
      hullPoint_logDegree_pos I v R n hdeg⟩

/-- Exact obstruction: the construction needs pointwise degree faithfulness,
not provided as a field of SourceImageRealization. -/
def PointwiseDegreeFaithfulnessObstruction : Prop :=
  ∀ b : ℝ,
    I.logDegreeAt 0 0 v (R.posRealAction (Multiplicative.ofAdd b)) = b

end LeanFormal.IUT.N8Closure.O4HullIdentityCounterexample
