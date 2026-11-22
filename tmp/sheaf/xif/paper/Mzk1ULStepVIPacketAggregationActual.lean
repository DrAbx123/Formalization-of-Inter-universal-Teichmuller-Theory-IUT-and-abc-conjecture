/-
# U-C Step (viii) part (alpha): per-packet StepV procession bound and bad-place
# weighted aggregation

Route requirement (U-C Step(viii) narrowing, part (alpha)): the bad-place weighted
C1 sum is at most the bad-place weighted aggregate of the per-packet procession
averages.  This file supplies the two NEW pieces:

* processionVolume_le_s3014: per packet, the procession-averaged actual StepV
  volume is at most the paper's per-packet procession-average bound
  S3014ProcessionAverageBound.  This is david's accepted StepV consumer
  (Mzk1StepVProcessionActual.stepVProcessionAverage_bound) whose only input is the
  explicit named gap StepVExtraNonneg (0 <= different + log p + exceptional term);
* weighted_bad_sum_le: the weighted aggregation step (new): pointwise dominated
  per-packet bounds aggregate with nonnegative bad-place weights gamma
  (nativeBadLocalWeight), Finset.sum_le_sum + weight nonnegativity.

Subsequently, taking B_b := S3014ProcessionAverageBound(packet_b) and
s3014 := sum_b gamma_b * B_b, the equality (sum_b gamma_b * B_b) = s3014 is
definitional, so in Mzk1ULStepVIIIActual.hstepVIII_of_retained the (alpha) input
hB reduces to rfl and the only retained part of hvi is hviTable (beta, paper
letters).
-/
import tmp.sheaf.xif.paper.Mzk1StepVProcessionActual
import tmp.sheaf.xif.paper.Mzk1StepVExtraNonnegActual
import tmp.sheaf.xif.paper.S3014StepVProcessionAverageActual
import tmp.sheaf.xif.paper.Mzk1ULPacketBPerLabelBridgeActual
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1ULStepVIPacketAggregationActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1StepVProcessionActual
open LeanFormal.IUT.XiFPaper.S3014StepVProcessionAverageActual

universe u v w
variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {ι : Type v} [Fintype ι] {V : ι → Type w}
variable (places : (i : ι) → V i → FinitePlaceAtPrime K p)
variable (tuple : (i : ι) → V i) (istar : ι)
variable (jValue : CommonPrimeCompletion (places istar (tuple istar)))
variable (exceptional : Finset ι) (l n : Nat)

/-- (alpha) per packet: the procession-averaged actual StepV volume is at most the
per-packet paper procession-average bound.  Input: the explicit named StepV gap
StepVExtraNonneg (different + log p + exceptional >= 0). -/
theorem processionVolume_le_s3014
    (h : StepVExtraNonneg (p := p) places tuple exceptional) :
    (1 / (n : ℝ)) * (∑ label ∈ Finset.Icc 1 n,
        stepVVolume (p := p) places tuple istar jValue l label) ≤
      S3014ProcessionAverageBound places tuple istar jValue exceptional l n :=
  stepVProcessionAverage_bound (p := p) places tuple istar jValue exceptional l n h

/-- (alpha) UNCONDITIONAL per-packet form: the StepV extra-nonneg gap is proved
unconditionally in Mzk1StepVExtraNonnegActual (stepVExtraNonneg_actual), so the
per-packet procession bound needs no hypothesis. -/
theorem processionVolume_le_s3014_actual :
    (1 / (n : ℝ)) * (∑ label ∈ Finset.Icc 1 n,
        stepVVolume (p := p) places tuple istar jValue l label) ≤
      S3014ProcessionAverageBound places tuple istar jValue exceptional l n :=
  LeanFormal.IUT.XiFPaper.Mzk1StepVExtraNonnegActual.stepVProcessionAverage_bound_actual
    (p := p) places tuple istar jValue exceptional l n

/-- (alpha) weighted aggregation step (new): with nonnegative bad-place weights
gamma (nativeBadLocalWeight), pointwise dominated per-packet bounds aggregate. -/
theorem weighted_bad_sum_le {ι' : Type*} [Fintype ι'] (w V S : ι' → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hVS : ∀ i, V i ≤ S i) :
    (∑ i, w i * V i) ≤ ∑ i, w i * S i :=
  Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hVS i) (hw i)

/-- (alpha) with B_b := S3014ProcessionAverageBound at packet b and
s3014 := sum_b gamma_b * B_b, the aggregation equality is definitional. -/
theorem bad_sum_eq_weighted_aggregate {ι' : Type*} [Fintype ι'] (w B : ι' → ℝ) :
    (∑ i, w i * B i) = ∑ i, w i * B i := rfl

#print axioms processionVolume_le_s3014
#print axioms processionVolume_le_s3014_actual
#print axioms weighted_bad_sum_le
#print axioms bad_sum_eq_weighted_aggregate

end LeanFormal.IUT.XiFPaper.Mzk1ULStepVIPacketAggregationActual
end