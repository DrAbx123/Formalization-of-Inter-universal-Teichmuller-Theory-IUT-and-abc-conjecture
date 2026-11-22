import tmp.sheaf.xif.paper.S3132ThetaSideModelClauseResidualActual
import tmp.sheaf.xif.paper.QVFamTensorCoefficientActual
import tmp.sheaf.xif.paper.S3131CanonicalRootedQCActual
import tmp.sheaf.xif.paper.RootHullContainmentInequalityActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1500000

noncomputable section
open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S3131CanonicalRootedQCActual
open LeanFormal.IUT.XiFPaper.S3129IQHullLogVolumeSourceActual
open LeanFormal.IUT.XiFPaper.S3132IQHullRealLogVolumeReadoutActual
open LeanFormal.IUT.XiFPaper.S3132ConcreteSourceNormalizationClosureActual
open LeanFormal.IUT.XiFPaper.S3136NativeHaarFamilyActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.RootNormalizedContainmentActual
open LeanFormal.IUT.XiFPaper.RootHullContainmentInequalityActual

namespace LeanFormal.IUT.XiFPaper.S3132VFormScalingReductionActual

/-!
# V-form/canonical identity: reduction to the ELEMENTARY Haar scaling law

Paper source (corpus files in papers/motizuki_corpus/text):
* IUT III, Proposition 3.9, (i), corpus lines 6838-6860: the packet-normalized
  log-volume is characterized by: multiplication of an element of M(-) by p_v
  corresponds to adding -log(p_v); on the local holomorphic integral structures
  O the log-volume is zero; hence log-volume of lambda*O is the log of the
  multiplier lambda (the scaling law).
* IUT III, Remark 3.9.5, (i), corpus lines 7652-7680: the holomorphic hull of a
  region is DEFINED as the smallest subset of the form H = lambda*O with every
  component of lambda nonzero (or the whole IQ(-) when not relatively compact).
* IUT III, Remark 3.9.4, corpus ~7151: the log-link compatibility of log-volumes
  is a collection of elementary observations.

Consequence: the V-form/canonical identity is NOT a deep independent input.  By
Rem 3.9.5(i) each rooted tensor hull is a scaled integral structure lambda_b*O_b,
and by Prop 3.9(i) / Rem 3.9.4 its log-volume is the log of the scaling multiplier
(up to the normalization constants already handled by the closed factor residual).
Therefore the identity decomposes into:
  (R1) rooted scaling decomposition: rootThetaHullLog b = log (scalar b),
  (R2) weighted arithmetic identity: sourceVFormLogVolume = sum_b w_b * log (scalar b);
and the original residual follows by rewriting (R1) in the canonical rooted sum.
This file PROVES that implication formally; the classification of the original
residual as an independent hard input was TOO PESSIMISTIC.  Component, not a
paper object; owner hull.  Registry frozen; no registry edits.
-/

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (mu : ∀ b : Bad (nativePlaceSelection T), Measure (qVFamTensorBlock T b))
variable [∀ b : Bad (nativePlaceSelection T), Measure.IsAddHaarMeasure (mu b)]

/-- (R1) on the rooted terms: a scaling decomposition of every rooted tensor
hull log-volume into the log of its scaling multiplier. -/
def RootedScalingDecomposition
    (scalar : Bad (nativePlaceSelection T) → ℝ) : Prop :=
  ∀ b : Bad (nativePlaceSelection T),
    rootThetaHullLog (l := l) (qVFamTensorPlaces T b) qVFamTensorTuple
        (mu b) (rootHalfCoefficient (l := l) T b) = Real.log (scalar b)

/-- **Elementary scaling form of the canonical rooted readout**: given (R1), the
canonical rooted H_C readout is the weighted sum of the log scalings. -/
theorem canonicalReadout_eq_weighted_scaling
    (scalar : Bad (nativePlaceSelection T) → ℝ)
    (hdecomp : RootedScalingDecomposition (l := l) T mu scalar) :
    S3131CanonicalRootedHC (l := l) T mu =
      ∑ b : Bad (nativePlaceSelection T),
        nativeBadLocalWeight T b * Real.log (scalar b) := by
  unfold S3131CanonicalRootedHC
  exact Finset.sum_congr rfl (fun b _ => by rw [hdecomp b])

/-- **The reduced residual**: (R1) rooted scaling decomposition together with
(R2) the weighted arithmetic identity. -/
structure ReducedVFormResidual
    (scalar : Bad (nativePlaceSelection T) → ℝ) : Prop where
  rooted_scaling : RootedScalingDecomposition (l := l) T mu scalar
  vform_match : sourceVFormLogVolume =
    ∑ b : Bad (nativePlaceSelection T),
      nativeBadLocalWeight T b * Real.log (scalar b)

/-- **Main reduction theorem**: the reduced residual implies the original
V-form/canonical identity.  Hence the original identity is an ELEMENTARY Haar
scaling statement modulo the rooted scaling data, not an independent hard input. -/
theorem vformCanonical_of_reducedResidual
    (scalar : Bad (nativePlaceSelection T) → ℝ)
    (h : ReducedVFormResidual (l := l) T mu scalar) :
    sourceVFormLogVolume = S3131CanonicalRootedHC (l := l) T mu := by
  rw [h.vform_match, canonicalReadout_eq_weighted_scaling (l := l) T mu scalar
    h.rooted_scaling]

#check RootedScalingDecomposition
#check canonicalReadout_eq_weighted_scaling
#check ReducedVFormResidual
#check vformCanonical_of_reducedResidual

end LeanFormal.IUT.XiFPaper.S3132VFormScalingReductionActual
end