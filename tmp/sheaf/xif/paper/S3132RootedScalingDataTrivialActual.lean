import tmp.sheaf.xif.paper.S3132VFormScalingReductionActual
import Mathlib.Analysis.SpecialFunctions.Log.Basic

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
open LeanFormal.IUT.XiFPaper.S3136ModelSourceClauseActual
open LeanFormal.IUT.XiFPaper.S3132VFormScalingReductionActual

namespace LeanFormal.IUT.XiFPaper.S3132RootedScalingDataTrivialActual

/-!
# RootedScalingDecomposition: the log/exp construction (R1 is content-free)

On the concrete source side, the rooted scaling decomposition (R1) is not an
extra hypothesis: for every real rooted log-volume x there is a scalar
exp(x) whose log is x.  Constructing the rooted scaling data with
scalar b := Real.exp (rootThetaHullLog b) gives R1 UNCONDITIONALLY, and
therefore the reduced residual is EXACTLY the weighted rooted identity (R2):
  sourceVFormLogVolume = sum_b nativeBadLocalWeight b * rootThetaHullLog b.
The original V-form/canonical identity is thus equivalent to (R2) alone.
Component, not a paper object; owner hull.
-/

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (mu : ∀ b : Bad (nativePlaceSelection T), Measure (qVFamTensorBlock T b))
variable [∀ b : Bad (nativePlaceSelection T), Measure.IsAddHaarMeasure (mu b)]

/-- The exp-based scalar family: log of this scalar is the rooted log-volume. -/
noncomputable def logExpScalar : Bad (nativePlaceSelection T) → ℝ :=
  fun b => Real.exp (rootThetaHullLog (l := l) (qVFamTensorPlaces T b)
    qVFamTensorTuple (mu b) (rootHalfCoefficient (l := l) T b))

/-- **R1 holds unconditionally** for the exp-based scalar family. -/
theorem rootedScalingData_logExpScalar :
    RootedScalingDecomposition T mu (logExpScalar T mu) := by
  intro b
  unfold logExpScalar
  exact (Real.log_exp _).symm

/-- **Canonical rooted readout as the weighted rooted log-volume sum** (R1
instantiated, unconditionally). -/
theorem canonicalReadout_eq_weightedRootedLog :
    S3131CanonicalRootedHC (l := l) T mu =
      ∑ b : Bad (nativePlaceSelection T),
        nativeBadLocalWeight T b *
          rootThetaHullLog (l := l) (qVFamTensorPlaces T b) qVFamTensorTuple
            (mu b) (rootHalfCoefficient (l := l) T b) := by
  rw [canonicalReadout_eq_weighted_scaling T mu
    (logExpScalar T mu) (rootedScalingData_logExpScalar T mu)]
  apply Finset.sum_congr rfl
  intro b _
  unfold logExpScalar
  rw [Real.log_exp]

/-- The weighted rooted identity (R2): the sharp arithmetic residual. -/
def WeightedRootedIdentity : Prop :=
  sourceVFormLogVolume =
    ∑ b : Bad (nativePlaceSelection T),
      nativeBadLocalWeight T b *
        rootThetaHullLog (l := l) (qVFamTensorPlaces T b) qVFamTensorTuple
          (mu b) (rootHalfCoefficient (l := l) T b)

/-- **The reduced residual is EXACTLY the weighted identity** (R1 is free). -/
theorem reducedResidual_iff_weightedIdentity :
    ReducedVFormResidual T mu (logExpScalar T mu) ↔
      WeightedRootedIdentity T mu := by
  constructor
  · intro h
    have hm := h.vform_match
    simpa [WeightedRootedIdentity, logExpScalar, Real.log_exp] using hm
  · intro h
    refine ⟨?rooted_scaling, ?vform_match⟩
    · exact rootedScalingData_logExpScalar T mu
    · simpa [WeightedRootedIdentity, logExpScalar, Real.log_exp] using h

/-- **The weighted identity alone yields the original V-form/canonical identity.** -/
theorem vformCanonical_of_weightedIdentity
    (h : WeightedRootedIdentity T mu) :
    sourceVFormLogVolume = S3131CanonicalRootedHC (l := l) T mu := by
  rw [canonicalReadout_eq_weightedRootedLog T mu]
  exact h

#check logExpScalar
#check rootedScalingData_logExpScalar
#check canonicalReadout_eq_weightedRootedLog
#check WeightedRootedIdentity
#check reducedResidual_iff_weightedIdentity
#check vformCanonical_of_weightedIdentity

end LeanFormal.IUT.XiFPaper.S3132RootedScalingDataTrivialActual
end