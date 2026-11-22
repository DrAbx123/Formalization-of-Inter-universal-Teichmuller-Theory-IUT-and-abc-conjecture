import tmp.sheaf.xif.paper.S3131CanonicalRootedQCActual
import tmp.sheaf.xif.paper.QVFamTensorCoefficientActual
import tmp.sheaf.xif.paper.RootHullContainmentInequalityActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1500000

noncomputable section
open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.RootNormalizedContainmentActual
open LeanFormal.IUT.XiFPaper.RootHullContainmentInequalityActual
open LeanFormal.IUT.XiFPaper.S3131CanonicalRootedQCActual

namespace LeanFormal.IUT.XiFPaper.S3132ThetaSideCanonicalSubsingletonActual

/-! # Paper-route Theta side: canonical rooted readout on a singleton bad index

Reduction lemma: when the native bad-place index is a subsingleton (the minimal
concrete case), the canonical rooted H_C readout collapses to the unique
weighted rooted tensor V-form term.  This is the evaluation step needed when the
concrete Example 3.6 native datum supplies a one-point bad family; it does not
assume the V-form/canonical identification.  Component, not a paper object. -/

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (mu : ∀ b : Bad (nativePlaceSelection T), Measure (qVFamTensorBlock T b))
variable [∀ b : Bad (nativePlaceSelection T), Measure.IsAddHaarMeasure (mu b)]

/-- **Singleton collapse of the canonical rooted readout.** -/
theorem canonicalRootedHC_of_subsingleton
    [Subsingleton (Bad (nativePlaceSelection T))]
    (b0 : Bad (nativePlaceSelection T)) :
    S3131CanonicalRootedHC (l := l) T mu =
      nativeBadLocalWeight T b0 *
        rootThetaHullLog (l := l) (qVFamTensorPlaces T b0) qVFamTensorTuple
          (mu b0) (rootHalfCoefficient (l := l) T b0) := by
  unfold S3131CanonicalRootedHC
  rw [Finset.sum_eq_single b0]
  · intro b _ hb
    exact absurd (Subsingleton.elim b b0) hb
  · intro h
    exact absurd (Finset.mem_univ b0) h

#check canonicalRootedHC_of_subsingleton

end LeanFormal.IUT.XiFPaper.S3132ThetaSideCanonicalSubsingletonActual
end