import tmp.sheaf.xif.paper.S1076RootStackPaperThetaHullMeasureActual
import tmp.sheaf.xif.paper.S824RootStackyHaarVolumeActual

/-! # S1079: root-stack ambient Haar / carrier audit

rootStackPaperThetaHull is the image of the logical lambda-O region under
rootStackEmbedding : qVFamTensorBlock -> rootStackExtension.  The embedding
lands in a proper closed subfield (the L-stalk), not in an open subset of the
ambient L(mu_2l).  Hence the ambient additive Haar rootStackHaar can give
measure zero on the transported hull, and S1076's positivity condition is
genuinely not derivable from compactness/closedness.

Dichotomy:
* if the embedding range is full, the image is open and ambient positivity
  follows;
* if the range is proper, the ambient Haar is the wrong measure; the correct
  measure is the pushforward of the qVFam-block Haar along the embedding
  (equivalently the L-stalk/S824 stacky measure), not ambient L(mu) Haar.

This file records the exact obstruction and the corrected measure type; no
fake positivity. -/

noncomputable section
open scoped BigOperators TensorProduct Topology
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 12000000

namespace LeanFormal.IUT.XiFPaper.S1079RootStackMeasureAuditActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamRootFactorCorrectionActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
open LeanFormal.IUT.XiFPaper.S793PaperLeastLambdaOHullActual
open LeanFormal.IUT.XiFPaper.S1073RootStackPaperThetaHullActual
open LeanFormal.IUT.XiFPaper.S1076RootStackPaperThetaHullMeasureActual
open LeanFormal.IUT.XiFPaper.S824RootStackyHaarVolumeActual
open LeanFormal.IUT.XiFPaper.S782FiniteRootStackExtensionActual
open MeasureTheory Topology

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-- The root-stack hull lies in the range of the root-stack embedding. -/
theorem s1079Hull_subset_range :
    rootStackPaperThetaHull (l := l) T b ⊆
      Set.range (rootStackEmbedding (l := l) T b) := by
  intro x hx
  rw [rootStackPaperThetaHull] at hx
  rcases hx with ⟨y, _, rfl⟩
  exact ⟨y, rfl⟩

/-- Exact full-range condition: the embedding is surjective.  If true, its
image is open and ambient positivity follows from S1076. -/
def S1079RangeFull : Prop :=
  Set.range (rootStackEmbedding (l := l) T b) = Set.univ

/-- Exact proper-range obstruction: ambient Haar is the wrong measure when the
embedding image is a proper closed subspace. -/
def S1079RangeProper : Prop :=
  Set.range (rootStackEmbedding (l := l) T b) ≠ Set.univ

/-- Corrected measure: pushforward of the qVFam-block Haar along the
root-stack embedding (L-stalk measure).  This avoids the ambient proper-subspace
zero-measure issue. -/
noncomputable def s1079HaarOnRange : Measure (rootStackExtension T b) :=
  Measure.map (rootStackEmbedding (l := l) T b)
    (Measure.addHaar : Measure (qVFamTensorBlock T b))

/-- Exact positivity target for the corrected (pushforward) measure. -/
def S1079CorrectedPositivity : Prop :=
  0 < s1079HaarOnRange (l := l) T b
    (rootStackPaperThetaHull (l := l) T b)

/-- Exact minimal obstruction record: either the embedding range is full
(ambient Haar is correct) or proper (ambient Haar is wrong; corrected measure
is required). -/
def S1079ExactMeasureDichotomy : Prop :=
  S1079RangeFull (l := l) T b ∨ S1079RangeProper (l := l) T b

end LeanFormal.IUT.XiFPaper.S1079RootStackMeasureAuditActual

end
