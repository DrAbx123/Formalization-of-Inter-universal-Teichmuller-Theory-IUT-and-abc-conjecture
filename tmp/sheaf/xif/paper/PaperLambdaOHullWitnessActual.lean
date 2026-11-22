import tmp.sheaf.xif.paper.PaperLambdaOHullHaarActual

/-!
# Unit-reference candidate and exact reverse gap for the unit lambda-O hull

Under the q-unit norm condition, the canonical unit reference O contains the
possible Theta image, hence O = 1 * O is an actual unit lambda-O candidate.
Therefore the lambda-O hull is contained in O.  The reverse inclusion is the
exact remaining candidate equality gap (hull = O); it is recorded, not assumed.

Haar finiteness of the hull follows unconditionally from hull subset O.
-/

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

noncomputable section
open scoped BigOperators Pointwise

namespace LeanFormal.IUT.XiFPaper.PaperLambdaOHullWitnessActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.PaperSourceGeometryActual
open LeanFormal.IUT.XiFPaper.PaperC3TensorGeometryActual
open LeanFormal.IUT.XiFPaper.PaperC3TensorBlockActual
open LeanFormal.IUT.XiFPaper.PaperLambdaOHullActual
open LeanFormal.IUT.XiFPaper.PaperLambdaOHullHaarActual
open MeasureTheory

universe u

variable {K : Type} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {l : PrimeGeFive}
variable {V : Type} [Fintype V]
variable (G : CompletionValuedSourceGeometry (l := l) (K := K) (p := p) V)
variable [MeasurableSpace (Block (G := G))]
variable [BorelSpace (Block (G := G))]
variable (mu : Measure (Block (G := G)))
variable [Measure.IsAddHaarMeasure mu]

/-- Under the q-unit norm condition, O is an actual unit lambda-O candidate. -/
theorem paperUnitReference_mem_lambdaOCandidates
    (hq : ∀ v : V,
      ‖(G.qUnit v : CommonPrimeCompletion (G.place v))‖ ≤ 1) :
    paperUnitReference (G := G) ∈ paperLambdaOCandidates (G := G) (l := l) := by
  refine ⟨1, ?_, ?_⟩
  · rw [paperLambdaOScaledRegion_eq_smul]
    simp
  · simpa [paperLambdaOScaledRegion] using
      paperQParameterImageSet_subset_unitReference_of_norm_le_one
        (G := G) (l := l) hq

/-- The unit lambda-O hull is contained in O. -/
theorem paperLambdaOHull_subset_unitReference
    (hq : ∀ v : V,
      ‖(G.qUnit v : CommonPrimeCompletion (G.place v))‖ ≤ 1) :
    paperLambdaOHull (G := G) (l := l) ⊆ paperUnitReference (G := G) := by
  exact paperLambdaOHull_subset_candidate (G := G) (l := l)
    (paperUnitReference (G := G))
    (paperUnitReference_mem_lambdaOCandidates (G := G) hq)

/-- Exact missing reverse inclusion: the hull equals O iff O is contained in the
hull. -/
def PaperLambdaOHullEqualsUnitReference (hq : ∀ v : V,
      ‖(G.qUnit v : CommonPrimeCompletion (G.place v))‖ ≤ 1) : Prop :=
  paperLambdaOHull (G := G) (l := l) = paperUnitReference (G := G)

/-- The exact reverse gap. -/
def PaperLambdaOHullReverseInclusionGap (hq : ∀ v : V,
      ‖(G.qUnit v : CommonPrimeCompletion (G.place v))‖ ≤ 1) : Prop :=
  paperUnitReference (G := G) ⊆ paperLambdaOHull (G := G) (l := l)

theorem paperLambdaOHullEqualsUnitReference_iff_reverse
    (hq : ∀ v : V,
      ‖(G.qUnit v : CommonPrimeCompletion (G.place v))‖ ≤ 1) :
    PaperLambdaOHullEqualsUnitReference (G := G) (l := l) hq ↔
      PaperLambdaOHullReverseInclusionGap (G := G) (l := l) hq := by
  constructor
  · intro h x hx
    rw [h]
    exact hx
  · intro h
    exact Set.Subset.antisymm
      (paperLambdaOHull_subset_unitReference (G := G) (l := l) hq) h

/-- Unconditional hull Haar finiteness from hull subset O. -/
theorem paperLambdaOHull_measure_lt_top
    (hq : ∀ v : V,
      ‖(G.qUnit v : CommonPrimeCompletion (G.place v))‖ ≤ 1) :
    mu (paperLambdaOHull (G := G) (l := l)) < ⊤ := by
  have hO := measure_arithmeticTupleCanonicalRegions_pos_lt_top
    (lambdaOPlaces (G := G)) (lambdaOTuple (V := V)) mu
  exact lt_of_le_of_lt
    (measure_mono (paperLambdaOHull_subset_unitReference (G := G) (l := l) hq))
    (by simpa [paperUnitReference, arithmeticTupleCanonicalUnitReference] using hO.2.2)

/-- Conditional actual equality witness for the hull candidate O. -/
noncomputable def paperLambdaOHullEqualsUnitReferenceData
    (hq : ∀ v : V,
      ‖(G.qUnit v : CommonPrimeCompletion (G.place v))‖ ≤ 1)
    (h : PaperLambdaOHullEqualsUnitReference (G := G) (l := l) hq) :
    PaperLambdaOHullCandidateGap (G := G) (l := l) where
  candidate := 1
  hull_eq_candidate := by
    rw [h]
    rw [paperLambdaOScaledRegion_eq_smul]
    simp

/-- Candidate O normalized log volume is zero. -/
theorem paperLambdaOCandidateLog_one :
    paperLambdaOCandidateLog (G := G) mu (1 : (Block (G := G))ˣ) = 0 := by
  unfold paperLambdaOCandidateLog
  rw [paperLambdaOScaledRegion_eq_smul]
  simpa using arithmeticTupleNormalizedLogVolume_canonicalUnitReference
    (lambdaOPlaces (G := G)) (lambdaOTuple (V := V)) mu

end LeanFormal.IUT.XiFPaper.PaperLambdaOHullWitnessActual

end