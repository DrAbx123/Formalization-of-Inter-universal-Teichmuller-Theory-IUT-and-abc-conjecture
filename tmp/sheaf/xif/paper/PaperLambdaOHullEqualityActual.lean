import tmp.sheaf.xif.paper.PaperLambdaOHullReverseReductionActual
import tmp.sheaf.xif.paper.PaperLambdaOHullWitnessActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceHolomorphicIntegralClosure

/-!
# Actual equality paperLambdaOHull = paperUnitReference

The j = 0 Theta image point is the identity.  Every unit lambda-O candidate
containing the image therefore contains the identity, hence has the form
u * o = 1 with o in O.  Since O is the integral closure, o * x is in O for
x in O, so O is contained in u * O.  Thus all candidates contain O and the
unit lambda-O hull equals O.  The hull log is then the canonical unit-reference
normalized log, which is zero.
-/

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

noncomputable section
open scoped BigOperators Pointwise

namespace LeanFormal.IUT.XiFPaper.PaperLambdaOHullEqualityActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.PaperSourceGeometryActual
open LeanFormal.IUT.XiFPaper.PaperC3TensorGeometryActual
open LeanFormal.IUT.XiFPaper.PaperC3TensorBlockActual
open LeanFormal.IUT.XiFPaper.PaperLambdaOHullActual
open LeanFormal.IUT.XiFPaper.PaperLambdaOHullHaarActual
open LeanFormal.IUT.XiFPaper.PaperLambdaOHullWitnessActual
open LeanFormal.IUT.XiFPaper.PaperLambdaOHullReverseReductionActual
open LeanFormal.IUT.Theorem311Source.OriginalInput
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
variable (hq : ∀ v : V,
  ‖(G.qUnit v : CommonPrimeCompletion (G.place v))‖ ≤ 1)

/-- The j=0 Theta image point is the identity of the tensor block. -/
theorem paperQParameterImagePoint_zero :
    paperQParameterImagePoint (G := G) (l := l) (LeanFormal.IUT.Theorem311Source.OriginalInput.zeroSignedLabel (l := l)) = 1 := by
  unfold paperQParameterImagePoint
  change arithmeticTupleTprod (fun v (_ : Unit) => G.place v) (fun _ => ())
    (fun v => (((G.qUnit v : G.valueCarrier v) ^
      (gaussExponent (LeanFormal.IUT.Theorem311Source.OriginalInput.zeroSignedLabel (l := l)).1).toNat) :
        CommonPrimeCompletion (G.place v))) = 1
  rw [LeanFormal.IUT.Theorem311Source.OriginalInput.zeroSignedLabel_val, gaussExponent_zero]
  exact arithmeticTupleTprod_one (fun v (_ : Unit) => G.place v) (fun _ => ())

/-- Every unit lambda-O candidate containing the image contains O. -/
theorem candidate_contains_unitReference
    (H : Set (Block (G := G)))
    (hH : H ∈ paperLambdaOCandidates (G := G) (l := l)) :
    paperUnitReference (G := G) ⊆ H := by
  rcases hH with ⟨u, hEq, hsub⟩
  have h1img : (1 : Block (G := G)) ∈
      paperQParameterImageSet (G := G) (l := l) := by
    exact ⟨LeanFormal.IUT.Theorem311Source.OriginalInput.zeroSignedLabel (l := l), paperQParameterImagePoint_zero (G := G)⟩
  have h1H : (1 : Block (G := G)) ∈ paperLambdaOScaledRegion (G := G) u := by
    rw [← hEq]
    exact hsub h1img
  rw [paperLambdaOScaledRegion_eq_smul] at h1H
  rcases Set.mem_smul_set.mp h1H with ⟨o, ho, h1o⟩
  intro x hx
  rw [hEq]
  rw [paperLambdaOScaledRegion_eq_smul]
  have hoI : o ∈ integralClosure ℤ_[p] (Block (G := G)) := by
    simpa [paperUnitReference, arithmeticTupleCanonicalUnitReference_eq_integralClosure] using ho
  have hxI : x ∈ integralClosure ℤ_[p] (Block (G := G)) := by
    simpa [paperUnitReference, arithmeticTupleCanonicalUnitReference_eq_integralClosure] using hx
  have hoxI : o * x ∈ integralClosure ℤ_[p] (Block (G := G)) :=
    (integralClosure ℤ_[p] (Block (G := G))).mul_mem hoI hxI
  refine Set.mem_smul_set.mpr ⟨o * x, ?_, ?_⟩
  · simpa [paperUnitReference, arithmeticTupleCanonicalUnitReference_eq_integralClosure] using hoxI
  · rw [smul_eq_mul]
    calc
      (u : Block (G := G)) * (o * x) = ((u : Block (G := G)) * o) * x := by ring
      _ = 1 * x := by rw [← h1o, smul_eq_mul]
      _ = x := one_mul x

/-- Actual reverse inclusion and equality hull = O. -/
theorem paperLambdaOHull_eq_unitReference (hq : ∀ v : V,
      ‖(G.qUnit v : CommonPrimeCompletion (G.place v))‖ ≤ 1) :
    paperLambdaOHull (G := G) (l := l) = paperUnitReference (G := G) := by
  apply Set.Subset.antisymm
  · exact paperLambdaOHull_subset_unitReference (G := G) (l := l) hq
  · rw [unitReference_subset_lambdaOHull_iff_forall_candidate (G := G) (l := l)]
    intro H hH
    exact candidate_contains_unitReference (G := G) H hH

/-- Actual candidate equality witness for O. -/
noncomputable def paperLambdaOHullEqualityData
    (hq : ∀ v : V,
      ‖(G.qUnit v : CommonPrimeCompletion (G.place v))‖ ≤ 1) :
    PaperLambdaOHullCandidateGap (G := G) (l := l) :=
  paperLambdaOHullEqualsUnitReferenceData (G := G) hq
    (by simpa [PaperLambdaOHullEqualsUnitReference]
      using paperLambdaOHull_eq_unitReference (G := G) (l := l) hq)

/-- Actual hull Haar positivity/finiteness. -/
theorem paperLambdaOHull_measure_pos_lt_top
    (hq : ∀ v : V,
      ‖(G.qUnit v : CommonPrimeCompletion (G.place v))‖ ≤ 1) :
    0 < mu (paperLambdaOHull (G := G) (l := l)) ∧
      mu (paperLambdaOHull (G := G) (l := l)) < ⊤ :=
  paperLambdaOHull_measure_pos_lt_top_of_candidate (G := G) mu
    (paperLambdaOHullEqualityData (G := G) hq)

/-- Actual hull normalized log is zero. -/
theorem paperLambdaOHullLog_eq_zero (hq : ∀ v : V,
      ‖(G.qUnit v : CommonPrimeCompletion (G.place v))‖ ≤ 1) :
    paperLambdaOHullLogOfCandidate (G := G) mu
      (paperLambdaOHullEqualityData (G := G) hq) = 0 := by
  unfold paperLambdaOHullLogOfCandidate paperLambdaOHullEqualityData
  unfold paperLambdaOHullEqualsUnitReferenceData
  exact paperLambdaOCandidateLog_one (G := G) mu

end LeanFormal.IUT.XiFPaper.PaperLambdaOHullEqualityActual

end