import tmp.sheaf.xif.paper.PaperLambdaOHullNonzeroLabelsActual
import tmp.sheaf.xif.paper.SignedLabelOneActual

/-!
# qUnit tensor lambda candidate and the nonzero-label hull

The actual qUnit tensor lambda is an actual unit-lambda-O candidate for the
nonzero Theta image.  Hence the nonzero-label lambda-O hull is contained in the
qUnit lambda-O region.  The qUnit lambda is integral under the unit-norm
condition, so its lambda-O region is contained in O.  Strictness (lambda-O
smaller than O) is recorded as an exact gap; no fake strictness is asserted.
-/

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

noncomputable section
open scoped BigOperators Pointwise

namespace LeanFormal.IUT.XiFPaper.PaperLambdaOHullQVFamilyActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.PaperSourceGeometryActual
open LeanFormal.IUT.XiFPaper.PaperC3TensorGeometryActual
open LeanFormal.IUT.XiFPaper.PaperC3TensorBlockActual
open LeanFormal.IUT.XiFPaper.PaperLambdaOHullActual
open LeanFormal.IUT.XiFPaper.PaperLambdaOHullNonzeroLabelsActual
open LeanFormal.IUT.XiFPaper.SignedLabelOneActual

universe u

variable {K : Type} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {l : PrimeGeFive}
variable {V : Type} [Fintype V]
variable (G : CompletionValuedSourceGeometry (l := l) (K := K) (p := p) V)

/-- The qUnit tensor lambda is a nonzero-label lambda-O candidate. -/
theorem qParameterUnitLambda_mem_nonzeroCandidates
    (hq : ∀ v : V,
      ‖(G.qUnit v : CommonPrimeCompletion (G.place v))‖ ≤ 1) :
    qParameterUnitLambdaHull (G := G) ∈
      paperNonzeroLambdaOCandidates (G := G) (l := l) := by
  refine ⟨qParameterUnitLambdaUnit (G := G), ?_, ?_⟩
  · change paperScaledRegion (G := G) (qParameterUnitLambda (G := G)) =
      paperLambdaOScaledRegion (G := G) (qParameterUnitLambdaUnit (G := G))
    rfl
  · rw [qParameterUnitLambdaHull]
    exact paperQParameterNonzeroImageSet_subset_qParameterUnitLambdaRegion (G := G) (l := l) hq

/-- The nonzero-label lambda-O hull is contained in the qUnit lambda-O region. -/
theorem paperNonzeroLambdaOHull_subset_qUnitLambdaHull
    (hq : ∀ v : V,
      ‖(G.qUnit v : CommonPrimeCompletion (G.place v))‖ ≤ 1) :
    paperNonzeroLambdaOHull (G := G) (l := l) ⊆
      qParameterUnitLambdaHull (G := G) :=
  paperNonzeroLambdaOHull_subset_candidate (G := G) (l := l)
    (qParameterUnitLambdaHull (G := G))
    (qParameterUnitLambda_mem_nonzeroCandidates (G := G) (l := l) hq)

/-- The qUnit lambda scaled image point at label 1 is the identity. -/
theorem qParameterUnitScaledImagePoint_one_eq :
    qParameterUnitScaledImagePoint (G := G) (l := l) (oneLabel l) (by
      rw [gaussExponent_oneLabel]) = 1 := by
  simp only [qParameterUnitScaledImagePoint, paperQUnitScaledImagePoint,
    gaussExponent_oneLabel, Nat.sub_self, pow_zero]
  exact arithmeticTupleTprod_one (fun v (_ : Unit) => G.place v) (fun _ => ())

/-- The qUnit tensor lambda is the label-1 Theta image point. -/
theorem qParameterUnitLambda_eq_thetaImagePoint_one
    (hq : ∀ v : V,
      ‖(G.qUnit v : CommonPrimeCompletion (G.place v))‖ ≤ 1) :
    qParameterUnitLambda (G := G) =
      paperQParameterImagePoint (G := G) (l := l) (oneLabel l) := by
  have h := paperQParameterImagePoint_eq_qUnitLambda_mul (G := G) (l := l)
    (oneLabel l) (by rw [gaussExponent_oneLabel])
  have h' : paperQParameterImagePoint (G := G) (l := l) (oneLabel l) =
      qParameterUnitLambda (G := G) *
        qParameterUnitScaledImagePoint (G := G) (l := l) (oneLabel l)
          (by rw [gaussExponent_oneLabel]) := by
    simpa [qParameterUnitLambda, qParameterUnitScaledImagePoint] using h
  rw [qParameterUnitScaledImagePoint_one_eq (G := G)] at h'
  simpa using h'.symm

/-- The qUnit tensor lambda lies in O under the unit-norm condition. -/
theorem qParameterUnitLambda_mem_unitReference
    (hq : ∀ v : V,
      ‖(G.qUnit v : CommonPrimeCompletion (G.place v))‖ ≤ 1) :
    qParameterUnitLambda (G := G) ∈ paperUnitReference (G := G) := by
  rw [qParameterUnitLambda_eq_thetaImagePoint_one (G := G) (l := l) hq]
  exact paperQParameterImagePoint_mem_unitReference_of_norm_le_one
    (G := G) (l := l) hq (oneLabel l)

/-- The qUnit lambda-O region is contained in O. -/
theorem qParameterUnitLambdaHull_subset_unitReference
    (hq : ∀ v : V,
      ‖(G.qUnit v : CommonPrimeCompletion (G.place v))‖ ≤ 1) :
    qParameterUnitLambdaHull (G := G) ⊆ paperUnitReference (G := G) := by
  intro x hx
  rcases hx with ⟨o, ho, rfl⟩
  have hlam : qParameterUnitLambda (G := G) ∈ integralClosure ℤ_[p] (Block (G := G)) := by
    simpa [paperUnitReference, arithmeticTupleCanonicalUnitReference_eq_integralClosure]
      using qParameterUnitLambda_mem_unitReference (G := G) (l := l) hq
  have hoI : o ∈ integralClosure ℤ_[p] (Block (G := G)) := by
    simpa [paperUnitReference, arithmeticTupleCanonicalUnitReference_eq_integralClosure]
      using ho
  have hmul : qParameterUnitLambda (G := G) * o ∈
      integralClosure ℤ_[p] (Block (G := G)) :=
    (integralClosure ℤ_[p] (Block (G := G))).mul_mem hlam hoI
  simpa [paperUnitReference, arithmeticTupleCanonicalUnitReference_eq_integralClosure]
    using hmul

/-- Exact strictness gap: the qUnit lambda-O region may be strictly smaller than O. -/
def PaperQUnitLambdaStrictnessGap
    (hq : ∀ v : V,
      ‖(G.qUnit v : CommonPrimeCompletion (G.place v))‖ ≤ 1) : Prop :=
  qParameterUnitLambdaHull (G := G) ≠ paperUnitReference (G := G)

/-- Equality of the qUnit region and O is the reverse inclusion. -/
theorem qParameterUnitLambdaHull_eq_unitReference_iff
    (hq : ∀ v : V,
      ‖(G.qUnit v : CommonPrimeCompletion (G.place v))‖ ≤ 1) :
    qParameterUnitLambdaHull (G := G) = paperUnitReference (G := G) ↔
      paperUnitReference (G := G) ⊆ qParameterUnitLambdaHull (G := G) := by
  constructor
  · intro h
    rw [h]
  · intro h
    exact Set.Subset.antisymm
      (qParameterUnitLambdaHull_subset_unitReference (G := G) (l := l) hq) h

end LeanFormal.IUT.XiFPaper.PaperLambdaOHullQVFamilyActual

end
