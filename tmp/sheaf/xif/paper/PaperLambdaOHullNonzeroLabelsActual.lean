import tmp.sheaf.xif.paper.PaperLambdaOHullWitnessActual
import tmp.sheaf.xif.paper.PaperLambdaOHullActual

/-!
# Unit lambda-O hull from nonzero Theta labels

Fig. 3.4 uses the nonzero Theta labels j = 1,...,l*; the zero label belongs to
the q-pilot, not the Theta image.  This file rebuilds the image/candidates/hull
using only nonzero signed labels, so the zero-label image point 1 is not used.
-/

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

noncomputable section
open scoped BigOperators Pointwise

namespace LeanFormal.IUT.XiFPaper.PaperLambdaOHullNonzeroLabelsActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.PaperSourceGeometryActual
open LeanFormal.IUT.XiFPaper.PaperC3TensorGeometryActual
open LeanFormal.IUT.XiFPaper.PaperC3TensorBlockActual
open LeanFormal.IUT.XiFPaper.PaperLambdaOHullActual
open LeanFormal.IUT.XiFPaper.PaperLambdaOHullWitnessActual

universe u

variable {K : Type} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {l : PrimeGeFive}
variable {V : Type} [Fintype V]
variable (G : CompletionValuedSourceGeometry (l := l) (K := K) (p := p) V)

/-- Unit-scaled region as a set smul of O. -/
theorem paperLambdaOScaledRegion_eq_smul (u : (Block (G := G))ˣ) :
    paperLambdaOScaledRegion (G := G) u =
      (u : Block (G := G)) • paperUnitReference (G := G) := by
  ext x
  constructor
  · rintro ⟨o, ho, rfl⟩
    exact ⟨o, ho, by simp [smul_eq_mul]⟩
  · rintro ⟨o, ho, rfl⟩
    exact ⟨o, ho, by simp [smul_eq_mul]⟩

/-- The actual q-parameter nonzero-label image set is the block's own
`paperQParameterNonzeroImageSet`; do not redefine a parallel local copy. -/
abbrev paperQParameterNonzeroImageSet : Set (Block (G := G)) :=
  PaperC3TensorBlockActual.paperQParameterNonzeroImageSet (G := G) (l := l)

/-- The nonzero-label image is contained in the full possible image. -/
theorem paperQParameterNonzeroImageSet_subset_possibleImage :
    paperQParameterNonzeroImageSet (G := G) (l := l) ⊆
      paperQParameterImageSet (G := G) (l := l) := by
  rintro x ⟨j, hj, rfl⟩
  exact ⟨j, rfl⟩

/-- Unit lambda-O candidates containing the nonzero-label image. -/
def paperNonzeroLambdaOCandidates : Set (Set (Block (G := G))) :=
  {H | ∃ u : (Block (G := G))ˣ,
    H = paperLambdaOScaledRegion (G := G) u ∧
    paperQParameterNonzeroImageSet (G := G) (l := l) ⊆ H}

/-- Actual nonzero-label unit lambda-O hull. -/
noncomputable def paperNonzeroLambdaOHull : Set (Block (G := G)) :=
  ⋂ H ∈ paperNonzeroLambdaOCandidates (G := G) (l := l), H

/-- The nonzero-label image is contained in its lambda-O hull. -/
theorem paperQParameterNonzeroImageSet_subset_hull :
    paperQParameterNonzeroImageSet (G := G) (l := l) ⊆
      paperNonzeroLambdaOHull (G := G) (l := l) := by
  intro x hx
  simp only [paperNonzeroLambdaOHull, Set.mem_iInter₂]
  intro H hH
  rcases hH with ⟨u, hEq, hsub⟩
  exact hsub hx

/-- The nonzero-label hull is contained in every nonzero-label candidate. -/
theorem paperNonzeroLambdaOHull_subset_candidate
    (H : Set (Block (G := G)))
    (hH : H ∈ paperNonzeroLambdaOCandidates (G := G) (l := l)) :
    paperNonzeroLambdaOHull (G := G) (l := l) ⊆ H := by
  intro x hx
  simp only [paperNonzeroLambdaOHull, Set.mem_iInter₂] at hx
  exact hx H hH

/-- Under the q-unit norm condition, O is a nonzero-label candidate. -/
theorem paperUnitReference_mem_nonzeroCandidates
    (hq : ∀ v : V,
      ‖(G.qUnit v : CommonPrimeCompletion (G.place v))‖ ≤ 1) :
    paperUnitReference (G := G) ∈ paperNonzeroLambdaOCandidates (G := G) (l := l) := by
  refine ⟨1, ?_, ?_⟩
  · rw [paperLambdaOScaledRegion_eq_smul]
    simp
  · exact (paperQParameterNonzeroImageSet_subset_possibleImage (G := G) (l := l)).trans
      (paperQParameterImageSet_subset_unitReference_of_norm_le_one (G := G) (l := l) hq)

/-- Nonzero-label hull is contained in O. -/
theorem paperNonzeroLambdaOHull_subset_unitReference
    (hq : ∀ v : V,
      ‖(G.qUnit v : CommonPrimeCompletion (G.place v))‖ ≤ 1) :
    paperNonzeroLambdaOHull (G := G) (l := l) ⊆ paperUnitReference (G := G) := by
  exact paperNonzeroLambdaOHull_subset_candidate (G := G) (l := l)
    (paperUnitReference (G := G))
    (paperUnitReference_mem_nonzeroCandidates (G := G) (l := l) hq)

/-- Exact reverse gap for the nonzero-label hull. -/
def PaperNonzeroLambdaOHullReverseGap
    (hq : ∀ v : V,
      ‖(G.qUnit v : CommonPrimeCompletion (G.place v))‖ ≤ 1) : Prop :=
  paperUnitReference (G := G) ⊆ paperNonzeroLambdaOHull (G := G) (l := l)

/-- Reverse gap is equivalent to all nonzero-label candidates containing O. -/
theorem paperNonzeroReverse_iff_forall_candidate
    (hq : ∀ v : V,
      ‖(G.qUnit v : CommonPrimeCompletion (G.place v))‖ ≤ 1) :
    PaperNonzeroLambdaOHullReverseGap (G := G) (l := l) hq ↔
      ∀ H : Set (Block (G := G)),
        H ∈ paperNonzeroLambdaOCandidates (G := G) (l := l) →
          paperUnitReference (G := G) ⊆ H := by
  constructor
  · intro h H hH
    exact h.trans (paperNonzeroLambdaOHull_subset_candidate (G := G) (l := l) H hH)
  · intro h x hx
    simp only [paperNonzeroLambdaOHull, Set.mem_iInter₂]
    intro H hH
    exact h H hH hx

end LeanFormal.IUT.XiFPaper.PaperLambdaOHullNonzeroLabelsActual

end