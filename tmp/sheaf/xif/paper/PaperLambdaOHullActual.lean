import tmp.sheaf.xif.paper.PaperC3TensorBlockActual

/-! # Actual unit lambda-O hull on PaperC3TensorBlockActual.Block -/

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

noncomputable section
open scoped BigOperators

namespace LeanFormal.IUT.XiFPaper.PaperLambdaOHullActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.PaperSourceGeometryActual
open LeanFormal.IUT.XiFPaper.PaperC3TensorGeometryActual
open LeanFormal.IUT.XiFPaper.PaperC3TensorBlockActual

universe u

variable {K : Type} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {l : PrimeGeFive}
variable {V : Type} [Fintype V]
variable (G : CompletionValuedSourceGeometry (l := l) (K := K) (p := p) V)

/-- Actual unit scaling lambda-O region: (u : Block) * O. -/
noncomputable def paperLambdaOScaledRegion (u : (Block (G := G))ˣ) :
    Set (Block (G := G)) :=
  paperScaledRegion (G := G) (u : Block (G := G))

theorem paperLambdaOScaledRegion_eq (u : (Block (G := G))ˣ) :
    paperLambdaOScaledRegion (G := G) u =
      {x : Block (G := G) | ∃ o ∈ paperUnitReference (G := G),
        x = (u : Block (G := G)) * o} := rfl

def paperLambdaOCandidates : Set (Set (Block (G := G))) :=
  {H | ∃ u : (Block (G := G))ˣ,
    H = paperLambdaOScaledRegion (G := G) u ∧
    paperQParameterImageSet (G := G) (l := l) ⊆ H}

noncomputable def paperLambdaOHull : Set (Block (G := G)) :=
  ⋂ H ∈ paperLambdaOCandidates (G := G) (l := l), H

theorem paperQParameterImageSet_subset_lambdaOHull :
    paperQParameterImageSet (G := G) (l := l) ⊆
      paperLambdaOHull (G := G) (l := l) := by
  intro x hx
  simp only [paperLambdaOHull, Set.mem_iInter₂]
  intro H hH
  rcases hH with ⟨u, hEq, hsub⟩
  exact hsub hx

theorem paperLambdaOHull_subset_candidate
    (H : Set (Block (G := G)))
    (hH : H ∈ paperLambdaOCandidates (G := G) (l := l)) :
    paperLambdaOHull (G := G) (l := l) ⊆ H := by
  intro x hx
  simp only [paperLambdaOHull, Set.mem_iInter₂] at hx
  exact hx H hH

theorem paperLambdaOHull_subset_scaledRegion (u : (Block (G := G))ˣ)
    (hsub : paperQParameterImageSet (G := G) (l := l) ⊆
      paperLambdaOScaledRegion (G := G) u) :
    paperLambdaOHull (G := G) (l := l) ⊆
      paperLambdaOScaledRegion (G := G) u := by
  apply paperLambdaOHull_subset_candidate
  exact ⟨u, rfl, hsub⟩

theorem paperQParameterHull_subset_lambdaOHull :
    paperQParameterHull (G := G) (l := l) ⊆
      paperLambdaOHull (G := G) (l := l) := by
  intro x hx
  simp only [paperLambdaOHull, Set.mem_iInter₂]
  intro H hH
  rcases hH with ⟨u, hEq, hsub⟩
  have hu : (u : Block (G := G)) ≠ 0 := Units.ne_zero u
  rw [hEq] at hsub
  have hcand : paperLambdaOScaledRegion (G := G) u ∈
      paperCandidateHulls (G := G) (l := l) := by
    refine ⟨(u : Block (G := G)), hu, rfl, hsub⟩
  rw [hEq]
  exact paperQParameterHull_subset_candidate (G := G) (l := l)
    (p := p) (paperLambdaOScaledRegion (G := G) u) hcand hx

end LeanFormal.IUT.XiFPaper.PaperLambdaOHullActual

end