import tmp.sheaf.xif.paper.PaperLambdaOHullWitnessActual

/-!
# Reduction of the unit lambda-O reverse inclusion

The reverse inclusion O subset paperLambdaOHull is exactly: every actual
unit lambda-O candidate containing the image contains O.  This candidate-level
condition is not implied by the q-unit norm hypothesis alone.
-/

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

noncomputable section
open scoped BigOperators Pointwise

namespace LeanFormal.IUT.XiFPaper.PaperLambdaOHullReverseReductionActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.PaperSourceGeometryActual
open LeanFormal.IUT.XiFPaper.PaperC3TensorGeometryActual
open LeanFormal.IUT.XiFPaper.PaperC3TensorBlockActual
open LeanFormal.IUT.XiFPaper.PaperLambdaOHullActual
open LeanFormal.IUT.XiFPaper.PaperLambdaOHullWitnessActual
open MeasureTheory

universe u

variable {K : Type} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {l : PrimeGeFive}
variable {V : Type} [Fintype V]
variable (G : CompletionValuedSourceGeometry (l := l) (K := K) (p := p) V)

/-- Reverse inclusion is exactly containment of O in every unit-scaled
candidate. -/
theorem unitReference_subset_lambdaOHull_iff_forall_candidate
    :
    paperUnitReference (G := G) ⊆ paperLambdaOHull (G := G) (l := l) ↔
      ∀ H : Set (Block (G := G)),
        H ∈ paperLambdaOCandidates (G := G) (l := l) →
          paperUnitReference (G := G) ⊆ H := by
  constructor
  · intro h H hH
    exact h.trans (paperLambdaOHull_subset_candidate (G := G) (l := l) H hH)
  · intro h x hx
    simp only [paperLambdaOHull, Set.mem_iInter₂]
    intro H hH
    exact h H hH hx

end LeanFormal.IUT.XiFPaper.PaperLambdaOHullReverseReductionActual

end
