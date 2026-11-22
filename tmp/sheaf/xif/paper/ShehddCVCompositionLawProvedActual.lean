import tmp.sheaf.xif.paper.Mzk1NestedInductionStepProviderActual
import tmp.sheaf.xif.paper.Mzk1P1MorphismInterfaceActual

/-!
# ShehddCVCompositionLawProvedActual — critical-value composition law over Qbar

Real proof eliminating the named input `CVCompositionLawF` of the StepProvider minpoly
layer (Mzk1NestedInductionStepProviderActual): the chain rule for formal derivatives,
`derivative (r.comp q) = derivative q * (derivative r).comp q`, plus
`aeval z (p.comp q) = aeval (aeval z q) p`, gives the critical-value composition law over
the algebraic closure of Q.  Consequently the minpoly Target transport
(stepTransport_of_goal) no longer needs the CV law as a hypothesis.

No sorry/axiom; no placeholder.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.ShehddCVCompositionLawProvedActual

open Polynomial
open LeanFormal.IUT.XiFPaper.Mzk1NestedInductionStepProviderActual
open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual
open LeanFormal.IUT.XiFPaper.PaperScopeLemma24Actual

/-- **PROVED:** the critical-value composition law over the algebraic closure of Q: a
critical point of the composite is a critical point of the inner factor or maps to a
critical point of the outer factor.  Proof: chain rule + `mul_eq_zero` + `aeval_comp`. -/
theorem cvCompositionLawF_proved :
    Mzk1NestedInductionStepProviderActual.CVCompositionLawF := by
  intro q r z hz
  have hprod :
      Polynomial.aeval z (Polynomial.derivative q) *
          Polynomial.aeval z ((Polynomial.derivative r).comp q) = 0 := by
    rw [Polynomial.derivative_comp] at hz
    simpa using hz
  rcases mul_eq_zero.mp hprod with hinner | houter
  · exact Or.inl hinner
  · exact Or.inr (by rwa [Polynomial.aeval_comp] at houter)

/-- **PROVED (unconditional transport):** the minpoly Target transport along `f0` now
holds without the CV law hypothesis: it is supplied by `cvCompositionLawF_proved`. -/
theorem stepTransport_of_goal_unconditional
    {S : Finset (P1Point (AlgebraicClosure ℚ))}
    {beta : P1Point (AlgebraicClosure ℚ)}
    {q : Polynomial (AlgebraicClosure ℚ)}
    {S' : Finset (P1Point (AlgebraicClosure ℚ))}
    (hqpos : 0 < q.natDegree)
    (hmap : ∀ p ∈ S, Mzk1NestedInductionStepProviderActual.f0Map q p ∈ S')
    (hcvS : ∀ z : AlgebraicClosure ℚ,
      Polynomial.aeval z (Polynomial.derivative q) = 0 →
        P1Point.ofFinite (Polynomial.aeval z q) ∈ S')
    (hgoal : PaperScopeLemma24Target S'
      (Mzk1NestedInductionStepProviderActual.f0Map q beta)) :
    PaperScopeLemma24Target S beta :=
  Mzk1NestedInductionStepProviderActual.stepTransport_of_goal
    cvCompositionLawF_proved hqpos hmap hcvS hgoal

end LeanFormal.IUT.XiFPaper.ShehddCVCompositionLawProvedActual
end
