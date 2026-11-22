import tmp.sheaf.xif.paper.Mzk1StepProviderPrimeActual
import tmp.sheaf.xif.paper.Mzk1NestedInductionStepProviderActual
import tmp.sheaf.xif.paper.Mzk1P1MorphismInterfaceActual
import tmp.sheaf.xif.paper.Mzk1F0StepGeometryActual

/-!
# ShehddF4bStepProviderClosureActual — f4b -> StepProvider closure chain

Real closure contribution: the two previously separate StepProvider inputs are combined in
one conditional theorem.

* f4b (numMaxP/lex strict decrease of the f0 step target) is DISCHARGED by the compiled
  theorem Mzk1F0StepGeometryActual.f0StepTarget_measure_lt (itself from
  Mzk1NestedInductionActual.measure_stepSet_lt);
* f5 (Target transport back along f0) is DISCHARGED by the compiled theorem
  Mzk1NestedInductionStepProviderActual.stepTransport_of_goal, conditional on the named
  CVCompositionLawF (critical-value composition law).

Remaining named inputs: CVCompositionLawF and the geometric existence of the normalised
f0 with f0(beta) notin S' (analytic avoidance; see Mzk1StepProviderPrimeActual.StepProviderFixedBetaChoiceInput).
No sorry/axiom, no placeholder.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.ShehddF4bStepProviderClosureActual

open LeanFormal.IUT.XiFPaper.Mzk1NestedInductionStepProviderActual
open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1F0StepGeometryActual
open LeanFormal.IUT.XiFPaper.Mzk1NestedInductionActual
open LeanFormal.IUT.XiFPaper.PaperScopeLemma24Actual
open Polynomial

/-- **PROVED chain (f4b + f5 closure):** the f0 step target has strictly smaller
lexicographic (max degree, number of maximal points) measure, and the paper-scope target
transports back from S' (at beta' = f0(beta)) to S (at beta), conditional only on the
critical-value composition law. -/
theorem f4b_stepProvider_closure_chain
    (hcv : Mzk1NestedInductionStepProviderActual.CVCompositionLawF)
    (SF : Finset Qbar) (alpha0 : Qbar) (halpha0 : alpha0 ∈ SF)
    (hmax : degQ alpha0 = maxDeg SF) (h2 : 2 ≤ degQ alpha0)
    {S : Finset (P1Point (AlgebraicClosure ℚ))} {beta : P1Point (AlgebraicClosure ℚ)}
    {q : Polynomial (AlgebraicClosure ℚ)} {S' : Finset (P1Point (AlgebraicClosure ℚ))}
    (hqpos : 0 < q.natDegree)
    (hmap : ∀ p ∈ S, Mzk1NestedInductionStepProviderActual.f0Map q p ∈ S')
    (hcvS : ∀ z : AlgebraicClosure ℚ,
      Polynomial.aeval z (Polynomial.derivative q) = 0 →
        P1Point.ofFinite (Polynomial.aeval z q) ∈ S')
    (hgoal : PaperScopeLemma24Target S'
      (Mzk1NestedInductionStepProviderActual.f0Map q beta)) :
    Prod.Lex (· < ·) (· < ·)
        (maxDeg (Mzk1F0StepGeometryActual.f0StepTarget SF alpha0),
          numMax (Mzk1F0StepGeometryActual.f0StepTarget SF alpha0))
        (maxDeg SF, numMax SF) ∧
      PaperScopeLemma24Target S beta :=
  ⟨Mzk1F0StepGeometryActual.f0StepTarget_measure_lt SF alpha0 halpha0 hmax h2,
    Mzk1NestedInductionStepProviderActual.stepTransport_of_goal hcv hqpos hmap hcvS hgoal⟩

end LeanFormal.IUT.XiFPaper.ShehddF4bStepProviderClosureActual
end
