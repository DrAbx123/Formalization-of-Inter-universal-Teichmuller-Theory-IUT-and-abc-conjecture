import tmp.sheaf.xif.paper.RestatedLemma24InterfaceActual
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

noncomputable section

/-!
# STEP 0 prior-art: CVCompositionLawStatement|SpecialSetPreservationStatement -> hits RestatedLemma24InterfaceActual (defs: criticalValuesOverC : Set ℂ, polyEvalP1, CVCompositionLawStatement, SpecialSetPreservationStatement) + hull helpers (critValues_comp_subset union form; same mathematical content) -> ADAPT (direct proof against abc's definitions; no bridge needed).

# Mzk1Lemma24CVLawProofActual — proves abc's CV composition law + special-set preservation

Unblocks abc's RestatedLemma24InductionActual.s3135_CVInvariant_comp: the statement
CVCompositionLawStatement becomes a theorem.  CV is abc's `criticalValuesOverC`
(Set ℂ, aeval at ℂ over ℚ-polynomials).  Registry frozen 14041.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1Lemma24CVLawProofActual

open Polynomial
open LeanFormal.IUT.XiFPaper.RestatedLemma24InterfaceActual

/-- **(1) CV composition law** for abc's restated 2.4 interface:
CV(r.comp q) ⊆ (aeval(-) r) '' CV(q) ∪ CV(r). -/
theorem cvCompositionLaw : RestatedLemma24InterfaceActual.CVCompositionLawStatement := by
  intro q r
  rintro c ⟨x, hx, hc⟩
  rcases hc with ⟨hz, hval⟩
  rw [Polynomial.natDegree_comp] at hx
  obtain ⟨hrne, hqne⟩ := Nat.mul_ne_zero_iff.mp hx
  have hderiv : Polynomial.aeval x (Polynomial.derivative (r.comp q)) =
      Polynomial.aeval x (Polynomial.derivative q) *
        Polynomial.aeval (Polynomial.aeval x q) (Polynomial.derivative r) := by
    rw [Polynomial.derivative_comp]
    rw [map_mul, Polynomial.aeval_comp]
  rw [hderiv] at hz
  rcases mul_eq_zero.mp hz with hq | hr
  · -- q' vanishes at x: c = aeval (q x) r with x a critical point of q
    refine Or.inl ⟨Polynomial.aeval x q, ⟨x, hqne, hq, rfl⟩, ?_⟩
    show Polynomial.aeval (Polynomial.aeval x q) r = c
    rw [← Polynomial.aeval_comp]
    exact hval
  · -- r' vanishes at q(x): c is a critical value of r
    refine Or.inr ⟨Polynomial.aeval x q, hrne, hr, ?_⟩
    show Polynomial.aeval (Polynomial.aeval x q) r = c
    rw [← Polynomial.aeval_comp]
    exact hval

/-- **(2) Special-set preservation** for abc's restated 2.4 interface: a polynomial
taking 0 and 1 into {0,1} takes all of {0,1} into {0,1}. -/
theorem specialSetPreservation : RestatedLemma24InterfaceActual.SpecialSetPreservationStatement := by
  intro r h0 h1 c hc
  rcases hc with h | h
  · rw [h]; exact h0
  · rw [h]; exact h1

/-- Bridge note: the same composition law in hull's `Polynomial.criticalValues`
vocabulary is `Mzk1Lemma22FullShapeHelpersActual.critValues_comp_subset_union`. -/
def cvLawRowRecord : List (String × String) :=
  [ ("CV composition law", "PROVED cvCompositionLaw (CVCompositionLawStatement)"),
    ("special-set preservation", "PROVED specialSetPreservation (SpecialSetPreservationStatement)"),
    ("consumer", "abc RestatedLemma24InductionActual.s3135_CVInvariant_comp") ]

#check cvCompositionLaw
#check specialSetPreservation

end LeanFormal.IUT.XiFPaper.Mzk1Lemma24CVLawProofActual
end