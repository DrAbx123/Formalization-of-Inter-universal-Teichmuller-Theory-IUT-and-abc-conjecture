import tmp.sheaf.xif.paper.Mzk1PolyMapActual
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Tactic

/-! # Mzk1PolyChainRuleActual — polynomial chain rule for P^1 unramifiedness (Lemma 2.2 upgrade)

STEP 0 prior-art: corpus Lemma 2.2 lines 106-135 (compose morphisms P^1 -> P^1);
Mzk1PolyMapActual (polyMapPoints/polyMorphism/polyUnramifiedAt), Mzk1Lemma22CompositionActual
(composition/induction), Mzk1Lemma22InductionActual (partial shape).  Mathlib
Polynomial.eval_comp / derivative_comp / comp_eq_zero_iff reused.

THIS FILE proves the algebraic core needed to upgrade the partial Lemma 2.2 shape
(nonconstant + preserves + avoids) to the full shape including unramifiedness:
* value map of a composed polynomial = composition of value maps;
* derivative chain rule: derivative tests compose (finite points);
* nonzero composition at infinity from nonconstancy of the inner polynomial. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1PolyChainRuleActual

open Polynomial
open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1PolyMapActual

/-- Value map of h.comp g is the composition of the value maps. -/
theorem polyMapPoints_comp_finite (g h : ℚ[X]) (x : ℚ) :
    polyMapPoints (h.comp g) (P1Point.ofFinite x) =
      polyMapPoints h (polyMapPoints g (P1Point.ofFinite x)) := by
  simp [polyMapPoints, P1Point.ofFinite, Polynomial.eval_comp]

theorem polyMapPoints_comp_infty (g h : ℚ[X]) :
    polyMapPoints (h.comp g) P1Point.infty =
      polyMapPoints h (polyMapPoints g P1Point.infty) := rfl

/-- Derivative chain rule for the unramifiedness predicate at finite points. -/
theorem polyUnramifiedAt_comp_finite {g h : ℚ[X]} {x : ℚ}
    (hg : g.derivative.eval x ≠ 0) (hh : h.derivative.eval (g.eval x) ≠ 0) :
    polyUnramifiedAt (h.comp g) (P1Point.ofFinite x) := by
  show (h.comp g).derivative.eval x ≠ 0
  rw [Polynomial.derivative_comp, Polynomial.eval_mul]
  have hcomp : (h.derivative.comp g).eval x = h.derivative.eval (g.eval x) := by
    rw [Polynomial.eval_comp]
  rw [hcomp]
  exact mul_ne_zero hg hh

/-- Nonzero composition at infinity: if the inner polynomial is nonconstant and the
outer polynomial is nonzero, then h.comp g is nonzero. -/
theorem comp_ne_zero_of_nonconstant {g h : ℚ[X]} (hgdeg : 1 ≤ g.natDegree) (hne : h ≠ 0) :
    h.comp g ≠ 0 := by
  intro hz
  rcases (Polynomial.comp_eq_zero_iff.mp hz) with hh | ⟨_, hconst⟩
  · exact hne hh
  · have : g.natDegree = 0 := by
      rw [hconst]
      simp
    omega

/-- Unramifiedness at infinity composes. -/
theorem polyUnramifiedAt_comp_infty {g h : ℚ[X]} (hgdeg : 1 ≤ g.natDegree)
    (hh : polyUnramifiedAt h P1Point.infty) :
    polyUnramifiedAt (h.comp g) P1Point.infty := by
  show h.comp g ≠ 0
  exact comp_ne_zero_of_nonconstant hgdeg hh

#check polyMapPoints_comp_finite
#check polyMapPoints_comp_infty
#check polyUnramifiedAt_comp_finite
#check comp_ne_zero_of_nonconstant
#check polyUnramifiedAt_comp_infty

end LeanFormal.IUT.XiFPaper.Mzk1PolyChainRuleActual
end
