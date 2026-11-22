/- Route 7.2: conjugate separation with the explicit constant p^{-B}. -/
import tmp.sheaf.xif.paper.Mzk1G1UniversalSeparationActual
import tmp.sheaf.xif.paper.Mzk1G1UniversalSeparationConstantActual
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1UniversalSeparationBoundActual

open Polynomial
open LeanFormal.IUT.XiFPaper.Mzk1G1UniversalSeparationActual
open LeanFormal.IUT.XiFPaper.Mzk1G1UniversalSeparationConstantActual

variable {R : Type*} [NormedField R] [IsUltrametricDist R] [DecidableEq R]

/-- Concrete separation bound: if the derivative at x has norm at least p^{-B}, then every other
root of the minimal polynomial is at distance at least p^{-B} from x. -/
theorem separation_of_derivative_norm_ge {p d : Nat} [Fact p.Prime] {f : R[X]} (hm : f.Monic)
    (hf : f.Splits) {x x' : R} (hx : x ∈ f.roots) (hx' : x' ∈ f.roots) (hxx' : x' ≠ x)
    (hroot : ∀ a ∈ f.roots, ‖x - a‖ ≤ 1)
    (hderiv : (p : ℝ) ^ (-(differentBound p d : ℤ)) ≤ ‖eval x f.derivative‖) :
    (p : ℝ) ^ (-(differentBound p d : ℤ)) ≤ ‖x - x'‖ :=
  le_norm_sub_of_le_norm_eval_derivative hm hf hx hx' hxx' hroot hderiv

#print axioms separation_of_derivative_norm_ge
end LeanFormal.IUT.XiFPaper.Mzk1G1UniversalSeparationBoundActual
