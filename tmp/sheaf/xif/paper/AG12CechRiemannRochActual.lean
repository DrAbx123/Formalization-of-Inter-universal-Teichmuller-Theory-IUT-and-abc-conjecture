import tmp.external.ported.flt_th.P2M.Sol.S_AlgebraicCurve_cechRiemannRoch_of_genusReached
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

/-!
# AG12: Čech Riemann-Roch consumer (A-class ported COMPLETE proof; genus-reached row)

Consumes the green ported module
tmp.external.ported.flt_th.P2M.Sol.S_AlgebraicCurve_cechRiemannRoch_of_genusReached
(EXIT=0; Apache-2.0 attribution retained; source sorry/axiom grep = 0):
its theorem P2MW....solution has a COMPLETE ported proof and is conditional exactly
on the paper rows:
* [IsCurveOver K F] and finite-dimensional L(0) (Riemann-Roch environment),
* RiemannGenusReachedAt γ D0 (the genus-reached input row),
* a two-chart cover with a point off each chart (h0/h1).
Conclusion: Cech H0/H1 finiteness, finrank equalities finrank H0 = ell D,
finrank H1 = indexOfSpecialty D, the index formula
finrank H0 - finrank H1 = deg D + 1 - γ, and H1 vanishing for D >= D0.

This file only re-exports the complete proof in the AG layer
(AG05 Cech + AG10 genus + AG12 RR); no re-proof, no axiom.

NOTE: imports only the flt_th ported universe (no adapted promotion in the same
file) to avoid the documented duplicate-namespace clash.

**Component, not paper object.**  Registry frozen 14041; no registry edits.
No sorry/axiom/True/PUnit/toy carrier.
-/

namespace LeanFormal.IUT.XiFPaper.AG12CechRiemannRochActual

open AlgebraicCurve

universe u

/-- A-class Čech Riemann-Roch consumer (complete ported proof; conditional exactly
on the paper genus-reached row + Cech cover data). -/
theorem ag12_cechRiemannRoch {K F : Type u} [Field K] [Field F] [Algebra K F]
    [IsCurveOver K F] [FiniteDimensional K ↥(LSpace (0 : Divisor K F))]
    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀)
    {S₀ S₁ : Set (Place K F)} (hcover : S₀ ∪ S₁ = Set.univ)
    (h₀ : ∃ v, v ∉ S₀) (h₁ : ∃ v, v ∉ S₁) (D : Divisor K F) :
    FiniteDimensional K ↥(cechH0 S₀ S₁ D) ∧ Module.Finite K (cechH1 S₀ S₁ D) ∧
      Module.finrank K ↥(cechH0 S₀ S₁ D) = ell D ∧
      Module.finrank K (cechH1 S₀ S₁ D) = indexOfSpecialty D ∧
      (Module.finrank K ↥(cechH0 S₀ S₁ D) : ℤ) - Module.finrank K (cechH1 S₀ S₁ D)
        = Divisor.degree D + 1 - γ ∧
      (D₀ ≤ D → Subsingleton (cechH1 S₀ S₁ D)) :=
  P2MW.S_AlgebraicCurve_cechRiemannRoch_of_genusReached.solution
    h hcover h₀ h₁ D

/-- A-class reuse record. -/
def ag12Reuse : List (String × String × String) :=
  [ ("Cech Riemann-Roch (H0/H1 finiteness, finrank, index formula, vanishing)", "tmp/external/ported/flt_th P2M/Sol/S_AlgebraicCurve_cechRiemannRoch_of_genusReached.lean (EXIT=0; COMPLETE ported proof)", "A (reused complete proof)"),
    ("paper rows consumed", "RiemannGenusReachedAt γ D0 (genus-reached row); two-chart cover h0/h1; [IsCurveOver]; FiniteDimensional L(0)", "class-B paper rows exactly as source"),
    ("AG05 Cech layer", "AG05CechActual (Cech H0/H1 canonical)", "A (reuse)"),
    ("AG10 genus layer", "AG10CanonicalDivisorGenusActual (canonical divisor/genus)", "A (reuse)") ]

end LeanFormal.IUT.XiFPaper.AG12CechRiemannRochActual

end
