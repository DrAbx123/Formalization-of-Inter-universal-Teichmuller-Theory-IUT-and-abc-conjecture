/- 
# B1 (owner emmy lane): A-4 value fibre on the first chart of `Y_n`

This is the ring-level input of the A-4 assembly for the **first chart** of the Fermat curve
`Y_n`: for a nonzero, nonconstant `h : ℚ[X]` and a value `c : ℚ`, the set of prime points
of `R n` at which the chart polynomial `h` of the protected coordinate
`g = psiChart0Coord n T` takes the value `c`,

  `{x : PrimeSpectrum (R n) | gHom n T (h - C c) ∈ x.asIdeal}`,

is finite.  (`gHom n T : ℚ[t] →+* R n` is `t ↦ psiChart0Coord n T`,
`Mzk1G1PsiChartFiniteGActual`; the fibre of `phiFixedL` over the lambda-chart point
`lambda = c` is cut out by exactly this set, cf. `Mzk1G1PhiFixedLChart0Actual`.)

Route (A-4):
1. `h - C c ≠ 0` for nonconstant `h` (`sub_C_ne_zero_of_pos_natDegree`);
2. `Mzk1G1PsiQuotientFiniteActual.quot_finiteDim` gives `R n ⧸ (h - C c)` finite over `ℚ`
   (through `R n` finite over `ℚ[t]`, `chartRing_finite_g`);
3. `Mzk1G1PsiFiberFiniteActual.finite_primes_of_finite_quotient` converts this
   finite-dimensionality into finiteness of the primes containing the value.

## Scope note on the hypotheses

The literal request carries only `h ≠ 0`; the statement is **false** for the constant
`h = C c` (then `h - C c = 0`, which lies in every prime).  We therefore require the
explicit hypothesis `0 < h.natDegree` (nonconstant `h`), which implies `h - C c ≠ 0`; the
`h ≠ 0` parameter is kept because it is the consumer's (B1/analytic-h) hypothesis and is
implied by `0 < h.natDegree`.

No sorry, no admit, no new axioms.
-/
import tmp.sheaf.xif.paper.Mzk1G1PsiQuotientFiniteActual
import tmp.sheaf.xif.paper.Mzk1G1PsiFiberFiniteActual
import Mathlib.Tactic

noncomputable section
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
open Polynomial

namespace LeanFormal.IUT.XiFPaper.Mzk1G1PhiFixedLValueFiberActual

open LeanFormal.IUT.XiFPaper.Mzk1G1FermatAffineChartActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiChartMapsActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiChartFiniteGActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiQuotientFiniteActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiFiberFiniteActual

/-- `h - C c` is nonzero for nonconstant `h`. -/
theorem sub_C_ne_zero_of_pos_natDegree {h : Polynomial ℚ} (hdeg : 0 < h.natDegree) (c : ℚ) :
    h - Polynomial.C c ≠ 0 := by
  intro hc
  have hc' : h = Polynomial.C c := sub_eq_zero.mp hc
  have hzero : h.natDegree = 0 := by
    rw [hc']
    exact Polynomial.natDegree_C c
  omega

/-- **A-4 value fibre (first chart of `Y_n`)**: for nonconstant nonzero `h` and any value
`c : ℚ`, only finitely many primes of `R n` contain the value `h(psiChart0Coord n T) - c`,
i.e. `gHom n T (h - C c)`. -/
theorem finite_primes_of_chart0_value (n : Nat) (T : Finset ℚ) (hT : T.Nonempty)
    (h : Polynomial ℚ) (hh : h ≠ 0) (hdeg : 0 < h.natDegree) (c : ℚ) :
    {x : PrimeSpectrum (R n) | gHom n T (h - Polynomial.C c) ∈ x.asIdeal}.Finite := by
  classical
  have hf : h - Polynomial.C c ≠ 0 := sub_C_ne_zero_of_pos_natDegree hdeg c
  have hfin : Module.Finite ℚ
      (R n ⧸ Ideal.span ({gHom n T (h - Polynomial.C c)} : Set (R n))) := by
    letI := gAlgebra n T
    exact quot_finiteDim n T hT (h - Polynomial.C c) hf
  exact finite_primes_of_finite_quotient (f := gHom n T (h - Polynomial.C c)) hfin

/-! ## Axiom checks -/

#print axioms sub_C_ne_zero_of_pos_natDegree
#print axioms finite_primes_of_chart0_value

end LeanFormal.IUT.XiFPaper.Mzk1G1PhiFixedLValueFiberActual
