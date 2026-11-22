import tmp.sheaf.xif.paper.Mzk1HTF4OrbitProductActual
import tmp.sheaf.xif.paper.Mzk1HTF4StageBActual
import Mathlib.NumberTheory.Height.MvPolynomial
import Mathlib.Tactic
/-!
# F4 per-place height estimate: `h_{div(P|_Y)} ≤ r h_{O(1)} + C`

Route §8.3: for a homogeneous `P` of degree `r`, the per-place bound
`|P(x)|_w ≤ C_w max_j |x_j|_w^r` summed by the product formula gives
`h_{div(P|_Y)}(y) ≤ r h_{O(1)}(y) + C`.

This file obtains the estimate from Mathlib's **admissible-height** theorem
`Height.logHeight_eval_le` (donor, already in Mathlib): for a family of homogeneous
polynomials of the same degree `N`, `logHeight (eval x p) ≤ log(max (mulHeightBound p) 1) + N logHeight x`.
We apply it to the single orbit-product `P = ∏ L_i` (`isHomogeneous_P`, degree `|ι|`)
and the chart-0 point `x = ![φ x0, φ x1, 1]`, so `hO1 = Height.logHeight x` (F8Pi donor).

## Reuse / donor check (2026-11-17)
* `Mathlib.NumberTheory.Height.MvPolynomial.logHeight_eval_le` /
  `mulHeight_eval_le` / `mulHeightBound` — Mathlib, no port needed;
* `Mzk1HTF4OrbitProductActual.isHomogeneous_P` (DONE 12:54:03);
* `Mzk1HTF4StageBActual.F4ActualDivisorData.hDivP_le` — this theorem instantiates it;
* `F8PiActual` uses the same `Height.logHeight ![...]` for `hO1` (DONE 21:00:11).

**Still explicit**: the identification `hDivP = logHeight (eval x P)` with the actual
divisor height `h_{div(P|_Y)}` and the nonvanishing/fixed-constant bookkeeping (`C`).
F4 is not closed until these plus Galois descent/scheme order are supplied.
-/
set_option maxHeartbeats 1000000
noncomputable section
open MvPolynomial
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.HTF4HeightEstimateActual
open LeanFormal.IUT.XiFPaper.HTF4OrbitProductActual
open LeanFormal.IUT.XiFPaper.HTF4StageBActual

variable {K : Type*} [Field K] [NumberField K] {ι X : Type*} [Fintype ι] [Fintype X]
  [DecidableEq X]

/-- **Per-place height estimate** for the orbit product: for any `x : Fin 3 → K`,
`logHeight (eval x P) ≤ C + |ι| * logHeight x`, where `C = log(max (mulHeightBound P) 1)`. -/
theorem orbitProduct_logHeight_le (D : OrbitProductData ι X) (x : Fin 3 → K) :
    Height.logHeight (fun _ : Unit =>
        MvPolynomial.eval x ((D.P).map (algebraMap ℚ K))) ≤
      Real.log (max (Height.mulHeightBound
        (fun _ : Unit => (D.P).map (algebraMap ℚ K))) 1) +
        (Fintype.card ι : ℝ) * Height.logHeight x := by
  have hp : ∀ _ : Unit, ((D.P).map (algebraMap ℚ K)).IsHomogeneous (Fintype.card ι) :=
    fun _ => D.isHomogeneous_P.map (algebraMap ℚ K)
  simpa using
    (Height.logHeight_eval_le (K := K)
      (p := fun _ : Unit => (D.P).map (algebraMap ℚ K)) hp x)
#print axioms orbitProduct_logHeight_le
end LeanFormal.IUT.XiFPaper.HTF4HeightEstimateActual
end