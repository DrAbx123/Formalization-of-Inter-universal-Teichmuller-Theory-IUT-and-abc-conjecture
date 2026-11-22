import Mathlib.NumberTheory.Height.Basic
import tmp.sheaf.xif.paper.Mzk1HTF4DivisorHeightActual
import Mathlib.Tactic
/-!
# F4: height vs divisor identification — Mathlib place-sum donor

Mathlib's `Height.logHeight₁_eq` expresses the logarithmic height of a field element as
a sum over the (admissible) absolute values:
`logHeight₁ x = (archAbsVal.map (fun v => log⁺ (v x))).sum + ∑ᶠ v : nonarchAbsVal, log⁺ (v.val x)`.
This is the exact donor for identifying the divisor-height sum `∑ z, D z * h z`
(`Mzk1HTF4DivisorHeightActual.divisorHeight`) with `Height.logHeight` once the local
weights `h z` are the place logarithms and the divisor is the zero/pole divisor.

## Reuse / donor check (2026-11-17)
* `Mathlib.NumberTheory.Height.Basic.logHeight₁_eq` (place-sum identity, DONE in Mathlib);
* `Height.logHeight_eq_log_mulHeight` (`logHeight = log mulHeight`, rfl);
* `Mzk1HTF4DivisorHeightActual.divisorHeight` (DONE 14:14:50).

**Explicit obligation**: the identification of the local weights `h z` with the place
logarithms and of the divisor with the zero/pole divisor of `P_i|_Y` is not proved here;
the place-sum identity itself is the Mathlib donor.
-/
noncomputable section
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.HTF4HeightDivisorLinkActual
open LeanFormal.IUT.XiFPaper.HTF4DivisorHeightActual

variable {K : Type*} [Field K] [Height.AdmissibleAbsValues K]

/-- Mathlib place-sum identity for the logarithmic height (re-exported donor). -/
theorem logHeight₁_eq_place_sum (x : K) :
    Height.logHeight₁ x =
      ((Height.AdmissibleAbsValues.archAbsVal (K := K)).map
          (fun v : AbsoluteValue K ℝ => Real.posLog (v x))).sum +
        ∑ᶠ v : Height.AdmissibleAbsValues.nonarchAbsVal (K := K),
          Real.posLog (v.val x) :=
  Height.logHeight₁_eq x
#print axioms logHeight₁_eq_place_sum
end LeanFormal.IUT.XiFPaper.HTF4HeightDivisorLinkActual
end