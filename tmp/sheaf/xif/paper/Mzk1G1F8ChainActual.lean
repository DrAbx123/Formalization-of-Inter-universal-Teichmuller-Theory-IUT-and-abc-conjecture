import tmp.sheaf.xif.paper.Mzk1G1F8PiActual
import tmp.sheaf.xif.paper.Mzk1G1F8SecondActual

/-! # F8 pointwise chain (route §8.6 L838-848)

Composition of the two proved halves of F8 on chart-0 data:
* first equality `f8_pi_height_chart0` (F8PiActual): `h(pi(y))` vs `n * h_{O_Y(1)}(y)`;
* second equality `f8_second_equality_p1ChartHeight` (F8SecondActual): `h(pi(y)) = n/(n-3) * h_{omega}-frame`.
The resulting inequality is the exact part of F8; the remaining `O(1)` gap is the
comparison of the Cech frame height with the arithmetic height of `omega_Y`
(documented in F8SecondActual).
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.F8ChainActual

open LeanFormal.IUT.XiFPaper.F8PiActual
open LeanFormal.IUT.XiFPaper.Mzk1G1F8SecondActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatOverlapActual

variable {k : Type} [Field k] [NumberField k]

/-- Pointwise F8 chain: the `n/(n-3)`-scaled `omega_Y` Čech-frame height differs from
`n * h_{O_Y(1)}(y)` by at most `n * finrank * log 2`. -/
theorem f8_chain_chart0 (n : ℕ) (hn : 4 ≤ n)
    (φ : Chart0Ring n →+* k)
    (hrel : (φ (x0 n)) ^ n + (φ (x1 n)) ^ n = 1) :
    |((n : ℝ) / ((n : ℝ) - 3)) * Height.logHeight₁ ((φ (x0 n)) ^ (n - 3))
      - (n : ℝ) * Height.logHeight ![(φ (x0 n)), (φ (x1 n)), 1]|
      ≤ (n : ℝ) * ((Module.finrank ℚ k : ℝ) * Real.log 2) := by
  have hfirst : |Height.logHeight₁ ((φ (x0 n)) ^ n)
      - (n : ℝ) * Height.logHeight ![(φ (x0 n)), (φ (x1 n)), 1]|
      ≤ (n : ℝ) * ((Module.finrank ℚ k : ℝ) * Real.log 2) := by
    simpa [p1ChartHeight] using f8_pi_height_chart0 (k := k) n (by omega) φ
      (RingHom.ext_rat _ _) hrel
  have hsecond : Height.logHeight₁ ((φ (x0 n)) ^ n)
      = ((n : ℝ) / ((n : ℝ) - 3)) * Height.logHeight₁ ((φ (x0 n)) ^ (n - 3)) := by
    simpa [p1ChartHeight] using f8_second_equality_p1ChartHeight (k := k) n hn φ
  rw [hsecond] at hfirst
  exact hfirst

#print axioms f8_chain_chart0

end LeanFormal.IUT.XiFPaper.F8ChainActual
end