/- Light part of the M2 pin data (compiles without the heavy critical-value import).

Provided here: gPoly positive degree, nonzero derivative, and the rational-value transfer
for zero branch values.  Reuse: `Mzk1GChoiceDegreeActual.gPoly_natDegree_pos` and
`Mathlib` `Polynomial.derivative_ne_zero`.  The critical-values-in-{0,1} statement for the
normalized polynomial `gPolyNorm = C (critFrac D)^{-1} * gPoly D` needs
`Mzk1CritValueInImageFinalActual` (heavy import, currently blocked by infra) and is
provided in `Mzk1GChoiceToM2PinActual`.
-/
import tmp.sheaf.xif.paper.Mzk1GChoiceDegreeActual
import tmp.sheaf.xif.paper.Mzk1Lemma22GChoiceConstructActual
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1GChoiceToM2PinLightActual

open LeanFormal.IUT.XiFPaper.Mzk1GChoiceDegreeActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma22GChoiceConstructActual
open Polynomial

/-- (1) gPoly has positive natDegree. -/
theorem gPoly_natDegree_pos_light (D : Mzk1ScaleData) : 0 < (gPoly D).natDegree :=
  lt_of_lt_of_le zero_lt_one (gPoly_natDegree_pos D)

/-- (2) gPoly has nonzero derivative. -/
theorem gPoly_derivative_ne_zero_light (D : Mzk1ScaleData) :
    Polynomial.derivative (gPoly D) ≠ 0 := by
  rw [Polynomial.derivative_ne_zero]
  exact Nat.ne_of_gt (lt_of_lt_of_le zero_lt_one (gPoly_natDegree_pos D))

/-- (5) a zero branch value is a rational value (c = 0). -/
theorem gPoly_value_mem_rat_light (D : Mzk1ScaleData) {z : ℂ}
    (h : Polynomial.aeval z (gPoly D) = 0) :
    ∃ c : ℚ, Polynomial.aeval z (gPoly D) = algebraMap ℚ ℂ c :=
  ⟨0, by rw [h, map_zero]⟩

end LeanFormal.IUT.XiFPaper.Mzk1GChoiceToM2PinLightActual
end
