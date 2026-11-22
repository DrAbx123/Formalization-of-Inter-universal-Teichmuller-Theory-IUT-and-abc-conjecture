import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Tactic

/-! # Mzk1Stage4HullProductLawActual (stage4 lane; hull product law)

A657 module: the hull PRODUCT LAW — the volume of a product of coordinate closed balls
is the product of the coordinate volumes (finite product measure formula).  This is the
product law used by the hull/annulus measure chain.  No new mathematics.
Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Stage4HullProductLawActual

open MeasureTheory
open scoped ENNReal BigOperators

/-- Hull product law: the product-closed-ball volume is the product of the coordinate
closed-ball volumes `ofReal (2·rᵢ)`. -/
theorem hull_product_ball_law {ι : Type*} [Fintype ι] (r : ι → Real) :
    volume (Set.pi Set.univ (fun i : ι => Metric.closedBall (0 : Real) (r i))) =
      ∏ i : ι, ENNReal.ofReal (2 * r i) := by
  change Measure.pi (fun _ : ι => (volume : Measure Real))
    (Set.pi Set.univ (fun i : ι => Metric.closedBall (0 : Real) (r i))) = _
  rw [Measure.pi_pi]
  exact Finset.prod_congr rfl (fun i _ => Real.volume_closedBall (0 : Real) (r i))

/-- Two-coordinate specialization of the hull product law. -/
theorem hull_product_ball_law_two (r s : Real) :
    volume (Set.pi Set.univ
        (fun i : Fin 2 => Metric.closedBall (0 : Real)
          (if i = 0 then r else s))) =
      ENNReal.ofReal (2 * r) * ENNReal.ofReal (2 * s) := by
  rw [hull_product_ball_law]
  rw [Fin.prod_univ_two]
  norm_num

#check hull_product_ball_law
#check hull_product_ball_law_two

end LeanFormal.IUT.XiFPaper.Mzk1Stage4HullProductLawActual
end
