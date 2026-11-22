import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

noncomputable section
open scoped BigOperators

namespace LeanFormal.IUT.XiFPaper.S2709MultiQLogFormulaActual

/-- The multi-q donor log-volume formula: for a finite family of contracting
positive reals `q i`, the sum of the per-place absolute logs equals minus the
log of the product.  This is the scalar formula a multi-q donor needs if its
single `q` has norm equal to the product of the place norms. -/
theorem S2709_multiQ_logVolume_eq_neg_log_prod
    {ι : Type} [Fintype ι] (q : ι → Real)
    (hpos : ∀ i, 0 < q i) (hlt : ∀ i, q i < 1) :
    (∑ i, |Real.log (q i)|) = -Real.log (∏ i, q i) := by
  have hlog : Real.log (∏ i, q i) = ∑ i, Real.log (q i) := by
    simpa using Real.log_prod (s := Finset.univ) (f := q)
      (fun i _ => ne_of_gt (hpos i))
  rw [hlog]
  have hneg : ∀ i, Real.log (q i) < 0 := fun i => Real.log_neg (hpos i) (hlt i)
  rw [Finset.sum_congr rfl (fun i _ => abs_of_neg (hneg i))]
  rw [← Finset.sum_neg_distrib]

#print axioms S2709_multiQ_logVolume_eq_neg_log_prod

end LeanFormal.IUT.XiFPaper.S2709MultiQLogFormulaActual
end
