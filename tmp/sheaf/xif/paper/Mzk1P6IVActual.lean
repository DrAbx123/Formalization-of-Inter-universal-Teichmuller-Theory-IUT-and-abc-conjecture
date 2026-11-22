import tmp.sheaf.xif.paper.Mzk1P6StepVAveragesActual
import Mathlib.Tactic

set_option maxHeartbeats 4000000
noncomputable section
open scoped BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.IUTIV.StepVProcessionAverage
open LeanFormal.IUT.XiFPaper.Mzk1P6StepVAveragesActual

namespace LeanFormal.IUT.XiFPaper.Mzk1P6IVActual

/-- The StepV averaged readout `R`. -/
noncomputable def p6IVR (n : Nat) (D Q S T : Real) : Real :=
  (1 / (n : Real)) *
    (∑ j ∈ Finset.Icc 1 n, collectionBound (2 * (n : Real) + 1) D Q S T j)

/-- Paper-normalized `D` entering the IV inequality. -/
noncomputable def p6IVD (l D : Real) : Real :=
  ((l + 1) / (l + 5)) * ((1 + 4 / l) * D)

/-- Paper-normalized `Q` entering the IV inequality. -/
noncomputable def p6IVQ (l Q : Real) : Real := Q

/-- Paper-normalized `S` entering the IV inequality. -/
noncomputable def p6IVS (l S : Real) : Real := ((l + 1) / l) * S

/-- Paper-normalized `T` entering the IV inequality. -/
noncomputable def p6IVT (l T : Real) : Real :=
  (5 * (l + 1) / (3 * (l + 5))) * T

/-- §12.4 item 5: the IV inequality
`R <= (l+5)/4 D - (l+1)/24 Q + S + (l+5)T`
for the actual StepV averaged readout. -/
theorem p6_iv_inequality
    (n : Nat) (hn : 2 ≤ n) (D Q S T : Real)
    (hD : 0 ≤ D) (hS : 0 ≤ S) (hT : 0 ≤ T)
    (l : Real) (hl : l = 2 * (n : Real) + 1) :
    p6IVR n D Q S T ≤
      (l + 5) / 4 * p6IVD l D - (l + 1) / 24 * p6IVQ l Q +
        p6IVS l S + (l + 5) * p6IVT l T := by
  have h := p6_stepVAverages_ivInequality n hn D Q S T hD hS hT
  have hln : l ≠ 0 := by rw [hl]; positivity
  have hl1 : l + 1 ≠ 0 := by rw [hl]; positivity
  have hl5 : l + 5 ≠ 0 := by rw [hl]; positivity
  rw [show p6IVR n D Q S T = (1 / (n : Real)) *
      (∑ j ∈ Finset.Icc 1 n, collectionBound (2 * (n : Real) + 1) D Q S T j) from rfl]
  refine h.trans_eq ?_
  unfold p6IVD p6IVQ p6IVS p6IVT
  rw [hl]
  field_simp [hln, hl1, hl5]
  ring

#print axioms p6_iv_inequality

end LeanFormal.IUT.XiFPaper.Mzk1P6IVActual
end