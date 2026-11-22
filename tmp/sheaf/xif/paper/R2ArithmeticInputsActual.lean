/- R2 total arithmetic inputs: integrate DONE HlogdK/HsQ/HVh data into R2 H.
   - mkHVhData instantiates hVh from real row readouts V_bj, weights w, and the
     procession identity H = normalized weighted row average;
   - R2Inputs bundles the three actual arithmetic inputs;
   - R2_arithmetic_total returns all three route-4.4 bounds (no fake equalities). -/
import tmp.sheaf.xif.paper.Mzk1ULR2ActualInputsActual
import Mathlib.Analysis.SpecialFunctions.Log.Basic

noncomputable section
set_option linter.unusedSectionVars false
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.R2ArithmeticInputsActual

open LeanFormal.IUT.XiFPaper.Mzk1ULR2ActualInputsActual

/-- Instantiate hVh from real procession rows: V_bj readouts, weights w_b, and the
    H identity H = (sum_i w_i V_i)/(sum_i w_i). -/
def mkHVhData (ι : Type*) [Fintype ι] (V w : ι → Real) (H : Real)
    (hw : ∀ i, 0 <= w i) (hpos : 0 < ∑ i, w i)
    (hH : H = (∑ i, w i * V i) / (∑ i, w i)) : HVhData ι where
  V := V
  w := w
  avg := H
  hw_nonneg := hw
  havg := by rw [hH]
  hsum_pos := hpos

/-- hVh for real rows: H <= weighted row average (equality here by construction). -/
theorem hVh_from_rows (ι : Type*) [Fintype ι] (V w : ι → Real) (H : Real)
    (hw : ∀ i, 0 <= w i) (hpos : 0 < ∑ i, w i)
    (hH : H = (∑ i, w i * V i) / (∑ i, w i)) :
    H <= (∑ i, w i * V i) / (∑ i, w i) := by
  subst hH
  exact le_refl _

/-- Bundle of the three actual arithmetic inputs for R2. -/
structure R2Inputs (ι : Type*) [Fintype ι] where
  hlogdK : HlogdKData
  hsQ : HsQData
  hVh : HVhData ι

/-- R2 total arithmetic bound: hlogdK + hsQ + hVh all hold simultaneously. -/
theorem R2_arithmetic_total (ι : Type*) [Fintype ι] (D : R2Inputs ι) :
    D.hlogdK.logDifferentK <= D.hlogdK.S_ar + 2 * D.hlogdK.logl + 21 ∧
    D.hsQ.logSQ <= 2 * D.hsQ.dmod * D.hsQ.S_ar + 5 + D.hsQ.logl ∧
    D.hVh.avg <= (∑ i, D.hVh.w i * D.hVh.V i) / (∑ i, D.hVh.w i) := by
  refine ⟨hlogdK_bound D.hlogdK, hsQ_bound D.hsQ, hVh_le_weighted ι D.hVh⟩

#print axioms mkHVhData
#print axioms hVh_from_rows
#print axioms R2_arithmetic_total

end LeanFormal.IUT.XiFPaper.R2ArithmeticInputsActual