/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1NormArchCKActual
import Mathlib.Tactic

/-! # #10: candidate abc haarScale formula `C_K * local-unit product` -/
noncomputable section
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1NormArchC3HaarScaleFormulaActual
open LeanFormal.IUT.XiFPaper.Mzk1NormArchCKActual
variable {K : Type*} [Field K] [NumberField K]

/-- Candidate arch factor times the product of normalized local unit-lattice masses. -/
noncomputable def c3HaarScaleCandidate (K : Type*) [Field K] [NumberField K]
    (localUnitProduct : ℝ) : ℝ :=
  archCK K * localUnitProduct

theorem c3HaarScaleCandidate_eq_inv_degree_mul (localUnitProduct : ℝ) :
    c3HaarScaleCandidate K localUnitProduct =
      ((Module.finrank ℚ K : ℝ))⁻¹ * localUnitProduct := by
  unfold c3HaarScaleCandidate archCK
  rfl

theorem c3HaarScaleCandidate_pos (localUnitProduct : ℝ)
    (h : 0 < localUnitProduct) : 0 < c3HaarScaleCandidate K localUnitProduct :=
  mul_pos archCK_pos h

/-- Degree-one plus unit local product gives the concrete value `1`. -/
theorem c3HaarScaleCandidate_eq_one_of_finrank_one
    (h : Module.finrank ℚ K = 1) (localUnitProduct : ℝ)
    (hu : localUnitProduct = 1) :
    c3HaarScaleCandidate K localUnitProduct = 1 := by
  unfold c3HaarScaleCandidate
  rw [archCK_eq_heightWeight,
    LeanFormal.IUT.XiFPaper.Mzk1NormArchCAbcActual.heightWeight_eq_one_of_finrank_one h, hu, one_mul]

/-- Formula-level named data: the abc `haarScale` equals `C_K * localUnitProduct`. -/
structure C3HaarScaleFormulaData (K : Type*) [Field K] [NumberField K] where
  localUnitProduct : ℝ
  localUnitProduct_pos : 0 < localUnitProduct
  haarScale : ℝ
  haarScale_eq : haarScale = c3HaarScaleCandidate K localUnitProduct

theorem C3HaarScaleFormulaData.haarScale_pos
    (D : C3HaarScaleFormulaData K) : 0 < D.haarScale := by
  rw [D.haarScale_eq]
  exact c3HaarScaleCandidate_pos D.localUnitProduct D.localUnitProduct_pos

def formulaRows : List (String × String) :=
  [ ("c3HaarScaleCandidate", "C_K * localUnitProduct explicit"),
    ("c3HaarScaleCandidate_eq_one_of_finrank_one", "[K:Q]=1 & product=1 => 1"),
    ("C3HaarScaleFormulaData", "formula-level named data"),
    ("missing blockEquiv/unitMass inhabitant", "GAP: C3S1902HaarScaleData has no constructed carrier"),
    ("product of local normalized unit masses", "GAP: needs localizedLine B3 + prod") ]
theorem formulaRows_length : formulaRows.length = 5 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1NormArchC3HaarScaleFormulaActual
