import tmp.sheaf.xif.paper.Mzk1FiniteMeasureLawsActualAdapted

/-! # Mzk1FiniteConjBoundActualAdapted — conjugate degree bound (real)

Real Lean (no sorry/axiom): every conjugate of alpha0 has degQ at most degQ alpha0, via
minpoly divisibility; hence the maximal degree of the conjugate set is bounded.  These are
the finite ingredients of the paper's "conjugates do not raise degrees" step.  Registry 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1FiniteConjBoundActualAdapted

open Polynomial
open LeanFormal.IUT.XiFPaper.Mzk1NestedInductionActual

attribute [local instance] Classical.decEq

universe u

/-- Conjugates of alpha0 have degree at most degQ alpha0. -/
theorem degQ_le_of_mem_conjSet (alpha0 x : Qbar) (hx : x ∈ conjSet alpha0) :
    degQ x <= degQ alpha0 := by
  have hroot : aeval x (minpoly ℚ alpha0) = 0 := mem_conjSet_iff.mp hx
  have hdvd : minpoly ℚ x ∣ minpoly ℚ alpha0 := minpoly.dvd ℚ x hroot
  have hne : minpoly ℚ alpha0 ≠ 0 := minpoly.ne_zero (isIntegral_Qbar alpha0)
  exact Polynomial.natDegree_le_of_dvd hdvd hne

/-- Maximal degree of the conjugate set is bounded by degQ alpha0. -/
theorem maxDeg_conjSet_le (alpha0 : Qbar) : maxDeg (conjSet alpha0) <= degQ alpha0 := by
  unfold maxDeg
  apply Finset.sup_le
  intro x hx
  exact degQ_le_of_mem_conjSet alpha0 x hx

def finiteConjBoundRows : List (String × String) :=
  [ ("degQ_le_of_mem_conjSet", "PROVED (minpoly divisibility)"),
    ("maxDeg_conjSet_le", "PROVED") ]

theorem finiteConjBoundRows_length : finiteConjBoundRows.length = 2 := rfl

#check degQ_le_of_mem_conjSet
#check maxDeg_conjSet_le

end LeanFormal.IUT.XiFPaper.Mzk1FiniteConjBoundActualAdapted
end
