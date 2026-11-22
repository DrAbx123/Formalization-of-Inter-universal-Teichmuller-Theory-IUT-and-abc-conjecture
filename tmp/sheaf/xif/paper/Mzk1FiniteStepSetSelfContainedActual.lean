import tmp.sheaf.xif.paper.Mzk1NestedInductionActual

/-! # Mzk1FiniteStepSetSelfContainedActual — self-contained finite step-set bound (real)

Real Lean (no sorry/axiom): unconditional bound on the maximal degree of the paper's step
set, self-contained (depends only on the green Mzk1NestedInductionActual; local re-proofs of
the Finset laws and conjugate bound avoid the stale-olean dependency chain).  This is the
finite-level f4a ingredient.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1FiniteStepSetSelfContainedActual

open Polynomial
open LeanFormal.IUT.XiFPaper.Mzk1NestedInductionActual

attribute [local instance] Classical.decEq

universe u

theorem maxDeg_union' (S T : Finset Qbar) :
    maxDeg (S ∪ T) = max (maxDeg S) (maxDeg T) := by
  unfold maxDeg
  rw [Finset.sup_union]

theorem maxDeg_image_le' (S : Finset Qbar) (f : Qbar -> Qbar) (M : Nat)
    (h : forall x, x ∈ S -> degQ (f x) <= M) :
    maxDeg (S.image f) <= M := by
  unfold maxDeg
  apply Finset.sup_le
  intro y hy
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
  exact h x hx

theorem degQ_le_of_mem_conjSet' (alpha0 x : Qbar) (hx : x ∈ conjSet alpha0) :
    degQ x <= degQ alpha0 := by
  have hroot : aeval x (minpoly ℚ alpha0) = 0 := mem_conjSet_iff.mp hx
  have hdvd : minpoly ℚ x ∣ minpoly ℚ alpha0 := minpoly.dvd ℚ x hroot
  have hne : minpoly ℚ alpha0 ≠ 0 := minpoly.ne_zero (isIntegral_Qbar alpha0)
  exact Polynomial.natDegree_le_of_dvd hdvd hne

theorem maxDeg_stepSet_le_max' (S : Finset Qbar) (alpha0 : Qbar) :
    maxDeg (stepSet S alpha0) <= max (maxDeg S) (degQ alpha0) := by
  unfold stepSet
  rw [maxDeg_union']
  apply max_le
  · apply maxDeg_image_le'
    intro x hx
    rcases Finset.mem_union.mp hx with hxS | hxC
    · have hxle : degQ x <= maxDeg S := by
        unfold maxDeg
        exact Finset.le_sup hxS
      exact le_trans (degQ_aeval_le (minpoly ℚ alpha0) x) (le_trans hxle (le_max_left _ _))
    · exact le_trans (degQ_aeval_le (minpoly ℚ alpha0) x)
        (le_trans (degQ_le_of_mem_conjSet' alpha0 x hxC) (le_max_right _ _))
  · apply maxDeg_image_le'
    intro xi hxi
    have hroot := aeval_derivative_eq_zero_of_mem_critSet hxi
    exact le_trans (le_of_lt (degQ_critValue_lt alpha0 xi hroot)) (le_max_right _ _)

theorem maxDeg_stepSet_le' (S : Finset Qbar) (alpha0 : Qbar)
    (hdeg : degQ alpha0 = maxDeg S) :
    maxDeg (stepSet S alpha0) <= maxDeg S := by
  have h : maxDeg (stepSet S alpha0) <= max (maxDeg S) (maxDeg S) := by
    have := maxDeg_stepSet_le_max' S alpha0
    rwa [hdeg] at this
  rwa [max_self] at h

def finiteStepSetSelfContainedRows : List (String × String) :=
  [ ("maxDeg_stepSet_le_max'", "PROVED (unconditional)"),
    ("maxDeg_stepSet_le'", "PROVED (finite f4a)") ]

theorem finiteStepSetSelfContainedRows_length : finiteStepSetSelfContainedRows.length = 2 := rfl

theorem maxDeg_stepSet_iterate_le_max'' (S : Finset Qbar) (alpha0 : Qbar) (n : Nat) :
    maxDeg (Nat.iterate (fun T => stepSet T alpha0) n S)
      <= max (maxDeg S) (degQ alpha0) := by
  induction n with
  | zero => exact le_max_left _ _
  | succ n ih =>
      show maxDeg (stepSet (Nat.iterate (fun T => stepSet T alpha0) n S) alpha0)
        <= max (maxDeg S) (degQ alpha0)
      exact le_trans (maxDeg_stepSet_le_max' _ alpha0) (max_le ih (le_max_right _ _))

theorem maxDeg_stepSet_iterate_le_maxDeg' (S : Finset Qbar) (alpha0 : Qbar)
    (hdeg : degQ alpha0 = maxDeg S) (n : Nat) :
    maxDeg (Nat.iterate (fun T => stepSet T alpha0) n S) <= maxDeg S := by
  have h := maxDeg_stepSet_iterate_le_max'' S alpha0 n
  rw [hdeg, max_self] at h
  exact h

#check maxDeg_stepSet_iterate_le_maxDeg'

#check maxDeg_stepSet_iterate_le_max''

#check maxDeg_stepSet_le_max'
#check maxDeg_stepSet_le'

end LeanFormal.IUT.XiFPaper.Mzk1FiniteStepSetSelfContainedActual
end
