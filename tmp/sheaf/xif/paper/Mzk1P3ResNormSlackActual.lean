/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotBaseChange
import LeanFormal.IUT.Foundations.NumberField.FinitePlaces
import Mathlib.Tactic

/-! # P3 RESDEG slack: local residue degree one iff residue-norm equality

CONDITIONAL-equivalence file; inputs are green lemmas about residueNormBase.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P3ResNormSlackActual

open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ArithmeticQPilotBaseChange

variable {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]

theorem log_lower_ne_zero (place : NumberField.FinitePlace K) :
    Real.log (residueNormBase (comap (k := k) place)) ≠ 0 :=
  Real.log_ne_zero_of_pos_of_ne_one
    (lt_trans zero_lt_one (residueNormBase_gt_one _))
    (ne_of_gt (residueNormBase_gt_one _))

theorem localResidueDegree_eq_one_of_residueNormBase_eq
    (place : NumberField.FinitePlace K)
    (h : residueNormBase place = residueNormBase (comap (k := k) place)) :
    localResidueDegree (k := k) place = 1 := by
  have hne := log_lower_ne_zero (k := k) place
  have hlog := congrArg Real.log h
  rw [residueNormBase_eq_lower_pow (k := k) place, Real.log_pow] at hlog
  have h1 : (localResidueDegree (k := k) place : ℝ) *
      Real.log (residueNormBase (comap (k := k) place)) =
      1 * Real.log (residueNormBase (comap (k := k) place)) := by
    simpa using hlog
  have hcast : (localResidueDegree (k := k) place : ℝ) = 1 :=
    mul_right_cancel₀ hne h1
  exact_mod_cast hcast

theorem residueNormBase_eq_of_localResidueDegree_eq_one
    (place : NumberField.FinitePlace K)
    (h : localResidueDegree (k := k) place = 1) :
    residueNormBase place = residueNormBase (comap (k := k) place) := by
  rw [residueNormBase_eq_lower_pow (k := k) place, h, pow_one]

theorem localResidueDegree_eq_one_iff_residueNormBase_eq
    (place : NumberField.FinitePlace K) :
    localResidueDegree (k := k) place = 1 ↔
      residueNormBase place = residueNormBase (comap (k := k) place) :=
  ⟨fun h => residueNormBase_eq_of_localResidueDegree_eq_one place h,
    fun h => localResidueDegree_eq_one_of_residueNormBase_eq place h⟩

end LeanFormal.IUT.XiFPaper.Mzk1P3ResNormSlackActual

end
