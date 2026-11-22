/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCompletionDegree
import Mathlib.Tactic

/-! # P3 UNRAM-RESIDUE fragment: e = f = 1 iff relative degree one

Green equivalence (unpacking the definition and Nat.mul_eq_one).
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
open LeanFormal.IUT.NumberFieldFinitePlace

namespace LeanFormal.IUT.XiFPaper.Mzk1P3UnramResidueActual

variable {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]

def UnramResidueData (place : NumberField.FinitePlace K) : Prop :=
  relativeRamificationIndex (k := k) place = 1
    ∧ relativeResidueDegree (k := k) place = 1

theorem unramResidueData_iff_relativeCompletionDegree_eq_one
    (place : NumberField.FinitePlace K) :
    UnramResidueData (k := k) place ↔ relativeCompletionDegree (k := k) place = 1 := by
  unfold UnramResidueData relativeCompletionDegree
  constructor
  · intro h
    rw [h.1, h.2, mul_one]
  · intro h
    have ha : relativeRamificationIndex (k := k) place = 1 := by
      have hdvd : relativeRamificationIndex (k := k) place ∣ 1 :=
        ⟨relativeResidueDegree (k := k) place, h.symm⟩
      exact Nat.dvd_one.mp hdvd
    have hb : relativeResidueDegree (k := k) place = 1 := by
      have hdvd : relativeResidueDegree (k := k) place ∣ 1 :=
        ⟨relativeRamificationIndex (k := k) place, by rw [mul_comm]; exact h.symm⟩
      exact Nat.dvd_one.mp hdvd
    exact ⟨ha, hb⟩

def unramResidueRows : List (String × String × String) :=
  [ ("UnramResidueData", "relative e = 1 and f = 1", "DEF (target Prop)"),
    ("unramResidueData_iff_relativeCompletionDegree_eq_one", "e=f=1 iff relative degree one", "PROVED (green)") ]

theorem unramResidueRows_length : unramResidueRows.length = 2 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1P3UnramResidueActual

end
