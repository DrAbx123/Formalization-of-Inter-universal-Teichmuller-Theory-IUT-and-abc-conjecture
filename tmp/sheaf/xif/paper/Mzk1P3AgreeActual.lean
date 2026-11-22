/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCompletionDegree
import Mathlib.Tactic

/-! # P3 AGREE target: local completed data vs number-ring place data

GAP-labeled file: AGREE is the comparison of the completed-valuation-ring
ramification index / residue degree with the number-ring place data.  We record
the two equivalent forms and the consumer identity (already green in
FinitePlaceCompletionDegree) without asserting the comparison.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P3AgreeActual

open LeanFormal.IUT.NumberFieldFinitePlace

variable {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]

theorem localDataAgreesWithPlaceData_iff (place : NumberField.FinitePlace K) :
    localDataAgreesWithPlaceData (k := k) place ↔
      localRamificationIndex (k := k) place = relativeRamificationIndex (k := k) place
      ∧ localInertiaDegree (k := k) place = relativeResidueDegree (k := k) place :=
  Iff.rfl

theorem finrank_eq_relativeCompletionDegree_of_agree
    (place : NumberField.FinitePlace K)
    (hfinite : Module.Finite
      ((comap (k := k) place).maximalIdeal.adicCompletionIntegers k)
      (place.maximalIdeal.adicCompletionIntegers K))
    (hagree : localDataAgreesWithPlaceData (k := k) place) :
    Module.finrank ((comap (k := k) place).maximalIdeal.adicCompletion k)
        (place.maximalIdeal.adicCompletion K) =
      relativeCompletionDegree (k := k) place :=
  finrank_adicCompletion_eq_relativeCompletionDegree (k := k) place hfinite hagree

def agreeRows : List (String × String × String) :=
  [ ("localDataAgreesWithPlaceData", "local completed e/f equals place data", "DEF (AGREE target)"),
    ("localDataAgreesWithPlaceData_iff", "two-component form", "PROVED (rfl)"),
    ("finrank_eq_relativeCompletionDegree_of_agree", "consumer identity given AGREE+finite", "PROVED (existing)"),
    ("proof", "compare residue fields / ramificationIdx across completion", "GAP-PC-AGREE") ]

theorem agreeRows_length : agreeRows.length = 4 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1P3AgreeActual

end
