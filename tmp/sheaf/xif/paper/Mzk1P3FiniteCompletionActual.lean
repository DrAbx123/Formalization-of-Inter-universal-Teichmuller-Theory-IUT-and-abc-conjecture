/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCompletionDegree
import Mathlib.Tactic

/-! # P3 FINITE fragment: Module.Finite of completed valuation rings (GAP-labeled)

Packages the existing conditional finiteness theorem and records its two
content inputs (separability and integral-closure comparison).
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
open LeanFormal.IUT.NumberFieldFinitePlace

namespace LeanFormal.IUT.XiFPaper.Mzk1P3FiniteCompletionActual

variable {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]

def FiniteCompletionIntegersData (place : NumberField.FinitePlace K) : Prop :=
  Module.Finite
    ((comap (k := k) place).maximalIdeal.adicCompletionIntegers k)
    (place.maximalIdeal.adicCompletionIntegers K)

theorem moduleFinite_of_separable_integralClosure
    (place : NumberField.FinitePlace K)
    (hseparable : Algebra.IsSeparable
      ((comap (k := k) place).maximalIdeal.adicCompletion k)
      (place.maximalIdeal.adicCompletion K))
    (hclosure : IsIntegralClosure (place.maximalIdeal.adicCompletionIntegers K)
      ((comap (k := k) place).maximalIdeal.adicCompletionIntegers k)
      (place.maximalIdeal.adicCompletion K)) :
    FiniteCompletionIntegersData (k := k) place :=
  moduleFinite_adicCompletionIntegers_of_isIntegralClosure (k := k) place hseparable hclosure

def finiteRows : List (String × String × String) :=
  [ ("FiniteCompletionIntegersData", "Module.Finite O_v O_w", "DEF (target Prop)"),
    ("moduleFinite_of_separable_integralClosure", "separable + integral closure => finite", "PROVED (existing)"),
    ("hseparable", "Algebra.IsSeparable of completed fields", "GAP-PC-FINITE-INPUT (content)"),
    ("hclosure", "IsIntegralClosure of completed valuation rings", "GAP-PC-FINITE-INPUT (content)") ]

theorem finiteRows_length : finiteRows.length = 4 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1P3FiniteCompletionActual

end
