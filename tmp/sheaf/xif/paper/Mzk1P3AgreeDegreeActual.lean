/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCompletionDegree
import tmp.sheaf.xif.paper.ProcessionNormalizationWeightsActual
import Mathlib.Tactic

/-! # P3 AGREE fragment: local completion degree equals relative completion degree under AGREE + FINITE
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P3AgreeDegreeActual

open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.ProcessionNormalizationWeightsActual

variable {l : PrimeGeFive}
variable (T : InitialThetaArithmeticData l)

theorem localCompletionDegree_eq_relativeCompletionDegree_of_agree
    (place : NumberField.FinitePlace T.K)
    (hfinite : Module.Finite
      ((comap (k := T.Fmod) place).maximalIdeal.adicCompletionIntegers T.Fmod)
      (place.maximalIdeal.adicCompletionIntegers T.K))
    (hagree : localDataAgreesWithPlaceData (k := T.Fmod) place) :
    localCompletionDegree T place = relativeCompletionDegree (k := T.Fmod) place := by
  unfold localCompletionDegree
  exact finrank_adicCompletion_eq_relativeCompletionDegree (k := T.Fmod) place hfinite hagree

def agreeDegreeRows : List (String × String × String) :=
  [ ("localCompletionDegree_eq_relativeCompletionDegree_of_agree", "actual local degree = relative degree under AGREE+FINITE", "PROVED (conditional)"),
    ("hfinite", "Module.Finite completed valuation rings", "input (GAP-PC-FINITE)"),
    ("hagree", "localDataAgreesWithPlaceData", "input (GAP-PC-AGREE)") ]

theorem agreeDegreeRows_length : agreeDegreeRows.length = 3 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1P3AgreeDegreeActual

end
