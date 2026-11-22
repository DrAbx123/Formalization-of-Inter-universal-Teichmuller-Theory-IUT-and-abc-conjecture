/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCompletionDegree
import Mathlib.Tactic

/-! # P3 AGREE residue-field fragment

GAP-labeled file.  AGREE has two genuine components (see CANONICAL-TARGET-MAP P3 GAP defs):
GAP-PC-AGREE-RAM (completion ramificationIdx) and GAP-PC-AGREE-FIELD (completion inertiaDeg /
residue-field comparison).  They are NOT eliminated by the number-ring rfl bridges.
FLT assets already in-repo (tmp/external/ported/flt/FLT/DedekindDomain/AdicValuation.lean:
`ResidueFieldEquivCompletionResidueField`, `inertiaDeg_asIdeal_completionIdeal :
Ideal.inertiaDeg (v.completionIdeal K) A = 1`; IntegralClosure.lean: ramificationIdx results)
are the intended reuse path once their oleans are green.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P3AgreeResidueFieldActual

open LeanFormal.IUT.NumberFieldFinitePlace

variable {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]

def AgreeFieldComponent (place : NumberField.FinitePlace K) : Prop :=
  localInertiaDegree (k := k) place = relativeResidueDegree (k := k) place

def AgreeRamComponent (place : NumberField.FinitePlace K) : Prop :=
  localRamificationIndex (k := k) place = relativeRamificationIndex (k := k) place

theorem localDataAgreesWithPlaceData_iff_components (place : NumberField.FinitePlace K) :
    localDataAgreesWithPlaceData (k := k) place ↔
      AgreeRamComponent (k := k) place ∧ AgreeFieldComponent (k := k) place :=
  Iff.rfl

def agreeResidueFieldRows : List (String × String × String) :=
  [ ("AgreeRamComponent", "completion ramificationIdx = relative e", "GAP-PC-AGREE-RAM target"),
    ("AgreeFieldComponent", "completion inertiaDeg = relative f", "GAP-PC-AGREE-FIELD target"),
    ("localDataAgreesWithPlaceData_iff_components", "AGREE = both components (rfl)", "PROVED (rfl)"),
    ("FLT reuse", "FLT/DedekindDomain/AdicValuation + IntegralClosure", "pending FLT oleans green") ]

theorem agreeResidueFieldRows_length : agreeResidueFieldRows.length = 4 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1P3AgreeResidueFieldActual

end
