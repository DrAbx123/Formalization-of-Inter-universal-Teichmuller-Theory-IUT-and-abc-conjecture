/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotBaseChange
import LeanFormal.IUT.Foundations.Geometry.FinitePlaceDegreeSumBound
import Mathlib.Tactic

/-! # P3 NORMFORMULA target (GAP): residue norm as characteristic^inertia degree

The target is exactly the absolute-norm power formula; it is recorded as a named
Prop with its two equivalent forms.  The proof is a GAP (needs assembly of
Ideal.absNorm_eq_pow_inertiaDeg_of_liesOver with under_eq_span_residueCharacteristic
and the inertiaDeg / inertiaDeg-prime conversion).
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P3NormFormulaActual

open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ArithmeticQPilotBaseChange

variable {K : Type*} [Field K] [NumberField K]

def ResidueNormPowerFormula (place : NumberField.FinitePlace K) : Prop :=
  residueNormBase place = (residueCharacteristic place : ℝ) ^ residueInertiaDegree place

def AbsNormPowerFormula (place : NumberField.FinitePlace K) : Prop :=
  (Ideal.absNorm place.maximalIdeal.asIdeal : ℝ) =
    (residueCharacteristic place : ℝ) ^ residueInertiaDegree place

theorem residueNormPowerFormula_iff_absNorm (place : NumberField.FinitePlace K) :
    ResidueNormPowerFormula place ↔ AbsNormPowerFormula place :=
  Iff.rfl

def residueNormFormulaRows : List (String × String × String) :=
  [ ("ResidueNormPowerFormula", "residueNormBase = char^inertiaDegree", "DEF (target Prop)"),
    ("AbsNormPowerFormula", "absNorm = char^inertiaDegree (definitionally same)", "DEF (equivalent)"),
    ("residueNormPowerFormula_iff_absNorm", "both forms equivalent", "PROVED (rfl)"),
    ("proof", "assemble absNorm_eq_pow_inertiaDeg with under_eq_span_residueCharacteristic", "GAP-PC-NORMFORMULA") ]

theorem residueNormFormulaRows_length : residueNormFormulaRows.length = 4 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1P3NormFormulaActual

end
