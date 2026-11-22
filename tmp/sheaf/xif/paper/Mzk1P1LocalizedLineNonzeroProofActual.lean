/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1P1LocalGeneratorUncondActual
import tmp.sheaf.xif.paper.Mzk1P1GeneratorNonzeroActual
import Mathlib.Tactic

/-! # P1: localizedLine nonzero from I nonzero, via FractionalIdeal.extended -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P1LocalizedLineNonzeroProofActual

open LeanFormal.IUT.PaperDeterminantLogVolume
open LeanFormal.IUT.XiFPaper.Mzk1P1LocalizedFractionalIdealActual
open LeanFormal.IUT.XiFPaper.Mzk1P1LocalGeneratorUncondActual
open LeanFormal.IUT.XiFPaper.Mzk1DetLinePlaceB5Actual
open LeanFormal.IUT.XiFPaper.Mzk1P1GeneratorNonzeroActual

variable {k : Type} [Field k] [NumberField k]

/-- If the fractional ideal is nonzero, its localized line is nonzero. -/
theorem localizedLine_ne_bot_of_ne_zero
    (I : LineBundle (k := k)) (v : NumberField.FinitePlace k) (hI : I ≠ 0) :
    localizedLine (k := k) I v ≠ ⊥ := by
  intro hbot
  have hcoe : localizedFractionalIdeal (k := k) I v = 0 := by
    apply FractionalIdeal.coeToSubmodule_injective
    rw [← localizedFractionalIdeal_coe_eq]
    exact hbot
  have hzero : I = 0 := by
    refine (FractionalIdeal.extended_eq_zero_iff
      (L := LocalField (k := k) v) (I := I)
      (hf := sourceNZLeComap v)
      (hf' := FaithfulSMul.algebraMap_injective _ _)
      (hN := ?_)).mp hcoe
    intro h
    exact (nonZeroDivisors.ne_zero h) rfl
  exact hI hzero

/-- The unconditional generator is nonzero when the line bundle is nonzero. -/
theorem localGeneratorUncond_ne_zero
    (I : LineBundle (k := k)) (v : NumberField.FinitePlace k) (hI : I ≠ 0) :
    (localGeneratorUncond (k := k) I v).generator ≠ 0 := by
  have hlt : localizedLine (k := k) I v ≠ ⊥ :=
    localizedLine_ne_bot_of_ne_zero I v hI
  intro hgen
  apply hlt
  have hspan := (localGeneratorUncond (k := k) I v).span_eq
  rw [hspan, hgen]
  simp

def localizedLineNonzeroProofRows : List (String × String × String) :=
  [ ("localizedLine_ne_bot_of_ne_zero", "I != 0 => localizedLine != bot", "PROVED (extended injective)"),
    ("localGeneratorUncond_ne_zero", "I != 0 => generator != 0", "PROVED") ]

theorem localizedLineNonzeroProofRows_length : localizedLineNonzeroProofRows.length = 2 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1P1LocalizedLineNonzeroProofActual
