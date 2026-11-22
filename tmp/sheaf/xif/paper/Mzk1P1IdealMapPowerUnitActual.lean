/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1P1IdealLocalizedCountProofActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace LeanFormal.IUT.XiFPaper.Mzk1P1IdealMapPowerUnitActual
open LeanFormal.IUT.PaperDeterminantLogVolume
open LeanFormal.IUT.XiFPaper.Mzk1DetLinePrincipalGeneratorActual
open LeanFormal.IUT.XiFPaper.Mzk1P1IdealLocalizedCountProofActual
open LeanFormal.IUT.NumberFieldFinitePlace
variable {k : Type} [Field k] [NumberField k]
theorem idealMapPower_one
    (v : NumberField.FinitePlace k) :
    IdealMapPowerStatement (k := k) (1 : Ideal (NumberField.RingOfIntegers k)) one_ne_zero v := by
  unfold IdealMapPowerStatement completionIdealOf
  simp
end LeanFormal.IUT.XiFPaper.Mzk1P1IdealMapPowerUnitActual
