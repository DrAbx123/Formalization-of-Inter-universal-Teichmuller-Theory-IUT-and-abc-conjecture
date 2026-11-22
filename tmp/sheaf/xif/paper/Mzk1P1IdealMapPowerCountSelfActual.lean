/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1P1IdealLocalizedCountProofActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P1IdealMapPowerCountSelfActual

open LeanFormal.IUT.PaperDeterminantLogVolume
open LeanFormal.IUT.XiFPaper.Mzk1P1IdealLocalizedCountProofActual
open LeanFormal.IUT.NumberFieldFinitePlace
variable {k : Type} [Field k] [NumberField k]
theorem count_self_maxIdeal (v : NumberField.FinitePlace k) :
    (Associates.mk v.maximalIdeal.asIdeal).count
      (Associates.mk v.maximalIdeal.asIdeal).factors = 1 := by
  apply Associates.count_self
  exact Associates.irreducible_mk.mpr v.maximalIdeal.irreducible


end LeanFormal.IUT.XiFPaper.Mzk1P1IdealMapPowerCountSelfActual
