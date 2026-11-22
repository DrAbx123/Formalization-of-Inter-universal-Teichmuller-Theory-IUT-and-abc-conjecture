/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1P1IdealMapPowerMaximalCountActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P1IdealMapPowerMaximalApplyActual

open LeanFormal.IUT.PaperDeterminantLogVolume
open LeanFormal.IUT.XiFPaper.Mzk1P1IdealLocalizedCountProofActual
open LeanFormal.IUT.XiFPaper.Mzk1P1IdealMapPowerMaximalCountActual
open LeanFormal.IUT.XiFPaper.Mzk1P1IdealMapPowerCountSelfActual
open LeanFormal.IUT.NumberFieldFinitePlace
variable {k : Type} [Field k] [NumberField k]
theorem idealMapPowerStatement_maxIdeal_apply
    (v : NumberField.FinitePlace k)
    (hmapmax : Ideal.map (algebraMap (NumberField.RingOfIntegers k)
      (LocalRing (k := k) v)) v.maximalIdeal.asIdeal =
        completionIdealOf (k := k) v) :
    IdealMapPowerStatement (k := k) v.maximalIdeal.asIdeal v.maximalIdeal.ne_bot v :=
  idealMapPowerStatement_maxIdeal v hmapmax


end LeanFormal.IUT.XiFPaper.Mzk1P1IdealMapPowerMaximalApplyActual
