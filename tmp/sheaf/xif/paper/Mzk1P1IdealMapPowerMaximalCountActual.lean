/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1P1IdealMapPowerMaximalActual
import tmp.sheaf.xif.paper.Mzk1P1IdealMapPowerCountSelfActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P1IdealMapPowerMaximalCountActual

open LeanFormal.IUT.PaperDeterminantLogVolume
open LeanFormal.IUT.XiFPaper.Mzk1P1IdealLocalizedCountProofActual
open LeanFormal.IUT.XiFPaper.Mzk1P1IdealMapPowerMaximalActual
open LeanFormal.IUT.XiFPaper.Mzk1P1IdealMapPowerCountSelfActual
open LeanFormal.IUT.NumberFieldFinitePlace
variable {k : Type} [Field k] [NumberField k]
theorem idealMapPowerStatement_maxIdeal
    (v : NumberField.FinitePlace k)
    (hmapmax : Ideal.map (algebraMap (NumberField.RingOfIntegers k)
      (LocalRing (k := k) v)) (underlyingPrime v).asIdeal =
        completionIdealOf (k := k) v) :
    IdealMapPowerStatement (k := k) (underlyingPrime v).asIdeal
      (underlyingPrime v).ne_bot v := by
  unfold IdealMapPowerStatement
  rw [count_self_maxIdeal, hmapmax, pow_one]


end LeanFormal.IUT.XiFPaper.Mzk1P1IdealMapPowerMaximalCountActual
