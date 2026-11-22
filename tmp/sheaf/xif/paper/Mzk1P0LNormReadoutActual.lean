/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1C3LogShellTensorLActual
import tmp.sheaf.xif.paper.Mzk1C3S1902UnitMassCitizenActual
import tmp.sheaf.xif.paper.Mzk1P0LPaperInstanceActual
import Mathlib.Tactic

/-! # P0-L: canonical normalized readout on the L carrier (lean version)

The theta reading uses the **unnormalized** additive Haar (`Measure.addHaar`), so it is
fixed only up to an additive constant; `unitMass = 1` is false in general.  We define the
normalized readout `thetaNormReadL := thetaRead - log(Haar(unitBall))` without changing old
target types.  This file is kept deliberately small (heavy log-div identities and the
iff-form are deferred) to avoid expensive instance unfolding. -/

noncomputable section
open scoped BigOperators ENNReal
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 400000

namespace LeanFormal.IUT.XiFPaper.Mzk1P0LNormReadoutActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.C3LogShellTensorLActual
open LeanFormal.IUT.XiFPaper.Mzk1P0LPaperInstanceActual
open MeasureTheory

universe ua upi umon ui
variable {l : PrimeGeFive}
variable (I : OriginalInput.{0, 0, upi, umon, ui} l (FinitePrimePlace 2 7))
variable {p : Nat} [Fact p.Prime]
variable (place : FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p)

/-- Product unit ball of the L tensor block (coordinatewise closed unit balls). -/
noncomputable def actualUnitBallL : Set (C3LogShellTensorBlockL (C3LAt I place)) :=
  {x | ‖x‖ ≤ 1}

/-- Haar mass of the product unit ball on the L carrier. -/
noncomputable def actualUnitMassL : Real :=
  (actualC3LogShellTensorHaarL (C3LAt I place) (actualUnitBallL (I := I) (place := place))).toReal

/-- Normalized theta readout: raw theta log-volume minus the unit-ball log mass. -/
noncomputable def thetaNormReadL : Real :=
  thetaReadActual I place - Real.log (actualUnitMassL (I := I) (place := place))

/-- Definitional equation for the canonical normalized readout (rfl only). -/
theorem thetaNormReadL_eq_raw_sub_log_unitMass :
    thetaNormReadL (I := I) (place := place) =
      thetaReadActual I place -
        Real.log (actualUnitMassL (I := I) (place := place)) := rfl

/-- Canonical normalized comparison target: q reading vs normalized theta readout. -/
def LNormComparisonTarget : Prop :=
  qReadActual I place ≤ thetaNormReadL (I := I) (place := place)

/-- The old (unnormalized) target follows from the normalized one plus a nonnegative
`log(unitMass)` (small proof only; no heavy unfolding beyond the definitions). -/
theorem qRead_le_thetaRead_of_normTarget
    (h : LNormComparisonTarget (I := I) (place := place))
    (hu : 0 ≤ Real.log (actualUnitMassL (I := I) (place := place))) :
    qReadActual I place ≤ thetaReadActual I place := by
  have h' : qReadActual I place ≤
      thetaReadActual I place - Real.log (actualUnitMassL (I := I) (place := place)) := by
    simpa [LNormComparisonTarget, thetaNormReadL] using h
  have h1 : thetaReadActual I place -
      Real.log (actualUnitMassL (I := I) (place := place)) ≤ thetaReadActual I place :=
    sub_le_self _ hu
  exact le_trans h' h1

def lNormReadoutRows : List (String × String × String) :=
  [ ("actualUnitBallL", "product closed unit ball on L tensor block", "DEFINED"),
    ("actualUnitMassL", "Haar(unitBall).toReal (unnormalized)", "DEFINED"),
    ("thetaNormReadL", "raw theta log - log(unitMass)", "DEFINED"),
    ("thetaNormReadL_eq_raw_sub_log_unitMass", "definitional equation", "PROVED (rfl)"),
    ("LNormComparisonTarget", "canonical target: qRead <= thetaNormReadL", "DEFINED"),
    ("qRead_le_thetaRead_of_normTarget", "old target from normalized + log unitMass >= 0", "PROVED (conditional)"),
    ("unitMass = 1", "GAP (false in general)", "NOT CLAIMED") ]

theorem lNormReadoutRows_length : lNormReadoutRows.length = 7 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1P0LNormReadoutActual

end