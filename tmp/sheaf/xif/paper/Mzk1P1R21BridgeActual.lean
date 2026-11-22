/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1P1GeneratorCountActual
import tmp.sheaf.xif.paper.Mzk1P1LocalizedSpanActual
import tmp.sheaf.xif.paper.Mzk1P1IdealLocalizedCountActual
import tmp.sheaf.xif.paper.Mzk1P1PrincipalValuationActual
import Mathlib.Tactic
import tmp.sheaf.xif.paper.DeterminantLogVolumeActual
import tmp.sheaf.xif.paper.Mzk1DetLinePlaceB5Actual
import tmp.sheaf.xif.paper.Mzk1P1LocalGeneratorFromIsPrincipalActual
import tmp.sheaf.xif.paper.Mzk1P1LocalizedFractionalIdealActual
import tmp.sheaf.xif.paper.Mzk1P1PlaceVolumeSignActual
import tmp.sheaf.xif.paper.Mzk1Ob33B5AssemblyActual
import tmp.sheaf.xif.paper.Mzk1B5AssemblyNoHproductAttemptActual

/-! # P1: R2.1 bridge assembly from the three named statements -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P1R21BridgeActual

open LeanFormal.IUT
open LeanFormal.IUT.PaperDeterminantLogVolume
open LeanFormal.IUT.XiFPaper.Mzk1DetLinePrincipalGeneratorActual
open LeanFormal.IUT.XiFPaper.Mzk1DetLinePlaceB5Actual
open LeanFormal.IUT.XiFPaper.Mzk1P1GeneratorCountActual
open LeanFormal.IUT.XiFPaper.Mzk1P1LocalizedSpanActual
open LeanFormal.IUT.XiFPaper.Mzk1P1IdealLocalizedCountActual
open LeanFormal.IUT.XiFPaper.Mzk1P1PrincipalValuationActual

variable {k : Type} [Field k] [NumberField k]

/-- The three named inputs needed for R2.1. -/
def R21AssemblyInputs : Prop :=
  (∀ (x : k) (v : NumberField.FinitePlace k),
      LocalizedSpanStatement (k := k) x v) ∧
  (∀ (I : Ideal (NumberField.RingOfIntegers k)) (_hI : I ≠ 0)
      (v : NumberField.FinitePlace k),
      IdealLocalizedCountStatement (k := k) I _hI v) ∧
  (PrincipalValuationStatement (k := k))

/-- The reduction target: the three inputs imply all R21Bridge instances.
(Kept as an explicit Prop so that no assembly step is silently assumed.) -/
def R21ReductionTarget : Prop :=
  R21AssemblyInputs (k := k) →
    ∀ (I : LineBundle (k := k)) (v : NumberField.FinitePlace k)
      (d : LocalGeneratorData (k := k) I v), R21Bridge (k := k) d

def r21Rows : List (String × String × String) :=
  [ ("R21AssemblyInputs", "LocalizedSpan + IdealLocalizedCount + PrincipalValuation", "GAP (three named statements)"),
    ("R21ReductionTarget", "inputs imply R21Bridge instances", "GAP (assembly proof not complete)") ]

theorem r21Rows_length : r21Rows.length = 2 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1P1R21BridgeActual

end