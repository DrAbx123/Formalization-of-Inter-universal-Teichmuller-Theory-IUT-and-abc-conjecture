/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1P1B5WithFvActual
import tmp.sheaf.xif.paper.Mzk1P1ResidueOneActual
import Mathlib.Tactic
import tmp.sheaf.xif.paper.DeterminantLogVolumeActual
import tmp.sheaf.xif.paper.Mzk1DetLinePlaceB5Actual
import tmp.sheaf.xif.paper.Mzk1P1LocalGeneratorFromIsPrincipalActual
import tmp.sheaf.xif.paper.Mzk1P1LocalizedFractionalIdealActual
import tmp.sheaf.xif.paper.Mzk1P1PlaceVolumeSignActual
import tmp.sheaf.xif.paper.Mzk1Ob33B5AssemblyActual
import tmp.sheaf.xif.paper.Mzk1B5AssemblyNoHproductAttemptActual

/-! # P1: f_v as residue degree -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1B5FvResidueDegreeActual

open LeanFormal.IUT.ArithmeticQPilotBaseChange
open LeanFormal.IUT.PaperDeterminantLogVolume
open LeanFormal.IUT.XiFPaper.Mzk1P1B5WithFvActual

variable {k : Type} [Field k] [NumberField k]

def ResidueDegreeStatement (v : NumberField.FinitePlace k) (fv : Nat) : Prop :=
  Real.log (residueNormBase v) =
    (fv : Real) * Real.log (LeanFormal.IUT.NumberFieldFinitePlace.residueCharacteristic v : Real)

def fvResidueDegreeRows : List (String × String × String) :=
  [ ("ResidueDegreeStatement", "log residueNormBase = f_v * log p", "GAP (residue degree identification)"),
    ("fv = 1", "residue-one specialization", "GAP (GAP-PC-RESDEG/tame)"),
    ("B5 with f_v", "placeB5WithFv_of_target PROVED", "PROVED") ]

theorem fvResidueDegreeRows_length : fvResidueDegreeRows.length = 3 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1B5FvResidueDegreeActual

end
