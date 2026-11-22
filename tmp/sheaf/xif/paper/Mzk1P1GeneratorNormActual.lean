/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1B5NormZpowActual
import Mathlib.Tactic
import tmp.sheaf.xif.paper.DeterminantLogVolumeActual
import tmp.sheaf.xif.paper.Mzk1DetLinePlaceB5Actual
import tmp.sheaf.xif.paper.Mzk1P1LocalGeneratorFromIsPrincipalActual
import tmp.sheaf.xif.paper.Mzk1P1LocalizedFractionalIdealActual
import tmp.sheaf.xif.paper.Mzk1P1PlaceVolumeSignActual
import tmp.sheaf.xif.paper.Mzk1Ob33B5AssemblyActual
import tmp.sheaf.xif.paper.Mzk1B5AssemblyNoHproductAttemptActual

/-! # P1: generator norm expression -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P1GeneratorNormActual

open LeanFormal.IUT.PaperDeterminantLogVolume
open LeanFormal.IUT.XiFPaper.Mzk1B5NormZpowActual

variable {k : Type} [Field k] [NumberField k]

def GeneratorNormStatement (v : NumberField.FinitePlace k)
    (x : LocalField (k := k) v) (_hx : x ≠ 0) : Prop :=
  NormZpowStatement (k := k) v x _hx

def generatorNormRows : List (String × String × String) :=
  [ ("GeneratorNormStatement", "norm = residueNormBase ^ localValuation", "GAP (zpow motive)"),
    ("proof chain", "FinitePlace.norm_def + WithZeroMulInt.toNNReal_neg_apply", "LOCATED") ]

theorem generatorNormRows_length : generatorNormRows.length = 2 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1P1GeneratorNormActual

end
