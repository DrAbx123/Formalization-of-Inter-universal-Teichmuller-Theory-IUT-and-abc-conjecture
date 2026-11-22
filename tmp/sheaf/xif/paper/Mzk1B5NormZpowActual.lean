/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.DeterminantLogVolumeActual
import LeanFormal.IUT.Foundations.NumberField.FinitePlaces
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.Tactic

/-!
# B5: completion norm as residueNormBase to the local valuation power (statement)

The proof chain (Mathlib `NumberField.FinitePlace.norm_def` +
`WithZeroMulInt.toNNReal_neg_apply` + base/exponent identification) is recorded here
as an explicit statement; the direct proof hits a `zpow` motive obstruction when
rewriting `residueNormBase` / `localValuation` under the integer power.
-/

noncomputable section
open scoped BigOperators NNReal
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1B5NormZpowActual

open LeanFormal.IUT
open LeanFormal.IUT.ArithmeticQPilotBaseChange
open LeanFormal.IUT.PaperDeterminantLogVolume
open LeanFormal.IUT.NumberFieldFinitePlace

variable {k : Type} [Field k] [NumberField k]

/-- Statement: for nonzero x, the completion norm is residueNormBase to the local valuation. -/
def NormZpowStatement (v : NumberField.FinitePlace k)
    (x : LocalField (k := k) v) (_hx : x ≠ 0) : Prop :=
  ‖x‖ = (residueNormBase v) ^ (localValuation (k := k) v x)

def normZpowRows : List (String × String × String) :=
  [ ("NormZpowStatement", "norm = residueNormBase ^ localValuation (x != 0)", "GAP (named statement; zpow motive obstruction)") ]

theorem normZpowRows_length : normZpowRows.length = 1 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1B5NormZpowActual

end