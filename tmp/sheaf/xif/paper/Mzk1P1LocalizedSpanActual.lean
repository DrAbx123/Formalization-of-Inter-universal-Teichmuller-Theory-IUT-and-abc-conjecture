/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.DeterminantLogVolumeActual
import Mathlib.RingTheory.FractionalIdeal.Operations
import Mathlib.Tactic

/-! # P1: localized line of a principal fractional ideal -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P1LocalizedSpanActual

open LeanFormal.IUT.PaperDeterminantLogVolume

variable {k : Type} [Field k] [NumberField k]

/-- Statement: localizing a principal fractional ideal gives the O_v-span of the
image of the generator. -/
def LocalizedSpanStatement (x : k) (v : NumberField.FinitePlace k) : Prop :=
  localizedLine (k := k)
      (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers k)) x) v =
    Submodule.span (LocalRing (k := k) v)
      {algebraMap k (LocalField (k := k) v) x}

def localizedSpanRows : List (String × String × String) :=
  [ ("LocalizedSpanStatement", "localizedLine (spanSingleton x) v = span O_v {algebraMap x}", "GAP (named statement; span/map coercion chain)"),
    ("proof route", "FractionalIdeal.coe_spanSingleton + Submodule.map_span + Submodule.span_span_of_tower", "MATHLIB route") ]

theorem localizedSpanRows_length : localizedSpanRows.length = 2 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1P1LocalizedSpanActual

end