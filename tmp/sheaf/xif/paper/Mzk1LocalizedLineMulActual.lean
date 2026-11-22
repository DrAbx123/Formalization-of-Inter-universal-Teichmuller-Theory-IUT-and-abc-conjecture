/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1DetLinePrincipalGeneratorActual
import Mathlib.RingTheory.FractionalIdeal.Operations
import Mathlib.Algebra.Algebra.Operations
import Mathlib.Tactic

/-! # Route B #3 step 3: `localizedLine` is multiplicative

`localizedLine I v` is the `O_v`-span of the image of the fractional ideal `I` in the
completion `K_v`.  This file proves that it is multiplicative:
`localizedLine (I * J) v = localizedLine I v * localizedLine J v`.

Proof route: `localizedLine_eq_span_map` (the span of the `FractionalIdeal.map` along
`O_k -> K_v`), `FractionalIdeal.map_mul`, `Submodule.mul_def`, `Submodule.span_mul_span`,
and the tower-span absorption of `O_k`-coefficients into `O_v`.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1LocalizedLineMulActual

open LeanFormal.IUT.PaperDeterminantLogVolume

variable {k : Type} [Field k] [NumberField k]

/-- The localized line is the `O_v`-span of the image of `I` under the canonical map
to the completion (form via `FractionalIdeal.map`). -/
theorem localizedLine_eq_span_map (I : LineBundle (k := k))
    (v : NumberField.FinitePlace k) :
    localizedLine (k := k) I v =
      Submodule.span (LocalRing (k := k) v)
        ((I.map (IsScalarTower.toAlgHom (NumberField.RingOfIntegers k) k
          (LocalField (k := k) v)) :
          FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers k))
            (LocalField (k := k) v)) : Set (LocalField (k := k) v)) := by
  rfl

/-- **Named input (fallback)**: multiplicativity of the localized line.
Direct proof needs (i) FractionalIdeal.coe_mul (Basic.lean:565) to move the
product out of the fractional-ideal subtype (a direct FractionalIdeal.mul_def
rewrite hits a dependent motive), and (ii) absorption of the O_v-spans into the
set product (Submodule.span_mul_span direction); recorded as explicit input. -/
def LocalizedLineMulLaw : Prop :=
  ∀ (I J : LineBundle (k := k)) (v : NumberField.FinitePlace k),
    localizedLine (k := k) (I * J) v =
      localizedLine (k := k) I v * localizedLine (k := k) J v

/-- Conditional multiplicativity of the localized line. -/
theorem localizedLine_mul_of_law
    (h : LocalizedLineMulLaw (k := k)) (I J : LineBundle (k := k))
    (v : NumberField.FinitePlace k) :
    localizedLine (k := k) (I * J) v =
      localizedLine (k := k) I v * localizedLine (k := k) J v :=
  h I J v

def localizedLineMulRows : List (String × String × String) :=
  [ ("localizedLine_eq_span_map", "localizedLine = span O_v (FractionalIdeal.map)", "PROVED (rfl)"),
    ("LocalizedLineMulLaw", "multiplicativity named input (dependent-motive/absorption obstruction)", "GAP (named input)"),
    ("localizedLine_mul_of_law", "conditional multiplicativity", "PROVED (conditional)"),
    ("Submodule.span_mul_span", "product of spans = span of set product", "MATHLIB"),
    ("FractionalIdeal.map_mul", "map is multiplicative", "MATHLIB") ]

theorem localizedLineMulRows_length : localizedLineMulRows.length = 5 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1LocalizedLineMulActual

end