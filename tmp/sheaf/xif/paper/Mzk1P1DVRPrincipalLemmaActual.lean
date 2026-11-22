/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1P1LocalizedIsPrincipalActual
import Mathlib.Algebra.Module.PID
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.Tactic

/-! # P1 route A: DVR f.g. torsion-free => principal (single missing lemma) -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P1DVRPrincipalLemmaActual

open LeanFormal.IUT.PaperDeterminantLogVolume

variable {k : Type} [Field k] [NumberField k]

/-- Route A single missing lemma: a finitely generated torsion-free submodule of
`LocalField k v` over the DVR `LocalRing k v` is principal. -/
def DVRFGPrincipalLemma (k : Type) [Field k] [NumberField k] : Prop :=
  ∀ (v : NumberField.FinitePlace k)
    (M : Submodule (LocalRing (k := k) v) (LocalField (k := k) v)),
      Module.Finite (LocalRing (k := k) v) M →
      IsTorsionFree (LocalRing (k := k) v) M → M.IsPrincipal

/-- The localized line is finitely generated (would follow from fractional-ideal
finite generation + localization; recorded as exact input here). -/
def LocalizedLineFG (I : LineBundle (k := k)) (v : NumberField.FinitePlace k) : Prop :=
  Module.Finite (LocalRing (k := k) v) (localizedLine (k := k) I v)

/-- Route A reduction: FG + DVR lemma ⇒ IsPrincipal. -/
theorem localizedLine_isPrincipal_of_dvrLemma
    (I : LineBundle (k := k)) (v : NumberField.FinitePlace k)
    (hlemma : DVRFGPrincipalLemma k)
    (hfg : LocalizedLineFG (k := k) I v)
    (htf : IsTorsionFree (LocalRing (k := k) v)
      (localizedLine (k := k) I v)) :
    (localizedLine (k := k) I v).IsPrincipal :=
  hlemma v (localizedLine (k := k) I v) hfg htf

def dvrPrincipalRows : List (String × String × String) :=
  [ ("DVRFGPrincipalLemma", "DVR: f.g. torsion-free submodule => principal", "SINGLE EXACT MISSING"),
    ("LocalizedLineFG", "localizedLine is f.g. over DVR", "EXACT INPUT (fractional FG + localization)"),
    ("localizedLine_isPrincipal_of_dvrLemma", "route A reduction", "PROVED conditional") ]

theorem dvrPrincipalRows_length : dvrPrincipalRows.length = 3 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1P1DVRPrincipalLemmaActual
