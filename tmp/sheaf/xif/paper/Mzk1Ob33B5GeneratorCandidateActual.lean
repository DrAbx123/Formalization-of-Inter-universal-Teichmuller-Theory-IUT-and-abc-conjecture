/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1Ob33B5CountUnconditionalAttemptActual
import tmp.sheaf.xif.paper.Mzk1PaperQPilotLineBundleSourceActual
import Mathlib.Tactic
import tmp.sheaf.xif.paper.DeterminantLogVolumeActual
import tmp.sheaf.xif.paper.Mzk1DetLinePlaceB5Actual
import tmp.sheaf.xif.paper.Mzk1P1LocalGeneratorFromIsPrincipalActual
import tmp.sheaf.xif.paper.Mzk1P1LocalizedFractionalIdealActual
import tmp.sheaf.xif.paper.Mzk1P1PlaceVolumeSignActual
import tmp.sheaf.xif.paper.Mzk1Ob33B5AssemblyActual
import tmp.sheaf.xif.paper.Mzk1B5AssemblyNoHproductAttemptActual

/-!
# P1: finite generator candidate from the localized principal-submodule structure

Given the actual DVR principal-submodule instance on `localizedLine I v`, define
the candidate generator as `Submodule.IsPrincipal.generator`, prove its span is
the localized line, and prove it is nonzero when the localized line is nonzero.
The only missing input is the `Submodule.IsPrincipal` instance itself (Mathlib
does not provide a localization/principal-submodule instance for `localizedLine`).
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1Ob33B5GeneratorCandidateActual

open LeanFormal.IUT.PaperDeterminantLogVolume
open LeanFormal.IUT.XiFPaper.Mzk1DetLinePrincipalGeneratorActual
open LeanFormal.IUT.XiFPaper.Mzk1PaperQPilotLineBundleSourceActual

variable {k : Type} [Field k] [NumberField k]

/-- Candidate generator of the localized line from the principal-submodule
structure. -/
noncomputable def localizedPrincipalGenerator
    (I : LineBundle (k := k)) (v : NumberField.FinitePlace k)
    [h : (localizedLine (k := k) I v).IsPrincipal] : LocalField (k := k) v :=
  Submodule.IsPrincipal.generator (localizedLine (k := k) I v)

theorem localizedPrincipalGenerator_span
    (I : LineBundle (k := k)) (v : NumberField.FinitePlace k)
    [h : (localizedLine (k := k) I v).IsPrincipal] :
    Submodule.span (LocalRing (k := k) v)
      {localizedPrincipalGenerator (k := k) I v} =
      localizedLine (k := k) I v :=
  Submodule.IsPrincipal.span_singleton_generator _

theorem localizedPrincipalGenerator_ne_zero
    (I : LineBundle (k := k)) (v : NumberField.FinitePlace k)
    [h : (localizedLine (k := k) I v).IsPrincipal]
    (hne : localizedLine (k := k) I v ≠ ⊥) :
    localizedPrincipalGenerator (k := k) I v ≠ 0 := by
  intro hzero
  apply hne
  rw [← localizedPrincipalGenerator_span (k := k) I v, hzero]
  simp

/-- Exact missing input: the localized line is a principal submodule. -/
def MissingLocalizedLinePrincipal
    (I : LineBundle (k := k)) (v : NumberField.FinitePlace k) : Prop :=
  (localizedLine (k := k) I v).IsPrincipal

def generatorCandidateRows : List (String × String × String) :=
  [ ("localizedPrincipalGenerator", "generator from Submodule.IsPrincipal", "CONSTRUCTED (given instance)"),
    ("localizedPrincipalGenerator_span", "span {generator} = localizedLine", "PROVED"),
    ("localizedPrincipalGenerator_ne_zero", "nonzero if localized line nonzero", "PROVED"),
    ("MissingLocalizedLinePrincipal", "Submodule.IsPrincipal localizedLine instance", "EXACT MISSING (Mathlib localization gap)") ]

theorem generatorCandidateRows_length : generatorCandidateRows.length = 4 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1Ob33B5GeneratorCandidateActual
