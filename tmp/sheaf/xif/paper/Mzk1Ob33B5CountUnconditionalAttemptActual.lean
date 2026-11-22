/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1Ob33B5IndexActual
import tmp.sheaf.xif.paper.Mzk1Ob33B5CountBridgeActual
import Mathlib.Tactic
import tmp.sheaf.xif.paper.DeterminantLogVolumeActual
import tmp.sheaf.xif.paper.Mzk1DetLinePlaceB5Actual
import tmp.sheaf.xif.paper.Mzk1P1LocalGeneratorFromIsPrincipalActual
import tmp.sheaf.xif.paper.Mzk1P1LocalizedFractionalIdealActual
import tmp.sheaf.xif.paper.Mzk1P1PlaceVolumeSignActual
import tmp.sheaf.xif.paper.Mzk1Ob33B5AssemblyActual
import tmp.sheaf.xif.paper.Mzk1B5AssemblyNoHproductAttemptActual

/-!
# Route B #3: attempt at unconditional generator valuation from span equality

The exact missing lemma is `SpanGeneratorValuationLemma`: for a generator whose
localized span is the line bundle, its local valuation is minus the fractional
ideal count.  `LocalGeneratorData.span_eq` alone does not provide this in Mathlib
(no DVR principal-generator/localization count lemma).  We record the missing
lemma name and prove all downstream consequences conditionally.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1Ob33B5CountUnconditionalAttemptActual

open LeanFormal.IUT.ArithmeticQPilotBaseChange
open LeanFormal.IUT.PaperDeterminantLogVolume
open LeanFormal.IUT.XiFPaper.Mzk1DetLinePlaceB5Actual
open LeanFormal.IUT.XiFPaper.Mzk1DetLinePrincipalGeneratorActual
open LeanFormal.IUT.XiFPaper.Mzk1B5CountLocalValuationBridgeActual
open LeanFormal.IUT.XiFPaper.Mzk1Ob33B5IndexActual
open LeanFormal.IUT.XiFPaper.Mzk1Ob33B5CountBridgeActual

variable {k : Type} [Field k] [NumberField k]

/-- Exact missing lemma: a DVR generator of the localized line has valuation
equal to minus the fractional-ideal count. -/
def SpanGeneratorValuationLemma (k : Type) [Field k] [NumberField k] : Prop :=
  ∀ {I : LineBundle (k := k)} (v : NumberField.FinitePlace k)
    (d : LocalGeneratorData (k := k) I v),
      PaperOModuleActual.localValuation (k := k) v d.generator =
        - (countExponent (k := k) v I : Int)

/-- The missing lemma is exactly the mainline `CountValuationBridge` input. -/
theorem countValuationBridge_of_spanGeneratorValuationLemma
    (h : SpanGeneratorValuationLemma k)
    {I : LineBundle (k := k)} {v : NumberField.FinitePlace k}
    (d : LocalGeneratorData (k := k) I v) :
    CountValuationBridge (k := k) d :=
  h v d

/-- Conditional unconditionalization: under the missing lemma, the relative
index is the count difference. -/
theorem relativePlaceIndex_eq_neg_count_add_count_of_lemma
    (h : SpanGeneratorValuationLemma k)
    {H O : LineBundle (k := k)} {v : NumberField.FinitePlace k}
    (dH : LocalGeneratorData (k := k) H v)
    (dO : LocalGeneratorData (k := k) O v) :
    relativePlaceIndex dH dO =
      - (countExponent (k := k) v H : Int) + (countExponent (k := k) v O : Int) := by
  unfold relativePlaceIndex
  rw [h v dH, h v dO]
  ring

def unconditionalAttemptRows : List (String × String × String) :=
  [ ("SpanGeneratorValuationLemma", "localValuation generator = -count", "EXACT MISSING lemma (Mathlib DVR/localization gap)"),
    ("relativePlaceIndex_eq_neg_count_add_count_of_lemma", "conditional unconditionalization", "PROVED conditional") ]

theorem unconditionalAttemptRows_length : unconditionalAttemptRows.length = 2 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1Ob33B5CountUnconditionalAttemptActual
