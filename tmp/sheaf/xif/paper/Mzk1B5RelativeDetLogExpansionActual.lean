/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1B5LocalGlobalProductFormulaActual
import tmp.sheaf.xif.paper.Mzk1DetLineConstructionActual
import tmp.sheaf.xif.paper.Mzk1DetLinePrincipalGeneratorActual
import tmp.sheaf.xif.paper.Mzk1Ob33ArchMetricActual
import tmp.sheaf.xif.paper.Mzk1DetLinePlaceB5MergedActual
import Mathlib.Tactic
import tmp.sheaf.xif.paper.DeterminantLogVolumeActual
import tmp.sheaf.xif.paper.Mzk1DetLinePlaceB5Actual
import tmp.sheaf.xif.paper.Mzk1P1LocalGeneratorFromIsPrincipalActual
import tmp.sheaf.xif.paper.Mzk1P1LocalizedFractionalIdealActual
import tmp.sheaf.xif.paper.Mzk1P1PlaceVolumeSignActual
import tmp.sheaf.xif.paper.Mzk1Ob33B5AssemblyActual
import tmp.sheaf.xif.paper.Mzk1B5AssemblyNoHproductAttemptActual

/-!
# Route B #3 step 1/3: relative determinant log expansion + arch summary

Uses the green qpilot product formula (integral ideals), the relative determinant
identity globalLogVolume_relativeDetLine, and the arch metric identity
archDetMetricWeight_eq_neg_archimedeanLogNorm.

The fractional-ideal expansion is kept as the explicit named input
FractionalLogVolumeExpansion (qpilot fractional version or num/den reduction).
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1B5RelativeDetLogExpansionActual

open LeanFormal.IUT
open LeanFormal.IUT.ArithmeticQPilotBaseChange
open LeanFormal.IUT.PaperDeterminantLogVolume
open LeanFormal.IUT.XiFPaper.Mzk1DetLineConstructionActual
open LeanFormal.IUT.XiFPaper.Mzk1DetLinePrincipalGeneratorActual
open LeanFormal.IUT.XiFPaper.Mzk1Ob33ArchMetricActual
open LeanFormal.IUT.XiFPaper.Mzk1NormArchCKActual
open LeanFormal.IUT.XiFPaper.Mzk1B5LocalGlobalProductFormulaActual

variable {k : Type} [Field k] [NumberField k]

def FractionalLogVolumeExpansion : Prop :=
  ∀ (I : LineBundle (k := k)) (_ : I ≠ 0),
    globalLogVolume (k := k) I =
      ∑ᶠ v : NumberField.FinitePlace k,
        (countExponent (k := k) v I : Real) * Real.log (residueNormBase v)

theorem relativeDetLog_eq_finsum_sub_of_expansions
    (h : FractionalLogVolumeExpansion (k := k))
    (H O : LineBundle (k := k)) (hH : H ≠ 0) (hO : O ≠ 0) :
    relativeDetLog (k := k) H O =
      (∑ᶠ v : NumberField.FinitePlace k,
        (countExponent (k := k) v H : Real) * Real.log (residueNormBase v))
      - (∑ᶠ v : NumberField.FinitePlace k,
        (countExponent (k := k) v O : Real) * Real.log (residueNormBase v)) := by
  unfold relativeDetLog
  rw [globalLogVolume_relativeDetLine (k := k) H O hH hO, h H hH, h O hO]

theorem relativeDetLog_eq_single_finsum
    (h : FractionalLogVolumeExpansion (k := k))
    (H O : LineBundle (k := k)) (hH : H ≠ 0) (hO : O ≠ 0)
    (hsub :
      (∑ᶠ v : NumberField.FinitePlace k,
        (countExponent (k := k) v H : Real) * Real.log (residueNormBase v))
      - (∑ᶠ v : NumberField.FinitePlace k,
        (countExponent (k := k) v O : Real) * Real.log (residueNormBase v))
      = ∑ᶠ v : NumberField.FinitePlace k,
        ((countExponent (k := k) v H : Real) - (countExponent (k := k) v O : Real)) *
          Real.log (residueNormBase v)) :
    relativeDetLog (k := k) H O =
      ∑ᶠ v : NumberField.FinitePlace k,
        ((countExponent (k := k) v H : Real) - (countExponent (k := k) v O : Real)) *
          Real.log (residueNormBase v) := by
  rw [relativeDetLog_eq_finsum_sub_of_expansions h H O hH hO, hsub]

theorem relativeDetLog_add_archMetricWeight_eq
    (h : FractionalLogVolumeExpansion (k := k))
    (H O : LineBundle (k := k)) (hH : H ≠ 0) (hO : O ≠ 0)
    (f : (k)ˣ) :
    relativeDetLog (k := k) H O + archDetMetricWeight (F := k) f =
      ((∑ᶠ v : NumberField.FinitePlace k,
        (countExponent (k := k) v H : Real) * Real.log (residueNormBase v))
      - (∑ᶠ v : NumberField.FinitePlace k,
        (countExponent (k := k) v O : Real) * Real.log (residueNormBase v)))
        - archCK k * archimedeanLogNorm (F := k) (f : k) := by
  rw [relativeDetLog_eq_finsum_sub_of_expansions h H O hH hO,
    archDetMetricWeight_eq_neg_archimedeanLogNorm (F := k) f]
  ring

def b5ExpansionRows : List (String × String × String) :=
  [ ("FractionalLogVolumeExpansion", "fractional ideal log expansion (named input)", "GAP (qpilot fractional version / num-den reduction)"),
    ("relativeDetLog_eq_finsum_sub_of_expansions", "log D(H,O) as difference of the two finite-place sums", "PROVED (conditional)"),
    ("relativeDetLog_eq_single_finsum", "single finsum form given the sub-distributivity equation", "PROVED (conditional on hsub)"),
    ("relativeDetLog_add_archMetricWeight_eq", "B5 summary with arch metric weight", "PROVED (conditional)"),
    ("archDetMetricWeight_eq_neg_archimedeanLogNorm", "arch metric = -C_K * log-norm", "GREEN (Ob33ArchMetric)") ]

theorem b5ExpansionRows_length : b5ExpansionRows.length = 5 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1B5RelativeDetLogExpansionActual

end