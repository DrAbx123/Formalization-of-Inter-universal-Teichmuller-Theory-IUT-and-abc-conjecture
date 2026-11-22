/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1Ob33B5IndexGeneratorActual
import tmp.sheaf.xif.paper.Mzk1Ob33B5CountUnconditionalAttemptActual
import Mathlib.Tactic

/-! # P7 #3: rewire Ob33 B5 index with the actual (unconditional) generator -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1Ob33B5IndexRewireActual

open LeanFormal.IUT.PaperDeterminantLogVolume
open LeanFormal.IUT.XiFPaper.Mzk1DetLinePlaceB5Actual
open LeanFormal.IUT.XiFPaper.Mzk1DetLinePrincipalGeneratorActual
open LeanFormal.IUT.XiFPaper.Mzk1Ob33B5IndexActual
open LeanFormal.IUT.XiFPaper.Mzk1Ob33B5IndexGeneratorActual
open LeanFormal.IUT.XiFPaper.Mzk1Ob33B5CountUnconditionalAttemptActual

variable {k : Type} [Field k] [NumberField k]

/-- Actual rank-one SNF datum for any line bundle (unconditional generator). -/
noncomputable def placeSNFDataActual (I : LineBundle (k := k))
    (v : NumberField.FinitePlace k) : PlaceSNFData (k := k) I v :=
  placeSNFDataOfGenerator (k := k) I v (generatorDataActual (k := k) I v)

theorem placeSNFDataActual_index (I : LineBundle (k := k))
    (v : NumberField.FinitePlace k) :
    (placeSNFDataActual (k := k) I v).index =
      PaperOModuleActual.localValuation (k := k) v
        (generatorDataActual (k := k) I v).generator := rfl

/-- Under the exact span-generator valuation lemma, the SNF index is minus the count. -/
theorem placeSNFDataActual_index_eq_neg_count_of_lemma
    (h : SpanGeneratorValuationLemma (k := k)) (I : LineBundle (k := k))
    (v : NumberField.FinitePlace k) :
    (placeSNFDataActual (k := k) I v).index = - (countExponent (k := k) v I : Int) := by
  exact h v (generatorDataActual (k := k) I v)

/-- Relative per-place index as a difference of counts, from the exact lemma. -/
theorem relativePlaceIndex_eq_neg_add_of_lemma
    (h : SpanGeneratorValuationLemma (k := k))
    {H O : LineBundle (k := k)} {v : NumberField.FinitePlace k}
    (dH : LocalGeneratorData (k := k) H v) (dO : LocalGeneratorData (k := k) O v) :
    relativePlaceIndex dH dO =
      - (countExponent (k := k) v H : Int) + (countExponent (k := k) v O : Int) := by
  unfold relativePlaceIndex
  rw [h v dH, h v dO]
  ring

/-- The rewire exposes the unconditional general SNF object. -/
theorem missingGeneralPlaceSNF_rewired : MissingGeneralPlaceSNF (k := k) :=
  missingGeneralPlaceSNF_proved (k := k)

def b5IndexRewireRows : List (String × String × String) :=
  [ ("placeSNFDataActual", "rank-one SNF from unconditional generator", "CONSTRUCTED"),
    ("placeSNFDataActual_index", "SNF index = generator valuation", "PROVED (rfl)"),
    ("placeSNFDataActual_index_eq_neg_count_of_lemma", "index = -count under span lemma", "PROVED (conditional)"),
    ("relativePlaceIndex_eq_neg_add_of_lemma", "relative index = count difference", "PROVED (conditional)"),
    ("missingGeneralPlaceSNF_rewired", "MissingGeneralPlaceSNF re-export", "PROVED") ]

theorem b5IndexRewireRows_length : b5IndexRewireRows.length = 5 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1Ob33B5IndexRewireActual

end