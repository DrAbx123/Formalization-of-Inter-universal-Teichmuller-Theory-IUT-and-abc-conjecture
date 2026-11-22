import tmp.sheaf.xif.paper.Mzk1G2EGapInputsActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Mzk1G2EGapInputsIffActual — G2.e: explicit gap inputs ↔ epsilon comparison

DAG node: iutiv-abc:G2.e.  Completes the identification between the explicit
EpsilonGapInputs structure and Cor312EpsilonArithmeticComparison: an epsilon
comparison gives its gap inputs at its own logShellPoint, and existential gap
inputs give the comparison.  Both directions are definitional; no gap is proved.
No closure claim; gate NOT PASSED.  Registry frozen 14041; no registry edits.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1G2EGapInputsIffActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1G2EGapInputsActual

universe u

/-- An epsilon comparison yields its explicit gap inputs. -/
def gapInputs_of_epsilonComparison {X : Type u} {W : IQHullLogVolumeInterface X}
    {epsilon : Real} (C : Cor312EpsilonArithmeticComparison W epsilon) :
    EpsilonGapInputs W C.logShellPoint epsilon :=
{ height_le_normalizedRegionVolume := C.height_le_normalizedRegionVolume
  regionVolume_le_normalizedWeight := C.regionVolume_le_normalizedWeight }

/-- Existential explicit gap inputs are equivalent to the epsilon comparison. -/
theorem nonempty_gapInputs_iff_nonempty_comparison {X : Type u}
    {W : IQHullLogVolumeInterface X} {epsilon : Real} :
    (∃ logShellPoint : Nat → Nat → Nat → X, EpsilonGapInputs W logShellPoint epsilon) ↔
    Nonempty (Cor312EpsilonArithmeticComparison W epsilon) := by
  constructor
  · rintro ⟨logShellPoint, I⟩
    exact ⟨epsilonComparison_of_gapInputs I⟩
  · rintro ⟨C⟩
    exact ⟨C.logShellPoint, gapInputs_of_epsilonComparison C⟩

/-- Rows: G2.e identification status. -/
def g2EGapInputsIffRows : List (String × String × String) :=
  [ ("comparison -> gap inputs", "gapInputs_of_epsilonComparison", "DEF (definitional)"),
    ("existential equivalence", "nonempty_gapInputs_iff_nonempty_comparison", "PROVED"),
    ("scope", "gaps named; no closure; gate NOT PASSED", "INTEGRITY") ]

theorem g2EGapInputsIffRows_length : g2EGapInputsIffRows.length = 3 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1G2EGapInputsIffActual

end
