import LeanFormal.IUT.ABCBridge.Bridge.Cor312ComparisonGapReduction
import tmp.sheaf.xif.paper.Mzk1G2EGapInputsActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Mzk1GapInputsAssemblyActual — reduced IUT IV §2 inputs land in explicit EpsilonGapInputs

DAG nodes: iutiv-abc:GapReduction / iutiv-abc:G2E.gapInputs.  The core gap assembly
produces a Cor312EpsilonArithmeticComparison; this file shows the same six reduced
inputs land in the explicit first-class EpsilonGapInputs structure of G2E, closing the
loop between the reduced-input assembly and the named-gap interface.  No gap field is
proved; the six inputs remain named.

No closure claim; GATE NOT PASSED; registry 14041; no registry edits.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1GapInputsAssemblyActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1G2EGapInputsActual

universe u

/-- Reduced gap inputs (explicit parameters) give first-class EpsilonGapInputs. -/
theorem epsilonGapInputs_of_reducedInputs {X : Type u} {W : IQHullLogVolumeInterface X}
    {logShellPoint : Nat → Nat → Nat → X} {eps D₀ D₁ : Real}
    (heps : 0 ≤ eps) (hD₀ : 0 ≤ D₀)
    (hval : ∀ a b c : Nat, IsABCTriple a b c →
      ∀ q ∈ arithmeticPrimeSupport (abcRationalPoint a c),
        max 0 (-(padicValRat q (abcRationalPoint a c) : Real)) ≤ 1 + eps)
    (hweightvol : ∀ a b c : Nat, IsABCTriple a b c →
      arithmeticWeight (abcRationalPoint a c) ≤
        (W.logVolume (normalizedComparisonRegion W logShellPoint a b c)).toReal)
    (hunit : W.logVolume W.unitRegion ≤ W.logVolume W.hull + ENNReal.ofReal D₀)
    (hsplit : ∀ a b c : Nat, IsABCTriple a b c →
      W.logVolume (normalizedComparisonRegion W logShellPoint a b c) ≤
        W.logVolume (W.scaleShift '' W.unitRegion) +
          W.logVolume {W.scaleShift (logShellPoint a b c)})
    (hptfin : ∀ a b c : Nat, IsABCTriple a b c →
      W.logVolume {W.scaleShift (logShellPoint a b c)} < ⊤)
    (hpoint : ∀ a b c : Nat, IsABCTriple a b c →
      (W.logVolume {W.scaleShift (logShellPoint a b c)}).toReal ≤
        (1 + eps) * arithmeticWeight (abcRationalPoint a c) + D₁) :
    EpsilonGapInputs W logShellPoint eps := by
  have hcomp := cor312GapAssembly_epsilonComparisonOfReducedInputs W logShellPoint
    heps hD₀ hval hweightvol hunit hsplit hptfin hpoint
  exact { height_le_normalizedRegionVolume := hcomp.height_le_normalizedRegionVolume
          regionVolume_le_normalizedWeight := hcomp.regionVolume_le_normalizedWeight }

/-- The explicit gap-inputs structure then gives the bridge interface at fixed eps. -/
theorem epsilonComparison_of_epsilonGapInputs {X : Type u}
    {W : IQHullLogVolumeInterface X} {logShellPoint : Nat → Nat → Nat → X} {eps : Real}
    (I : EpsilonGapInputs W logShellPoint eps) :
    Cor312EpsilonArithmeticComparison W eps :=
  epsilonComparison_of_gapInputs I

/-- Rows: assembly -> explicit gap inputs status. -/
def gapInputsAssemblyRows : List (String × String × String) :=
  [ ("reduced inputs -> EpsilonGapInputs", "epsilonGapInputs_of_reducedInputs", "PROVED (conditional)"),
    ("EpsilonGapInputs -> comparison", "epsilonComparison_of_epsilonGapInputs", "DEF (G2E)"),
    ("named inputs", "six reduced IUT IV §2 inputs", "NAMED"),
    ("scope", "no closure; gate NOT PASSED", "INTEGRITY") ]

theorem gapInputsAssemblyRows_length : gapInputsAssemblyRows.length = 4 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1GapInputsAssemblyActual

end
