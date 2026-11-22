import tmp.sheaf.xif.paper.S2777MixedSpaceHeightGapActual
import tmp.sheaf.xif.paper.S2776BridgeHeightReduction
import LeanFormal.IUT.ABCBridge.Bridge.Cor312ToABCBridgeInterface

noncomputable section
open scoped ENNReal nonZeroDivisors Classical
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2780HeightDictionaryNoGoActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2766EpsilonComparisonGapActual
open LeanFormal.IUT.XiFPaper.S2767HeightGapEpsilonActual
open LeanFormal.IUT.XiFPaper.S2760MixedSpacePaperFactorActual
open LeanFormal.IUT.XiFPaper.S2776BridgeHeightReduction
open MeasureTheory

universe u

variable (K : Type u) [Field K] [NumberField K]
variable (J : (FractionalIdeal (NumberField.RingOfIntegers K)⁰ K)ˣ)

/-- The S2776 height dictionary is false for every `J`, `eps`, `C`: the
comparison-region volume is the fixed hull volume (S2767), while heights are
unbounded. -/
theorem S2780_heightDictionary_false (eps C : Real) :
    ¬ S2776HeightDictionary K J eps C := by
  intro h
  let V : Real :=
    ((S2760IQHullInterface K J).logVolume
      (S2760IQHullInterface K J).hull).toReal
  obtain ⟨a, b, c, habc, hgt⟩ :=
    abcRationalPoint_logHeight_unbounded (C * V)
  have hh := h a b c habc
  rw [S2767_region_logVolume_eq_hull] at hh
  exact not_lt_of_ge hh hgt

/-- Consequently there is no S2776 height dictionary with any constant. -/
theorem S2780_no_heightDictionary :
    ¬ ∃ C : Real, S2776HeightDictionary K J eps C := by
  rintro ⟨C, hC⟩
  exact S2780_heightDictionary_false K J eps C hC

#check S2780_heightDictionary_false
#check S2780_no_heightDictionary
#print axioms S2780_heightDictionary_false

end LeanFormal.IUT.XiFPaper.S2780HeightDictionaryNoGoActual
end
