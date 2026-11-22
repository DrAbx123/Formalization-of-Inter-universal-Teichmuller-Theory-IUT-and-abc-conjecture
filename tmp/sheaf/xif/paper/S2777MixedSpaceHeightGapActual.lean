import tmp.sheaf.xif.paper.S2767HeightGapEpsilonActual
import LeanFormal.IUT.ABCBridge.Bridge.Cor312ToABCBridgeInterface

noncomputable section
open scoped ENNReal nonZeroDivisors Classical
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2777MixedSpaceHeightGapActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2766EpsilonComparisonGapActual
open LeanFormal.IUT.XiFPaper.S2767HeightGapEpsilonActual
open LeanFormal.IUT.XiFPaper.S2760MixedSpacePaperFactorActual
open MeasureTheory

universe u

variable (K : Type u) [Field K] [NumberField K]
variable (J : (FractionalIdeal (NumberField.RingOfIntegers K)⁰ K)ˣ)

/-- The S2766 height comparison is false for every `J` and `eps`: the comparison
region has exactly the hull log-volume (S2767), hence a triple-independent
bound, while ABC heights are unbounded. -/
theorem S2777_heightGap_false (eps : Real) :
    ¬ (∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤
        (1 + eps) *
          (((S2760IQHullInterface K J).logVolume
            (S2766ComparisonRegion K J eps a b c)).toReal)) := by
  intro h
  let C : Real :=
    (1 + eps) *
      ((S2760IQHullInterface K J).logVolume
        (S2760IQHullInterface K J).hull).toReal
  obtain ⟨a, b, c, habc, hgt⟩ :=
    abcRationalPoint_logHeight_unbounded C
  have hh := h a b c habc
  have hreg := S2767_region_logVolume_eq_hull (K := K) (J := J) eps a b c
  rw [hreg] at hh
  exact not_lt_of_ge hh hgt

/-- Exact obstruction: the S2766 epsilon-comparison gap cannot be inhabited. -/
theorem S2777_epsilonGap_false (eps : Real) :
    ¬ Nonempty (S2766EpsilonComparisonGap K J eps) := by
  rintro ⟨G⟩
  exact S2777_heightGap_false K J eps G.height_le_region

#check S2777_heightGap_false
#check S2777_epsilonGap_false
#print axioms S2777_epsilonGap_false

end LeanFormal.IUT.XiFPaper.S2777MixedSpaceHeightGapActual
end
