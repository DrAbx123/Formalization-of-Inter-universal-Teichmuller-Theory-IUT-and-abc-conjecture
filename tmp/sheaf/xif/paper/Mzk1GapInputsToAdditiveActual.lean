import tmp.sheaf.xif.paper.Mzk1G2EGapInputsActual
import LeanFormal.IUT.ABCBridge.Bridge.IUTToABC
import LeanFormal.IUT.ABCBridge.Arithmetic.ABCHeightArithmeticWeightComparison

/-! Mainline: chain consumer from G2.e explicit gap inputs to the additive V2 contract
  and to the logarithmic ABC conjecture (new conclusions, composed from the proved
  conditional bridge plus the proved equivalences). -/

namespace LeanFormal.IUT.XiFPaper.Mzk1GapInputsToAdditiveActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1G2EGapInputsActual

universe u

theorem v2_of_gapInputs (X : Type u) (W : IQHullLogVolumeInterface X)
    (logShellPoint : Nat → Nat → Nat → X)
    (I : ∀ epsilon : Real, 0 < epsilon → EpsilonGapInputs W logShellPoint epsilon) :
    ABCHeightWeightAdditiveBoundV2 :=
  abcConjecture_iff_ABCHeightWeightAdditiveBoundV2.mp
    (abcConjecture_of_gapInputs X W logShellPoint I)

theorem logConjecture_of_gapInputs (X : Type u) (W : IQHullLogVolumeInterface X)
    (logShellPoint : Nat → Nat → Nat → X)
    (I : ∀ epsilon : Real, 0 < epsilon → EpsilonGapInputs W logShellPoint epsilon) :
    ABCLogConjecture :=
  abcConjecture_iff_abcLogConjecture.mp
    (abcConjecture_of_gapInputs X W logShellPoint I)

theorem heightWeightBound_of_gapInputs (X : Type u) (W : IQHullLogVolumeInterface X)
    (logShellPoint : Nat → Nat → Nat → X)
    (I : ∀ epsilon : Real, 0 < epsilon → EpsilonGapInputs W logShellPoint epsilon) :
    (∀ epsilon : Real, 0 < epsilon → ∃ A : Real, ∀ a b c : Nat, IsABCTriple a b c → Height.logHeight₁ (abcRationalPoint a c) ≤ (1 + epsilon) * arithmeticWeight (abcRationalPoint a c) + A) :=
  abcConjecture_iff_abcArithmeticWeightHeightBound.mp
    (abcConjecture_of_gapInputs X W logShellPoint I)

end LeanFormal.IUT.XiFPaper.Mzk1GapInputsToAdditiveActual