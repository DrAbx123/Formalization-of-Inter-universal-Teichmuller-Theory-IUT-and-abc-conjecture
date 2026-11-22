import tmp.sheaf.xif.paper.Mzk1G2EGapInputsActual
import tmp.sheaf.xif.paper.Mzk1G2EGapInputsIffActual
import tmp.sheaf.xif.paper.Mzk1G2EEpsilonActual

/-! Mainline: reuse-chain re-exports for G2.e explicit gap inputs / epsilon data. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1G2EReuseActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1G2EGapInputsActual

universe u

theorem abcConjecture_of_gapInputs_reuse (X : Type u)
    (W : IQHullLogVolumeInterface X)
    (logShellPoint : Nat → Nat → Nat → X)
    (I : ∀ epsilon : Real, 0 < epsilon → EpsilonGapInputs W logShellPoint epsilon) :
    ABCConjecture :=
  LeanFormal.IUT.XiFPaper.Mzk1G2EGapInputsActual.abcConjecture_of_gapInputs X W logShellPoint I

theorem nonempty_gapInputs_iff_nonempty_comparison_reuse {X : Type u}
    {W : IQHullLogVolumeInterface X} {epsilon : Real} :
    (∃ logShellPoint : Nat → Nat → Nat → X, EpsilonGapInputs W logShellPoint epsilon) ↔
      Nonempty (Cor312EpsilonArithmeticComparison W epsilon) :=
  LeanFormal.IUT.XiFPaper.Mzk1G2EGapInputsIffActual.nonempty_gapInputs_iff_nonempty_comparison

theorem abcConjecture_of_data_reuse (carrier : Type u)
    (hullData : IQHullLogVolumeInterface carrier)
    (epsilonComparison : ∀ epsilon : Real, 0 < epsilon →
      Cor312EpsilonArithmeticComparison hullData epsilon) :
    ABCConjecture :=
  LeanFormal.IUT.XiFPaper.Mzk1G2EEpsilonActual.abcConjecture_of_data carrier hullData epsilonComparison

theorem heightBound_of_data_reuse (carrier : Type u)
    (hullData : IQHullLogVolumeInterface carrier)
    (epsilonComparison : ∀ epsilon : Real, 0 < epsilon →
      Cor312EpsilonArithmeticComparison hullData epsilon) :
    ∀ epsilon : Real, 0 < epsilon → ∃ A : Real, ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤
        (1 + epsilon) * arithmeticWeight (abcRationalPoint a c) + A :=
  LeanFormal.IUT.XiFPaper.Mzk1G2EEpsilonActual.heightBound_of_data carrier hullData epsilonComparison

theorem g2ERows_length_reuse :
    LeanFormal.IUT.XiFPaper.Mzk1G2EEpsilonActual.g2eRows.length = 5 :=
  LeanFormal.IUT.XiFPaper.Mzk1G2EEpsilonActual.g2eRows_length

end LeanFormal.IUT.XiFPaper.Mzk1G2EReuseActual