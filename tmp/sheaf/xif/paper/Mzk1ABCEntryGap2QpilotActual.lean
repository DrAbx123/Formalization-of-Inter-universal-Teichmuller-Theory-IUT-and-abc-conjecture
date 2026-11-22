/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.ABCBridge.Bridge.Cor312ToABCBridgeInterface
import Mathlib.Tactic

/-! # Mzk1ABCEntryGap2QpilotActual — Gap-2 arithmetic consumer (qpilot, own name)

A572: the Gap-2 side of the Cor 3.12 -> ABC bridge, from the green bridge module:
* region log-volume bound (the `(1+ε)` weight estimate with θ and D);
* derived finiteness of the comparison-region volume;
* the `ENNReal.ofReal`/`toReal` faithfulness;
* the additive contract v2 consumer.
 -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1ABCEntryGap2QpilotActual

open LeanFormal.IUT
open LeanFormal.IUT
open MeasureTheory
open scoped ENNReal

universe u

/-- Gap 2 (named paper link): the `ε`-normalized comparison-region log-volume is
bounded by `(1+ε)·weight + θ + D`. -/
theorem gap2_regionVolume_bound {X : Type u} {W : IQHullLogVolumeInterface X}
    {epsilon : Real} (C : Cor312EpsilonArithmeticComparison W epsilon) :
    ∃ D : Real, ∀ a b c : Nat, IsABCTriple a b c →
      (W.logVolume (C.comparisonRegion a b c)).toReal ≤
        (1 + epsilon) * arithmeticWeight (abcRationalPoint a c) +
          (W.logVolume W.hull).toReal + D :=
  C.regionVolume_le_normalizedWeight

/-- Gap 2 consequence: the comparison-region log-volume is finite on ABC triples. -/
theorem gap2_regionVolume_lt_top {X : Type u} {W : IQHullLogVolumeInterface X}
    {epsilon : Real} (C : Cor312EpsilonArithmeticComparison W epsilon) :
    ∀ a b c : Nat, IsABCTriple a b c →
      W.logVolume (C.comparisonRegion a b c) < ⊤ :=
  C.comparisonRegion_logVolume_lt_top

/-- Gap 2 consequence: `.toReal` presentation is faithful (ofReal round-trip). -/
theorem gap2_ofReal_toReal {X : Type u} {W : IQHullLogVolumeInterface X}
    {epsilon : Real} (C : Cor312EpsilonArithmeticComparison W epsilon)
    {a b c : Nat} (habc : IsABCTriple a b c) :
    ENNReal.ofReal (W.logVolume (C.comparisonRegion a b c)).toReal =
      W.logVolume (C.comparisonRegion a b c) :=
  cor312ComparisonRegionVolume_ofReal_toReal C habc

/-- Gap 2 consumer: version-2 additive comparison data for every `ε` yields the
additive global contract. -/
theorem gap2_additive_contract {X : Type u} (W : IQHullLogVolumeInterface X)
    (Aeps : Real → Real)
    (hcomp : ∀ epsilon : Real, 0 < epsilon →
      Cor312EpsilonArithmeticComparisonAdditive W epsilon (Aeps epsilon)) :
    ABCHeightWeightAdditiveBoundV2 :=
  abcHeightWeightAdditiveBoundV2_of_epsilonComparisonAdditive W Aeps hcomp

#check gap2_regionVolume_bound
#check gap2_additive_contract

end LeanFormal.IUT.XiFPaper.Mzk1ABCEntryGap2QpilotActual
end
