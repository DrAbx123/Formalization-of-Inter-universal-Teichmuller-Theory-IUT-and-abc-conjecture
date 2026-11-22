import LeanFormal.IUT.ABCBridge.Bridge.Cor312ToABCBridgeInterface
import LeanFormal.IUT.ABCBridge.Arithmetic.ABCHeightArithmeticWeightComparison
import LeanFormal.IUT.ABCBridge.Bridge.IUTToABC

/-!
  Mainline: T2 additive (contract v2) decomposition.  Same two-gap shape as
  Cor312ToABCBridgeInterface but with the version-2 additive height comparison
  (IUT IV Theorem A bounded-discrepancy form).  The two Props are the unproved
  paper links; the composition theorems consuming them are real proofs.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1T2AdditiveStatementActual

open LeanFormal.IUT

universe u

/-- Gap 1 additive (Thm A form): height <= (1+eps)*regionVolume + A, paper link. -/
def AdditiveHeightGap {X : Type u} (W : IQHullLogVolumeInterface X) (epsilon A : Real)
    (logShellPoint : Nat → Nat → Nat → X) : Prop :=
  ∀ a b c : Nat, IsABCTriple a b c →
    Height.logHeight₁ (abcRationalPoint a c) ≤
      (1 + epsilon) *
        (W.logVolume (normalizedComparisonRegion W logShellPoint a b c)).toReal + A

/-- Gap 2 (unchanged log-volume computation), paper link. -/
def AdditiveRegionWeightGap {X : Type u} (W : IQHullLogVolumeInterface X)
    (epsilon : Real) (logShellPoint : Nat → Nat → Nat → X) : Prop :=
  ∃ D : Real, ∀ a b c : Nat, IsABCTriple a b c →
    (W.logVolume (normalizedComparisonRegion W logShellPoint a b c)).toReal ≤
      (1 + epsilon) * arithmeticWeight (abcRationalPoint a c) +
        (W.logVolume W.hull).toReal + D

/-- Additive interface = named point + the two additive gap Props (structural). -/
theorem additive_gap_statement_iff {X : Type u} (W : IQHullLogVolumeInterface X)
    (epsilon A : Real) :
    Nonempty (Cor312EpsilonArithmeticComparisonAdditive W epsilon A) ↔
      ∃ p : Nat → Nat → Nat → X,
        AdditiveHeightGap W epsilon A p ∧ AdditiveRegionWeightGap W epsilon p := by
  constructor
  · rintro ⟨C⟩
    exact ⟨C.logShellPoint, C.height_le_normalizedRegionVolume_add,
      C.regionVolume_le_normalizedWeight⟩
  · rintro ⟨p, h1, h2⟩
    exact ⟨{ logShellPoint := p
             height_le_normalizedRegionVolume_add := h1
             regionVolume_le_normalizedWeight := h2 }⟩

/-- The additive comparison family yields the approved V2 contract. -/
theorem additiveV2_of_additiveFamily {X : Type u} (W : IQHullLogVolumeInterface X)
    (Aeps : Real → Real)
    (h : ∀ epsilon : Real, 0 < epsilon →
      Cor312EpsilonArithmeticComparisonAdditive W epsilon (Aeps epsilon)) :
    ABCHeightWeightAdditiveBoundV2 :=
  abcHeightWeightAdditiveBoundV2_of_epsilonComparisonAdditive W Aeps h

/-- And hence ABCConjecture (equivalence with V2 is proved). -/
theorem abcConjecture_of_additiveFamily {X : Type u} (W : IQHullLogVolumeInterface X)
    (Aeps : Real → Real)
    (h : ∀ epsilon : Real, 0 < epsilon →
      Cor312EpsilonArithmeticComparisonAdditive W epsilon (Aeps epsilon)) :
    ABCConjecture :=
  abcConjecture_iff_ABCHeightWeightAdditiveBoundV2.mpr
    (additiveV2_of_additiveFamily W Aeps h)

end LeanFormal.IUT.XiFPaper.Mzk1T2AdditiveStatementActual