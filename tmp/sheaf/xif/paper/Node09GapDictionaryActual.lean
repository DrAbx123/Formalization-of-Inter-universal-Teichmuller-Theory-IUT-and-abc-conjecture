import LeanFormal.IUT.ABCBridge.Bridge.Cor312ComparisonGapReduction
import LeanFormal.IUT.ABCBridge.Bridge.Cor312ComparisonGapSupplyLayer

noncomputable section
open LeanFormal.IUT

namespace LeanFormal.IUT.XiFPaper.Node09GapDictionaryActual

universe u

/-- Gap 1 in conditional reduced form: from the valuation bound and the named
weight-versus-region-volume comparison. -/
theorem gap1_of_weight_bound {X : Type u}
    (W : IQHullLogVolumeInterface X) (logShellPoint : Nat → Nat → Nat → X)
    {eps : Real} (heps : 0 ≤ eps)
    (hval : ∀ a b c : Nat, IsABCTriple a b c →
      ∀ q ∈ arithmeticPrimeSupport (abcRationalPoint a c),
        max 0 (-(padicValRat q (abcRationalPoint a c) : Real)) ≤ 1 + eps)
    (hweightvol : ∀ a b c : Nat, IsABCTriple a b c →
      arithmeticWeight (abcRationalPoint a c) ≤
        (W.logVolume (normalizedComparisonRegion W logShellPoint a b c)).toReal) :
    ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤
        (1 + eps) *
          (W.logVolume (normalizedComparisonRegion W logShellPoint a b c)).toReal :=
  cor312Gap1_height_le_normalizedRegionVolume_of_weight_bound W logShellPoint heps hval hweightvol

/-- Gap 2 in conditional reduced form: from unit-region normalization, split,
point finiteness and point-volume inputs. -/
theorem gap2_of_inputs {X : Type u}
    (W : IQHullLogVolumeInterface X) (logShellPoint : Nat → Nat → Nat → X)
    {eps D₀ D₁ : Real} (hD₀ : 0 ≤ D₀)
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
    ∃ D : Real, ∀ a b c : Nat, IsABCTriple a b c →
      (W.logVolume (normalizedComparisonRegion W logShellPoint a b c)).toReal ≤
        (1 + eps) * arithmeticWeight (abcRationalPoint a c) +
          (W.logVolume W.hull).toReal + D :=
  cor312Gap2_regionVolume_le_normalizedWeight_of_split_pointBound_unitRegionBound
    W logShellPoint hD₀ hunit hsplit hptfin hpoint

/-- Exact missing dictionary between the conditional paper312 endpoint and the
IV/ABC comparison interface. -/
def Node09GapDictionaryMissing : List String :=
  [ "no direct map: ExplicitPaper312Inequality is the IUT-volume inequality A <= Lbar + Dbar, not a statement about the carrier, ABC height, arithmetic weight, or normalizedComparisonRegion",
    "gap 1 is reduced by Cor312ComparisonGapReduction.cor312Gap1_height_le_normalizedRegionVolume_of_weight_bound to: valuation bound hval + weight-versus-region-volume comparison hweightvol; the latter is not derivable (negative calibration cor312Gap1_exists_carrier_arithmeticWeight_gt_normalizedComparisonRegionVolume)",
    "gap 2 is reduced by Cor312ComparisonGapReduction.cor312Gap2_regionVolume_le_normalizedWeight_of_split_pointBound_unitRegionBound to hunit + hsplit + hptfin + hpoint",
    "hsplit and hptfin are supplied for the value-realized source interface by Cor312ComparisonGapSupplyLayer.cor312GapSupply_sourceInterface_hsplit / _hptfin",
    "hunit (unit-region normalization) and hpoint (point-volume/height comparison) remain paper-level open inputs; hweightvol has no abstract supply (negative calibration)",
    "to consume final_paper312_conditional in the IV/ABC bridge one must additionally supply IFQHullLogVolumeInterface carrier, the point datum logShellPoint, and the dictionary mapping A/Lbar/Dbar to the normalized region log-volume and Height.logHeight/arithmeticWeight" ]

end LeanFormal.IUT.XiFPaper.Node09GapDictionaryActual
