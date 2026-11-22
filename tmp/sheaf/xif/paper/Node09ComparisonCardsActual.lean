import LeanFormal.IUT.ABCBridge.Bridge.Cor312ComparisonGapReduction
import LeanFormal.IUT.ABCBridge.Bridge.Cor312ToABCBridgeInterface

noncomputable section
open LeanFormal.IUT

namespace LeanFormal.IUT.XiFPaper.Node09ComparisonCardsActual

universe u

/-- Exact paper-level input cards for the IV/ABC comparison: the two genuine
dictionary cards (weight volume and direct point volume) plus the reduced inputs
of the frozen gap reductions.  No field is derived from the carrier; all are
explicit paper-level inputs. -/
structure Node09ComparisonCards (X : Type u) (W : IQHullLogVolumeInterface X)
    (logShellPoint : Nat → Nat → Nat → X) (eps D₀ D₁ : ℝ) : Prop where
  heps : 0 ≤ eps
  hD₀ : 0 ≤ D₀
  hval : ∀ a b c : Nat, IsABCTriple a b c →
    ∀ q ∈ arithmeticPrimeSupport (abcRationalPoint a c),
      max 0 (-(padicValRat q (abcRationalPoint a c) : Real)) ≤ 1 + eps
  hweightvol : ∀ a b c : Nat, IsABCTriple a b c →
    arithmeticWeight (abcRationalPoint a c) ≤
      (W.logVolume (normalizedComparisonRegion W logShellPoint a b c)).toReal
  hunit : W.logVolume W.unitRegion ≤ W.logVolume W.hull + ENNReal.ofReal D₀
  hsplit : ∀ a b c : Nat, IsABCTriple a b c →
    W.logVolume (normalizedComparisonRegion W logShellPoint a b c) ≤
      W.logVolume (W.scaleShift '' W.unitRegion) +
        W.logVolume {W.scaleShift (logShellPoint a b c)}
  hptfin : ∀ a b c : Nat, IsABCTriple a b c →
    W.logVolume {W.scaleShift (logShellPoint a b c)} < ⊤
  hpoint : ∀ a b c : Nat, IsABCTriple a b c →
    (W.logVolume {W.scaleShift (logShellPoint a b c)}).toReal ≤
      (1 + eps) * arithmeticWeight (abcRationalPoint a c) + D₁

/-- The frozen epsilon comparison from the explicit cards. -/
def Node09ComparisonCards.toEpsilonComparison
    (X : Type u) (W : IQHullLogVolumeInterface X)
    (logShellPoint : Nat → Nat → Nat → X) (eps D₀ D₁ : Real)
    (I : Node09ComparisonCards X W logShellPoint eps D₀ D₁) :
    Cor312EpsilonArithmeticComparison W eps where
  logShellPoint := logShellPoint
  height_le_normalizedRegionVolume :=
    cor312Gap1_height_le_normalizedRegionVolume_of_weight_bound W logShellPoint
      I.heps I.hval I.hweightvol
  regionVolume_le_normalizedWeight :=
    cor312Gap2_regionVolume_le_normalizedWeight_of_split_pointBound_unitRegionBound
      W logShellPoint I.hD₀ I.hunit I.hsplit I.hptfin I.hpoint

/-- The full IV/ABC bridge interface from a family of explicit cards. -/
def Node09ComparisonCards.toCor312Interface
    (X : Type u) (W : IQHullLogVolumeInterface X)
    (logShellPoint : Nat → Nat → Nat → X)
    (Aeps : Real → Real) (D₀ : Real)
    (cards : ∀ eps : Real, 0 < eps →
      Node09ComparisonCards X W logShellPoint eps D₀ (Aeps eps)) :
    Cor312ToABCBridgeInterface where
  carrier := X
  hullData := W
  epsilonComparison := fun eps heps =>
    Node09ComparisonCards.toEpsilonComparison X W logShellPoint eps D₀ (Aeps eps)
      (cards eps heps)

/-- Exact reading of the direct point-volume card and the weight dictionary. -/
def Node09ComparisonCardsDoc : List String :=
  [ "direct point-volume card (hpoint): (logVolume {scaleShift (logShellPoint a b c)}).toReal <= (1+eps)*arithmeticWeight + D1; this is the replacement for the refuted point-height dictionary",
    "weight dictionary (hweightvol): arithmeticWeight <= normalizedComparisonRegion logVolume; genuine conditional input. The status theorem cor312GapDict_weightDictionary_not_universal assumes D+hdeg and is vacuous under the hull obstruction, so the actual-p dictionary is neither proved nor refuted here",
    "hsplit/hptfin: actual for the value-realized source interface in Cor312ComparisonGapSupplyLayer; abstract form kept as explicit fields here",
    "hunit: can be canonicalized to max D.degreeBound 0 in the source-interface assembly (cor312CarrierSpec_epsilonComparison_of_dictionaries)",
    "the two dictionaries (weight and point-height) are jointly refutable (cor312CarrierSpec_dictionaries_jointly_refutable); the direct point-volume card is not tied to height and is the paper-level input to use" ]

end LeanFormal.IUT.XiFPaper.Node09ComparisonCardsActual
