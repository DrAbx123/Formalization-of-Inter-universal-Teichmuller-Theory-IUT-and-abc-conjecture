import LeanFormal.IUT.ABCBridge.Bridge.Cor312ComparisonGapReduction
import tmp.sheaf.xif.paper.Node09ComparisonCardsActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Node09ComparisonCardsActual

namespace LeanFormal.IUT.XiFPaper.Node09SingletonPointCardsActual

universe u

/-- Singleton point-volume cards: a two-sided comparison between the scaled point
singleton volume and the arithmetic weight, plus finiteness of the comparison
region.  This is the direct point-volume route (no height dictionary). -/
structure Node09SingletonPointCards (X : Type u) (W : IQHullLogVolumeInterface X)
    (logShellPoint : Nat → Nat → Nat → X) (eps D₀ D₁ : Real) : Prop where
  heps : 0 ≤ eps
  hD₀ : 0 ≤ D₀
  hval : ∀ a b c : Nat, IsABCTriple a b c →
    ∀ q ∈ arithmeticPrimeSupport (abcRationalPoint a c),
      max 0 (-(padicValRat q (abcRationalPoint a c) : Real)) ≤ 1 + eps
  hunit : W.logVolume W.unitRegion ≤ W.logVolume W.hull + ENNReal.ofReal D₀
  hsplit : ∀ a b c : Nat, IsABCTriple a b c →
    W.logVolume (normalizedComparisonRegion W logShellPoint a b c) ≤
      W.logVolume (W.scaleShift '' W.unitRegion) +
        W.logVolume {W.scaleShift (logShellPoint a b c)}
  hptfin : ∀ a b c : Nat, IsABCTriple a b c →
    W.logVolume {W.scaleShift (logShellPoint a b c)} < ⊤
  hregion_fin : ∀ a b c : Nat, IsABCTriple a b c →
    W.logVolume (normalizedComparisonRegion W logShellPoint a b c) < ⊤
  hweight_le_singleton : ∀ a b c : Nat, IsABCTriple a b c →
    ENNReal.ofReal (arithmeticWeight (abcRationalPoint a c)) ≤
      W.logVolume {W.scaleShift (logShellPoint a b c)}
  hsingleton_le_weight : ∀ a b c : Nat, IsABCTriple a b c →
    (W.logVolume {W.scaleShift (logShellPoint a b c)}).toReal ≤
      (1 + eps) * arithmeticWeight (abcRationalPoint a c) + D₁

/-- The singleton point-volume cards yield the comparison cards: the weight
dictionary follows from the singleton lower bound and region finiteness, while
the direct point-volume card is the singleton upper bound. -/
def Node09SingletonPointCards.toComparisonCards
    (X : Type u) (W : IQHullLogVolumeInterface X)
    (logShellPoint : Nat → Nat → Nat → X) (eps D₀ D₁ : Real)
    (I : Node09SingletonPointCards X W logShellPoint eps D₀ D₁) :
    Node09ComparisonCards X W logShellPoint eps D₀ D₁ where
  heps := I.heps
  hD₀ := I.hD₀
  hval := I.hval
  hunit := I.hunit
  hsplit := I.hsplit
  hptfin := I.hptfin
  hweightvol := by
    intro a b c habc
    have hENN :=
      cor312Gap1_weight_le_normalizedRegionVolume_of_singletonVolume
        W logShellPoint I.hweight_le_singleton a b c habc
    have hle : (ENNReal.ofReal (arithmeticWeight (abcRationalPoint a c))).toReal ≤
        (W.logVolume (normalizedComparisonRegion W logShellPoint a b c)).toReal :=
      ENNReal.toReal_mono (ne_of_lt (I.hregion_fin a b c habc)) hENN
    rwa [ENNReal.toReal_ofReal (arithmeticWeight_nonneg _)] at hle
  hpoint := I.hsingleton_le_weight

/-- Exact paper-level reading of the singleton point-volume route. -/
def Node09SingletonPointCardsDoc : List String :=
  [ "hweight_le_singleton: ofReal (arithmeticWeight x) <= logVolume {scaleShift (logShellPoint a b c)}",
    "hsingleton_le_weight: (logVolume {scaleShift (logShellPoint a b c)}).toReal <= (1+eps)*arithmeticWeight + D1",
    "hregion_fin: logVolume of normalizedComparisonRegion < top, used only to convert the lower bound to toReal",
    "this route replaces the refuted point-height dictionary by a two-sided point-volume/weight comparison; the cards family is then obtained by toComparisonCards",
    "remaining paper-level input: the two singleton inequalities plus hval/hunit/hsplit/hptfin; no inhabitant is constructed" ]

end LeanFormal.IUT.XiFPaper.Node09SingletonPointCardsActual
