import tmp.sheaf.xif.paper.Node09CardsToFrontierActual
import tmp.sheaf.xif.paper.Node09SingletonPointCardsActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Node09ComparisonCardsActual
open LeanFormal.IUT.XiFPaper.Node09SingletonPointCardsActual
open LeanFormal.IUT.XiFPaper.Node09CardsToFrontierActual

namespace LeanFormal.IUT.XiFPaper.Node09SingletonFinalActual

/-- A singleton cards family (existential constants) yields the ABC frontier. -/
theorem frontier_of_singleton_cards
    (X : Type) (W : IQHullLogVolumeInterface X)
    (logShellPoint : Nat → Nat → Nat → X)
    (cards : ∀ (eps : Real) (_hε : 0 < eps),
      ∃ D₀ D₁ : Real, Node09SingletonPointCards X W logShellPoint eps D₀ D₁) :
    ABCFrontier.{0} :=
  frontier_of_cards X W logShellPoint (fun eps hε => by
    obtain ⟨D₀, D₁, I⟩ := cards eps hε
    exact ⟨D₀, D₁, I.toComparisonCards X W logShellPoint eps D₀ D₁⟩)

/-- Singleton point-volume cards yield the conditional ABC conjecture. -/
theorem abcConjecture_of_singleton_cards
    (X : Type) (W : IQHullLogVolumeInterface X)
    (logShellPoint : Nat → Nat → Nat → X)
    (cards : ∀ (eps : Real) (_hε : 0 < eps),
      ∃ D₀ D₁ : Real, Node09SingletonPointCards X W logShellPoint eps D₀ D₁) :
    ABCConjecture :=
  abcConjecture_of_frontier.{0} (frontier_of_singleton_cards X W logShellPoint cards)

/-- Singleton point-volume cards yield the final ABC height bound. -/
theorem final_abcHeightBound_of_singleton_cards
    (X : Type) (W : IQHullLogVolumeInterface X)
    (logShellPoint : Nat → Nat → Nat → X)
    (cards : ∀ (eps : Real) (_hε : 0 < eps),
      ∃ D₀ D₁ : Real, Node09SingletonPointCards X W logShellPoint eps D₀ D₁) :
    ∀ epsilon : Real, 0 < epsilon → ∃ A : Real,
      ∀ a b c : Nat, IsABCTriple a b c →
        Height.logHeight₁ (abcRationalPoint a c) ≤
          (1 + epsilon) * arithmeticWeight (abcRationalPoint a c) + A :=
  cor312ToABCBridge_heightBound
    (bridgeInterface_of_frontier
      (frontier_of_singleton_cards X W logShellPoint cards))

/-- Exact paper-level input for the singleton route. -/
def Node09SingletonFinalResidual : List String :=
  [ "hweight_le_singleton: ofReal (arithmeticWeight x) <= logVolume {scaleShift (logShellPoint a b c)}",
    "reduction of hweight_le_singleton: on the value-realized carrier the singleton volume is sourceSetVolume of the point, and cor312GapDict_singletonVolume_toReal_eq_max identifies its toReal with max (sourceLocalLogDegree) 0; the weight dictionary arithmeticWeight <= sourceLocalLogDegree (Cor312GapDictionaryLayer.cor312GapDict_weightDictionary_iff_scalingSeparated) then gives the ENNReal lower bound by ofReal monotonicity",
    "hsingleton_le_weight: (logVolume {scaleShift (logShellPoint a b c)}).toReal <= (1+eps)*arithmeticWeight + D1",
    "reduction of hsingleton_le_weight: by cor312GapDict_singletonVolume_toReal_le_iff it is equivalent to the untruncated degree upper bound sourceLocalLogDegree v (scaleShift point) <= (1+eps)*arithmeticWeight + D1; this is the direct degree/point-volume estimate, not a height comparison",
    "P7 report section 9.1/9.2 gives the q-ideal product-region volume V(J_q;C_q) = -sum n f log p (weighted M_q), but no singleton point-volume donor: one must compare the point singleton to the product region and to arithmeticWeight, which is the paper-level IUT IV estimate",
    "hregion_fin, hval, hunit, hsplit, hptfin are reduced inputs; hsplit/hptfin are actual for the value-realized source interface, hunit can be canonicalized, hregion_fin follows from region finiteness",
    "no inhabitant is constructed; this is a conditional bridge only" ]

end LeanFormal.IUT.XiFPaper.Node09SingletonFinalActual
