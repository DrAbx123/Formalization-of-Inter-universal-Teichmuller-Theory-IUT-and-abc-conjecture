import tmp.sheaf.xif.paper.Node09ComparisonCardsActual

noncomputable section
open LeanFormal.IUT

namespace LeanFormal.IUT.XiFPaper.Node09FinalABCBridgeActual

universe u

/-- Final conditional theorem: a family of explicit comparison cards yields the
ABC height bound through the frozen Cor 3.12 -> ABC consumer. -/
theorem final_abcHeightBound_of_cards
    (X : Type u) (W : IQHullLogVolumeInterface X)
    (logShellPoint : Nat → Nat → Nat → X)
    (Aeps : Real → Real) (D₀ : Real)
    (cards : ∀ eps : Real, 0 < eps →
      LeanFormal.IUT.XiFPaper.Node09ComparisonCardsActual.Node09ComparisonCards
        X W logShellPoint eps D₀ (Aeps eps)) :
    ∀ epsilon : Real, 0 < epsilon → ∃ A : Real,
      ∀ a b c : Nat, IsABCTriple a b c →
        Height.logHeight₁ (abcRationalPoint a c) ≤
          (1 + epsilon) * arithmeticWeight (abcRationalPoint a c) + A :=
  cor312ToABCBridge_heightBound
    (LeanFormal.IUT.XiFPaper.Node09ComparisonCardsActual.Node09ComparisonCards.toCor312Interface
      X W logShellPoint Aeps D₀ cards)

/-- Exact remaining paper-level input for the final conditional theorem. -/
def Node09FinalABCBridgeResidual : List String :=
  [ "the only remaining input is the cards family: for every eps > 0, a Node09ComparisonCards X W logShellPoint eps D0 (Aeps eps)",
    "the cards encode the direct point-volume card (logVolume {scaleShift (logShellPoint a b c)}).toReal <= (1+eps)*arithmeticWeight + D1 and the weight dictionary arithmeticWeight <= normalizedComparisonRegion logVolume, plus the reduced hval/hunit/hsplit/hptfin inputs",
    "no inhabitant is constructed and no axiom is introduced; the dictionaries are jointly refutable (cor312CarrierSpec_dictionaries_jointly_refutable), so the direct point-volume card is the intended paper-level replacement",
    "once the cards family is supplied, final_abcHeightBound_of_cards closes the ABC height bound through cor312ToABCBridge_heightBound with no additional gap" ]

end LeanFormal.IUT.XiFPaper.Node09FinalABCBridgeActual
