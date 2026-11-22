import LeanFormal.IUT.ABCBridge.Bridge.ABCFrontier
import tmp.sheaf.xif.paper.Node09ComparisonCardsActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Node09ComparisonCardsActual

namespace LeanFormal.IUT.XiFPaper.Node09CardsToFrontierActual

/-- A cards family (with existentially chosen constants) yields the explicit ABC
frontier: the two comparison clauses F4/F5 at the same carrier and point datum. -/
theorem frontier_of_cards
    (X : Type) (W : IQHullLogVolumeInterface X)
    (logShellPoint : Nat → Nat → Nat → X)
    (cards : ∀ (eps : Real) (_hε : 0 < eps),
      ∃ D₀ D₁ : Real, Node09ComparisonCards X W logShellPoint eps D₀ D₁) :
    ABCFrontier.{0} := by
  have hF4 : FrontierHeightComparisonClause W (fun _ _ => logShellPoint) := by
    intro eps hε a b c habc
    obtain ⟨D₀, D₁, I⟩ := cards eps hε
    exact cor312Gap1_height_le_normalizedRegionVolume_of_weight_bound
      W logShellPoint I.heps I.hval I.hweightvol a b c habc
  have hF5 : FrontierRegionComparisonClause W (fun _ _ => logShellPoint) := by
    intro eps hε
    obtain ⟨D₀, D₁, I⟩ := cards eps hε
    exact cor312Gap2_regionVolume_le_normalizedWeight_of_split_pointBound_unitRegionBound
      W logShellPoint I.hD₀ I.hunit I.hsplit I.hptfin I.hpoint
  exact ⟨X, W, fun _ _ => logShellPoint, hF4, hF5⟩

/-- Conditional ABC conjecture from the cards family. -/
theorem abcConjecture_of_cards
    (X : Type) (W : IQHullLogVolumeInterface X)
    (logShellPoint : Nat → Nat → Nat → X)
    (cards : ∀ (eps : Real) (_hε : 0 < eps),
      ∃ D₀ D₁ : Real, Node09ComparisonCards X W logShellPoint eps D₀ D₁) :
    ABCConjecture :=
  abcConjecture_of_frontier.{0} (frontier_of_cards X W logShellPoint cards)

/-- Exact paper-level input for the conditional ABC frontier. -/
def Node09CardsToFrontierResidual : List String :=
  [ "cards family: for every eps > 0, exists D0 D1 with Node09ComparisonCards X W logShellPoint eps D0 D1",
    "the cards family consists of the direct point-volume card, the weight dictionary, hval, hunit, hsplit, hptfin; no inhabitant is constructed",
    "frontier_of_cards builds ABCFrontier (F4/F5 at the same carrier/point), and abcConjecture_of_cards yields ABCConjecture conditionally; no unconditional claim" ]

end LeanFormal.IUT.XiFPaper.Node09CardsToFrontierActual
