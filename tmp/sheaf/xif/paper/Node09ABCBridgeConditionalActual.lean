import LeanFormal.IUT.ABCBridge.Bridge.Cor312ToABCBridgeInterface
import tmp.sheaf.xif.paper.Node09FinalConditionalActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT

namespace LeanFormal.IUT.XiFPaper.Node09ABCBridgeConditionalActual

universe u

/-- The exact residual interface needed to consume the conditional paper312
endpoint in the IV/ABC bridge: the hull/finiteness carrier plus the two named
comparison gaps.  This is the same data as Cor312ToABCBridgeInterface; the
definition is kept here so the residual is explicit. -/
structure Node09ABCBridgeInterface where
  carrier : Type u
  hullData : IQHullLogVolumeInterface carrier
  epsilonComparison : ∀ epsilon : Real, 0 < epsilon →
    Cor312EpsilonArithmeticComparison hullData epsilon

/-- The frozen IV/ABC bridge interface built from the explicit residual data. -/
def Node09ABCBridgeInterface.toCor312 (I : Node09ABCBridgeInterface) :
    Cor312ToABCBridgeInterface where
  carrier := I.carrier
  hullData := I.hullData
  epsilonComparison := I.epsilonComparison

/-- The ABC-height-bound consequence of the explicit residual interface. -/
theorem Node09ABCBridgeInterface.heightBound (I : Node09ABCBridgeInterface) :
    ∀ epsilon : Real, 0 < epsilon → ∃ A : Real,
      ∀ a b c : Nat, IsABCTriple a b c →
        Height.logHeight₁ (abcRationalPoint a c) ≤
          (1 + epsilon) * arithmeticWeight (abcRationalPoint a c) + A :=
  cor312ToABCBridge_heightBound I.toCor312

/-- Exact missing link between our conditional paper312 endpoint and the IV/ABC
bridge interface. -/
def Node09ABCBridgeResidualMissing : List String :=
  [ "ExplicitPaper312Inequality gives the IUT-volume inequality A <= Lbar + Dbar; it does not mention the ABC height, arithmetic weight, the carrier, or the normalized comparison region",
    "missing dictionary: map the paper312 A/Lbar/Dbar sums to (logVolume (normalizedComparisonRegion W logShellPoint a b c)).toReal and to Height.logHeight / arithmeticWeight",
    "missing gap 1: height_le_normalizedRegionVolume (IUT IV arithmetic line-bundle comparison)",
    "missing gap 2: regionVolume_le_normalizedWeight (IUT IV main log-volume estimate with hull bound)",
    "the frozen consumer is LeanFormal.IUT.ABCBridge.Bridge.Cor312ToABCBridgeInterface; once its hullData and epsilonComparison fields are supplied, cor312ToABCBridge_heightBound applies with no further gap" ]

end LeanFormal.IUT.XiFPaper.Node09ABCBridgeConditionalActual
