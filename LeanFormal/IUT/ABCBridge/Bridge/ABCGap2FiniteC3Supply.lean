import LeanFormal.IUT.ABCBridge.Bridge.Cor312ComparisonGapReduction
import LeanFormal.IUT.ABCBridge.Bridge.Cor312ComparisonGapSupplyLayer
import LeanFormal.IUT.ABCBridge.Bridge.ABCFrontierReductions

/-!
  # Finite / C3-side realized supply for gap 2 (`regionVolume_le_normalizedWeight`)

  This module feeds the already-proved value-realized supplies from
  `Cor312ComparisonGapSupplyLayer` into the gap-2 comparison
  `cor312Gap2_regionVolume_le_normalizedWeight_of_split_pointBound_unitRegionBound`.

  The two finite-side inputs are discharged by actual theorems:
  * `hsplit` from `cor312GapSupply_sourceInterface_hsplit`;
  * `hptfin` from `cor312GapSupply_sourceInterface_hptfin`.

  The normalization (`hunit`) and point-volume (`hpoint`) inputs remain explicit
  hypotheses, exactly as in the abstract comparison; no sorry/axiom is introduced.
-/
noncomputable section
open scoped BigOperators
namespace LeanFormal.IUT
universe ua uv upi umon ui
namespace ABCBridge
namespace FiniteC3Supply
open Theorem311Source
open Theorem311Source.OriginalInput

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
variable (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
variable (D : I.SourceUnitRegionHaarData v R n)
variable (p : Nat → Nat → Nat → I.ThetaPilotPoint v)
variable {eps D₀ D₁ : ℝ}

/-- Realized gap-2 `regionVolume_le_normalizedWeight`, with the finite/C3-side
inputs (`hsplit`, `hptfin`) supplied by actual theorems; only the unit-region
normalization and point-volume bounds remain as explicit hypotheses. -/
theorem ABCGap2RegionVolume_finiteC3
    (hD₀ : 0 ≤ D₀)
    (hunit : (I.sourceUnitRegionHaarInterface v R n D).logVolume
        (I.sourceUnitRegionHaarInterface v R n D).unitRegion ≤
      (I.sourceUnitRegionHaarInterface v R n D).logVolume
        (I.sourceUnitRegionHaarInterface v R n D).hull + ENNReal.ofReal D₀)
    (hpoint : ∀ a b c : Nat, IsABCTriple a b c →
      ((I.sourceUnitRegionHaarInterface v R n D).logVolume
        {(I.sourceUnitRegionHaarInterface v R n D).scaleShift (p a b c)}).toReal ≤
        (1 + eps) * arithmeticWeight (abcRationalPoint a c) + D₁) :
    ∃ Dbound : ℝ, ∀ a b c : Nat, IsABCTriple a b c →
      ((I.sourceUnitRegionHaarInterface v R n D).logVolume
        (normalizedComparisonRegion
          (I.sourceUnitRegionHaarInterface v R n D) p a b c)).toReal ≤
        (1 + eps) * arithmeticWeight (abcRationalPoint a c) +
          ((I.sourceUnitRegionHaarInterface v R n D).logVolume
            (I.sourceUnitRegionHaarInterface v R n D).hull).toReal + Dbound :=
  cor312Gap2_regionVolume_le_normalizedWeight_of_split_pointBound_unitRegionBound
    (I.sourceUnitRegionHaarInterface v R n D) p hD₀ hunit
    (fun a b c habc =>
      cor312GapSupply_sourceInterface_hsplit I v R n D p a b c habc)
    (fun a b c _ =>
      cor312GapSupply_sourceInterface_hptfin I v R n D p a b c)
    hpoint

#check ABCGap2RegionVolume_finiteC3
end FiniteC3Supply
end ABCBridge
end LeanFormal.IUT
end
