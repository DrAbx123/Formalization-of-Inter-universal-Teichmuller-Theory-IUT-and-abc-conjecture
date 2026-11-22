import tmp.sheaf.xif.paper.Mzk1Gap1ScalingLawTargetActual

/-! # Gap1 wiring: scaling law + arithmetic -> Gap1 (thin consumer) -/

namespace LeanFormal.IUT.XiFPaper.Mzk1Gap1WiringShaActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.Mzk1PaperComparisonRegionScalingActual
open LeanFormal.IUT.XiFPaper.Mzk1Gap1ScalingLawTargetActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))] [Nonempty (Bad (nativePlaceSelection T))]

/-- Gap1 wiring: exact paper-region scaling law + arithmetic inequality imply Gap1. -/
theorem gap1_wiring
    (point : Nat → Nat → Nat → S1902Carrier T)
    (ratio : Nat → Nat → Nat → Real) (const ε : Real) (hε : 0 < ε)
    (hvol : PaperRegionScalingLaw T point ratio const)
    (harith : forall a b c : Nat, IsABCTriple a b c →
      Real.log (c : Real) ≤
        (1 + ε) * ((s1902LogVolume T (s1902UnitRegion T)).toReal +
          Real.log (ratio a b c) + const)) :
    forall a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤
        (1 + ε) * (s1902LogVolume T (paperComparisonRegion T point a b c)).toReal :=
  gap1_of_scalingLaw_and_arith (T := T) point ratio const ε hε hvol harith

#print axioms gap1_wiring

end LeanFormal.IUT.XiFPaper.Mzk1Gap1WiringShaActual
