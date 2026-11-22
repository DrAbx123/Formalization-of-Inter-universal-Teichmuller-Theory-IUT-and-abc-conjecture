import tmp.sheaf.xif.paper.Mzk1Gap1ScalingLawTargetActual

/-! # Gap1 wiring V2 (direct proof, no instance-sensitive call) -/

namespace LeanFormal.IUT.XiFPaper.Mzk1Gap1WiringV2ShaActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.Mzk1PaperComparisonRegionScalingActual
open LeanFormal.IUT.XiFPaper.Mzk1Gap1ScalingLawTargetActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))] [Nonempty (Bad (nativePlaceSelection T))]

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
        (1 + ε) * (s1902LogVolume T (paperComparisonRegion T point a b c)).toReal := by
  intro a b c habc
  rw [hvol a b c]
  rw [show Height.logHeight₁ (abcRationalPoint a c) = Real.log (c : Real) from
    abcRationalPoint_logHeight₁ habc]
  exact harith a b c habc

#print axioms gap1_wiring

end LeanFormal.IUT.XiFPaper.Mzk1Gap1WiringV2ShaActual
