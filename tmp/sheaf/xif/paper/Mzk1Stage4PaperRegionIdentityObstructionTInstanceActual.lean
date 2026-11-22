import tmp.sheaf.xif.paper.Mzk1Stage4PaperRegionIdentityObstructionActual
import tmp.sheaf.xif.paper.S1902ActualThetaHullActual

/-! # Mzk1Stage4PaperRegionIdentityObstructionTInstanceActual (stage4 lane; T-instance)

A628 module: the A618 obstruction instantiated at the concrete S1902 carrier T — under
identity scaling the comparison region is the fixed `unit ∪ {point}`, independent of the
ABC triple.  Canonical files only READ.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Stage4PaperRegionIdentityObstructionTInstanceActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.Mzk1Stage4PaperComparisonRegionScalingDesignActual
open LeanFormal.IUT.XiFPaper.Mzk1Stage4PaperRegionIdentityObstructionActual

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))] [Nonempty (Bad (nativePlaceSelection T))]

/-- S1902 T-instance: identity scaling gives the fixed region `unit ∪ {point}`. -/
theorem s1902_identity_region_eq (point : S1902Carrier T) (a b c : Nat) :
    region (identityScaling (S1902Carrier T) (s1902UnitRegion T) point) a b c =
      s1902UnitRegion T ∪ {point} :=
  identity_region_eq (S1902Carrier T) (s1902UnitRegion T) point a b c

/-- S1902 T-instance: the identity-scaling region does not depend on the triple. -/
theorem s1902_identity_region_independent (point : S1902Carrier T)
    (a b c a' b' c' : Nat) :
    region (identityScaling (S1902Carrier T) (s1902UnitRegion T) point) a b c =
      region (identityScaling (S1902Carrier T) (s1902UnitRegion T) point) a' b' c' :=
  identity_region_independent (S1902Carrier T) (s1902UnitRegion T) point a b c a' b' c'

#check s1902_identity_region_eq
#check s1902_identity_region_independent

end LeanFormal.IUT.XiFPaper.Mzk1Stage4PaperRegionIdentityObstructionTInstanceActual
end
