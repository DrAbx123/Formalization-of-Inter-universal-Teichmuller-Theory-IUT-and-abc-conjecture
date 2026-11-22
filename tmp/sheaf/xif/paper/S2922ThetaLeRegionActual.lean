import tmp.sheaf.xif.paper.S2919ThetaUpperFromProcession
import tmp.sheaf.xif.paper.S2833S2800HregionActual
import tmp.sheaf.xif.paper.S2781PointedLineBundleRegionActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2919ThetaUpperFromProcession
open LeanFormal.IUT.XiFPaper.S2833S2800HregionActual
open LeanFormal.IUT.XiFPaper.S2780LineBundleABCBridgeActual
open LeanFormal.IUT.XiFPaper.S2792NormalizedLineBundleBridge
open LeanFormal.IUT.XiFPaper.S2781PointedLineBundleRegionActual
open LeanFormal.IUT.XiFPaper.S2808S2800HalfNormalizedActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S2922ThetaLeRegionActual

/-- Direct theta_le_region with AJ equal to the certificate's thetaUpper:
the region term is nonnegative by S2833. -/
theorem S2922_theta_le_region
    (C : ThetaUpperCertificate)
    (heps : 0 <= 1 + C.eps)
    (a b c : Nat) (habc : IsABCTriple a b c) :
    C.thetaUpper <=
      6 * (1 + C.eps) * S2792RegionVolume a b c + C.thetaUpper := by
  have h0 : 0 <= S2780RegionVolume a b c := S2833_s_nonneg a b c habc
  have hV : 0 <= S2792RegionVolume a b c := by
    unfold S2792RegionVolume
    linarith
  have hterm : 0 <= 6 * (1 + C.eps) * S2792RegionVolume a b c :=
    mul_nonneg (mul_nonneg (by norm_num) heps) hV
  linarith

/-- The same bound with the actual S2833 hull volume:
6(1+eps) times the HalfIQHull normalized-region logVolume equals
6(1+eps) times S2792RegionVolume. -/
theorem S2922_theta_le_hull_volume
    (C : ThetaUpperCertificate)
    (heps : 0 <= 1 + C.eps)
    (a b c : Nat) (habc : IsABCTriple a b c) :
    C.thetaUpper <=
      6 * (1 + C.eps) *
        ((S2808HalfIQHull S2833l 1).logVolume
          (normalizedComparisonRegion (S2808HalfIQHull S2833l 1)
            (S2781LogShellPoint S2833l) a b c)).toReal + C.thetaUpper := by
  rw [S2833_region_volume a b c habc]
  exact S2922_theta_le_region C heps a b c habc

#check S2922_theta_le_region
#check S2922_theta_le_hull_volume
#print axioms S2922_theta_le_region
#print axioms S2922_theta_le_hull_volume

end LeanFormal.IUT.XiFPaper.S2922ThetaLeRegionActual
end