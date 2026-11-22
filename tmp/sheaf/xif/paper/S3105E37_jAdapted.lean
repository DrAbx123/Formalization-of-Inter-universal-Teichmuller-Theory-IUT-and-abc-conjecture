import tmp.sheaf.xif.paper.S2801D6FaithfulActual
import LeanFormal.IUT.IUTI.InitialTheta.ConcreteArithmeticExample

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.XiFPaper.S2801D6FaithfulActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S3105E37_jAdapted

abbrev K := GaussianField

/-- E37 curve base-changed to the Gaussian field. -/
noncomputable def E37Base : WeierstrassCurve K :=
  (S2801E37Curve ℚ).map (algebraMap ℚ K)

theorem S3105E37_delta : (S2801E37Curve ℚ).Δ = (64 : ℚ) := by
  norm_num [S2801E37Curve, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

instance : (S2801E37Curve ℚ).IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, S3105E37_delta]
  norm_num

theorem S3105E37_jAdapted_rat : (S2801E37Curve ℚ).j = (1728 : ℚ) := by
  norm_num [S2801E37Curve, WeierstrassCurve.j, WeierstrassCurve.c₄,
    WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

theorem S3105E37_jAdapted : E37Base.j = (1728 : K) := by
  change ((S2801E37Curve ℚ).map (algebraMap ℚ K)).j = (1728 : K)
  rw [WeierstrassCurve.map_j, S3105E37_jAdapted_rat]
  norm_num

#check S3105E37_jAdapted
#print axioms S3105E37_jAdapted

end LeanFormal.IUT.XiFPaper.S3105E37_jAdapted
end
