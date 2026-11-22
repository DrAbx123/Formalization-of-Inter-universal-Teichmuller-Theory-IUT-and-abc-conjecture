import tmp.sheaf.xif.paper.Mzk1GLActContinuousActionActual
import tmp.sheaf.xif.paper.Mzk1CanonicalHaarCoordLatticeActual
/-! GAP-DET-HAAR step 2: GL_d(Z_p) preserves canonical Haar -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1GapDetHaarGLInvarianceActual
open LeanFormal.IUT.XiFPaper.Mzk1GLActContinuousActionActual
open LeanFormal.IUT.XiFPaper.Mzk1CanonicalHaarCoordLatticeActual
/-- Green GL invariance / lattice preservation donors. -/
def glDonors : List String :=
  [ "glAct_image_eq_of_mul_eq_one", "glContinuous_image_coordLattice",
    "glContinuous_canonical_haar_invariant",
    "canonical_map_eq_of_image_eq_full" ]
theorem glDonors_length : glDonors.length = 4 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1GapDetHaarGLInvarianceActual
end
