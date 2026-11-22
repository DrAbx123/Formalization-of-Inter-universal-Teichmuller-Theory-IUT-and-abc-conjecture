import tmp.sheaf.xif.paper.Mzk1P2DetHaarProofActual
import tmp.sheaf.xif.paper.Mzk1GapDetHaarSNFActual
import tmp.sheaf.xif.paper.Mzk1GapDetHaarGLInvarianceActual
import tmp.sheaf.xif.paper.Mzk1GapDetHaarDiagonalActual
import tmp.sheaf.xif.paper.Mzk1GapDetHaarScalarActual
/-! GAP-DET-HAAR final assembly status -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1GapDetHaarFinalActual
def detHaarFinalRows : List String :=
  [ "scalar factor = coordLattice image mass (green)",
    "GL_d(Zp) ratio 1 (green donor)",
    "diagonal p^e ratio B4 (green donor)",
    "SNF decomposition of arbitrary GL_d(Qp) (missing)",
    "composition of scalar/GL/diagonal factors (missing)" ]
theorem detHaarFinalRows_length : detHaarFinalRows.length = 5 := rfl
def detHaarFinalMissing : List String :=
  [ "SNF decomposition U diag W", "composition of Haar scalars" ]
theorem detHaarFinalMissing_length : detHaarFinalMissing.length = 2 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1GapDetHaarFinalActual
end
