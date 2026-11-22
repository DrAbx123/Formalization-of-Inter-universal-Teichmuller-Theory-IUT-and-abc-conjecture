import tmp.sheaf.xif.paper.Mzk1CanonicalDiagUncondFinalActual
/-! GAP-DET-HAAR step 3: B4 diagonal volume ratio -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1GapDetHaarDiagonalActual
open LeanFormal.IUT.XiFPaper.Mzk1CanonicalDiagUncondFinalActual
/-- B4 unconditional diagonal ratio donor. -/
def diagonalDonor : String := "canonical_diag_volume_ratio_uncond"
theorem diagonalDonor_eq : diagonalDonor = "canonical_diag_volume_ratio_uncond" := rfl
/-- Exact remaining bridge: diagonal ratio stated for the same Haar normalization as GL action. -/
def diagonalMissing : List String :=
  [ "diag p^e image of coordLattice = coordDual e",
    "same p2Haar normalization (addHaarMeasure coordinateCompacts)" ]
theorem diagonalMissing_length : diagonalMissing.length = 2 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1GapDetHaarDiagonalActual
end
