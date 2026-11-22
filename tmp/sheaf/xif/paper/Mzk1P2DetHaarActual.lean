import Mathlib.Tactic

/-! # P2 determinant-Haar work item

The general p-adic determinant-Haar law is not closed in this batch.
This file records the exact remaining work items and the donor theorem names
already present in the tree; it does not assert the law as an interface.

Donors present:
* glContinuous_canonical_haar_invariant
  (Mzk1GLActContinuousActionActual)
* canonical_diag_volume_ratio_uncond
  (Mzk1CanonicalDiagUncondFinalActual)
* general_snf_volume_ratio
  (Mzk1GeneralSNFVolume3Actual)
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1P2DetHaarActual

/-- Exact missing steps for the general det-Haar law. -/
def detHaarMissing : List String :=
  [ "SNF decomposition B = U * diag(p^e) * W with U,W in GL_d(Z_p) for arbitrary B in GL_d(Q_p)",
    "diagonal p^e lattice volume ratio for the canonical additive Haar in the same normalization as the GL action",
    "Haar scalar uniqueness after SNF: identify the scalar with the norm of det B",
    "NOTE: scalar factor = coordLattice image mass and lattice-preserving scalar=1 are now green in Mzk1P2DetHaarProofActual" ]

theorem detHaarMissing_length : detHaarMissing.length = 4 := rfl

/-- Donor theorem names, for the next batch. -/
def detHaarDonors : List String :=
  [ "Mzk1GLActContinuousActionActual.glContinuous_canonical_haar_invariant",
    "Mzk1CanonicalDiagUncondFinalActual.canonical_diag_volume_ratio_uncond",
    "Mzk1GeneralSNFVolume3Actual.general_snf_volume_ratio" ]

theorem detHaarDonors_length : detHaarDonors.length = 3 := rfl

#check detHaarMissing
#check detHaarDonors
end LeanFormal.IUT.XiFPaper.Mzk1P2DetHaarActual
end
