import tmp.sheaf.xif.paper.S1565AffineZSMulIdentitiesActual
import tmp.sheaf.xif.paper.S1535UniversalRecursionActual
/-! # S1569: corrected nonzero affine recursion
S1560AffineRecursion is false at n=0.  The corrected statement carries
n != 0 and the actual nonvanishing of polyToField psi_n.  It is proved
directly from the definitions of Universal.smulX/smulY.  The Z-coordinate
polynomial identities dblZ_smulPoly/addZ_smulPoly remain the exact first
missing auxiliary for dblXYZ_smulField/addXYZ_smulField. -/
noncomputable section
open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped Polynomial.Bivariate
namespace WeierstrassCurve.Universal
variable (n : ℤ)
/-- Corrected nonzero affine recursion, with the actual psi nonvanishing. -/
theorem s1569AffineRecursion_nonzero (_hn : n ≠ 0)
    (hψ : polyToField (curve.toAffine.ψ n) ≠ 0) :
    smulX n * (polyToField (curve.toAffine.ψ n)) ^ 2 =
      polyToField (curve.toAffine.φ n) ∧
    smulY n * (polyToField (curve.toAffine.ψ n)) ^ 3 =
      polyToField (curve.toAffine.ω n) := by
  constructor
  · rw [smulX_def]
    field_simp [hψ]
  · rw [smulY_def]
    field_simp [hψ]
/-- Exact first missing universal psi nonvanishing. -/
def S1569PsiNonzeroMissing : Prop :=
  ∀ n : ℤ, n ≠ 0 → polyToField (curve.toAffine.ψ n) ≠ 0
end WeierstrassCurve.Universal
end
