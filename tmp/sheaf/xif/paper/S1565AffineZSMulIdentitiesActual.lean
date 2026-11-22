import tmp.sheaf.xif.paper.S1560ZSMulPointFormulaFromOmegaActual
import tmp.sheaf.xif.paper.S1521OmegaInvariantCancellationActual
import tmp.sheaf.xif.paper.S1535UniversalRecursionActual
/-! # S1565: omega eval actual; affine recursion target is FALSE at n=0
S1521's omega_spec specializes to the concrete S1560OmegaEvalIdentity.
The S1560AffineRecursion target is refuted at n = 0: smulX 0 = 0, psi_0 = 0,
but phi_0 = 1, so its first conjunct reads 0 = 1.  A corrected recursion must
carry n != 0 (and psi_n != 0).  The dblXYZ/addXYZ identities are not proved
here; their exact first auxiliary is the universal psi-nonzero lemma plus the
Z-coordinate polynomial identities from TauCeti ZSMul.lean.  No fake identity. -/
noncomputable section
open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped Polynomial.Bivariate
namespace LeanFormal.IUT.XiFPaper.S1565AffineZSMulIdentitiesActual
universe u
open LeanFormal.IUT.XiFPaper.S1560ZSMulPointFormulaFromOmegaActual
variable {F : Type u} [Field F] (W : WeierstrassCurve.Affine F)
/-- S1521 `ω_spec` evaluated at a concrete point. -/
theorem s1565OmegaEvalIdentity : S1560OmegaEvalIdentity W := by
  intro x y n
  have h := congrArg (fun p : F[X][Y] => Polynomial.evalEval x y p)
      (W.ω_spec n)
  have h2 : Polynomial.evalEval x y (2 : F[X][Y]) = (2 : F) := by
    simpa using Polynomial.evalEval_natCast x y 2
  simp only [Polynomial.evalEval_add, Polynomial.evalEval_mul, Polynomial.evalEval_pow,
    Polynomial.evalEval_C] at h
  rw [h2] at h
  simpa using h
/-- The S1560 affine recursion is false at n = 0. -/
theorem s1565AffineRecursion_false :
    ¬ S1560AffineRecursion := by
  intro h
  have h0 := h.1 0
  rw [WeierstrassCurve.Universal.smulX_def,
      WeierstrassCurve.Universal.polyToField, WeierstrassCurve.φ_zero,
      WeierstrassCurve.ψ_zero] at h0
  simpa using h0
-- Exact first missing for dblXYZ/addXYZ:
-- Universal.polyToField_ψ_ne_zero and the Z-coordinate polynomial identities
-- (TauCeti dblZ_smulPoly/addZ_smulPoly), then dblXYZ_smulField/addXYZ_smulField.
end LeanFormal.IUT.XiFPaper.S1565AffineZSMulIdentitiesActual
