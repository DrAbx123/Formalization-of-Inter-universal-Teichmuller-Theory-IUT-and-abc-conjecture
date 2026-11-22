import tmp.sheaf.xif.paper.S3119PhiMatrixActual
import tmp.sheaf.xif.paper.S3119YDecompositionActual
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1348D6OrbicurveActual
open LeanFormal.IUT.XiFPaper.S3119AutoClassificationTargets
open LeanFormal.IUT.XiFPaper.S3119CoordinateRingForwardActual
open LeanFormal.IUT.XiFPaper.S3119YDecompositionActual
open LeanFormal.IUT.XiFPaper.S3119PowReduceActual
open LeanFormal.IUT.XiFPaper.S3119PhiMatrixActual
namespace LeanFormal.IUT.XiFPaper.S3119NormDegreeActual
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
variable {l : PrimeGeFive}

theorem S3119_equiv_phi_x0 (l : PrimeGeFive)
    (φ : S1348CoordinateRing l ≃ₐ[K l] S1348CoordinateRing l) :
    S3119CoordinateRingEquiv l (φ (S3119x0 (l := l))) =
      S3119Xp l φ • (1 : CR l) +
        S3119Xq l φ • AdjoinRoot.root (W l).polynomial := by
  rw [S3119Xp_spec (l := l) φ]
  rw [map_add, map_mul]
  simp only [S3119Equiv_Kx0, S3119Equiv_y0]
  congr 1
  · rw [show (AdjoinRoot.of (W l).polynomial) (S3119Xp l φ) =
        S3119Xp l φ • (1 : CR l) from by
      rw [WeierstrassCurve.Affine.CoordinateRing.smul, mul_one]
      rfl]
  · rw [Algebra.smul_def, AdjoinRoot.algebraMap_eq (f := (W l).polynomial)]

theorem S3119Norm_phi_x0_eq (l : PrimeGeFive)
    (φ : S1348CoordinateRing l ≃ₐ[K l] S1348CoordinateRing l) :
    S3119Norm l (φ (S3119x0 (l := l))) =
      Algebra.norm (Polynomial (K l))
        (S3119Xp l φ • (1 : CR l) +
          S3119Xq l φ • AdjoinRoot.root (W l).polynomial) := by
  unfold S3119Norm
  rw [S3119_equiv_phi_x0]

theorem S3119Norm_phi_x0_degree (l : PrimeGeFive)
    (φ : S1348CoordinateRing l ≃ₐ[K l] S1348CoordinateRing l) :
    (S3119Norm l (φ (S3119x0 (l := l)))).degree =
      max (2 • (S3119Xp l φ).degree) (2 • (S3119Xq l φ).degree + 3) := by
  rw [S3119Norm_phi_x0_eq]
  change (Algebra.norm (Polynomial (K l))
      (S3119Xp l φ • (1 : CR l) +
        S3119Xq l φ •
          (WeierstrassCurve.Affine.CoordinateRing.mk (W l)) Polynomial.X)).degree =
    max (2 • (S3119Xp l φ).degree) (2 • (S3119Xq l φ).degree + 3)
  rw [WeierstrassCurve.Affine.CoordinateRing.degree_norm_smul_basis]

#check S3119_equiv_phi_x0
#check S3119Norm_phi_x0_eq
#check S3119Norm_phi_x0_degree
#print axioms S3119Norm_phi_x0_degree
end LeanFormal.IUT.XiFPaper.S3119NormDegreeActual
end
