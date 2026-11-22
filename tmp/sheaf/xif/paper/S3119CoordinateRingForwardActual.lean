import tmp.sheaf.xif.paper.S1348D6OrbicurveActual
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1348D6OrbicurveActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open MvPolynomial
namespace LeanFormal.IUT.XiFPaper.S3119CoordinateRingForwardActual
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

abbrev K (l : PrimeGeFive) := S1348K l
abbrev W (l : PrimeGeFive) : WeierstrassCurve.Affine (K l) :=
  (S1348Curve l).toAffine
abbrev CR (l : PrimeGeFive) := (W l).CoordinateRing

/-- X-coordinate in Mathlib's AdjoinRoot model. -/
noncomputable def xCR (l : PrimeGeFive) : CR l :=
  algebraMap (Polynomial (K l)) (CR l) Polynomial.X

/-- Y-coordinate (the AdjoinRoot root) in Mathlib's model. -/
noncomputable def yCR (l : PrimeGeFive) : CR l :=
  AdjoinRoot.root (W l).polynomial

/-- The evaluation map from the two-variable polynomial ring to the AdjoinRoot
coordinate ring. -/
noncomputable def S3119φ0 (l : PrimeGeFive) :
    MvPolynomial (Fin 2) (K l) →ₐ[K l] CR l :=
  MvPolynomial.aeval ![xCR l, yCR l]














lemma S3119φ0_mk (l : PrimeGeFive) :
    S3119φ0 l (S1348AffinePolynomial l) =
      AdjoinRoot.mk (W l).polynomial (W l).polynomial := by
  rw [← AdjoinRoot.aeval_eq (f := (W l).polynomial)]
  rw [Polynomial.aeval_def]
  have hp : (W l).polynomial =
      Polynomial.X ^ 2
        + Polynomial.C (Polynomial.C (W l).a₁ * Polynomial.X + Polynomial.C (W l).a₃)
            * Polynomial.X
        - Polynomial.C (Polynomial.X ^ 3 + Polynomial.C (W l).a₂ * Polynomial.X ^ 2
            + Polynomial.C (W l).a₄ * Polynomial.X + Polynomial.C (W l).a₆) := rfl
  simp only [hp, S3119φ0, xCR, yCR, S1348AffinePolynomial, weierstrassAffinePolynomial,
    MvPolynomial.aeval_X, MvPolynomial.aeval_C, map_add, map_mul, map_pow, map_sub,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_add, Polynomial.eval₂_mul,
    Polynomial.eval₂_sub, Polynomial.eval₂_pow, Matrix.cons_val_zero, Matrix.cons_val_one]
  simp only [Polynomial.C_eq_algebraMap]
  simp only [← IsScalarTower.algebraMap_apply (K l) (Polynomial (K l)) (CR l)]
  ring_nf


theorem S3119φ0_relation (l : PrimeGeFive) :
    S3119φ0 l (S1348AffinePolynomial l) = 0 := by
  rw [S3119φ0_mk, AdjoinRoot.mk_self]


noncomputable def S3119Forward (l : PrimeGeFive) :
    S1348CoordinateRing l →ₐ[K l] CR l :=
  Ideal.Quotient.liftₐ (Ideal.span {S1348AffinePolynomial l}) (S3119φ0 l) (by
    intro x hx
    rw [Ideal.mem_span_singleton] at hx
    rcases hx with ⟨c, rfl⟩
    rw [map_mul, S3119φ0_relation, zero_mul])







@[simp] lemma S3119_aeval_coe_apply (l : PrimeGeFive) (p : Polynomial (K l)) :
    (↑(Polynomial.aeval (R := K l) (A := S1348CoordinateRing l)
        (Ideal.Quotient.mk (Ideal.span {S1348AffinePolynomial l}) (MvPolynomial.X 0))) :
      Polynomial (K l) → S1348CoordinateRing l) p =
    Polynomial.eval₂
      (algebraMap (K l) (S1348CoordinateRing l))
      (Ideal.Quotient.mk (Ideal.span {S1348AffinePolynomial l}) (MvPolynomial.X 0)) p := by
  rw [Polynomial.aeval_def]


@[simp] lemma S3119_aeval_coe_ringHom_apply (l : PrimeGeFive) (p : Polynomial (K l)) :
    (Polynomial.aeval (R := K l) (A := S1348CoordinateRing l)
        (Ideal.Quotient.mk (Ideal.span {S1348AffinePolynomial l}) (MvPolynomial.X 0)) :
      Polynomial (K l) →+* S1348CoordinateRing l) p =
    Polynomial.eval₂
      (algebraMap (K l) (S1348CoordinateRing l))
      (Ideal.Quotient.mk (Ideal.span {S1348AffinePolynomial l}) (MvPolynomial.X 0)) p := by
  change (Polynomial.aeval (R := K l) (A := S1348CoordinateRing l)
      (Ideal.Quotient.mk (Ideal.span {S1348AffinePolynomial l}) (MvPolynomial.X 0))) p =
    Polynomial.eval₂ (algebraMap (K l) (S1348CoordinateRing l))
      (Ideal.Quotient.mk (Ideal.span {S1348AffinePolynomial l}) (MvPolynomial.X 0)) p
  rw [Polynomial.aeval_def]


noncomputable def S3119Backward (l : PrimeGeFive) :
    CR l →ₐ[K l] S1348CoordinateRing l :=
  AdjoinRoot.liftAlgHom
    ((W l).polynomial)
    (Polynomial.aeval (R := K l) (A := S1348CoordinateRing l)
      (Ideal.Quotient.mk (Ideal.span {S1348AffinePolynomial l}) (MvPolynomial.X 0)))
    (Ideal.Quotient.mk (Ideal.span {S1348AffinePolynomial l}) (MvPolynomial.X 1))
    (by
      have h : Polynomial.eval₂
          (↑(Polynomial.aeval (R := K l) (A := S1348CoordinateRing l)
            (Ideal.Quotient.mk (Ideal.span {S1348AffinePolynomial l}) (MvPolynomial.X 0))))
          (Ideal.Quotient.mk (Ideal.span {S1348AffinePolynomial l}) (MvPolynomial.X 1))
          (W l).polynomial =
          Ideal.Quotient.mk (Ideal.span {S1348AffinePolynomial l}) (S1348AffinePolynomial l) := by
        rw [show (W l).polynomial =
            Polynomial.X ^ 2
              + Polynomial.C (Polynomial.C (W l).a₁ * Polynomial.X + Polynomial.C (W l).a₃)
                  * Polynomial.X
              - Polynomial.C (Polynomial.X ^ 3 + Polynomial.C (W l).a₂ * Polynomial.X ^ 2
                  + Polynomial.C (W l).a₄ * Polynomial.X + Polynomial.C (W l).a₆) from rfl]
        simp only [Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_add,
          Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
          S3119_aeval_coe_ringHom_apply]
        simp only [← Ideal.Quotient.mk_algebraMap]
        conv_lhs => simp only [← map_add, ← map_mul, ← map_sub, ← map_pow]
        congr 1
        simp only [S1348AffinePolynomial, weierstrassAffinePolynomial,
          MvPolynomial.C_eq_algebraMap]
        ring
      rw [h, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.subset_span (Set.mem_singleton _))



noncomputable def S3119CoordinateRingEquiv (l : PrimeGeFive) :
    S1348CoordinateRing l ≃ₐ[K l] CR l :=
  AlgEquiv.ofAlgHom (S3119Forward l) (S3119Backward l) (by
    apply AdjoinRoot.algHom_ext'
    · apply Polynomial.algHom_ext
      simp [S3119Forward, S3119Backward, S3119φ0, xCR, yCR,
        Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk,
        AdjoinRoot.liftAlgHom_of, AdjoinRoot.liftAlgHom_root,
        AdjoinRoot.algebraMap_eq, Polynomial.aeval_X]
    · simp [S3119Forward, S3119Backward, S3119φ0, xCR, yCR,
        Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk,
        AdjoinRoot.liftAlgHom_of, AdjoinRoot.liftAlgHom_root,
        AdjoinRoot.algebraMap_eq, Polynomial.aeval_X]) (by
    apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;>
      simp [S3119Forward, S3119Backward, S3119φ0, xCR, yCR,
        Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk,
        AdjoinRoot.liftAlgHom_of, AdjoinRoot.liftAlgHom_root,
        AdjoinRoot.algebraMap_eq, Polynomial.aeval_X])


noncomputable def S3119Norm (l : PrimeGeFive) (x : S1348CoordinateRing l) :
    Polynomial (K l) :=
  Algebra.norm (Polynomial (K l)) (S3119CoordinateRingEquiv l x)

theorem S3119Norm_X0 (l : PrimeGeFive) :
    S3119Norm l (Ideal.Quotient.mk (Ideal.span {S1348AffinePolynomial l})
      (MvPolynomial.X 0)) = Polynomial.X ^ 2 := by
  unfold S3119Norm
  have hval : S3119CoordinateRingEquiv l
      (Ideal.Quotient.mk (Ideal.span {S1348AffinePolynomial l}) (MvPolynomial.X 0)) =
      (Polynomial.X : Polynomial (K l)) • (1 : CR l) := by
    simp [S3119CoordinateRingEquiv, S3119Forward, S3119φ0, xCR,
      Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk,
      WeierstrassCurve.Affine.CoordinateRing.smul,
      AdjoinRoot.algebraMap_eq, AdjoinRoot.mk_C]
  rw [hval]
  have h := WeierstrassCurve.Affine.CoordinateRing.norm_smul_basis
    (W' := W l) (p := (Polynomial.X : Polynomial (K l))) (q := 0)
  simpa using h

#check S3119Norm
#check S3119Norm_X0

def S3119NormDegreeTwoTarget (l : PrimeGeFive) : Prop :=
  ∀ φ : S1348CoordinateRing l ≃ₐ[K l] S1348CoordinateRing l,
    (S3119Norm l (φ (Ideal.Quotient.mk (Ideal.span {S1348AffinePolynomial l})
      (MvPolynomial.X 0)))).degree ≤ 2

#check S3119NormDegreeTwoTarget

#print axioms S3119Norm_X0

#check S3119CoordinateRingEquiv
#print axioms S3119CoordinateRingEquiv

#check S3119Backward
#print axioms S3119Backward

#check S3119_aeval_coe_ringHom_apply

#check S3119_aeval_coe_apply

#check S3119Forward
#print axioms S3119Forward

#check S3119φ0_relation
#print axioms S3119φ0_relation

#check S3119φ0_mk
#print axioms S3119φ0_mk

def S3119φ0_relation_target (l : PrimeGeFive) : Prop :=
  S3119φ0 l (S1348AffinePolynomial l) = 0

#check S3119φ0_relation_target
end LeanFormal.IUT.XiFPaper.S3119CoordinateRingForwardActual
end
