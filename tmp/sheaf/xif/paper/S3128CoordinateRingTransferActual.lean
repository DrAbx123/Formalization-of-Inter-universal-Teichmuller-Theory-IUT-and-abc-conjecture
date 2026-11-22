import tmp.sheaf.xif.paper.S3119CoordinateRingForwardActual
import tmp.sheaf.xif.paper.S3128SignActionActual
import Mathlib.Algebra.Ring.Equiv
noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1348D6OrbicurveActual
open LeanFormal.IUT.XiFPaper.S3119CoordinateRingForwardActual
open LeanFormal.IUT.XiFPaper.S3128SignActionActual
open LeanFormal.IUT.XiFPaper.S3128SignRankTwoActual
open LeanFormal.IUT.XiFPaper.S3119NegInvolutionAttempt
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S3128CoordinateRingTransferActual
variable {l : PrimeGeFive}

noncomputable instance S3128CoordinateRing_isDomain : IsDomain (S1348CoordinateRing l) :=
  MulEquiv.isDomain (CR l) (S3119CoordinateRingEquiv l).toRingEquiv.toMulEquiv

theorem S3128CoordinateRingEquiv_x :
    S3119CoordinateRingEquiv l (S3128x l) =
      (Polynomial.X : Polynomial (K l)) • (1 : CR l) := by
  simp [S3119CoordinateRingEquiv, S3119Forward, S3119φ0, xCR, S3128x,
    Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk,
    WeierstrassCurve.Affine.CoordinateRing.smul,
    AdjoinRoot.algebraMap_eq, AdjoinRoot.mk_C]

noncomputable instance S3128AlgebraKXPullback :
    Algebra (Polynomial (K l)) (S1348CoordinateRing l) :=
  (((S3119CoordinateRingEquiv l).symm.toRingHom).comp
    (algebraMap (Polynomial (K l)) (CR l))).toAlgebra

noncomputable def S3128LinearEquiv :
    S1348CoordinateRing l ≃ₗ[Polynomial (K l)] CR l where
  toFun := S3119CoordinateRingEquiv l
  invFun := (S3119CoordinateRingEquiv l).symm
  left_inv x := by simp
  right_inv x := by simp
  map_add' x y := map_add _ _ _
  map_smul' c x := by
    rw [Algebra.smul_def, Algebra.smul_def, map_mul]
    congr 1
    change (S3119CoordinateRingEquiv l)
      ((S3119CoordinateRingEquiv l).symm
        ((algebraMap (Polynomial (K l)) (CR l)) c)) =
      (algebraMap (Polynomial (K l)) (CR l)) c
    simp

noncomputable def S3128Basis :
    Module.Basis (Fin 2) (Polynomial (K l)) (S1348CoordinateRing l) :=
  (WeierstrassCurve.Affine.CoordinateRing.basis (W l)).map
    S3128LinearEquiv.symm

noncomputable instance S3128ModuleFreeKX :
    Module.Free (Polynomial (K l)) (S1348CoordinateRing l) :=
  Module.Free.of_basis S3128Basis

noncomputable instance S3128ModuleFlatKX :
    Module.Flat (Polynomial (K l)) (S1348CoordinateRing l) :=
  Module.Flat.of_free

#check S3128ModuleFreeKX
#check S3128ModuleFlatKX
theorem S3128CoordinateRingEquiv_y :
    S3119CoordinateRingEquiv l (S3128y l) =
      WeierstrassCurve.Affine.CoordinateRing.mk (W l)
        (Polynomial.X : Polynomial (Polynomial (K l))) := by
  simp [S3119CoordinateRingEquiv, S3119Forward, S3119φ0, yCR, S3128y]

theorem S3128Basis_zero : S3128Basis (l := l) 0 = 1 := by
  change S3128LinearEquiv.symm
    (WeierstrassCurve.Affine.CoordinateRing.basis (W l) 0) = 1
  rw [WeierstrassCurve.Affine.CoordinateRing.basis_zero]
  simp [S3128LinearEquiv]

theorem S3128Basis_one : S3128Basis (l := l) 1 = S3128y l := by
  change S3128LinearEquiv.symm
    (WeierstrassCurve.Affine.CoordinateRing.basis (W l) 1) = S3128y l
  rw [WeierstrassCurve.Affine.CoordinateRing.basis_one]
  apply S3128LinearEquiv.injective
  rw [LinearEquiv.apply_symm_apply]
  rw [show S3128LinearEquiv (S3128y l) =
      S3119CoordinateRingEquiv l (S3128y l) from rfl]
  rw [← S3128CoordinateRingEquiv_y]

theorem S3128h2CR :
    (algebraMap (Polynomial (K l)) (CR l)) (2 : Polynomial (K l)) =
      (2 : CR l) := by
  rw [AdjoinRoot.algebraMap_eq]
  exact map_ofNat (AdjoinRoot.of (W l).polynomial) 2

theorem S3128h2A :
    (algebraMap (Polynomial (K l)) (S1348CoordinateRing l))
      (2 : Polynomial (K l)) = (2 : S1348CoordinateRing l) := by
  change (S3119CoordinateRingEquiv l).symm
    ((algebraMap (Polynomial (K l)) (CR l)) 2) = 2
  rw [S3128h2CR]
  exact map_ofNat (S3119CoordinateRingEquiv l).symm.toRingHom 2

theorem S3128X_smul_one :
    (Polynomial.X : Polynomial (K l)) • (1 : S1348CoordinateRing l) =
      S3128x l := by
  rw [Algebra.smul_def, mul_one]
  change (S3119CoordinateRingEquiv l).symm (xCR l) = S3128x l
  apply_fun (S3119CoordinateRingEquiv l) using (S3119CoordinateRingEquiv l).injective
  rw [AlgEquiv.apply_symm_apply, S3128CoordinateRingEquiv_x, xCR,
    Algebra.algebraMap_eq_smul_one]

theorem S3128t_ne_zero : S3128t (l := l) ≠ 0 := by
  intro h0
  have ht : S3128t (l := l) =
      (Polynomial.X : Polynomial (K l)) • S3128Basis (l := l) 0 +
        (2 : Polynomial (K l)) • S3128Basis (l := l) 1 := by
    rw [S3128Basis_zero, S3128Basis_one, S3128X_smul_one]
    rw [show (2 : Polynomial (K l)) • S3128y l = 2 * S3128y l from by
      rw [Algebra.smul_def, S3128h2A]]
    simp [S3128t]
    ring
  have hcoeff : (S3128Basis (l := l)).repr (S3128t (l := l)) 1 =
      (2 : Polynomial (K l)) := by
    rw [ht, map_add, map_smul, map_smul, Finsupp.add_apply,
      Finsupp.smul_apply, Finsupp.smul_apply]
    simp [S3128Basis.repr_self]
  have hzero : (S3128Basis (l := l)).repr (S3128t (l := l)) 1 = 0 := by
    rw [h0, map_zero]
    rfl
  have htwo : (2 : Polynomial (K l)) = 0 := by
    rw [← hcoeff, hzero]
  exact two_ne_zero htwo

theorem S3128CoordinateRingEquiv_aeval (p : Polynomial (K l)) :
    S3119CoordinateRingEquiv l (Polynomial.aeval (S3128x l) p) =
      (algebraMap (Polynomial (K l)) (CR l)) p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simp [map_add, hp, hq]
  | monomial n a =>
      rw [← Polynomial.C_mul_X_pow_eq_monomial]
      simp [Polynomial.aeval_X, Polynomial.aeval_mul,
        S3128CoordinateRingEquiv_x, Polynomial.C_eq_algebraMap]
      rw [show AdjoinRoot.of (W l).polynomial
          ((algebraMap (K l) (Polynomial (K l))) a) =
            algebraMap (K l) (CR l) a from by
        rw [← AdjoinRoot.algebraMap_eq,
          IsScalarTower.algebraMap_apply (K l) (Polynomial (K l)) (CR l)]]
      rw [show AdjoinRoot.of (W l).polynomial
          (Polynomial.X : Polynomial (K l)) =
            (Polynomial.X : Polynomial (K l)) • (1 : CR l) from by
        rw [← AdjoinRoot.algebraMap_eq, Algebra.algebraMap_eq_smul_one]]

theorem S3128Kx_smul_one (p : Polynomial (K l)) :
    p • (1 : S1348CoordinateRing l) = Polynomial.aeval (S3128x l) p := by
  rw [Algebra.smul_def, mul_one]
  change (S3119CoordinateRingEquiv l).symm
    ((algebraMap (Polynomial (K l)) (CR l)) p) =
    Polynomial.aeval (S3128x l) p
  rw [← S3128CoordinateRingEquiv_aeval]
  simp

theorem S3128SignGen_smul_eq_hom (a : S1348CoordinateRing l) :
    S3128SignGen • a = S3119NegQuotientHom (l := l) a := by
  rw [S3128Sign_smul_def, S3128SignSmul,
    if_neg S3128SignGen_ne_one]

theorem S3128NegQuotientHom_x :
    S3119NegQuotientHom (l := l) (S3128x l) = S3128x l := by
  simp [S3128x, S3119NegQuotientHom_mk, S3119NegPolyHom_X0]

theorem S3128SignGen_smul_algebraMap (a : K l) :
    S3128SignGen • (algebraMap (K l) (S1348CoordinateRing l) a) =
      algebraMap (K l) (S1348CoordinateRing l) a := by
  rw [S3128SignGen_smul_eq_hom]
  exact AlgHom.commutes (S3119NegQuotientHom (l := l)) a

theorem S3128SignGen_smul_Kx (p : Polynomial (K l)) :
    S3128SignGen • Polynomial.aeval (S3128x l) p =
      Polynomial.aeval (S3128x l) p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [Polynomial.aeval_add, S3128SignGen_smul_eq_hom, map_add]
      rw [show S3119NegQuotientHom (l := l)
            (Polynomial.aeval (S3128x l) p) = Polynomial.aeval (S3128x l) p from by
          rw [← S3128SignGen_smul_eq_hom]; exact hp]
      rw [show S3119NegQuotientHom (l := l)
            (Polynomial.aeval (S3128x l) q) = Polynomial.aeval (S3128x l) q from by
          rw [← S3128SignGen_smul_eq_hom]; exact hq]
  | monomial n a =>
      rw [← Polynomial.C_mul_X_pow_eq_monomial,
        Polynomial.aeval_mul, Polynomial.aeval_C]
      rw [show (Polynomial.aeval (S3128x l)) (Polynomial.X ^ n) =
          ((Polynomial.aeval (S3128x l)) Polynomial.X) ^ n from map_pow _ _ _]
      rw [Polynomial.aeval_X]
      rw [S3128SignGen_smul_eq_hom, map_mul, map_pow,
        AlgHom.commutes, S3128NegQuotientHom_x]

#check S3128SignGen_smul_Kx
#check S3128CoordinateRingEquiv_aeval
#check S3128Kx_smul_one
end LeanFormal.IUT.XiFPaper.S3128CoordinateRingTransferActual
end
