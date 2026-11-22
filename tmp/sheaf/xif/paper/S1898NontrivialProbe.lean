import tmp.sheaf.xif.paper.S1898EllipticInvolutionActual
import tmp.sheaf.xif.paper.S1687Torsion23RealizationActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S1898NontrivialProbe

open CategoryTheory
open CategoryTheory.Bicategory
open AlgebraicGeometry
open scoped Pseudofunctor.StrongTrans
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1687Torsion23RealizationActual
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S1898EllipticInvolutionActual
open LeanFormal.IUT.XiFPaper.S1667AdmissibleCurveActual

theorem lifted_equation :
    S1726Curve.toAffine.Equation
      (S1720Lift (S1687Alpha S1687Y)) (S1720Lift S1687Y) := by
  have h : S1687AffineF.Equation (S1687Alpha S1687Y) S1687Y :=
    S1687Y_alpha_equation
  have h' : ((S1667Curve.toAffine).baseChange S1687Field).Equation
      (S1687Alpha S1687Y) S1687Y := by
    simpa [S1687AffineF, S1687CurveF] using h
  have h2 := WeierstrassCurve.Affine.Equation.baseChange
    (W := S1667Curve.toAffine) (f := S1720Lift) h'
  simpa [S1726Curve, S1726Curve_curve] using h2

theorem lifted_y_ne_zero : S1720Lift S1687Y ≠ 0 := by
  intro h
  exact S1687Y_ne_zero (S1720Lift.injective (by simpa using h))

theorem coordEndo_ne_id :
    S1898CoordEndo ≠ AlgHom.id S1726K S1726CoordinateRing := by
  intro h
  let ψ : S1726CoordinateRing →ₐ[S1726K] S1726K :=
    S1726PointAlgHom (S1720Lift (S1687Alpha S1687Y)) (S1720Lift S1687Y)
      lifted_equation
  have hψ : ψ.comp S1898CoordEndo = ψ := by
    rw [h, AlgHom.comp_id]
  have h2 := congrArg (fun φ : S1726CoordinateRing →ₐ[S1726K] S1726K =>
    φ (Ideal.Quotient.mk (Ideal.span {S1726AffinePolynomial})
      (MvPolynomial.X 1))) hψ
  rw [AlgHom.comp_apply, S1898CoordEndo_y, map_neg] at h2
  have hy : ψ (Ideal.Quotient.mk (Ideal.span {S1726AffinePolynomial})
      (MvPolynomial.X 1)) = S1720Lift S1687Y := by
    simp [ψ]
  rw [hy] at h2
  have h3 : (2 : S1726K) * S1720Lift S1687Y = 0 := by
    linear_combination -h2
  exact lifted_y_ne_zero ((mul_eq_zero.mp h3).resolve_left (by norm_num))

theorem affineEndo_ne_id : S1898AffineEndo ≠ 𝟙 S1726AffineOver := by
  intro h
  have hleft := congrArg
    (fun f : S1726AffineOver ⟶ S1726AffineOver => f.left) h
  change Spec.map (CommRingCat.ofHom S1898CoordEndo.toRingHom) =
    𝟙 (Spec (CommRingCat.of S1726CoordinateRing)) at hleft
  have hspec : Spec.map (CommRingCat.ofHom S1898CoordEndo.toRingHom) =
      Spec.map (𝟙 (CommRingCat.of S1726CoordinateRing)) := by
    simpa using hleft
  have hringCat : CommRingCat.ofHom S1898CoordEndo.toRingHom =
      𝟙 (CommRingCat.of S1726CoordinateRing) :=
    Spec.map_injective hspec
  have hring : S1898CoordEndo.toRingHom = RingHom.id S1726CoordinateRing :=
    congrArg CommRingCat.Hom.hom hringCat
  apply coordEndo_ne_id
  ext x
  exact congrArg (fun f : S1726CoordinateRing →+* S1726CoordinateRing => f x) hring

theorem ellipticInvolution_ne_id (l : PrimeGeFive) :
    S1898EllipticInvolution l ≠
      Pseudofunctor.StrongTrans.id S1898Stack := by
  intro h
  have h1 := congrArg
    (fun e : Pseudofunctor.StrongTrans S1898Stack S1898Stack =>
      (e.app (LocallyDiscrete.mk (Opposite.op S1726AffineOver))).toFunctor.obj
        (Discrete.mk (𝟙 S1726AffineOver))) h
  rw [S1898EllipticInvolution_app_affine] at h1
  have hid : (Pseudofunctor.StrongTrans.id S1898Stack).app
      (LocallyDiscrete.mk (Opposite.op S1726AffineOver)) =
      𝟙 (S1898Stack.obj (LocallyDiscrete.mk (Opposite.op S1726AffineOver))) := rfl
  rw [hid, Cat.Hom.id_toFunctor] at h1
  exact affineEndo_ne_id (congrArg Discrete.as h1)

end LeanFormal.IUT.XiFPaper.S1898NontrivialProbe

end