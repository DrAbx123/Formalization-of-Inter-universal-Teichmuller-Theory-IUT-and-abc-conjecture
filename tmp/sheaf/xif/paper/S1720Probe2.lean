import tmp.sheaf.xif.paper.S1708NinePointInjectionActual
import LeanFormal.IUT.Foundations.Geometry.ReductionBaseChange
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

set_option backward.isDefEq.respectTransparency false

noncomputable section
open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open LeanFormal.IUT

namespace Probe2

open PuncturedEllipticCurve

theorem torsion23Rational_baseChange
    {k K : Type*} [Field k] [Field K] [Algebra k K] [Algebra.IsAlgebraic k K]
    (X : PuncturedEllipticCurve k)
    (h : PuncturedEllipticCurve.Torsion23Rational X) :
    PuncturedEllipticCurve.Torsion23Rational (X.baseChange K) := by
  classical
  letI : CommRing (AlgebraicClosure k) := (AlgebraicClosure.instField k).toCommRing
  letI : CommRing (AlgebraicClosure K) := (AlgebraicClosure.instField K).toCommRing
  let e : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure K :=
    IsAlgClosure.equiv k (AlgebraicClosure k) (AlgebraicClosure K)
  have hcurve : ((X.curve.toAffine⁄K)⁄(AlgebraicClosure K)) = (X.curve.toAffine⁄(AlgebraicClosure K)) := by
    change (X.curve.toAffine⁄K).map
      ((IsScalarTower.toAlgHom k K (AlgebraicClosure K) : K →ₐ[k] AlgebraicClosure K) :
        K →+* AlgebraicClosure K) = X.curve.toAffine⁄(AlgebraicClosure K)
    rw [WeierstrassCurve.Affine.map_baseChange]
  intro P hP
  change ((X.curve.toAffine⁄K)⁄(AlgebraicClosure K)).Point at P
  cases hcurve
  let P0 := Affine.Point.map (W' := X.curve.toAffine)
    (e.symm : AlgebraicClosure K →ₐ[k] AlgebraicClosure k) P
  have hP0 : (6 : ℤ) • P0 = 0 := by
    dsimp only [P0]
    rw [← AddMonoidHom.map_zsmul, hP, AddMonoidHom.map_zero]
  obtain ⟨Q, hQ⟩ := h P0 hP0
  refine ⟨Affine.Point.baseChange (W' := X.curve.toAffine) k K Q, ?_⟩
  have hmap : Affine.Point.map (W' := X.curve.toAffine)
      (e : AlgebraicClosure k →ₐ[k] AlgebraicClosure K)
      (Affine.Point.baseChange (W' := X.curve.toAffine) k (AlgebraicClosure k) Q) = P := by
    rw [hQ]
    dsimp only [P0]
    rw [Affine.Point.map_map]
    have hcomp : (e : AlgebraicClosure k →ₐ[k] AlgebraicClosure K).comp
        (e.symm : AlgebraicClosure K →ₐ[k] AlgebraicClosure k) =
        AlgHom.id k (AlgebraicClosure K) := by
      ext x
      simp
    rw [hcomp]
    exact Affine.Point.map_id (W' := X.curve.toAffine) P
  have hA : Affine.Point.baseChange (W' := X.curve.toAffine) K (AlgebraicClosure K)
        (Affine.Point.baseChange (W' := X.curve.toAffine) k K Q) =
      Affine.Point.map (W' := X.curve.toAffine)
        (Algebra.ofId k (AlgebraicClosure K)) Q := by
    rw [Affine.Point.baseChange, Affine.Point.baseChange, Affine.Point.map_map]
    congr 1
    ext x
    simp
  rw [hA, ← hmap]
  congr 1
  ext x
  simp

end Probe2
