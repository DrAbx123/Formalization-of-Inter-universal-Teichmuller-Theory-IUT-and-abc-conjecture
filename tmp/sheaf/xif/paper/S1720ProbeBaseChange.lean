import tmp.sheaf.xif.paper.S1720SourceArithmeticActual

set_option backward.isDefEq.respectTransparency false

noncomputable section
open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open LeanFormal.IUT

namespace ProbeBaseChange

open PuncturedEllipticCurve

def pc {F : Type} [Field F] [DecidableEq F] {W₁ W₂ : WeierstrassCurve F}
    (h : W₁ = W₂) : W₁.toAffine.Point → W₂.toAffine.Point :=
  fun P => h ▸ P

theorem pc_zero {F : Type} [Field F] [DecidableEq F] {W₁ W₂ : WeierstrassCurve F}
    (h : W₁ = W₂) : pc h (0 : W₁.toAffine.Point) = 0 := by
  cases h
  rfl

theorem pc_zsmul {F : Type} [Field F] [DecidableEq F] {W₁ W₂ : WeierstrassCurve F}
    (h : W₁ = W₂) (n : ℤ) (P : W₁.toAffine.Point) :
    pc h (n • P) = n • pc h P := by
  cases h
  rfl

theorem pc_inj {F : Type} [Field F] [DecidableEq F] {W₁ W₂ : WeierstrassCurve F}
    (h : W₁ = W₂) : Function.Injective (pc h) := by
  cases h
  exact fun _ _ h => h

theorem torsion23Rational_baseChange
    {k K : Type} [Field k] [Field K] [Algebra k K] [Algebra.IsAlgebraic k K]
    (X : PuncturedEllipticCurve k)
    (h : PuncturedEllipticCurve.Torsion23Rational X) :
    PuncturedEllipticCurve.Torsion23Rational (X.baseChange K) := by
  classical
  letI : CommRing (AlgebraicClosure k) := (AlgebraicClosure.instField k).toCommRing
  letI : CommRing (AlgebraicClosure K) := (AlgebraicClosure.instField K).toCommRing
  let e : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure K :=
    IsAlgClosure.equiv k (AlgebraicClosure k) (AlgebraicClosure K)
  let W := X.curve.toAffine
  have hcurve : ((W⁄K)⁄(AlgebraicClosure K)) = (W⁄(AlgebraicClosure K)) := by
    change (W⁄K).map
      ((IsScalarTower.toAlgHom k K (AlgebraicClosure K) : K →ₐ[k] AlgebraicClosure K) :
        K →+* AlgebraicClosure K) = W⁄(AlgebraicClosure K)
    rw [WeierstrassCurve.Affine.map_baseChange]
  intro P hP
  change ((W⁄K)⁄(AlgebraicClosure K)).Point at P
  let P' : (W⁄(AlgebraicClosure K)).Point := pc hcurve P
  have hP' : (6 : ℤ) • P' = 0 := by
    dsimp only [P']
    rw [← pc_zsmul hcurve 6 P, hP, pc_zero]
  let P0 := Affine.Point.map (W' := W)
    (e.symm : AlgebraicClosure K →ₐ[k] AlgebraicClosure k) P'
  have hP0 : (6 : ℤ) • P0 = 0 := by
    dsimp only [P0]
    rw [← AddMonoidHom.map_zsmul, hP', AddMonoidHom.map_zero]
  obtain ⟨Q, hQ⟩ := h P0 hP0
  refine ⟨Affine.Point.baseChange (W' := W) k K Q, ?_⟩
  apply pc_inj hcurve
  have hleft : pc hcurve
      (Affine.Point.baseChange (W' := W) K (AlgebraicClosure K)
        (Affine.Point.baseChange (W' := W) k K Q)) =
      Affine.Point.baseChange (W' := W) k (AlgebraicClosure K) Q := by
    dsimp only [pc]
    cases hcurve
    rw [Affine.Point.baseChange, Affine.Point.baseChange, Affine.Point.baseChange,
      Affine.Point.map_map]
    congr 1
    ext x
    simp
  rw [hleft]
  change Affine.Point.baseChange (W' := W) k (AlgebraicClosure K) Q = P'
  have hbase : Affine.Point.baseChange (W' := W) k (AlgebraicClosure K) Q =
      Affine.Point.map (W' := W) (e : AlgebraicClosure k →ₐ[k] AlgebraicClosure K)
        (Affine.Point.baseChange (W' := W) k (AlgebraicClosure k) Q) := by
    rw [Affine.Point.baseChange, Affine.Point.baseChange, Affine.Point.map_map]
    congr 1
    ext x
    simp
  rw [hbase, hQ]
  change Affine.Point.map (W' := W) (e : AlgebraicClosure k →ₐ[k] AlgebraicClosure K)
    (Affine.Point.map (W' := W)
      (e.symm : AlgebraicClosure K →ₐ[k] AlgebraicClosure k) P') = P'
  rw [Affine.Point.map_map]
  have hcomp : (e : AlgebraicClosure k →ₐ[k] AlgebraicClosure K).comp
      (e.symm : AlgebraicClosure K →ₐ[k] AlgebraicClosure k) =
      AlgHom.id k (AlgebraicClosure K) := by
    ext x
    simp
  rw [hcomp]
  exact Affine.Point.map_id (W' := W) P'

end ProbeBaseChange
