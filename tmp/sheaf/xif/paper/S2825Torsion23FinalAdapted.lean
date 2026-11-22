import tmp.sheaf.xif.paper.S2815TorsionPrepActual
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2809E6FiniteActual
open LeanFormal.IUT.XiFPaper.S2790F6Actual
open WeierstrassCurve
open WeierstrassCurve.Affine
noncomputable section
local instance : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩
local instance : DecidableEq S2790F6 := Classical.decEq S2790F6
local instance : DecidableEq L1 := Classical.decEq L1
local instance : DecidableEq S2790L := Classical.decEq S2790L
local instance : Nontrivial L1 := inferInstance
local instance : Nontrivial S2790L := inferInstance
local instance : XL1.curve.IsElliptic := inferInstance
local instance : S2790EL.curve.IsElliptic := inferInstance
set_option maxHeartbeats 8000000

theorem S2825_torsion23 :
    PuncturedEllipticCurve.Torsion23Rational (S2790E.baseChange S2790F6) := by
  intro P hP
  rcases P with _ | ⟨x, y, hns⟩
  · refine ⟨0, ?_⟩
    change (WeierstrassCurve.Affine.Point.map (W' := XF6.curve.toAffine)
      (Algebra.ofId S2790F6 L1)) (0 : (XF6.curve.toAffine⁄S2790F6).Point) = 0
    rw [WeierstrassCurve.Affine.Point.map_zero]
  · have hxmem : S2815Equiv x ∈ S2790CoordSet :=
      S2815coord_mem (WeierstrassCurve.Affine.Point.some x y hns) hP (by simp [S2815PointCoords])
    have hymem : S2815Equiv y ∈ S2790CoordSet :=
      S2815coord_mem (WeierstrassCurve.Affine.Point.some x y hns) hP (by simp [S2815PointCoords])
    have hxsub : S2790CoordSet ⊆ (S2790F6 : Set S2790L) :=
      IntermediateField.subset_adjoin GaussianField S2790CoordSet
    let x0 : S2790F6 := ⟨S2815Equiv x, hxsub hxmem⟩
    let y0 : S2790F6 := ⟨S2815Equiv y, hxsub hymem⟩
    have hxeq : algebraMap S2790F6 L1 x0 = x := by
      apply S2815Equiv.injective
      rw [S2815Equiv.commutes]
      rfl
    have hyeq : algebraMap S2790F6 L1 y0 = y := by
      apply S2815Equiv.injective
      rw [S2815Equiv.commutes]
      rfl
    have hns' : (S2790E.baseChange L1).curve.toAffine.Nonsingular x y :=
      S2815_hns_align x y hns
    have hns0 : XF6.curve.toAffine.Nonsingular x0 y0 := by
      have halign : (S2790E.baseChange L1).curve.toAffine.Nonsingular
          (algebraMap S2790F6 L1 x0) (algebraMap S2790F6 L1 y0) := by
        simpa [hxeq, hyeq] using hns'
      have hcomp : (algebraMap S2790F6 L1).comp (algebraMap GaussianField S2790F6) =
          algebraMap GaussianField L1 := by
        apply RingHom.ext
        intro z
        exact IsScalarTower.algebraMap_apply GaussianField S2790F6 L1 z
      exact (WeierstrassCurve.Affine.baseChange_nonsingular
        (W := XF6.curve.toAffine) (f := Algebra.ofId S2790F6 L1)
        (Algebra.ofId S2790F6 L1).injective x0 y0).mp (by
          simpa [WeierstrassCurve.map_map, hcomp, PuncturedEllipticCurve.baseChange,
            WeierstrassCurve.baseChange] using halign)
    have hW : (XF6.curve.toAffine⁄S2790F6) = XF6.curve.toAffine := by
      simp [XF6, PuncturedEllipticCurve.baseChange, WeierstrassCurve.baseChange]
    have hns0' : (XF6.curve.toAffine⁄S2790F6).Nonsingular x0 y0 := hW ▸ hns0
    let Q : (XF6.curve.toAffine⁄S2790F6).Point :=
      WeierstrassCurve.Affine.Point.some x0 y0 hns0'
    refine ⟨Q, ?_⟩
    have hV : (XF6.curve.toAffine⁄L1) = XL1.curve.toAffine := by
      simp [XF6, XL1, PuncturedEllipticCurve.baseChange, WeierstrassCurve.baseChange]
    change (WeierstrassCurve.Affine.Point.map (W' := XF6.curve.toAffine)
      (Algebra.ofId S2790F6 L1)) Q = WeierstrassCurve.Affine.Point.some x y hns
    rw [WeierstrassCurve.Affine.Point.map_some]
    cases hV
    change WeierstrassCurve.Affine.Point.some (algebraMap S2790F6 L1 x0)
      (algebraMap S2790F6 L1 y0) _ = WeierstrassCurve.Affine.Point.some x y hns
    rw [hxeq, hyeq]
    congr
    exact Subsingleton.elim _ _