import tmp.sheaf.xif.paper.S2828PointRealizationActual
import tmp.sheaf.xif.paper.S2801E37ProjectiveClosure
import tmp.sheaf.xif.paper.S2789E37OrbicurveSignActual
import tmp.sheaf.xif.paper.S2814bE37ChartZOverActual

noncomputable section
open WeierstrassCurve LeanFormal.IUT CategoryTheory AlgebraicGeometry
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2829E37GaussianPointActual

open LeanFormal.IUT.XiFPaper.S2801D6FaithfulActual
open LeanFormal.IUT.XiFPaper.S2801E37ProjectiveClosure
open LeanFormal.IUT.XiFPaper.S2813E37TwoFPointsActual
open LeanFormal.IUT.XiFPaper.S2814E37ChartPointsActual
open LeanFormal.IUT.XiFPaper.S2814bE37ChartZOverActual
open LeanFormal.IUT.XiFPaper.S2789E37OrbicurveSignActual
open LeanFormal.IUT.XiFPaper.S2828PointRealizationActual

abbrev K : Type := S2789Arithmetic.F
local instance : Field K := S2789Arithmetic.fieldF
local instance : DecidableEq K := Classical.decEq _

noncomputable def S2829Curve : WeierstrassCurve K := S2801E37Curve K

theorem S2829_discriminant : S2829Curve.Δ = 37 := by
  norm_num [S2829Curve, S2801E37Curve, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

instance S2829_isElliptic : S2829Curve.IsElliptic :=
  ⟨isUnit_iff_ne_zero.mpr (by rw [S2829_discriminant]; norm_num)⟩

noncomputable def S2829ChartZOver (x y : K)
    (h : y ^ 2 + y = x ^ 3 - x) :
    S2813Base K ⟶ S2801E37AsOver K :=
  Over.homMk (E37ChartZSchemePoint K x y h) (by
    change Spec.map (CommRingCat.ofHom (E37ChartZPoint K x y h)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap K (S2801E37CoordinateRing K))) = 𝟙 _
    have hring :
        (CommRingCat.ofHom (algebraMap K (S2801E37CoordinateRing K))) ≫
          (CommRingCat.ofHom (E37ChartZPoint K x y h)) =
        CommRingCat.ofHom (RingHom.id K) := by
      ext c
      exact congrArg (fun f => f c) (E37ChartZPoint_comp_algebraMap K x y h)
    rw [← Spec.map_comp, hring]
    simp)


theorem S2829InfinityEval_comp_algebraMap :
    (E37InfinityEval K).comp (algebraMap K (E37ChartYRing K)) = RingHom.id K := by
  ext c
  change (E37InfinityEval K) ((Ideal.Quotient.mk (E37ChartYIdeal K))
    (MvPolynomial.C c)) = c
  unfold E37InfinityEval
  rw [Ideal.Quotient.lift_mk]
  simp [E37InfinityPolynomialEval]

noncomputable def S2829ChartYInfinityOver :
    S2813Base K ⟶ E37ChartYAsOver K :=
  Over.homMk (Spec.map (CommRingCat.ofHom (E37InfinityEval K))) (by
    change Spec.map (CommRingCat.ofHom (E37InfinityEval K)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap K (E37ChartYRing K))) = 𝟙 _
    have hring :
        (CommRingCat.ofHom (algebraMap K (E37ChartYRing K))) ≫
          (CommRingCat.ofHom (E37InfinityEval K)) =
        CommRingCat.ofHom (RingHom.id K) := by
      ext c
      exact congrArg (fun f => f c) (S2829InfinityEval_comp_algebraMap)
    rw [← Spec.map_comp, hring]
    simp)

#check S2829InfinityEval_comp_algebraMap
#check S2829ChartYInfinityOver
#print axioms S2829ChartYInfinityOver


noncomputable def S2829ZOverToAffinePoint
    (z : S2813Base K ⟶ S2801E37AsOver K) :
    S2829Curve.toAffine.Point := by
  let f := S2828_chartZHom K z.left
  have hEq : S2829Curve.toAffine.Equation
      (f (S2801E37X K)) (f (S2801E37Y K)) :=
    S2828_chartZ_equation K z.left
  haveI : (S2829Curve.toAffine).IsElliptic := S2829_isElliptic
  exact WeierstrassCurve.Affine.Point.some
    (f (S2801E37X K)) (f (S2801E37Y K))
    ((WeierstrassCurve.Affine.equation_iff_nonsingular
      (W := S2829Curve.toAffine)
      (x := f (S2801E37X K)) (y := f (S2801E37Y K))).mp hEq)

noncomputable def S2829ZOverToProjectivePoint
    (z : S2813Base K ⟶ S2801E37AsOver K) :
    S2829Curve.toProjective.Point :=
  (WeierstrassCurve.Projective.Point.toAffineAddEquiv
    S2829Curve.toProjective).symm (S2829ZOverToAffinePoint z)

noncomputable def S2829PointMap :
    ((S2813Base K ⟶ S2801E37AsOver K) ⊕
      (S2813Base K ⟶ E37ChartYAsOver K)) → S2829Curve.toProjective.Point
  | Sum.inl z => S2829ZOverToProjectivePoint z
  | Sum.inr _ => 0

#check S2829ZOverToAffinePoint
#check S2829ZOverToProjectivePoint
#check S2829PointMap
#print axioms S2829ZOverToAffinePoint


theorem S2829_chartZHom_chartZSchemePoint (x y : K)
    (h : y ^ 2 + y = x ^ 3 - x) :
    S2828_chartZHom K (E37ChartZSchemePoint K x y h) =
      E37ChartZPoint K x y h := by
  simp [S2828_chartZHom, E37ChartZSchemePoint]

theorem S2829ZOver_roundtrip (x y : K)
    (h : y ^ 2 + y = x ^ 3 - x) :
    S2829ZOverToAffinePoint (S2829ChartZOver x y h) =
      WeierstrassCurve.Affine.Point.some x y
        ((WeierstrassCurve.Affine.equation_iff_nonsingular
          (W := S2829Curve.toAffine) (x := x) (y := y)).mp
          (by simpa [S2829Curve, S2829_chartZHom_chartZSchemePoint, E37ChartZPoint_X, E37ChartZPoint_Y] using
            (S2828_chartZ_equation K (E37ChartZSchemePoint K x y h)))) := by
  unfold S2829ZOverToAffinePoint S2829ChartZOver
  simp [S2829_chartZHom_chartZSchemePoint, E37ChartZPoint_X, E37ChartZPoint_Y]

#check S2829_chartZHom_chartZSchemePoint
#check S2829ZOver_roundtrip
#print axioms S2829ZOver_roundtrip


theorem S2829PointMap_surjective : Function.Surjective (S2829PointMap) := by
  intro P
  by_cases hP : P = 0
  · exact ⟨Sum.inr (S2829ChartYInfinityOver), by simp [S2829PointMap, hP]⟩
  · let e := WeierstrassCurve.Projective.Point.toAffineAddEquiv
      S2829Curve.toProjective
    have hQ : e P ≠ 0 := by
      intro h0
      apply hP
      apply e.injective
      simpa using h0
    obtain ⟨Q, hQdef⟩ : ∃ Q, e P = Q := ⟨_, rfl⟩
    cases Q with
    | zero => exact absurd hQdef hQ
    | some x y hns =>
      have hEq : S2829Curve.toAffine.Equation x y := by
        haveI : (S2829Curve.toAffine).IsElliptic := S2829_isElliptic
        exact (WeierstrassCurve.Affine.equation_iff_nonsingular
          (W := S2829Curve.toAffine)).mpr hns
      have hraw : y ^ 2 + y = x ^ 3 - x := by
        simpa [S2829Curve, S2801E37Curve, WeierstrassCurve.Affine.equation_iff,
          sub_eq_add_neg]
          using hEq
      refine ⟨Sum.inl (S2829ChartZOver x y hraw), ?_⟩
      show e.symm (S2829ZOverToAffinePoint (S2829ChartZOver x y hraw)) = P
      rw [S2829ZOver_roundtrip]
      rw [← hQdef]
      simp

#check S2829PointMap_surjective
#print axioms S2829PointMap_surjective

#check S2829Curve
#check S2829_isElliptic
#check S2829ChartZOver
#print axioms S2829_isElliptic
#print axioms S2829ChartZOver

end LeanFormal.IUT.XiFPaper.S2829E37GaussianPointActual
end
