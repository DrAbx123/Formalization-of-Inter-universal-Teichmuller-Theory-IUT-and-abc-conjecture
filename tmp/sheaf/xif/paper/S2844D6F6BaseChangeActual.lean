import tmp.sheaf.xif.paper.S2831GluedOverPointMapActual
import tmp.sheaf.xif.paper.S2839A6F6ClauseRestatementActual
import tmp.sheaf.xif.paper.S2821E37ProjectiveOverActual
import tmp.sheaf.xif.paper.S2812IsStackActual
import tmp.sheaf.xif.paper.S2813E37TwoFPointsActual
import tmp.sheaf.xif.paper.S2809E6FiniteActual
import tmp.sheaf.xif.paper.S2814bE37ChartZOverActual
import tmp.sheaf.xif.paper.S2789E37OrbicurveSignActual
import LeanFormal.IUT.IUTII.Frobenioid.Example36OrbicurveFeasibility

noncomputable section
open WeierstrassCurve LeanFormal.IUT CategoryTheory AlgebraicGeometry
open LeanFormal.IUT.XiFPaper.S2801E37ProjectiveClosure
open LeanFormal.IUT.XiFPaper.S2801D6FaithfulActual
open LeanFormal.IUT.XiFPaper.S2813E37TwoFPointsActual
open LeanFormal.IUT.XiFPaper.S2814E37ChartPointsActual
open LeanFormal.IUT.XiFPaper.S2814bE37ChartZOverActual
open LeanFormal.IUT.XiFPaper.S2820E37TransitionActual
open LeanFormal.IUT.XiFPaper.S2821E37ProjectiveOverActual
open LeanFormal.IUT.XiFPaper.S2831GluedOverPointMapActual
open LeanFormal.IUT.XiFPaper.S2809E6FiniteActual
open LeanFormal.IUT.XiFPaper.S2839A6F6ClauseRestatementActual
open LeanFormal.IUT.XiFPaper.S2828PointRealizationActual
open scoped SpecOfNotation
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2844D6F6BaseChangeActual

abbrev K : Type := A6F6
local instance : Field K := inferInstance
local instance : DecidableEq K := Classical.decEq _
local instance : NumberField K := LeanFormal.IUT.XiFPaper.S2809E6FiniteActual.S2809_numberField

noncomputable def S2844Curve : WeierstrassCurve K := S2801E37Curve K

theorem S2844_discriminant : S2844Curve.Δ = 37 := by
  norm_num [S2844Curve, S2801E37Curve, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

instance S2844_isElliptic : S2844Curve.IsElliptic :=
  ⟨isUnit_iff_ne_zero.mpr (by rw [S2844_discriminant]; norm_num)⟩

noncomputable def S2844Punctured : PuncturedEllipticCurve K where
  curve := S2844Curve
  isElliptic := S2844_isElliptic
  puncture := ⟨WeierstrassCurve.Projective.nonsingularLift_zero⟩

noncomputable abbrev S2844X : Iut.SchemeOverField K := S2821AsOver K
noncomputable abbrev S2844Base : Iut.SchemeOverField K := S2813Base K

theorem S2844_chartZHom_chartZSchemePoint (x y : K)
    (h : y ^ 2 + y = x ^ 3 - x) :
    LeanFormal.IUT.XiFPaper.S2828PointRealizationActual.S2828_chartZHom K
        (E37ChartZSchemePoint K x y h) = E37ChartZPoint K x y h := by
  simp [LeanFormal.IUT.XiFPaper.S2828PointRealizationActual.S2828_chartZHom,
    E37ChartZSchemePoint]

noncomputable def S2844ChartZOver (x y : K)
    (h : y ^ 2 + y = x ^ 3 - x) : S2844Base ⟶ S2844X := by
  classical
  let z : S2813Base K ⟶ S2801E37AsOver K :=
    Over.homMk (E37ChartZSchemePoint K x y h) (by
      change Spec.map (CommRingCat.ofHom (E37ChartZPoint K x y h)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap K (S2801E37CoordinateRing K))) = 𝟙 _
      have hring :
          (CommRingCat.ofHom (algebraMap K (S2801E37CoordinateRing K))) ≫
            (CommRingCat.ofHom (E37ChartZPoint K x y h)) =
          CommRingCat.ofHom (RingHom.id K) := by
        ext c
        simpa using congrArg (fun f => f c) (E37ChartZPoint_comp_algebraMap K x y h)
      rw [← Spec.map_comp, hring]
      simp)
  exact z ≫ S2821ChartZOver K

theorem S2844InfinityEval_comp_algebraMap :
    (E37InfinityEval K).comp (algebraMap K (E37ChartYRing K)) = RingHom.id K := by
  ext c
  simp only [RingHom.comp_apply, RingHom.id_apply]
  rw [show (algebraMap K (E37ChartYRing K)) c =
    Ideal.Quotient.mk (E37ChartYIdeal K) (MvPolynomial.C c) from rfl]
  unfold E37InfinityEval
  rw [Ideal.Quotient.lift_mk]
  simp [E37InfinityPolynomialEval]

noncomputable def S2844InfinityOver : S2844Base ⟶ S2844X := by
  classical
  let y : S2813Base K ⟶ E37ChartYAsOver K :=
    Over.homMk (Spec.map (CommRingCat.ofHom (E37InfinityEval K))) (by
      change Spec.map (CommRingCat.ofHom (E37InfinityEval K)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap K (E37ChartYRing K))) = 𝟙 _
      have hring :
          (CommRingCat.ofHom (algebraMap K (E37ChartYRing K))) ≫
            (CommRingCat.ofHom (E37InfinityEval K)) =
          CommRingCat.ofHom (RingHom.id K) := by
        ext c
        simpa using congrArg (fun f => f c) S2844InfinityEval_comp_algebraMap
      rw [← Spec.map_comp, hring]
      simp)
  exact y ≫ S2821ChartYOver K

noncomputable def S2844ZSchemeToAffinePoint
    (z : Spec (CommRingCat.of K) ⟶ S2801E37AffineScheme K) :
    S2844Curve.toAffine.Point := by
  let f := LeanFormal.IUT.XiFPaper.S2828PointRealizationActual.S2828_chartZHom K z
  have hEq : S2844Curve.toAffine.Equation
      (f (S2801E37X K)) (f (S2801E37Y K)) := by
    simpa [S2844Curve] using
      LeanFormal.IUT.XiFPaper.S2828PointRealizationActual.S2828_chartZ_equation K z
  exact WeierstrassCurve.Affine.Point.some
    (f (S2801E37X K)) (f (S2801E37Y K))
    ((WeierstrassCurve.Affine.equation_iff_nonsingular
      (W := S2844Curve.toAffine)
      (x := f (S2801E37X K)) (y := f (S2801E37Y K))).mp hEq)

noncomputable def S2844ZSchemeToProjectivePoint
    (z : Spec (CommRingCat.of K) ⟶ S2801E37AffineScheme K) :
    S2844Curve.toProjective.Point :=
  (WeierstrassCurve.Projective.Point.toAffineAddEquiv
    S2844Curve.toProjective).symm (S2844ZSchemeToAffinePoint z)

noncomputable def S2844PointMap :
    ((Spec (CommRingCat.of K) ⟶ S2801E37AffineScheme K) ⊕
      (Spec (CommRingCat.of K) ⟶ E37ChartYScheme K)) →
        S2844Curve.toProjective.Point
  | Sum.inl z => S2844ZSchemeToProjectivePoint z
  | Sum.inr _ => 0

noncomputable def S2844GluedMap
    (x : Spec (CommRingCat.of K) ⟶ S2820E37ProjectiveScheme K) :
    S2844Curve.toProjective.Point := by
  classical
  exact
    if h : ∃ z : Spec (CommRingCat.of K) ⟶ S2801E37AffineScheme K,
        z ≫ S2820E37ChartZMap K = x then
      S2844PointMap (Sum.inl h.choose)
    else
      have hfac := S2828_fpoint_factors_chart K (S2820E37TransitionIso K) x
      have hy : ∃ y : Spec (CommRingCat.of K) ⟶ E37ChartYScheme K,
          y ≫ S2820E37ChartYMap K = x := by
        rcases hfac with ⟨z, hz⟩ | hy
        · exact absurd ⟨z, hz⟩ h
        · exact hy
      S2844PointMap (Sum.inr hy.choose)

noncomputable def S2844GluedOverMap (x : S2844Base ⟶ S2844X) :
    S2844Curve.toProjective.Point :=
  S2844GluedMap x.left

theorem S2844ZOver_roundtrip (x y : K)
    (h : y ^ 2 + y = x ^ 3 - x) :
    S2844ZSchemeToAffinePoint (E37ChartZSchemePoint K x y h) =
      WeierstrassCurve.Affine.Point.some x y
        ((WeierstrassCurve.Affine.equation_iff_nonsingular
          (W := S2844Curve.toAffine) (x := x) (y := y)).mp
          (by
            simpa [S2844Curve, S2844_chartZHom_chartZSchemePoint,
              E37ChartZPoint_X, E37ChartZPoint_Y] using
              (S2828_chartZ_equation K (E37ChartZSchemePoint K x y h)))) := by
  unfold S2844ZSchemeToAffinePoint
  simp [S2844_chartZHom_chartZSchemePoint, E37ChartZPoint_X, E37ChartZPoint_Y]

theorem S2844GluedMap_chartZ (x y : K)
    (h : y ^ 2 + y = x ^ 3 - x) :
    S2844GluedMap (E37ChartZSchemePoint K x y h ≫ S2820E37ChartZMap K) =
      S2844ZSchemeToProjectivePoint (E37ChartZSchemePoint K x y h) := by
  classical
  unfold S2844GluedMap
  split_ifs with hex'
  · haveI : IsOpenImmersion (S2820E37ChartZMap K) :=
      (E37ProjGlueData K (S2820E37TransitionIso K)).ι_isOpenImmersion (ULift.up false)
    haveI : Mono (S2820E37ChartZMap K) :=
      IsOpenImmersion.mono (S2820E37ChartZMap K)
    have hchoose : hex'.choose = E37ChartZSchemePoint K x y h := by
      apply (cancel_mono (S2820E37ChartZMap K)).mp
      exact hex'.choose_spec
    rw [hchoose]
    rfl
  · exact absurd ⟨E37ChartZSchemePoint K x y h, rfl⟩ hex'

theorem S2844GluedMap_surjective_of_ne_zero (P : S2844Curve.toProjective.Point)
    (hP : P ≠ 0) :
    ∃ x : Spec (CommRingCat.of K) ⟶ S2820E37ProjectiveScheme K,
      S2844GluedMap x = P := by
  classical
  let e := WeierstrassCurve.Projective.Point.toAffineAddEquiv
    S2844Curve.toProjective
  have hQ : e P ≠ 0 := by
    intro h0
    apply hP
    apply e.injective
    simpa using h0
  obtain ⟨Q, hQdef⟩ : ∃ Q, e P = Q := ⟨_, rfl⟩
  cases Q with
  | zero => exact absurd hQdef hQ
  | some x y hns =>
    have hEq : S2844Curve.toAffine.Equation x y :=
      (WeierstrassCurve.Affine.equation_iff_nonsingular
        (W := S2844Curve.toAffine)).mpr hns
    have hraw : y ^ 2 + y = x ^ 3 - x := by
      simpa [S2844Curve, S2801E37Curve, WeierstrassCurve.Affine.equation_iff,
        sub_eq_add_neg] using hEq
    refine ⟨E37ChartZSchemePoint K x y hraw ≫ S2820E37ChartZMap K, ?_⟩
    rw [S2844GluedMap_chartZ]
    show e.symm (S2844ZSchemeToAffinePoint (E37ChartZSchemePoint K x y hraw)) = P
    rw [S2844ZOver_roundtrip]
    rw [← hQdef]
    simp

noncomputable abbrev S2844Fiber : Iut.EtaleStackPseudofunctor K :=
  LeanFormal.IUT.XiFPaper.S2812IsStackActual.fiber K S2844X

instance S2844Fiber_isStack :
    S2844Fiber.IsStack (Iut.SchemeOverField.etaleTopology K) :=
  inferInstance

theorem S2844GluedOverMap_surjective_of_ne_zero (P : S2844Curve.toProjective.Point)
    (hP : P ≠ 0) :
    ∃ x : S2844Base ⟶ S2844X, S2844GluedOverMap x = P := by
  classical
  let e := WeierstrassCurve.Projective.Point.toAffineAddEquiv S2844Curve.toProjective
  have hQ : e P ≠ 0 := by
    intro h0
    apply hP
    apply e.injective
    simpa using h0
  obtain ⟨Q, hQdef⟩ : ∃ Q, e P = Q := ⟨_, rfl⟩
  cases Q with
  | zero => exact absurd hQdef hQ
  | some x y hns =>
    have hEq : S2844Curve.toAffine.Equation x y :=
      (WeierstrassCurve.Affine.equation_iff_nonsingular
        (W := S2844Curve.toAffine)).mpr hns
    have hraw : y ^ 2 + y = x ^ 3 - x := by
      simpa [S2844Curve, S2801E37Curve, WeierstrassCurve.Affine.equation_iff,
        sub_eq_add_neg] using hEq
    refine ⟨S2844ChartZOver x y hraw, ?_⟩
    change S2844GluedMap
      (E37ChartZSchemePoint K x y hraw ≫ S2820E37ChartZMap K) = P
    rw [S2844GluedMap_chartZ]
    show e.symm (S2844ZSchemeToAffinePoint (E37ChartZSchemePoint K x y hraw)) = P
    rw [S2844ZOver_roundtrip]
    rw [← hQdef]
    simp

/-- Exact missing point-realization datum: the zero projective point is the image
of some actual base-scheme morphism (this is the infinity/chart-disjointness step). -/
def S2844ZeroPreimage : Prop :=
  ∃ x : S2844Base ⟶ S2844X, S2844GluedOverMap x = 0

/-- Conditional curve-point realization: all nonzero points are actual, the zero
point is the single explicit remaining preimage. -/
noncomputable def S2844CurvePointRealization (h0 : S2844ZeroPreimage) :
    S2813CurvePointRealization K S2844X S2844Punctured where
  pointMap := S2844GluedOverMap
  surjective := by
    intro P
    by_cases hP : P = 0
    · rw [hP]
      exact h0
    · exact S2844GluedOverMap_surjective_of_ne_zero P hP

end LeanFormal.IUT.XiFPaper.S2844D6F6BaseChangeActual
end


