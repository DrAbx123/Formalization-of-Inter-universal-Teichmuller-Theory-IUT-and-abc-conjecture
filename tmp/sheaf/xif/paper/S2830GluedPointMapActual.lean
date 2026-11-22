import tmp.sheaf.xif.paper.S2829E37GaussianPointActual
import tmp.sheaf.xif.paper.S2820E37TransitionActual

noncomputable section
open WeierstrassCurve LeanFormal.IUT CategoryTheory AlgebraicGeometry
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2830GluedPointMapActual

open LeanFormal.IUT.XiFPaper.S2829E37GaussianPointActual
open LeanFormal.IUT.XiFPaper.S2801D6FaithfulActual
open LeanFormal.IUT.XiFPaper.S2814E37ChartPointsActual
open LeanFormal.IUT.XiFPaper.S2828PointRealizationActual
open LeanFormal.IUT.XiFPaper.S2820E37TransitionActual
open LeanFormal.IUT.XiFPaper.S2801E37ProjectiveClosure
open LeanFormal.IUT.XiFPaper.S2789E37OrbicurveSignActual

local instance : Field K := S2789Arithmetic.fieldF
local instance : DecidableEq K := Classical.decEq _

noncomputable def S2830ZSchemeToAffinePoint
    (z : Spec (CommRingCat.of K) ⟶ S2801E37AffineScheme K) :
    S2829Curve.toAffine.Point := by
  let f := S2828_chartZHom K z
  have hEq : S2829Curve.toAffine.Equation
      (f (S2801E37X K)) (f (S2801E37Y K)) :=
    S2828_chartZ_equation K z
  haveI : (S2829Curve.toAffine).IsElliptic := S2829_isElliptic
  exact WeierstrassCurve.Affine.Point.some
    (f (S2801E37X K)) (f (S2801E37Y K))
    ((WeierstrassCurve.Affine.equation_iff_nonsingular
      (W := S2829Curve.toAffine)).mp hEq)

noncomputable def S2830ZSchemeToProjectivePoint
    (z : Spec (CommRingCat.of K) ⟶ S2801E37AffineScheme K) :
    S2829Curve.toProjective.Point :=
  (WeierstrassCurve.Projective.Point.toAffineAddEquiv
    S2829Curve.toProjective).symm (S2830ZSchemeToAffinePoint z)

noncomputable def S2830PointMap :
    ((Spec (CommRingCat.of K) ⟶ S2801E37AffineScheme K) ⊕
      (Spec (CommRingCat.of K) ⟶ E37ChartYScheme K)) →
        S2829Curve.toProjective.Point
  | Sum.inl z => S2830ZSchemeToProjectivePoint z
  | Sum.inr _ => 0

#check S2830ZSchemeToAffinePoint
#check S2830ZSchemeToProjectivePoint
#check S2830PointMap
#print axioms S2830ZSchemeToAffinePoint


noncomputable def S2830GluedMap
    (x : Spec (CommRingCat.of K) ⟶ S2820E37ProjectiveScheme K) :
    S2829Curve.toProjective.Point := by
  classical
  exact
    if h : ∃ z : Spec (CommRingCat.of K) ⟶ S2801E37AffineScheme K,
        z ≫ S2820E37ChartZMap K = x then
      S2830PointMap (Sum.inl h.choose)
    else
      have hfac := S2828_fpoint_factors_chart K (S2820E37TransitionIso K) x
      have hy : ∃ y : Spec (CommRingCat.of K) ⟶ E37ChartYScheme K,
          y ≫ S2820E37ChartYMap K = x := by
        rcases hfac with ⟨z, hz⟩ | hy
        · exact absurd ⟨z, hz⟩ h
        · exact hy
      S2830PointMap (Sum.inr hy.choose)

theorem S2830GluedMap_surjective_of_chartZ
    (hZ : ∀ P : S2829Curve.toProjective.Point,
      ∃ z : Spec (CommRingCat.of K) ⟶ S2801E37AffineScheme K,
        S2830ZSchemeToProjectivePoint z = P) :
    Function.Surjective (S2830GluedMap) := by
  classical
  intro P
  obtain ⟨z, hz⟩ := hZ P
  refine ⟨z ≫ S2820E37ChartZMap K, ?_⟩
  haveI : IsOpenImmersion (S2820E37ChartZMap K) :=
    (E37ProjGlueData K (S2820E37TransitionIso K)).ι_isOpenImmersion (ULift.up false)
  haveI : Mono (S2820E37ChartZMap K) :=
    IsOpenImmersion.mono (S2820E37ChartZMap K)
  let hex : ∃ z' : Spec (CommRingCat.of K) ⟶ S2801E37AffineScheme K,
      z' ≫ S2820E37ChartZMap K = z ≫ S2820E37ChartZMap K := ⟨z, rfl⟩
  unfold S2830GluedMap
  rw [dif_pos hex]
  have hchoose : hex.choose = z := by
    apply (cancel_mono (S2820E37ChartZMap K)).mp
    exact hex.choose_spec
  rw [hchoose]
  exact hz

#check S2830GluedMap
#check S2830GluedMap_surjective_of_chartZ
#print axioms S2830GluedMap

end LeanFormal.IUT.XiFPaper.S2830GluedPointMapActual
end
