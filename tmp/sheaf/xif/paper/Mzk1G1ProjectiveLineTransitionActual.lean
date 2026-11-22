import tmp.sheaf.xif.paper.Mzk1G1ProjectiveLineGluedActual
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Tactic

noncomputable section
open AlgebraicGeometry CategoryTheory
namespace LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineTransitionActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineGluedActual

variable {R : Type} [CommRing R] [Algebra ℚ R]

/-- The ring map Q[lambda] -> R sending lambda to a. -/
noncomputable def evalAt (a : R) : Polynomial ℚ →+* R :=
  (Polynomial.aeval (R := ℚ) a).toRingHom

theorem evalAt_X (a : R) : evalAt a Polynomial.X = a :=
  Polynomial.aeval_X a

theorem evalAt_C (a : R) (r : ℚ) : evalAt a (Polynomial.C r) = algebraMap ℚ R r :=
  Polynomial.aeval_C a r

/-- The lambda-chart point of P^1 with coordinate a, over an affine base Spec R. -/
noncomputable def chartMorphism0 (a : R) : Spec (CommRingCat.of R) ⟶ projectiveLineGlued :=
  Spec.map (CommRingCat.ofHom (evalAt a)) ≫ localChart0

/-- The t-chart point of P^1 with coordinate a, over an affine base Spec R. -/
noncomputable def chartMorphismInf (a : R) : Spec (CommRingCat.of R) ⟶ projectiveLineGlued :=
  Spec.map (CommRingCat.ofHom (evalAt a)) ≫ localChartInf

/-- THE P^1 CHART TRANSITION over any affine base: when the coordinate a is a unit, the
lambda-chart point with coordinate a and the t-chart point with coordinate a^{-1} are the
same point of P^1 (the transition t = lambda^{-1} of the two charts). -/
theorem chartMorphism_transition (u : Rˣ) :
    chartMorphism0 (u : R) = chartMorphismInf ((u⁻¹ : Rˣ) : R) := by
  set A : Polynomial ℚ →+* R := evalAt (u : R) with hA
  have hAX : A Polynomial.X = (u : R) := by
    rw [hA]; exact evalAt_X (u : R)
  have hAunit : IsUnit (A Polynomial.X) := by
    rw [hAX]; exact u.isUnit
  set g : OverlapRing →+* R :=
    IsLocalization.Away.lift (S := OverlapRing) (x := (Polynomial.X : Polynomial ℚ))
      (g := A) hAunit with hg
  have hgcomp : g.comp (algebraMap (Polynomial ℚ) OverlapRing) = A :=
    IsLocalization.Away.lift_comp (S := OverlapRing) (x := (Polynomial.X : Polynomial ℚ))
      (g := A) hAunit
  have hg_inv : g invLambda = ((u⁻¹ : Rˣ) : R) := by
    have hmul : (u : R) * g invLambda = 1 := by
      have h1 : g (algebraMap (Polynomial ℚ) OverlapRing (Polynomial.X : Polynomial ℚ)) *
          g invLambda = 1 := by
        rw [← map_mul]
        have h : algebraMap (Polynomial ℚ) OverlapRing (Polynomial.X : Polynomial ℚ) * invLambda = 1 :=
          ovLambda_mul_invLambda
        rw [h, map_one]
      have hcomp_apply :
          g (algebraMap (Polynomial ℚ) OverlapRing (Polynomial.X : Polynomial ℚ)) =
            A Polynomial.X := RingHom.congr_fun hgcomp Polynomial.X
      rw [hcomp_apply, hAX] at h1
      exact h1
    rw [← Units.inv_mul_cancel_left u (g invLambda)]
    rw [hmul, mul_one]
  have hB : evalAt ((u⁻¹ : Rˣ) : R) =
      g.comp (invAuto.comp (algebraMap (Polynomial ℚ) OverlapRing)) := by
    apply Polynomial.ringHom_ext
    · intro r
      rw [RingHom.comp_apply, RingHom.comp_apply, evalAt_C]
      have h1 : algebraMap (Polynomial ℚ) OverlapRing (Polynomial.C r) =
          algebraMap ℚ OverlapRing r := by
        rw [Polynomial.C_eq_algebraMap,
          IsScalarTower.algebraMap_apply ℚ (Polynomial ℚ) OverlapRing r]
      rw [h1]
      have h2 : invAuto (algebraMap ℚ OverlapRing r) = algebraMap ℚ OverlapRing r := by
        rw [← h1, invAuto, IsLocalization.Away.lift_eq]
        exact infMapR_C r
      rw [h2]
      have h3 : g (algebraMap ℚ OverlapRing r) = algebraMap ℚ R r := by
        rw [← h1]
        have h4 : g (algebraMap (Polynomial ℚ) OverlapRing (Polynomial.C r)) =
            A (Polynomial.C r) := RingHom.congr_fun hgcomp (Polynomial.C r)
        rw [h4, hA]
        exact evalAt_C (u : R) r
      exact h3.symm
    · have hinner :
          invAuto ((algebraMap (Polynomial ℚ) OverlapRing) (Polynomial.X : Polynomial ℚ)) =
            invLambda := by
        rw [show (algebraMap (Polynomial ℚ) OverlapRing) (Polynomial.X : Polynomial ℚ) = ovLambda
          from rfl]
        exact invAuto_ovLambda
      rw [RingHom.comp_apply, RingHom.comp_apply, evalAt_X, hinner]
      exact hg_inv.symm
  rw [chartMorphism0, chartMorphismInf, ← hA, hB]
  have hL : Spec.map (CommRingCat.ofHom A) ≫ localChart0 =
      Spec.map (CommRingCat.ofHom g) ≫ (overlapToChart0 ≫ localChart0) := by
    rw [← hgcomp, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
    rfl
  have hR :
      Spec.map (CommRingCat.ofHom (g.comp (invAuto.comp (algebraMap (Polynomial ℚ) OverlapRing)))) ≫
        localChartInf = Spec.map (CommRingCat.ofHom g) ≫ (overlapToChartInf ≫ localChartInf) := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
    rfl
  rw [hL, hR, localChart_overlap_condition]

#print axioms chartMorphism_transition
end LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineTransitionActual
