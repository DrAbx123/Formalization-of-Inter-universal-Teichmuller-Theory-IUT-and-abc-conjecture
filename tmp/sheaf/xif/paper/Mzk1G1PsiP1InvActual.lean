/- P^1 inversion p1Inv : P^1 ⟶ P^1 (lambda |-> lambda^{-1}) as a glued morphism.
   Owner: grace (handed over by henry; assembly only, hard ring proof credited to henry's route).
   Reuse: p1GlueData (ProjectiveLineGluedActual), Mzk1GlueMorphismActual.glueMorphism,
   specMap_chartMorphismInf/0 (PsiHPolyFinalActual), chartMorphism_transition, invAuto lemmas. -/
import tmp.sheaf.xif.paper.Mzk1G1PsiHPolyFinalActual
import tmp.sheaf.xif.paper.Mzk1G1PsiFixedActual
import tmp.sheaf.xif.paper.Mzk1GlueMorphismActual
import Mathlib.Tactic

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Polynomial
namespace LeanFormal.IUT.XiFPaper.Mzk1G1PsiP1InvActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineGluedActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineTransitionActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiHPolyFinalActual
open LeanFormal.IUT.XiFPaper.Mzk1GlueMorphismActual

/-- P¹ 反演的 chart 映射：λ-chart 片 t' = λ，t-chart 片 λ' = t。 -/
noncomputable def p1InvFun : (i : p1GlueData.J) → p1GlueData.U i ⟶ projectiveLineGlued
  | ⟨false⟩ => chartMorphismInf (R := Polynomial ℚ) Polynomial.X
  | ⟨true⟩ => chartMorphism0 (R := Polynomial ℚ) Polynomial.X

/-- 反演的两片在 overlap 上兼容。 -/
theorem p1Inv_overlap_compat :
    overlapToChart0 ≫ p1InvFun ⟨false⟩ = overlapToChartInf ≫ p1InvFun ⟨true⟩ := by
  show Spec.map (CommRingCat.ofHom (algebraMap (Polynomial ℚ) OverlapRing)) ≫
      chartMorphismInf (R := Polynomial ℚ) Polynomial.X =
    Spec.map (CommRingCat.ofHom (invAuto.comp (algebraMap (Polynomial ℚ) OverlapRing))) ≫
      chartMorphism0 (R := Polynomial ℚ) Polynomial.X
  have hfix : ∀ r : ℚ, invAuto (algebraMap ℚ OverlapRing r) = algebraMap ℚ OverlapRing r := by
    intro r
    have h1 : invAuto (infMapR (Polynomial.C r)) =
        algebraMap (Polynomial ℚ) OverlapRing (Polynomial.C r) :=
      RingHom.congr_fun invAuto_comp_infMapR (Polynomial.C r)
    rw [infMapR_C r] at h1
    rw [h1, Polynomial.C_eq_algebraMap,
      IsScalarTower.algebraMap_apply ℚ (Polynomial ℚ) OverlapRing r]
  have h0 : (algebraMap (Polynomial ℚ) OverlapRing) Polynomial.X = ovLambda := rfl
  have h1 : invAuto ((algebraMap (Polynomial ℚ) OverlapRing) Polynomial.X) = invLambda := by
    rw [h0]
    exact invAuto_ovLambda
  have hrho0 : ((invAuto.comp (algebraMap (Polynomial ℚ) OverlapRing)).comp
      (algebraMap ℚ (Polynomial ℚ))) = algebraMap ℚ OverlapRing := by
    ext r
    simp only [RingHom.comp_apply]
    rw [IsScalarTower.algebraMap_apply ℚ (Polynomial ℚ) OverlapRing r]
    exact hfix r
  rw [specMap_chartMorphismInf (R := Polynomial ℚ) (S := OverlapRing)
      (algebraMap (Polynomial ℚ) OverlapRing)
      (by ext r; exact IsScalarTower.algebraMap_apply ℚ (Polynomial ℚ) OverlapRing r)
      Polynomial.X,
    specMap_chartMorphism0 (R := Polynomial ℚ) (S := OverlapRing)
      (invAuto.comp (algebraMap (Polynomial ℚ) OverlapRing)) hrho0 Polynomial.X,
    h0]
  rw [show (invAuto.comp (algebraMap (Polynomial ℚ) OverlapRing)) Polynomial.X = invLambda from by
    simp only [RingHom.comp_apply]
    exact h1]
  have hu : IsUnit (algebraMap (Polynomial ℚ) OverlapRing Polynomial.X) :=
    IsLocalization.Away.algebraMap_isUnit (S := OverlapRing) (x := Polynomial.X)
  let u : OverlapRingˣ := hu.unit
  have hu_val : (↑u : OverlapRing) = algebraMap (Polynomial ℚ) OverlapRing Polynomial.X :=
    IsUnit.unit_spec hu
  have hmul : (↑u : OverlapRing) * IsLocalization.Away.invSelf
      (x := (Polynomial.X : Polynomial ℚ)) = 1 := by
    rw [hu_val, IsLocalization.Away.mul_invSelf]
  have hinv : (↑u⁻¹ : OverlapRing) = invLambda := by
    apply Units.inv_eq_of_mul_eq_one_right (u := u) (a := invLambda)
    rw [hu_val]
    exact ovLambda_mul_invLambda
  have htr := chartMorphism_transition (R := OverlapRing) (u⁻¹)
  rw [inv_inv] at htr
  rw [← hinv, htr, hu_val, h0]

/-- 反演在胶合数据的 overlap 上的兼容（GlueData 形式）。 -/
theorem p1Inv_compat : ∀ i j, p1GlueData.f i j ≫ p1InvFun i =
    p1GlueData.t i j ≫ p1GlueData.f j i ≫ p1InvFun j := by
  intro i j
  obtain ⟨bi⟩ := i
  obtain ⟨bj⟩ := j
  cases bi <;> cases bj
  · simp
  · change overlapToChart0 ≫ p1InvFun ⟨false⟩ =
      overlapToChartInf ≫ p1InvFun ⟨true⟩
    exact p1Inv_overlap_compat
  · change overlapToChartInf ≫ p1InvFun ⟨true⟩ =
      overlapToChart0 ≫ p1InvFun ⟨false⟩
    exact p1Inv_overlap_compat.symm
  · simp

/-- **P¹ 反演**：`p1Inv : P¹ ⟶ P¹`（λ ↦ λ⁻¹）。 -/
noncomputable def p1Inv : projectiveLineGlued ⟶ projectiveLineGlued :=
  glueMorphism (D := p1GlueData) p1InvFun p1Inv_compat

theorem p1Inv_ι (i : p1GlueData.J) :
    p1GlueData.ι i ≫ p1Inv = p1InvFun i :=
  glueMorphism_ι (D := p1GlueData) p1InvFun p1Inv_compat i

theorem p1Inv_ι_false :
    p1GlueData.ι ⟨false⟩ ≫ p1Inv = chartMorphismInf (R := Polynomial ℚ) Polynomial.X :=
  p1Inv_ι ⟨false⟩

theorem p1Inv_ι_true :
    p1GlueData.ι ⟨true⟩ ≫ p1Inv = chartMorphism0 (R := Polynomial ℚ) Polynomial.X :=
  p1Inv_ι ⟨true⟩

#print axioms p1Inv_overlap_compat
#print axioms p1Inv_compat
#print axioms p1Inv
#print axioms p1Inv_ι

end LeanFormal.IUT.XiFPaper.Mzk1G1PsiP1InvActual