/- B2 general-T: `psiPoly` (two-section map), zero fibre = `DTZeroElem`, DTZeroElem havoid (value layer).
  Header RECON: psiGeneral_preimage_p1Zero_eq (DONE 05:24:22), DTZeroElem (DONE),
  chartMorphism0_mem_boundarySetGlued_iff (emmy DONE), Polynomial.X_sub_C_dvd_sub_C_eval.
  General Galois-orbit case = A3/RR obligation, not claimed. No sorry/axiom. -/
import tmp.sheaf.xif.paper.Mzk1G1B1GeneralPsiZeroFibreActual
import tmp.sheaf.xif.paper.Mzk1G1B2PsiPolyDTZeroActual
import tmp.sheaf.xif.paper.Mzk1G1PhiFixedLChart0BoundaryActual
import Mathlib.Tactic

noncomputable section
open Polynomial CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace LeanFormal.IUT.XiFPaper.Mzk1G1B2PsiPolyHavoidActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatCurveActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatAffineChartActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiGeneralActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiCoverActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiChartMapsActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiAffineOverlapActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineGluedActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineTransitionActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineBoundaryActual
open LeanFormal.IUT.XiFPaper.Mzk1G1B1GeneralPsiZeroFibreActual
open LeanFormal.IUT.XiFPaper.Mzk1G1B2PsiPolyDTZeroActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PhiFixedLChart0BoundaryActual

variable (n : Nat) (T : Finset ℚ)

abbrev Compat (u0 : R n) (u1 : Localization.Away (psiChartInfDenom n T)) : Prop :=
  chart0ToOverlap n T ≫ chartMorphism0 u0 = chartInfPieceToOverlap n T ≫ chartMorphismInf u1

noncomputable def psiPoly (u0 : R n)
    (u1 : Localization.Away (psiChartInfDenom n T)) (haffine : Compat n T u0 u1) :
    fermatCurveScheme n ⟶ projectiveLineGlued :=
  psiGeneral n T u0 u1 haffine

theorem psiPoly_preimage_p1Zero_eq_DTZeroElem (u0 : R n)
    (u1 : Localization.Away (psiChartInfDenom n T)) (haffine : Compat n T u0 u1) :
    (psiPoly n T u0 u1 haffine) ⁻¹' p1Zero = DTZeroElem n u0 :=
  psiGeneral_preimage_p1Zero_eq n T u0 u1 haffine

theorem aeval_sub_eval_zero_mem (h : Polynomial ℚ) (u : R n) (p : Ideal (R n))
    (hu : u ∈ p) :
    Polynomial.aeval u h - algebraMap ℚ (R n) (Polynomial.eval 0 h) ∈ p := by
  have hdvd : Polynomial.X - Polynomial.C (0 : ℚ) ∣
      h - Polynomial.C (Polynomial.eval 0 h) := Polynomial.X_sub_C_dvd_sub_C_eval
  obtain ⟨q, hq⟩ := hdvd
  have hX : Polynomial.X - Polynomial.C (0 : ℚ) = Polynomial.X := by simp
  rw [hX] at hq
  have hsub : Polynomial.aeval u h - algebraMap ℚ (R n) (Polynomial.eval 0 h) =
      Polynomial.aeval u (h - Polynomial.C (Polynomial.eval 0 h)) := by
    simp [map_sub]
  rw [hsub, hq, map_mul]
  have hXeval : Polynomial.aeval u (Polynomial.X : Polynomial ℚ) = u := by simp
  rw [hXeval, mul_comm]
  exact p.mul_mem_left (Polynomial.aeval u q) hu

theorem aeval_notMem_of_eval_zero_ne (h : Polynomial ℚ) (u : R n) (p : Ideal (R n))
    (hp : p.IsPrime) (hu : u ∈ p) (h0 : Polynomial.eval 0 h ≠ 0) :
    Polynomial.aeval u h ∉ p := by
  intro hmem
  have hcong := aeval_sub_eval_zero_mem n h u p hu
  have hval : algebraMap ℚ (R n) (Polynomial.eval 0 h) ∈ p := by
    have := p.sub_mem hmem hcong
    simpa using this
  have hunit : IsUnit (algebraMap ℚ (R n) (Polynomial.eval 0 h)) :=
    IsUnit.map (algebraMap ℚ (R n)) (isUnit_iff_ne_zero.mpr h0)
  exact hp.ne_top (Ideal.eq_top_of_isUnit_mem p hval hunit)

theorem aeval_sub_one_notMem_of_eval_zero_ne_one (h : Polynomial ℚ) (u : R n)
    (p : Ideal (R n)) (hp : p.IsPrime) (hu : u ∈ p)
    (h1 : Polynomial.eval 0 h ≠ 1) : Polynomial.aeval u h - 1 ∉ p := by
  intro hmem
  have hcong := aeval_sub_eval_zero_mem n h u p hu
  have hval : algebraMap ℚ (R n) (Polynomial.eval 0 h - 1) ∈ p := by
    have hA : algebraMap ℚ (R n) (Polynomial.eval 0 h - 1) =
        algebraMap ℚ (R n) (Polynomial.eval 0 h) - 1 := by
      rw [map_sub, map_one]
    have hsplit : Polynomial.aeval u h - 1 =
        (Polynomial.aeval u h - algebraMap ℚ (R n) (Polynomial.eval 0 h)) +
          algebraMap ℚ (R n) (Polynomial.eval 0 h - 1) := by
      rw [hA]
      ring
    rw [hsplit] at hmem
    have hsub : ((Polynomial.aeval u h - algebraMap ℚ (R n) (Polynomial.eval 0 h)) +
          algebraMap ℚ (R n) (Polynomial.eval 0 h - 1)) -
          (Polynomial.aeval u h - algebraMap ℚ (R n) (Polynomial.eval 0 h)) ∈ p :=
      p.sub_mem hmem hcong
    simpa using hsub
  have hne : Polynomial.eval 0 h - 1 ≠ 0 := by
    intro hh
    exact h1 (sub_eq_zero.mp hh)
  have hunit : IsUnit (algebraMap ℚ (R n) (Polynomial.eval 0 h - 1)) :=
    IsUnit.map (algebraMap ℚ (R n)) (isUnit_iff_ne_zero.mpr hne)
  exact hp.ne_top (Ideal.eq_top_of_isUnit_mem p hval hunit)

theorem chartMorphism0_aeval_notMem_boundary (h : Polynomial ℚ) (u : R n)
    (p : PrimeSpectrum (R n)) (hp : p.asIdeal.IsPrime) (hu : u ∈ p.asIdeal)
    (h0 : Polynomial.eval 0 h ≠ 0) (h1 : Polynomial.eval 0 h ≠ 1) :
    chartMorphism0 (R := R n) (Polynomial.aeval u h) p ∉ boundarySetGlued := by
  rw [chartMorphism0_mem_boundarySetGlued_iff]
  rintro (hmem | hmem)
  · exact aeval_notMem_of_eval_zero_ne n h u p.asIdeal hp hu h0 hmem
  · exact aeval_sub_one_notMem_of_eval_zero_ne_one n h u p.asIdeal hp hu h1 hmem

#print axioms psiPoly_preimage_p1Zero_eq_DTZeroElem
#print axioms aeval_sub_eval_zero_mem
#print axioms aeval_notMem_of_eval_zero_ne
#print axioms aeval_sub_one_notMem_of_eval_zero_ne_one
#print axioms chartMorphism0_aeval_notMem_boundary

end LeanFormal.IUT.XiFPaper.Mzk1G1B2PsiPolyHavoidActual
