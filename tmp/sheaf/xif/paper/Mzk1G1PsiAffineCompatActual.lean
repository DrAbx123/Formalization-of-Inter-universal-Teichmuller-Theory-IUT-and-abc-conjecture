import tmp.sheaf.xif.paper.Mzk1G1PsiProductIdentityActual
import tmp.sheaf.xif.paper.Mzk1G1ProjectiveLineTransitionActual
import Mathlib.Tactic

noncomputable section
open AlgebraicGeometry CategoryTheory Polynomial
namespace LeanFormal.IUT.XiFPaper.Mzk1G1PsiAffineCompatActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatAffineChartActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatSecondChartActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatOverlapActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiChartMapsActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiAffineOverlapActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiProductIdentityActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineTransitionActual

variable (n : Nat) (T : Finset ℚ)

theorem val_pow (u : (overlapRing n T)ˣ) (k : ℕ) :
    (((u ^ k : (overlapRing n T)ˣ)) : overlapRing n T) =
      ((u : overlapRing n T)) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, Units.val_mul, ih, pow_succ]

theorem isUnit_r1 : IsUnit (r2ToOverlap n T (r1 n)) := by
  have h : r2ToOverlap n T (r1 n) = r2ToOverlap n T (chartR n) := rfl
  rw [h]
  exact isUnit_r n T

/-- The unit of the overlap ring coming from r. -/
noncomputable def rUnit : (overlapRing n T)ˣ := (isUnit_r n T).unit

theorem rUnit_val : ((rUnit n T : (overlapRing n T)ˣ) : overlapRing n T) =
    r2ToOverlap n T (chartR n) := (isUnit_r n T).unit_spec

/-- The unit of the overlap ring coming from q. -/
noncomputable def qUnit : (overlapRing n T)ˣ := (isUnit_q n T).unit

theorem qUnit_val : ((qUnit n T : (overlapRing n T)ˣ) : overlapRing n T) =
    r2ToOverlap n T (psiChartInfDenom n T) := (isUnit_q n T).unit_spec

theorem infToOverlap_algMap (a : R2 n) :
    infToOverlap n T (algebraMap (R2 n) (OverlapInf n) a) = r2ToOverlap n T a :=
  RingHom.congr_fun
    (IsLocalization.Away.lift_comp (x := r1 n) (g := r2ToOverlap n T) (isUnit_r1 n T)) a

/-- The image of iu1 in the overlap ring is the inverse of r. -/
theorem infToOverlap_iu1 :
    infToOverlap n T (iu1 n) = (((rUnit n T)⁻¹ : (overlapRing n T)ˣ) : overlapRing n T) := by
  have h1 : infToOverlap n T (u1 n) = ((rUnit n T : (overlapRing n T)ˣ) : overlapRing n T) := by
    show infToOverlap n T (algebraMap (ChartInfRing n) (OverlapInf n) (r1 n)) = _
    rw [infToOverlap_algMap n T (r1 n)]
    exact (rUnit_val n T).symm
  have h2 : infToOverlap n T (iu1 n) * ((rUnit n T : (overlapRing n T)ˣ) : overlapRing n T) = 1 := by
    rw [← h1]
    rw [← map_mul, iu1_mul_u1, map_one]
  calc infToOverlap n T (iu1 n)
      = infToOverlap n T (iu1 n) * 1 := (mul_one _).symm
    _ = infToOverlap n T (iu1 n) *
          (((rUnit n T : (overlapRing n T)ˣ) : overlapRing n T) *
            (((rUnit n T)⁻¹ : (overlapRing n T)ˣ) : overlapRing n T)) := by
        rw [Units.mul_inv]
    _ = (infToOverlap n T (iu1 n) *
          ((rUnit n T : (overlapRing n T)ˣ) : overlapRing n T)) *
            (((rUnit n T)⁻¹ : (overlapRing n T)ˣ) : overlapRing n T) := by
        rw [mul_assoc]
    _ = (((rUnit n T)⁻¹ : (overlapRing n T)ˣ) : overlapRing n T) := by
        rw [h2, one_mul]

theorem qToOverlap_algMap (a : R2 n) :
    qToOverlap n T
        (algebraMap (R2 n) (Localization.Away (psiChartInfDenom n T)) a) =
      r2ToOverlap n T a :=
  RingHom.congr_fun
    (IsLocalization.Away.lift_comp (x := psiChartInfDenom n T) (g := r2ToOverlap n T)
      (isUnit_q n T)) a

/-- The distinguished unit whose two chart presentations give the two chart maps. -/
noncomputable def psiUnit : (overlapRing n T)ˣ := (rUnit n T) ^ T.card * (qUnit n T)⁻¹

theorem psiUnit_val :
    ((psiUnit n T : (overlapRing n T)ˣ) : overlapRing n T) =
      (r2ToOverlap n T (chartR n)) ^ T.card *
        (((qUnit n T)⁻¹ : (overlapRing n T)ˣ) : overlapRing n T) := by
  rw [psiUnit, Units.val_mul, val_pow n T, rUnit_val n T]

/-- The q-chart coordinate is the distinguished unit. -/
theorem qToOverlap_coord :
    qToOverlap n T (psiChartInfCoord n T) =
      ((psiUnit n T : (overlapRing n T)ˣ) : overlapRing n T) := by
  have h := congrArg (qToOverlap n T) (psiChartInfCoord_spec (n := n) T)
  rw [map_mul, qToOverlap_algMap n T (psiChartInfDenom n T),
    qToOverlap_algMap n T (chartR n ^ T.card), map_pow, ← rUnit_val n T] at h
  have hQ : r2ToOverlap n T (psiChartInfDenom n T) =
      ((qUnit n T : (overlapRing n T)ˣ) : overlapRing n T) := (qUnit_val n T).symm
  rw [hQ] at h
  calc qToOverlap n T (psiChartInfCoord n T)
      = qToOverlap n T (psiChartInfCoord n T) * 1 := (mul_one _).symm
    _ = qToOverlap n T (psiChartInfCoord n T) *
          (((qUnit n T : (overlapRing n T)ˣ) : overlapRing n T) *
            (((qUnit n T)⁻¹ : (overlapRing n T)ˣ) : overlapRing n T)) := by
        rw [Units.mul_inv]
    _ = (qToOverlap n T (psiChartInfCoord n T) *
          ((qUnit n T : (overlapRing n T)ˣ) : overlapRing n T)) *
            (((qUnit n T)⁻¹ : (overlapRing n T)ˣ) : overlapRing n T) := by
        rw [mul_assoc]
    _ = (((rUnit n T : (overlapRing n T)ˣ) : overlapRing n T) ^ T.card) *
            (((qUnit n T)⁻¹ : (overlapRing n T)ˣ) : overlapRing n T) := by
        rw [h]
    _ = ((psiUnit n T : (overlapRing n T)ˣ) : overlapRing n T) := by
        rw [psiUnit, Units.val_mul, val_pow n T, rUnit_val n T]

/-- The psi-coordinate of the first chart is the inverse of the distinguished unit. -/
theorem rToOverlap_coord :
    rToOverlap n T (psiChart0Coord n T) =
      (((psiUnit n T)⁻¹ : (overlapRing n T)ˣ) : overlapRing n T) := by
  have h : rToOverlap n T (psiChart0Coord n T) =
      infToOverlap n T (iu1 n) ^ T.card *
        infToOverlap n T (algebraMap (R2 n) (OverlapInf n) (psiChartInfDenom n T)) := by
    rw [rToOverlap, RingHom.comp_apply, psi_psiChart0Coord n T, map_mul, map_pow]
  rw [h, infToOverlap_iu1 n T, infToOverlap_algMap n T (psiChartInfDenom n T),
    ← qUnit_val n T]
  have hpow : ((((rUnit n T)⁻¹ : (overlapRing n T)ˣ) : overlapRing n T)) ^ T.card =
      ((((rUnit n T)⁻¹) ^ T.card : (overlapRing n T)ˣ) : overlapRing n T) :=
    (val_pow n T ((rUnit n T)⁻¹) T.card).symm
  rw [hpow]
  rw [show ((rUnit n T)⁻¹) ^ T.card = ((rUnit n T) ^ T.card)⁻¹ from inv_pow (rUnit n T) T.card]
  rw [psiUnit, mul_inv_rev, inv_inv, Units.val_mul]
  rw [mul_comm]

/-- The first chart ring map to the overlap is rational-linear. -/
theorem rToOverlap_rat :
    (rToOverlap n T).comp (algebraMap ℚ (R n)) = algebraMap ℚ (overlapRing n T) := by
  ext r
  rw [RingHom.comp_apply, rToOverlap, RingHom.comp_apply, psi_algebraMap n r,
    IsScalarTower.algebraMap_apply ℚ (R2 n) (OverlapInf n) r,
    infToOverlap_algMap n T (algebraMap ℚ (R2 n) r)]
  exact (RingHom.congr_fun
    (IsScalarTower.algebraMap_eq ℚ (R2 n) (overlapRing n T)) r).symm

/-- The q-chart ring map to the overlap is rational-linear. -/
theorem qToOverlap_rat :
    (qToOverlap n T).comp (algebraMap ℚ (Localization.Away (psiChartInfDenom n T))) =
      algebraMap ℚ (overlapRing n T) := by
  ext r
  rw [RingHom.comp_apply,
    IsScalarTower.algebraMap_apply ℚ (R2 n)
      (Localization.Away (psiChartInfDenom n T)) r,
    qToOverlap_algMap n T (algebraMap ℚ (R2 n) r)]
  exact (RingHom.congr_fun
    (IsScalarTower.algebraMap_eq ℚ (R2 n) (overlapRing n T)) r).symm

/-- AFFINE COMPATIBILITY of the two chart presentations of psi on the common overlap
Spec(Away(q*r)): the first-chart morphism (t = psiChart0Coord) and the q-chart morphism
(lambda = psiChartInfCoord) agree there, because the two coordinates are mutually
inverse units. -/
theorem affine_compat :
    chart0ToOverlap n T ≫ chartMorphismInf (R := R n) (psiChart0Coord n T) =
      chartInfPieceToOverlap n T ≫
        chartMorphism0 (R := Localization.Away (psiChartInfDenom n T))
          (psiChartInfCoord n T) := by
  rw [chart0ToOverlap, chartInfPieceToOverlap]
  rw [chartMorphismInf_comp (f := rToOverlap n T) (hf := rToOverlap_rat n T)
    (a := psiChart0Coord n T)]
  rw [chartMorphism0_comp (f := qToOverlap n T) (hf := qToOverlap_rat n T)
    (a := psiChartInfCoord n T)]
  rw [rToOverlap_coord n T, qToOverlap_coord n T]
  exact (chartMorphism_transition (R := overlapRing n T) (psiUnit n T)).symm

#print axioms affine_compat
end LeanFormal.IUT.XiFPaper.Mzk1G1PsiAffineCompatActual
