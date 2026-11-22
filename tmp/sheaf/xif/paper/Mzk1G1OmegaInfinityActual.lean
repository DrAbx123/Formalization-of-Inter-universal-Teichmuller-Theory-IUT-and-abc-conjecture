/- G1-B Fermat Omega local bases on the infinity chart: s = x^{-1}, r = y/x with
1 + s^n = r^n, omegaInf = (s dr - r ds)/n, and the local basis identities
(n s^(n-1)) omegaInf = -dr on D(s), (n r^(n-1)) omegaInf = -ds on D(r) (route §3.1). -/
import tmp.sheaf.xif.paper.Mzk1G1FermatTransitionActual
import tmp.sheaf.xif.paper.Mzk1G1FermatSecondChartActual
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.Tactic
noncomputable section
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatTransitionActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatSecondChartActual
namespace LeanFormal.IUT.XiFPaper.Mzk1G1OmegaInfinityActual

/-- Generic: a natural multiple of a module element is the ring multiple. -/
theorem nsmul_smul_eq {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (n : ℕ) (a : R) (z : M) : n • (a • z) = ((n : R) * a) • z := by
  rw [← Nat.cast_smul_eq_nsmul R n, smul_smul]

/-- The absolute differential module of the infinity chart. -/
abbrev OmegaInf (n : ℕ) : Type := KaehlerDifferential ℚ (R2 n)

/-- d(s) on the infinity chart. -/
noncomputable def dS (n : ℕ) : OmegaInf n := KaehlerDifferential.D ℚ (R2 n) (infinityS n)
/-- d(r) on the infinity chart. -/
noncomputable def dR (n : ℕ) : OmegaInf n := KaehlerDifferential.D ℚ (R2 n) (infinityR n)

/-- The infinity-chart Euler form s dr - r ds. -/
noncomputable def omegaInfForm (n : ℕ) : OmegaInf n :=
  infinityS n • dR n - infinityR n • dS n

/-- n is a nonzero rational number for n >= 1. -/
theorem n_neq_zero_rat {n : ℕ} (hn : 1 ≤ n) : (n : ℚ) ≠ 0 := by
  have hpos : (0 : ℚ) < (n : ℚ) := by exact_mod_cast (by omega : 0 < n)
  exact ne_of_gt hpos

/-- n is a unit of the Q-algebra R2 n, for n >= 1. -/
theorem natCast_isUnit_inf (n : ℕ) (hn : 1 ≤ n) : IsUnit (n : R2 n) := by
  rw [← map_natCast (algebraMap ℚ (R2 n)) n]
  exact IsUnit.map (algebraMap ℚ (R2 n)).toMonoidHom (isUnit_iff_ne_zero.mpr (n_neq_zero_rat hn))

/-- A unit of the scalar ring acts injectively on OmegaInf. -/
theorem smul_eq_of_unit_smul_eq_inf (n : ℕ) (hn : 1 ≤ n) {a b : OmegaInf n}
    (h : ((↑(natCast_isUnit_inf n hn).unit) : R2 n) • a =
      ((↑(natCast_isUnit_inf n hn).unit) : R2 n) • b) : a = b := by
  have hinv : ((↑((natCast_isUnit_inf n hn).unit)⁻¹) : R2 n) *
      ((↑(natCast_isUnit_inf n hn).unit) : R2 n) = 1 := by
    simpa using Units.inv_mul_cancel_left ((natCast_isUnit_inf n hn).unit) 1
  calc a = (1 : R2 n) • a := (one_smul _ _).symm
    _ = (((↑((natCast_isUnit_inf n hn).unit)⁻¹) : R2 n) *
          ((↑(natCast_isUnit_inf n hn).unit) : R2 n)) • a := by rw [hinv]
    _ = ((↑((natCast_isUnit_inf n hn).unit)⁻¹) : R2 n) •
          (((↑(natCast_isUnit_inf n hn).unit) : R2 n) • a) := by rw [smul_smul]
    _ = ((↑((natCast_isUnit_inf n hn).unit)⁻¹) : R2 n) •
          (((↑(natCast_isUnit_inf n hn).unit) : R2 n) • b) := by rw [h]
    _ = (((↑((natCast_isUnit_inf n hn).unit)⁻¹) : R2 n) *
          ((↑(natCast_isUnit_inf n hn).unit) : R2 n)) • b := by rw [smul_smul]
    _ = (1 : R2 n) • b := by rw [hinv]
    _ = b := one_smul _ _

/-- The derivative relation of the infinity chart: n s^(n-1) ds - n r^(n-1) dr = 0. -/
theorem derivation_relation_inf (n : ℕ) :
    ((n : R2 n) * infinityS n ^ (n - 1)) • dS n -
      ((n : R2 n) * infinityR n ^ (n - 1)) • dR n = 0 := by
  have h := congrArg (KaehlerDifferential.D ℚ (R2 n)) (infinityS_pow_add_one_sub_infinityR_pow n)
  simp only [map_sub, map_add, map_one, Derivation.map_one_eq_zero] at h
  rw [Derivation.leibniz_pow, Derivation.leibniz_pow, nsmul_smul_eq, nsmul_smul_eq] at h
  simpa [dS, dR] using h

/-- r^n - s^n = 1 on the infinity chart. -/
theorem sum_eq_one_inf (n : ℕ) : infinityR n ^ n - infinityS n ^ n = 1 := by
  have h := infinityS_pow_add_one_sub_infinityR_pow n
  have h1 : 1 + infinityS n ^ n = infinityR n ^ n := sub_eq_zero.mp h
  rw [← h1]
  ring

/-- The derivative relation multiplied by r. -/
theorem r_mul_relation (n : ℕ) (hn : 1 ≤ n) :
    ((n : R2 n) * infinityR n * infinityS n ^ (n - 1)) • dS n -
      ((n : R2 n) * infinityR n ^ n) • dR n = 0 := by
  have h := congrArg (fun z => (infinityR n) • z) (derivation_relation_inf n)
  have hL : (infinityR n) • (((n : R2 n) * infinityS n ^ (n - 1)) • dS n) =
      ((n : R2 n) * infinityR n * infinityS n ^ (n - 1)) • dS n := by
    rw [show ((n : R2 n) * infinityR n * infinityS n ^ (n - 1)) =
      ((infinityR n) * ((n : R2 n) * infinityS n ^ (n - 1))) by ring]
    rw [smul_smul]
  have hR : (infinityR n) • (((n : R2 n) * infinityR n ^ (n - 1)) • dR n) =
      ((n : R2 n) * infinityR n ^ n) • dR n := by
    rw [show ((n : R2 n) * infinityR n ^ n) =
      ((infinityR n) * ((n : R2 n) * infinityR n ^ (n - 1))) by
      rw [show infinityR n ^ n = infinityR n * infinityR n ^ (n - 1) from by
        rw [← pow_succ', Nat.sub_add_cancel hn]]
      ring]
    rw [smul_smul]
  rw [smul_sub, smul_zero, hL, hR] at h
  exact h

/-- The derivative relation multiplied by s. -/
theorem s_mul_relation (n : ℕ) (hn : 1 ≤ n) :
    ((n : R2 n) * infinityS n ^ n) • dS n -
      ((n : R2 n) * infinityS n * infinityR n ^ (n - 1)) • dR n = 0 := by
  have h := congrArg (fun z => (infinityS n) • z) (derivation_relation_inf n)
  have hL : (infinityS n) • (((n : R2 n) * infinityS n ^ (n - 1)) • dS n) =
      ((n : R2 n) * infinityS n ^ n) • dS n := by
    rw [show ((n : R2 n) * infinityS n ^ n) =
      ((infinityS n) * ((n : R2 n) * infinityS n ^ (n - 1))) by
      rw [show infinityS n ^ n = infinityS n * infinityS n ^ (n - 1) from by
        rw [← pow_succ', Nat.sub_add_cancel hn]]
      ring]
    rw [smul_smul]
  have hR : (infinityS n) • (((n : R2 n) * infinityR n ^ (n - 1)) • dR n) =
      ((n : R2 n) * infinityS n * infinityR n ^ (n - 1)) • dR n := by
    rw [show ((n : R2 n) * infinityS n * infinityR n ^ (n - 1)) =
      ((infinityS n) * ((n : R2 n) * infinityR n ^ (n - 1))) by ring]
    rw [smul_smul]
  rw [smul_sub, smul_zero, hL, hR] at h
  exact h

/-- (n s^(n-1)) omegaInf = -(n dr). -/
theorem n_s_pow_smul_omegaInf (n : ℕ) (hn : 1 ≤ n) :
    ((n : R2 n) * infinityS n ^ (n - 1)) • omegaInfForm n = -((n : R2 n) • dR n) := by
  have hr := r_mul_relation n hn
  have hsub : ((n : R2 n) * infinityR n * infinityS n ^ (n - 1)) • dS n =
      ((n : R2 n) * infinityR n ^ n) • dR n := sub_eq_zero.mp hr
  have hsum := sum_eq_one_inf n
  calc
    ((n : R2 n) * infinityS n ^ (n - 1)) • omegaInfForm n
        = (((n : R2 n) * infinityS n ^ (n - 1)) * infinityS n) • dR n -
            (((n : R2 n) * infinityS n ^ (n - 1)) * infinityR n) • dS n := by
            simp only [omegaInfForm, smul_sub, smul_smul]
    _ = ((n : R2 n) * infinityS n ^ n) • dR n -
            ((n : R2 n) * infinityR n * infinityS n ^ (n - 1)) • dS n := by
            rw [show ((n : R2 n) * infinityS n ^ (n - 1)) * infinityS n =
                  (n : R2 n) * infinityS n ^ n by
                  rw [mul_assoc, show infinityS n ^ (n - 1) * infinityS n = infinityS n ^ n by
                    rw [← pow_succ, Nat.sub_add_cancel hn]],
                show ((n : R2 n) * infinityS n ^ (n - 1)) * infinityR n =
                  (n : R2 n) * infinityR n * infinityS n ^ (n - 1) by ring]
    _ = ((n : R2 n) * infinityS n ^ n) • dR n - ((n : R2 n) * infinityR n ^ n) • dR n := by
            rw [hsub]
    _ = ((n : R2 n) * (infinityS n ^ n - infinityR n ^ n)) • dR n := by
            rw [mul_sub, sub_smul]
    _ = ((n : R2 n) * (-1)) • dR n := by
            rw [show infinityS n ^ n - infinityR n ^ n = -1 by
              rw [← neg_sub, hsum]]
    _ = -((n : R2 n) • dR n) := by
            rw [show (n : R2 n) * (-1) = -(n : R2 n) by ring, neg_smul]

/-- (n r^(n-1)) omegaInf = -(n ds). -/
theorem n_r_pow_smul_omegaInf (n : ℕ) (hn : 1 ≤ n) :
    ((n : R2 n) * infinityR n ^ (n - 1)) • omegaInfForm n = -((n : R2 n) • dS n) := by
  have hs := s_mul_relation n hn
  have hsub : ((n : R2 n) * infinityS n * infinityR n ^ (n - 1)) • dR n =
      ((n : R2 n) * infinityS n ^ n) • dS n := by
    have := sub_eq_zero.mp hs
    exact this.symm
  have hsum := sum_eq_one_inf n
  calc
    ((n : R2 n) * infinityR n ^ (n - 1)) • omegaInfForm n
        = (((n : R2 n) * infinityR n ^ (n - 1)) * infinityS n) • dR n -
            (((n : R2 n) * infinityR n ^ (n - 1)) * infinityR n) • dS n := by
            simp only [omegaInfForm, smul_sub, smul_smul]
    _ = ((n : R2 n) * infinityS n * infinityR n ^ (n - 1)) • dR n -
            ((n : R2 n) * infinityR n ^ n) • dS n := by
            rw [show ((n : R2 n) * infinityR n ^ (n - 1)) * infinityS n =
                  (n : R2 n) * infinityS n * infinityR n ^ (n - 1) by ring,
                show ((n : R2 n) * infinityR n ^ (n - 1)) * infinityR n =
                  (n : R2 n) * infinityR n ^ n by
                  rw [mul_assoc, show infinityR n ^ (n - 1) * infinityR n = infinityR n ^ n by
                    rw [← pow_succ, Nat.sub_add_cancel hn]]]
    _ = ((n : R2 n) * infinityS n ^ n) • dS n - ((n : R2 n) * infinityR n ^ n) • dS n := by
            rw [hsub]
    _ = ((n : R2 n) * (infinityS n ^ n - infinityR n ^ n)) • dS n := by
            rw [mul_sub, sub_smul]
    _ = ((n : R2 n) * (-1)) • dS n := by
            rw [show infinityS n ^ n - infinityR n ^ n = -1 by
              rw [← neg_sub, hsum]]
    _ = -((n : R2 n) • dS n) := by
            rw [show (n : R2 n) * (-1) = -(n : R2 n) by ring, neg_smul]

#print axioms derivation_relation_inf
#print axioms n_s_pow_smul_omegaInf
#print axioms n_r_pow_smul_omegaInf
end LeanFormal.IUT.XiFPaper.Mzk1G1OmegaInfinityActual
