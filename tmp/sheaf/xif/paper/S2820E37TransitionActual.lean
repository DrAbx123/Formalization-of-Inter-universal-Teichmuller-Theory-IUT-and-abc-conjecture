import tmp.sheaf.xif.paper.S2801E37ProjectiveClosure
import tmp.sheaf.xif.paper.S2801D6FaithfulActual
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Tactic

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2820E37TransitionActual
open LeanFormal.IUT.XiFPaper.S2801E37ProjectiveClosure
open LeanFormal.IUT.XiFPaper.S2801D6FaithfulActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36

universe u

variable (K : Type u) [Field K]

theorem e37_affine_polynomial (K : Type u) [Field K] :
    S2801E37Polynomial K =
      MvPolynomial.X 1 ^ 2 + MvPolynomial.X 1 - MvPolynomial.X 0 ^ 3 + MvPolynomial.X 0 := by
  simp [S2801E37Polynomial, weierstrassAffinePolynomial, S2801E37Curve]; ring

/-- The actual E37 Weierstrass relation in the chart-Z coordinate ring. -/
theorem e37_relation (K : Type u) [Field K] :
    S2801E37Y K ^ 2 + S2801E37Y K = S2801E37X K ^ 3 - S2801E37X K :=
  S2801E37_relation K

variable (K : Type) [Field K]

abbrev R0 (K : Type) [Field K] : Type := S2801E37CoordinateRing K
abbrev R1 (K : Type) [Field K] : Type := E37ChartYRing K
abbrev A0 (K : Type) [Field K] : Type := E37ChartZOverlapRing K
abbrev A1 (K : Type) [Field K] : Type := E37ChartYOverlapRing K

abbrev tbar (K : Type) [Field K] : R1 K :=
  Ideal.Quotient.mk (E37ChartYIdeal K) (MvPolynomial.X 1)

abbrev sbar (K : Type) [Field K] : R1 K :=
  Ideal.Quotient.mk (E37ChartYIdeal K) (MvPolynomial.X 0)

abbrev tOne (K : Type) [Field K] : Submonoid.powers (tbar K) :=
  ⟨1, ⟨0, by simp⟩⟩

abbrev tPow (K : Type) [Field K] : Submonoid.powers (tbar K) :=
  ⟨tbar K, ⟨1, by simp [pow_one]⟩⟩

noncomputable abbrev t1 (K : Type) [Field K] : A1 K :=
  Localization.mk (tbar K) (tOne K)

noncomputable abbrev s1 (K : Type) [Field K] : A1 K :=
  Localization.mk (sbar K) (tOne K)

noncomputable abbrev tInv (K : Type) [Field K] : A1 K :=
  Localization.mk (1 : R1 K) (tPow K)

theorem t1_mul_tInv (K : Type) [Field K] : t1 K * tInv K = 1 := by
  rw [t1, tInv, Localization.mk_mul]
  rw [show tOne K * tPow K = tPow K from Subtype.ext (by simp [tOne, tPow])]
  simpa using Localization.mk_self (tPow K)

theorem tInv_mul_t1 (K : Type) [Field K] : tInv K * t1 K = 1 := by
  rw [mul_comm, t1_mul_tInv]

theorem chartYRelation_quotient (K : Type) [Field K] :
    Ideal.Quotient.mk (E37ChartYIdeal K) (E37ChartYPolynomial K) = 0 := by
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span (Set.mem_singleton _)

theorem chartYPolynomial_eq (K : Type) [Field K] :
    Ideal.Quotient.mk (E37ChartYIdeal K) (E37ChartYPolynomial K) =
      sbar K ^ 3 - sbar K * tbar K ^ 2 - tbar K - tbar K ^ 2 := by
  simp [E37ChartYPolynomial, tbar, sbar]

theorem hrel (K : Type) [Field K] :
    t1 K + t1 K ^ 2 = s1 K ^ 3 - s1 K * t1 K ^ 2 := by
  have hR : sbar K ^ 3 - sbar K * tbar K ^ 2 - tbar K - tbar K ^ 2 = 0 := by
    rw [← chartYPolynomial_eq K]
    exact chartYRelation_quotient K
  have h := congrArg (algebraMap (R1 K) (A1 K)) hR
  simp only [map_sub, map_add, map_pow, map_mul, map_zero] at h
  have h1 : algebraMap (R1 K) (A1 K) (tbar K) = t1 K := rfl
  have h2 : algebraMap (R1 K) (A1 K) (sbar K) = s1 K := rfl
  rw [h1, h2] at h
  linear_combination -h

theorem hzero (K : Type) [Field K] :
    tInv K ^ 2 + tInv K - (s1 K * tInv K) ^ 3 + s1 K * tInv K = 0 := by
  have e1 : tInv K ^ 3 * t1 K = tInv K ^ 2 := by
    rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_succ, mul_assoc,
      tInv_mul_t1 K, mul_one]
  have e2 : tInv K ^ 3 * t1 K ^ 2 = tInv K := by
    calc tInv K ^ 3 * t1 K ^ 2 = tInv K * (tInv K * t1 K) ^ 2 := by ring
      _ = tInv K * 1 ^ 2 := by rw [tInv_mul_t1 K]
      _ = tInv K := by ring
  calc tInv K ^ 2 + tInv K - (s1 K * tInv K) ^ 3 + s1 K * tInv K
      = tInv K ^ 3 * (t1 K + t1 K ^ 2 - s1 K ^ 3 + s1 K * t1 K ^ 2) := by
        rw [show tInv K ^ 3 * (t1 K + t1 K ^ 2 - s1 K ^ 3 + s1 K * t1 K ^ 2)
            = tInv K ^ 3 * t1 K + tInv K ^ 3 * t1 K ^ 2 - s1 K ^ 3 * tInv K ^ 3 +
              s1 K * tInv K ^ 3 * t1 K ^ 2 from by ring]
        rw [e1, mul_assoc (s1 K) (tInv K ^ 3) (t1 K ^ 2), e2]
        ring
    _ = 0 := by
        have h' : t1 K + t1 K ^ 2 - s1 K ^ 3 + s1 K * t1 K ^ 2 = 0 := by
          linear_combination hrel K
        rw [h']
        ring

abbrev evalVals (K : Type) [Field K] : Fin 2 → A1 K :=
  ![s1 K * tInv K, tInv K]

theorem alphaPoly_zero (K : Type) [Field K] :
    MvPolynomial.eval₂Hom (algebraMap K (A1 K)) (evalVals K)
      (S2801E37Polynomial K) = 0 := by
  rw [e37_affine_polynomial]
  simp [evalVals, hzero K]

noncomputable def alphaPoly (K : Type) [Field K] :
    MvPolynomial (Fin 2) K →+* A1 K :=
  MvPolynomial.eval₂Hom (algebraMap K (A1 K)) (evalVals K)

theorem alphaPoly_mem_ker (K : Type) [Field K] :
    S2801E37Ideal K ≤ RingHom.ker (alphaPoly K) := by
  rw [S2801E37Ideal, Ideal.span_le]
  intro a ha
  rw [Set.mem_singleton_iff] at ha
  subst ha
  exact RingHom.mem_ker.mpr (alphaPoly_zero K)

noncomputable def alpha (K : Type) [Field K] : R0 K →+* A1 K :=
  Ideal.Quotient.lift (S2801E37Ideal K) (alphaPoly K) (alphaPoly_mem_ker K)

theorem alpha_S2801E37Y (K : Type) [Field K] :
    alpha K (S2801E37Y K) = tInv K := by
  simp [alpha, S2801E37Y, alphaPoly, evalVals]

theorem alpha_S2801E37Y_isUnit (K : Type) [Field K] :
    IsUnit (alpha K (S2801E37Y K)) := by
  rw [alpha_S2801E37Y]
  exact isUnit_iff_exists_inv.mpr ⟨t1 K, tInv_mul_t1 K⟩

noncomputable def phi (K : Type) [Field K] : A0 K →+* A1 K :=
  Localization.awayLift (alpha K) (S2801E37Y K) (alpha_S2801E37Y_isUnit K)


/-! ## Symmetric inverse map psi : A1 → A0 -/

abbrev yOne (K : Type) [Field K] : Submonoid.powers (S2801E37Y K) :=
  ⟨1, ⟨0, by simp⟩⟩

abbrev yPow (K : Type) [Field K] : Submonoid.powers (S2801E37Y K) :=
  ⟨S2801E37Y K, ⟨1, by simp [pow_one]⟩⟩

noncomputable abbrev y0 (K : Type) [Field K] : A0 K :=
  Localization.mk (S2801E37Y K) (yOne K)

noncomputable abbrev x0 (K : Type) [Field K] : A0 K :=
  Localization.mk (S2801E37X K) (yOne K)

noncomputable abbrev yInv (K : Type) [Field K] : A0 K :=
  Localization.mk (1 : R0 K) (yPow K)

theorem y0_mul_yInv (K : Type) [Field K] : y0 K * yInv K = 1 := by
  rw [y0, yInv, Localization.mk_mul]
  rw [show yOne K * yPow K = yPow K from Subtype.ext (by simp [yOne, yPow])]
  simpa using Localization.mk_self (yPow K)

theorem yInv_mul_y0 (K : Type) [Field K] : yInv K * y0 K = 1 := by
  rw [mul_comm, y0_mul_yInv]

theorem hrelW (K : Type) [Field K] : y0 K ^ 2 + y0 K = x0 K ^ 3 - x0 K := by
  have h := congrArg (algebraMap (R0 K) (A0 K)) (e37_relation K)
  simp only [map_pow, map_add, map_sub] at h
  have h1 : algebraMap (R0 K) (A0 K) (S2801E37Y K) = y0 K := rfl
  have h2 : algebraMap (R0 K) (A0 K) (S2801E37X K) = x0 K := rfl
  rw [h1, h2] at h
  exact h

theorem hzero2 (K : Type) [Field K] :
    yInv K ^ 2 + yInv K - (x0 K * yInv K) ^ 3 + x0 K * yInv K ^ 3 = 0 := by
  have h1 : yInv K = y0 K ^ 2 * yInv K ^ 3 := by
    calc yInv K = yInv K * (y0 K * yInv K) ^ 2 := by rw [y0_mul_yInv K]; ring
      _ = y0 K ^ 2 * yInv K ^ 3 := by ring
  have h2 : yInv K ^ 2 = y0 K * yInv K ^ 3 := by
    calc yInv K ^ 2 = yInv K ^ 2 * (y0 K * yInv K) := by rw [y0_mul_yInv K]; ring
      _ = y0 K * yInv K ^ 3 := by ring
  have hz : y0 K + y0 K ^ 2 - x0 K ^ 3 + x0 K = 0 := by
    linear_combination hrelW K
  have hsum : yInv K ^ 2 + yInv K = (y0 K + y0 K ^ 2) * yInv K ^ 3 := by
    linear_combination h2 + h1
  calc yInv K ^ 2 + yInv K - (x0 K * yInv K) ^ 3 + x0 K * yInv K ^ 3
      = ((y0 K + y0 K ^ 2) - x0 K ^ 3 + x0 K) * yInv K ^ 3 := by
        rw [hsum]; ring_nf
    _ = 0 := by rw [hz]; ring

abbrev betaVals (K : Type) [Field K] : Fin 2 → A0 K :=
  ![x0 K * yInv K, yInv K]

noncomputable def betaPoly (K : Type) [Field K] :
    MvPolynomial (Fin 2) K →+* A0 K :=
  MvPolynomial.eval₂Hom (algebraMap K (A0 K)) (betaVals K)

theorem betaPoly_zero (K : Type) [Field K] :
    betaPoly K (E37ChartYPolynomial K) = 0 := by
  simp [betaPoly, E37ChartYPolynomial, betaVals]
  linear_combination -hzero2 K

theorem betaPoly_mem_ker (K : Type) [Field K] :
    E37ChartYIdeal K ≤ RingHom.ker (betaPoly K) := by
  rw [E37ChartYIdeal, Ideal.span_le]
  intro a ha
  rw [Set.mem_singleton_iff] at ha
  subst ha
  exact RingHom.mem_ker.mpr (betaPoly_zero K)

noncomputable def beta (K : Type) [Field K] : R1 K →+* A0 K :=
  Ideal.Quotient.lift (E37ChartYIdeal K) (betaPoly K) (betaPoly_mem_ker K)

theorem beta_tbar (K : Type) [Field K] : beta K (tbar K) = yInv K := by
  simp [beta, betaPoly, betaVals, tbar]

theorem beta_tbar_isUnit (K : Type) [Field K] : IsUnit (beta K (tbar K)) := by
  rw [beta_tbar]
  exact isUnit_iff_exists_inv.mpr ⟨y0 K, yInv_mul_y0 K⟩

noncomputable def psi (K : Type) [Field K] : A1 K →+* A0 K :=
  Localization.awayLift (beta K) (tbar K) (beta_tbar_isUnit K)

theorem psi_s1 (K : Type) [Field K] : psi K (s1 K) = x0 K * yInv K := by
  have hone : tOne K = 1 := Subtype.ext rfl
  rw [s1, hone, Localization.mk_one_eq_algebraMap]
  have h := IsLocalization.Away.lift_comp (R := R1 K) (S := A1 K) (x := tbar K) (g := beta K) (beta_tbar_isUnit K)
  have h' := RingHom.congr_fun h (sbar K)
  simpa [psi, beta, betaPoly, betaVals] using h'

theorem psi_t1 (K : Type) [Field K] : psi K (t1 K) = yInv K := by
  have hone : tOne K = 1 := Subtype.ext rfl
  rw [t1, hone, Localization.mk_one_eq_algebraMap]
  have h := IsLocalization.Away.lift_comp (R := R1 K) (S := A1 K) (x := tbar K) (g := beta K) (beta_tbar_isUnit K)
  have h' := RingHom.congr_fun h (tbar K)
  simpa [psi, beta, betaPoly, betaVals] using h'

theorem psi_tInv (K : Type) [Field K] : psi K (tInv K) = y0 K := by
  have hprod : psi K (tInv K) * yInv K = 1 := by
    calc psi K (tInv K) * yInv K = psi K (tInv K) * psi K (t1 K) := by rw [psi_t1 K]
      _ = psi K (tInv K * t1 K) := by rw [map_mul]
      _ = psi K 1 := by rw [tInv_mul_t1 K]
      _ = 1 := map_one (psi K)
  calc psi K (tInv K) = psi K (tInv K) * (yInv K * y0 K) := by rw [yInv_mul_y0 K]; ring
    _ = (psi K (tInv K) * yInv K) * y0 K := by ring
    _ = 1 * y0 K := by rw [hprod]
    _ = y0 K := by ring


open AlgebraicGeometry CategoryTheory

theorem x0_eq_algebraMap (K : Type) [Field K] :
    x0 K = algebraMap (R0 K) (A0 K) (S2801E37X K) := by
  have hone : yOne K = 1 := Subtype.ext rfl
  rw [x0, hone]
  exact Localization.mk_one_eq_algebraMap (M := Submonoid.powers (S2801E37Y K)) (S2801E37X K)

theorem y0_eq_algebraMap (K : Type) [Field K] :
    y0 K = algebraMap (R0 K) (A0 K) (S2801E37Y K) := by
  have hone : yOne K = 1 := Subtype.ext rfl
  rw [y0, hone]
  exact Localization.mk_one_eq_algebraMap (M := Submonoid.powers (S2801E37Y K)) (S2801E37Y K)

noncomputable def gammaPoly (K : Type) [Field K] :
    MvPolynomial (Fin 2) K →+* A0 K :=
  MvPolynomial.eval₂Hom (algebraMap K (A0 K)) ![x0 K, y0 K]

theorem gammaPoly_eq (K : Type) [Field K] :
    gammaPoly K = (algebraMap (R0 K) (A0 K)).comp
      (Ideal.Quotient.mk (S2801E37Ideal K)) := by
  apply MvPolynomial.ringHom_ext
  · intro a
    change gammaPoly K (MvPolynomial.C a) =
      ((algebraMap (R0 K) (A0 K)).comp (Ideal.Quotient.mk (S2801E37Ideal K))) (MvPolynomial.C a)
    rw [RingHom.comp_apply]
    have hmk : Ideal.Quotient.mk (S2801E37Ideal K) (MvPolynomial.C a) =
        algebraMap K (R0 K) a := by
      exact Ideal.Quotient.mk_algebraMap K (I := S2801E37Ideal K) a
    rw [hmk]
    simp only [gammaPoly, MvPolynomial.eval₂Hom_C]
    exact IsScalarTower.algebraMap_apply K (R0 K) (A0 K) a
  · intro i
    fin_cases i
    · change gammaPoly K (MvPolynomial.X 0) =
        ((algebraMap (R0 K) (A0 K)).comp (Ideal.Quotient.mk (S2801E37Ideal K))) (MvPolynomial.X 0)
      rw [RingHom.comp_apply]
      have hx : algebraMap (R0 K) (A0 K) ((Ideal.Quotient.mk (S2801E37Ideal K)) (MvPolynomial.X 0)) = x0 K := by
        rw [← x0_eq_algebraMap K]
      rw [hx]
      simp [gammaPoly]
    · change gammaPoly K (MvPolynomial.X 1) =
        ((algebraMap (R0 K) (A0 K)).comp (Ideal.Quotient.mk (S2801E37Ideal K))) (MvPolynomial.X 1)
      rw [RingHom.comp_apply]
      have hy : algebraMap (R0 K) (A0 K) ((Ideal.Quotient.mk (S2801E37Ideal K)) (MvPolynomial.X 1)) = y0 K := by
        rw [← y0_eq_algebraMap K]
      rw [hy]
      simp [gammaPoly]

theorem gammaPoly_apply (K : Type) [Field K] (p : MvPolynomial (Fin 2) K) :
    gammaPoly K p = algebraMap (R0 K) (A0 K) (Ideal.Quotient.mk (S2801E37Ideal K) p) := by
  have h := RingHom.congr_fun (gammaPoly_eq K) p
  simpa [RingHom.comp_apply] using h

theorem psi_comp_alphaPoly (K : Type) [Field K] :
    (psi K).comp (alphaPoly K) = gammaPoly K := by
  have hcomp : (psi K).comp (algebraMap (R1 K) (A1 K)) = beta K := by
    simpa [psi] using IsLocalization.Away.lift_comp (R := R1 K) (S := A1 K)
      (x := tbar K) (g := beta K) (beta_tbar_isUnit K)
  apply MvPolynomial.ringHom_ext
  · intro a
    change psi K (alphaPoly K (MvPolynomial.C a)) = gammaPoly K (MvPolynomial.C a)
    have ha : alphaPoly K (MvPolynomial.C a) = algebraMap K (A1 K) a := by
      simp [alphaPoly, MvPolynomial.eval₂Hom_C]
    rw [ha]
    have h1 : psi K (algebraMap K (A1 K) a) = algebraMap K (A0 K) a := by
      rw [IsScalarTower.algebraMap_apply K (R1 K) (A1 K)]
      rw [show psi K ((algebraMap (R1 K) (A1 K)) ((algebraMap K (R1 K)) a)) =
          beta K ((algebraMap K (R1 K)) a) from
        RingHom.congr_fun hcomp ((algebraMap K (R1 K)) a)]
      have hmk : Ideal.Quotient.mk (E37ChartYIdeal K) (MvPolynomial.C a) =
          algebraMap K (R1 K) a := by
        exact Ideal.Quotient.mk_algebraMap K (I := E37ChartYIdeal K) a
      rw [← hmk]
      simp [beta, betaPoly, MvPolynomial.eval₂Hom_C]
    rw [h1]
    simp [gammaPoly, MvPolynomial.eval₂Hom_C]
  · intro i
    fin_cases i
    · change psi K (alphaPoly K (MvPolynomial.X 0)) = gammaPoly K (MvPolynomial.X 0)
      have ha : alphaPoly K (MvPolynomial.X 0) = s1 K * tInv K := by
        simp [alphaPoly, evalVals, MvPolynomial.eval₂Hom_X']
      rw [ha, map_mul, psi_s1 K, psi_tInv K]
      rw [mul_assoc (x0 K) (yInv K) (y0 K), yInv_mul_y0 K, mul_one]
      have hg : gammaPoly K (MvPolynomial.X 0) = x0 K := by
        simp [gammaPoly]
      rw [hg]
    · change psi K (alphaPoly K (MvPolynomial.X 1)) = gammaPoly K (MvPolynomial.X 1)
      have ha : alphaPoly K (MvPolynomial.X 1) = tInv K := by
        simp [alphaPoly, evalVals, MvPolynomial.eval₂Hom_X']
      rw [ha, psi_tInv K]
      have hg : gammaPoly K (MvPolynomial.X 1) = y0 K := by
        simp [gammaPoly]
      rw [hg]

theorem psi_comp_alpha (K : Type) [Field K] :
    (psi K).comp (alpha K) = algebraMap (R0 K) (A0 K) := by
  apply Ideal.Quotient.ringHom_ext
  rw [RingHom.comp_assoc]
  change (psi K).comp (alphaPoly K) =
    (algebraMap (R0 K) (A0 K)).comp (Ideal.Quotient.mk (S2801E37Ideal K))
  rw [psi_comp_alphaPoly K, gammaPoly_eq K]

theorem psi_phi (K : Type) [Field K] : (psi K).comp (phi K) = RingHom.id (A0 K) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (S2801E37Y K))
  rw [RingHom.comp_assoc]
  rw [show (phi K).comp (algebraMap (R0 K) (A0 K)) = alpha K from
    IsLocalization.Away.lift_comp (R := R0 K) (S := A0 K) (x := S2801E37Y K)
      (g := alpha K) (alpha_S2801E37Y_isUnit K)]
  simpa using psi_comp_alpha K


theorem s1_eq_algebraMap (K : Type) [Field K] :
    s1 K = algebraMap (R1 K) (A1 K) (sbar K) := by
  have hone : tOne K = 1 := Subtype.ext rfl
  rw [s1, hone]
  exact Localization.mk_one_eq_algebraMap (M := Submonoid.powers (tbar K)) (sbar K)

theorem t1_eq_algebraMap (K : Type) [Field K] :
    t1 K = algebraMap (R1 K) (A1 K) (tbar K) := by
  have hone : tOne K = 1 := Subtype.ext rfl
  rw [t1, hone]
  exact Localization.mk_one_eq_algebraMap (M := Submonoid.powers (tbar K)) (tbar K)

noncomputable def deltaPoly (K : Type) [Field K] :
    MvPolynomial (Fin 2) K →+* A1 K :=
  MvPolynomial.eval₂Hom (algebraMap K (A1 K)) ![s1 K, t1 K]

theorem deltaPoly_eq (K : Type) [Field K] :
    deltaPoly K = (algebraMap (R1 K) (A1 K)).comp
      (Ideal.Quotient.mk (E37ChartYIdeal K)) := by
  apply MvPolynomial.ringHom_ext
  · intro a
    change deltaPoly K (MvPolynomial.C a) =
      ((algebraMap (R1 K) (A1 K)).comp (Ideal.Quotient.mk (E37ChartYIdeal K))) (MvPolynomial.C a)
    rw [RingHom.comp_apply]
    have hmk : Ideal.Quotient.mk (E37ChartYIdeal K) (MvPolynomial.C a) =
        algebraMap K (R1 K) a := by
      exact Ideal.Quotient.mk_algebraMap K (I := E37ChartYIdeal K) a
    rw [hmk]
    simp only [deltaPoly, MvPolynomial.eval₂Hom_C]
    exact IsScalarTower.algebraMap_apply K (R1 K) (A1 K) a
  · intro i
    fin_cases i
    · change deltaPoly K (MvPolynomial.X 0) =
        ((algebraMap (R1 K) (A1 K)).comp (Ideal.Quotient.mk (E37ChartYIdeal K))) (MvPolynomial.X 0)
      rw [RingHom.comp_apply]
      have hx : algebraMap (R1 K) (A1 K) ((Ideal.Quotient.mk (E37ChartYIdeal K)) (MvPolynomial.X 0)) = s1 K :=
        (s1_eq_algebraMap K).symm
      rw [hx]
      simp only [deltaPoly, MvPolynomial.eval₂Hom_X']
      simp
    · change deltaPoly K (MvPolynomial.X 1) =
        ((algebraMap (R1 K) (A1 K)).comp (Ideal.Quotient.mk (E37ChartYIdeal K))) (MvPolynomial.X 1)
      rw [RingHom.comp_apply]
      have hx : algebraMap (R1 K) (A1 K) ((Ideal.Quotient.mk (E37ChartYIdeal K)) (MvPolynomial.X 1)) = t1 K :=
        (t1_eq_algebraMap K).symm
      rw [hx]
      simp only [deltaPoly, MvPolynomial.eval₂Hom_X']
      simp

theorem deltaPoly_apply (K : Type) [Field K] (p : MvPolynomial (Fin 2) K) :
    deltaPoly K p = algebraMap (R1 K) (A1 K) (Ideal.Quotient.mk (E37ChartYIdeal K) p) := by
  have h := RingHom.congr_fun (deltaPoly_eq K) p
  simpa [RingHom.comp_apply] using h

theorem phi_comp_betaPoly (K : Type) [Field K] :
    (phi K).comp (betaPoly K) = deltaPoly K := by
  have hcompA0 : (phi K).comp (algebraMap (R0 K) (A0 K)) = alpha K := by
    simpa [phi] using IsLocalization.Away.lift_comp (R := R0 K) (S := A0 K)
      (x := S2801E37Y K) (g := alpha K) (alpha_S2801E37Y_isUnit K)
  have hy0 : phi K (y0 K) = tInv K := by
    rw [y0_eq_algebraMap K]
    rw [show (phi K) ((algebraMap (R0 K) (A0 K)) (S2801E37Y K)) = (alpha K) (S2801E37Y K) from
      RingHom.congr_fun hcompA0 (S2801E37Y K)]
    exact alpha_S2801E37Y K
  have hyInv : phi K (yInv K) = t1 K := by
    have hprod : phi K (yInv K) * tInv K = 1 := by
      calc phi K (yInv K) * tInv K = phi K (yInv K) * phi K (y0 K) := by rw [hy0]
        _ = phi K (yInv K * y0 K) := by rw [map_mul]
        _ = phi K 1 := by rw [yInv_mul_y0 K]
        _ = 1 := map_one (phi K)
    calc phi K (yInv K) = phi K (yInv K) * (tInv K * t1 K) := by rw [tInv_mul_t1 K]; ring
      _ = (phi K (yInv K) * tInv K) * t1 K := by ring
      _ = 1 * t1 K := by rw [hprod]
      _ = t1 K := by ring
  have hx0 : phi K (x0 K) = s1 K * tInv K := by
    rw [x0_eq_algebraMap K]
    rw [show (phi K) ((algebraMap (R0 K) (A0 K)) (S2801E37X K)) = (alpha K) (S2801E37X K) from
      RingHom.congr_fun hcompA0 (S2801E37X K)]
    simp [alpha, alphaPoly, evalVals]
  apply MvPolynomial.ringHom_ext
  · intro a
    change phi K (betaPoly K (MvPolynomial.C a)) = deltaPoly K (MvPolynomial.C a)
    have hmk0 : Ideal.Quotient.mk (S2801E37Ideal K) (MvPolynomial.C a) =
        algebraMap K (R0 K) a := by
      exact Ideal.Quotient.mk_algebraMap K (I := S2801E37Ideal K) a
    have h1 : phi K (betaPoly K (MvPolynomial.C a)) =
        alpha K ((Ideal.Quotient.mk (S2801E37Ideal K)) (MvPolynomial.C a)) := by
      simp only [betaPoly, MvPolynomial.eval₂Hom_C]
      rw [IsScalarTower.algebraMap_apply K (R0 K) (A0 K)]
      rw [show (phi K) ((algebraMap (R0 K) (A0 K)) ((algebraMap K (R0 K)) a)) =
          (alpha K) ((algebraMap K (R0 K)) a) from
        RingHom.congr_fun hcompA0 ((algebraMap K (R0 K)) a)]
      rw [← hmk0]
    rw [h1]
    have hdelta : deltaPoly K (MvPolynomial.C a) = algebraMap K (A1 K) a := by
      simp only [deltaPoly, MvPolynomial.eval₂Hom_C]
    rw [hdelta]
    simp [alpha, alphaPoly, MvPolynomial.eval₂Hom_C]
  · intro i
    fin_cases i
    · change phi K (betaPoly K (MvPolynomial.X 0)) = deltaPoly K (MvPolynomial.X 0)
      have hL : betaPoly K (MvPolynomial.X 0) = x0 K * yInv K := by
        simp [betaPoly, betaVals]
      have hR : deltaPoly K (MvPolynomial.X 0) = s1 K := by
        simp [deltaPoly]
      rw [hL, hR, map_mul, hx0, hyInv]
      rw [mul_assoc (s1 K) (tInv K) (t1 K), tInv_mul_t1 K, mul_one]
    · change phi K (betaPoly K (MvPolynomial.X 1)) = deltaPoly K (MvPolynomial.X 1)
      have hL : betaPoly K (MvPolynomial.X 1) = yInv K := by
        simp [betaPoly, betaVals]
      have hR : deltaPoly K (MvPolynomial.X 1) = t1 K := by
        simp [deltaPoly]
      rw [hL, hR, hyInv]

theorem phi_comp_beta (K : Type) [Field K] :
    (phi K).comp (beta K) = algebraMap (R1 K) (A1 K) := by
  apply Ideal.Quotient.ringHom_ext
  rw [RingHom.comp_assoc]
  change (phi K).comp (betaPoly K) =
    (algebraMap (R1 K) (A1 K)).comp (Ideal.Quotient.mk (E37ChartYIdeal K))
  rw [phi_comp_betaPoly K, deltaPoly_eq K]

theorem phi_psi (K : Type) [Field K] : (phi K).comp (psi K) = RingHom.id (A1 K) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (tbar K))
  rw [RingHom.comp_assoc]
  rw [show (psi K).comp (algebraMap (R1 K) (A1 K)) = beta K from
    IsLocalization.Away.lift_comp (R := R1 K) (S := A1 K) (x := tbar K)
      (g := beta K) (beta_tbar_isUnit K)]
  simpa using phi_comp_beta K

/-! ## 1. The ring equivalence of the two overlap localisation rings -/

/-- The ring equivalence between the two overlap localisation rings: the forward
direction is `phi : A0 →+* A1` and the inverse direction is `psi : A1 →+* A0`. -/
noncomputable def curveChartOverlapTransitionRingEquiv (K : Type) [Field K] :
    A0 K ≃+* A1 K :=
  RingEquiv.ofRingHom (phi K) (psi K) (phi_psi K) (psi_phi K)

/-- The forward direction of the overlap transition ring equivalence is `phi`. -/
theorem curveChartOverlapTransitionRingEquiv_apply (K : Type) [Field K] (a : A0 K) :
    curveChartOverlapTransitionRingEquiv K a = phi K a := rfl

/-- The inverse direction of the overlap transition ring equivalence is `psi`. -/
theorem curveChartOverlapTransitionRingEquiv_symm_apply (K : Type) [Field K] (b : A1 K) :
    (curveChartOverlapTransitionRingEquiv K).symm b = psi K b := rfl

/-! ## 2. The transition isomorphism of the overlap schemes -/

noncomputable def S2820E37TransitionIso (K : Type) [Field K] :
    E37ChartZOverlap K ≅ E37ChartYOverlap K :=
  Iso.mk (Spec.map (CommRingCat.ofHom (psi K))) (Spec.map (CommRingCat.ofHom (phi K)))
    (by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, psi_phi, CommRingCat.ofHom_id,
        Spec.map_id])
    (by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, phi_psi, CommRingCat.ofHom_id,
        Spec.map_id])

/-- The fixed E37 projective scheme, using the actual transition isomorphism. -/
noncomputable abbrev S2820E37ProjectiveScheme (K : Type) [Field K] : Scheme :=
  E37ProjGluedScheme K (S2820E37TransitionIso K)

noncomputable abbrev S2820E37ChartZMap (K : Type) [Field K] :
    S2801E37AffineScheme K ⟶ S2820E37ProjectiveScheme K :=
  E37ProjChartZMap K (S2820E37TransitionIso K)

noncomputable abbrev S2820E37ChartYMap (K : Type) [Field K] :
    E37ChartYScheme K ⟶ S2820E37ProjectiveScheme K :=
  E37ProjChartYMap K (S2820E37TransitionIso K)

noncomputable abbrev S2820E37PointAtInfinity (K : Type) [Field K] :
    S2820E37ProjectiveScheme K :=
  E37ProjPointAtInfinity K (S2820E37TransitionIso K)

#check S2820E37TransitionIso
#check S2820E37ProjectiveScheme
#check S2820E37ChartZMap
#check S2820E37ChartYMap
#check S2820E37PointAtInfinity
#print axioms S2820E37TransitionIso
#print axioms S2820E37ProjectiveScheme

end LeanFormal.IUT.XiFPaper.S2820E37TransitionActual
end
