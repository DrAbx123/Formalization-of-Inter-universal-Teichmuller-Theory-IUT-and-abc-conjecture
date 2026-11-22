/-
  G1 -- Fermat: the overlap of the two standard affine charts.

  Chart 0 (x ^ n + y ^ n = 1):
    ring R n = Q[x,y] / (x^n + y^n - 1),  x0 = x, x1 = y.
  Chart infinity (1 + s ^ n = r ^ n):
    ring R2 n = Q[s,r] / (1 + s^n - r^n),  s1 = s = X 0,  r1 = r = X 1.

  Change of variables:  r = x^{-1}, s = y * x^{-1};
  inverse:              x = r^{-1}, y = s * r^{-1}.

  We show that the two overlaps Away x0 and Away r1 are canonically isomorphic
  (as rings, and hence that the corresponding affine schemes are isomorphic), and that
  the overlap sits openly in both charts.
-/
import tmp.sheaf.xif.paper.Mzk1G1FermatAffineChartActual
import tmp.sheaf.xif.paper.Mzk1G1FermatSecondChartActual
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Tactic

noncomputable section

open AlgebraicGeometry CategoryTheory
open MvPolynomial
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatAffineChartActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatSecondChartActual

set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1G1FermatOverlapActual

/-! ## The two chart rings -/

/-- The common polynomial ring Q[X0, X1]. -/
abbrev Poly2 : Type := MvPolynomial (Fin 2) ℚ

/-- The ring of the first affine chart x^n + y^n = 1. -/
abbrev Chart0Ring (n : Nat) : Type := Mzk1G1FermatAffineChartActual.R n

/-- The ring of the second (infinity) affine chart 1 + s^n = r^n. -/
abbrev ChartInfRing (n : Nat) : Type := Mzk1G1FermatSecondChartActual.R2 n

abbrev ideal0 (n : Nat) : Ideal Poly2 := Ideal.span {fermatEquation n}
abbrev idealInf (n : Nat) : Ideal Poly2 := Ideal.span {secondEquation n}

theorem fermatEquation_def (n : Nat) :
    fermatEquation n = (MvPolynomial.X 0 : Poly2) ^ n + (MvPolynomial.X 1 : Poly2) ^ n - 1 :=
  rfl

theorem secondEquation_def (n : Nat) :
    secondEquation n = (1 : Poly2) + (MvPolynomial.X 0 : Poly2) ^ n - (MvPolynomial.X 1 : Poly2) ^ n :=
  rfl

theorem ideal0_def (n : Nat) : ideal0 n = Ideal.span {fermatEquation n} := rfl
theorem idealInf_def (n : Nat) : idealInf n = Ideal.span {secondEquation n} := rfl

/-- The class of X 0 in the first chart. -/
def x0 (n : Nat) : Chart0Ring n := Ideal.Quotient.mk (ideal0 n) (MvPolynomial.X 0)
/-- The class of X 1 in the first chart. -/
def x1 (n : Nat) : Chart0Ring n := Ideal.Quotient.mk (ideal0 n) (MvPolynomial.X 1)
/-- The class of X 1 in the second chart, i.e. r. -/
def r1 (n : Nat) : ChartInfRing n := Ideal.Quotient.mk (idealInf n) (MvPolynomial.X 1)
/-- The class of X 0 in the second chart, i.e. s. -/
def s1 (n : Nat) : ChartInfRing n := Ideal.Quotient.mk (idealInf n) (MvPolynomial.X 0)

theorem x0_def (n : Nat) : x0 n = Ideal.Quotient.mk (ideal0 n) (MvPolynomial.X 0) := rfl
theorem x1_def (n : Nat) : x1 n = Ideal.Quotient.mk (ideal0 n) (MvPolynomial.X 1) := rfl
theorem r1_def (n : Nat) : r1 n = Ideal.Quotient.mk (idealInf n) (MvPolynomial.X 1) := rfl
theorem s1_def (n : Nat) : s1 n = Ideal.Quotient.mk (idealInf n) (MvPolynomial.X 0) := rfl

/-! ## The defining relations in the two charts -/

theorem chart0_relation (n : Nat) : x0 n ^ n + x1 n ^ n = 1 := by
  have h : Ideal.Quotient.mk (ideal0 n) (fermatEquation n) = 0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span (by simp)
  simp only [fermatEquation_def, map_sub, map_add, map_pow, map_one] at h
  rw [x0_def, x1_def]
  exact sub_eq_zero.mp h

theorem chartInf_relation (n : Nat) : 1 + s1 n ^ n = r1 n ^ n := by
  have h : Ideal.Quotient.mk (idealInf n) (secondEquation n) = 0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span (by simp)
  simp only [secondEquation_def, map_sub, map_add, map_pow, map_one] at h
  rw [s1_def, r1_def]
  exact sub_eq_zero.mp h

/-! ## The two overlaps -/

abbrev Overlap0 (n : Nat) : Type := Localization.Away (x0 n)
abbrev OverlapInf (n : Nat) : Type := Localization.Away (r1 n)

/-- x0 viewed in the overlap Away x0. -/
def u0 (n : Nat) : Overlap0 n := algebraMap (Chart0Ring n) (Overlap0 n) (x0 n)
/-- x1 viewed in the overlap Away x0. -/
def w0 (n : Nat) : Overlap0 n := algebraMap (Chart0Ring n) (Overlap0 n) (x1 n)
/-- x0^{-1} in the overlap Away x0. -/
def iu0 (n : Nat) : Overlap0 n := IsLocalization.Away.invSelf (S := Overlap0 n) (x0 n)

/-- r1 viewed in the overlap Away r1. -/
def u1 (n : Nat) : OverlapInf n := algebraMap (ChartInfRing n) (OverlapInf n) (r1 n)
/-- s1 viewed in the overlap Away r1. -/
def w1 (n : Nat) : OverlapInf n := algebraMap (ChartInfRing n) (OverlapInf n) (s1 n)
/-- r1^{-1} in the overlap Away r1. -/
def iu1 (n : Nat) : OverlapInf n := IsLocalization.Away.invSelf (S := OverlapInf n) (r1 n)

theorem u0_def (n : Nat) : u0 n = algebraMap (Chart0Ring n) (Overlap0 n) (x0 n) := rfl
theorem w0_def (n : Nat) : w0 n = algebraMap (Chart0Ring n) (Overlap0 n) (x1 n) := rfl
theorem iu0_def (n : Nat) : iu0 n = IsLocalization.Away.invSelf (S := Overlap0 n) (x0 n) := rfl
theorem u1_def (n : Nat) : u1 n = algebraMap (ChartInfRing n) (OverlapInf n) (r1 n) := rfl
theorem w1_def (n : Nat) : w1 n = algebraMap (ChartInfRing n) (OverlapInf n) (s1 n) := rfl
theorem iu1_def (n : Nat) : iu1 n = IsLocalization.Away.invSelf (S := OverlapInf n) (r1 n) := rfl

theorem u0_mul_iu0 (n : Nat) : u0 n * iu0 n = 1 :=
  IsLocalization.Away.mul_invSelf (S := Overlap0 n) (x0 n)

theorem iu0_mul_u0 (n : Nat) : iu0 n * u0 n = 1 :=
  (mul_comm (iu0 n) (u0 n)).trans (u0_mul_iu0 n)

theorem u1_mul_iu1 (n : Nat) : u1 n * iu1 n = 1 :=
  IsLocalization.Away.mul_invSelf (S := OverlapInf n) (r1 n)

theorem iu1_mul_u1 (n : Nat) : iu1 n * u1 n = 1 :=
  (mul_comm (iu1 n) (u1 n)).trans (u1_mul_iu1 n)

/-- The structure map of the first chart into its overlap. -/
def base0 (n : Nat) : ℚ →+* Overlap0 n :=
  (algebraMap (Chart0Ring n) (Overlap0 n)).comp (algebraMap ℚ (Chart0Ring n))

/-- The structure map of the second chart into its overlap. -/
def base1 (n : Nat) : ℚ →+* OverlapInf n :=
  (algebraMap (ChartInfRing n) (OverlapInf n)).comp (algebraMap ℚ (ChartInfRing n))

theorem base0_def (n : Nat) :
    base0 n = (algebraMap (Chart0Ring n) (Overlap0 n)).comp (algebraMap ℚ (Chart0Ring n)) := rfl
theorem base1_def (n : Nat) :
    base1 n = (algebraMap (ChartInfRing n) (OverlapInf n)).comp (algebraMap ℚ (ChartInfRing n)) := rfl

theorem algebraMap_rat_chart0 (n : Nat) (r : ℚ) :
    algebraMap ℚ (Chart0Ring n) r = Ideal.Quotient.mk (ideal0 n) (MvPolynomial.C r) := by
  have h := Ideal.Quotient.mk_algebraMap (I := ideal0 n) (x := r)
  rw [MvPolynomial.algebraMap_eq] at h
  exact h.symm

theorem algebraMap_rat_chartInf (n : Nat) (r : ℚ) :
    algebraMap ℚ (ChartInfRing n) r = Ideal.Quotient.mk (idealInf n) (MvPolynomial.C r) := by
  have h := Ideal.Quotient.mk_algebraMap (I := idealInf n) (x := r)
  rw [MvPolynomial.algebraMap_eq] at h
  exact h.symm

/-! ## The two substitution homomorphisms on Q[X0,X1] -/

/-- Substitution r = X1^{-1}, s = X0 * X1^{-1} (from chart 0 to the overlap at r1). -/
def psiAux (n : Nat) : Poly2 →+* OverlapInf n :=
  MvPolynomial.eval₂Hom (base1 n)
    (fun i : Fin 2 => if (i : ℕ) = 0 then iu1 n else w1 n * iu1 n)

/-- Substitution x = X1^{-1}, y = X0 * X1^{-1} (from chart infinity to the overlap at x0). -/
def phiAux (n : Nat) : Poly2 →+* Overlap0 n :=
  MvPolynomial.eval₂Hom (base0 n)
    (fun i : Fin 2 => if (i : ℕ) = 0 then w0 n * iu0 n else iu0 n)

theorem psiAux_def (n : Nat) :
    psiAux n = MvPolynomial.eval₂Hom (base1 n)
      (fun i : Fin 2 => if (i : ℕ) = 0 then iu1 n else w1 n * iu1 n) := rfl

theorem phiAux_def (n : Nat) :
    phiAux n = MvPolynomial.eval₂Hom (base0 n)
      (fun i : Fin 2 => if (i : ℕ) = 0 then w0 n * iu0 n else iu0 n) := rfl

theorem psiAux_zero (n : Nat) : psiAux n (MvPolynomial.X 0) = iu1 n := by
  rw [psiAux_def, MvPolynomial.eval₂Hom_X']
  show (if (((0 : Fin 2) : ℕ) = 0) then iu1 n else w1 n * iu1 n) = iu1 n
  exact if_pos rfl

theorem psiAux_one (n : Nat) : psiAux n (MvPolynomial.X 1) = w1 n * iu1 n := by
  rw [psiAux_def, MvPolynomial.eval₂Hom_X']
  show (if (((1 : Fin 2) : ℕ) = 0) then iu1 n else w1 n * iu1 n) = w1 n * iu1 n
  exact if_neg (by decide)

theorem phiAux_zero (n : Nat) : phiAux n (MvPolynomial.X 0) = w0 n * iu0 n := by
  rw [phiAux_def, MvPolynomial.eval₂Hom_X']
  show (if (((0 : Fin 2) : ℕ) = 0) then w0 n * iu0 n else iu0 n) = w0 n * iu0 n
  exact if_pos rfl

theorem phiAux_one (n : Nat) : phiAux n (MvPolynomial.X 1) = iu0 n := by
  rw [phiAux_def, MvPolynomial.eval₂Hom_X']
  show (if (((1 : Fin 2) : ℕ) = 0) then w0 n * iu0 n else iu0 n) = iu0 n
  exact if_neg (by decide)

theorem psiAux_fermat (n : Nat) : psiAux n (fermatEquation n) = 0 := by
  have hrel' : (1 : OverlapInf n) + algebraMap (ChartInfRing n) (OverlapInf n) (s1 n) ^ n
      = algebraMap (ChartInfRing n) (OverlapInf n) (r1 n) ^ n := by
    have h := congrArg (algebraMap (ChartInfRing n) (OverlapInf n)) (chartInf_relation n)
    simpa only [map_add, map_one, map_pow] using h
  have hrel : 1 + w1 n ^ n = u1 n ^ n := by
    rw [w1_def, u1_def]
    exact hrel'
  have hu : u1 n ^ n * iu1 n ^ n = 1 := by
    rw [← mul_pow, u1_mul_iu1, one_pow]
  have key : iu1 n ^ n + w1 n ^ n * iu1 n ^ n = 1 := by
    calc iu1 n ^ n + w1 n ^ n * iu1 n ^ n = (1 + w1 n ^ n) * iu1 n ^ n := by ring
      _ = u1 n ^ n * iu1 n ^ n := by rw [hrel]
      _ = 1 := hu
  simp only [fermatEquation_def, map_sub, map_add, map_pow, map_one, psiAux_zero, psiAux_one]
  rw [sub_eq_zero, mul_pow]
  exact key

theorem phiAux_second (n : Nat) : phiAux n (secondEquation n) = 0 := by
  have hrel' : algebraMap (Chart0Ring n) (Overlap0 n) (x0 n) ^ n
      + algebraMap (Chart0Ring n) (Overlap0 n) (x1 n) ^ n = 1 := by
    have h := congrArg (algebraMap (Chart0Ring n) (Overlap0 n)) (chart0_relation n)
    simpa only [map_add, map_one, map_pow] using h
  have hrel : u0 n ^ n + w0 n ^ n = 1 := by
    rw [u0_def, w0_def]
    exact hrel'
  have hu : u0 n ^ n * iu0 n ^ n = 1 := by
    rw [← mul_pow, u0_mul_iu0, one_pow]
  have key : 1 + w0 n ^ n * iu0 n ^ n = iu0 n ^ n := by
    have h : iu0 n ^ n = 1 + w0 n ^ n * iu0 n ^ n := by
      calc iu0 n ^ n = 1 * iu0 n ^ n := by ring
        _ = (u0 n ^ n + w0 n ^ n) * iu0 n ^ n := by rw [← hrel]
        _ = u0 n ^ n * iu0 n ^ n + w0 n ^ n * iu0 n ^ n := by rw [add_mul]
        _ = 1 + w0 n ^ n * iu0 n ^ n := by rw [hu]
    exact h.symm
  simp only [secondEquation_def, map_sub, map_add, map_pow, map_one, phiAux_zero, phiAux_one]
  rw [sub_eq_zero, mul_pow]
  exact key

theorem psiAux_ker (n : Nat) : ∀ a : Poly2, a ∈ ideal0 n → psiAux n a = 0 := by
  have hle : ideal0 n ≤ RingHom.ker (psiAux n) := by
    refine Ideal.span_le.mpr ?_
    intro x hx
    have hx' : x = fermatEquation n := by simpa using hx
    subst hx'
    exact RingHom.mem_ker.mpr (psiAux_fermat n)
  intro a ha
  exact RingHom.mem_ker.mp (hle ha)

theorem phiAux_ker (n : Nat) : ∀ a : Poly2, a ∈ idealInf n → phiAux n a = 0 := by
  have hle : idealInf n ≤ RingHom.ker (phiAux n) := by
    refine Ideal.span_le.mpr ?_
    intro x hx
    have hx' : x = secondEquation n := by simpa using hx
    subst hx'
    exact RingHom.mem_ker.mpr (phiAux_second n)
  intro a ha
  exact RingHom.mem_ker.mp (hle ha)

/-- The substitution induced on the quotient ring of the first chart. -/
def psi (n : Nat) : Chart0Ring n →+* OverlapInf n :=
  Ideal.Quotient.lift (ideal0 n) (psiAux n) (psiAux_ker n)

/-- The substitution induced on the quotient ring of the second chart. -/
def phi (n : Nat) : ChartInfRing n →+* Overlap0 n :=
  Ideal.Quotient.lift (idealInf n) (phiAux n) (phiAux_ker n)

theorem psi_def (n : Nat) : psi n = Ideal.Quotient.lift (ideal0 n) (psiAux n) (psiAux_ker n) := rfl
theorem phi_def (n : Nat) : phi n = Ideal.Quotient.lift (idealInf n) (phiAux n) (phiAux_ker n) := rfl

@[simp]
theorem psi_mk (n : Nat) (a : Poly2) :
    psi n (Ideal.Quotient.mk (ideal0 n) a) = psiAux n a := rfl

@[simp]
theorem phi_mk (n : Nat) (a : Poly2) :
    phi n (Ideal.Quotient.mk (idealInf n) a) = phiAux n a := rfl

theorem psi_x0 (n : Nat) : psi n (x0 n) = iu1 n := by
  rw [x0_def, psi_mk, psiAux_zero]

theorem psi_x1 (n : Nat) : psi n (x1 n) = w1 n * iu1 n := by
  rw [x1_def, psi_mk, psiAux_one]

theorem phi_s1 (n : Nat) : phi n (s1 n) = w0 n * iu0 n := by
  rw [s1_def, phi_mk, phiAux_zero]

theorem phi_r1 (n : Nat) : phi n (r1 n) = iu0 n := by
  rw [r1_def, phi_mk, phiAux_one]

/-! ## Unit-ness of the two coordinates in the overlaps -/

theorem iu0_isUnit (n : Nat) : IsUnit (iu0 n) :=
  isUnit_iff_exists_inv.mpr ⟨u0 n, iu0_mul_u0 n⟩

theorem iu1_isUnit (n : Nat) : IsUnit (iu1 n) :=
  isUnit_iff_exists_inv.mpr ⟨u1 n, iu1_mul_u1 n⟩

theorem hpsi (n : Nat) : IsUnit (psi n (x0 n)) := by
  rw [psi_x0]
  exact iu1_isUnit n

theorem hphi (n : Nat) : IsUnit (phi n (r1 n)) := by
  rw [phi_r1]
  exact iu0_isUnit n

/-! ## The induced maps between the overlaps -/

/-- alpha : Away x0 -> Away r1, induced by r = x^{-1}, s = y x^{-1}. -/
def alpha (n : Nat) : Overlap0 n →+* OverlapInf n :=
  IsLocalization.Away.lift (x0 n) (g := psi n) (hpsi n)

/-- beta : Away r1 -> Away x0, induced by x = r^{-1}, y = s r^{-1}. -/
def beta (n : Nat) : OverlapInf n →+* Overlap0 n :=
  IsLocalization.Away.lift (r1 n) (g := phi n) (hphi n)

theorem alpha_def (n : Nat) : alpha n = IsLocalization.Away.lift (x0 n) (g := psi n) (hpsi n) := rfl
theorem beta_def (n : Nat) : beta n = IsLocalization.Away.lift (r1 n) (g := phi n) (hphi n) := rfl

theorem alpha_comp_algebraMap (n : Nat) :
    (alpha n).comp (algebraMap (Chart0Ring n) (Overlap0 n)) = psi n :=
  IsLocalization.Away.lift_comp (g := psi n) (x0 n) (hpsi n)

theorem beta_comp_algebraMap (n : Nat) :
    (beta n).comp (algebraMap (ChartInfRing n) (OverlapInf n)) = phi n :=
  IsLocalization.Away.lift_comp (g := phi n) (r1 n) (hphi n)

theorem alpha_algebraMap (n : Nat) (a : Chart0Ring n) :
    alpha n (algebraMap (Chart0Ring n) (Overlap0 n) a) = psi n a :=
  RingHom.congr_fun (alpha_comp_algebraMap n) a

theorem beta_algebraMap (n : Nat) (a : ChartInfRing n) :
    beta n (algebraMap (ChartInfRing n) (OverlapInf n) a) = phi n a :=
  RingHom.congr_fun (beta_comp_algebraMap n) a

theorem alpha_u0 (n : Nat) : alpha n (u0 n) = iu1 n := by
  rw [u0_def, alpha_algebraMap, psi_x0]

theorem beta_u1 (n : Nat) : beta n (u1 n) = iu0 n := by
  rw [u1_def, beta_algebraMap, phi_r1]

theorem alpha_iu0 (n : Nat) : alpha n (iu0 n) = u1 n := by
  have h1 : alpha n (iu0 n) * alpha n (u0 n) = 1 := by
    rw [← map_mul, iu0_mul_u0, map_one]
  rw [alpha_u0] at h1
  calc alpha n (iu0 n) = alpha n (iu0 n) * 1 := (mul_one _).symm
    _ = alpha n (iu0 n) * (iu1 n * u1 n) := by rw [iu1_mul_u1]
    _ = (alpha n (iu0 n) * iu1 n) * u1 n := by rw [mul_assoc]
    _ = 1 * u1 n := by rw [h1]
    _ = u1 n := one_mul _

theorem beta_iu1 (n : Nat) : beta n (iu1 n) = u0 n := by
  have h1 : beta n (iu1 n) * beta n (u1 n) = 1 := by
    rw [← map_mul, iu1_mul_u1, map_one]
  rw [beta_u1] at h1
  calc beta n (iu1 n) = beta n (iu1 n) * 1 := (mul_one _).symm
    _ = beta n (iu1 n) * (iu0 n * u0 n) := by rw [iu0_mul_u0]
    _ = (beta n (iu1 n) * iu0 n) * u0 n := by rw [mul_assoc]
    _ = 1 * u0 n := by rw [h1]
    _ = u0 n := one_mul _

/-! ## Compatibility of alpha and beta with the two chart structure maps -/

theorem beta_comp_psiAux (n : Nat) :
    (beta n).comp (psiAux n)
      = (algebraMap (Chart0Ring n) (Overlap0 n)).comp (Ideal.Quotient.mk (ideal0 n)) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp only [RingHom.comp_apply, psiAux_def, MvPolynomial.eval₂Hom_C, base1_def,
      beta_algebraMap, algebraMap_rat_chartInf, phi_mk, phiAux_def, MvPolynomial.eval₂Hom_C,
      base0_def, algebraMap_rat_chart0]
  · intro i
    have h2 : i = 0 ∨ i = 1 := by
      have hi : (i : ℕ) = 0 ∨ (i : ℕ) = 1 := by
        have := i.isLt
        omega
      rcases hi with h0 | h1
      · exact Or.inl (Fin.ext (by simpa using h0))
      · exact Or.inr (Fin.ext (by simpa using h1))
    rcases h2 with h | h
    · rw [h]
      simp only [RingHom.comp_apply, psiAux_zero, beta_iu1, ← x0_def, ← u0_def]
    · rw [h]
      simp only [RingHom.comp_apply, psiAux_one, map_mul, w1_def, beta_algebraMap,
        beta_iu1, phi_s1, ← x1_def, ← w0_def]
      simp only [mul_assoc, iu0_mul_u0, mul_one]

theorem alpha_comp_phiAux (n : Nat) :
    (alpha n).comp (phiAux n)
      = (algebraMap (ChartInfRing n) (OverlapInf n)).comp (Ideal.Quotient.mk (idealInf n)) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp only [RingHom.comp_apply, phiAux_def, MvPolynomial.eval₂Hom_C, base0_def,
      alpha_algebraMap, algebraMap_rat_chart0, psi_mk, psiAux_def, MvPolynomial.eval₂Hom_C,
      base1_def, algebraMap_rat_chartInf]
  · intro i
    have h2 : i = 0 ∨ i = 1 := by
      have hi : (i : ℕ) = 0 ∨ (i : ℕ) = 1 := by
        have := i.isLt
        omega
      rcases hi with h0 | h1
      · exact Or.inl (Fin.ext (by simpa using h0))
      · exact Or.inr (Fin.ext (by simpa using h1))
    rcases h2 with h | h
    · rw [h]
      simp only [RingHom.comp_apply, phiAux_zero, map_mul, w0_def, alpha_algebraMap,
        psi_x1, alpha_iu0, ← s1_def, ← w1_def]
      simp only [mul_assoc, iu1_mul_u1, mul_one]
    · rw [h]
      simp only [RingHom.comp_apply, phiAux_one, alpha_iu0, ← r1_def, ← u1_def]

theorem ringHom_ext_quot0 {n : Nat} {f g : Chart0Ring n →+* Overlap0 n}
    (h : ∀ a : Poly2, f (Ideal.Quotient.mk (ideal0 n) a) = g (Ideal.Quotient.mk (ideal0 n) a)) :
    f = g := by
  refine RingHom.ext fun x => ?_
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective (I := ideal0 n) x
  exact h a

theorem beta_comp_psi (n : Nat) :
    (beta n).comp (psi n) = algebraMap (Chart0Ring n) (Overlap0 n) := by
  apply ringHom_ext_quot0 (n := n)
  intro a
  have h1 : psi n (Ideal.Quotient.mk (ideal0 n) a) = psiAux n a := psi_mk n a
  rw [RingHom.comp_apply, h1]
  exact RingHom.congr_fun (beta_comp_psiAux n) a

theorem alpha_comp_phi (n : Nat) :
    (alpha n).comp (phi n) = algebraMap (ChartInfRing n) (OverlapInf n) := by
  apply Ideal.Quotient.ringHom_ext
  have h1 : (phi n).comp (Ideal.Quotient.mk (idealInf n)) = phiAux n :=
    RingHom.ext fun a => by
      rw [RingHom.comp_apply]
      exact phi_mk n a
  have h2 : ((alpha n).comp (phi n)).comp (Ideal.Quotient.mk (idealInf n))
      = (alpha n).comp (phiAux n) := by
    rw [RingHom.comp_assoc, h1]
  rw [h2, alpha_comp_phiAux]

theorem alpha_beta (n : Nat) : (alpha n).comp (beta n) = RingHom.id (OverlapInf n) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (r1 n))
  rw [RingHom.comp_assoc, beta_comp_algebraMap, alpha_comp_phi, RingHom.id_comp]

theorem beta_alpha (n : Nat) : (beta n).comp (alpha n) = RingHom.id (Overlap0 n) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (x0 n))
  rw [RingHom.comp_assoc, alpha_comp_algebraMap, beta_comp_psi, RingHom.id_comp]

/-- The two overlaps are isomorphic as rings. -/
def overlapRingEquiv (n : Nat) : Overlap0 n ≃+* OverlapInf n where
  toFun := alpha n
  invFun := beta n
  left_inv x := RingHom.congr_fun (beta_alpha n) x
  right_inv x := RingHom.congr_fun (alpha_beta n) x
  map_mul' := (alpha n).map_mul
  map_add' := (alpha n).map_add

/-! ## The induced isomorphism of the overlaps as schemes -/

/-- Spec (Away r1) -> Spec (Away x0), i.e. from the first overlap to the second. -/
def overlapSpecMap01 (n : Nat) :
    Spec (CommRingCat.of (Overlap0 n)) ⟶ Spec (CommRingCat.of (OverlapInf n)) :=
  Spec.map (CommRingCat.ofHom (beta n))

/-- Spec (Away x0) -> Spec (Away r1). -/
def overlapSpecMap10 (n : Nat) :
    Spec (CommRingCat.of (OverlapInf n)) ⟶ Spec (CommRingCat.of (Overlap0 n)) :=
  Spec.map (CommRingCat.ofHom (alpha n))

theorem overlapSpecMap01_10 (n : Nat) :
    overlapSpecMap01 n ≫ overlapSpecMap10 n
      = 𝟙 (Spec (CommRingCat.of (Overlap0 n))) := by
  show Spec.map (CommRingCat.ofHom (beta n)) ≫ Spec.map (CommRingCat.ofHom (alpha n)) = 𝟙 _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, beta_alpha, CommRingCat.ofHom_id,
    Spec.map_id]

theorem overlapSpecMap10_01 (n : Nat) :
    overlapSpecMap10 n ≫ overlapSpecMap01 n
      = 𝟙 (Spec (CommRingCat.of (OverlapInf n))) := by
  show Spec.map (CommRingCat.ofHom (alpha n)) ≫ Spec.map (CommRingCat.ofHom (beta n)) = 𝟙 _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, alpha_beta, CommRingCat.ofHom_id,
    Spec.map_id]

/-- The two overlaps are isomorphic as schemes. -/
def overlapSchemeIso (n : Nat) :
    Spec (CommRingCat.of (Overlap0 n)) ≅ Spec (CommRingCat.of (OverlapInf n)) where
  hom := overlapSpecMap01 n
  inv := overlapSpecMap10 n
  hom_inv_id := overlapSpecMap01_10 n
  inv_hom_id := overlapSpecMap10_01 n

/-- The first overlap as an open subscheme of the first chart. -/
def overlapToChart0 (n : Nat) :
    Spec (CommRingCat.of (Overlap0 n)) ⟶ Spec (CommRingCat.of (Chart0Ring n)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (Chart0Ring n) (Overlap0 n)))

instance overlapToChart0_isOpenImmersion (n : Nat) : IsOpenImmersion (overlapToChart0 n) := by
  show IsOpenImmersion
    (Spec.map (CommRingCat.ofHom (algebraMap (Chart0Ring n) (Overlap0 n))))
  infer_instance

/-- The first overlap as an open subscheme of the second chart. -/
def overlapToChartInf (n : Nat) :
    Spec (CommRingCat.of (Overlap0 n)) ⟶ Spec (CommRingCat.of (ChartInfRing n)) :=
  (overlapSchemeIso n).hom ≫
    Spec.map (CommRingCat.ofHom (algebraMap (ChartInfRing n) (OverlapInf n)))

instance overlapToChartInf_isOpenImmersion (n : Nat) : IsOpenImmersion (overlapToChartInf n) := by
  show IsOpenImmersion ((overlapSchemeIso n).hom ≫
    Spec.map (CommRingCat.ofHom (algebraMap (ChartInfRing n) (OverlapInf n))))
  infer_instance

/-! ## Axiom checks -/

#print axioms chart0_relation
#print axioms chartInf_relation
#print axioms psiAux_fermat
#print axioms phiAux_second
#print axioms u0_mul_iu0
#print axioms iu0_mul_u0
#print axioms u1_mul_iu1
#print axioms iu1_mul_u1
#print axioms psi_x0
#print axioms psi_x1
#print axioms phi_s1
#print axioms phi_r1
#print axioms alpha_u0
#print axioms alpha_iu0
#print axioms beta_u1
#print axioms beta_iu1
#print axioms beta_comp_psi
#print axioms alpha_comp_phi
#print axioms alpha_beta
#print axioms beta_alpha
#print axioms overlapRingEquiv
#print axioms overlapSchemeIso
#print axioms overlapToChart0_isOpenImmersion
#print axioms overlapToChartInf_isOpenImmersion

end LeanFormal.IUT.XiFPaper.Mzk1G1FermatOverlapActual
