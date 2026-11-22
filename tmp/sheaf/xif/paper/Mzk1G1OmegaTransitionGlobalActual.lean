/- G1-B Fermat Omega transition actual (stage 2): the overlap ring O0 = Away x0 of the
affine chart, the induced differentials d u0, d w0, and the derivative relation
n u^(n-1) du + n w^(n-1) dw = 0 in Omega_{O0/k} (route §3.1, A3 setup). -/
import tmp.sheaf.xif.paper.Mzk1G1FermatOverlapActual
import tmp.sheaf.xif.paper.Mzk1G1OmegaActual
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.Tactic
noncomputable section
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatOverlapActual
namespace LeanFormal.IUT.XiFPaper.Mzk1G1OmegaTransitionGlobalActual

/-- Generic: a natural multiple of a module element is the ring multiple. -/
theorem nsmul_smul_eq {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (n : ℕ) (a : R) (z : M) : n • (a • z) = ((n : R) * a) • z := by
  rw [← Nat.cast_smul_eq_nsmul R n, smul_smul]

variable (n : ℕ)

/-- The overlap O0 = Localization.Away x0 of the affine chart. -/
abbrev O0 (n : ℕ) : Type := Overlap0 n

/-- The absolute differential module of the overlap. -/
abbrev OM (n : ℕ) : Type := KaehlerDifferential ℚ (O0 n)

/-- d(u0) in Omega_{O0/k}. -/
noncomputable def du (n : ℕ) : OM n := KaehlerDifferential.D ℚ (O0 n) (u0 n)
/-- d(w0) in Omega_{O0/k}. -/
noncomputable def dw (n : ℕ) : OM n := KaehlerDifferential.D ℚ (O0 n) (w0 n)
/-- d(iu0) in Omega_{O0/k}. -/
noncomputable def diu (n : ℕ) : OM n := KaehlerDifferential.D ℚ (O0 n) (iu0 n)

/-- u0 is a unit (u0 * iu0 = 1). -/
theorem u0_isUnit (n : ℕ) : IsUnit (u0 n) :=
  isUnit_iff_exists_inv.mpr ⟨iu0 n, u0_mul_iu0 n⟩

/-- The Fermat relation u^n + w^n = 1 in the overlap. -/
theorem overlap_relation (n : ℕ) : u0 n ^ n + w0 n ^ n - 1 = 0 := by
  have h := congrArg (algebraMap (Chart0Ring n) (Overlap0 n)) (chart0_relation n)
  rw [map_add, map_pow, map_pow, map_one] at h
  rw [u0_def, w0_def]
  exact sub_eq_zero.mpr h

/-- The derivative relation n u^(n-1) du + n w^(n-1) dw = 0 in Omega_{O0/k}. -/
theorem overlap_derivation_relation (n : ℕ) :
    ((n : O0 n) * u0 n ^ (n - 1)) • du n +
      ((n : O0 n) * w0 n ^ (n - 1)) • dw n = 0 := by
  have h0 : KaehlerDifferential.D ℚ (O0 n) (u0 n ^ n) +
      KaehlerDifferential.D ℚ (O0 n) (w0 n ^ n) = 0 := by
    have h := congrArg (KaehlerDifferential.D ℚ (O0 n)) (overlap_relation n)
    simpa [map_sub, map_add, map_one, Derivation.map_one_eq_zero] using h
  have hu : KaehlerDifferential.D ℚ (O0 n) (u0 n ^ n) = n • (u0 n ^ (n - 1) • du n) := by
    rw [Derivation.leibniz_pow, du]
  have hw : KaehlerDifferential.D ℚ (O0 n) (w0 n ^ n) = n • (w0 n ^ (n - 1) • dw n) := by
    rw [Derivation.leibniz_pow, dw]
  rw [hu, hw, nsmul_smul_eq, nsmul_smul_eq] at h0
  exact h0

/-- d(iu0) = -iu0^2 du0 in the overlap (from iu0 * u0 = 1). -/
theorem diu_eq (n : ℕ) : diu n = (-((iu0 n) ^ 2)) • du n := by
  rw [diu, du]
  exact Derivation.leibniz_of_mul_eq_one (D := KaehlerDifferential.D ℚ (O0 n)) (iu0_mul_u0 n)

/-- The infinity-chart coordinates realized on the overlap: r = iu0, s = w0 iu0. -/
noncomputable def rr (n : ℕ) : O0 n := iu0 n
noncomputable def ss (n : ℕ) : O0 n := w0 n * iu0 n

/-- d(r) = d(iu0). -/
theorem d_rr (n : ℕ) : KaehlerDifferential.D ℚ (O0 n) (rr n) = diu n := by
  rw [rr, diu]

/-- d(s) = w0 d(iu0) + iu0 d(w0). -/
theorem d_ss (n : ℕ) :
    KaehlerDifferential.D ℚ (O0 n) (ss n) = w0 n • diu n + iu0 n • dw n := by
  rw [ss, Derivation.leibniz]
  rw [diu, dw]

#print axioms overlap_relation
#print axioms overlap_derivation_relation
#print axioms diu_eq

/-! ## Stage 2: the A3 transition omega_inf = u0^(n-3) omega_0 on the overlap -/

/-- Generic cancellation by a unit scalar. -/
theorem smul_eq_of_isUnit_smul_eq {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {c : R} (hc : IsUnit c) {a b : M} (h : c • a = c • b) : a = b := by
  rcases hc with ⟨u, rfl⟩
  have h' := congrArg (fun z : M => (↑u⁻¹ : R) • z) h
  have hinv : (↑u⁻¹ : R) * ↑u = 1 := by
    simpa using Units.inv_mul_cancel_left u (1 : R)
  simpa [smul_smul, hinv] using h'

/-- n is a unit in the overlap ring (Q-algebra). -/
theorem natCast_isUnit_O0 (n : ℕ) (hn : 1 ≤ n) : IsUnit (n : O0 n) := by
  have hq : (n : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mp hn)
  have h := IsUnit.map (algebraMap ℚ (O0 n)) (isUnit_iff_ne_zero.mpr hq)
  simpa using h

/-- The numerator w du - u dw of the local basis omega_0 = (w du - u dw)/n. -/
noncomputable def omega0O (n : ℕ) : OM n := w0 n • du n - u0 n • dw n

/-- The numerator s dr - r ds of the infinity-chart form. -/
noncomputable def omegaInfRaw (n : ℕ) : OM n :=
  ss n • KaehlerDifferential.D ℚ (O0 n) (rr n) -
    rr n • KaehlerDifferential.D ℚ (O0 n) (ss n)

/-- On the overlap, s dr - r ds = -iu0^2 dw0. -/
theorem omegaInfRaw_eq (n : ℕ) : omegaInfRaw n = (-((iu0 n) ^ 2)) • dw n := by
  have h1 : ss n • KaehlerDifferential.D ℚ (O0 n) (rr n) =
      -((w0 n * iu0 n ^ 3) • du n) := by
    calc ss n • KaehlerDifferential.D ℚ (O0 n) (rr n)
        = (w0 n * iu0 n) • diu n := by rw [ss, d_rr]
      _ = (w0 n * iu0 n) • ((-(iu0 n ^ 2)) • du n) := by rw [diu_eq]
      _ = -(((w0 n * iu0 n) * iu0 n ^ 2) • du n) := by
            rw [neg_smul, smul_neg, smul_smul]
      _ = -((w0 n * iu0 n ^ 3) • du n) := by
            rw [show (w0 n * iu0 n) * iu0 n ^ 2 = w0 n * iu0 n ^ 3 by ring]
  have h2 : rr n • KaehlerDifferential.D ℚ (O0 n) (ss n) =
      -((w0 n * iu0 n ^ 3) • du n) + (iu0 n ^ 2) • dw n := by
    rw [d_ss, smul_add]
    have hA : rr n • (w0 n • diu n) = -((w0 n * iu0 n ^ 3) • du n) := by
      calc rr n • (w0 n • diu n)
          = (iu0 n * w0 n) • diu n := by rw [rr, smul_smul]
        _ = (iu0 n * w0 n) • ((-(iu0 n ^ 2)) • du n) := by rw [diu_eq]
        _ = -(((iu0 n * w0 n) * iu0 n ^ 2) • du n) := by
              rw [neg_smul, smul_neg, smul_smul]
        _ = -((w0 n * iu0 n ^ 3) • du n) := by
              rw [show (iu0 n * w0 n) * iu0 n ^ 2 = w0 n * iu0 n ^ 3 by ring]
    have hB : rr n • (iu0 n • dw n) = (iu0 n ^ 2) • dw n := by
      rw [rr, smul_smul, show iu0 n * iu0 n = iu0 n ^ 2 by ring]
    rw [hA, hB]
  rw [omegaInfRaw, h1, h2, neg_smul]
  abel

/-- The infinity chart form scaled by u0^2 is -dw0. -/
theorem smul_sq_omegaInfRaw (n : ℕ) : (u0 n) ^ 2 • omegaInfRaw n = -(dw n) := by
  calc (u0 n) ^ 2 • omegaInfRaw n
      = (u0 n) ^ 2 • ((-(iu0 n) ^ 2) • dw n) := by rw [omegaInfRaw_eq]
    _ = -((u0 n) ^ 2 • ((iu0 n) ^ 2 • dw n)) := by rw [neg_smul, smul_neg]
    _ = -(((u0 n) ^ 2 * (iu0 n) ^ 2) • dw n) := by rw [smul_smul]
    _ = -((1 : O0 n) • dw n) := by
          rw [show (u0 n) ^ 2 * (iu0 n) ^ 2 = 1 by
            calc (u0 n) ^ 2 * (iu0 n) ^ 2 = (u0 n * iu0 n) ^ 2 := by ring
              _ = 1 := by rw [u0_mul_iu0]; norm_num]
    _ = -(dw n) := by rw [one_smul]

/-- The omega_0 numerator scaled by n u0^(n-1) is -n dw0, by the derivative relation. -/
theorem n_smul_omega0O (n : ℕ) (hn : 1 ≤ n) :
    (n : O0 n) • (u0 n ^ (n - 1) • omega0O n) = -((n : O0 n) • dw n) := by
  have hrel := overlap_derivation_relation n
  have hdu : ((n : O0 n) * u0 n ^ (n - 1)) • du n =
      -(((n : O0 n) * w0 n ^ (n - 1)) • dw n) := eq_neg_of_add_eq_zero_left hrel
  have hu : u0 n ^ (n - 1) * u0 n = u0 n ^ n := by
    rw [← pow_succ, Nat.sub_add_cancel hn]
  have hw : w0 n ^ (n - 1) * w0 n = w0 n ^ n := by
    rw [← pow_succ, Nat.sub_add_cancel hn]
  have hsum : w0 n ^ n + u0 n ^ n = (1 : O0 n) := by
    have h := overlap_relation n
    have h' : u0 n ^ n + w0 n ^ n = 1 := sub_eq_zero.mp h
    rw [add_comm]; exact h'
  calc (n : O0 n) • (u0 n ^ (n - 1) • omega0O n)
      = ((n : O0 n) * u0 n ^ (n - 1)) • omega0O n := by rw [smul_smul]
    _ = ((n : O0 n) * u0 n ^ (n - 1)) • (w0 n • du n - u0 n • dw n) := by rw [omega0O]
    _ = ((n : O0 n) * u0 n ^ (n - 1) * w0 n) • du n -
          ((n : O0 n) * u0 n ^ (n - 1) * u0 n) • dw n := by
          rw [smul_sub, smul_smul, smul_smul]
    _ = w0 n • (((n : O0 n) * u0 n ^ (n - 1)) • du n) -
          ((n : O0 n) * u0 n ^ n) • dw n := by
          rw [show (n : O0 n) * u0 n ^ (n - 1) * w0 n =
              w0 n * ((n : O0 n) * u0 n ^ (n - 1)) by ring]
          rw [← smul_smul]
          rw [show (n : O0 n) * u0 n ^ (n - 1) * u0 n = (n : O0 n) * u0 n ^ n by
                rw [mul_assoc, hu]]
    _ = -(((w0 n * ((n : O0 n) * w0 n ^ (n - 1)))) • dw n) -
          ((n : O0 n) * u0 n ^ n) • dw n := by
          rw [hdu, smul_neg, smul_smul]
    _ = -(((((n : O0 n) * w0 n ^ n) + ((n : O0 n) * u0 n ^ n))) • dw n) := by
          rw [show w0 n * ((n : O0 n) * w0 n ^ (n - 1)) = (n : O0 n) * (w0 n ^ (n - 1) * w0 n) by ring,
            hw, sub_eq_add_neg, ← neg_add, ← add_smul]
    _ = -(((n : O0 n) * (w0 n ^ n + u0 n ^ n)) • dw n) := by
          rw [show (n : O0 n) * w0 n ^ n + (n : O0 n) * u0 n ^ n =
            (n : O0 n) * (w0 n ^ n + u0 n ^ n) by ring]
    _ = -(((n : O0 n) * 1) • dw n) := by rw [hsum]
    _ = -((n : O0 n) • dw n) := by rw [mul_one]

/-- A3: on the overlap the infinity-chart form is u0^(n-3) times the affine form. -/
theorem omegaInfRaw_eq_pow_smul_omega0O (n : ℕ) (hn : 3 ≤ n) :
    omegaInfRaw n = (u0 n) ^ (n - 3) • omega0O n := by
  have h1 : 1 ≤ n := by omega
  have hpow : (u0 n) ^ (n - 1) = (u0 n) ^ 2 * (u0 n) ^ (n - 3) := by
    rw [← pow_add]
    congr 1
    omega
  have hL2 : ((n : O0 n) * (u0 n) ^ 2) • omegaInfRaw n =
      ((n : O0 n) * (u0 n) ^ 2) • ((u0 n) ^ (n - 3) • omega0O n) := by
    calc ((n : O0 n) * (u0 n) ^ 2) • omegaInfRaw n
        = (n : O0 n) • ((u0 n) ^ 2 • omegaInfRaw n) := by rw [smul_smul]
      _ = (n : O0 n) • (-(dw n)) := by rw [smul_sq_omegaInfRaw]
      _ = -((n : O0 n) • dw n) := by rw [smul_neg]
      _ = (n : O0 n) • ((u0 n) ^ (n - 1) • omega0O n) := by rw [n_smul_omega0O n h1]
      _ = ((n : O0 n) * (u0 n) ^ 2) • ((u0 n) ^ (n - 3) • omega0O n) := by
            rw [hpow]
            simp only [smul_smul]
            rw [show (n : O0 n) * ((u0 n) ^ 2 * (u0 n) ^ (n - 3)) =
                (n : O0 n) * u0 n ^ 2 * u0 n ^ (n - 3) by ring]
  have hc : IsUnit ((n : O0 n) * (u0 n) ^ 2) :=
    (natCast_isUnit_O0 n h1).mul ((u0_isUnit n).pow 2)
  exact smul_eq_of_isUnit_smul_eq hc hL2

#print axioms smul_sq_omegaInfRaw
#print axioms n_smul_omega0O
#print axioms omegaInfRaw_eq_pow_smul_omega0O

end LeanFormal.IUT.XiFPaper.Mzk1G1OmegaTransitionGlobalActual

