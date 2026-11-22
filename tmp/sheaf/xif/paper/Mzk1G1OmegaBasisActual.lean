/- G1-B Fermat Omega local bases actual: the section omega0 = (y dx - x dy)/n and the
local basis identities (n y^(n-1)) omega0 = dx on D(y), (n x^(n-1)) omega0 = -dy on D(x)
(route §3.1). -/
import tmp.sheaf.xif.paper.Mzk1G1OmegaActual
import Mathlib.Tactic
noncomputable section
open LeanFormal.IUT.XiFPaper.Mzk1G1OmegaActual
namespace LeanFormal.IUT.XiFPaper.Mzk1G1OmegaBasisActual

/-- n is a nonzero rational number for n >= 1. -/
theorem n_neq_zero_rat {n : ℕ} (hn : 1 ≤ n) : (n : ℚ) ≠ 0 := by
  have hpos : (0 : ℚ) < (n : ℚ) := by exact_mod_cast (by omega : 0 < n)
  exact ne_of_gt hpos

/-- n is a unit of the Q-algebra B n, for n >= 1. -/
theorem natCast_isUnit (n : ℕ) (hn : 1 ≤ n) : IsUnit (n : B n) := by
  rw [← map_natCast (algebraMap ℚ (B n)) n]
  exact IsUnit.map (algebraMap ℚ (B n)).toMonoidHom (isUnit_iff_ne_zero.mpr (n_neq_zero_rat hn))

/-- A unit of the scalar ring acts injectively on Omega. -/
theorem smul_eq_of_unit_smul_eq (n : ℕ) (hn : 1 ≤ n) {a b : Omega n}
    (h : ((↑(natCast_isUnit n hn).unit) : B n) • a =
      ((↑(natCast_isUnit n hn).unit) : B n) • b) : a = b := by
  have hinv : ((↑((natCast_isUnit n hn).unit)⁻¹) : B n) *
      ((↑(natCast_isUnit n hn).unit) : B n) = 1 := by
    simpa using Units.inv_mul_cancel_left ((natCast_isUnit n hn).unit) 1
  calc a = (1 : B n) • a := (one_smul _ _).symm
    _ = (((↑((natCast_isUnit n hn).unit)⁻¹) : B n) *
          ((↑(natCast_isUnit n hn).unit) : B n)) • a := by rw [hinv]
    _ = ((↑((natCast_isUnit n hn).unit)⁻¹) : B n) •
          (((↑(natCast_isUnit n hn).unit) : B n) • a) := by rw [smul_smul]
    _ = ((↑((natCast_isUnit n hn).unit)⁻¹) : B n) •
          (((↑(natCast_isUnit n hn).unit) : B n) • b) := by rw [h]
    _ = (((↑((natCast_isUnit n hn).unit)⁻¹) : B n) *
          ((↑(natCast_isUnit n hn).unit) : B n)) • b := by rw [smul_smul]
    _ = (1 : B n) • b := by rw [hinv]
    _ = b := one_smul _ _

/-- The derivation relation multiplied by x. -/
theorem x_mul_relation (n : ℕ) (hn : 1 ≤ n) :
    ((n : B n) * coordX n ^ n) • dX n +
      ((n : B n) * coordX n * coordY n ^ (n - 1)) • dY n = 0 := by
  have h := congrArg (fun z => (coordX n) • z) (derivation_relation n)
  have hL : (coordX n) • (((n : B n) * coordX n ^ (n - 1)) • dX n) =
      ((n : B n) * coordX n ^ n) • dX n := by
    rw [show ((n : B n) * coordX n ^ n) =
      ((coordX n) * ((n : B n) * coordX n ^ (n - 1))) by
      rw [show coordX n ^ n = coordX n * coordX n ^ (n - 1) from by
        rw [← pow_succ', Nat.sub_add_cancel hn]]
      ring]
    rw [smul_smul]
  have hR : (coordX n) • (((n : B n) * coordY n ^ (n - 1)) • dY n) =
      ((n : B n) * coordX n * coordY n ^ (n - 1)) • dY n := by
    rw [show ((n : B n) * coordX n * coordY n ^ (n - 1)) =
      ((coordX n) * ((n : B n) * coordY n ^ (n - 1))) by ring]
    rw [smul_smul]
  rw [smul_add, smul_zero, hL, hR] at h
  exact h

/-- The derivation relation multiplied by y. -/
theorem y_mul_relation (n : ℕ) (hn : 1 ≤ n) :
    ((n : B n) * coordY n * coordX n ^ (n - 1)) • dX n +
      ((n : B n) * coordY n ^ n) • dY n = 0 := by
  have h := congrArg (fun z => (coordY n) • z) (derivation_relation n)
  have hL : (coordY n) • (((n : B n) * coordX n ^ (n - 1)) • dX n) =
      ((n : B n) * coordY n * coordX n ^ (n - 1)) • dX n := by
    rw [show ((n : B n) * coordY n * coordX n ^ (n - 1)) =
      ((coordY n) * ((n : B n) * coordX n ^ (n - 1))) by ring]
    rw [smul_smul]
  have hR : (coordY n) • (((n : B n) * coordY n ^ (n - 1)) • dY n) =
      ((n : B n) * coordY n ^ n) • dY n := by
    rw [show ((n : B n) * coordY n ^ n) =
      ((coordY n) * ((n : B n) * coordY n ^ (n - 1))) by
      rw [show coordY n ^ n = coordY n * coordY n ^ (n - 1) from by
        rw [← pow_succ', Nat.sub_add_cancel hn]]
      ring]
    rw [smul_smul]
  rw [smul_add, smul_zero, hL, hR] at h
  exact h

theorem sum_eq_one (n : ℕ) : coordY n ^ n + coordX n ^ n = (1 : B n) := by
  have h : coordX n ^ n + coordY n ^ n = 1 := sub_eq_zero.mp (relation n)
  rw [add_comm]; exact h

/-- (n y^(n-1)) omega = n dx. -/
theorem n_y_pow_smul_omegaForm (n : ℕ) (hn : 1 ≤ n) :
    ((n : B n) * coordY n ^ (n - 1)) • omegaForm n = (n : B n) • dX n := by
  have hx := x_mul_relation n hn
  have hxy : ((n : B n) * coordX n * coordY n ^ (n - 1)) • dY n =
      -(((n : B n) * coordX n ^ n) • dX n) := by
    have h := add_eq_zero_iff_eq_neg.mp hx
    have h2 := congrArg Neg.neg h
    simpa using h2.symm
  have hsum := sum_eq_one n
  calc
    ((n : B n) * coordY n ^ (n - 1)) • omegaForm n
        = (((n : B n) * coordY n ^ (n - 1)) * coordY n) • dX n -
            (((n : B n) * coordY n ^ (n - 1)) * coordX n) • dY n := by
            simp only [omegaForm, smul_sub, smul_smul]
    _ = ((n : B n) * coordY n ^ n) • dX n -
            ((n : B n) * coordX n * coordY n ^ (n - 1)) • dY n := by
            rw [show ((n : B n) * coordY n ^ (n - 1)) * coordY n =
                  (n : B n) * coordY n ^ n by
                  rw [mul_assoc, show coordY n ^ (n - 1) * coordY n = coordY n ^ n by
                    rw [← pow_succ, Nat.sub_add_cancel hn]],
                show ((n : B n) * coordY n ^ (n - 1)) * coordX n =
                  (n : B n) * coordX n * coordY n ^ (n - 1) by ring]
    _ = ((n : B n) * coordY n ^ n) • dX n + ((n : B n) * coordX n ^ n) • dX n := by
            rw [hxy, sub_neg_eq_add]
    _ = ((n : B n) * (coordY n ^ n + coordX n ^ n)) • dX n := by
            rw [mul_add, add_smul]
    _ = (n : B n) • dX n := by rw [hsum, mul_one]

/-- (n x^(n-1)) omega = -(n dy). -/
theorem n_x_pow_smul_omegaForm (n : ℕ) (hn : 1 ≤ n) :
    ((n : B n) * coordX n ^ (n - 1)) • omegaForm n = -((n : B n) • dY n) := by
  have hy := y_mul_relation n hn
  have hyx : ((n : B n) * coordY n * coordX n ^ (n - 1)) • dX n =
      -(((n : B n) * coordY n ^ n) • dY n) := by
    exact add_eq_zero_iff_eq_neg.mp hy
  have hsum := sum_eq_one n
  calc
    ((n : B n) * coordX n ^ (n - 1)) • omegaForm n
        = (((n : B n) * coordX n ^ (n - 1)) * coordY n) • dX n -
            (((n : B n) * coordX n ^ (n - 1)) * coordX n) • dY n := by
            simp only [omegaForm, smul_sub, smul_smul]
    _ = ((n : B n) * coordY n * coordX n ^ (n - 1)) • dX n -
            ((n : B n) * coordX n ^ n) • dY n := by
            rw [show ((n : B n) * coordX n ^ (n - 1)) * coordY n =
                  (n : B n) * coordY n * coordX n ^ (n - 1) by ring,
                show ((n : B n) * coordX n ^ (n - 1)) * coordX n =
                  (n : B n) * coordX n ^ n by
                  rw [mul_assoc, show coordX n ^ (n - 1) * coordX n = coordX n ^ n by
                    rw [← pow_succ, Nat.sub_add_cancel hn]]]
    _ = -(((n : B n) * coordY n ^ n) • dY n) - ((n : B n) * coordX n ^ n) • dY n := by
            rw [hyx]
    _ = -(((n : B n) * (coordY n ^ n + coordX n ^ n)) • dY n) := by
            rw [mul_add, add_smul, neg_add, sub_eq_add_neg]
    _ = -((n : B n) • dY n) := by rw [hsum, mul_one]

/-- On D(y) the local basis dx is y^(n-1) times the Euler form. -/
theorem y_pow_smul_omegaForm (n : ℕ) (hn : 1 ≤ n) :
    (coordY n ^ (n - 1)) • omegaForm n = dX n := by
  have hu : ((↑(natCast_isUnit n hn).unit) : B n) = (n : B n) :=
    (natCast_isUnit n hn).unit_spec
  have h : ((↑(natCast_isUnit n hn).unit) : B n) •
      ((coordY n ^ (n - 1)) • omegaForm n) =
      ((↑(natCast_isUnit n hn).unit) : B n) • dX n := by
    calc ((↑(natCast_isUnit n hn).unit) : B n) • ((coordY n ^ (n - 1)) • omegaForm n)
        = (((↑(natCast_isUnit n hn).unit) : B n) * coordY n ^ (n - 1)) • omegaForm n :=
          smul_smul _ _ _
      _ = ((n : B n) * coordY n ^ (n - 1)) • omegaForm n := by rw [hu]
      _ = (n : B n) • dX n := n_y_pow_smul_omegaForm n hn
      _ = ((↑(natCast_isUnit n hn).unit) : B n) • dX n := by rw [hu]
  exact smul_eq_of_unit_smul_eq n hn h

/-- On D(x) the Euler form gives -dy. -/
theorem x_pow_smul_omegaForm (n : ℕ) (hn : 1 ≤ n) :
    (coordX n ^ (n - 1)) • omegaForm n = -dY n := by
  have hu : ((↑(natCast_isUnit n hn).unit) : B n) = (n : B n) :=
    (natCast_isUnit n hn).unit_spec
  have h : ((↑(natCast_isUnit n hn).unit) : B n) •
      ((coordX n ^ (n - 1)) • omegaForm n) =
      ((↑(natCast_isUnit n hn).unit) : B n) • (-dY n) := by
    calc ((↑(natCast_isUnit n hn).unit) : B n) • ((coordX n ^ (n - 1)) • omegaForm n)
        = (((↑(natCast_isUnit n hn).unit) : B n) * coordX n ^ (n - 1)) • omegaForm n :=
          smul_smul _ _ _
      _ = ((n : B n) * coordX n ^ (n - 1)) • omegaForm n := by rw [hu]
      _ = -((n : B n) • dY n) := n_x_pow_smul_omegaForm n hn
      _ = ((↑(natCast_isUnit n hn).unit) : B n) • (-dY n) := by rw [hu, smul_neg]
  exact smul_eq_of_unit_smul_eq n hn h

/-- The route section omega0 = (1/n)(y dx - x dy) = (y dx - x dy)/n. -/
noncomputable def omega0 (n : ℕ) (hn : 1 ≤ n) : Omega n :=
  ((↑((natCast_isUnit n hn).unit)⁻¹) : B n) • omegaForm n

/-- On D(y): (n y^(n-1)) omega0 = dx, i.e. omega0 = dx/(n y^(n-1)) is the local basis. -/
theorem n_y_pow_smul_omega0 (n : ℕ) (hn : 1 ≤ n) :
    ((n : B n) * coordY n ^ (n - 1)) • omega0 n hn = dX n := by
  have hu : ((↑(natCast_isUnit n hn).unit) : B n) = (n : B n) :=
    (natCast_isUnit n hn).unit_spec
  have hu2 : ((n : B n)) * ((↑((natCast_isUnit n hn).unit)⁻¹) : B n) = 1 :=
    (natCast_isUnit n hn).mul_val_inv
  have hscalar : ((n : B n) * coordY n ^ (n - 1)) *
      ((↑((natCast_isUnit n hn).unit)⁻¹) : B n) = coordY n ^ (n - 1) := by
    calc ((n : B n) * coordY n ^ (n - 1)) * ((↑((natCast_isUnit n hn).unit)⁻¹) : B n)
        = (((n : B n)) * ((↑((natCast_isUnit n hn).unit)⁻¹) : B n)) *
            coordY n ^ (n - 1) := by ring
      _ = 1 * coordY n ^ (n - 1) := by rw [hu2]
      _ = coordY n ^ (n - 1) := one_mul _
  calc
    ((n : B n) * coordY n ^ (n - 1)) • omega0 n hn
        = (((n : B n) * coordY n ^ (n - 1)) *
            ((↑((natCast_isUnit n hn).unit)⁻¹) : B n)) • omegaForm n := by
            rw [omega0, smul_smul]
    _ = (coordY n ^ (n - 1)) • omegaForm n := by rw [hscalar]
    _ = dX n := y_pow_smul_omegaForm n hn

/-- On D(x): (n x^(n-1)) omega0 = -dy, i.e. omega0 = -dy/(n x^(n-1)) is the local basis. -/
theorem n_x_pow_smul_omega0 (n : ℕ) (hn : 1 ≤ n) :
    ((n : B n) * coordX n ^ (n - 1)) • omega0 n hn = -dY n := by
  have hu : ((↑(natCast_isUnit n hn).unit) : B n) = (n : B n) :=
    (natCast_isUnit n hn).unit_spec
  have hu2 : ((n : B n)) * ((↑((natCast_isUnit n hn).unit)⁻¹) : B n) = 1 :=
    (natCast_isUnit n hn).mul_val_inv
  have hscalar : ((n : B n) * coordX n ^ (n - 1)) *
      ((↑((natCast_isUnit n hn).unit)⁻¹) : B n) = coordX n ^ (n - 1) := by
    calc ((n : B n) * coordX n ^ (n - 1)) * ((↑((natCast_isUnit n hn).unit)⁻¹) : B n)
        = (((n : B n)) * ((↑((natCast_isUnit n hn).unit)⁻¹) : B n)) *
            coordX n ^ (n - 1) := by ring
      _ = 1 * coordX n ^ (n - 1) := by rw [hu2]
      _ = coordX n ^ (n - 1) := one_mul _
  calc
    ((n : B n) * coordX n ^ (n - 1)) • omega0 n hn
        = (((n : B n) * coordX n ^ (n - 1)) *
            ((↑((natCast_isUnit n hn).unit)⁻¹) : B n)) • omegaForm n := by
            rw [omega0, smul_smul]
    _ = (coordX n ^ (n - 1)) • omegaForm n := by rw [hscalar]
    _ = -dY n := x_pow_smul_omegaForm n hn

#print axioms natCast_isUnit
#print axioms y_pow_smul_omegaForm
#print axioms n_y_pow_smul_omega0
#print axioms n_x_pow_smul_omega0
end LeanFormal.IUT.XiFPaper.Mzk1G1OmegaBasisActual
