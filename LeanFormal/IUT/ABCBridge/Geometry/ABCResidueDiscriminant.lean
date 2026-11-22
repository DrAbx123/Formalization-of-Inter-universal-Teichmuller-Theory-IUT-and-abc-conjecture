import LeanFormal.IUT.ABCBridge.Statement
import LeanFormal.IUT.ABCBridge.Geometry.FreyWeierstrassCurve
import Mathlib.Data.ZMod.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
import Mathlib.Tactic

/-!
# The residue discriminant of the integral ABC curve

For the integral model `y² = x (x - a) (x + b)` and `a + b = c`, the
discriminant is `16 a² b² c²`.  This file identifies its actual residues,
their prime support, and their unit locus.  These are statements about the
displayed integral equation; minimality and conductor exponents are separate
questions.
-/

namespace LeanFormal.IUT

/-- The residue of the discriminant of the integral ABC equation. -/
def abcResidueDiscriminant (a b c p : ℕ) : ZMod p :=
  16 * (a : ZMod p) ^ 2 * (b : ZMod p) ^ 2 * (c : ZMod p) ^ 2

/-- The displayed residue is the cast of the actual integral discriminant. -/
theorem abcResidueDiscriminant_eq_natCast (a b c p : ℕ) :
    abcResidueDiscriminant a b c p = ((16 * (a * b * c) ^ 2 : ℕ) : ZMod p) := by
  simp only [abcResidueDiscriminant, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  ring

/-- This form allows support to be tested on the single integer `abc`. -/
theorem abcResidueDiscriminant_eq_product_square (a b c p : ℕ) :
    abcResidueDiscriminant a b c p = 16 * ((a * b * c : ℕ) : ZMod p) ^ 2 := by
  simp only [abcResidueDiscriminant, Nat.cast_mul]
  ring

/-- Divisibility detects vanishing even before a prime modulus is assumed. -/
theorem abcResidueDiscriminant_eq_zero_iff_dvd_discriminant (a b c p : ℕ) :
    abcResidueDiscriminant a b c p = 0 ↔ p ∣ 16 * (a * b * c) ^ 2 := by
  rw [abcResidueDiscriminant_eq_natCast, ZMod.natCast_eq_zero_iff]

/-- At an odd prime the factor `2` remains nonzero in the residue field. -/
theorem abc_two_natCast_ne_zero {p : ℕ} (hp : p.Prime) (hp_two : p ≠ 2) :
    (2 : ZMod p) ≠ 0 := by
  intro hzero
  have hdiv : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp hzero
  rcases (Nat.dvd_prime Nat.prime_two).mp hdiv with hone | htwo
  · exact hp.ne_one hone
  · exact hp_two htwo

/-- At an odd prime the factor `16` remains nonzero in the residue field. -/
theorem abc_sixteen_natCast_ne_zero {p : ℕ} (hp : p.Prime) (hp_two : p ≠ 2) :
    (16 : ZMod p) ≠ 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  have hpower := pow_ne_zero 4 (abc_two_natCast_ne_zero hp hp_two)
  norm_num at hpower ⊢
  exact hpower

/-- The actual discriminant residue is nonzero exactly off the support of `abc`. -/
theorem abcResidueDiscriminant_ne_zero_iff {a b c p : ℕ}
    (hp : p.Prime) (hp_two : p ≠ 2) :
    abcResidueDiscriminant a b c p ≠ 0 ↔ ¬ p ∣ a * b * c := by
  letI : Fact p.Prime := ⟨hp⟩
  rw [abcResidueDiscriminant_eq_product_square]
  simp [abc_sixteen_natCast_ne_zero hp hp_two, ZMod.natCast_eq_zero_iff, hp.dvd_mul]

/-- The complementary locus is exactly the odd-prime support of `abc`. -/
theorem abcResidueDiscriminant_eq_zero_iff {a b c p : ℕ}
    (hp : p.Prime) (hp_two : p ≠ 2) :
    abcResidueDiscriminant a b c p = 0 ↔ p ∣ a * b * c := by
  exact not_iff_not.mp (abcResidueDiscriminant_ne_zero_iff hp hp_two)

/-- The support is the union of the three actual prime-divisibility conditions. -/
theorem abcResidueDiscriminant_eq_zero_iff_factor {a b c p : ℕ}
    (hp : p.Prime) (hp_two : p ≠ 2) :
    abcResidueDiscriminant a b c p = 0 ↔ p ∣ a ∨ p ∣ b ∨ p ∣ c := by
  rw [abcResidueDiscriminant_eq_zero_iff hp hp_two]
  simp only [hp.dvd_mul, or_assoc]

/-- Each coordinate is nonzero precisely when the residue discriminant is nonzero. -/
theorem abcResidueDiscriminant_ne_zero_iff_coordinates {a b c p : ℕ}
    (hp : p.Prime) (hp_two : p ≠ 2) :
    abcResidueDiscriminant a b c p ≠ 0 ↔
      (a : ZMod p) ≠ 0 ∧ (b : ZMod p) ≠ 0 ∧ (c : ZMod p) ≠ 0 := by
  rw [ne_eq, abcResidueDiscriminant_eq_zero_iff_factor hp hp_two]
  simp only [not_or, ne_eq, ZMod.natCast_eq_zero_iff]

/-- A nonzero residue discriminant is a unit because the modulus is prime. -/
theorem abcResidueDiscriminant_isUnit_iff {a b c p : ℕ}
    (hp : p.Prime) (hp_two : p ≠ 2) :
    IsUnit (abcResidueDiscriminant a b c p) ↔ ¬ p ∣ a * b * c := by
  letI : Fact p.Prime := ⟨hp⟩
  rw [isUnit_iff_ne_zero, abcResidueDiscriminant_ne_zero_iff hp hp_two]

/-- The factor `16` is invertible at every odd prime. -/
theorem abc_sixteen_natCast_isUnit {p : ℕ} (hp : p.Prime) (hp_two : p ≠ 2) :
    IsUnit (16 : ZMod p) := by
  letI : Fact p.Prime := ⟨hp⟩
  exact isUnit_iff_ne_zero.mpr (abc_sixteen_natCast_ne_zero hp hp_two)

/-- The product and discriminant have exactly the same unit locus at odd primes. -/
theorem abcResidueDiscriminant_isUnit_iff_product {a b c p : ℕ}
    (hp : p.Prime) (hp_two : p ≠ 2) :
    IsUnit (abcResidueDiscriminant a b c p) ↔ IsUnit ((a * b * c : ℕ) : ZMod p) := by
  letI : Fact p.Prime := ⟨hp⟩
  rw [abcResidueDiscriminant_isUnit_iff hp hp_two, isUnit_iff_ne_zero]
  exact (not_congr (ZMod.natCast_eq_zero_iff (a * b * c) p)).symm

/-- All three coordinate residues are units exactly on the nonsingular locus. -/
theorem abcResidueDiscriminant_isUnit_iff_coordinates {a b c p : ℕ}
    (hp : p.Prime) (hp_two : p ≠ 2) :
    IsUnit (abcResidueDiscriminant a b c p) ↔
      IsUnit (a : ZMod p) ∧ IsUnit (b : ZMod p) ∧ IsUnit (c : ZMod p) := by
  letI : Fact p.Prime := ⟨hp⟩
  simp only [isUnit_iff_ne_zero]
  exact abcResidueDiscriminant_ne_zero_iff_coordinates hp hp_two

/-- At `2` this displayed integral model always has vanishing discriminant residue. -/
theorem abcResidueDiscriminant_two (a b c : ℕ) :
    abcResidueDiscriminant a b c 2 = 0 := by
  have hsixteen : (16 : ZMod 2) = 0 := by decide
  simp [abcResidueDiscriminant, hsixteen]

/-- The root pair `a,-b` collides exactly when `c` vanishes in the residue field. -/
theorem abc_residue_root_collision_iff {a b c p : ℕ} (hsum : a + b = c) :
    (a : ZMod p) = -(b : ZMod p) ↔ p ∣ c := by
  have hcast : (a : ZMod p) + (b : ZMod p) = (c : ZMod p) := by
    simpa only [Nat.cast_add] using congrArg (fun n : ℕ => (n : ZMod p)) hsum
  rw [← ZMod.natCast_eq_zero_iff c p, ← hcast, ← sub_neg_eq_add, sub_eq_zero]

/-- The three roots of `x (x-a) (x+b)` are distinct exactly off `abc`. -/
theorem abc_residue_roots_distinct_iff {a b c p : ℕ} (hsum : a + b = c)
    (hp : p.Prime) (hp_two : p ≠ 2) :
    abcResidueDiscriminant a b c p ≠ 0 ↔
      (0 : ZMod p) ≠ (a : ZMod p) ∧
        (0 : ZMod p) ≠ -(b : ZMod p) ∧
        (a : ZMod p) ≠ -(b : ZMod p) := by
  rw [abcResidueDiscriminant_ne_zero_iff_coordinates hp hp_two]
  have hlast : (a : ZMod p) ≠ -(b : ZMod p) ↔ (c : ZMod p) ≠ 0 := by
    simpa only [ne_eq, ZMod.natCast_eq_zero_iff] using
      not_congr (abc_residue_root_collision_iff (p := p) hsum)
  constructor
  · rintro ⟨ha, hb, hc⟩
    exact ⟨ha.symm, (neg_ne_zero.mpr hb).symm, hlast.mpr hc⟩
  · rintro ⟨ha, hb, hab⟩
    exact ⟨ha.symm, neg_ne_zero.mp hb.symm, hlast.mp hab⟩

/-- Prime `2` is the only prime excluded by the coefficient `16`. -/
theorem abcResidueDiscriminant_eq_zero_iff_prime {a b c p : ℕ} (hp : p.Prime) :
    abcResidueDiscriminant a b c p = 0 ↔ p = 2 ∨ p ∣ a * b * c := by
  by_cases hp_two : p = 2
  · subst p
    simp [abcResidueDiscriminant_two]
  · rw [abcResidueDiscriminant_eq_zero_iff hp hp_two]
    simp [hp_two]

/-- A prime avoids the displayed discriminant precisely when it avoids `2abc`. -/
theorem abcResidueDiscriminant_ne_zero_iff_prime {a b c p : ℕ} (hp : p.Prime) :
    abcResidueDiscriminant a b c p ≠ 0 ↔ p ≠ 2 ∧ ¬ p ∣ a * b * c := by
  simpa only [not_or] using not_congr (abcResidueDiscriminant_eq_zero_iff_prime hp)

/-- This integral-discriminant unit test covers every prime, including `2`. -/
theorem abcResidueDiscriminant_isUnit_iff_prime {a b c p : ℕ} (hp : p.Prime) :
    IsUnit (abcResidueDiscriminant a b c p) ↔ p ≠ 2 ∧ ¬ p ∣ a * b * c := by
  letI : Fact p.Prime := ⟨hp⟩
  rw [isUnit_iff_ne_zero, abcResidueDiscriminant_ne_zero_iff_prime hp]

/-- A proved integral discriminant formula maps to the displayed residue formula. -/
theorem abc_integralModel_map_discriminant {a b c p : ℕ}
    (W : WeierstrassCurve ℤ)
    (hdiscriminant : W.Δ = 16 * (a : ℤ) ^ 2 * (b : ℤ) ^ 2 * (c : ℤ) ^ 2) :
    (W.map (Int.castRingHom (ZMod p))).Δ = abcResidueDiscriminant a b c p := by
  rw [WeierstrassCurve.map_Δ, hdiscriminant]
  simp [abcResidueDiscriminant]

/-- Mathlib's ellipticity criterion for the residue of an integral model
with the indicated discriminant.  The discriminant equality is an explicit
hypothesis to be discharged by the concrete model's proved formula. -/
theorem abc_integralModel_map_isElliptic_iff {a b c p : ℕ}
    (W : WeierstrassCurve ℤ)
    (hdiscriminant : W.Δ = 16 * (a : ℤ) ^ 2 * (b : ℤ) ^ 2 * (c : ℤ) ^ 2)
    (hp : p.Prime) (hp_two : p ≠ 2) :
    (W.map (Int.castRingHom (ZMod p))).IsElliptic ↔ ¬ p ∣ a * b * c := by
  rw [WeierstrassCurve.isElliptic_iff,
    abc_integralModel_map_discriminant W hdiscriminant]
  exact abcResidueDiscriminant_isUnit_iff hp hp_two

/-- Exact all-prime criterion for the displayed integral model's nonsingular
residue equation.  It makes no minimal-model or conductor assertion. -/
theorem abc_integralModel_map_isElliptic_iff_prime {a b c p : ℕ}
    (W : WeierstrassCurve ℤ)
    (hdiscriminant : W.Δ = 16 * (a : ℤ) ^ 2 * (b : ℤ) ^ 2 * (c : ℤ) ^ 2)
    (hp : p.Prime) :
    (W.map (Int.castRingHom (ZMod p))).IsElliptic ↔ p ≠ 2 ∧ ¬ p ∣ a * b * c := by
  rw [WeierstrassCurve.isElliptic_iff,
    abc_integralModel_map_discriminant W hdiscriminant]
  exact abcResidueDiscriminant_isUnit_iff_prime hp

/-- The bad locus of this residue equation is precisely the discriminant
support; this does not identify the conductor of its generic fibre. -/
theorem abc_integralModel_map_not_isElliptic_iff {a b c p : ℕ}
    (W : WeierstrassCurve ℤ)
    (hdiscriminant : W.Δ = 16 * (a : ℤ) ^ 2 * (b : ℤ) ^ 2 * (c : ℤ) ^ 2)
    (hp : p.Prime) (hp_two : p ≠ 2) :
    ¬ (W.map (Int.castRingHom (ZMod p))).IsElliptic ↔ p ∣ a * b * c := by
  simpa only [not_not] using not_congr
    (abc_integralModel_map_isElliptic_iff W hdiscriminant hp hp_two)

/-- The prime `2` is exactly where the residue field kills the cubic's factor `2`. -/
theorem abc_two_natCast_ne_zero_iff {p : ℕ} (hp : p.Prime) :
    (2 : ZMod p) ≠ 0 ↔ p ≠ 2 := by
  constructor
  · intro htwo heq
    subst p
    exact htwo (by decide)
  · exact abc_two_natCast_ne_zero hp

/-- The actual Frey cubic over the residue field is elliptic at precisely the
odd primes outside the support of `abc`. -/
theorem freyWeierstrassCurve_zmod_isElliptic_iff {a b c p : ℕ}
    (hsum : a + b = c) (hp : p.Prime) (hp_two : p ≠ 2) :
    (freyWeierstrassCurve (a : ZMod p) (b : ZMod p)).IsElliptic ↔ ¬ p ∣ a * b * c := by
  letI : Fact p.Prime := ⟨hp⟩
  have hcast : (a : ZMod p) + (b : ZMod p) = (c : ZMod p) := by
    simpa only [Nat.cast_add] using congrArg (fun n : ℕ => (n : ZMod p)) hsum
  calc
    (freyWeierstrassCurve (a : ZMod p) (b : ZMod p)).IsElliptic ↔
        (a : ZMod p) ≠ 0 ∧ (b : ZMod p) ≠ 0 ∧ (c : ZMod p) ≠ 0 := by
      rw [freyWeierstrassCurve_isElliptic_iff, hcast]
      simp [abc_two_natCast_ne_zero hp hp_two, true_and]
    _ ↔ ¬ p ∣ a * b * c :=
      (abcResidueDiscriminant_ne_zero_iff_coordinates hp hp_two).symm.trans
        (abcResidueDiscriminant_ne_zero_iff hp hp_two)

/-- The same concrete criterion including the special prime `2`. -/
theorem freyWeierstrassCurve_zmod_isElliptic_iff_prime {a b c p : ℕ}
    (hsum : a + b = c) (hp : p.Prime) :
    (freyWeierstrassCurve (a : ZMod p) (b : ZMod p)).IsElliptic ↔
      p ≠ 2 ∧ ¬ p ∣ a * b * c := by
  letI : Fact p.Prime := ⟨hp⟩
  by_cases hp_two : p = 2
  · subst p
    rw [freyWeierstrassCurve_isElliptic_iff]
    have htwo : (2 : ZMod 2) = 0 := by decide +revert
    simp [htwo]
  · rw [freyWeierstrassCurve_zmod_isElliptic_iff hsum hp hp_two]
    simp [hp_two]

/-- Reduction of the actual integral equation agrees with the same equation
formed directly over the residue field. -/
theorem freyWeierstrassCurve_int_map_zmod (a b p : ℕ) :
    (freyWeierstrassCurve (a : ℤ) (b : ℤ)).map (Int.castRingHom (ZMod p)) =
      freyWeierstrassCurve (a : ZMod p) (b : ZMod p) := by
  rw [freyWeierstrassCurve_map]
  simp only [map_natCast]

/-- The integral ABC equation has nonsingular residue exactly away from its
odd discriminant support.  No minimality assumption is hidden in this statement. -/
theorem freyWeierstrassCurve_int_map_zmod_isElliptic_iff {a b c p : ℕ}
    (hsum : a + b = c) (hp : p.Prime) (hp_two : p ≠ 2) :
    ((freyWeierstrassCurve (a : ℤ) (b : ℤ)).map
      (Int.castRingHom (ZMod p))).IsElliptic ↔ ¬ p ∣ a * b * c := by
  rw [freyWeierstrassCurve_int_map_zmod]
  exact freyWeierstrassCurve_zmod_isElliptic_iff hsum hp hp_two

/-- The exact complement for the displayed integral equation at odd primes. -/
theorem freyWeierstrassCurve_int_map_zmod_not_isElliptic_iff {a b c p : ℕ}
    (hsum : a + b = c) (hp : p.Prime) (hp_two : p ≠ 2) :
    ¬ ((freyWeierstrassCurve (a : ℤ) (b : ℤ)).map
      (Int.castRingHom (ZMod p))).IsElliptic ↔ p ∣ a * b * c := by
  simpa only [not_not] using not_congr
    (freyWeierstrassCurve_int_map_zmod_isElliptic_iff hsum hp hp_two)

/-- The concrete residue equation, its discriminant, and the radical support
give equivalent tests without introducing an abstract elliptic-curve surrogate. -/
theorem freyWeierstrassCurve_zmod_isElliptic_iff_discriminant {a b c p : ℕ}
    (hsum : a + b = c) (hp : p.Prime) :
    (freyWeierstrassCurve (a : ZMod p) (b : ZMod p)).IsElliptic ↔
      IsUnit (abcResidueDiscriminant a b c p) := by
  exact (freyWeierstrassCurve_zmod_isElliptic_iff_prime hsum hp).trans
    (abcResidueDiscriminant_isUnit_iff_prime hp).symm

/-- In odd residue characteristic, the concrete equation is elliptic exactly
when its three displayed roots are pairwise distinct. -/
theorem freyWeierstrassCurve_zmod_isElliptic_iff_distinct_roots {a b c p : ℕ}
    (hsum : a + b = c) (hp : p.Prime) (hp_two : p ≠ 2) :
    (freyWeierstrassCurve (a : ZMod p) (b : ZMod p)).IsElliptic ↔
      (0 : ZMod p) ≠ (a : ZMod p) ∧
        (0 : ZMod p) ≠ -(b : ZMod p) ∧
        (a : ZMod p) ≠ -(b : ZMod p) := by
  exact (freyWeierstrassCurve_zmod_isElliptic_iff hsum hp hp_two).trans
    ((abcResidueDiscriminant_ne_zero_iff hp hp_two).symm.trans
      (abc_residue_roots_distinct_iff hsum hp hp_two))

/-- The concrete integral equation has the ABC discriminant after `a+b=c`. -/
theorem freyWeierstrassCurve_int_abc_discriminant {a b c : ℕ} (hsum : a + b = c) :
    (freyWeierstrassCurve (a : ℤ) (b : ℤ)).Δ =
      16 * (a : ℤ) ^ 2 * (b : ℤ) ^ 2 * (c : ℤ) ^ 2 := by
  have hcast : (a : ℤ) + (b : ℤ) = (c : ℤ) := by
    simpa only [Nat.cast_add] using congrArg (fun n : ℕ => (n : ℤ)) hsum
  rw [freyWeierstrassCurve_discriminant, hcast]

/-- The residue expression is the discriminant of the actual Frey equation. -/
theorem freyWeierstrassCurve_zmod_abc_discriminant {a b c p : ℕ}
    (hsum : a + b = c) :
    (freyWeierstrassCurve (a : ZMod p) (b : ZMod p)).Δ =
      abcResidueDiscriminant a b c p := by
  have hcast : (a : ZMod p) + (b : ZMod p) = (c : ZMod p) := by
    simpa only [Nat.cast_add] using congrArg (fun n : ℕ => (n : ZMod p)) hsum
  rw [freyWeierstrassCurve_discriminant, hcast]
  rfl

/-- Computing the discriminant commutes with reducing the integral equation. -/
theorem freyWeierstrassCurve_int_map_zmod_discriminant {a b c p : ℕ}
    (hsum : a + b = c) :
    ((freyWeierstrassCurve (a : ℤ) (b : ℤ)).map (Int.castRingHom (ZMod p))).Δ =
      abcResidueDiscriminant a b c p := by
  rw [freyWeierstrassCurve_int_map_zmod]
  exact freyWeierstrassCurve_zmod_abc_discriminant hsum

/-- The concrete residue curve's discriminant vanishes exactly on odd support. -/
theorem freyWeierstrassCurve_zmod_discriminant_eq_zero_iff {a b c p : ℕ}
    (hsum : a + b = c) (hp : p.Prime) (hp_two : p ≠ 2) :
    (freyWeierstrassCurve (a : ZMod p) (b : ZMod p)).Δ = 0 ↔ p ∣ a * b * c := by
  rw [freyWeierstrassCurve_zmod_abc_discriminant hsum]
  exact abcResidueDiscriminant_eq_zero_iff hp hp_two

/-- Exact nonvanishing of the concrete discriminant, ready for the residue
curve's standard Mathlib ellipticity class. -/
theorem freyWeierstrassCurve_zmod_discriminant_ne_zero_iff {a b c p : ℕ}
    (hsum : a + b = c) (hp : p.Prime) (hp_two : p ≠ 2) :
    (freyWeierstrassCurve (a : ZMod p) (b : ZMod p)).Δ ≠ 0 ↔ ¬ p ∣ a * b * c := by
  rw [freyWeierstrassCurve_zmod_abc_discriminant hsum]
  exact abcResidueDiscriminant_ne_zero_iff hp hp_two

/-- The concrete discriminant is a unit at exactly the primes outside odd support. -/
theorem freyWeierstrassCurve_zmod_discriminant_isUnit_iff {a b c p : ℕ}
    (hsum : a + b = c) (hp : p.Prime) (hp_two : p ≠ 2) :
    IsUnit (freyWeierstrassCurve (a : ZMod p) (b : ZMod p)).Δ ↔ ¬ p ∣ a * b * c := by
  rw [freyWeierstrassCurve_zmod_abc_discriminant hsum]
  exact abcResidueDiscriminant_isUnit_iff hp hp_two

/-- The integral model's residue equation has the exact all-prime criterion. -/
theorem freyWeierstrassCurve_int_map_zmod_isElliptic_iff_prime {a b c p : ℕ}
    (hsum : a + b = c) (hp : p.Prime) :
    ((freyWeierstrassCurve (a : ℤ) (b : ℤ)).map
      (Int.castRingHom (ZMod p))).IsElliptic ↔ p ≠ 2 ∧ ¬ p ∣ a * b * c := by
  rw [freyWeierstrassCurve_int_map_zmod]
  exact freyWeierstrassCurve_zmod_isElliptic_iff_prime hsum hp

end LeanFormal.IUT
