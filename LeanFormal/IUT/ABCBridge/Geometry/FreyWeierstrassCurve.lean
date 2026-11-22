import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Mathlib.Tactic
import LeanFormal.IUT.ABCBridge.Arithmetic.RationalPointDictionary

/-!
# The Frey Weierstrass curve attached to an additive pair

The model in this file is Mathlib's actual `WeierstrassCurve`, with equation
`y² = x * (x - a) * (x + b)`.  Its discriminant and j-invariant are the actual
Mathlib invariants.  These formulas provide the curve input for the ABC-to-IUT
arithmetic specialization; they do not establish minimality, semistability,
conductor formulas, or any comparison with an IUT theta construction.

Batch status: CANDIDATE pending the coordinated compilation and axiom audit.
-/

namespace LeanFormal.IUT

universe u v w

section RingModel

variable {R : Type u} [CommRing R]

/-- The integral-form Frey equation `y² = x * (x - a) * (x + b)`. -/
def freyWeierstrassCurve (a b : R) : WeierstrassCurve R where
  a₁ := 0
  a₂ := b - a
  a₃ := 0
  a₄ := -(a * b)
  a₆ := 0

@[simp] theorem freyWeierstrassCurve_a₁ (a b : R) :
    (freyWeierstrassCurve a b).a₁ = 0 := rfl

@[simp] theorem freyWeierstrassCurve_a₂ (a b : R) :
    (freyWeierstrassCurve a b).a₂ = b - a := rfl

@[simp] theorem freyWeierstrassCurve_a₃ (a b : R) :
    (freyWeierstrassCurve a b).a₃ = 0 := rfl

@[simp] theorem freyWeierstrassCurve_a₄ (a b : R) :
    (freyWeierstrassCurve a b).a₄ = -(a * b) := rfl

@[simp] theorem freyWeierstrassCurve_a₆ (a b : R) :
    (freyWeierstrassCurve a b).a₆ = 0 := rfl

/-- The displayed cubic is exactly the right side of the Weierstrass equation. -/
theorem freyWeierstrassCurve_equation (a b x y : R) :
    y ^ 2 + (freyWeierstrassCurve a b).a₁ * x * y +
        (freyWeierstrassCurve a b).a₃ * y =
      x ^ 3 + (freyWeierstrassCurve a b).a₂ * x ^ 2 +
        (freyWeierstrassCurve a b).a₄ * x + (freyWeierstrassCurve a b).a₆ ↔
      y ^ 2 = x * (x - a) * (x + b) := by
  simp only [freyWeierstrassCurve_a₁, freyWeierstrassCurve_a₂,
    freyWeierstrassCurve_a₃, freyWeierstrassCurve_a₄,
    freyWeierstrassCurve_a₆, zero_mul, add_zero]
  congr 1 <;> ring

@[simp] theorem freyWeierstrassCurve_b₂ (a b : R) :
    (freyWeierstrassCurve a b).b₂ = 4 * (b - a) := by
  simp [WeierstrassCurve.b₂, freyWeierstrassCurve]

@[simp] theorem freyWeierstrassCurve_b₄ (a b : R) :
    (freyWeierstrassCurve a b).b₄ = -2 * a * b := by
  simp only [WeierstrassCurve.b₄, freyWeierstrassCurve_a₁,
    freyWeierstrassCurve_a₃, freyWeierstrassCurve_a₄]
  ring

@[simp] theorem freyWeierstrassCurve_b₆ (a b : R) :
    (freyWeierstrassCurve a b).b₆ = 0 := by
  simp [WeierstrassCurve.b₆, freyWeierstrassCurve]

@[simp] theorem freyWeierstrassCurve_b₈ (a b : R) :
    (freyWeierstrassCurve a b).b₈ = -(a ^ 2 * b ^ 2) := by
  simp only [WeierstrassCurve.b₈, freyWeierstrassCurve_a₁,
    freyWeierstrassCurve_a₂, freyWeierstrassCurve_a₃,
    freyWeierstrassCurve_a₄, freyWeierstrassCurve_a₆]
  ring

@[simp] theorem freyWeierstrassCurve_c₄ (a b : R) :
    (freyWeierstrassCurve a b).c₄ = 16 * (a ^ 2 + a * b + b ^ 2) := by
  rw [WeierstrassCurve.c₄, freyWeierstrassCurve_b₂, freyWeierstrassCurve_b₄]
  ring

@[simp] theorem freyWeierstrassCurve_c₆ (a b : R) :
    (freyWeierstrassCurve a b).c₆ =
      32 * (a - b) * (2 * a + b) * (a + 2 * b) := by
  rw [WeierstrassCurve.c₆, freyWeierstrassCurve_b₂,
    freyWeierstrassCurve_b₄, freyWeierstrassCurve_b₆]
  ring

@[simp] theorem freyWeierstrassCurve_discriminant (a b : R) :
    (freyWeierstrassCurve a b).Δ = 16 * a ^ 2 * b ^ 2 * (a + b) ^ 2 := by
  rw [WeierstrassCurve.Δ, freyWeierstrassCurve_b₂,
    freyWeierstrassCurve_b₄, freyWeierstrassCurve_b₆,
    freyWeierstrassCurve_b₈]
  ring

/-- The discriminant square presentation is useful for integer valuations. -/
theorem freyWeierstrassCurve_discriminant_square (a b : R) :
    (freyWeierstrassCurve a b).Δ = (4 * a * b * (a + b)) ^ 2 := by
  rw [freyWeierstrassCurve_discriminant]
  ring

/-- Substitute the additive ABC relation without imposing a characteristic. -/
theorem freyWeierstrassCurve_discriminant_of_add_eq
    (a b c : R) (hadd : a + b = c) :
    (freyWeierstrassCurve a b).Δ = 16 * a ^ 2 * b ^ 2 * c ^ 2 := by
  rw [freyWeierstrassCurve_discriminant, hadd]

theorem freyWeierstrassCurve_discriminant_of_left_eq_zero (b : R) :
    (freyWeierstrassCurve 0 b).Δ = 0 := by simp

theorem freyWeierstrassCurve_discriminant_of_right_eq_zero (a : R) :
    (freyWeierstrassCurve a 0).Δ = 0 := by simp

theorem freyWeierstrassCurve_discriminant_of_add_eq_zero
    (a b : R) (hadd : a + b = 0) :
    (freyWeierstrassCurve a b).Δ = 0 := by
  simp [hadd]

theorem freyWeierstrassCurve_c₄_swap (a b : R) :
    (freyWeierstrassCurve b a).c₄ = (freyWeierstrassCurve a b).c₄ := by
  simp only [freyWeierstrassCurve_c₄]
  ring

theorem freyWeierstrassCurve_c₆_swap (a b : R) :
    (freyWeierstrassCurve b a).c₆ = -(freyWeierstrassCurve a b).c₆ := by
  simp only [freyWeierstrassCurve_c₆]
  ring

theorem freyWeierstrassCurve_discriminant_swap (a b : R) :
    (freyWeierstrassCurve b a).Δ = (freyWeierstrassCurve a b).Δ := by
  simp only [freyWeierstrassCurve_discriminant]
  ring

/-- Scaling both additive parameters has weight two on `c₄`. -/
theorem freyWeierstrassCurve_c₄_scale (a b scale : R) :
    (freyWeierstrassCurve (scale * a) (scale * b)).c₄ =
      scale ^ 2 * (freyWeierstrassCurve a b).c₄ := by
  simp only [freyWeierstrassCurve_c₄]
  ring

theorem freyWeierstrassCurve_c₆_scale (a b scale : R) :
    (freyWeierstrassCurve (scale * a) (scale * b)).c₆ =
      scale ^ 3 * (freyWeierstrassCurve a b).c₆ := by
  simp only [freyWeierstrassCurve_c₆]
  ring

theorem freyWeierstrassCurve_discriminant_scale (a b scale : R) :
    (freyWeierstrassCurve (scale * a) (scale * b)).Δ =
      scale ^ 6 * (freyWeierstrassCurve a b).Δ := by
  simp only [freyWeierstrassCurve_discriminant]
  ring

/-- A genuine ellipticity criterion over a ring, using units rather than nonzero elements. -/
theorem freyWeierstrassCurve_isElliptic_of_isUnit
    (a b : R) (htwo : IsUnit (2 : R)) (ha : IsUnit a) (hb : IsUnit b)
    (hab : IsUnit (a + b)) : (freyWeierstrassCurve a b).IsElliptic := by
  refine ⟨?_⟩
  rw [freyWeierstrassCurve_discriminant]
  have hsixteen : IsUnit (16 : R) := by
    convert htwo.pow 4 using 1 <;> norm_num
  exact ((hsixteen.mul (ha.pow 2)).mul (hb.pow 2)).mul (hab.pow 2)

end RingModel

section BaseChange

variable {R : Type u} {S : Type v} {T : Type w}
variable [CommRing R] [CommRing S] [CommRing T]

/-- Base change preserves this exact chosen model, not just its invariant values. -/
@[simp] theorem freyWeierstrassCurve_map (a b : R) (f : R →+* S) :
    (freyWeierstrassCurve a b).map f = freyWeierstrassCurve (f a) (f b) := by
  ext <;> simp [freyWeierstrassCurve, WeierstrassCurve.map]

@[simp] theorem freyWeierstrassCurve_baseChange
    [Algebra R S] (a b : R) :
    (freyWeierstrassCurve a b).baseChange S =
      freyWeierstrassCurve (algebraMap R S a) (algebraMap R S b) := by
  exact freyWeierstrassCurve_map a b (algebraMap R S)

theorem freyWeierstrassCurve_map_comp
    (a b : R) (f : R →+* S) (g : S →+* T) :
    ((freyWeierstrassCurve a b).map f).map g =
      freyWeierstrassCurve (g (f a)) (g (f b)) := by
  simp only [freyWeierstrassCurve_map]

theorem freyWeierstrassCurve_map_discriminant (a b : R) (f : R →+* S) :
    (freyWeierstrassCurve (f a) (f b)).Δ =
      f (16 * a ^ 2 * b ^ 2 * (a + b) ^ 2) := by
  rw [← freyWeierstrassCurve_map, WeierstrassCurve.map_Δ,
    freyWeierstrassCurve_discriminant]

theorem freyWeierstrassCurve_map_c₄ (a b : R) (f : R →+* S) :
    (freyWeierstrassCurve (f a) (f b)).c₄ =
      f (16 * (a ^ 2 + a * b + b ^ 2)) := by
  rw [← freyWeierstrassCurve_map, WeierstrassCurve.map_c₄,
    freyWeierstrassCurve_c₄]

theorem freyWeierstrassCurve_map_c₆ (a b : R) (f : R →+* S) :
    (freyWeierstrassCurve (f a) (f b)).c₆ =
      f (32 * (a - b) * (2 * a + b) * (a + 2 * b)) := by
  rw [← freyWeierstrassCurve_map, WeierstrassCurve.map_c₆,
    freyWeierstrassCurve_c₆]

end BaseChange

section FieldModel

variable {K : Type u} [Field K]

/-- In characteristic different from two the three distinct cubic roots ensure ellipticity. -/
theorem freyWeierstrassCurve_discriminant_ne_zero
    (a b : K) (htwo : (2 : K) ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : a + b ≠ 0) : (freyWeierstrassCurve a b).Δ ≠ 0 := by
  rw [freyWeierstrassCurve_discriminant]
  have hsixteen : (16 : K) ≠ 0 := by
    convert pow_ne_zero 4 htwo using 1 <;> norm_num
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero hsixteen (pow_ne_zero 2 ha))
    (pow_ne_zero 2 hb)) (pow_ne_zero 2 hab)

theorem freyWeierstrassCurve_isElliptic
    (a b : K) (htwo : (2 : K) ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : a + b ≠ 0) : (freyWeierstrassCurve a b).IsElliptic := by
  exact ⟨isUnit_iff_ne_zero.mpr
    (freyWeierstrassCurve_discriminant_ne_zero a b htwo ha hb hab)⟩

/-- No characteristic-two case is silently included in the ellipticity criterion. -/
theorem freyWeierstrassCurve_isElliptic_iff (a b : K) :
    (freyWeierstrassCurve a b).IsElliptic ↔
      (2 : K) ≠ 0 ∧ a ≠ 0 ∧ b ≠ 0 ∧ a + b ≠ 0 := by
  constructor
  · intro helliptic
    have hdiscriminant := helliptic.isUnit.ne_zero
    have htwo : (2 : K) ≠ 0 := by
      intro hzero
      have hsixteen : (16 : K) = 0 := by
        calc
          (16 : K) = 2 ^ 4 := by norm_num
          _ = 0 := by rw [hzero]; norm_num
      apply hdiscriminant
      simp [hsixteen]
    have ha : a ≠ 0 := by
      intro hzero
      apply hdiscriminant
      simp [hzero]
    have hb : b ≠ 0 := by
      intro hzero
      apply hdiscriminant
      simp [hzero]
    have hab : a + b ≠ 0 := by
      intro hzero
      apply hdiscriminant
      simp [hzero]
    exact ⟨htwo, ha, hb, hab⟩
  · rintro ⟨htwo, ha, hb, hab⟩
    exact freyWeierstrassCurve_isElliptic a b htwo ha hb hab

theorem freyWeierstrassCurve_not_isElliptic_of_two_eq_zero
    (a b : K) (htwo : (2 : K) = 0) :
    ¬ (freyWeierstrassCurve a b).IsElliptic := by
  intro helliptic
  exact ((freyWeierstrassCurve_isElliptic_iff a b).mp helliptic).1 htwo

/-- Formula for Mathlib's j-invariant, with its actual ellipticity instance. -/
theorem freyWeierstrassCurve_j (a b : K)
    [(freyWeierstrassCurve a b).IsElliptic] :
    (freyWeierstrassCurve a b).j =
      256 * (a ^ 2 + a * b + b ^ 2) ^ 3 /
        (a ^ 2 * b ^ 2 * (a + b) ^ 2) := by
  have hparameters := (freyWeierstrassCurve_isElliptic_iff a b).mp
    (inferInstance : (freyWeierstrassCurve a b).IsElliptic)
  rcases hparameters with ⟨htwo, ha, hb, hab⟩
  have hsixteen : (16 : K) ≠ 0 := by
    convert pow_ne_zero 4 htwo using 1 <;> norm_num
  simp only [WeierstrassCurve.j, Units.val_inv_eq_inv_val,
    WeierstrassCurve.coe_Δ', freyWeierstrassCurve_c₄,
    freyWeierstrassCurve_discriminant]
  field_simp [hsixteen, ha, hb, hab]
  <;> ring

theorem freyWeierstrassCurve_j_of_add_eq (a b c : K)
    [(freyWeierstrassCurve a b).IsElliptic] (hadd : a + b = c) :
    (freyWeierstrassCurve a b).j =
      256 * (a ^ 2 + a * b + b ^ 2) ^ 3 / (a ^ 2 * b ^ 2 * c ^ 2) := by
  rw [freyWeierstrassCurve_j, hadd]

/-- Swapping the additive parameters preserves the actual j-invariant. -/
theorem freyWeierstrassCurve_j_swap (a b : K)
    [(freyWeierstrassCurve a b).IsElliptic]
    [(freyWeierstrassCurve b a).IsElliptic] :
    (freyWeierstrassCurve b a).j = (freyWeierstrassCurve a b).j := by
  rw [freyWeierstrassCurve_j, freyWeierstrassCurve_j]
  congr 1 <;> ring

end FieldModel

section IntegralAndRationalModels

/-- The chosen integral Frey model for natural additive parameters. -/
def integralFreyWeierstrassCurve (a b : ℕ) : WeierstrassCurve ℤ :=
  freyWeierstrassCurve (a : ℤ) (b : ℤ)

/-- The generic fiber over `ℚ` of the chosen integral model. -/
def rationalFreyWeierstrassCurve (a b : ℕ) : WeierstrassCurve ℚ :=
  freyWeierstrassCurve (a : ℚ) (b : ℚ)

/-- All reductions of the integral model have the same coefficient formula. -/
@[simp] theorem integralFreyWeierstrassCurve_map
    {R : Type u} [CommRing R] (a b : ℕ) (f : ℤ →+* R) :
    (integralFreyWeierstrassCurve a b).map f =
      freyWeierstrassCurve (a : R) (b : R) := by
  simp [integralFreyWeierstrassCurve, freyWeierstrassCurve_map]

@[simp] theorem integralFreyWeierstrassCurve_baseChange
    {R : Type u} [CommRing R] [Algebra ℤ R] (a b : ℕ) :
    (integralFreyWeierstrassCurve a b).baseChange R =
      freyWeierstrassCurve (a : R) (b : R) := by
  exact integralFreyWeierstrassCurve_map a b (algebraMap ℤ R)

/-- The rational curve is exactly a base change of the integral curve. -/
theorem integralFreyWeierstrassCurve_baseChange_rat (a b : ℕ) :
    (integralFreyWeierstrassCurve a b).baseChange ℚ =
      rationalFreyWeierstrassCurve a b := by
  exact integralFreyWeierstrassCurve_baseChange a b

@[simp] theorem rationalFreyWeierstrassCurve_map
    {R : Type u} [CommRing R] (a b : ℕ) (f : ℚ →+* R) :
    (rationalFreyWeierstrassCurve a b).map f =
      freyWeierstrassCurve (a : R) (b : R) := by
  simp [rationalFreyWeierstrassCurve, freyWeierstrassCurve_map]

@[simp] theorem integralFreyWeierstrassCurve_c₄ (a b : ℕ) :
    (integralFreyWeierstrassCurve a b).c₄ =
      16 * ((a : ℤ) ^ 2 + (a : ℤ) * (b : ℤ) + (b : ℤ) ^ 2) :=
  freyWeierstrassCurve_c₄ (a : ℤ) (b : ℤ)

@[simp] theorem rationalFreyWeierstrassCurve_c₄ (a b : ℕ) :
    (rationalFreyWeierstrassCurve a b).c₄ =
      16 * ((a : ℚ) ^ 2 + (a : ℚ) * (b : ℚ) + (b : ℚ) ^ 2) :=
  freyWeierstrassCurve_c₄ (a : ℚ) (b : ℚ)

/-- The positivity and additive equation used here come from the actual ABC predicate. -/
theorem freyWeierstrassCurve_isElliptic_of_isABCTriple
    {K : Type u} [Field K] [CharZero K] {a b c : ℕ} (h : IsABCTriple a b c) :
    (freyWeierstrassCurve (a : K) (b : K)).IsElliptic := by
  have hpositive : 0 < a ∧ 0 < b ∧ a + b = c ∧ Nat.Coprime a b :=
    (isABCTriple_iff_positivePrimitiveAdditiveTriple a b c).mp h
  rcases hpositive with ⟨ha, hb, _, _⟩
  apply freyWeierstrassCurve_isElliptic
  · norm_num
  · exact_mod_cast Nat.ne_of_gt ha
  · exact_mod_cast Nat.ne_of_gt hb
  · rw [← Nat.cast_add]
    exact_mod_cast Nat.ne_of_gt (Nat.add_pos_left ha b)

theorem rationalFreyWeierstrassCurve_isElliptic_of_isABCTriple
    {a b c : ℕ} (h : IsABCTriple a b c) :
    (rationalFreyWeierstrassCurve a b).IsElliptic :=
  freyWeierstrassCurve_isElliptic_of_isABCTriple h

/-- The actual invariant of the integral model, with the third ABC coordinate. -/
theorem integralFreyWeierstrassCurve_discriminant_of_isABCTriple
    {a b c : ℕ} (h : IsABCTriple a b c) :
    (integralFreyWeierstrassCurve a b).Δ =
      16 * (a : ℤ) ^ 2 * (b : ℤ) ^ 2 * (c : ℤ) ^ 2 := by
  have hpositive := (isABCTriple_iff_positivePrimitiveAdditiveTriple a b c).mp h
  apply freyWeierstrassCurve_discriminant_of_add_eq
  exact_mod_cast hpositive.2.2.1

theorem rationalFreyWeierstrassCurve_discriminant_of_isABCTriple
    {a b c : ℕ} (h : IsABCTriple a b c) :
    (rationalFreyWeierstrassCurve a b).Δ =
      16 * (a : ℚ) ^ 2 * (b : ℚ) ^ 2 * (c : ℚ) ^ 2 := by
  have hpositive := (isABCTriple_iff_positivePrimitiveAdditiveTriple a b c).mp h
  apply freyWeierstrassCurve_discriminant_of_add_eq
  exact_mod_cast hpositive.2.2.1

theorem integralFreyWeierstrassCurve_discriminant_square_of_isABCTriple
    {a b c : ℕ} (h : IsABCTriple a b c) :
    (integralFreyWeierstrassCurve a b).Δ =
      (4 * (a : ℤ) * (b : ℤ) * (c : ℤ)) ^ 2 := by
  rw [integralFreyWeierstrassCurve_discriminant_of_isABCTriple h]
  ring

/-- Casting the natural discriminant formula gives precisely the integral discriminant. -/
theorem integralFreyWeierstrassCurve_discriminant_natCast_of_isABCTriple
    {a b c : ℕ} (h : IsABCTriple a b c) :
    (integralFreyWeierstrassCurve a b).Δ = ((16 * a ^ 2 * b ^ 2 * c ^ 2 : ℕ) : ℤ) := by
  rw [integralFreyWeierstrassCurve_discriminant_of_isABCTriple h]
  push_cast <;> rfl

theorem integralFreyWeierstrassCurve_c₄_of_isABCTriple
    {a b c : ℕ} (h : IsABCTriple a b c) :
    (integralFreyWeierstrassCurve a b).c₄ =
      16 * ((c : ℤ) ^ 2 - (a : ℤ) * (b : ℤ)) := by
  have hpositive := (isABCTriple_iff_positivePrimitiveAdditiveTriple a b c).mp h
  have hadd : (a : ℤ) + (b : ℤ) = (c : ℤ) := by
    exact_mod_cast hpositive.2.2.1
  rw [integralFreyWeierstrassCurve_c₄, ← hadd]
  ring

theorem rationalFreyWeierstrassCurve_c₄_of_isABCTriple
    {a b c : ℕ} (h : IsABCTriple a b c) :
    (rationalFreyWeierstrassCurve a b).c₄ =
      16 * ((c : ℚ) ^ 2 - (a : ℚ) * (b : ℚ)) := by
  have hpositive := (isABCTriple_iff_positivePrimitiveAdditiveTriple a b c).mp h
  have hadd : (a : ℚ) + (b : ℚ) = (c : ℚ) := by
    exact_mod_cast hpositive.2.2.1
  rw [rationalFreyWeierstrassCurve_c₄, ← hadd]
  ring

theorem integralFreyWeierstrassCurve_c₆_of_isABCTriple
    {a b c : ℕ} (h : IsABCTriple a b c) :
    (integralFreyWeierstrassCurve a b).c₆ =
      32 * ((a : ℤ) - (b : ℤ)) * ((a : ℤ) + (c : ℤ)) * ((b : ℤ) + (c : ℤ)) := by
  have hpositive := (isABCTriple_iff_positivePrimitiveAdditiveTriple a b c).mp h
  have hadd : (a : ℤ) + (b : ℤ) = (c : ℤ) := by
    exact_mod_cast hpositive.2.2.1
  change (freyWeierstrassCurve (a : ℤ) (b : ℤ)).c₆ = _
  rw [freyWeierstrassCurve_c₆, ← hadd]
  ring

theorem integralFreyWeierstrassCurve_discriminant_pos_of_isABCTriple
    {a b c : ℕ} (h : IsABCTriple a b c) :
    0 < (integralFreyWeierstrassCurve a b).Δ := by
  have hpositive := (isABCTriple_iff_positivePrimitiveAdditiveTriple a b c).mp h
  have ha : (0 : ℤ) < (a : ℤ) := by exact_mod_cast hpositive.1
  have hb : (0 : ℤ) < (b : ℤ) := by exact_mod_cast hpositive.2.1
  have hc : (0 : ℤ) < (c : ℤ) := by
    exact_mod_cast (hpositive.2.2.1 ▸ Nat.add_pos_left hpositive.1 b)
  rw [integralFreyWeierstrassCurve_discriminant_of_isABCTriple h]
  positivity

theorem integralFreyWeierstrassCurve_discriminant_ne_zero_of_isABCTriple
    {a b c : ℕ} (h : IsABCTriple a b c) :
    (integralFreyWeierstrassCurve a b).Δ ≠ 0 :=
  ne_of_gt (integralFreyWeierstrassCurve_discriminant_pos_of_isABCTriple h)

theorem rationalFreyWeierstrassCurve_discriminant_ne_zero_of_isABCTriple
    {a b c : ℕ} (h : IsABCTriple a b c) :
    (rationalFreyWeierstrassCurve a b).Δ ≠ 0 := by
  letI := rationalFreyWeierstrassCurve_isElliptic_of_isABCTriple h
  exact (rationalFreyWeierstrassCurve a b).isUnit_Δ.ne_zero

theorem integralFreyWeierstrassCurve_c₄_pos_of_isABCTriple
    {a b c : ℕ} (h : IsABCTriple a b c) :
    0 < (integralFreyWeierstrassCurve a b).c₄ := by
  have hpositive := (isABCTriple_iff_positivePrimitiveAdditiveTriple a b c).mp h
  have ha : (0 : ℤ) < (a : ℤ) := by exact_mod_cast hpositive.1
  have hb : (0 : ℤ) < (b : ℤ) := by exact_mod_cast hpositive.2.1
  rw [integralFreyWeierstrassCurve_c₄]
  positivity

theorem rationalFreyWeierstrassCurve_c₄_pos_of_isABCTriple
    {a b c : ℕ} (h : IsABCTriple a b c) :
    0 < (rationalFreyWeierstrassCurve a b).c₄ := by
  have hpositive := (isABCTriple_iff_positivePrimitiveAdditiveTriple a b c).mp h
  have ha : (0 : ℚ) < (a : ℚ) := by exact_mod_cast hpositive.1
  have hb : (0 : ℚ) < (b : ℚ) := by exact_mod_cast hpositive.2.1
  rw [rationalFreyWeierstrassCurve_c₄]
  positivity

/-- The local instance is a proved consequence of the ABC triple, not an extra hypothesis. -/
theorem rationalFreyWeierstrassCurve_j_of_isABCTriple
    {a b c : ℕ} (h : IsABCTriple a b c) :
    letI := rationalFreyWeierstrassCurve_isElliptic_of_isABCTriple h
    (rationalFreyWeierstrassCurve a b).j =
      256 * ((a : ℚ) ^ 2 + (a : ℚ) * (b : ℚ) + (b : ℚ) ^ 2) ^ 3 /
        ((a : ℚ) ^ 2 * (b : ℚ) ^ 2 * (c : ℚ) ^ 2) := by
  letI := rationalFreyWeierstrassCurve_isElliptic_of_isABCTriple h
  have hpositive := (isABCTriple_iff_positivePrimitiveAdditiveTriple a b c).mp h
  haveI : (freyWeierstrassCurve (a : ℚ) (b : ℚ)).IsElliptic :=
    rationalFreyWeierstrassCurve_isElliptic_of_isABCTriple h
  apply freyWeierstrassCurve_j_of_add_eq
  exact_mod_cast hpositive.2.2.1

theorem rationalFreyWeierstrassCurve_j_ne_zero_of_isABCTriple
    {a b c : ℕ} (h : IsABCTriple a b c) :
    letI := rationalFreyWeierstrassCurve_isElliptic_of_isABCTriple h
    (rationalFreyWeierstrassCurve a b).j ≠ 0 := by
  letI := rationalFreyWeierstrassCurve_isElliptic_of_isABCTriple h
  intro hzero
  exact ne_of_gt (rationalFreyWeierstrassCurve_c₄_pos_of_isABCTriple h)
    ((rationalFreyWeierstrassCurve a b).j_eq_zero_iff.mp hzero)

/-- Mathlib's actual j-invariant commutes with a field extension of the ABC curve. -/
theorem rationalFreyWeierstrassCurve_map_j_of_isABCTriple
    {R : Type u} [CommRing R] {a b c : ℕ} (h : IsABCTriple a b c)
    (f : ℚ →+* R) :
    letI := rationalFreyWeierstrassCurve_isElliptic_of_isABCTriple h
    ((rationalFreyWeierstrassCurve a b).map f).j =
      f ((rationalFreyWeierstrassCurve a b).j) := by
  letI := rationalFreyWeierstrassCurve_isElliptic_of_isABCTriple h
  exact WeierstrassCurve.map_j (rationalFreyWeierstrassCurve a b) f

/-- The same discriminant formula survives every reduction of the integral model. -/
theorem integralFreyWeierstrassCurve_map_discriminant_of_isABCTriple
    {R : Type u} [CommRing R] {a b c : ℕ} (h : IsABCTriple a b c)
    (f : ℤ →+* R) :
    ((integralFreyWeierstrassCurve a b).map f).Δ =
      16 * (a : R) ^ 2 * (b : R) ^ 2 * (c : R) ^ 2 := by
  rw [WeierstrassCurve.map_Δ,
    integralFreyWeierstrassCurve_discriminant_of_isABCTriple h]
  simp

end IntegralAndRationalModels

end LeanFormal.IUT
