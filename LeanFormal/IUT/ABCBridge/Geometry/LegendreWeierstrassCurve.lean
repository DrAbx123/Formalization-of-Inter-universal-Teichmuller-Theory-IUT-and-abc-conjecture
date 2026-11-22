import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
import Mathlib.Tactic
import LeanFormal.IUT.ABCBridge.Arithmetic.RationalPointDictionary

/-!
# The actual Legendre Weierstrass family

This file realizes the parameter `parameter` of the Legendre family as Mathlib's
`WeierstrassCurve`, with equation `y² = x(x - 1)(x - parameter)`. Its invariant
identities hold over arbitrary commutative rings. Over fields the exact
smooth parameter domain is characteristic different from two and `parameter ≠ 0, 1`.

The rational specialization uses the existing ABC dictionary. These results
supply an elliptic family and its actual j invariant for the arithmetic
parameterization; they make no assertion about IUT admissibility or conductors.
-/

noncomputable section

namespace LeanFormal.IUT

section CommutativeRing

variable {R : Type*} [CommRing R]

/-- The Weierstrass equation `y² = x(x - 1)(x - parameter)`. -/
def legendreWeierstrassCurve (parameter : R) : WeierstrassCurve R where
  a₁ := 0
  a₂ := -(1 + parameter)
  a₃ := 0
  a₄ := parameter
  a₆ := 0

@[simp] theorem legendreWeierstrassCurve_a₁ (parameter : R) :
    (legendreWeierstrassCurve parameter).a₁ = 0 := rfl

@[simp] theorem legendreWeierstrassCurve_a₂ (parameter : R) :
    (legendreWeierstrassCurve parameter).a₂ = -(1 + parameter) := rfl

@[simp] theorem legendreWeierstrassCurve_a₃ (parameter : R) :
    (legendreWeierstrassCurve parameter).a₃ = 0 := rfl

@[simp] theorem legendreWeierstrassCurve_a₄ (parameter : R) :
    (legendreWeierstrassCurve parameter).a₄ = parameter := rfl

@[simp] theorem legendreWeierstrassCurve_a₆ (parameter : R) :
    (legendreWeierstrassCurve parameter).a₆ = 0 := rfl

/-- The family uses the actual Mathlib affine equation predicate. -/
theorem legendreWeierstrassCurve_equation_iff (parameter x y : R) :
    (legendreWeierstrassCurve parameter).toAffine.Equation x y ↔
      y ^ 2 = x * (x - 1) * (x - parameter) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  change (y ^ 2 + 0 * x * y + 0 * y =
    x ^ 3 + -(1 + parameter) * x ^ 2 + parameter * x + 0) ↔ _
  constructor <;> intro hequation <;> linear_combination hequation

@[simp] theorem legendreWeierstrassCurve_b₂ (parameter : R) :
    (legendreWeierstrassCurve parameter).b₂ = -4 * (1 + parameter) := by
  simp only [WeierstrassCurve.b₂, legendreWeierstrassCurve_a₁,
    legendreWeierstrassCurve_a₂]
  ring

@[simp] theorem legendreWeierstrassCurve_b₄ (parameter : R) :
    (legendreWeierstrassCurve parameter).b₄ = 2 * parameter := by
  simp [WeierstrassCurve.b₄]

@[simp] theorem legendreWeierstrassCurve_b₆ (parameter : R) :
    (legendreWeierstrassCurve parameter).b₆ = 0 := by
  simp [WeierstrassCurve.b₆]

@[simp] theorem legendreWeierstrassCurve_b₈ (parameter : R) :
    (legendreWeierstrassCurve parameter).b₈ = -parameter ^ 2 := by
  simp [WeierstrassCurve.b₈]

@[simp] theorem legendreWeierstrassCurve_c₄ (parameter : R) :
    (legendreWeierstrassCurve parameter).c₄ = 16 * (parameter ^ 2 - parameter + 1) := by
  simp only [WeierstrassCurve.c₄, legendreWeierstrassCurve_b₂,
    legendreWeierstrassCurve_b₄]
  ring

@[simp] theorem legendreWeierstrassCurve_c₆ (parameter : R) :
    (legendreWeierstrassCurve parameter).c₆ = 32 * (parameter + 1) * (parameter - 2) * (2 * parameter - 1) := by
  simp only [WeierstrassCurve.c₆, legendreWeierstrassCurve_b₂,
    legendreWeierstrassCurve_b₄, legendreWeierstrassCurve_b₆]
  ring

@[simp] theorem legendreWeierstrassCurve_discriminant (parameter : R) :
    (legendreWeierstrassCurve parameter).Δ = 16 * parameter ^ 2 * (1 - parameter) ^ 2 := by
  simp only [WeierstrassCurve.Δ, legendreWeierstrassCurve_b₂,
    legendreWeierstrassCurve_b₄, legendreWeierstrassCurve_b₆,
    legendreWeierstrassCurve_b₈]
  ring

/-- Unit hypotheses provide an elliptic family over a ring, before passing to fields. -/
theorem legendreWeierstrassCurve_isElliptic_of_isUnit (parameter : R)
    (htwo : IsUnit (2 : R)) (hparameter : IsUnit parameter)
    (hcomplement : IsUnit (1 - parameter)) : (legendreWeierstrassCurve parameter).IsElliptic := by
  constructor
  rw [legendreWeierstrassCurve_discriminant]
  have hsixteen : IsUnit (16 : R) := by
    convert htwo.pow 4 using 1
    norm_num
  exact (hsixteen.mul (hparameter.pow 2)).mul (hcomplement.pow 2)

/-- The three distinguished finite branch points lie on the actual affine equation. -/
theorem legendreWeierstrassCurve_equation_zero (parameter : R) :
    (legendreWeierstrassCurve parameter).toAffine.Equation 0 0 := by
  rw [legendreWeierstrassCurve_equation_iff]
  ring

theorem legendreWeierstrassCurve_equation_one (parameter : R) :
    (legendreWeierstrassCurve parameter).toAffine.Equation 1 0 := by
  rw [legendreWeierstrassCurve_equation_iff]
  ring

theorem legendreWeierstrassCurve_equation_parameter (parameter : R) :
    (legendreWeierstrassCurve parameter).toAffine.Equation parameter 0 := by
  rw [legendreWeierstrassCurve_equation_iff]
  ring

variable {S : Type*} [CommRing S]

/-- Formation of the curve commutes with arbitrary ring homomorphisms. -/
@[simp] theorem legendreWeierstrassCurve_map (parameter : R) (f : R →+* S) :
    (legendreWeierstrassCurve parameter).map f = legendreWeierstrassCurve (f parameter) := by
  ext <;> simp [WeierstrassCurve.map, legendreWeierstrassCurve]

@[simp] theorem legendreWeierstrassCurve_baseChange (parameter : R) [Algebra R S] :
    (legendreWeierstrassCurve parameter).baseChange S =
      legendreWeierstrassCurve (algebraMap R S parameter) := by
  exact legendreWeierstrassCurve_map parameter (algebraMap R S)

theorem legendreWeierstrassCurve_discriminant_map (parameter : R) (f : R →+* S) :
    (legendreWeierstrassCurve (f parameter)).Δ = f (legendreWeierstrassCurve parameter).Δ := by
  rw [← legendreWeierstrassCurve_map parameter f]
  exact (legendreWeierstrassCurve parameter).map_Δ f

theorem legendreWeierstrassCurve_c₄_map (parameter : R) (f : R →+* S) :
    (legendreWeierstrassCurve (f parameter)).c₄ = f (legendreWeierstrassCurve parameter).c₄ := by
  rw [← legendreWeierstrassCurve_map parameter f]
  exact (legendreWeierstrassCurve parameter).map_c₄ f

/-- This applies in particular when reducing an integral parameter into a residue field. -/
theorem legendreWeierstrassCurve_equation_map (parameter x y : R) (f : R →+* S)
    (hequation : (legendreWeierstrassCurve parameter).toAffine.Equation x y) :
    (legendreWeierstrassCurve (f parameter)).toAffine.Equation (f x) (f y) := by
  rw [legendreWeierstrassCurve_equation_iff] at hequation ⊢
  simpa only [map_pow, map_mul, map_sub, map_one] using congrArg f hequation

theorem legendreWeierstrassCurve_equation_map_iff (parameter x y : R) (f : R →+* S)
    (hinjective : Function.Injective f) :
    (legendreWeierstrassCurve (f parameter)).toAffine.Equation (f x) (f y) ↔
      (legendreWeierstrassCurve parameter).toAffine.Equation x y := by
  rw [legendreWeierstrassCurve_equation_iff, legendreWeierstrassCurve_equation_iff]
  constructor
  · intro hequation
    apply hinjective
    simpa only [map_pow, map_mul, map_sub, map_one] using hequation
  · intro hequation
    simpa only [map_pow, map_mul, map_sub, map_one] using congrArg f hequation

end CommutativeRing

section IntegralDomain

variable {R : Type*} [CommRing R] [IsDomain R]

/-- The only affine points with zero y-coordinate have the three branch coordinates. -/
theorem legendreWeierstrassCurve_equation_y_zero_iff (parameter x : R) :
    (legendreWeierstrassCurve parameter).toAffine.Equation x 0 ↔
      x = 0 ∨ x = 1 ∨ x = parameter := by
  rw [legendreWeierstrassCurve_equation_iff]
  simp only [zero_pow (by decide : 2 ≠ 0)]
  rw [eq_comm]
  simp only [mul_eq_zero, sub_eq_zero]
  exact or_assoc

end IntegralDomain

section Field

variable {F : Type*} [Field F]

theorem legendreWeierstrassCurve_discriminant_ne_zero (parameter : F)
    (htwo : (2 : F) ≠ 0) (hzero : parameter ≠ 0) (hone : parameter ≠ 1) :
    (legendreWeierstrassCurve parameter).Δ ≠ 0 := by
  rw [legendreWeierstrassCurve_discriminant]
  have hsixteen : (16 : F) ≠ 0 := by
    convert pow_ne_zero 4 htwo using 1
    norm_num
  exact mul_ne_zero (mul_ne_zero hsixteen (pow_ne_zero 2 hzero))
    (pow_ne_zero 2 (sub_ne_zero.mpr hone.symm))

theorem legendreWeierstrassCurve_isElliptic (parameter : F)
    (htwo : (2 : F) ≠ 0) (hzero : parameter ≠ 0) (hone : parameter ≠ 1) :
    (legendreWeierstrassCurve parameter).IsElliptic := by
  exact ⟨isUnit_iff_ne_zero.mpr
    (legendreWeierstrassCurve_discriminant_ne_zero parameter htwo hzero hone)⟩

theorem legendreWeierstrassCurve_discriminant_eq_zero_iff (parameter : F)
    (htwo : (2 : F) ≠ 0) :
    (legendreWeierstrassCurve parameter).Δ = 0 ↔ parameter = 0 ∨ parameter = 1 := by
  have hsixteen : (16 : F) ≠ 0 := by
    convert pow_ne_zero 4 htwo using 1
    norm_num
  rw [legendreWeierstrassCurve_discriminant]
  simp only [mul_eq_zero, pow_eq_zero_iff (by decide : 2 ≠ 0),
    hsixteen, false_or, sub_eq_zero]
  exact or_congr Iff.rfl eq_comm

/-- Over a field of characteristic different from two, the excluded parameters are exact. -/
theorem legendreWeierstrassCurve_isElliptic_iff (parameter : F) (htwo : (2 : F) ≠ 0) :
    (legendreWeierstrassCurve parameter).IsElliptic ↔ parameter ≠ 0 ∧ parameter ≠ 1 := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero,
    ne_eq, legendreWeierstrassCurve_discriminant_eq_zero_iff parameter htwo, not_or]

/-- This family degenerates in characteristic two; no smoothness assertion is transported there. -/
theorem legendreWeierstrassCurve_not_isElliptic_of_two_eq_zero (parameter : F)
    (htwo : (2 : F) = 0) : ¬(legendreWeierstrassCurve parameter).IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero]
  have hsixteen : (16 : F) = 0 := by
    calc
      (16 : F) = 2 ^ 4 := by norm_num
      _ = 0 := by rw [htwo]; norm_num
  simp [legendreWeierstrassCurve_discriminant, hsixteen]

/-- The actual Mathlib j invariant, written literally to interface with parameter symmetries. -/
theorem legendreWeierstrassCurve_j (parameter : F)
    [(legendreWeierstrassCurve parameter).IsElliptic] :
    (legendreWeierstrassCurve parameter).j =
      256 * (parameter ^ 2 - parameter + 1) ^ 3 / (parameter ^ 2 * (1 - parameter) ^ 2) := by
  have hdiscriminant := (legendreWeierstrassCurve parameter).Δ'.ne_zero
  rw [WeierstrassCurve.coe_Δ', legendreWeierstrassCurve_discriminant] at hdiscriminant
  have hdenominator : parameter ^ 2 * (1 - parameter) ^ 2 ≠ 0 := by
    intro hzero
    apply hdiscriminant
    calc
      16 * parameter ^ 2 * (1 - parameter) ^ 2 = 16 * (parameter ^ 2 * (1 - parameter) ^ 2) := by ring
      _ = 0 := by rw [hzero, mul_zero]
  rw [WeierstrassCurve.j, Units.val_inv_eq_inv_val, ← div_eq_inv_mul,
    WeierstrassCurve.coe_Δ', legendreWeierstrassCurve_c₄,
    legendreWeierstrassCurve_discriminant,
    div_eq_div_iff hdiscriminant hdenominator]
  ring

/-- Normalizing an additive triple gives the discriminant in arithmetic coordinates. -/
theorem legendreWeierstrassCurve_discriminant_div (a b c : F)
    (hsum : a + b = c) (hc : c ≠ 0) :
    (legendreWeierstrassCurve (a / c)).Δ = 16 * a ^ 2 * b ^ 2 / c ^ 4 := by
  rw [legendreWeierstrassCurve_discriminant]
  rw [← hsum] at hc ⊢
  field_simp
  ring

theorem legendreWeierstrassCurve_c₄_div (a b c : F)
    (hsum : a + b = c) (hc : c ≠ 0) :
    (legendreWeierstrassCurve (a / c)).c₄ =
      16 * (a ^ 2 + a * b + b ^ 2) / c ^ 2 := by
  rw [legendreWeierstrassCurve_c₄]
  rw [← hsum] at hc ⊢
  field_simp
  ring

/-- The actual j invariant in additive-triple coordinates, for use in height comparisons. -/
theorem legendreWeierstrassCurve_j_div (a b c : F)
    (hsum : a + b = c) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    [(legendreWeierstrassCurve (a / c)).IsElliptic] :
    (legendreWeierstrassCurve (a / c)).j =
      256 * (a ^ 2 + a * b + b ^ 2) ^ 3 / (a ^ 2 * b ^ 2 * c ^ 2) := by
  have hcomplement : 1 - a / c = b / c := by
    field_simp
    linear_combination -hsum
  rw [legendreWeierstrassCurve_j, hcomplement]
  rw [← hsum] at hc ⊢
  field_simp
  ring

variable {K : Type*} [Field K]

/-- A field embedding preserves the punctured parameter domain and its actual elliptic curve. -/
theorem legendreWeierstrassCurve_isElliptic_map (parameter : F) (f : F →+* K)
    (htwo : (2 : F) ≠ 0) (hzero : parameter ≠ 0) (hone : parameter ≠ 1) :
    (legendreWeierstrassCurve (f parameter)).IsElliptic := by
  apply legendreWeierstrassCurve_isElliptic
  · have himage : f (2 : F) ≠ 0 := (map_ne_zero f).mpr htwo
    simpa only [map_ofNat] using himage
  · exact (map_ne_zero f).mpr hzero
  · intro hequal
    apply hone
    apply f.injective
    simpa only [map_one] using hequal

theorem legendreWeierstrassCurve_j_map (parameter : F) (f : F →+* K)
    [(legendreWeierstrassCurve parameter).IsElliptic]
    [(legendreWeierstrassCurve (f parameter)).IsElliptic] :
    (legendreWeierstrassCurve (f parameter)).j = f (legendreWeierstrassCurve parameter).j := by
  rw [legendreWeierstrassCurve_j, legendreWeierstrassCurve_j]
  simp only [map_div₀, map_mul, map_pow, map_add, map_sub, map_one, map_ofNat]

theorem legendreWeierstrassCurve_j_baseChange (parameter : F) [Algebra F K]
    [(legendreWeierstrassCurve parameter).IsElliptic]
    [(legendreWeierstrassCurve (algebraMap F K parameter)).IsElliptic] :
    (legendreWeierstrassCurve (algebraMap F K parameter)).j =
      algebraMap F K (legendreWeierstrassCurve parameter).j :=
  legendreWeierstrassCurve_j_map parameter (algebraMap F K)

end Field

section RationalABC

variable {a b c : ℕ}

/-- The existing ABC rational point defines an actual elliptic Legendre curve over ℚ. -/
theorem abcRationalPoint_legendre_isElliptic (h : IsABCTriple a b c) :
    (legendreWeierstrassCurve (abcRationalPoint a c)).IsElliptic :=
  legendreWeierstrassCurve_isElliptic _ (by norm_num)
    (abcRationalPoint_ne_zero h) (abcRationalPoint_ne_one h)

theorem abcRationalPoint_legendre_discriminant_ne_zero (h : IsABCTriple a b c) :
    (legendreWeierstrassCurve (abcRationalPoint a c)).Δ ≠ 0 :=
  legendreWeierstrassCurve_discriminant_ne_zero _ (by norm_num)
    (abcRationalPoint_ne_zero h) (abcRationalPoint_ne_one h)

/-- The discriminant of the ABC specialization, with its denominator displayed. -/
theorem abcRationalPoint_legendre_discriminant (h : IsABCTriple a b c) :
    (legendreWeierstrassCurve (abcRationalPoint a c)).Δ =
      16 * (a : ℚ) ^ 2 * (b : ℚ) ^ 2 / (c : ℚ) ^ 4 := by
  rcases h with ⟨ha, hb, hsum, _⟩
  have hc : c ≠ 0 := by omega
  exact legendreWeierstrassCurve_discriminant_div (a : ℚ) (b : ℚ) (c : ℚ)
    (by exact_mod_cast hsum) (by exact_mod_cast hc)

theorem abcRationalPoint_legendre_c₄ (h : IsABCTriple a b c) :
    (legendreWeierstrassCurve (abcRationalPoint a c)).c₄ =
      16 * ((a : ℚ) ^ 2 + (a : ℚ) * (b : ℚ) + (b : ℚ) ^ 2) / (c : ℚ) ^ 2 := by
  rcases h with ⟨ha, hb, hsum, _⟩
  have hc : c ≠ 0 := by omega
  exact legendreWeierstrassCurve_c₄_div (a : ℚ) (b : ℚ) (c : ℚ)
    (by exact_mod_cast hsum) (by exact_mod_cast hc)

/-- The actual j invariant of the ABC specialization, under its proved ellipticity instance. -/
theorem abcRationalPoint_legendre_j (h : IsABCTriple a b c) :
    letI := abcRationalPoint_legendre_isElliptic h
    (legendreWeierstrassCurve (abcRationalPoint a c)).j =
      256 * (abcRationalPoint a c ^ 2 - abcRationalPoint a c + 1) ^ 3 /
        (abcRationalPoint a c ^ 2 * (1 - abcRationalPoint a c) ^ 2) := by
  letI := abcRationalPoint_legendre_isElliptic h
  exact legendreWeierstrassCurve_j _

/-- This is the actual elliptic j invariant, not a separately defined rational expression. -/
theorem abcRationalPoint_legendre_j_eq_abcExpression (h : IsABCTriple a b c) :
    letI := abcRationalPoint_legendre_isElliptic h
    (legendreWeierstrassCurve (abcRationalPoint a c)).j =
      256 * ((a : ℚ) ^ 2 + (a : ℚ) * (b : ℚ) + (b : ℚ) ^ 2) ^ 3 /
        ((a : ℚ) ^ 2 * (b : ℚ) ^ 2 * (c : ℚ) ^ 2) := by
  letI := abcRationalPoint_legendre_isElliptic h
  letI : (legendreWeierstrassCurve ((a : ℚ) / (c : ℚ))).IsElliptic := by
    simpa only [abcRationalPoint] using abcRationalPoint_legendre_isElliptic h
  rcases h with ⟨ha, hb, hsum, _⟩
  have hc : c ≠ 0 := by omega
  exact legendreWeierstrassCurve_j_div (a : ℚ) (b : ℚ) (c : ℚ)
    (by exact_mod_cast hsum) (by exact_mod_cast Nat.ne_of_gt ha)
    (by exact_mod_cast Nat.ne_of_gt hb) (by exact_mod_cast hc)

/-- The ABC specialization remains elliptic under every rational field embedding. -/
theorem abcRationalPoint_legendre_isElliptic_map {K : Type*} [Field K]
    (f : ℚ →+* K) (h : IsABCTriple a b c) :
    (legendreWeierstrassCurve (f (abcRationalPoint a c))).IsElliptic :=
  legendreWeierstrassCurve_isElliptic_map _ f (by norm_num)
    (abcRationalPoint_ne_zero h) (abcRationalPoint_ne_one h)

/-- In particular, the arithmetic curve is available over each characteristic-zero field. -/
theorem abcRationalPoint_legendre_isElliptic_baseChange {K : Type*} [Field K] [Algebra ℚ K]
    (h : IsABCTriple a b c) :
    (legendreWeierstrassCurve (algebraMap ℚ K (abcRationalPoint a c))).IsElliptic :=
  abcRationalPoint_legendre_isElliptic_map (algebraMap ℚ K) h

end RationalABC

end LeanFormal.IUT
