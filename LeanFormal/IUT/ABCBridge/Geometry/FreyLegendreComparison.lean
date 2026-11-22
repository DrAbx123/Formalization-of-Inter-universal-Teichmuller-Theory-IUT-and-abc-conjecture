import LeanFormal.IUT.ABCBridge.Geometry.FreyWeierstrassCurve
import LeanFormal.IUT.ABCBridge.Geometry.LegendreWeierstrassCurve
import LeanFormal.IUT.ABCBridge.Geometry.LegendreQuadraticParameterFields
import LeanFormal.IUT.Foundations.Geometry.WeierstrassVariableChangePoints
import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange

/-!
# An actual variable change between the Frey and Legendre curves

For `a + b = c` and a unit `u` satisfying `u² = -c`, the coordinate change
`oldX = u² * newX + a`, `oldY = u³ * newY` sends the Frey equation to the
Legendre equation with parameter `a / c`. The square-root hypothesis is
retained: equality of j invariants alone would not justify this comparison
over the original field.
-/

noncomputable section

namespace LeanFormal.IUT

open LegendreQuadraticParameterFields

section VariableChange

variable {K : Type*} [Field K]

/-- The actual Mathlib change of variables: `oldX = u²X+a`, `oldY = u³Y`. -/
def freyToLegendreVariableChange (a : K) (u : Kˣ) :
    WeierstrassCurve.VariableChange K := ⟨u, a, 0, 0⟩

@[simp] theorem freyToLegendreVariableChange_u (a : K) (u : Kˣ) :
    (freyToLegendreVariableChange a u).u = u := rfl

@[simp] theorem freyToLegendreVariableChange_r (a : K) (u : Kˣ) :
    (freyToLegendreVariableChange a u).r = a := rfl

@[simp] theorem freyToLegendreVariableChange_s (a : K) (u : Kˣ) :
    (freyToLegendreVariableChange a u).s = 0 := rfl

@[simp] theorem freyToLegendreVariableChange_t (a : K) (u : Kˣ) :
    (freyToLegendreVariableChange a u).t = 0 := rfl

/-- The two distinct nonzero terms of an additive triple give a punctured parameter. -/
theorem freyLegendreParameter_ne_zero (a c : K) (ha : a ≠ 0) (hc : c ≠ 0) :
    a / c ≠ 0 := div_ne_zero ha hc

theorem freyLegendreParameter_ne_one (a b c : K)
    (hsum : a + b = c) (hb : b ≠ 0) (hc : c ≠ 0) : a / c ≠ 1 := by
  intro hone
  have hac : a = c := by
    simpa only [one_mul] using (div_eq_iff hc).mp hone
  apply hb
  linear_combination hsum - hac

/-- The square-root condition supplies exactly the scale needed for the actual curve. -/
theorem freyToLegendreVariableChange_curve (a b c : K)
    (hsum : a + b = c) (hc : c ≠ 0) (u : Kˣ) (hu : (u : K) ^ 2 = -c) :
    freyToLegendreVariableChange a u • freyWeierstrassCurve a b =
      legendreWeierstrassCurve (a / c) := by
  have hb : b = c - a := by linear_combination hsum
  have hcunit : c = -(u : K) ^ 2 := by linear_combination hu
  have hunit : (u : K) ≠ 0 := u.ne_zero
  ext <;>
    simp only [freyToLegendreVariableChange, WeierstrassCurve.variableChange_a₁,
      WeierstrassCurve.variableChange_a₂, WeierstrassCurve.variableChange_a₃,
      WeierstrassCurve.variableChange_a₄, WeierstrassCurve.variableChange_a₆,
      freyWeierstrassCurve, legendreWeierstrassCurve, hb, hcunit,
      Units.val_inv_eq_inv_val, zero_add, add_zero, zero_mul, mul_zero, sub_zero]
  all_goals (field_simp [hunit, hc] <;> ring)

/-- The inverse group action recovers the original Frey Weierstrass curve. -/
theorem freyToLegendreVariableChange_inverse_curve (a b c : K)
    (hsum : a + b = c) (hc : c ≠ 0) (u : Kˣ) (hu : (u : K) ^ 2 = -c) :
    (freyToLegendreVariableChange a u)⁻¹ • legendreWeierstrassCurve (a / c) =
      freyWeierstrassCurve a b := by
  rw [← freyToLegendreVariableChange_curve a b c hsum hc u hu]
  exact inv_smul_smul (freyToLegendreVariableChange a u) (freyWeierstrassCurve a b)

/-- The finite branch coordinates are explicitly related by the same transformation. -/
theorem freyToLegendreVariableChange_branch_coordinates (a b c : K)
    (hsum : a + b = c) (hc : c ≠ 0) (u : Kˣ) (hu : (u : K) ^ 2 = -c) :
    (u : K) ^ 2 * 0 + a = a ∧
      (u : K) ^ 2 * 1 + a = -b ∧
      (u : K) ^ 2 * (a / c) + a = 0 := by
  rw [hu]
  constructor
  · ring
  constructor
  · linear_combination hsum
  · field_simp
    ring

/-- The equation-level scaling also fixes the orientation of the variable change. -/
theorem freyToLegendreVariableChange_equation_iff (a b c x y : K)
    (hsum : a + b = c) (hc : c ≠ 0) (u : Kˣ) (hu : (u : K) ^ 2 = -c) :
    (freyWeierstrassCurve a b).toAffine.Equation
        ((u : K) ^ 2 * x + a) ((u : K) ^ 3 * y) ↔
      (legendreWeierstrassCurve (a / c)).toAffine.Equation x y := by
  have hb : b = c - a := by linear_combination hsum
  have hcunit : c = -(u : K) ^ 2 := by linear_combination hu
  have hunit : (u : K) ≠ 0 := u.ne_zero
  have hpolynomial :
      ((u : K) ^ 2 * x + a) ^ 3 +
          (b - a) * ((u : K) ^ 2 * x + a) ^ 2 -
          a * b * ((u : K) ^ 2 * x + a) =
        (u : K) ^ 6 * (x * (x - 1) * (x - a / c)) := by
    simp only [hb, hcunit]
    field_simp [hunit, hc]
    ring
  have hFreyEquation :
      (freyWeierstrassCurve a b).toAffine.Equation
          ((u : K) ^ 2 * x + a) ((u : K) ^ 3 * y) ↔
        ((u : K) ^ 3 * y) ^ 2 =
          ((u : K) ^ 2 * x + a) ^ 3 +
            (b - a) * ((u : K) ^ 2 * x + a) ^ 2 -
            a * b * ((u : K) ^ 2 * x + a) := by
    rw [WeierstrassCurve.Affine.equation_iff]
    simp only [freyWeierstrassCurve, zero_mul, zero_add, add_zero]
    constructor <;> intro hequation <;> linear_combination hequation
  have hleft : ((u : K) ^ 3 * y) ^ 2 = (u : K) ^ 6 * y ^ 2 := by ring
  rw [hFreyEquation, legendreWeierstrassCurve_equation_iff, hleft, hpolynomial]
  constructor
  · exact mul_left_cancel₀ (pow_ne_zero 6 hunit)
  · exact congrArg ((u : K) ^ 6 * ·)

/-- The comparison transports to every field embedding with its mapped square root. -/
theorem freyToLegendreVariableChange_curve_map {L : Type*} [Field L]
    (f : K →+* L) (a b c : K) (hsum : a + b = c) (hc : c ≠ 0)
    (u : Kˣ) (hu : (u : K) ^ 2 = -c) :
    freyToLegendreVariableChange (f a) (Units.map f.toMonoidHom u) •
        freyWeierstrassCurve (f a) (f b) =
      legendreWeierstrassCurve (f a / f c) := by
  apply freyToLegendreVariableChange_curve (f a) (f b) (f c)
  · simpa only [map_add] using congrArg f hsum
  · exact (map_ne_zero f).mpr hc
  · simpa using congrArg f hu

/-- Equality of actual j invariants induced by the exhibited variable change. -/
theorem freyToLegendreVariableChange_j (a b c : K)
    (hsum : a + b = c) (hc : c ≠ 0) (u : Kˣ) (hu : (u : K) ^ 2 = -c)
    [(freyWeierstrassCurve a b).IsElliptic]
    [(legendreWeierstrassCurve (a / c)).IsElliptic] :
    (freyWeierstrassCurve a b).j = (legendreWeierstrassCurve (a / c)).j := by
  simpa only [freyToLegendreVariableChange_curve a b c hsum hc u hu] using
    (WeierstrassCurve.variableChange_j (freyWeierstrassCurve a b)
      (freyToLegendreVariableChange a u)).symm

end VariableChange

section SquareRootField

variable {K : Type*} [Field K]

/-- A concrete scaling unit in the actual field obtained by adjoining a square root of `-c`. -/
def freyLegendreSquareRootUnit (c : K) (hc : c ≠ 0) : (squareRootField K (-c))ˣ :=
  Units.mk0 (squareRoot K (-c)) (squareRoot_ne_zero K (-c) (neg_ne_zero.mpr hc))

theorem freyLegendreSquareRootUnit_sq (c : K) (hc : c ≠ 0) :
    (freyLegendreSquareRootUnit c hc : squareRootField K (-c)) ^ 2 =
      -(algebraMap K (squareRootField K (-c)) c) := by
  change squareRoot K (-c) ^ 2 = -(algebraMap K (squareRootField K (-c)) c)
  simpa only [map_neg] using squareRoot_sq K (-c)

/-- A concrete extension of degree at most two realizes the curve comparison.
Both curves in the conclusion are actual base changes from `K`. -/
theorem freyLegendreComparison_overSquareRootField (a b c : K)
    (hsum : a + b = c) (hc : c ≠ 0) :
    Module.finrank K (squareRootField K (-c)) ≤ 2 ∧
      freyToLegendreVariableChange (algebraMap K (squareRootField K (-c)) a)
          (freyLegendreSquareRootUnit c hc) •
        (freyWeierstrassCurve a b).baseChange (squareRootField K (-c)) =
      (legendreWeierstrassCurve (a / c)).baseChange (squareRootField K (-c)) := by
  refine ⟨squareRootField_finrank_le_two K (-c), ?_⟩
  have hFreyBaseChange :
      (freyWeierstrassCurve a b).baseChange (squareRootField K (-c)) =
        freyWeierstrassCurve (algebraMap K (squareRootField K (-c)) a)
          (algebraMap K (squareRootField K (-c)) b) := by
    ext <;> simp [WeierstrassCurve.baseChange, WeierstrassCurve.map, freyWeierstrassCurve]
  rw [hFreyBaseChange, legendreWeierstrassCurve_baseChange, map_div₀]
  apply freyToLegendreVariableChange_curve
      (algebraMap K (squareRootField K (-c)) a)
      (algebraMap K (squareRootField K (-c)) b)
      (algebraMap K (squareRootField K (-c)) c)
  · simpa only [map_add] using congrArg (algebraMap K (squareRootField K (-c))) hsum
  · exact (map_ne_zero (algebraMap K (squareRootField K (-c)))).mpr hc
  · exact freyLegendreSquareRootUnit_sq c hc

/-- The explicitly given comparison also has an inverse over the same bounded extension. -/
theorem freyLegendreComparison_inverse_overSquareRootField (a b c : K)
    (hsum : a + b = c) (hc : c ≠ 0) :
    (freyToLegendreVariableChange (algebraMap K (squareRootField K (-c)) a)
        (freyLegendreSquareRootUnit c hc))⁻¹ •
      (legendreWeierstrassCurve (a / c)).baseChange (squareRootField K (-c)) =
    (freyWeierstrassCurve a b).baseChange (squareRootField K (-c)) := by
  rw [← (freyLegendreComparison_overSquareRootField a b c hsum hc).2]
  exact inv_smul_smul _ _

end SquareRootField

section CharacteristicZero

variable {K : Type*} [Field K] [CharZero K]

/-- The domain conditions produce an actual elliptic Legendre curve before comparing j. -/
theorem freyLegendreParameter_isElliptic (a b c : K)
    (hsum : a + b = c) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    (legendreWeierstrassCurve (a / c)).IsElliptic :=
  legendreWeierstrassCurve_isElliptic (a / c) (by norm_num)
    (freyLegendreParameter_ne_zero a c ha hc)
    (freyLegendreParameter_ne_one a b c hsum hb hc)

/-- Both sides of the comparison have proved ellipticity under the same domain conditions. -/
theorem freyLegendreComparison_frey_isElliptic (a b c : K)
    (hsum : a + b = c) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    (freyWeierstrassCurve a b).IsElliptic := by
  apply (freyWeierstrassCurve_isElliptic_iff a b).mpr
  exact ⟨by norm_num, ha, hb, by simpa only [hsum] using hc⟩

/-- The actual j invariants agree already over the base field.
The separately proved variable-change equality retains its square-root hypothesis. -/
theorem freyLegendreComparison_j (a b c : K)
    (hsum : a + b = c) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    [(freyWeierstrassCurve a b).IsElliptic]
    [(legendreWeierstrassCurve (a / c)).IsElliptic] :
    (freyWeierstrassCurve a b).j = (legendreWeierstrassCurve (a / c)).j := by
  rw [legendreWeierstrassCurve_j_div a b c hsum ha hb hc]
  rw [WeierstrassCurve.j, Units.val_inv_eq_inv_val, ← div_eq_inv_mul,
    WeierstrassCurve.coe_Δ', freyWeierstrassCurve_c₄,
    freyWeierstrassCurve_discriminant, hsum]
  field_simp [ha, hb, hc]
  ring

section RationalABC

variable [Algebra ℚ K] {a b c : ℕ}

/-- The ABC rational parameter after base change is the quotient of its natural-number casts. -/
theorem abcFreyLegendreParameter_baseChange :
    algebraMap ℚ K (abcRationalPoint a c) = (a : K) / (c : K) := by
  simp [abcRationalPoint]

/-- An ABC triple supplies the actual Frey elliptic curve over any characteristic-zero field. -/
theorem abcFreyLegendreComparison_frey_isElliptic (h : IsABCTriple a b c) :
    (freyWeierstrassCurve (a : K) (b : K)).IsElliptic := by
  rcases h with ⟨ha, hb, hsum, _⟩
  have hc : c ≠ 0 := by omega
  exact freyLegendreComparison_frey_isElliptic (a : K) (b : K) (c : K)
    (by exact_mod_cast hsum) (by exact_mod_cast Nat.ne_of_gt ha)
    (by exact_mod_cast Nat.ne_of_gt hb) (by exact_mod_cast hc)

/-- The actual ABC curve comparison holds over any field containing a square root of `-c`. -/
theorem abcFreyToLegendreVariableChange_curve (h : IsABCTriple a b c)
    (u : Kˣ) (hu : (u : K) ^ 2 = -(c : K)) :
    freyToLegendreVariableChange (a : K) u •
        freyWeierstrassCurve (a : K) (b : K) =
      legendreWeierstrassCurve (algebraMap ℚ K (abcRationalPoint a c)) := by
  rw [abcFreyLegendreParameter_baseChange]
  rcases h with ⟨ha, hb, hsum, _⟩
  have hc : c ≠ 0 := by omega
  exact freyToLegendreVariableChange_curve (a : K) (b : K) (c : K)
    (by exact_mod_cast hsum) (by exact_mod_cast hc) u hu

theorem abcFreyToLegendreVariableChange_inverse_curve (h : IsABCTriple a b c)
    (u : Kˣ) (hu : (u : K) ^ 2 = -(c : K)) :
    (freyToLegendreVariableChange (a : K) u)⁻¹ •
        legendreWeierstrassCurve (algebraMap ℚ K (abcRationalPoint a c)) =
      freyWeierstrassCurve (a : K) (b : K) := by
  rw [← abcFreyToLegendreVariableChange_curve h u hu]
  exact inv_smul_smul (freyToLegendreVariableChange (a : K) u)
    (freyWeierstrassCurve (a : K) (b : K))

/-- ABC specialization of equality of the two actual elliptic j invariants. -/
theorem abcFreyLegendreComparison_j (h : IsABCTriple a b c) :
    letI := abcFreyLegendreComparison_frey_isElliptic (K := K) h
    letI := abcRationalPoint_legendre_isElliptic_baseChange (K := K) h
    (freyWeierstrassCurve (a : K) (b : K)).j =
      (legendreWeierstrassCurve (algebraMap ℚ K (abcRationalPoint a c))).j := by
  letI := abcFreyLegendreComparison_frey_isElliptic (K := K) h
  letI := abcRationalPoint_legendre_isElliptic_baseChange (K := K) h
  rcases h with ⟨ha, hb, hsum, _⟩
  have hc : c ≠ 0 := by omega
  have hsumK : (a : K) + (b : K) = (c : K) := by exact_mod_cast hsum
  have haK : (a : K) ≠ 0 := by exact_mod_cast Nat.ne_of_gt ha
  have hbK : (b : K) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hb
  have hcK : (c : K) ≠ 0 := by exact_mod_cast hc
  letI := freyLegendreParameter_isElliptic (a : K) (b : K) (c : K)
    hsumK haK hbK hcK
  simpa only [abcFreyLegendreParameter_baseChange] using
    freyLegendreComparison_j (a : K) (b : K) (c : K) hsumK haK hbK hcK

end RationalABC

end CharacteristicZero

section NumberFieldABC

variable (K : Type*) [Field K] [NumberField K] {a b c : ℕ}

/-- The scaling unit is actual data in the number field constructed by adjoining `√(-c)`. -/
def abcFreyLegendreScalingUnit (h : IsABCTriple a b c) :
    (freyScalingField K (c : ℤ))ˣ := by
  have hc : c ≠ 0 := by
    rcases h with ⟨ha, hb, hsum, _⟩
    omega
  exact freyScalingUnit K (c : ℤ) (by exact_mod_cast hc)

theorem abcFreyLegendreScalingUnit_sq (h : IsABCTriple a b c) :
    (abcFreyLegendreScalingUnit K h : freyScalingField K (c : ℤ)) ^ 2 =
      -(c : freyScalingField K (c : ℤ)) := by
  change freyScalingRoot K (c : ℤ) ^ 2 = -(c : freyScalingField K (c : ℤ))
  simpa using freyScalingRoot_sq K (c : ℤ)

/-- Both actual elliptic curves are related by the exhibited change of variables over
the concrete number field of degree at most two over `K`. -/
theorem abcFreyLegendreComparison_overScalingField (h : IsABCTriple a b c) :
    Module.finrank K (freyScalingField K (c : ℤ)) ≤ 2 ∧
      (freyWeierstrassCurve (a : freyScalingField K (c : ℤ))
        (b : freyScalingField K (c : ℤ))).IsElliptic ∧
      (legendreWeierstrassCurve
        (algebraMap ℚ (freyScalingField K (c : ℤ)) (abcRationalPoint a c))).IsElliptic ∧
      freyToLegendreVariableChange (a : freyScalingField K (c : ℤ))
          (abcFreyLegendreScalingUnit K h) •
        freyWeierstrassCurve (a : freyScalingField K (c : ℤ))
          (b : freyScalingField K (c : ℤ)) =
      legendreWeierstrassCurve
        (algebraMap ℚ (freyScalingField K (c : ℤ)) (abcRationalPoint a c)) := by
  refine ⟨freyScalingField_finrank_le_two K (c : ℤ),
    abcFreyLegendreComparison_frey_isElliptic (K := freyScalingField K (c : ℤ)) h,
    abcRationalPoint_legendre_isElliptic_baseChange (K := freyScalingField K (c : ℤ)) h,
    ?_⟩
  exact abcFreyToLegendreVariableChange_curve (K := freyScalingField K (c : ℤ)) h
    (abcFreyLegendreScalingUnit K h) (abcFreyLegendreScalingUnit_sq K h)

/-- The same bounded-extension comparison is stated directly for base changes of the
curves over the original number field `K`. -/
theorem abcFreyLegendreComparison_baseChange_overScalingField (h : IsABCTriple a b c) :
    Module.finrank K (freyScalingField K (c : ℤ)) ≤ 2 ∧
      freyToLegendreVariableChange (a : freyScalingField K (c : ℤ))
          (abcFreyLegendreScalingUnit K h) •
        (freyWeierstrassCurve (a : K) (b : K)).baseChange (freyScalingField K (c : ℤ)) =
      (legendreWeierstrassCurve (algebraMap ℚ K (abcRationalPoint a c))).baseChange
        (freyScalingField K (c : ℤ)) := by
  refine ⟨freyScalingField_finrank_le_two K (c : ℤ), ?_⟩
  have hFreyBaseChange :
      (freyWeierstrassCurve (a : K) (b : K)).baseChange (freyScalingField K (c : ℤ)) =
        freyWeierstrassCurve (a : freyScalingField K (c : ℤ))
          (b : freyScalingField K (c : ℤ)) := by
    ext <;> simp [WeierstrassCurve.baseChange, WeierstrassCurve.map, freyWeierstrassCurve]
  have hLegendreBaseChange :
      (legendreWeierstrassCurve (algebraMap ℚ K (abcRationalPoint a c))).baseChange
          (freyScalingField K (c : ℤ)) =
        legendreWeierstrassCurve
          (algebraMap ℚ (freyScalingField K (c : ℤ)) (abcRationalPoint a c)) := by
    rw [legendreWeierstrassCurve_baseChange]
    congr 1
  rw [hFreyBaseChange, hLegendreBaseChange]
  exact (abcFreyLegendreComparison_overScalingField K h).2.2.2

theorem abcFreyLegendreComparison_inverse_overScalingField (h : IsABCTriple a b c) :
    (freyToLegendreVariableChange (a : freyScalingField K (c : ℤ))
        (abcFreyLegendreScalingUnit K h))⁻¹ •
      legendreWeierstrassCurve
        (algebraMap ℚ (freyScalingField K (c : ℤ)) (abcRationalPoint a c)) =
    freyWeierstrassCurve (a : freyScalingField K (c : ℤ))
      (b : freyScalingField K (c : ℤ)) :=
  abcFreyToLegendreVariableChange_inverse_curve (K := freyScalingField K (c : ℤ)) h
    (abcFreyLegendreScalingUnit K h) (abcFreyLegendreScalingUnit_sq K h)

/-- Equality of actual elliptic j invariants in the concrete bounded extension. -/
theorem abcFreyLegendreComparison_j_overScalingField (h : IsABCTriple a b c) :
    letI := abcFreyLegendreComparison_frey_isElliptic
      (K := freyScalingField K (c : ℤ)) h
    letI := abcRationalPoint_legendre_isElliptic_baseChange
      (K := freyScalingField K (c : ℤ)) h
    (freyWeierstrassCurve (a : freyScalingField K (c : ℤ))
      (b : freyScalingField K (c : ℤ))).j =
    (legendreWeierstrassCurve
      (algebraMap ℚ (freyScalingField K (c : ℤ)) (abcRationalPoint a c))).j :=
  abcFreyLegendreComparison_j (K := freyScalingField K (c : ℤ)) h

end NumberFieldABC

section RationalPointComparison

variable {K : Type*} [Field K] [CharZero K] [DecidableEq K]

/-- The exhibited curve change gives an actual additive equivalence of Mathlib rational points. -/
def freyToLegendrePointEquiv (a b c : K)
    (hsum : a + b = c) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (u : Kˣ) (hu : (u : K) ^ 2 = -c) :
    (legendreWeierstrassCurve (a / c)).toAffine.Point ≃+
      (freyWeierstrassCurve a b).toAffine.Point := by
  letI := freyLegendreComparison_frey_isElliptic a b c hsum ha hb hc
  exact (weierstrassPointCongr (freyToLegendreVariableChange_curve a b c hsum hc u hu).symm).trans
    (weierstrassVariableChangePointEquiv (freyWeierstrassCurve a b)
      (freyToLegendreVariableChange a u))

@[simp] theorem freyToLegendrePointEquiv_zero (a b c : K)
    (hsum : a + b = c) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (u : Kˣ) (hu : (u : K) ^ 2 = -c) :
    freyToLegendrePointEquiv a b c hsum ha hb hc u hu 0 = 0 :=
  map_zero _

/-- On finite points the actual additive equivalence has the required explicit coordinates. -/
theorem freyToLegendrePointEquiv_some (a b c : K)
    (hsum : a + b = c) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (u : Kˣ) (hu : (u : K) ^ 2 = -c) {x y : K}
    (hpoint : (legendreWeierstrassCurve (a / c)).toAffine.Nonsingular x y) :
    letI := freyLegendreComparison_frey_isElliptic a b c hsum ha hb hc
    freyToLegendrePointEquiv a b c hsum ha hb hc u hu (.some x y hpoint) =
      WeierstrassCurve.Affine.Point.mk
        ((freyToLegendreVariableChange_equation_iff a b c x y hsum hc u hu).mpr hpoint.left) := by
  letI := freyLegendreComparison_frey_isElliptic a b c hsum ha hb hc
  simp only [freyToLegendrePointEquiv, AddEquiv.trans_apply]
  rw [weierstrassPointCongr_some]
  rw [weierstrassVariableChangePointEquiv_apply]
  rw [weierstrassVariableChangePointMap_some]
  simp only [WeierstrassCurve.Affine.Point.mk,
    weierstrassChangeX, weierstrassChangeY, freyToLegendreVariableChange,
    mul_zero, zero_mul, add_zero]

variable [Algebra ℚ K] {a b c : ℕ}

/-- The ABC rational parameter is compared to the actual Frey point group. -/
def abcFreyToLegendrePointEquiv (h : IsABCTriple a b c)
    (u : Kˣ) (hu : (u : K) ^ 2 = -(c : K)) :
    (legendreWeierstrassCurve (algebraMap ℚ K (abcRationalPoint a c))).toAffine.Point ≃+
      (freyWeierstrassCurve (a : K) (b : K)).toAffine.Point := by
  letI := abcFreyLegendreComparison_frey_isElliptic (K := K) h
  exact (weierstrassPointCongr (abcFreyToLegendreVariableChange_curve h u hu).symm).trans
    (weierstrassVariableChangePointEquiv (freyWeierstrassCurve (a : K) (b : K))
      (freyToLegendreVariableChange (a : K) u))

end RationalPointComparison

section NumberFieldPointComparison

variable (K : Type*) [Field K] [NumberField K] {a b c : ℕ}
variable [DecidableEq (freyScalingField K (c : ℤ))]

/-- The concrete extension of degree at most two supplies the actual ABC/Frey point-group equivalence. -/
def abcFreyLegendreScalingPointEquiv (h : IsABCTriple a b c) :
    (legendreWeierstrassCurve
      (algebraMap ℚ (freyScalingField K (c : ℤ)) (abcRationalPoint a c))).toAffine.Point ≃+
    (freyWeierstrassCurve (a : freyScalingField K (c : ℤ))
      (b : freyScalingField K (c : ℤ))).toAffine.Point :=
  abcFreyToLegendrePointEquiv (K := freyScalingField K (c : ℤ)) h
    (abcFreyLegendreScalingUnit K h) (abcFreyLegendreScalingUnit_sq K h)

/-- Galois preserves the square equation while allowing the actual scaling root to move. -/
theorem abcFreyLegendreScalingUnit_galois_square (h : IsABCTriple a b c)
    (σ : freyScalingField K (c : ℤ) ≃ₐ[K] freyScalingField K (c : ℤ)) :
    (Units.map σ.toAlgHom.toRingHom.toMonoidHom (abcFreyLegendreScalingUnit K h) :
      freyScalingField K (c : ℤ)) ^ 2 = -(c : freyScalingField K (c : ℤ)) := by
  simpa using congrArg σ (abcFreyLegendreScalingUnit_sq K h)

theorem abcFreyLegendreScalingVariableChange_galois (h : IsABCTriple a b c)
    (σ : freyScalingField K (c : ℤ) ≃ₐ[K] freyScalingField K (c : ℤ)) :
    (freyToLegendreVariableChange (a : freyScalingField K (c : ℤ))
      (abcFreyLegendreScalingUnit K h)).map σ.toAlgHom.toRingHom =
    freyToLegendreVariableChange (a : freyScalingField K (c : ℤ))
      (Units.map σ.toAlgHom.toRingHom.toMonoidHom (abcFreyLegendreScalingUnit K h)) := by
  ext <;> simp [freyToLegendreVariableChange, WeierstrassCurve.VariableChange.map]

end NumberFieldPointComparison

end LeanFormal.IUT
