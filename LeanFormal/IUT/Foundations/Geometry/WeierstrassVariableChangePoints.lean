import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
import Mathlib.Tactic

/-!
# Variable changes on actual Weierstrass rational points

The point carrier and its additive group are Mathlib's
`WeierstrassCurve.Affine.Point`. A variable change `C` carries points of
`C • W` to points of `W` by `(x,y) ↦ (u²x+r,u³y+u²sx+t)` and fixes infinity.
The proofs below use the existing secant/tangent group law. Naturality moves
both the curve coefficients and the variable-change coefficients; no Galois
invariance of the scaling unit is assumed.
-/

noncomputable section

namespace LeanFormal.IUT

open WeierstrassCurve

/-- Base change preserves ellipticity; `W.baseChange A` is definitionally `W.map (algebraMap R A)`. -/
instance weierstrassBaseChangeIsElliptic {R A : Type*} [CommRing R] [CommRing A]
    [Algebra R A] (W : WeierstrassCurve R) [W.IsElliptic] :
    (W.baseChange A).IsElliptic :=
  instIsEllipticMap W (algebraMap R A)

section Coordinates

variable {K : Type*} [Field K]

def weierstrassChangeX (C : VariableChange K) (x : K) : K :=
  (C.u : K) ^ 2 * x + C.r

def weierstrassChangeY (C : VariableChange K) (x y : K) : K :=
  (C.u : K) ^ 3 * y + (C.u : K) ^ 2 * C.s * x + C.t

def weierstrassChangeInverseX (C : VariableChange K) (x : K) : K :=
  (C.u : K)⁻¹ ^ 2 * (x - C.r)

def weierstrassChangeInverseY (C : VariableChange K) (x y : K) : K :=
  (C.u : K)⁻¹ ^ 3 * (y - C.s * (x - C.r) - C.t)

@[simp] theorem weierstrassChangeX_inverseX (C : VariableChange K) (x : K) :
    weierstrassChangeX C (weierstrassChangeInverseX C x) = x := by
  dsimp [weierstrassChangeX, weierstrassChangeInverseX]
  field_simp [C.u.ne_zero]
  ring

@[simp] theorem weierstrassChangeInverseX_changeX (C : VariableChange K) (x : K) :
    weierstrassChangeInverseX C (weierstrassChangeX C x) = x := by
  dsimp [weierstrassChangeX, weierstrassChangeInverseX]
  field_simp [C.u.ne_zero]
  ring

@[simp] theorem weierstrassChangeY_inverseXY (C : VariableChange K) (x y : K) :
    weierstrassChangeY C (weierstrassChangeInverseX C x)
      (weierstrassChangeInverseY C x y) = y := by
  dsimp [weierstrassChangeX, weierstrassChangeY,
    weierstrassChangeInverseX, weierstrassChangeInverseY]
  field_simp [C.u.ne_zero]
  ring

@[simp] theorem weierstrassChangeInverseY_changeXY (C : VariableChange K) (x y : K) :
    weierstrassChangeInverseY C (weierstrassChangeX C x)
      (weierstrassChangeY C x y) = y := by
  dsimp [weierstrassChangeX, weierstrassChangeY,
    weierstrassChangeInverseX, weierstrassChangeInverseY]
  field_simp [C.u.ne_zero]
  ring

theorem weierstrassChangeX_injective (C : VariableChange K) :
    Function.Injective (weierstrassChangeX C) := by
  intro x z hequal
  simpa only [weierstrassChangeInverseX_changeX] using
    congrArg (weierstrassChangeInverseX C) hequal

theorem weierstrassChangeY_injective (C : VariableChange K) (x : K) :
    Function.Injective (weierstrassChangeY C x) := by
  intro y z hequal
  simpa only [weierstrassChangeInverseY_changeXY] using
    congrArg (weierstrassChangeInverseY C (weierstrassChangeX C x)) hequal

/-- The actual affine equation is carried to the original curve's equation. -/
theorem weierstrassVariableChange_equation_iff (W : WeierstrassCurve K)
    (C : VariableChange K) (x y : K) :
    W.toAffine.Equation (weierstrassChangeX C x) (weierstrassChangeY C x y) ↔
      (C • W).toAffine.Equation x y := by
  rw [Affine.equation_iff', Affine.equation_iff']
  have hscale :
      weierstrassChangeY C x y ^ 2 +
          W.a₁ * weierstrassChangeX C x * weierstrassChangeY C x y +
          W.a₃ * weierstrassChangeY C x y -
          (weierstrassChangeX C x ^ 3 + W.a₂ * weierstrassChangeX C x ^ 2 +
            W.a₄ * weierstrassChangeX C x + W.a₆) =
        (C.u : K) ^ 6 *
          (y ^ 2 + (C • W).a₁ * x * y + (C • W).a₃ * y -
            (x ^ 3 + (C • W).a₂ * x ^ 2 + (C • W).a₄ * x + (C • W).a₆)) := by
    simp only [weierstrassChangeX, weierstrassChangeY,
      WeierstrassCurve.variableChange_def, Units.val_inv_eq_inv_val]
    field_simp [C.u.ne_zero]
    ring
  rw [hscale]
  simp only [mul_eq_zero, pow_ne_zero 6 C.u.ne_zero, false_or]

theorem weierstrassVariableChange_inverse_equation (W : WeierstrassCurve K)
    (C : VariableChange K) {x y : K} (hequation : W.toAffine.Equation x y) :
    (C • W).toAffine.Equation (weierstrassChangeInverseX C x)
      (weierstrassChangeInverseY C x y) := by
  apply (weierstrassVariableChange_equation_iff W C _ _).mp
  simpa only [weierstrassChangeX_inverseX, weierstrassChangeY_inverseXY] using hequation

theorem weierstrassVariableChange_negY (W : WeierstrassCurve K)
    (C : VariableChange K) (x y : K) :
    weierstrassChangeY C x ((C • W).toAffine.negY x y) =
      W.toAffine.negY (weierstrassChangeX C x) (weierstrassChangeY C x y) := by
  simp only [Affine.negY, weierstrassChangeX, weierstrassChangeY,
    WeierstrassCurve.variableChange_def, Units.val_inv_eq_inv_val]
  field_simp [C.u.ne_zero]
  ring

theorem weierstrassVariableChange_opposite_iff (W : WeierstrassCurve K)
    (C : VariableChange K) (x₁ x₂ y₁ y₂ : K) :
    (weierstrassChangeX C x₁ = weierstrassChangeX C x₂ ∧
      weierstrassChangeY C x₁ y₁ =
        W.toAffine.negY (weierstrassChangeX C x₂) (weierstrassChangeY C x₂ y₂)) ↔
    (x₁ = x₂ ∧ y₁ = (C • W).toAffine.negY x₂ y₂) := by
  constructor
  · rintro ⟨hx, hy⟩
    have hcoordinates := weierstrassChangeX_injective C hx
    refine ⟨hcoordinates, ?_⟩
    subst x₂
    apply weierstrassChangeY_injective C x₁
    simpa only [weierstrassVariableChange_negY] using hy
  · rintro ⟨rfl, hy⟩
    exact ⟨rfl, by rw [hy, weierstrassVariableChange_negY]⟩

theorem weierstrassVariableChange_tangent_denominator (W : WeierstrassCurve K)
    (C : VariableChange K) (x y : K) :
    weierstrassChangeY C x y -
        W.toAffine.negY (weierstrassChangeX C x) (weierstrassChangeY C x y) =
      (C.u : K) ^ 3 * (y - (C • W).toAffine.negY x y) := by
  rw [← weierstrassVariableChange_negY]
  dsimp [weierstrassChangeY]
  ring

theorem weierstrassVariableChange_tangent_numerator (W : WeierstrassCurve K)
    (C : VariableChange K) (x y : K) :
    3 * weierstrassChangeX C x ^ 2 + 2 * W.a₂ * weierstrassChangeX C x + W.a₄ -
        W.a₁ * weierstrassChangeY C x y =
      (C.u : K) ^ 4 *
          (3 * x ^ 2 + 2 * (C • W).a₂ * x + (C • W).a₄ - (C • W).a₁ * y) +
        C.s * (C.u : K) ^ 3 * (y - (C • W).toAffine.negY x y) := by
  simp only [weierstrassChangeX, weierstrassChangeY, Affine.negY,
    WeierstrassCurve.variableChange_def, Units.val_inv_eq_inv_val]
  field_simp [C.u.ne_zero]
  ring

theorem weierstrassVariableChange_addX (W : WeierstrassCurve K)
    (C : VariableChange K) (x₁ x₂ slope : K) :
    weierstrassChangeX C ((C • W).toAffine.addX x₁ x₂ slope) =
      W.toAffine.addX (weierstrassChangeX C x₁) (weierstrassChangeX C x₂)
        ((C.u : K) * slope + C.s) := by
  simp only [Affine.addX, weierstrassChangeX,
    WeierstrassCurve.variableChange_def, Units.val_inv_eq_inv_val]
  field_simp [C.u.ne_zero]
  ring

theorem weierstrassVariableChange_addY (W : WeierstrassCurve K)
    (C : VariableChange K) (x₁ x₂ y₁ slope : K) :
    weierstrassChangeY C ((C • W).toAffine.addX x₁ x₂ slope)
        ((C • W).toAffine.addY x₁ x₂ y₁ slope) =
      W.toAffine.addY (weierstrassChangeX C x₁) (weierstrassChangeX C x₂)
        (weierstrassChangeY C x₁ y₁) ((C.u : K) * slope + C.s) := by
  simp only [Affine.addY, Affine.negAddY, Affine.negY, Affine.addX,
    weierstrassChangeX, weierstrassChangeY,
    WeierstrassCurve.variableChange_def, Units.val_inv_eq_inv_val]
  field_simp [C.u.ne_zero]
  ring

variable [DecidableEq K]

/-- The existing secant/tangent slope transforms by the actual linear part of the coordinate map. -/
theorem weierstrassVariableChange_slope (W : WeierstrassCurve K)
    (C : VariableChange K) {x₁ x₂ y₁ y₂ : K}
    (h₁ : (C • W).toAffine.Equation x₁ y₁)
    (h₂ : (C • W).toAffine.Equation x₂ y₂)
    (hxy : ¬(x₁ = x₂ ∧ y₁ = (C • W).toAffine.negY x₂ y₂)) :
    W.toAffine.slope (weierstrassChangeX C x₁) (weierstrassChangeX C x₂)
        (weierstrassChangeY C x₁ y₁) (weierstrassChangeY C x₂ y₂) =
      (C.u : K) * (C • W).toAffine.slope x₁ x₂ y₁ y₂ + C.s := by
  by_cases hx : x₁ = x₂
  · have hy : y₁ ≠ (C • W).toAffine.negY x₂ y₂ := fun hy => hxy ⟨hx, hy⟩
    have hyequal := Affine.Y_eq_of_Y_ne h₁ h₂ hx hy
    subst x₂
    subst y₂
    have hdenominator : y₁ - (C • W).toAffine.negY x₁ y₁ ≠ 0 := sub_ne_zero.mpr hy
    have hOldDenominator : weierstrassChangeY C x₁ y₁ -
        W.toAffine.negY (weierstrassChangeX C x₁) (weierstrassChangeY C x₁ y₁) ≠ 0 := by
      rw [weierstrassVariableChange_tangent_denominator]
      exact mul_ne_zero (pow_ne_zero 3 C.u.ne_zero) hdenominator
    rw [Affine.slope_of_Y_ne rfl (sub_ne_zero.mp hOldDenominator),
      Affine.slope_of_Y_ne rfl hy, weierstrassVariableChange_tangent_numerator,
      weierstrassVariableChange_tangent_denominator]
    field_simp [hdenominator, C.u.ne_zero]
  · have hxOld : weierstrassChangeX C x₁ ≠ weierstrassChangeX C x₂ :=
      fun hequal => hx (weierstrassChangeX_injective C hequal)
    rw [Affine.slope_of_X_ne hxOld, Affine.slope_of_X_ne hx]
    have hxdifference : weierstrassChangeX C x₁ - weierstrassChangeX C x₂ =
        (C.u : K) ^ 2 * (x₁ - x₂) := by
      dsimp [weierstrassChangeX]
      ring
    have hydifference : weierstrassChangeY C x₁ y₁ - weierstrassChangeY C x₂ y₂ =
        (C.u : K) ^ 3 * (y₁ - y₂) + (C.u : K) ^ 2 * C.s * (x₁ - x₂) := by
      dsimp [weierstrassChangeY]
      ring
    rw [hxdifference, hydifference]
    field_simp [sub_ne_zero.mpr hx, C.u.ne_zero]

end Coordinates

section ActualPoints

variable {K : Type*} [Field K] [DecidableEq K]
variable (W : WeierstrassCurve K) (C : VariableChange K) [W.IsElliptic]

/-- The forward map uses Mathlib's actual point constructors. -/
def weierstrassVariableChangePointMap : (C • W).toAffine.Point → W.toAffine.Point
  | .zero => .zero
  | .some x y h => .mk ((weierstrassVariableChange_equation_iff W C x y).mpr h.left)

def weierstrassVariableChangePointInverse : W.toAffine.Point → (C • W).toAffine.Point
  | .zero => .zero
  | .some x y h => .mk (weierstrassVariableChange_inverse_equation W C h.left)

@[simp] theorem weierstrassVariableChangePointMap_zero :
    weierstrassVariableChangePointMap W C 0 = 0 := rfl

@[simp] theorem weierstrassVariableChangePointInverse_zero :
    weierstrassVariableChangePointInverse W C 0 = 0 := rfl

@[simp] theorem weierstrassVariableChangePointMap_some {x y : K}
    (h : (C • W).toAffine.Nonsingular x y) :
    weierstrassVariableChangePointMap W C (.some x y h) =
      .mk ((weierstrassVariableChange_equation_iff W C x y).mpr h.left) := rfl

@[simp] theorem weierstrassVariableChangePointInverse_some {x y : K}
    (h : W.toAffine.Nonsingular x y) :
    weierstrassVariableChangePointInverse W C (.some x y h) =
      .mk (weierstrassVariableChange_inverse_equation W C h.left) := rfl

theorem weierstrassVariableChangePoint_leftInverse :
    Function.LeftInverse (weierstrassVariableChangePointInverse W C)
      (weierstrassVariableChangePointMap W C) := by
  intro P
  cases P with
  | zero => rfl
  | some x y h =>
    simp only [weierstrassVariableChangePointMap, weierstrassVariableChangePointInverse,
      Affine.Point.mk, Affine.Point.some.injEq]
    exact ⟨weierstrassChangeInverseX_changeX C x, weierstrassChangeInverseY_changeXY C x y⟩

theorem weierstrassVariableChangePoint_rightInverse :
    Function.RightInverse (weierstrassVariableChangePointInverse W C)
      (weierstrassVariableChangePointMap W C) := by
  intro P
  cases P with
  | zero => rfl
  | some x y h =>
    simp only [weierstrassVariableChangePointMap, weierstrassVariableChangePointInverse,
      Affine.Point.mk, Affine.Point.some.injEq]
    exact ⟨weierstrassChangeX_inverseX C x, weierstrassChangeY_inverseXY C x y⟩

/-- The existing Mathlib group law is respected, including infinity and opposite pairs. -/
theorem weierstrassVariableChangePointMap_add (P Q : (C • W).toAffine.Point) :
    weierstrassVariableChangePointMap W C (P + Q) =
      weierstrassVariableChangePointMap W C P + weierstrassVariableChangePointMap W C Q := by
  rcases P with (_ | ⟨x₁, y₁, h₁⟩)
  · rfl
  rcases Q with (_ | ⟨x₂, y₂, h₂⟩)
  · rfl
  by_cases hxy : x₁ = x₂ ∧ y₁ = (C • W).toAffine.negY x₂ y₂
  · have hold := (weierstrassVariableChange_opposite_iff W C x₁ x₂ y₁ y₂).mpr hxy
    rw [Affine.Point.add_of_Y_eq hxy.left hxy.right]
    simp only [weierstrassVariableChangePointMap, Affine.Point.mk]
    exact (Affine.Point.add_of_Y_eq hold.left hold.right).symm
  · have hold : ¬(weierstrassChangeX C x₁ = weierstrassChangeX C x₂ ∧
        weierstrassChangeY C x₁ y₁ =
          W.toAffine.negY (weierstrassChangeX C x₂) (weierstrassChangeY C x₂ y₂)) :=
      fun hequal => hxy ((weierstrassVariableChange_opposite_iff W C x₁ x₂ y₁ y₂).mp hequal)
    rw [Affine.Point.add_some hxy]
    simp only [weierstrassVariableChangePointMap, Affine.Point.mk]
    rw [Affine.Point.add_some hold, Affine.Point.some.injEq,
      weierstrassVariableChange_slope W C h₁.left h₂.left hxy]
    exact ⟨weierstrassVariableChange_addX W C x₁ x₂ _,
      weierstrassVariableChange_addY W C x₁ x₂ y₁ _⟩

/-- The actual additive equivalence induced by the Weierstrass variable change. -/
def weierstrassVariableChangePointEquiv : (C • W).toAffine.Point ≃+ W.toAffine.Point where
  toFun := weierstrassVariableChangePointMap W C
  invFun := weierstrassVariableChangePointInverse W C
  left_inv := weierstrassVariableChangePoint_leftInverse W C
  right_inv := weierstrassVariableChangePoint_rightInverse W C
  map_add' := weierstrassVariableChangePointMap_add W C

@[simp] theorem weierstrassVariableChangePointEquiv_apply (P : (C • W).toAffine.Point) :
    weierstrassVariableChangePointEquiv W C P = weierstrassVariableChangePointMap W C P := rfl

@[simp] theorem weierstrassVariableChangePointEquiv_symm_apply (P : W.toAffine.Point) :
    (weierstrassVariableChangePointEquiv W C).symm P =
      weierstrassVariableChangePointInverse W C P := rfl

theorem weierstrassVariableChangePointMap_bijective :
    Function.Bijective (weierstrassVariableChangePointMap W C) :=
  (weierstrassVariableChangePointEquiv W C).bijective

end ActualPoints

section PointTransport

variable {K : Type*} [Field K] [DecidableEq K]
variable {W V : WeierstrassCurve K}

/-- Transport along an equality of actual curves preserves their existing point group. -/
def weierstrassPointCongr (h : W = V) : W.toAffine.Point ≃+ V.toAffine.Point := by
  subst V
  exact AddEquiv.refl _

@[simp] theorem weierstrassPointCongr_zero (h : W = V) :
    weierstrassPointCongr h 0 = 0 := by
  cases h
  rfl

@[simp] theorem weierstrassPointCongr_some (h : W = V) {x y : K}
    (hpoint : W.toAffine.Nonsingular x y) :
    weierstrassPointCongr h (.some x y hpoint) = .some x y (h ▸ hpoint) := by
  cases h
  rfl

@[simp] theorem weierstrassPointCongr_refl (P : W.toAffine.Point) :
    weierstrassPointCongr (rfl : W = W) P = P := rfl

theorem weierstrassPointCongr_trans {U : WeierstrassCurve K} (hWV : W = V)
    (hVU : V = U) (P : W.toAffine.Point) :
    weierstrassPointCongr hVU (weierstrassPointCongr hWV P) =
      weierstrassPointCongr (hWV.trans hVU) P := by
  cases hWV
  cases hVU
  rfl

variable (W) [W.IsElliptic]

theorem weierstrassVariableChangePointEquiv_one (P : ((1 : VariableChange K) • W).toAffine.Point) :
    weierstrassVariableChangePointEquiv W 1 P =
      weierstrassPointCongr (one_smul (VariableChange K) W) P := by
  cases P with
  | zero => simp [← Affine.Point.zero_def]
  | some x y h =>
    simp only [weierstrassVariableChangePointEquiv_apply,
      weierstrassVariableChangePointMap_some, weierstrassPointCongr_some,
      Affine.Point.mk, Affine.Point.some.injEq]
    simp [weierstrassChangeX, weierstrassChangeY, VariableChange.one_def]

theorem weierstrassChangeX_mul (C D : VariableChange K) (x : K) :
    weierstrassChangeX (C * D) x = weierstrassChangeX D (weierstrassChangeX C x) := by
  simp only [weierstrassChangeX, VariableChange.mul_def, Units.val_mul]
  ring

theorem weierstrassChangeY_mul (C D : VariableChange K) (x y : K) :
    weierstrassChangeY (C * D) x y =
      weierstrassChangeY D (weierstrassChangeX C x) (weierstrassChangeY C x y) := by
  simp only [weierstrassChangeX, weierstrassChangeY, VariableChange.mul_def, Units.val_mul]
  ring

/-- The order agrees with Mathlib's left action on curve coefficients:
the coordinate maps for `C * D` compose as the map for `C`, then the map for `D`. -/
theorem weierstrassVariableChangePointEquiv_mul (C D : VariableChange K)
    (P : ((C * D) • W).toAffine.Point) :
    weierstrassVariableChangePointEquiv W (C * D) P =
      weierstrassVariableChangePointEquiv W D
        (weierstrassVariableChangePointEquiv (D • W) C
          (weierstrassPointCongr (mul_smul C D W) P)) := by
  cases P with
  | zero => simp [← Affine.Point.zero_def]
  | some x y h =>
    simp only [weierstrassVariableChangePointEquiv_apply,
      weierstrassVariableChangePointMap_some, weierstrassPointCongr_some,
      Affine.Point.mk, Affine.Point.some.injEq]
    exact ⟨weierstrassChangeX_mul C D x, weierstrassChangeY_mul C D x y⟩

end PointTransport

section FieldEmbeddings

variable {K L : Type*} [Field K] [Field L] [DecidableEq K] [DecidableEq L]

/-- A ring-homomorphism adapter for Mathlib's existing base-change point homomorphism. -/
def weierstrassPointMap (W : WeierstrassCurve K) (f : K →+* L) :
    W.toAffine.Point →+ (W.map f).toAffine.Point := by
  letI : Algebra K L := f.toAlgebra
  exact Affine.Point.map (W' := W.toAffine) (Algebra.ofId K L)

theorem weierstrassPointMap_nonsingular (W : WeierstrassCurve K) (f : K →+* L)
    {x y : K} (h : W.toAffine.Nonsingular x y) :
    (W.map f).toAffine.Nonsingular (f x) (f y) := by
  letI : Algebra K L := f.toAlgebra
  exact (W.toAffine.baseChange_nonsingular (Algebra.ofId K L).injective x y).mpr h

@[simp] theorem weierstrassPointMap_zero (W : WeierstrassCurve K) (f : K →+* L) :
    weierstrassPointMap W f 0 = 0 := rfl

@[simp] theorem weierstrassPointMap_some (W : WeierstrassCurve K) (f : K →+* L)
    {x y : K} (h : W.toAffine.Nonsingular x y) :
    weierstrassPointMap W f (.some x y h) =
      .some (f x) (f y) (weierstrassPointMap_nonsingular W f h) := rfl

theorem weierstrassPointMap_injective (W : WeierstrassCurve K) (f : K →+* L) :
    Function.Injective (weierstrassPointMap W f) := by
  rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩) hequal
  · rfl
  · cases hequal
  · cases hequal
  · simp only [weierstrassPointMap_some, Affine.Point.some.injEq] at hequal ⊢
    exact ⟨f.injective hequal.left, f.injective hequal.right⟩

theorem weierstrassPointMap_algebraMap [Algebra K L] (W : WeierstrassCurve K) :
    weierstrassPointMap W (algebraMap K L) =
      Affine.Point.baseChange (W' := W.toAffine) K L := by
  ext P
  cases P <;> rfl

theorem weierstrassChangeX_map (C : VariableChange K) (f : K →+* L) (x : K) :
    f (weierstrassChangeX C x) = weierstrassChangeX (C.map f) (f x) := by
  simp [weierstrassChangeX, VariableChange.map]

theorem weierstrassChangeY_map (C : VariableChange K) (f : K →+* L) (x y : K) :
    f (weierstrassChangeY C x y) = weierstrassChangeY (C.map f) (f x) (f y) := by
  simp [weierstrassChangeY, VariableChange.map]

/-- Naturality maps the variable-change coefficients as well as the point coordinates. -/
theorem weierstrassVariableChangePointEquiv_naturality (W : WeierstrassCurve K)
    (C : VariableChange K) [W.IsElliptic] (f : K →+* L) (P : (C • W).toAffine.Point) :
    weierstrassPointMap W f (weierstrassVariableChangePointEquiv W C P) =
      weierstrassVariableChangePointEquiv (W.map f) (C.map f)
        (weierstrassPointCongr (W.map_variableChange C f).symm
          (weierstrassPointMap (C • W) f P)) := by
  cases P with
  | zero => simp [← Affine.Point.zero_def]
  | some x y h =>
    simp only [weierstrassVariableChangePointEquiv_apply,
      weierstrassVariableChangePointMap_some, weierstrassPointMap_some,
      weierstrassPointCongr_some, Affine.Point.mk, Affine.Point.some.injEq]
    exact ⟨weierstrassChangeX_map C f x, weierstrassChangeY_map C f x y⟩

theorem weierstrassVariableChangePointEquiv_baseChange [Algebra K L]
    (W : WeierstrassCurve K) (C : VariableChange K) [W.IsElliptic]
    (P : (C • W).toAffine.Point) :
    weierstrassPointMap W (algebraMap K L) (weierstrassVariableChangePointEquiv W C P) =
      weierstrassVariableChangePointEquiv (W.baseChange L) (C.map (algebraMap K L))
        (weierstrassPointCongr (W.map_variableChange C (algebraMap K L)).symm
          (weierstrassPointMap (C • W) (algebraMap K L) P)) :=
  weierstrassVariableChangePointEquiv_naturality W C (algebraMap K L) P

end FieldEmbeddings

section GaloisNaturality

variable {F K : Type*} [Field F] [Field K] [Algebra F K] [DecidableEq K]

/-- Semilinear compatibility for an arbitrary curve: both `W` and `C` are conjugated. -/
theorem weierstrassVariableChangePointEquiv_galois_naturality (W : WeierstrassCurve K)
    (C : VariableChange K) [W.IsElliptic] (σ : K ≃ₐ[F] K)
    (P : (C • W).toAffine.Point) :
    weierstrassPointMap W σ.toAlgHom.toRingHom (weierstrassVariableChangePointEquiv W C P) =
      weierstrassVariableChangePointEquiv (W.map σ.toAlgHom.toRingHom)
        (C.map σ.toAlgHom.toRingHom)
        (weierstrassPointCongr (W.map_variableChange C σ.toAlgHom.toRingHom).symm
          (weierstrassPointMap (C • W) σ.toAlgHom.toRingHom P)) :=
  weierstrassVariableChangePointEquiv_naturality W C σ.toAlgHom.toRingHom P

/-- The existing Mathlib point maps give the actual Galois additive equivalence on a base curve. -/
def weierstrassPointGaloisEquiv (W : WeierstrassCurve F) (σ : K ≃ₐ[F] K) :
    (W.baseChange K).toAffine.Point ≃+ (W.baseChange K).toAffine.Point where
  toFun := Affine.Point.map (W' := W.toAffine) σ.toAlgHom
  invFun := Affine.Point.map (W' := W.toAffine) σ.symm.toAlgHom
  left_inv := by
    intro P
    cases P <;> simp [Affine.Point.map, Affine.Point.some.injEq, ← Affine.Point.zero_def]
  right_inv := by
    intro P
    cases P <;> simp [Affine.Point.map, Affine.Point.some.injEq, ← Affine.Point.zero_def]
  map_add' := (Affine.Point.map (W' := W.toAffine) σ.toAlgHom).map_add

@[simp] theorem weierstrassPointGaloisEquiv_zero (W : WeierstrassCurve F) (σ : K ≃ₐ[F] K) :
    weierstrassPointGaloisEquiv W σ 0 = 0 := rfl

theorem weierstrassBaseChange_galois_fixed (W : WeierstrassCurve F) (σ : K ≃ₐ[F] K) :
    (W.baseChange K).map σ.toAlgHom.toRingHom = W.baseChange K := by
  ext <;> simp [WeierstrassCurve.baseChange, WeierstrassCurve.map]

theorem weierstrassChangedCurve_galois (W : WeierstrassCurve F)
    (C : VariableChange K) (σ : K ≃ₐ[F] K) :
    (C • W.baseChange K).map σ.toAlgHom.toRingHom =
      C.map σ.toAlgHom.toRingHom • W.baseChange K := by
  rw [← WeierstrassCurve.map_variableChange, weierstrassBaseChange_galois_fixed]

/-- Galois sends the changed curve to the curve changed by the conjugate coefficients. -/
def weierstrassChangedPointGalois (W : WeierstrassCurve F)
    (C : VariableChange K) (σ : K ≃ₐ[F] K) :
    (C • W.baseChange K).toAffine.Point →+
      (C.map σ.toAlgHom.toRingHom • W.baseChange K).toAffine.Point :=
  (weierstrassPointCongr (weierstrassChangedCurve_galois W C σ)).toAddMonoidHom.comp
    (weierstrassPointMap (C • W.baseChange K) σ.toAlgHom.toRingHom)

/-- The accurate Galois square for a base curve allows the change-of-variables coefficients to move. -/
theorem weierstrassVariableChangePointEquiv_galois_baseChange (W : WeierstrassCurve F)
    [W.IsElliptic] (C : VariableChange K) (σ : K ≃ₐ[F] K)
    (P : (C • W.baseChange K).toAffine.Point) :
    weierstrassPointGaloisEquiv W σ
        (weierstrassVariableChangePointEquiv (W.baseChange K) C P) =
      weierstrassVariableChangePointEquiv (W.baseChange K) (C.map σ.toAlgHom.toRingHom)
        (weierstrassChangedPointGalois W C σ P) := by
  cases P with
  | zero =>
    rw [← Affine.Point.zero_def, map_zero (weierstrassChangedPointGalois W C σ),
      weierstrassVariableChangePointEquiv_apply, weierstrassVariableChangePointMap_zero,
      weierstrassPointGaloisEquiv_zero]
    rfl
  | some x y h =>
    have hCG : weierstrassChangedPointGalois W C σ (Affine.Point.some x y h) =
        weierstrassPointCongr (weierstrassChangedCurve_galois W C σ)
          (weierstrassPointMap (C • W.baseChange K) σ.toAlgHom.toRingHom (Affine.Point.some x y h)) := rfl
    rw [hCG]
    rw [weierstrassPointMap_some]
    rw [weierstrassPointCongr_some]
    change Affine.Point.map (W' := W.toAffine) σ.toAlgHom
        (weierstrassVariableChangePointMap (W.baseChange K) C (Affine.Point.some x y h)) =
      weierstrassVariableChangePointMap (W.baseChange K) (C.map σ.toAlgHom.toRingHom)
        (Affine.Point.some (σ.toAlgHom.toRingHom x) (σ.toAlgHom.toRingHom y)
          (weierstrassChangedCurve_galois W C σ ▸
            weierstrassPointMap_nonsingular (C • W.baseChange K) σ.toAlgHom.toRingHom h))
    rw [weierstrassVariableChangePointMap_some]
    rw [weierstrassVariableChangePointMap_some]
    simp [Affine.Point.map, Affine.Point.mk, Affine.Point.some.injEq,
      weierstrassChangeX, weierstrassChangeY, VariableChange.map]

/-- Galois transport between the two changed models is also an actual additive equivalence. -/
def weierstrassChangedPointGaloisEquiv (W : WeierstrassCurve F)
    [W.IsElliptic] (C : VariableChange K) (σ : K ≃ₐ[F] K) :
    (C • W.baseChange K).toAffine.Point ≃+
      (C.map σ.toAlgHom.toRingHom • W.baseChange K).toAffine.Point :=
  (weierstrassVariableChangePointEquiv (W.baseChange K) C).trans
    ((weierstrassPointGaloisEquiv W σ).trans
      (weierstrassVariableChangePointEquiv (W.baseChange K)
        (C.map σ.toAlgHom.toRingHom)).symm)

theorem weierstrassChangedPointGaloisEquiv_apply (W : WeierstrassCurve F)
    [W.IsElliptic] (C : VariableChange K) (σ : K ≃ₐ[F] K)
    (P : (C • W.baseChange K).toAffine.Point) :
    weierstrassChangedPointGaloisEquiv W C σ P = weierstrassChangedPointGalois W C σ P := by
  apply (weierstrassVariableChangePointEquiv (W.baseChange K)
    (C.map σ.toAlgHom.toRingHom)).injective
  simp only [weierstrassChangedPointGaloisEquiv, AddEquiv.trans_apply,
    AddEquiv.apply_symm_apply]
  exact weierstrassVariableChangePointEquiv_galois_baseChange W C σ P

theorem weierstrassPointGaloisEquiv_refl (W : WeierstrassCurve F)
    (P : (W.baseChange K).toAffine.Point) :
    weierstrassPointGaloisEquiv W (AlgEquiv.refl : K ≃ₐ[F] K) P = P := by
  cases P <;> rfl

theorem weierstrassPointGaloisEquiv_trans (W : WeierstrassCurve F)
    (σ τ : K ≃ₐ[F] K) (P : (W.baseChange K).toAffine.Point) :
    weierstrassPointGaloisEquiv W (σ.trans τ) P =
      weierstrassPointGaloisEquiv W τ (weierstrassPointGaloisEquiv W σ P) := by
  cases P <;> rfl

end GaloisNaturality

end LeanFormal.IUT
