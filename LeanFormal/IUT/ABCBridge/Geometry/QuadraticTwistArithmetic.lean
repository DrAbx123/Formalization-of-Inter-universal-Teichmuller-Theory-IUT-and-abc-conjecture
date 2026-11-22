import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
import LeanFormal.IUT.ABCBridge.Geometry.FreyWeierstrassCurve

/-!
# Quadratic-twist arithmetic for the Frey/Legendre comparison

This file treats only Weierstrass models with `a₁ = a₃ = 0`.  For those models
the twist coefficients are `d*a₂`, `d²*a₄`, and `d³*a₆`.  The input equalities
are explicit; this construction does not turn an arbitrary characteristic-two
Weierstrass equation into an even equation.

The invariant statements use Mathlib's actual `c₄`, `c₆`, `Δ`, and `j`.
The square-root comparison uses Mathlib's actual `VariableChange` action;
equality of j-invariants is not used as an isomorphism criterion.

Consumer: the concrete Frey/Legendre comparison over a field in which the
twist parameter has a nonzero square root.  CANDIDATE pending batch validation.
-/

namespace LeanFormal.IUT

universe u v

section RestrictedTwist

variable {R : Type u} [CommRing R]

/-- The quadratic twist construction restricted to models with zero odd coefficients. -/
def zeroOddWeierstrassQuadraticTwist (W : WeierstrassCurve R) (d : R)
    (_ha₁ : W.a₁ = 0) (_ha₃ : W.a₃ = 0) : WeierstrassCurve R where
  a₁ := 0
  a₂ := d * W.a₂
  a₃ := 0
  a₄ := d ^ 2 * W.a₄
  a₆ := d ^ 3 * W.a₆

variable (W : WeierstrassCurve R) (d : R) (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0)

@[simp] theorem zeroOddWeierstrassQuadraticTwist_a₁ :
    (zeroOddWeierstrassQuadraticTwist W d ha₁ ha₃).a₁ = 0 := rfl

@[simp] theorem zeroOddWeierstrassQuadraticTwist_a₂ :
    (zeroOddWeierstrassQuadraticTwist W d ha₁ ha₃).a₂ = d * W.a₂ := rfl

@[simp] theorem zeroOddWeierstrassQuadraticTwist_a₃ :
    (zeroOddWeierstrassQuadraticTwist W d ha₁ ha₃).a₃ = 0 := rfl

@[simp] theorem zeroOddWeierstrassQuadraticTwist_a₄ :
    (zeroOddWeierstrassQuadraticTwist W d ha₁ ha₃).a₄ = d ^ 2 * W.a₄ := rfl

@[simp] theorem zeroOddWeierstrassQuadraticTwist_a₆ :
    (zeroOddWeierstrassQuadraticTwist W d ha₁ ha₃).a₆ = d ^ 3 * W.a₆ := rfl

@[simp] theorem zeroOddWeierstrassQuadraticTwist_one :
    zeroOddWeierstrassQuadraticTwist W 1 ha₁ ha₃ = W := by
  ext <;> simp [zeroOddWeierstrassQuadraticTwist, ha₁, ha₃]

/-- Successive twists multiply their parameters at the level of the chosen models. -/
theorem zeroOddWeierstrassQuadraticTwist_mul (e : R) :
    zeroOddWeierstrassQuadraticTwist
        (zeroOddWeierstrassQuadraticTwist W d ha₁ ha₃) e rfl rfl =
      zeroOddWeierstrassQuadraticTwist W (e * d) ha₁ ha₃ := by
  ext <;> simp [zeroOddWeierstrassQuadraticTwist] <;> ring

@[simp] theorem zeroOddWeierstrassQuadraticTwist_b₂ :
    (zeroOddWeierstrassQuadraticTwist W d ha₁ ha₃).b₂ = d * W.b₂ := by
  simp [WeierstrassCurve.b₂, zeroOddWeierstrassQuadraticTwist, ha₁] <;> ring

@[simp] theorem zeroOddWeierstrassQuadraticTwist_b₄ :
    (zeroOddWeierstrassQuadraticTwist W d ha₁ ha₃).b₄ = d ^ 2 * W.b₄ := by
  simp [WeierstrassCurve.b₄, zeroOddWeierstrassQuadraticTwist, ha₁, ha₃] <;> ring

@[simp] theorem zeroOddWeierstrassQuadraticTwist_b₆ :
    (zeroOddWeierstrassQuadraticTwist W d ha₁ ha₃).b₆ = d ^ 3 * W.b₆ := by
  simp [WeierstrassCurve.b₆, zeroOddWeierstrassQuadraticTwist, ha₃] <;> ring

@[simp] theorem zeroOddWeierstrassQuadraticTwist_b₈ :
    (zeroOddWeierstrassQuadraticTwist W d ha₁ ha₃).b₈ = d ^ 4 * W.b₈ := by
  simp [WeierstrassCurve.b₈, zeroOddWeierstrassQuadraticTwist, ha₁, ha₃] <;> ring

@[simp] theorem zeroOddWeierstrassQuadraticTwist_c₄ :
    (zeroOddWeierstrassQuadraticTwist W d ha₁ ha₃).c₄ = d ^ 2 * W.c₄ := by
  simp only [WeierstrassCurve.c₄, zeroOddWeierstrassQuadraticTwist_b₂,
    zeroOddWeierstrassQuadraticTwist_b₄]
  ring

@[simp] theorem zeroOddWeierstrassQuadraticTwist_c₆ :
    (zeroOddWeierstrassQuadraticTwist W d ha₁ ha₃).c₆ = d ^ 3 * W.c₆ := by
  simp only [WeierstrassCurve.c₆, zeroOddWeierstrassQuadraticTwist_b₂,
    zeroOddWeierstrassQuadraticTwist_b₄, zeroOddWeierstrassQuadraticTwist_b₆]
  ring

@[simp] theorem zeroOddWeierstrassQuadraticTwist_discriminant :
    (zeroOddWeierstrassQuadraticTwist W d ha₁ ha₃).Δ = d ^ 6 * W.Δ := by
  simp only [WeierstrassCurve.Δ, zeroOddWeierstrassQuadraticTwist_b₂,
    zeroOddWeierstrassQuadraticTwist_b₄, zeroOddWeierstrassQuadraticTwist_b₆,
    zeroOddWeierstrassQuadraticTwist_b₈]
  ring

/-- Over a ring, the twist parameter must be a unit for this ellipticity implication. -/
theorem zeroOddWeierstrassQuadraticTwist_isElliptic
    [W.IsElliptic] (hd : IsUnit d) :
    (zeroOddWeierstrassQuadraticTwist W d ha₁ ha₃).IsElliptic := by
  refine ⟨?_⟩
  rw [zeroOddWeierstrassQuadraticTwist_discriminant]
  exact (hd.pow 6).mul W.isUnit_Δ

/-- This literal equality connects the twist arithmetic to the Frey family. -/
theorem zeroOddWeierstrassQuadraticTwist_frey (a b d : R) :
    zeroOddWeierstrassQuadraticTwist (freyWeierstrassCurve a b) d rfl rfl =
      freyWeierstrassCurve (d * a) (d * b) := by
  ext <;> simp [zeroOddWeierstrassQuadraticTwist, freyWeierstrassCurve] <;> ring

end RestrictedTwist

section TwistBaseChange

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
variable (W : WeierstrassCurve R) (d : R) (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0)

/-- Twisting commutes exactly with a ring-homomorphism base change. -/
theorem zeroOddWeierstrassQuadraticTwist_map (f : R →+* S) :
    (zeroOddWeierstrassQuadraticTwist W d ha₁ ha₃).map f =
      zeroOddWeierstrassQuadraticTwist (W.map f) (f d)
        (by simp [WeierstrassCurve.map_a₁, ha₁])
        (by simp [WeierstrassCurve.map_a₃, ha₃]) := by
  ext <;> simp [zeroOddWeierstrassQuadraticTwist, WeierstrassCurve.map]

theorem zeroOddWeierstrassQuadraticTwist_baseChange [Algebra R S] :
    (zeroOddWeierstrassQuadraticTwist W d ha₁ ha₃).baseChange S =
      zeroOddWeierstrassQuadraticTwist (W.baseChange S) (algebraMap R S d)
        (by simp [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁, ha₁])
        (by simp [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₃, ha₃]) := by
  exact zeroOddWeierstrassQuadraticTwist_map W d ha₁ ha₃ (algebraMap R S)

end TwistBaseChange

section FieldTwist

variable {K : Type u} [Field K]
variable (W : WeierstrassCurve K) (d : K) (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0)

/-- The twisted cubic is nonsingular exactly when its parameter and original discriminant are nonzero. -/
theorem zeroOddWeierstrassQuadraticTwist_isElliptic_iff :
    (zeroOddWeierstrassQuadraticTwist W d ha₁ ha₃).IsElliptic ↔
      d ≠ 0 ∧ W.IsElliptic := by
  constructor
  · intro htwisted
    have hdiscriminant := htwisted.isUnit.ne_zero
    rw [zeroOddWeierstrassQuadraticTwist_discriminant] at hdiscriminant
    have hd : d ≠ 0 := by
      intro hdzero
      apply hdiscriminant
      simp [hdzero]
    refine ⟨hd, ⟨isUnit_iff_ne_zero.mpr ?_⟩⟩
    exact (mul_ne_zero_iff.mp hdiscriminant).2
  · rintro ⟨hd, horiginal⟩
    letI := horiginal
    exact zeroOddWeierstrassQuadraticTwist_isElliptic W d ha₁ ha₃
      (isUnit_iff_ne_zero.mpr hd)

/-- Equality of the actual j-invariants, without asserting an isomorphism over the base field. -/
theorem zeroOddWeierstrassQuadraticTwist_j [W.IsElliptic] (hd : d ≠ 0) :
    letI := zeroOddWeierstrassQuadraticTwist_isElliptic W d ha₁ ha₃
      (isUnit_iff_ne_zero.mpr hd)
    (zeroOddWeierstrassQuadraticTwist W d ha₁ ha₃).j = W.j := by
  letI := zeroOddWeierstrassQuadraticTwist_isElliptic W d ha₁ ha₃
    (isUnit_iff_ne_zero.mpr hd)
  have hdiscriminant : W.Δ ≠ 0 := W.isUnit_Δ.ne_zero
  simp only [WeierstrassCurve.j, Units.val_inv_eq_inv_val, WeierstrassCurve.coe_Δ',
    zeroOddWeierstrassQuadraticTwist_c₄, zeroOddWeierstrassQuadraticTwist_discriminant]
  field_simp [hd, hdiscriminant] <;> ring

end FieldTwist

section SquareRootVariableChange

variable {R : Type u} [CommRing R]

/-- The actual coordinate change with old coordinates `(u²*X,u³*Y)`. -/
def quadraticTwistRootVariableChange (u : Rˣ) : WeierstrassCurve.VariableChange R where
  u := u
  r := 0
  s := 0
  t := 0

@[simp] theorem quadraticTwistRootVariableChange_u (u : Rˣ) :
    (quadraticTwistRootVariableChange u).u = u := rfl

@[simp] theorem quadraticTwistRootVariableChange_r (u : Rˣ) :
    (quadraticTwistRootVariableChange u).r = 0 := rfl

@[simp] theorem quadraticTwistRootVariableChange_s (u : Rˣ) :
    (quadraticTwistRootVariableChange u).s = 0 := rfl

@[simp] theorem quadraticTwistRootVariableChange_t (u : Rˣ) :
    (quadraticTwistRootVariableChange u).t = 0 := rfl

/-- A unit square root explicitly removes the twist by the real Mathlib action. -/
theorem quadraticTwistRootVariableChange_smul
    (W : WeierstrassCurve R) (d : R) (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0)
    (u : Rˣ) (hroot : (u : R) ^ 2 = d) :
    quadraticTwistRootVariableChange u •
        zeroOddWeierstrassQuadraticTwist W d ha₁ ha₃ = W := by
  have hcancel₂ : (↑u⁻¹ : R) ^ 2 * d = 1 := by
    rw [← hroot, ← mul_pow]
    simp
  have hcancel₄ : (↑u⁻¹ : R) ^ 4 * d ^ 2 = 1 := by
    calc
      (↑u⁻¹ : R) ^ 4 * d ^ 2 = ((↑u⁻¹ : R) ^ 2 * d) ^ 2 := by ring
      _ = 1 := by rw [hcancel₂]; simp
  have hcancel₆ : (↑u⁻¹ : R) ^ 6 * d ^ 3 = 1 := by
    calc
      (↑u⁻¹ : R) ^ 6 * d ^ 3 = ((↑u⁻¹ : R) ^ 2 * d) ^ 3 := by ring
      _ = 1 := by rw [hcancel₂]; simp
  rw [WeierstrassCurve.variableChange_def]
  ext <;> simp [quadraticTwistRootVariableChange, zeroOddWeierstrassQuadraticTwist,
    ha₁, ha₃, ← mul_assoc, hcancel₂, hcancel₄, hcancel₆]

/-- The inverse coordinate change constructs the twist from the original equation. -/
theorem zeroOddWeierstrassQuadraticTwist_eq_inv_smul
    (W : WeierstrassCurve R) (d : R) (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0)
    (u : Rˣ) (hroot : (u : R) ^ 2 = d) :
    zeroOddWeierstrassQuadraticTwist W d ha₁ ha₃ =
      (quadraticTwistRootVariableChange u)⁻¹ • W := by
  conv_rhs => rw [← quadraticTwistRootVariableChange_smul W d ha₁ ha₃ u hroot]
  simp only [smul_smul, inv_mul_cancel, one_smul]

/-- Applied to the Frey family, the coordinate substitution is an equality of actual curves. -/
theorem quadraticTwistRootVariableChange_smul_frey
    (a b d : R) (u : Rˣ) (hroot : (u : R) ^ 2 = d) :
    quadraticTwistRootVariableChange u • freyWeierstrassCurve (d * a) (d * b) =
      freyWeierstrassCurve a b := by
  rw [← zeroOddWeierstrassQuadraticTwist_frey]
  exact quadraticTwistRootVariableChange_smul (freyWeierstrassCurve a b) d rfl rfl u hroot

end SquareRootVariableChange

section SquareRootFieldExtension

variable {K : Type u} {L : Type v} [Field K] [Field L]

/-- A nonzero square root in a target field supplies the actual change of variables there. -/
theorem zeroOddWeierstrassQuadraticTwist_map_squareRoot
    (W : WeierstrassCurve K) (d : K) (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0)
    (f : K →+* L) (root : L) (hroot : root ^ 2 = f d) (hroot_ne : root ≠ 0) :
    quadraticTwistRootVariableChange (Units.mk0 root hroot_ne) •
        ((zeroOddWeierstrassQuadraticTwist W d ha₁ ha₃).map f) = W.map f := by
  rw [zeroOddWeierstrassQuadraticTwist_map]
  apply quadraticTwistRootVariableChange_smul
  exact hroot

/-- If the twist parameter is nonzero, a chosen square root is automatically nonzero. -/
theorem zeroOddWeierstrassQuadraticTwist_map_exists_variableChange
    (W : WeierstrassCurve K) (d : K) (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0)
    (hd : d ≠ 0) (f : K →+* L) (root : L) (hroot : root ^ 2 = f d) :
    ∃ coordinateChange : WeierstrassCurve.VariableChange L,
      coordinateChange • ((zeroOddWeierstrassQuadraticTwist W d ha₁ ha₃).map f) = W.map f := by
  have hroot_ne : root ≠ 0 := by
    intro hzero
    have hparameter : f d = 0 := by simpa [hzero] using hroot.symm
    exact hd (f.injective (by simpa using hparameter))
  exact ⟨quadraticTwistRootVariableChange (Units.mk0 root hroot_ne),
    zeroOddWeierstrassQuadraticTwist_map_squareRoot W d ha₁ ha₃ f root hroot hroot_ne⟩

end SquareRootFieldExtension

end LeanFormal.IUT
