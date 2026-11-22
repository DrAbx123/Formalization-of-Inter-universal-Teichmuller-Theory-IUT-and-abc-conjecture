import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The unified local value-group and integral-cone data of IUT III, Example 3.6

At a place v of a number field F, Example 3.6 uses the local quotient
Gamma_v = K_v^! / U_v together with its integral positive cone.  The finite
places and the archimedean places are different local objects (fractional
ideals versus closed balls), but they have the same value-group/integral-cone
shape.  This file freezes that common shape as actual data and proves the
elementary local laws used by the global ideal-family category.

Main contents:
* LocalValueData carries the additive value group Gamma, the integral cone
  C <= Gamma and the local principal map delta : F^! -> Gamma.
* LocalValueData.localInclusion is the local morphism condition
  delta(f) + n * a1 - a2 in C, matching handoff chapter 1, B4/C.
* identity and composition laws of the local conditions are proved; they are
  the local input for the global composition rule (m,g) o (n,f) = (nm, g f^m).
* two concrete instances are constructed for the genuine number field Q:
  the finite place p (value group Z, cone N, delta the p-adic valuation) and
  the archimedean place (R, cone [0,inf), delta -log|x|).

Boundary: this file does not construct the global ideal families, the torsor
category or the equivalence of Example 3.6; it only freezes the local value
data that those constructions consume.
-/

noncomputable section

namespace LeanFormal.IUT.IUTII.Frobenioid
namespace Example36

universe u v

/-- The local value-group data of IUT III, Example 3.6 at one place.

Gamma is the additive value group K_v^! / U_v, cone is the integral positive
cone, and delta is the local principal map from the global multiplicative
group F^!. -/
structure LocalValueData (F : Type u) (Gamma : Type v) [Field F] [AddCommGroup Gamma] where
  /-- The integral positive cone: the local effective divisors. -/
  cone : AddSubmonoid Gamma
  /-- The cone is sharp: an element and its negative both integral must vanish.
  This is the elementary-divisor/sharp-effective-monoid requirement of the
  Frobenioid structure; it is what makes an isomorphism of ideal families
  detected by the two opposite inclusions. -/
  cone_sharp : ∀ a : Gamma, a ∈ cone → -a ∈ cone → a = 0
  /-- The local principal map delta_v, multiplicative on F^! and additive in Gamma. -/
  delta : Fˣ →* Multiplicative Gamma

namespace LocalValueData

variable {F : Type u} {Gamma : Type v} [Field F] [AddCommGroup Gamma]
variable (D : LocalValueData F Gamma)

/-- The additive form of the local principal map. -/
def deltaAdd (x : Fˣ) : Gamma :=
  Multiplicative.toAdd (D.delta x)

@[simp]
theorem deltaAdd_one : D.deltaAdd 1 = 0 := by
  simp [deltaAdd]

@[simp]
theorem deltaAdd_mul (x y : Fˣ) :
    D.deltaAdd (x * y) = D.deltaAdd x + D.deltaAdd y := by
  simp [deltaAdd]

theorem deltaAdd_pow (x : Fˣ) (n : ℕ) :
    D.deltaAdd (x ^ n) = n • D.deltaAdd x := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, deltaAdd_mul, ih, add_smul, one_smul]

/-- The integral cone is closed under natural multiples. -/
theorem nsmul_mem_cone {a : Gamma} (h : a ∈ D.cone) (n : ℕ) :
    n • a ∈ D.cone := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [succ_nsmul]
      exact D.cone.add_mem ih h

/-- The local morphism condition of Example 3.6:
delta(f) + n a1 - a2 lies in the integral cone, where a1, a2 are the value
coordinates of the local objects.  In the finite case this is
nu_v(f) + n nu_v(J1) - nu_v(J2) >= 0; in the archimedean case it is
-log|f| - n log r1 + log r2 >= 0. -/
def localInclusion (n : ℕ) (f : Fˣ) (a1 a2 : Gamma) : Prop :=
  D.deltaAdd f + n • a1 - a2 ∈ D.cone

theorem localInclusion_iff_mem (n : ℕ) (f : Fˣ) (a1 a2 : Gamma) :
    D.localInclusion n f a1 a2 ↔ D.deltaAdd f + n • a1 - a2 ∈ D.cone :=
  Iff.rfl

/-- The identity local morphism (1,1) preserves every integral object. -/
theorem localInclusion_one_one (a : Gamma) :
    D.localInclusion 1 (1 : Fˣ) a a := by
  unfold localInclusion
  simp

/-- Local composition of the morphism conditions: the local part of
(m,g) o (n,f) = (nm, g f^m).  The two cone memberships are added. -/
theorem localInclusion_comp {n m : ℕ} {f g : Fˣ} {a1 a2 a3 : Gamma}
    (h1 : D.localInclusion n f a1 a2) (h2 : D.localInclusion m g a2 a3) :
    D.localInclusion (n * m) (g * f ^ m) a1 a3 := by
  unfold localInclusion at h1 h2 ⊢
  have hdelta : D.deltaAdd (g * f ^ m) = D.deltaAdd g + m • D.deltaAdd f := by
    rw [deltaAdd_mul, deltaAdd_pow]
  rw [hdelta]
  have hcone1 : m • (D.deltaAdd f + n • a1 - a2) ∈ D.cone :=
    D.nsmul_mem_cone h1 m
  have hsum : m • (D.deltaAdd f + n • a1 - a2) + (D.deltaAdd g + m • a2 - a3) ∈ D.cone :=
    D.cone.add_mem hcone1 h2
  have harith :
      D.deltaAdd g + m • D.deltaAdd f + (n * m) • a1 - a3 =
        m • (D.deltaAdd f + n • a1 - a2) + (D.deltaAdd g + m • a2 - a3) := by
    simp only [smul_sub, smul_add, smul_smul]
    rw [mul_comm n m]
    abel
  rw [harith]
  exact hsum

end LocalValueData

/-- The nonnegative integers as an additive submonoid of Z. -/
def integerNonnegCone : AddSubmonoid ℤ where
  carrier := {n | 0 ≤ n}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    simpa using add_nonneg (by simpa using ha) (by simpa using hb)

@[simp]
theorem mem_integerNonnegCone {n : ℤ} : n ∈ integerNonnegCone ↔ 0 ≤ n := by
  show n ∈ ({n : ℤ | 0 ≤ n} : Set ℤ) ↔ 0 ≤ n
  exact Iff.rfl

/-- The nonnegative reals as an additive submonoid of R. -/
def realNonnegCone : AddSubmonoid ℝ where
  carrier := {r | 0 ≤ r}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    simpa using add_nonneg (by simpa using ha) (by simpa using hb)

@[simp]
theorem mem_realNonnegCone {r : ℝ} : r ∈ realNonnegCone ↔ 0 ≤ r := by
  show r ∈ ({r : ℝ | 0 ≤ r} : Set ℝ) ↔ 0 ≤ r
  exact Iff.rfl

/-- The finite rational place p: value group Z, integral cone N, and delta the
p-adic valuation. -/
def rationalFiniteLocalData (p : ℕ) [Fact p.Prime] : LocalValueData ℚ ℤ where
  cone := integerNonnegCone
  cone_sharp := by
    intro a ha ha'
    have h1 : 0 ≤ a := ha
    have h2 : 0 ≤ -a := ha'
    omega
  delta :=
    { toFun := fun x => Multiplicative.ofAdd (padicValRat p (x : ℚ))
      map_one' := by
        rw [show ((1 : ℚˣ) : ℚ) = (1 : ℚ) from rfl, padicValRat.one]
        rfl
      map_mul' := by
        intro x y
        have hval : ((x * y : ℚˣ) : ℚ) = (x : ℚ) * (y : ℚ) := Units.val_mul x y
        rw [hval, padicValRat.mul (Units.ne_zero x) (Units.ne_zero y)]
        rfl }

/-- On the concrete finite rational place the unified inclusion condition is
exactly the valuation inequality of handoff chapter 1, B4. -/
theorem rationalFiniteLocalInclusion_iff (p : ℕ) [Fact p.Prime]
    (n : ℕ) (f : ℚˣ) (a1 a2 : ℤ) :
    (rationalFiniteLocalData p).localInclusion n f a1 a2 ↔
      padicValRat p (f : ℚ) + n * a1 - a2 ≥ 0 := by
  unfold LocalValueData.localInclusion LocalValueData.deltaAdd rationalFiniteLocalData
  simp

/-- The archimedean rational place: value group R with coordinate -log|x|, and
the nonnegative cone. -/
def rationalArchimedeanLocalData : LocalValueData ℚ ℝ where
  cone := realNonnegCone
  cone_sharp := by
    intro a ha ha'
    have h1 : 0 ≤ a := ha
    have h2 : 0 ≤ -a := ha'
    linarith
  delta :=
    { toFun := fun x => Multiplicative.ofAdd (-Real.log |(((x : ℚ) : ℝ))|)
      map_one' := by
        simp
      map_mul' := by
        intro x y
        have hx : (((x : ℚ) : ℝ)) ≠ 0 := Rat.cast_ne_zero.mpr (Units.ne_zero x)
        have hy : (((y : ℚ) : ℝ)) ≠ 0 := Rat.cast_ne_zero.mpr (Units.ne_zero y)
        have hlog : -Real.log |(((x * y : ℚˣ) : ℚ) : ℝ)| =
            -Real.log |(((x : ℚ) : ℝ))| + -Real.log |(((y : ℚ) : ℝ))| := by
          have hval : ((((x * y : ℚˣ) : ℚ)) : ℝ) =
              (((x : ℚ) : ℝ)) * (((y : ℚ) : ℝ)) := by
            rw [Units.val_mul, Rat.cast_mul]
          rw [hval, abs_mul, Real.log_mul (abs_ne_zero.mpr hx) (abs_ne_zero.mpr hy)]
          ring
        exact congrArg Multiplicative.ofAdd hlog }

/-- On the archimedean rational place the unified inclusion condition is the
inequality -log|f| - n log r1 + log r2 >= 0, i.e. the closed-ball criterion
|f| r1^n <= r2. -/
theorem rationalArchimedeanLocalInclusion_iff
    (n : ℕ) (f : ℚˣ) (a1 a2 : ℝ) :
    rationalArchimedeanLocalData.localInclusion n f a1 a2 ↔
      -Real.log |(((f : ℚ) : ℝ))| + n * a1 - a2 ≥ 0 := by
  unfold LocalValueData.localInclusion LocalValueData.deltaAdd rationalArchimedeanLocalData
  simp

end Example36
end LeanFormal.IUT.IUTII.Frobenioid
