import LeanFormal.IUT.Foundations.Arithmetic.NormLog
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Algebra.Ring.Subring.Units
import Mathlib.Algebra.Group.TypeTags.Hom
import Mathlib.Analysis.Complex.Basic

/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/

/-!
# The archimedean local dictionary of III Example 3.6

This module formalizes the archimedean half of the local dictionary used in
Inter-universal Teichmüller Theory III, Example 3.6: at an infinite place of a
number field the local objects are closed balls B(r) of a real or complex
local field, the scale is the quotient of the multiplicative group by the
norm-one unit circle, and the local degree functional is the additive character
u ↦ -log ‖u‖.

The main mathematical contents are:

* the closed-ball object localClosedBall K r, its zero-radius degeneration,
  and the monotonicity/injectivity of the radius (under the explicit hypothesis
  RadiusRealization K that every nonnegative radius occurs as a norm);
* the power region localPowerImage K r n = B(r)^n and the exact scaled
  containment criterion
  f * B(r1)^n ⊆ B(r2) ↔ ‖f‖ * r1^n ≤ r2,
  together with its logarithmic form
  ν(f) + n·δ(r1) − δ(r2) ≥ 0, where ν(f) = -log ‖f‖ and
  δ(r) = -log r is the "delta" of the handoff (the archimedean analogue of
  the finite-place valuation of a generator);
* the norm-one unit circle normOneUnits K, the identification of
  Kˣ / normOneUnits K with the positive units of ℝ via the norm, and the
  compatibility of this quotient with the log dictionary;
* the calibration that the closed unit ball is not additively closed, so that
  the archimedean local object is an ordered scale object and not a ring or
  module region;
* the instantiations K = ℝ and K = ℂ, where RadiusRealization is proved.

The hypothesis RadiusRealization K is genuine: for a general normed field,
for example ℚ_p, the set of norms is discrete and radii cannot be recovered
from balls.  It is proved here for ℝ and ℂ only.

This file supplies the local archimedean dictionary only.  It does not construct
global ideal families, local Hodge theaters, prime-strips, or Kummer
identifications, and it does not touch the complex Haar normalization: in the
chapter's language this is the archimedean local half of Ex3.6, at the level of
one place.  The complex Haar degree-two factor [ℂ : ℝ] belongs to the later
global normalization layer and is deliberately not used here.
-/

namespace LeanFormal.IUT

variable {K : Type*}

section RadiusRealization

variable [NormedField K]

/-- RadiusRealization K states that every nonnegative real number is the norm
of some element of K.  This is the precise hypothesis needed to recover a
radius from a closed ball, and to turn a containment of scaled power regions into
a numerical inequality.  It fails for a general normed field (for example
ℚ_p), and is proved below for ℝ and ℂ. -/
def RadiusRealization (K : Type*) [NormedField K] : Prop :=
  ∀ r : ℝ, 0 ≤ r → ∃ x : K, ‖x‖ = r

/-- The archimedean local object of radius r: the closed ball {x | ‖x‖ ≤ r}. -/
def localClosedBall (K : Type*) [NormedField K] (r : ℝ) : Set K :=
  Metric.closedBall (0 : K) r

/-- Membership in the closed radius-r ball is the norm bound. -/
theorem mem_localClosedBall {r : ℝ} {x : K} :
    x ∈ localClosedBall K r ↔ ‖x‖ ≤ r := by
  rw [localClosedBall, Metric.mem_closedBall, dist_zero_right]

/-- The radius-zero local object is the singleton zero ball. -/
theorem localClosedBall_zero : localClosedBall K (0 : ℝ) = {0} := by
  rw [localClosedBall, Metric.closedBall_zero]

/-- The zero point lies in the closed ball exactly when the radius is nonnegative. -/
theorem zero_mem_localClosedBall {r : ℝ} :
    (0 : K) ∈ localClosedBall K r ↔ 0 ≤ r := by
  rw [mem_localClosedBall, norm_zero]

/-- Under radius realization, the ball scale is monotone in the radius, and
conversely the containment of balls recovers the inequality of radii. -/
theorem localClosedBall_subset_iff (hreal : RadiusRealization K) {r1 r2 : ℝ}
    (hr1 : 0 ≤ r1) :
    localClosedBall K r1 ⊆ localClosedBall K r2 ↔ r1 ≤ r2 := by
  constructor
  · intro hsub
    obtain ⟨x, hx⟩ := hreal r1 hr1
    have hxmem : x ∈ localClosedBall K r1 := mem_localClosedBall.mpr (le_of_eq hx)
    have hbound : ‖x‖ ≤ r2 := mem_localClosedBall.mp (hsub hxmem)
    rwa [hx] at hbound
  · intro hle x hx
    exact mem_localClosedBall.mpr (le_trans (mem_localClosedBall.mp hx) hle)

/-- Under radius realization the radius is recovered from the closed ball: two
closed balls with nonnegative radii are equal if and only if the radii are equal. -/
theorem localClosedBall_eq_iff (hreal : RadiusRealization K) {r1 r2 : ℝ}
    (h1 : 0 ≤ r1) (h2 : 0 ≤ r2) :
    localClosedBall K r1 = localClosedBall K r2 ↔ r1 = r2 := by
  constructor
  · intro heq
    have h12 : r1 ≤ r2 :=
      (localClosedBall_subset_iff hreal h1).mp (le_of_eq heq)
    have h21 : r2 ≤ r1 :=
      (localClosedBall_subset_iff hreal h2).mp (le_of_eq heq.symm)
    exact le_antisymm h12 h21
  · intro h
    rw [h]

/-- A nonnegative radius is realized by a nonempty closed ball. -/
theorem localClosedBall_nonempty (hreal : RadiusRealization K) {r : ℝ}
    (hr : 0 ≤ r) : (localClosedBall K r).Nonempty := by
  obtain ⟨x, hx⟩ := hreal r hr
  exact ⟨x, mem_localClosedBall.mpr (le_of_eq hx)⟩

/-- The n-fold multiplicative image B(r)^n = {x ^ n | x ∈ B(r)}. -/
def localPowerImage (K : Type*) [NormedField K] (r : ℝ) (n : ℕ) : Set K :=
  {y : K | ∃ x : K, ‖x‖ ≤ r ∧ y = x ^ n}

/-- Membership in the n-fold power region. -/
theorem mem_localPowerImage {r : ℝ} {n : ℕ} {y : K} :
    y ∈ localPowerImage K r n ↔ ∃ x : K, ‖x‖ ≤ r ∧ y = x ^ n :=
  Iff.rfl

/-- The power region is the image of the ball under the n-th power map. -/
theorem localPowerImage_eq_image (r : ℝ) (n : ℕ) :
    localPowerImage K r n = (fun x : K => x ^ n) '' localClosedBall K r := by
  ext y
  simp [localPowerImage, localClosedBall, Metric.mem_closedBall, dist_zero_right,
    eq_comm]

/-- The n-th power of a point of B(r) lies in B(r^n). -/
theorem pow_mem_localClosedBall {r : ℝ} {x : K}
    (hx : x ∈ localClosedBall K r) (n : ℕ) :
    x ^ n ∈ localClosedBall K (r ^ n) := by
  rw [mem_localClosedBall, norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg x) (mem_localClosedBall.mp hx) n

/-- The n-fold power region is contained in the ball of radius r^n. -/
theorem localPowerImage_subset_closedBall_pow {r : ℝ} (n : ℕ) :
    localPowerImage K r n ⊆ localClosedBall K (r ^ n) := by
  rintro y ⟨x, hx, rfl⟩
  exact pow_mem_localClosedBall (mem_localClosedBall.mpr hx) n

/-- The scaled n-fold power region f · B(r)^n = {f · x ^ n | x ∈ B(r)}. -/
def localScaledPowerImage (K : Type*) [NormedField K] (f : K) (r : ℝ)
    (n : ℕ) : Set K :=
  {y : K | ∃ x : K, ‖x‖ ≤ r ∧ y = f * x ^ n}

/-- Membership in the scaled power region. -/
theorem mem_localScaledPowerImage {f : K} {r : ℝ} {n : ℕ} {y : K} :
    y ∈ localScaledPowerImage K f r n ↔
      ∃ x : K, ‖x‖ ≤ r ∧ y = f * x ^ n :=
  Iff.rfl

/-- The scaled power region is the image of the ball under x ↦ f · x ^ n. -/
theorem localScaledPowerImage_eq_image (f : K) (r : ℝ) (n : ℕ) :
    localScaledPowerImage K f r n =
      (fun x : K => f * x ^ n) '' localClosedBall K r := by
  ext y
  simp [localScaledPowerImage, localClosedBall, Metric.mem_closedBall,
    dist_zero_right, eq_comm]

/-- Multiplication by 1 does not change the power region. -/
theorem localScaledPowerImage_one (r : ℝ) (n : ℕ) :
    localScaledPowerImage K (1 : K) r n = localPowerImage K r n := by
  ext y
  simp [localScaledPowerImage, localPowerImage, one_mul]

/-- Multiplication of two closed balls lands in the closed ball of the product
radius: the archimedean local analogue of the tensor product of rank-one
objects. -/
theorem mul_mem_localClosedBall {r1 r2 : ℝ} (hr1 : 0 ≤ r1)
    {x y : K} (hx : x ∈ localClosedBall K r1) (hy : y ∈ localClosedBall K r2) :
    x * y ∈ localClosedBall K (r1 * r2) := by
  rw [mem_localClosedBall, norm_mul]
  exact mul_le_mul (mem_localClosedBall.mp hx) (mem_localClosedBall.mp hy)
    (norm_nonneg y) hr1

/-- The scaled containment criterion.  Under radius realization, the scaled
n-th power region f · B(r1)^n is contained in B(r2) if and only if
‖f‖ · r1^n ≤ r2.  The radius r1 must be nonnegative. -/
theorem localScaledPowerImage_subset_closedBall_iff
    (hreal : RadiusRealization K) (f : K) {r1 r2 : ℝ} (hr1 : 0 ≤ r1) (n : ℕ) :
    localScaledPowerImage K f r1 n ⊆ localClosedBall K r2 ↔
      ‖f‖ * r1 ^ n ≤ r2 := by
  constructor
  · intro hsub
    obtain ⟨x, hx⟩ := hreal r1 hr1
    have hy : f * x ^ n ∈ localClosedBall K r2 :=
      hsub ⟨x, le_of_eq hx, rfl⟩
    have hbound : ‖f * x ^ n‖ ≤ r2 := mem_localClosedBall.mp hy
    rwa [norm_mul, norm_pow, hx] at hbound
  · intro hle y hy
    obtain ⟨x, hx, rfl⟩ := hy
    rw [mem_localClosedBall, norm_mul, norm_pow]
    have hpow : ‖x‖ ^ n ≤ r1 ^ n :=
      pow_le_pow_left₀ (norm_nonneg x) hx n
    calc
      ‖f‖ * ‖x‖ ^ n ≤ ‖f‖ * r1 ^ n :=
        mul_le_mul_of_nonneg_left hpow (norm_nonneg f)
      _ ≤ r2 := hle

end RadiusRealization

section UnitCircle

variable [NormedField K]

/-- The norm-one unit circle U = {u : Kˣ | ‖u‖ = 1}, a subgroup of Kˣ. -/
def normOneUnits (K : Type*) [NormedField K] : Subgroup Kˣ where
  carrier := {u : Kˣ | ‖(u : K)‖ = 1}
  one_mem' := by simp
  mul_mem' := by
    intro u v hu hv
    rw [Set.mem_setOf_eq, Units.val_mul, norm_mul, hu, hv, one_mul]
  inv_mem' := by
    intro u hu
    rw [Set.mem_setOf_eq, Units.val_inv_eq_inv_val, norm_inv, hu, inv_one]

/-- Membership in the norm-one unit circle. -/
theorem mem_normOneUnits (u : Kˣ) : u ∈ normOneUnits K ↔ ‖(u : K)‖ = 1 :=
  Iff.rfl

/-- The quotient map Kˣ → Kˣ/U of the multiplicative group by the unit circle. -/
noncomputable def unitNormClassMap (K : Type*) [NormedField K] :
    Kˣ →* Kˣ ⧸ normOneUnits K :=
  QuotientGroup.mk' (normOneUnits K)

/-- The kernel of the quotient map is the norm-one unit circle. -/
theorem unitNormClassMap_ker : (unitNormClassMap K).ker = normOneUnits K :=
  QuotientGroup.ker_mk' (normOneUnits K)

/-- The norm map Kˣ → ℝˣ, whose range is the subgroup of positive units. -/
noncomputable def unitNormHom (K : Type*) [NormedField K] : Kˣ →* ℝˣ where
  toFun u := Units.mk0 ‖(u : K)‖ (ne_of_gt (norm_pos_unit K u))
  map_one' := by
    apply Units.ext
    change ‖((1 : Kˣ) : K)‖ = (1 : ℝ)
    simp
  map_mul' := by
    intro u v
    apply Units.ext
    change ‖(((u * v : Kˣ)) : K)‖ = ‖(u : K)‖ * ‖(v : K)‖
    rw [Units.val_mul, norm_mul]

/-- The kernel of the norm map is exactly the norm-one unit circle. -/
theorem unitNormHom_ker : (unitNormHom K).ker = normOneUnits K := by
  ext u
  rw [MonoidHom.mem_ker, mem_normOneUnits]
  constructor
  · intro h
    have hval := congrArg Units.val h
    simpa [unitNormHom, Units.val_mk0] using hval
  · intro h
    apply Units.ext
    simp [unitNormHom, h]

/-- Under radius realization, the range of the norm map is the subgroup of
positive units of ℝ. -/
theorem unitNormHom_range_eq_posSubgroup (hreal : RadiusRealization K) :
    (unitNormHom K).range = Units.posSubgroup ℝ := by
  ext v
  constructor
  · intro hv
    rw [MonoidHom.mem_range] at hv
    obtain ⟨u, rfl⟩ := hv
    rw [Units.mem_posSubgroup]
    exact norm_pos_unit K u
  · intro hv
    rw [Units.mem_posSubgroup] at hv
    rw [MonoidHom.mem_range]
    obtain ⟨x, hx⟩ := hreal (v : ℝ) (le_of_lt hv)
    have hxne : x ≠ 0 := by
      intro hx0
      rw [hx0, norm_zero] at hx
      exact (ne_of_gt hv) hx.symm
    refine ⟨Units.mk0 x hxne, ?_⟩
    have hmk : unitNormHom K (Units.mk0 x hxne) =
        Units.mk0 ‖x‖ (ne_of_gt (norm_pos_unit K (Units.mk0 x hxne))) := by
      simp [unitNormHom]
    apply Units.ext
    rw [hmk]
    simp [hx]

/-- Two units have the same class in Kˣ/U if and only if they have the same
norm.  This is the representative-level form of the scale dictionary. -/
theorem normClass_mk_eq_iff_norm_eq (u v : Kˣ) :
    QuotientGroup.mk' (normOneUnits K) u = QuotientGroup.mk' (normOneUnits K) v ↔
      ‖(u : K)‖ = ‖(v : K)‖ := by
  change (u : Kˣ ⧸ normOneUnits K) = (v : Kˣ ⧸ normOneUnits K) ↔
    ‖(u : K)‖ = ‖(v : K)‖
  rw [QuotientGroup.eq, mem_normOneUnits, Units.val_mul,
    Units.val_inv_eq_inv_val, norm_mul, norm_inv]
  constructor
  · intro h
    have hu : 0 < ‖(u : K)‖ := norm_pos_unit K u
    have hmul : ‖(u : K)‖ * (‖(u : K)‖⁻¹ * ‖(v : K)‖) = ‖(u : K)‖ * 1 := by
      rw [h]
    rw [mul_one, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt hu), one_mul] at hmul
    exact hmul.symm
  · intro h
    rw [h]
    exact inv_mul_cancel₀ (ne_of_gt (norm_pos_unit K v))

/-- The multiplicative equivalence Kˣ/U ≃* (ℝˣ)⁺ between the quotient by the
norm-one unit circle and the positive units of ℝ, induced by the norm.  This is
the archimedean scale dictionary of Ex3.6: a class [u] corresponds to the
radius ‖u‖. -/
noncomputable def normClassEquivPosUnits (hreal : RadiusRealization K) :
    Kˣ ⧸ normOneUnits K ≃* Units.posSubgroup ℝ :=
  (QuotientGroup.quotientMulEquivOfEq (unitNormHom_ker (K := K)).symm).trans
    ((QuotientGroup.quotientKerEquivRange (unitNormHom K)).trans
      (MulEquiv.subgroupCongr (unitNormHom_range_eq_posSubgroup (K := K) hreal)))

/-- The equivalence is realized by the norm on representatives. -/
theorem normClassEquivPosUnits_mk (hreal : RadiusRealization K) (u : Kˣ) :
    (((normClassEquivPosUnits (K := K) hreal)
        (QuotientGroup.mk' (normOneUnits K) u) :
        Units.posSubgroup ℝ) : ℝˣ) = unitNormHom K u := by
  rfl

/-- The scale class of a unit is the positive unit with value ‖u‖. -/
theorem normClassEquivPosUnits_mk_val (hreal : RadiusRealization K) (u : Kˣ) :
    ((((normClassEquivPosUnits (K := K) hreal)
        (QuotientGroup.mk' (normOneUnits K) u) :
        Units.posSubgroup ℝ) : ℝˣ) : ℝ) = ‖(u : K)‖ := by
  rw [normClassEquivPosUnits_mk]
  simp [unitNormHom, Units.val_mk0]

/-- Under radius realization the scale dictionary is a bijection between Kˣ/U
and the positive radii. -/
theorem normClassEquivPosUnits_bijective (hreal : RadiusRealization K) :
    Function.Bijective (normClassEquivPosUnits (K := K) hreal) :=
  (normClassEquivPosUnits (K := K) hreal).bijective

end UnitCircle

section AbsLogDictionary

variable [NormedField K]

/-- The archimedean local additive character ν(u) = -log ‖u‖, as an additive
homomorphism from the multiplicative group of units (written additively) to ℝ.
This is the archimedean analogue of the finite-place valuation ν_v. -/
noncomputable def absLogAddHom (K : Type*) [NormedField K] : Additive Kˣ →+ ℝ where
  toFun u := -Real.log ‖((u.toMul : Kˣ) : K)‖
  map_zero' := by
    change -Real.log ‖((Additive.toMul (0 : Additive Kˣ) : Kˣ) : K)‖ = 0
    rw [toMul_zero]
    simp
  map_add' := by
    intro u v
    change -Real.log ‖((Additive.toMul (u + v) : Kˣ) : K)‖ =
      -Real.log ‖((Additive.toMul u : Kˣ) : K)‖ +
        -Real.log ‖((Additive.toMul v : Kˣ) : K)‖
    rw [toMul_add, Units.val_mul, norm_mul,
      Real.log_mul (norm_pos_unit K (Additive.toMul u)).ne'
        (norm_pos_unit K (Additive.toMul v)).ne']
    ring

/-- The value of the archimedean additive character on a unit. -/
theorem absLogAddHom_ofMul (u : Kˣ) :
    absLogAddHom K (Additive.ofMul u) = -Real.log ‖(u : K)‖ := by
  change -Real.log ‖((Additive.toMul (Additive.ofMul u) : Kˣ) : K)‖ =
    -Real.log ‖(u : K)‖
  rw [toMul_ofMul]

/-- Consistency with the existing norm-log degree homomorphism of
Foundations.Arithmetic.NormLog: the archimedean character is its negative. -/
theorem absLogAddHom_ofMul_eq_neg_unitNormLogDegree (u : Kˣ) :
    absLogAddHom K (Additive.ofMul u) = -(unitNormLogDegree K u).toAdd := by
  rw [absLogAddHom_ofMul]
  rfl

/-- The kernel of the archimedean additive character is exactly the norm-one
unit circle, under the multiplicative-to-additive identification of Kˣ. -/
theorem absLogAddHom_ofMul_eq_zero_iff (u : Kˣ) :
    absLogAddHom K (Additive.ofMul u) = 0 ↔ u ∈ normOneUnits K := by
  rw [absLogAddHom_ofMul, mem_normOneUnits]
  constructor
  · intro h
    have hlog : Real.log ‖(u : K)‖ = 0 := by
      have := congrArg Neg.neg h
      simpa using this
    have hexp := congrArg Real.exp hlog
    rwa [Real.exp_log (norm_pos_unit K u), Real.exp_zero] at hexp
  · intro h
    rw [h, Real.log_one, neg_zero]

/-- Under radius realization the archimedean additive character is surjective
onto the whole additive real line: every real number is the log-scale of some
unit. -/
theorem absLogAddHom_surjective (hreal : RadiusRealization K) :
    Function.Surjective (absLogAddHom K) := by
  intro y
  obtain ⟨x, hx⟩ := hreal (Real.exp (-y)) (le_of_lt (Real.exp_pos (-y)))
  have hxne : x ≠ 0 := by
    intro hx0
    rw [hx0, norm_zero] at hx
    exact (ne_of_gt (Real.exp_pos (-y))) hx.symm
  refine ⟨Additive.ofMul (Units.mk0 x hxne), ?_⟩
  rw [absLogAddHom_ofMul]
  have hnorm : ‖((Units.mk0 x hxne : Kˣ) : K)‖ = Real.exp (-y) := hx
  rw [hnorm, Real.log_exp]
  ring

/-- The archimedean local log dictionary is the short exact sequence
1 → U → Kˣ → ℝ → 0: the kernel of the additive character is exactly the
norm-one unit circle, and under radius realization the character is onto the
additive real line. -/
theorem archimedeanLocalLog_exact (hreal : RadiusRealization K) :
    (∀ u : Kˣ, absLogAddHom K (Additive.ofMul u) = 0 ↔ u ∈ normOneUnits K) ∧
      Function.Surjective (absLogAddHom K) :=
  ⟨absLogAddHom_ofMul_eq_zero_iff, absLogAddHom_surjective hreal⟩

/-- The archimedean delta of a radius: δ(r) = -log r.  This is the additive
log-scale attached to the multiplicative radius r; it is the archimedean
analogue of the finite-place valuation of a generator. -/
noncomputable def archimedeanDelta (r : ℝ) : ℝ := -Real.log r

/-- The delta of the standard radius 1 vanishes. -/
theorem archimedeanDelta_one : archimedeanDelta 1 = 0 := by
  simp [archimedeanDelta]

/-- Delta is additive in the product of nonzero radii. -/
theorem archimedeanDelta_mul {r1 r2 : ℝ} (h1 : r1 ≠ 0) (h2 : r2 ≠ 0) :
    archimedeanDelta (r1 * r2) = archimedeanDelta r1 + archimedeanDelta r2 := by
  rw [archimedeanDelta, archimedeanDelta, archimedeanDelta, Real.log_mul h1 h2,
    neg_add]

/-- Delta of a reciprocal is the negative of the delta. -/
theorem archimedeanDelta_inv {r : ℝ} :
    archimedeanDelta r⁻¹ = -archimedeanDelta r := by
  rw [archimedeanDelta, archimedeanDelta, Real.log_inv, neg_neg]

/-- The archimedean additive character is the delta of the norm. -/
theorem absLogAddHom_ofMul_eq_archimedeanDelta (u : Kˣ) :
    absLogAddHom K (Additive.ofMul u) = archimedeanDelta ‖(u : K)‖ := by
  rw [absLogAddHom_ofMul, archimedeanDelta]

/-- Real arithmetic behind the logarithmic form of the containment criterion:
for positive reals a, b, c and n : ℕ, a * b^n ≤ c if and only if
-log a + n * (-log b) - (-log c) ≥ 0. -/
theorem mul_pow_le_iff_negLog {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (n : ℕ) :
    a * b ^ n ≤ c ↔ 0 ≤ -Real.log a + (n : ℝ) * (-Real.log b) - -Real.log c := by
  have hlog : Real.log (a * b ^ n) = Real.log a + (n : ℝ) * Real.log b := by
    rw [Real.log_mul ha.ne' (pow_ne_zero n hb.ne'), Real.log_pow]
  constructor
  · intro h
    have h1 : Real.log (a * b ^ n) ≤ Real.log c :=
      Real.log_le_log (mul_pos ha (pow_pos hb n)) h
    rw [hlog] at h1
    linarith
  · intro h
    have h1 : Real.log a + (n : ℝ) * Real.log b ≤ Real.log c := by linarith
    have h2 : Real.log (a * b ^ n) ≤ Real.log c := by rwa [hlog]
    exact (Real.log_le_log_iff (mul_pos ha (pow_pos hb n)) hc).mp h2

/-- The delta form of the scaled containment criterion for units: with
ν(f) = -log ‖f‖ and δ(r) = -log r, we have
f · B(r1)^n ⊆ B(r2) iff ν(f) + n·δ(r1) - δ(r2) ≥ 0. -/
theorem localScaledPowerImage_subset_closedBall_iff_archimedeanDelta
    (hreal : RadiusRealization K) (f : Kˣ) {r1 r2 : ℝ} (hr1 : 0 < r1)
    (hr2 : 0 < r2) (n : ℕ) :
    localScaledPowerImage K (f : K) r1 n ⊆ localClosedBall K r2 ↔
      0 ≤ absLogAddHom K (Additive.ofMul f) + (n : ℝ) * archimedeanDelta r1 -
        archimedeanDelta r2 := by
  rw [localScaledPowerImage_subset_closedBall_iff hreal (f : K) (le_of_lt hr1) n,
    absLogAddHom_ofMul, archimedeanDelta, archimedeanDelta]
  exact mul_pow_le_iff_negLog (norm_pos_unit K f) hr1 hr2 n

/-- The explicit-log form of the same criterion, as stated in the handoff:
f · B(r1)^n ⊆ B(r2) iff -log ‖f‖ + n·(-log r1) - (-log r2) ≥ 0. -/
theorem localScaledPowerImage_subset_closedBall_iff_absLog
    (hreal : RadiusRealization K) (f : Kˣ) {r1 r2 : ℝ} (hr1 : 0 < r1)
    (hr2 : 0 < r2) (n : ℕ) :
    localScaledPowerImage K (f : K) r1 n ⊆ localClosedBall K r2 ↔
      0 ≤ -Real.log ‖(f : K)‖ + (n : ℝ) * (-Real.log r1) - -Real.log r2 :=
  (localScaledPowerImage_subset_closedBall_iff_archimedeanDelta hreal f hr1 hr2
      n).trans (by
    rw [absLogAddHom_ofMul, archimedeanDelta, archimedeanDelta])

/-- At the standard radius one the scaled criterion is independent of the
power n and simply says that f itself lies in the target ball. -/
theorem standardRadius_scaledPowerImage_subset_closedBall_iff
    (hreal : RadiusRealization K) (f : Kˣ) {r2 : ℝ} (n : ℕ) :
    localScaledPowerImage K (f : K) 1 n ⊆ localClosedBall K r2 ↔
      ‖(f : K)‖ ≤ r2 := by
  rw [localScaledPowerImage_subset_closedBall_iff hreal (f : K) zero_le_one n,
    one_pow, mul_one]

end AbsLogDictionary

section NonAdditivity

variable [NormedField K]

/-- A subset of the local field is additively closed if it contains the sum of
any two of its points. -/
def IsAdditivelyClosed (s : Set K) : Prop := ∀ x ∈ s, ∀ y ∈ s, x + y ∈ s

end NonAdditivity

section StandardRadius

variable [NormedField K]

/-- The archimedean "standard object" statement: scaling the closed unit ball by
a nonzero field element f gives the closed ball of radius ‖f‖.  This is the
analogue of the finite-place identity f·O_v at a place. -/
theorem scaledUnitBall_eq_closedBall_norm {f : K} (hf : f ≠ 0) :
    localScaledPowerImage K f 1 1 = localClosedBall K ‖f‖ := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [mem_localClosedBall, norm_mul, pow_one]
    have hle : ‖x‖ ≤ 1 := hx
    calc
      ‖f‖ * ‖x‖ ≤ ‖f‖ * 1 := mul_le_mul_of_nonneg_left hle (norm_nonneg f)
      _ = ‖f‖ := mul_one ‖f‖
  · intro hy
    rw [mem_localClosedBall] at hy
    refine ⟨f⁻¹ * y, ?_, ?_⟩
    · rw [norm_mul, norm_inv, ← div_eq_inv_mul,
        div_le_one (norm_pos_iff.mpr hf)]
      exact hy
    · rw [pow_one]
      simp [← mul_assoc, mul_inv_cancel₀ hf]

/-- The standard radius-one object is fixed by multiplication by 1. -/
theorem localScaledPowerImage_one_one :
    localScaledPowerImage K (1 : K) 1 1 = localClosedBall K 1 := by
  simpa using scaledUnitBall_eq_closedBall_norm (K := K) (f := (1 : K)) one_ne_zero

end StandardRadius

section RealInstantiation

/-- The real normed field realizes every nonnegative radius as a norm. -/
theorem radiusRealization_real : RadiusRealization ℝ := by
  intro r hr
  exact ⟨r, by rw [Real.norm_eq_abs, abs_of_nonneg hr]⟩

/-- The real unit ball contains 1. -/
theorem real_one_mem_closedUnitBall : (1 : ℝ) ∈ localClosedBall ℝ 1 := by
  rw [mem_localClosedBall]
  norm_num

/-- The real unit ball does not contain 2. -/
theorem real_two_notMem_closedUnitBall : (2 : ℝ) ∉ localClosedBall ℝ 1 := by
  rw [mem_localClosedBall, Real.norm_eq_abs]
  norm_num

/-- The real closed unit ball is not additively closed: 1 and 1 lie in it, but
their sum 2 does not.  Hence the archimedean local object is an ordered scale
object, not a ring or module region. -/
theorem real_closedUnitBall_not_additivelyClosed :
    ¬ IsAdditivelyClosed (localClosedBall ℝ 1) := by
  intro h
  have hsum : (1 + 1 : ℝ) ∈ localClosedBall ℝ 1 :=
    h 1 real_one_mem_closedUnitBall 1 real_one_mem_closedUnitBall
  have h12 : (1 : ℝ) + 1 = 2 := by norm_num
  rw [h12] at hsum
  exact real_two_notMem_closedUnitBall hsum

/-- The real local scale dictionary: ℝˣ modulo the norm-one circle {±1} is the
group of positive units of ℝ. -/
noncomputable def real_unitQuotientEquivPosUnits :
    ℝˣ ⧸ normOneUnits ℝ ≃* Units.posSubgroup ℝ :=
  normClassEquivPosUnits (K := ℝ) radiusRealization_real

/-- The concrete real converted containment criterion in delta form. -/
theorem real_scaledPowerImage_subset_closedBall_iff_archimedeanDelta
    (f : ℝˣ) {r1 r2 : ℝ} (hr1 : 0 < r1) (hr2 : 0 < r2) (n : ℕ) :
    localScaledPowerImage ℝ (f : ℝ) r1 n ⊆ localClosedBall ℝ r2 ↔
      0 ≤ absLogAddHom ℝ (Additive.ofMul f) + (n : ℝ) * archimedeanDelta r1 -
        archimedeanDelta r2 :=
  localScaledPowerImage_subset_closedBall_iff_archimedeanDelta
    radiusRealization_real f hr1 hr2 n

/-- The concrete real short exact sequence of the archimedean log dictionary. -/
theorem real_archimedeanLocalLog_exact :
    (∀ u : ℝˣ, absLogAddHom ℝ (Additive.ofMul u) = 0 ↔ u ∈ normOneUnits ℝ) ∧
      Function.Surjective (absLogAddHom ℝ) :=
  archimedeanLocalLog_exact radiusRealization_real

end RealInstantiation

section ComplexInstantiation

/-- The complex normed field realizes every nonnegative radius as a norm. -/
theorem radiusRealization_complex : RadiusRealization ℂ := by
  intro r hr
  exact ⟨(r : ℂ), by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]⟩

/-- The complex unit ball contains 1. -/
theorem complex_one_mem_closedUnitBall : (1 : ℂ) ∈ localClosedBall ℂ 1 := by
  rw [mem_localClosedBall]
  norm_num

/-- The complex unit ball does not contain 2. -/
theorem complex_two_notMem_closedUnitBall : (2 : ℂ) ∉ localClosedBall ℂ 1 := by
  rw [mem_localClosedBall]
  have h : ‖(2 : ℂ)‖ = 2 := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.norm_real]
    norm_num
  rw [h]
  norm_num

/-- The complex closed unit ball is not additively closed: 1 and 1 lie in it,
but their sum 2 does not. -/
theorem complex_closedUnitBall_not_additivelyClosed :
    ¬ IsAdditivelyClosed (localClosedBall ℂ 1) := by
  intro h
  have hsum : (1 + 1 : ℂ) ∈ localClosedBall ℂ 1 :=
    h 1 complex_one_mem_closedUnitBall 1 complex_one_mem_closedUnitBall
  have h12 : (1 : ℂ) + 1 = 2 := by norm_num
  rw [h12] at hsum
  exact complex_two_notMem_closedUnitBall hsum

/-- The complex local scale dictionary: ℂˣ modulo the norm-one unit circle is
the group of positive units of ℝ.  The factor [ℂ : ℝ] enters only later, in the
Haar/degree normalization; it is not part of this local scale dictionary. -/
noncomputable def complex_unitQuotientEquivPosUnits :
    ℂˣ ⧸ normOneUnits ℂ ≃* Units.posSubgroup ℝ :=
  normClassEquivPosUnits (K := ℂ) radiusRealization_complex

/-- The concrete complex converted containment criterion in delta form. -/
theorem complex_scaledPowerImage_subset_closedBall_iff_archimedeanDelta
    (f : ℂˣ) {r1 r2 : ℝ} (hr1 : 0 < r1) (hr2 : 0 < r2) (n : ℕ) :
    localScaledPowerImage ℂ (f : ℂ) r1 n ⊆ localClosedBall ℂ r2 ↔
      0 ≤ absLogAddHom ℂ (Additive.ofMul f) + (n : ℝ) * archimedeanDelta r1 -
        archimedeanDelta r2 :=
  localScaledPowerImage_subset_closedBall_iff_archimedeanDelta
    radiusRealization_complex f hr1 hr2 n

/-- The concrete complex short exact sequence of the archimedean log dictionary. -/
theorem complex_archimedeanLocalLog_exact :
    (∀ u : ℂˣ, absLogAddHom ℂ (Additive.ofMul u) = 0 ↔ u ∈ normOneUnits ℂ) ∧
      Function.Surjective (absLogAddHom ℂ) :=
  archimedeanLocalLog_exact radiusRealization_complex

end ComplexInstantiation

end LeanFormal.IUT
