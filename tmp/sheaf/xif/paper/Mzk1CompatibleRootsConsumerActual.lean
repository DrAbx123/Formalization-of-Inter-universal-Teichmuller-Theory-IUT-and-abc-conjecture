/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.IUTII.Kummer.CompatibleRoots

/-! # Compatible root systems: consumer laws for roots maps -/

namespace LeanFormal.IUT

namespace CompatibleRootSystem

variable {M : Type*} [CommGroup M] {value : M}

/-- The rational-zero root is the unit. -/
theorem roots_zero (R : CompatibleRootSystem M value) :
    (R.roots 0).toMul = 1 := by
  simp

/-- The root map is additive on rational exponents. -/
theorem roots_add (R : CompatibleRootSystem M value) (q1 q2 : ℚ) :
    (R.roots (q1 + q2)).toMul = (R.roots q1).toMul * (R.roots q2).toMul := by
  rw [map_add]
  simp

/-- The negative rational root is the inverse unit. -/
theorem roots_neg (R : CompatibleRootSystem M value) (q : ℚ) :
    (R.roots (-q)).toMul = ((R.roots q).toMul)⁻¹ := by
  rw [map_neg]
  simp

/-- Natural multiples of the rational exponent give powers of the root. -/
theorem roots_nsmul (R : CompatibleRootSystem M value) (n : ℕ) (q : ℚ) :
    (R.roots (n • q)).toMul = ((R.roots q).toMul) ^ n := by
  rw [R.roots.map_nsmul]
  simp

/-- Two compatible root systems differ by a root of unity of the denominator. -/
theorem quotient_pow_den_unit (first second : CompatibleRootSystem M value) (q : ℚ) :
    ((second.roots q).toMul / (first.roots q).toMul) ^ q.den = 1 :=
  quotient_pow_den first second q

end CompatibleRootSystem

end LeanFormal.IUT
