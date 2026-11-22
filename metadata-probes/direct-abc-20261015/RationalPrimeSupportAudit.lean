/-
  Public-API and axiom audit probe for the RationalPrimeSupport package.

  Compiled with `lake env lean` against the project libraries.  It queries only
  public names (`#check`) and reports the axiom dependencies (`#print axioms`,
  which is the transitive closure of axioms used by each declaration).  It does
  not restate or re-prove the package and does not inspect proof bodies.
-/
import LeanFormal.IUT.ABCBridge.Arithmetic.RationalPrimeSupport
import Mathlib.Tactic

open LeanFormal.IUT

/-! ## Accepted consumer API (exact binders) -/

#check @IsABCTriple
#check @abcRationalPoint
#check @abcRationalPoint_num
#check @abcRationalPoint_den
#check @abcRationalPoint_num_natAbs
#check @abcRationalPoint_den_sub_num
#check @abcRationalPoint_mulHeight₁
#check @abcRationalPoint_logHeight₁
#check @abcRationalPoint_ne_zero
#check @abcRationalPoint_ne_one
#check @isABCTriple_iff_positivePrimitiveAdditiveTriple
#check @prime_dvd_abc_iff_prime_dvd_point_coordinates

/-! ## New public API of this package -/

#check @arithmeticPrimeSupport
#check @arithmeticWeight
#check @natRadical_cast_pos
#check @natRadical_cast_log_eq_sum_primeFactors
#check @arithmeticPrimeSupport_abcRationalPoint
#check @arithmeticWeight_abcRationalPoint

/-! ## Interface test: the accepted predicate really is the explicit conjunction

`IsABCTriple` was not read from source; these examples confirm through the
compiler that it unfolds to positivity of `a`, `b` plus additivity and
coprimality, from which positivity of `c` and non-vanishing of `a*b*c` follow. -/

example {a b c : ℕ} (h : IsABCTriple a b c) : 0 < a := by
  obtain ⟨ha, hb, hsum, hcop⟩ := h
  exact ha

example {a b c : ℕ} (h : IsABCTriple a b c) : a * b * c ≠ 0 := by
  obtain ⟨ha, hb, hsum, hcop⟩ := h
  have ha0 : a ≠ 0 := by omega
  have hb0 : b ≠ 0 := by omega
  have hc0 : c ≠ 0 := by omega
  exact Nat.mul_ne_zero (Nat.mul_ne_zero ha0 hb0) hc0

/-! ## Axiom reports (transitive axiom closure per declaration) -/

#print axioms LeanFormal.IUT.natRadical_cast_pos
#print axioms LeanFormal.IUT.natRadical_cast_log_eq_sum_primeFactors
#print axioms LeanFormal.IUT.arithmeticPrimeSupport_abcRationalPoint
#print axioms LeanFormal.IUT.arithmeticWeight_abcRationalPoint
