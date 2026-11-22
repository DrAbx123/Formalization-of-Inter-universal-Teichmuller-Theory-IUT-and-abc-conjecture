import LeanFormal.IUT.ABCBridge.Geometry.FreySplitMultiplicativeReduction
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.FieldTheory.KummerPolynomial

/-!
# Quadratic residue-field extensions splitting the Frey tangent quadratic

For an odd prime `p` of multiplicative reduction of the integral ABC Frey
equation, the split-multiplicative reduction predicate of Mathlib uses the
literal polynomial
`C c₄ * X ^ 2 + C (a₁ * c₄) * X - C (54 * b₆ - 3 * b₂ * b₄ + a₂ * c₄)`
over the residue field.  For the Frey equation this is
`freyMultiplicativeSplittingPolynomial`, and on each of the three support
cases `p ∣ a`, `p ∣ b`, `p ∣ c` it equals `C (16 * d ^ 2) * (X ^ 2 - C d)`
for the residue `d` of `b`, `-a`, `a` respectively, as established in
`FreySplitMultiplicativeReduction`.

This file supplies the missing unconditional construction: for any field `K`
and any `d : K`, the quotient `K[X] / (X ^ 2 - d)` (`quadraticRootExtension`)
contains a square root of `d`; when `d` is not a square in `K`, this quotient
is a genuine field of degree exactly two over `K`.  Consequently the actual
Frey splitting polynomial splits over a degree-`≤ 2` extension of the actual
residue field `FreyResidueField p` with two distinct tangent slopes, with no
square-root hypothesis in the residue field.

## Main results

* `quadraticRootExtension_root_sq` : the class of `X` squares to `d`;
* `irreducible_X_sq_sub_C_of_no_squareRoot` and
  `quadraticRootExtension_isField` : the quotient is a genuine field exactly
  off the square case;
* `quadraticRootExtension_finrank` : the quotient is two-dimensional over `K`;
* `exists_squareRoot_extension` and `squareRoot_or_quadraticRootExtension` :
  the dichotomy "square root in the base field, or a genuine quadratic
  extension";
* `exists_extension_splitting_scaledQuadratic` : the scaled quadratic
  `C u * (X ^ 2 - C d)` splits over the constructed extension into
  `C (algebraMap u) * (X - C r) * (X + C r)` with distinct tangent slopes;
* `freyResidue_exists_quadraticSplittingExtension_of_dvd_left` (also
  `_of_dvd_right`, `_of_dvd_sum`) : the three prime-support cases for the
  actual Frey splitting polynomial over the actual residue field.

## Scope

All statements concern the residue-field side only.  No Tate parameter, no
lift of a residue extension to a valued field, and no uniqueness of the
extension is asserted.  The equivalence over `ℤ_[p]` with
`HasSplitMultiplicativeReduction` remains the pair of implications in
`freyPadicCurve_hasSplitMultiplicativeReduction_iff_of_dvd_left` and its
companions in `FreySplitMultiplicativeReduction`.
-/

noncomputable section

namespace LeanFormal.IUT

open Polynomial

universe v

/-- The quadratic residue extension `K[X] / (X ^ 2 - d)`: the class of `X` is a
square root of `d`.  It is a field exactly when `d` is not a square in `K`
(`quadraticRootExtension_isField`), and it is two-dimensional over `K` in all
cases (`quadraticRootExtension_finrank`). -/
abbrev quadraticRootExtension (K : Type*) [Field K] (d : K) : Type _ :=
  AdjoinRoot (X ^ 2 - C d : K[X])

/-- The canonical square root of `d` in `K[X] / (X ^ 2 - d)`. -/
theorem quadraticRootExtension_root_sq {K : Type*} [Field K] (d : K) :
    (AdjoinRoot.root (X ^ 2 - C d : K[X])) ^ 2 =
      algebraMap K (quadraticRootExtension K d) d := by
  have hroot := AdjoinRoot.eval₂_root (X ^ 2 - C d : K[X])
  simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C] at hroot
  rw [AdjoinRoot.algebraMap_eq]
  exact sub_eq_zero.mp hroot

/-- The quadratic `X ^ 2 - d` is irreducible over a field when `d` is not a
square in that field. -/
theorem irreducible_X_sq_sub_C_of_no_squareRoot {K : Type*} [Field K] {d : K}
    (h : ∀ r : K, r ^ 2 ≠ d) : Irreducible (X ^ 2 - C d : K[X]) :=
  (X_pow_sub_C_irreducible_iff_of_prime (a := d) Nat.prime_two).mpr h

/-- The quotient `K[X] / (X ^ 2 - d)` is a genuine field when `d` is not a
square in `K`. -/
@[implicit_reducible] def quadraticRootExtension_isField {K : Type*} [Field K] {d : K}
    (h : ∀ r : K, r ^ 2 ≠ d) : Field (quadraticRootExtension K d) := by
  haveI : Fact (Irreducible (X ^ 2 - C d : K[X])) :=
    ⟨irreducible_X_sq_sub_C_of_no_squareRoot h⟩
  infer_instance

/-- The quotient `K[X] / (X ^ 2 - d)` is two-dimensional over `K`, whether or
not `d` is a square. -/
theorem quadraticRootExtension_finrank {K : Type*} [Field K] (d : K) :
    Module.finrank K (quadraticRootExtension K d) = 2 := by
  have hf : (X ^ 2 - C d : K[X]) ≠ 0 :=
    (monic_X_pow_sub_C d (by norm_num)).ne_zero
  rw [PowerBasis.finrank (AdjoinRoot.powerBasis hf),
    AdjoinRoot.powerBasis_dim hf, natDegree_X_pow_sub_C]

/-- The quotient `K[X] / (X ^ 2 - d)` is finite-dimensional over `K`. -/
theorem quadraticRootExtension_finiteDimensional {K : Type*} [Field K] (d : K) :
    FiniteDimensional K (quadraticRootExtension K d) := by
  have hf : (X ^ 2 - C d : K[X]) ≠ 0 :=
    (monic_X_pow_sub_C d (by norm_num)).ne_zero
  exact Module.Finite.of_basis (AdjoinRoot.powerBasis hf).basis

/-- Every element of a field has a square root in some extension of degree at
most two: the base field itself when the square root already exists, and the
quadratic quotient `K[X] / (X ^ 2 - d)` otherwise. -/
theorem exists_squareRoot_extension (K : Type v) [Field K] (d : K) :
    ∃ (L : Type v) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L),
      Module.finrank K L ≤ 2 ∧ ∃ r : L, r ^ 2 = algebraMap K L d := by
  by_cases h : ∃ r : K, r ^ 2 = d
  · obtain ⟨r, hr⟩ := h
    refine ⟨K, ‹Field K›, Algebra.id K, inferInstance, ?_, r, ?_⟩
    · rw [Module.finrank_self]
      norm_num
    · rw [hr, Algebra.algebraMap_self_apply]
  · refine ⟨quadraticRootExtension K d,
      quadraticRootExtension_isField fun r hr => h ⟨r, hr⟩,
      AdjoinRoot.instAlgebra (X ^ 2 - C d : K[X]), quadraticRootExtension_finiteDimensional d,
      le_of_eq (quadraticRootExtension_finrank d),
      AdjoinRoot.root (X ^ 2 - C d : K[X]), quadraticRootExtension_root_sq d⟩

/-- Sharp dichotomy: either `d` has a square root in `K`, or `K[X] / (X ^ 2 - d)`
is a genuine field extension of degree exactly two containing one. -/
theorem squareRoot_or_quadraticRootExtension (K : Type v) [Field K] (d : K) :
    (∃ r : K, r ^ 2 = d) ∨
      ∃ (L : Type v) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L),
        Module.finrank K L = 2 ∧ ∃ r : L, r ^ 2 = algebraMap K L d := by
  by_cases h : ∃ r : K, r ^ 2 = d
  · exact Or.inl h
  · exact Or.inr ⟨quadraticRootExtension K d,
      quadraticRootExtension_isField fun r hr => h ⟨r, hr⟩,
      AdjoinRoot.instAlgebra (X ^ 2 - C d : K[X]), quadraticRootExtension_finiteDimensional d,
      quadraticRootExtension_finrank d,
      AdjoinRoot.root (X ^ 2 - C d : K[X]), quadraticRootExtension_root_sq d⟩

/-- The scaled quadratic `C u * (X ^ 2 - C d)` with `d ≠ 0` in odd
characteristic splits over a constructed degree-`≤ 2` extension into the two
distinct tangent factors `X - r` and `X + r`, where `r ^ 2 = algebraMap K L d`.
No square root of `d` in `K` is assumed. -/
theorem exists_extension_splitting_scaledQuadratic {K : Type v} [Field K]
    (htwo : (2 : K) ≠ 0) (u d : K) (hd : d ≠ 0) :
    ∃ (L : Type v) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L),
      Module.finrank K L ≤ 2 ∧
        ∃ r : L, r ^ 2 = algebraMap K L d ∧
          (C u * (X ^ 2 - C d) : K[X]).map (algebraMap K L) =
              C (algebraMap K L u) * (X - C r) * (X + C r) ∧
          ((C u * (X ^ 2 - C d) : K[X]).map (algebraMap K L)).Splits ∧ r ≠ -r := by
  obtain ⟨L, hF, hA, hD, hle, r, hr⟩ := exists_squareRoot_extension K d
  have hsplit := frey_scaled_quadratic_map_splits_with_distinct_slopes
    (algebraMap K L) htwo u d hd r hr
  exact ⟨L, hF, hA, hD, hle, r, hr, hsplit.1, hsplit.2.1, hsplit.2.2⟩

/-- First prime-support case `p ∣ a`: the actual Frey splitting polynomial,
whose tangent parameter is the residue of `b`, splits over a constructed
degree-`≤ 2` extension of the actual residue field, with two distinct tangent
slopes.  No square root of the parameter in the residue field is assumed. -/
theorem freyResidue_exists_quadraticSplittingExtension_of_dvd_left
    {p a b c : ℕ} [Fact p.Prime] (h : IsABCTriple a b c) (hp_two : p ≠ 2)
    (ha : p ∣ a) :
    ∃ (L : Type) (_ : Field L) (_ : Algebra (FreyResidueField p) L)
      (_ : FiniteDimensional (FreyResidueField p) L),
      Module.finrank (FreyResidueField p) L ≤ 2 ∧
        ∃ r : L,
          r ^ 2 = algebraMap (FreyResidueField p) L (b : FreyResidueField p) ∧
          ((freyMultiplicativeSplittingPolynomial (a : FreyResidueField p)
              (b : FreyResidueField p)).map
            (algebraMap (FreyResidueField p) L)).Splits ∧
          r ≠ -r := by
  obtain ⟨hb, _hc⟩ := freyResidue_units_of_dvd_left h hp_two ha
  have hazero : (a : FreyResidueField p) = 0 :=
    (freyResidue_natCast_eq_zero_iff p a).mpr ha
  obtain ⟨L, hF, hA, hD, hle, r, hr, _hfac, hsplit, hne⟩ :=
    exists_extension_splitting_scaledQuadratic (K := FreyResidueField p)
      (freyResidue_two_ne_zero hp_two) (16 * (b : FreyResidueField p) ^ 2)
      (b : FreyResidueField p)
      hb
  refine ⟨L, hF, hA, hD, hle, r, hr, ?_, hne⟩
  rwa [hazero, freyMultiplicativeSplittingPolynomial_zero_left]

/-- Second prime-support case `p ∣ b`: the tangent parameter is the residue of
`-a`.  Same unconditional degree-`≤ 2` extension statement. -/
theorem freyResidue_exists_quadraticSplittingExtension_of_dvd_right
    {p a b c : ℕ} [Fact p.Prime] (h : IsABCTriple a b c) (hp_two : p ≠ 2)
    (hb : p ∣ b) :
    ∃ (L : Type) (_ : Field L) (_ : Algebra (FreyResidueField p) L)
      (_ : FiniteDimensional (FreyResidueField p) L),
      Module.finrank (FreyResidueField p) L ≤ 2 ∧
        ∃ r : L,
          r ^ 2 = algebraMap (FreyResidueField p) L (-(a : FreyResidueField p)) ∧
          ((freyMultiplicativeSplittingPolynomial (a : FreyResidueField p)
              (b : FreyResidueField p)).map
            (algebraMap (FreyResidueField p) L)).Splits ∧
          r ≠ -r := by
  obtain ⟨hanonzero, _hc⟩ := freyResidue_units_of_dvd_right h hp_two hb
  have hbzero : (b : FreyResidueField p) = 0 :=
    (freyResidue_natCast_eq_zero_iff p b).mpr hb
  obtain ⟨L, hF, hA, hD, hle, r, hr, _hfac, hsplit, hne⟩ :=
    exists_extension_splitting_scaledQuadratic (K := FreyResidueField p)
      (freyResidue_two_ne_zero hp_two) (16 * (a : FreyResidueField p) ^ 2)
      (-(a : FreyResidueField p)) (neg_ne_zero.mpr hanonzero)
  refine ⟨L, hF, hA, hD, hle, r, hr, ?_, hne⟩
  rwa [hbzero, freyMultiplicativeSplittingPolynomial_zero_right]

/-- Third prime-support case `p ∣ c`: the residues satisfy `b = -a`, and after
translating the double root the tangent parameter is the residue of `a`.  Same
unconditional degree-`≤ 2` extension statement. -/
theorem freyResidue_exists_quadraticSplittingExtension_of_dvd_sum
    {p a b c : ℕ} [Fact p.Prime] (h : IsABCTriple a b c) (hp_two : p ≠ 2)
    (hc : p ∣ c) :
    ∃ (L : Type) (_ : Field L) (_ : Algebra (FreyResidueField p) L)
      (_ : FiniteDimensional (FreyResidueField p) L),
      Module.finrank (FreyResidueField p) L ≤ 2 ∧
        ∃ r : L,
          r ^ 2 = algebraMap (FreyResidueField p) L (a : FreyResidueField p) ∧
          ((freyMultiplicativeSplittingPolynomial (a : FreyResidueField p)
              (b : FreyResidueField p)).map
            (algebraMap (FreyResidueField p) L)).Splits ∧
          r ≠ -r := by
  obtain ⟨hneg, hanonzero, _⟩ := freyResidue_units_of_dvd_sum h hp_two hc
  obtain ⟨L, hF, hA, hD, hle, r, hr, _hfac, hsplit, hne⟩ :=
    exists_extension_splitting_scaledQuadratic (K := FreyResidueField p)
      (freyResidue_two_ne_zero hp_two) (16 * (a : FreyResidueField p) ^ 2)
      (a : FreyResidueField p) hanonzero
  refine ⟨L, hF, hA, hD, hle, r, hr, ?_, hne⟩
  rwa [hneg, freyMultiplicativeSplittingPolynomial_neg_right]

end LeanFormal.IUT
