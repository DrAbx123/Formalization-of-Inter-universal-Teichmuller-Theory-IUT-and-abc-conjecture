/-
Algebraic cover lemmas for the reverse polynomial `hRev` used in the `hPoly` construction.

`hRev h = ∑ i ∈ h.support, C (h.coeff i) * X ^ (h.natDegree - i)` is Mathlib's
`Polynomial.reverse h`.  Hence its constant coefficient is `h.leadingCoeff`, the ideal
`(X, hRev h)` is the unit ideal, and the lambda chart is covered by `D(X)` and `D(hRev h)`.
-/
import tmp.sheaf.xif.paper.Mzk1G1PsiHPolyActual
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic -- or OpenImmersion / AffineScheme as needed
import Mathlib.Tactic

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Polynomial

namespace LeanFormal.IUT.XiFPaper.Mzk1G1PsiHPolyCoverAlgebraActual

open LeanFormal.IUT.XiFPaper.Mzk1G1PsiHPolyActual

variable (h : Polynomial ℚ)

/-- hRev agrees with Polynomial.reverse for nonzero h. -/
theorem hRev_eq_reverse (hh : h ≠ 0) : hRev h = h.reverse := by
  have hlead : h.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hh
  -- `h` is the sum of its monomials `C (h.coeff i) * X ^ i`, and reversing exponents
  -- `i ↦ h.natDegree - i` on the support is exactly `reflect h.natDegree`.
  have hsum : h = ∑ i ∈ h.support, Polynomial.C (h.coeff i) * Polynomial.X ^ i :=
    (Polynomial.sum_C_mul_X_pow_eq h).symm
  have hrefl : ∀ (N : ℕ) (s : Finset ℕ) (c : ℕ → ℚ),
      Polynomial.reflect N (∑ i ∈ s, Polynomial.C (c i) * Polynomial.X ^ i) =
        ∑ i ∈ s, Polynomial.C (c i) * Polynomial.X ^ (Polynomial.revAt N i) := by
    intro N s c
    induction s using Finset.induction with
    | empty => simp
    | insert a s ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha, Polynomial.reflect_add, ih,
          Polynomial.reflect_C_mul_X_pow]
  calc
    hRev h = ∑ i ∈ h.support, Polynomial.C (h.coeff i) *
        Polynomial.X ^ (Polynomial.revAt h.natDegree i) := by
      rw [hRev]
      refine Finset.sum_congr rfl ?_
      intro i hi
      rw [Polynomial.revAt_le (Polynomial.le_natDegree_of_mem_supp i hi)]
    _ = Polynomial.reflect h.natDegree
          (∑ i ∈ h.support, Polynomial.C (h.coeff i) * Polynomial.X ^ i) :=
      (hrefl h.natDegree h.support h.coeff).symm
    _ = Polynomial.reflect h.natDegree h := by rw [← hsum]
    _ = h.reverse := rfl

/-- The constant coefficient of hRev is leadingCoeff h. -/
theorem hRev_coeff_zero : (hRev h).coeff 0 = h.leadingCoeff := by
  rcases eq_or_ne h 0 with rfl | hh
  · simp [hRev]
  · rw [hRev_eq_reverse h hh, Polynomial.coeff_zero_reverse]

/-- X and hRev generate the unit ideal. -/
theorem span_X_hRev_eq_top (hh : h ≠ 0) : Ideal.span {Polynomial.X, hRev h} = ⊤ := by
  -- `hRev h - C (leadingCoeff h)` is divisible by `X`.
  have hcoeff : (hRev h).coeff 0 = h.leadingCoeff := hRev_coeff_zero h
  have hxdvd : Polynomial.X ∣ hRev h - Polynomial.C (h.leadingCoeff) := by
    rw [Polynomial.X_dvd_iff, Polynomial.coeff_sub, hcoeff, Polynomial.coeff_C_zero, sub_self]
  obtain ⟨g, hg⟩ := hxdvd
  -- Thus `C (leadingCoeff h) = hRev h - X * g` lies in the ideal, and is inverted by
  -- `C (leadingCoeff h)⁻¹`, so that `1` is a linear combination of `X` and `hRev h`.
  rw [Ideal.eq_top_iff_one, Ideal.mem_span_pair]
  refine ⟨-(Polynomial.C (h.leadingCoeff)⁻¹ * g), Polynomial.C (h.leadingCoeff)⁻¹, ?_⟩
  have hlead : h.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hh
  have hCa : Polynomial.C (h.leadingCoeff)⁻¹ * Polynomial.C (h.leadingCoeff) = 1 := by
    rw [← Polynomial.C_mul, inv_mul_cancel₀ hlead, Polynomial.C_1]
  have hrev : hRev h = Polynomial.C (h.leadingCoeff) + Polynomial.X * g := by
    rw [← hg]
    ring
  calc
    -(Polynomial.C (h.leadingCoeff)⁻¹ * g) * Polynomial.X +
        Polynomial.C (h.leadingCoeff)⁻¹ * hRev h
        = -(Polynomial.C (h.leadingCoeff)⁻¹ * g) * Polynomial.X +
            Polynomial.C (h.leadingCoeff)⁻¹ *
              (Polynomial.C (h.leadingCoeff) + Polynomial.X * g) := by
          rw [hrev]
      _ = 1 := by
          rw [mul_add, hCa]
          ring

/-- The lambda chart is covered by D(X) and D(hRev). -/
theorem basicOpen_X_sup_basicOpen_hRev (hh : h ≠ 0) :
    PrimeSpectrum.basicOpen (Polynomial.X : Polynomial ℚ) ⊔
      PrimeSpectrum.basicOpen (hRev h) = ⊤ := by
  have hspan := span_X_hRev_eq_top h hh
  -- Package the two generators as a family over `Bool`.
  have hrange : Set.range (fun b : Bool => bif b then (Polynomial.X : Polynomial ℚ) else hRev h)
      = {Polynomial.X, hRev h} := by
    ext x
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨b, rfl⟩
      cases b <;> simp
    · rintro (rfl | rfl)
      · exact ⟨true, by simp⟩
      · exact ⟨false, by simp⟩
  have hspan' : Ideal.span (Set.range (fun b : Bool =>
      bif b then (Polynomial.X : Polynomial ℚ) else hRev h)) = ⊤ := by
    rw [hrange]
    exact hspan
  have key := (PrimeSpectrum.iSup_basicOpen_eq_top_iff (f := fun b : Bool =>
    bif b then (Polynomial.X : Polynomial ℚ) else hRev h)).mpr hspan'
  rw [iSup_bool_eq] at key
  simpa using key

#print axioms hRev_eq_reverse
#print axioms hRev_coeff_zero
#print axioms span_X_hRev_eq_top
#print axioms basicOpen_X_sup_basicOpen_hRev

end LeanFormal.IUT.XiFPaper.Mzk1G1PsiHPolyCoverAlgebraActual

-- t

-- t