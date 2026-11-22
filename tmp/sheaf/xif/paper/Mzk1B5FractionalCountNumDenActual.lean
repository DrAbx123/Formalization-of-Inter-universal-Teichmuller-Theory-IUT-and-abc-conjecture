import tmp.sheaf.xif.paper.Mzk1B5FractionalAbsNormFormulaActual
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.FractionalIdeal.Inverse
import Mathlib.Tactic

/-! # B5 fractional count = num-count - den-count

Uses FractionalIdeal.den_mul_self_eq_num' and FractionalIdeal.count_well_defined
to identify the fractional ideal count with the difference of the integer counts
of num and span {den}.
-/

noncomputable section
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1B5FractionalCountNumDenActual

open IsDedekindDomain

variable (K : Type) [Field K] [NumberField K]

/-- Fractional ideal count is the integer count of num minus that of span {den}. -/
theorem count_eq_count_num_sub_count_den
    (I : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K)
    (hI : I ≠ 0)
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    FractionalIdeal.count K v I =
      ((Associates.mk v.asIdeal).count (Associates.mk I.num).factors : Int) -
      ((Associates.mk v.asIdeal).count
        (Associates.mk (Ideal.span {(I.den : NumberField.RingOfIntegers K)})).factors : Int) := by
  classical
  let R := NumberField.RingOfIntegers K
  let a : R := (I.den : R)
  have ha_ne : a ≠ 0 := nonZeroDivisors.ne_zero I.den.property
  have hspan_ne : FractionalIdeal.spanSingleton (nonZeroDivisors R)
      (algebraMap R K a) ≠ 0 := by
    rw [FractionalIdeal.spanSingleton_ne_zero_iff]
    exact (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr ha_ne
  have hden_eq : FractionalIdeal.spanSingleton (nonZeroDivisors R) (algebraMap R K a) * I =
      (I.num : FractionalIdeal (nonZeroDivisors R) K) :=
    FractionalIdeal.den_mul_self_eq_num' (S := nonZeroDivisors R) (P := K) I
  have h_aJ : I =
      FractionalIdeal.spanSingleton (nonZeroDivisors R) ((algebraMap R K a)⁻¹) *
        ((I.num : FractionalIdeal (nonZeroDivisors R) K)) := by
    calc
      I = (1 : FractionalIdeal (nonZeroDivisors R) K) * I := by rw [one_mul]
      _ = (FractionalIdeal.spanSingleton (nonZeroDivisors R) (algebraMap R K a))⁻¹ *
            FractionalIdeal.spanSingleton (nonZeroDivisors R) (algebraMap R K a) * I := by
        rw [inv_mul_cancel₀ hspan_ne, one_mul]
      _ = (FractionalIdeal.spanSingleton (nonZeroDivisors R) (algebraMap R K a))⁻¹ *
            (FractionalIdeal.spanSingleton (nonZeroDivisors R) (algebraMap R K a) * I) := by
        rw [mul_assoc]
      _ = FractionalIdeal.spanSingleton (nonZeroDivisors R) ((algebraMap R K a)⁻¹) *
            (I.num : FractionalIdeal (nonZeroDivisors R) K) := by
        rw [FractionalIdeal.spanSingleton_inv, hden_eq]
  have hcount := FractionalIdeal.count_well_defined (K := K) (v := v) hI
    (a := a) (J := I.num) (by
      simpa [FractionalIdeal.spanSingleton, a] using h_aJ)
  simpa [a] using hcount

#check count_eq_count_num_sub_count_den
end LeanFormal.IUT.XiFPaper.Mzk1B5FractionalCountNumDenActual
end
