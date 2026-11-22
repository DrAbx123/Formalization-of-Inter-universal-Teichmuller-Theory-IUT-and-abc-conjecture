import tmp.sheaf.xif.paper.Mzk1B5LocalGlobalProductFormulaActual
import Mathlib.RingTheory.FractionalIdeal.Norm
import Mathlib.RingTheory.FractionalIdeal.Operations
import Mathlib.Tactic

/-! # B5 fractional ideal absNorm formula

For a nonzero fractional ideal I of O_K:

  absNorm I = absNorm(num I) / |norm den I|

and therefore

  log absNorm I =
    log absNorm(num I) - log absNorm(span {den I}).

Combining with the integer ideal product formula gives the num/den count sum.
The direct identification of this difference with FractionalIdeal.count is recorded
as the next bridge (count_well_defined), not assumed.
-/

noncomputable section
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1B5FractionalAbsNormFormulaActual

open IsDedekindDomain

variable (K : Type) [Field K] [NumberField K]

/-- absNorm of a fractional ideal as the num/den quotient. -/
theorem absNorm_eq_num_div_den (I : FractionalIdeal
    (nonZeroDivisors (NumberField.RingOfIntegers K)) K) :
    (FractionalIdeal.absNorm I : Real) =
      (Ideal.absNorm I.num : Real) /
        (|(Algebra.norm Int (I.den : NumberField.RingOfIntegers K))| : Real) := by
  rw [FractionalIdeal.absNorm_eq]
  push_cast
  rfl

/-- Denominator appears as the integer ideal span {den}. -/
theorem absNorm_span_den_eq (I : FractionalIdeal
    (nonZeroDivisors (NumberField.RingOfIntegers K)) K) :
    (Ideal.absNorm (Ideal.span {(I.den : NumberField.RingOfIntegers K)}) : Real) =
      |(Algebra.norm Int (I.den : NumberField.RingOfIntegers K))| := by
  rw [Ideal.absNorm_span_singleton]
  norm_num [Int.natCast_natAbs]

/-- Fractional ideal log-norm as the difference of num and denominator log-norms. -/
theorem log_absNorm_fractional_eq_num_sub_den
    (I : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K)
    (hI : I ≠ 0) :
    Real.log (FractionalIdeal.absNorm I : Real) =
      Real.log (Ideal.absNorm I.num : Real) -
        Real.log (Ideal.absNorm
          (Ideal.span {(I.den : NumberField.RingOfIntegers K)}) : Real) := by
  have hnum_ne : I.num ≠ 0 := (FractionalIdeal.num_eq_zero_iff).not.mpr hI
  have hden_ne : (I.den : NumberField.RingOfIntegers K) ≠ 0 :=
    nonZeroDivisors.ne_zero I.den.property
  have hdenSpan : Ideal.span {(I.den : NumberField.RingOfIntegers K)} ≠ 0 := by
    simpa [Ideal.span_singleton_eq_bot] using hden_ne
  have hnum_pos : (0 : Real) < (Ideal.absNorm I.num : Real) := by
    have hne : Ideal.absNorm I.num ≠ 0 := by
      rw [Ideal.absNorm_ne_zero_iff]
      exact Ideal.finiteQuotientOfFreeOfNeBot _ hnum_ne
    exact_mod_cast Nat.pos_of_ne_zero hne
  have hden_pos : (0 : Real) <
      (Ideal.absNorm (Ideal.span {(I.den : NumberField.RingOfIntegers K)}) : Real) := by
    have hne : Ideal.absNorm (Ideal.span
        {(I.den : NumberField.RingOfIntegers K)}) ≠ 0 := by
      rw [Ideal.absNorm_ne_zero_iff]
      exact Ideal.finiteQuotientOfFreeOfNeBot _ hdenSpan
    exact_mod_cast Nat.pos_of_ne_zero hne
  rw [absNorm_eq_num_div_den K I, ← Int.cast_abs, ← absNorm_span_den_eq K I,
    Real.log_div hnum_pos.ne' hden_pos.ne']

/-- Fractional version: log-norm is the difference of the integer count sums. -/
theorem log_absNorm_fractional_eq_sum_diff
    (I : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K)
    (hI : I ≠ 0) :
    Real.log (FractionalIdeal.absNorm I : Real) =
      (∑ᶠ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
        ((Associates.mk v.asIdeal).count (Associates.mk I.num).factors : Real) *
          Real.log (Ideal.absNorm v.asIdeal : Real)) -
      (∑ᶠ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
        ((Associates.mk v.asIdeal).count
          (Associates.mk (Ideal.span {(I.den : NumberField.RingOfIntegers K)})).factors : Real) *
          Real.log (Ideal.absNorm v.asIdeal : Real)) := by
  have hnum_ne : I.num ≠ 0 := (FractionalIdeal.num_eq_zero_iff).not.mpr hI
  have hden_ne : (I.den : NumberField.RingOfIntegers K) ≠ 0 := nonZeroDivisors.ne_zero I.den.property
  have hdenSpan : Ideal.span {(I.den : NumberField.RingOfIntegers K)} ≠ 0 := by
    simpa [Ideal.span_singleton_eq_bot] using hden_ne
  rw [log_absNorm_fractional_eq_num_sub_den K I hI,
    Mzk1B5LocalGlobalProductFormulaActual.log_absNorm_eq_sum_count_mul_log K I.num hnum_ne,
    Mzk1B5LocalGlobalProductFormulaActual.log_absNorm_eq_sum_count_mul_log K
      (Ideal.span {(I.den : NumberField.RingOfIntegers K)}) hdenSpan]

#check absNorm_eq_num_div_den
#check absNorm_span_den_eq
#check log_absNorm_fractional_eq_num_sub_den
#check log_absNorm_fractional_eq_sum_diff
end LeanFormal.IUT.XiFPaper.Mzk1B5FractionalAbsNormFormulaActual
end
