import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-! # B5 local-global product formula for ideal norms

For a nonzero ideal I of the integer ring O_K of a number field K:

  absNorm I = ∏ᶠ v, absNorm (v^{count_v I})

and therefore

  log (absNorm I) = Σᶠ v, count_v(I) * log (absNorm v),

where count_v(I) is Associates count in the Dedekind factorization.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1B5LocalGlobalProductFormulaActual

open IsDedekindDomain

variable (K : Type) [Field K] [NumberField K]

/-- Multiplicative absNorm as a monoid hom into Real. -/
noncomputable def absNormReal :
    Ideal (NumberField.RingOfIntegers K) →* Real where
  toFun I := (Ideal.absNorm I : Real)
  map_one' := by simp
  map_mul' I J := by simp [map_mul]

/-- Exact factorization of Real-valued absolute norms over the finite places. -/
theorem absNormReal_eq_finprod
    (I : Ideal (NumberField.RingOfIntegers K)) (hI : I ≠ 0) :
    (Ideal.absNorm I : Real) =
      ∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
        (Ideal.absNorm (v.maxPowDividing I) : Real) := by
  calc
    (Ideal.absNorm I : Real) = absNormReal K I := rfl
    _ = absNormReal K
        (∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
          v.maxPowDividing I) := by
      rw [Ideal.finprod_heightOneSpectrum_factorization hI]
    _ = ∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
          absNormReal K (v.maxPowDividing I) :=
      map_finprod (absNormReal K) (Ideal.hasFiniteMulSupport hI)
    _ = _ := rfl

/-- Positivity of each factor in the finite-place factorization. -/
theorem absNorm_maxPowDividing_pos
    (I : Ideal (NumberField.RingOfIntegers K)) (hI : I ≠ 0)
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    0 < (Ideal.absNorm (v.maxPowDividing I) : Real) := by
  have hne : Ideal.absNorm (v.maxPowDividing I) ≠ 0 := by
    rw [Ideal.absNorm_ne_zero_iff]
    exact Ideal.finiteQuotientOfFreeOfNeBot _
      (pow_ne_zero _ v.ne_bot)
  exact_mod_cast Nat.pos_of_ne_zero hne

/-- B5 product formula: log absNorm I = sum over finite places of
count_v(I) * log absNorm(v). -/
theorem log_absNorm_eq_sum_count_mul_log
    (I : Ideal (NumberField.RingOfIntegers K)) (hI : I ≠ 0) :
    Real.log (Ideal.absNorm I : Real) =
      ∑ᶠ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
        ((Associates.mk v.asIdeal).count (Associates.mk I).factors : Real) *
          Real.log (Ideal.absNorm v.asIdeal : Real) := by
  calc
    Real.log (Ideal.absNorm I : Real) =
        Real.log (∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
          (Ideal.absNorm (v.maxPowDividing I) : Real)) := by
      rw [absNormReal_eq_finprod K I hI]
    _ = ∑ᶠ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
          Real.log (Ideal.absNorm (v.maxPowDividing I) : Real) :=
      Real.log_finprod (fun v => absNorm_maxPowDividing_pos K I hI v)
    _ = ∑ᶠ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
          ((Associates.mk v.asIdeal).count (Associates.mk I).factors : Real) *
            Real.log (Ideal.absNorm v.asIdeal : Real) := by
      apply finsum_congr
      intro v
      rw [IsDedekindDomain.HeightOneSpectrum.maxPowDividing, map_pow]
      push_cast
      rw [Real.log_pow]

#check absNormReal
#check absNormReal_eq_finprod
#check absNorm_maxPowDividing_pos
#check log_absNorm_eq_sum_count_mul_log
end LeanFormal.IUT.XiFPaper.Mzk1B5LocalGlobalProductFormulaActual
end
