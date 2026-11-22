import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.FractionalIdeal.Norm
import Mathlib.Analysis.SpecialFunctions.Log.Basic

noncomputable section
open scoped BigOperators nonZeroDivisors
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2737IdealNormLogActual

universe uS uR uK
variable {S : Type uS} [CommRing S] [IsDedekindDomain S]
variable [Module.Free ℤ S] [Module.Finite ℤ S]

/-- Ideal norm is multiplicative. -/
theorem S2737_ideal_absNorm_mul (I J : Ideal S) :
    Ideal.absNorm (I * J) = Ideal.absNorm I * Ideal.absNorm J :=
  map_mul Ideal.absNorm I J

/-- Log of the ideal norm is additive on products. -/
theorem S2737_log_ideal_absNorm_mul (I J : Ideal S)
    (hI : Ideal.absNorm I ≠ 0) (hJ : Ideal.absNorm J ≠ 0) :
    Real.log (Ideal.absNorm (I * J) : Real) =
      Real.log (Ideal.absNorm I : Real) +
        Real.log (Ideal.absNorm J : Real) := by
  rw [S2737_ideal_absNorm_mul, Nat.cast_mul, Real.log_mul]
  · exact_mod_cast hI
  · exact_mod_cast hJ

/-- The log of the norm of a finite prime-ideal product is the sum of the
logs of the factor norms.  This is the `log >= weight` form once each factor
has norm at least the corresponding prime weight. -/
theorem S2737_log_ideal_absNorm_prod {ι : Type*} [Fintype ι]
    (P : ι → Ideal S) (hpos : ∀ i, Ideal.absNorm (P i) ≠ 0) :
    Real.log (Ideal.absNorm (∏ i, P i) : Real) =
      ∑ i, Real.log (Ideal.absNorm (P i) : Real) := by
  rw [map_prod Ideal.absNorm P Finset.univ, Nat.cast_prod]
  rw [Real.log_prod]
  intro i _
  exact_mod_cast hpos i

/-- Fractional-ideal norm is multiplicative. -/
theorem S2737_fractionalIdeal_absNorm_mul
    {R : Type uR} [CommRing R] [IsDomain R] {K : Type uK} [Field K]
    [Algebra R K] [IsFractionRing R K] [IsDedekindDomain R]
    [Module.Free ℤ R]
    (I J : FractionalIdeal R⁰ K) :
    FractionalIdeal.absNorm (I * J) =
      FractionalIdeal.absNorm I * FractionalIdeal.absNorm J :=
  map_mul FractionalIdeal.absNorm I J

#check S2737_ideal_absNorm_mul
#check S2737_log_ideal_absNorm_prod
#print axioms S2737_log_ideal_absNorm_prod

end LeanFormal.IUT.XiFPaper.S2737IdealNormLogActual
end
