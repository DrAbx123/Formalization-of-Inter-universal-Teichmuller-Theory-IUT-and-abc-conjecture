import Mathlib.RingTheory.FractionalIdeal.Norm
import Mathlib.RingTheory.Ideal.Norm.AbsNorm

noncomputable section
open scoped BigOperators nonZeroDivisors
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2733IdealAbsNormProductActual

universe uR uK
variable {R : Type uR} [CommRing R] [IsDomain R]
variable {K : Type uK} [Field K] [Algebra R K] [IsFractionRing R K]
variable [IsDedekindDomain R] [Module.Free ℤ R] [Module.Finite ℤ R]

/-- Multiplicativity of `FractionalIdeal.absNorm` over a finite product. -/
theorem S2733_fractionalIdeal_absNorm_prod
    {ι : Type*} [Fintype ι] (I : ι → FractionalIdeal R⁰ K) :
    FractionalIdeal.absNorm (∏ i, I i) =
      ∏ i, FractionalIdeal.absNorm (I i) :=
  map_prod FractionalIdeal.absNorm I Finset.univ

/-- Power form of multiplicative fractional-ideal norm. -/
theorem S2733_fractionalIdeal_absNorm_pow
    (I : FractionalIdeal R⁰ K) (n : Nat) :
    FractionalIdeal.absNorm (I ^ n) = FractionalIdeal.absNorm I ^ n :=
  map_pow FractionalIdeal.absNorm I n

/-- Multiplicativity of `Ideal.absNorm` over a finite product. -/
theorem S2733_ideal_absNorm_prod
    {ι : Type*} [Fintype ι] (P : ι → Ideal R) :
    Ideal.absNorm (∏ i, P i) = ∏ i, Ideal.absNorm (P i) :=
  map_prod Ideal.absNorm P Finset.univ

/-- Power form of the ideal norm. -/
theorem S2733_ideal_absNorm_pow
    (P : Ideal R) (n : Nat) :
    Ideal.absNorm (P ^ n) = Ideal.absNorm P ^ n :=
  map_pow Ideal.absNorm P n

/-- An integral ideal's fractional-ideal norm is its ideal norm. -/
theorem S2733_fractionalIdeal_absNorm_coeIdeal
    (P : Ideal R) :
    FractionalIdeal.absNorm (P : FractionalIdeal R⁰ K) =
      (Ideal.absNorm P : ℚ) :=
  FractionalIdeal.coeIdeal_absNorm P

#print axioms S2733_fractionalIdeal_absNorm_prod
#print axioms S2733_fractionalIdeal_absNorm_coeIdeal

end LeanFormal.IUT.XiFPaper.S2733IdealAbsNormProductActual
end
