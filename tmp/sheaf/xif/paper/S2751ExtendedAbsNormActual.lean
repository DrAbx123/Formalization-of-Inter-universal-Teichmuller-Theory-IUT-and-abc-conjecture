import Mathlib.RingTheory.FractionalIdeal.Norm
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import tmp.sheaf.xif.paper.S2748RationalAbsNormActual

noncomputable section
open scoped nonZeroDivisors
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2751ExtendedAbsNormActual

universe uR uK
variable {R : Type uR} [CommRing R] [IsDomain R]
variable {K : Type uK} [Field K] [Algebra R K] [IsFractionRing R K]
variable [IsDedekindDomain R] [Module.Free ℤ R] [Module.Finite ℤ R]

/-- Coercion of an ideal product to a fractional ideal is the product of the
coerced factors. -/
theorem S2751_coeIdeal_mul (I J : Ideal R) :
    ((I * J : Ideal R) : FractionalIdeal R⁰ K) =
      (I : FractionalIdeal R⁰ K) * (J : FractionalIdeal R⁰ K) :=
  FractionalIdeal.coeIdeal_mul I J

/-- The absNorm of the coerced product is the product of the cofactor
absNorms. -/
theorem S2751_extended_absNorm (I J : Ideal R) :
    FractionalIdeal.absNorm ((I * J : Ideal R) : FractionalIdeal R⁰ K) =
      FractionalIdeal.absNorm (I : FractionalIdeal R⁰ K) *
        FractionalIdeal.absNorm (J : FractionalIdeal R⁰ K) := by
  rw [S2751_coeIdeal_mul, map_mul]

/-- Unconditional rational-place absNorm: the bridge in S2750 is not needed
because S2748 already proves the value directly. -/
theorem S2751_absNorm_rationalFinitePlace (p : Nat) [Fact (Nat.Prime p)] :
    Ideal.absNorm (rationalFinitePlace p).maximalIdeal.asIdeal = p :=
  LeanFormal.IUT.XiFPaper.S2748RationalAbsNormActual.S2748_absNorm_rationalFinitePlace p

#check S2751_extended_absNorm
#check S2751_absNorm_rationalFinitePlace
#print axioms S2751_extended_absNorm

end LeanFormal.IUT.XiFPaper.S2751ExtendedAbsNormActual
end
