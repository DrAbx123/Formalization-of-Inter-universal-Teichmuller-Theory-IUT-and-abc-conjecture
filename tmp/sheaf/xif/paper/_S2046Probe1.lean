import Mathlib.NumberTheory.Cyclotomic.Gal
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.Polynomial.Eisenstein.IsIntegral
import Mathlib.RingTheory.Polynomial.Eisenstein.Basic

open Polynomial
open scoped Cyclotomic

variable (p : Nat) [Fact (Nat.Prime p)]
variable (n : Nat)

#check CyclotomicField (p ^ n) ℚ_[p]
#check IsCyclotomicExtension.zeta_spec
#check IsCyclotomicExtension.autEquivPow
#check PadicInt.toZModPow
#check PadicInt.unitCoeff
#check PadicInt.mkUnits
#check PadicInt.isUnit_iff
#check PadicInt.unitCoeff_coe
#check PadicInt.lift
#check PadicInt.ext_of_toZModPow
#check IsPrimitive.irreducible_iff_irreducible_map_fraction_map
#check Polynomial.cyclotomic_prime_pow_comp_X_add_one_isEisensteinAt
#check Polynomial.IsEisensteinAt.irreducible
#check Polynomial.cyclotomic.isPrimitive
#check Polynomial.Monic.isPrimitive
#check IsFractionRing ℤ_[p] ℚ_[p]
#check IsIntegrallyClosed ℤ_[p]

example : IsCyclotomicExtension {p ^ n} ℚ_[p] (CyclotomicField (p ^ n) ℚ_[p]) := inferInstance
