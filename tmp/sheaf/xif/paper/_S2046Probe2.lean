import Mathlib.NumberTheory.Cyclotomic.Gal
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.Polynomial.Eisenstein.IsIntegral
import Mathlib.RingTheory.Polynomial.Eisenstein.Basic

open Polynomial
open scoped Cyclotomic

#check cyclotomic_prime_pow_comp_X_add_one_isEisensteinAt
#check cyclotomic_comp_X_add_one_isEisensteinAt
#check IsCyclotomicExtension.isGalois
#check IsCyclotomicExtension.finiteDimensional
#check IsCyclotomicExtension.finrank
#check IsCyclotomicExtension.Aut.commGroup
#check IsCyclotomicExtension.zeta
#check IsCyclotomicExtension.zeta_spec
#check IsPrimitiveRoot.autToPow
#check IsPrimitiveRoot.autToPow_spec
#check IsPrimitiveRoot.autToPow_injective
#check IsCyclotomicExtension.fromZetaAut
