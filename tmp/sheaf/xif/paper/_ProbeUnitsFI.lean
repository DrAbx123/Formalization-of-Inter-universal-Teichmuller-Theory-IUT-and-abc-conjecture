import Mathlib.NumberTheory.NumberField.FractionalIdeal
import Mathlib.Algebra.GroupWithZero.Units.Basic
variable (K : Type*) [Field K] [NumberField K]
#check Units.mk0
#check FractionalIdeal.instCommGroupWithZero
#check FractionalIdeal.coeToSubmodule_injective
#check FractionalIdeal.units