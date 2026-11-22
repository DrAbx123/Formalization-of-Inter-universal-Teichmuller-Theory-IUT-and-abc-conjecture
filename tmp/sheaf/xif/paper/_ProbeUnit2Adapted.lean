import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCompletionLocalInputs
import LeanFormal.IUT.Foundations.NumberField.FinitePlaces
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
variable {K : Type} [Field K] [NumberField K] (v : NumberField.FinitePlace K)
#check CharP.ringChar
#check CharP.cast_eq_zero_iff
#check CharP.of_ringHom_of_ne_zero
#check IsLocalRing.ResidueField
#check IsLocalRing.residue
#check IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers
