import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCompletionLocalInputs
import LeanFormal.IUT.Foundations.NumberField.FinitePlaces
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
variable {K : Type} [Field K] [NumberField K] (v : NumberField.FinitePlace K)
#check v.adicCompletionIntegers K
#check IsLocalRing.residue_ne_zero_iff_isUnit
#check adicCompletionResidueQuotientEquiv
#check (v.maximalIdeal)
#check v.residueCharacteristic
#check CharP.cast_eq_zero_iff
