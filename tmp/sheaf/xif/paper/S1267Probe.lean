import tmp.sheaf.xif.paper.S1219ConcreteTensorLandingActual
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicTensorFieldDecomposition
import Mathlib.Algebra.Group.Pi.Units

open LeanFormal.IUT
open LeanFormal.IUT.LocalFieldPadicTensor
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.Theorem311Source

noncomputable section
universe upi umon ui
variable {l : PrimeGeFive}
variable (I : OriginalInput.{0, 0, upi, umon, ui} l (FinitePrimePlace 2 7))
variable {p : Nat} [Fact p.Prime]
variable (place : FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p)

#check Units.mkOfMulEqOne
#check Units.val_mkOfMulEqOne
#check mul_inv_cancel₀
#check inv_mul_cancel₀
#check MulEquiv.piUnits
#check PiTensorProduct.tprod_prod
#check PiTensorProduct.tprod_mul_tprod
#check PiTensorProduct.singleAlgHom
#check PiTensorProduct.one_def
#check RingHom.injective
#check Pi.evalAlgHom
#check AlgEquiv.map_prod
#check map_prod
#check Finset.prod_ne_zero_iff
#check Finset.prod_apply
#check Pi.prod_apply
#check MonoidHom.mulSingle
#check Pi.mulSingle
#check Finset.prod_ite_eq
#check Finset.prod_ite_eq'
#check exists_finiteNormedFieldProduct_piTensor
#check ConcreteTensorLandingData
#check concreteC3ActualFields
#check concreteTensorLanding
#check FinitePlaceQCandidate.q_ne_zero
#check PiTensorProduct.liftAlgHom
#check PiTensorProduct.algHom_ext
#check PiTensorProduct.singleAlgHom_apply
#check AlgEquiv.toRingEquiv
#check Units.map
#check Units.ext
#check Units.ext_iff

end