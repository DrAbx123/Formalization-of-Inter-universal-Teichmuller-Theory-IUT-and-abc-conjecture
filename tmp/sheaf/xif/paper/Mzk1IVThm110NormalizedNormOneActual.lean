import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedCompletion
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCommonPrimeCompletion
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1IVThm110NormalizedNormOneActual
open LeanFormal.IUT.NumberFieldFinitePlace
variable {K : Type*} [Field K] [NumberField K]
variable (place : NumberField.FinitePlace K)
instance normalizedCompletionNormOne : NormOneClass (NormalizedCompletion place) := by
  infer_instance
variable {p : Nat} (placep : FinitePlaceAtPrime K p)
instance commonPrimeCompletionNormOne : NormOneClass (CommonPrimeCompletion placep) := by
  infer_instance
#check normalizedCompletionNormOne
#check commonPrimeCompletionNormOne
end LeanFormal.IUT.XiFPaper.Mzk1IVThm110NormalizedNormOneActual
end