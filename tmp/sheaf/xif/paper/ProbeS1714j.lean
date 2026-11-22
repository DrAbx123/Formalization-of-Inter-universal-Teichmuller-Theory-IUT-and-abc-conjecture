import LeanFormal.IUT.Foundations.Geometry.ConcreteSplitCurveFivePlace
import Mathlib.Tactic
open LeanFormal.IUT

example :
    concreteFivePadicEquiv.toRingEquiv.toRingHom.comp
      (algebraMap concreteLocalIntegers concreteLocalField) =
    (algebraMap concreteFiveCompletionIntegers concreteFiveCompletion).comp
      concreteFivePadicIntEquiv.toRingEquiv.toRingHom := by
  apply RingHom.ext
  intro x
  change concreteFivePadicEquiv (algebraMap concreteLocalIntegers
    concreteLocalField x) =
    algebraMap concreteFiveCompletionIntegers concreteFiveCompletion
      (concreteFivePadicIntEquiv x)
  change concreteFivePadicEquiv (algebraMap concreteLocalIntegers
    concreteLocalField x) = (concreteFivePadicIntEquiv x : concreteFiveCompletion)
  rw [concreteFivePadicIntEquiv_coe]
  congr 1
