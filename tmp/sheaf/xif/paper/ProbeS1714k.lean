import LeanFormal.IUT.Foundations.Geometry.ConcreteSplitCurveFivePlace
import Mathlib.Tactic
open LeanFormal.IUT
open WeierstrassCurve

local instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
abbrev K5 := ℚ_[5]
abbrev R5 := ℤ_[5]

example :
    concreteFivePadicEquiv.toRingEquiv.toRingHom.comp
      (algebraMap R5 K5) =
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
