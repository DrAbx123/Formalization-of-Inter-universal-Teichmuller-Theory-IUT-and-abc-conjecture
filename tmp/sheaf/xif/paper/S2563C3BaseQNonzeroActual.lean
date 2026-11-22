import tmp.sheaf.xif.paper.RelativeNormCompletion
import Mathlib.RingTheory.Norm.Basic

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.XiFPaper.RelativeNormCompletion

namespace LeanFormal.IUT.XiFPaper.S2563C3BaseQNonzeroActual

variable {l : PrimeGeFive} (X : N8NativeInput l)

theorem S2563RelativeNormRaw_ne_zero :
    relativeNormRaw (X := X) (nativeQActual X).q ≠ 0 := by
  unfold relativeNormRaw
  letI := relativeCompletionAlgebra (X := X)
  haveI : Module.Free (NativeBaseCompletionRaw (X := X))
      (NativeFCompletion (X := X)) := inferInstance
  haveI : Module.Finite (NativeBaseCompletionRaw (X := X))
      (NativeFCompletion (X := X)) := relativeCompletionModuleFinite (X := X)
  exact Algebra.norm_ne_zero_iff.mpr (nativeQActual X).q_ne_zero

#check S2563RelativeNormRaw_ne_zero
#print axioms S2563RelativeNormRaw_ne_zero
end LeanFormal.IUT.XiFPaper.S2563C3BaseQNonzeroActual
end