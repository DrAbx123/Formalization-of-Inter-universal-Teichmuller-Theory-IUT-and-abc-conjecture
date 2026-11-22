import tmp.sheaf.xif.paper.RelativeNormCompletion
import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
import Mathlib.Topology.Algebra.ValuativeRel.ValuativeTopology
import Mathlib.NumberTheory.LocalField.Basic

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.RelativeNormCompletion

namespace LeanFormal.IUT.XiFPaper.S2564TauCetiInstanceSkeletonActual

variable {l : PrimeGeFive} (X : N8NativeInput l)

noncomputable instance S2564FCompletionValuativeRel :
    ValuativeRel (NativeFCompletion (X := X)) :=
  ValuativeRel.ofValuation (Valued.v :
    Valuation (NativeFCompletion (X := X)) (WithZero (Multiplicative Int)))

noncomputable instance S2564BaseCompletionRawValuativeRel :
    ValuativeRel (NativeBaseCompletionRaw (X := X)) :=
  ValuativeRel.ofValuation (Valued.v :
    Valuation (NativeBaseCompletionRaw (X := X)) (WithZero (Multiplicative Int)))

/-- Exact target for the completion ValuativeExtension instance. -/
noncomputable instance S2564FValuedCompatible :
    (Valued.v : Valuation (NativeFCompletion (X := X))
      (WithZero (Multiplicative Int))).Compatible :=
  Valuation.Compatible.ofValuation _

noncomputable instance S2564FCompletionIsNontrivial :
    ValuativeRel.IsNontrivial (NativeFCompletion (X := X)) :=
  (ValuativeRel.isNontrivial_iff_isNontrivial
    (Valued.v : Valuation (NativeFCompletion (X := X))
      (WithZero (Multiplicative Int)))).mpr inferInstance

noncomputable instance S2564BaseValuedCompatible :
    (Valued.v : Valuation (NativeBaseCompletionRaw (X := X))
      (WithZero (Multiplicative Int))).Compatible :=
  Valuation.Compatible.ofValuation _

noncomputable instance S2564BaseCompletionIsNontrivial :
    ValuativeRel.IsNontrivial (NativeBaseCompletionRaw (X := X)) :=
  (ValuativeRel.isNontrivial_iff_isNontrivial
    (Valued.v : Valuation (NativeBaseCompletionRaw (X := X))
      (WithZero (Multiplicative Int)))).mpr inferInstance

def S2564ValuativeExtensionTarget : Prop := by
  letI := relativeCompletionAlgebra (X := X)
  exact Nonempty (ValuativeExtension (NativeBaseCompletionRaw (X := X))
    (NativeFCompletion (X := X)))

/-- Minimal skeleton: the remaining local-field instance obligations. -/
structure S2564TauCetiInstanceSkeleton where
  fNonarch : IsNonarchimedeanLocalField (NativeFCompletion (X := X))
  baseNonarch : IsNonarchimedeanLocalField (NativeBaseCompletionRaw (X := X))
  extension : S2564ValuativeExtensionTarget (X := X)

#check S2564FCompletionValuativeRel
#check S2564BaseCompletionRawValuativeRel
#check S2564TauCetiInstanceSkeleton
#check S2564FCompletionIsNontrivial
#check S2564BaseCompletionIsNontrivial
#print axioms S2564FCompletionValuativeRel
#print axioms S2564FCompletionIsNontrivial
end LeanFormal.IUT.XiFPaper.S2564TauCetiInstanceSkeletonActual
end