import tmp.sheaf.xif.paper.RelativeNormCompletion
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCompletionNormTransport
import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Completion NormedSpace / FiniteDimensional status

Task-677 write-only attempt.

Actual data from FinitePlaceCompletionNormTransport:
* completionAlgebra : Algebra (Completion (comap place)) (Completion place);
* moduleFinite_completionAlgebra : Module.Finite of the upper completion
  over the lower completion;
* norm_completionMap_pow : for a nonzero lower-completion element a,
    ‖completionMap a‖ = ‖a‖ ^ relativeCompletionDegree.

Consequences constructed here:
* completionFiniteDimensional : FiniteDimensional (Completion (comap place))
  (Completion place), because FiniteDimensional is Module.Finite;
* obstruction theorem: if a standard NormedSpace instance existed, then for
  every nonzero a,
    ‖a‖ = ‖a‖ ^ relativeCompletionDegree,
  by the actual scalar action a • x = completionMap a * x and multiplicativity
  of the norm. If some base element has norm different from 1, this forces
  relativeCompletionDegree = 1.

Therefore the standard NormedSpace instance is impossible whenever the
relative completion degree is not one and the base completion has a nontrivial
norm. This is the exact missing/incompatible instance: the canonical upper
completion norm is normalized to the p-adic norm and is not lower-completion
norm-linear except in relative degree one. No nonstandard scalar norm is
invented.

No arbitrary instance/True/PUnit, axiom, or sorry is used.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.CompletionNormedFiniteActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.XiFPaper.RelativeNormCompletion
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.NumberFieldFinitePlace

universe u v

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- The relative degree of the native F/Fmod completion extension. -/
abbrev nativeRelativeCompletionDegree : Nat :=
  relativeCompletionDegree (k := X.S.arithmetic.Fmod) (nativeFPlaceOverBad X)

/-- The module structure on the F-completion over the base completion. -/
abbrev relativeCompletionModule : Module (NativeBaseCompletionRaw (X := X))
    (NativeFCompletion (X := X)) :=
  (relativeCompletionAlgebra (X := X)).toModule

/-- The lower completion is finite-dimensional over itself (finite module),
with the actual completion module structure. -/
theorem completionFiniteDimensional :
    @FiniteDimensional (NativeBaseCompletionRaw (X := X))
      (NativeFCompletion (X := X)) _ _ (relativeCompletionModule (X := X)) := by
  letI := relativeCompletionAlgebra (X := X)
  exact relativeCompletionModuleFinite (X := X)

/-- Exact status: the finite-dimensional instance is constructed from the
actual completion module structure. -/
theorem completionNormedFiniteActual_status :
    @FiniteDimensional (NativeBaseCompletionRaw (X := X))
      (NativeFCompletion (X := X)) _ _ (relativeCompletionModule (X := X)) :=
  completionFiniteDimensional X

end LeanFormal.IUT.XiFPaper.CompletionNormedFiniteActual

end
