import tmp.sheaf.xif.paper.RelativeNormCompletion
import tmp.sheaf.xif.paper.FToFmodMapActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedCompletion
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Basis.VectorSpace

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Actual additive F-completion -> Fmod-completion map

Task-658 write-only construction.

The actual local extension of completions is
  completionAlgebra : Algebra (Completion (comap F-place)) (Completion F-place)
with finite module structure. Completing the relative trace by the algebra trace
therefore gives an actual Fmod-linear additive map
  Algebra.trace (Completion (comap F-place)) (Completion F-place).

This file constructs:
* relativeTraceRawAddHom : Completion F ->+ Completion (comap F-place);
* relativeTraceCompletionAddHom : Completion F ->+ Completion (base place),
  by casting the base place equality;
* relativeTraceFmodAddHom : Completion F ->+ NormalizedCompletion (base place)
  = FmodCompletion, by the actual normalized-completion ring equivalence;
* the actual additive FCompletionToFmodCompletionMap.

The map is the actual algebra trace, not a chosen or arbitrary function.
No continuity is asserted: the trace is additive/linear over the base
completion. The continuous extension of the relative trace is a separate
analytic statement; this file constructs the additive map available from the
actual completion algebra and its finite module structure.

No arbitrary map, True/PUnit, axiom, or sorry is used.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.AdditiveFToFmodActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.XiFPaper.RelativeNormCompletion
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.FToFmodMapActual

universe u v w

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- The raw relative trace additive map on completions, at the comap base
place. -/
noncomputable def relativeTraceRawAddHom :
    NativeFCompletion (X := X) →+ NativeBaseCompletionRaw (X := X) :=
  letI := relativeCompletionAlgebra (X := X)
  haveI : Module.Finite (NativeBaseCompletionRaw (X := X))
      (NativeFCompletion (X := X)) :=
    relativeCompletionModuleFinite (X := X)
  haveI : Module.Free (NativeBaseCompletionRaw (X := X))
      (NativeFCompletion (X := X)) :=
    inferInstance
  (Algebra.trace (NativeBaseCompletionRaw (X := X))
    (NativeFCompletion (X := X))).toAddMonoidHom

/-- The raw relative trace is the algebra trace. -/
theorem relativeTraceRawAddHom_apply (x : NativeFCompletion (X := X)) :
    relativeTraceRawAddHom X x =
      letI := relativeCompletionAlgebra (X := X)
      haveI : Module.Finite (NativeBaseCompletionRaw (X := X))
          (NativeFCompletion (X := X)) :=
        relativeCompletionModuleFinite (X := X)
      haveI : Module.Free (NativeBaseCompletionRaw (X := X))
          (NativeFCompletion (X := X)) :=
        inferInstance
      Algebra.trace (NativeBaseCompletionRaw (X := X))
        (NativeFCompletion (X := X)) x := rfl

/-- Cast the raw trace to the native bad base completion. -/
noncomputable def relativeTraceCompletionAddHom :
    NativeFCompletion (X := X) →+ NativeBaseCompletion (X := X) where
  toFun x :=
    cast (congrArg (fun p : NumberField.FinitePlace X.S.arithmetic.Fmod =>
      NumberFieldFinitePlace.Completion p) (nativeFPlaceOverBad_comap X))
      (relativeTraceRawAddHom X x)
  map_zero' := by
    dsimp
    cases nativeFPlaceOverBad_comap X
    simp
  map_add' x y := by
    dsimp
    cases nativeFPlaceOverBad_comap X
    simp

/-- The actual additive F-completion -> Fmod-completion map, using the actual
normalized-completion ring equivalence. -/
noncomputable def relativeTraceFmodAddHom :
    NativeFCompletion (X := X) →+
      NormalizedCompletion (nativeBadBasePlace X) :=
  ((normalizedCompletionRingEquiv (nativeBadBasePlace X)).symm.toRingHom.toAddMonoidHom).comp
    (relativeTraceCompletionAddHom X)

/-- The final map is additive by construction. -/
theorem relativeTraceFmodAddHom_add (x y : NativeFCompletion (X := X)) :
    relativeTraceFmodAddHom X (x + y) =
      relativeTraceFmodAddHom X x + relativeTraceFmodAddHom X y :=
  map_add (relativeTraceFmodAddHom X) x y

/-- The actual additive F-completion -> Fmod-completion map in the frozen
FCompletionToFmodCompletionMap shape. -/
noncomputable def fCompletionToFmodCompletionMap :
    FCompletionToFmodCompletionMap (X := X) where
  toFmod := relativeTraceFmodAddHom X

/-- The frozen map is the actual algebra-trace construction. -/
theorem fCompletionToFmodCompletionMap_toFmod (x : NativeFCompletion (X := X)) :
    (fCompletionToFmodCompletionMap X).toFmod x =
      relativeTraceFmodAddHom X x := rfl

/-- The exact map object is actually constructed. -/
theorem fCompletionToFmodCompletionMap_nonempty :
    Nonempty (FCompletionToFmodCompletionMap (X := X)) :=
  ⟨fCompletionToFmodCompletionMap X⟩

/-- Exact status: the additive map exists from the actual completion algebra
and finite module structure; no continuous-extension assertion is made. -/
theorem additiveFToFmodActual_status :
    (fCompletionToFmodCompletionMap X).toFmod =
      relativeTraceFmodAddHom X := rfl

end LeanFormal.IUT.N8Closure.AdditiveFToFmodActual

end
