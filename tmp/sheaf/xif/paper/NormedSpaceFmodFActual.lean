import tmp.sheaf.xif.paper.ValuedNormedInstancesActual

/-! # NormedSpace Fmod F from p-adic norm compatibility

The actual p-adic NormedField structures on Fmod and F are constructed in
ValuedNormedInstancesActual.  A NormedSpace Fmod F additionally requires

  forall a x, ||a • x||_F <= ||a||_Fmod * ||x||_F.

The frozen source proves no such compatibility between the independently
normalized base and extension absolute values.  This file records that
compatibility as an explicit hypothesis, constructs the NormedSpace
conditionally, and states the exact missing compatibility theorem.

No arbitrary instance/axiom/sorry. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.NormedSpaceFmodFActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.FToFmodMapActual
open LeanFormal.IUT.XiFPaper.ValuedNormedInstancesActual

universe ua uv upi umon ui uF uG

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- Explicit p-adic norm compatibility for the scalar action Fmod on F. -/
structure FmodFNormCompatibility
    (Fmod : Type uF) (F : Type uG) [NormedField Fmod] [NormedField F]
    [Algebra Fmod F] where
  norm_smul_le : ∀ (a : Fmod) (x : F),
    ‖a • x‖ ≤ ‖a‖ * ‖x‖

/-- Construct NormedSpace from the explicit compatibility inequality. -/
noncomputable def normedSpaceOfCompatibility
    {Fmod : Type uF} {F : Type uG} [NormedField Fmod] [NormedField F]
    [Algebra Fmod F] (D : FmodFNormCompatibility Fmod F) :
    NormedSpace Fmod F where
  norm_smul_le := D.norm_smul_le

/-- The same compatibility for the Fmod-completion as an Fmod-module. -/
structure FmodCompletionNormCompatibility
    [Algebra X.S.arithmetic.Fmod
      (CommonPrimeCompletion (nativeFmodPlaceAtPrime X))] where
  norm_smul_le : ∀ (a : X.S.arithmetic.Fmod)
      (x : CommonPrimeCompletion (nativeFmodPlaceAtPrime X)),
    ‖a • x‖ ≤ ‖a‖ * ‖x‖

/-- Conditional NormedSpace on the p-adic completion. -/
noncomputable def normedSpaceCompletionOfCompatibility
    [Algebra X.S.arithmetic.Fmod
      (CommonPrimeCompletion (nativeFmodPlaceAtPrime X))]
    (D : FmodCompletionNormCompatibility (X := X)) :
    NormedSpace X.S.arithmetic.Fmod
      (CommonPrimeCompletion (nativeFmodPlaceAtPrime X)) where
  norm_smul_le := D.norm_smul_le

/-- Conditional actual NormedSpace Fmod F from the missing compatibility. -/
noncomputable def nativeNormedSpaceFmodF
    [Algebra X.S.arithmetic.Fmod X.S.arithmetic.F]
    (D : @FmodFNormCompatibility X.S.arithmetic.Fmod X.S.arithmetic.F
      (nativeFmodNormedField (X := X)) (nativeFNormedField (X := X)) _) :
    @NormedSpace X.S.arithmetic.Fmod X.S.arithmetic.F
      (nativeFmodNormedField (X := X)) (nativeFNormedField (X := X)) _ := by
  letI := nativeFmodNormedField (X := X)
  letI := nativeFNormedField (X := X)
  letI := (inferInstance : Algebra X.S.arithmetic.Fmod X.S.arithmetic.F)
  exact normedSpaceOfCompatibility
    (Fmod := X.S.arithmetic.Fmod) (F := X.S.arithmetic.F) D

/-- Exact missing compatibility: p-adic norm scalar inequality for Fmod on F. -/
def MissingFmodFNormCompatibility : Prop :=
  Nonempty (FmodFNormCompatibility X.S.arithmetic.Fmod X.S.arithmetic.F
    (nativeFmodNormedField (X := X)) (nativeFNormedField (X := X)))

/-- Exact missing compatibility for the completion norm. -/
def MissingFmodCompletionNormCompatibility : Prop :=
  Nonempty (FmodCompletionNormCompatibility (X := X))

/-! ## Exact missing compatibility theorem

Constructed/determined:
1. NormedField Fmod from nativeFmodValued;
2. NormedField F from nativeFValued;
3. conditional NormedSpace from an explicit norm_smul inequality.

Missing:
  forall a : Fmod, x : F,
    ||a • x||_F <= ||a||_Fmod * ||x||_F

and the analogous inequality for CommonPrimeCompletion(nativeFmodPlaceAtPrime).
These are the exact p-adic norm compatibility theorems; they are not derivable
from the separately normalized Valued.toNormedField structures.  No arbitrary
instance/axiom is inserted. -/

end LeanFormal.IUT.XiFPaper.NormedSpaceFmodFActual

end
