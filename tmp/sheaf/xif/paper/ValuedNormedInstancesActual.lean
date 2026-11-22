import tmp.sheaf.xif.paper.RelativeTraceNormedSpaceActual
import Mathlib.Topology.Algebra.Valued.NormedValued

/-! # NormedField instances from the actual Valued data

The actual p-adic valuations nativeFmodValued and nativeFValued are rank-one
valuations (finite places).  Mathlib's Valued.toNormedField therefore gives
actual NormedField structures on the base field Fmod and the extension field F.

The completion CommonPrimeCompletion(nativeFmodPlaceAtPrime) already has its
production NormedField instance.

What is not available is a NormedSpace Fmod F (or Fmod-completion) compatible
with these norms; the relative trace uniformity package needs that missing
structure.  No arbitrary instance/axiom/sorry is used. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.ValuedNormedInstancesActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.FToFmodMapActual
open LeanFormal.IUT.XiFPaper.RelativeTraceNormedSpaceActual

universe ua uv upi umon ui

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- Actual NormedField on the base number field Fmod from its p-adic Valued
structure. -/
noncomputable def nativeFmodNormedField :
    NormedField X.S.arithmetic.Fmod := by
  letI := nativeFmodValued (X := X)
  haveI : (nativeFmodValued (X := X)).v.RankOne := inferInstance
  exact Valued.toNormedField X.S.arithmetic.Fmod ℤᵐ⁰

/-- Actual NormedField on the extension number field F from its p-adic Valued
structure. -/
noncomputable def nativeFNormedField :
    NormedField X.S.arithmetic.F := by
  letI := nativeFValued (X := X)
  haveI : (nativeFValued (X := X)).v.RankOne := inferInstance
  exact Valued.toNormedField X.S.arithmetic.F ℤᵐ⁰

/-- The production NormedField on the Fmod-completion. -/
noncomputable def nativeFmodCompletionNormedField :
    NormedField (CommonPrimeCompletion (nativeFmodPlaceAtPrime X)) :=
  inferInstance

/-- Actual NormedField data assembled from the two place valuations and the
production completion norm. -/
structure NativeNormedFields where
  normedFieldFmod : NormedField X.S.arithmetic.Fmod
  normedFieldF : NormedField X.S.arithmetic.F
  normedFieldCompletion : NormedField
    (CommonPrimeCompletion (nativeFmodPlaceAtPrime X))

/-- The actual normed-field data. -/
noncomputable def nativeNormedFields : NativeNormedFields (X := X) where
  normedFieldFmod := nativeFmodNormedField (X := X)
  normedFieldF := nativeFNormedField (X := X)
  normedFieldCompletion := nativeFmodCompletionNormedField (X := X)

/-- Exact missing NormedSpace data: base -> extension and base -> completion
compatibility with the actual p-adic norms. -/
structure NativeNormedSpaceData (Fmod : Type ua) (F : Type uv)
    [Field Fmod] [Field F] where
  normedFieldFmod : NormedField Fmod
  normedFieldF : NormedField F
  normedSpace : NormedSpace Fmod F
  finiteDimensional : FiniteDimensional Fmod F

/-- The missing NormedSpace data specialized to the actual fields. -/
abbrev NativeFmodFNormedSpaceGap : Prop :=
  Nonempty (NativeNormedSpaceData X.S.arithmetic.Fmod X.S.arithmetic.F)

/-! ## Exact missing instance

Constructed actually:
1. NormedField Fmod via Valued.toNormedField on nativeFmodValued;
2. NormedField F via Valued.toNormedField on nativeFValued;
3. NormedField on CommonPrimeCompletion via the production instance.

Missing:
1. NormedSpace Fmod F compatible with the two p-adic norms;
2. NormedSpace Fmod (CommonPrimeCompletion nativeFmodPlaceAtPrime) compatible
   with the completion norm;
3. FiniteDimensional Fmod F paired with those norm structures.

These are exactly RelativeTraceNormedData.normedSpaceBase,
normedSpaceCompletion, finiteDimensional.  No arbitrary instance/axiom is
inserted. -/

end LeanFormal.IUT.XiFPaper.ValuedNormedInstancesActual

end
