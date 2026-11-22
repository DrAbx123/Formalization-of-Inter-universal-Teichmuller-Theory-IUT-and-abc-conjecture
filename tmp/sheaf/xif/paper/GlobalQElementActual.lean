import tmp.sheaf.xif.paper.QPilotGlobalLiftActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Actual global q-pilot element from principal ideal data

Task-651 write-only attempt.

The target is a global integral q-pilot element
  globalQ : SourceOK A
with local compatibility to the actual C3/base q.

The local q lives in a completion and is not a global element. However, an
actual global element can be obtained from an actual q-pilot ideal together
with its principal-generator data: use the canonical generator of the
principal ideal. This is not an arbitrary choice: it is the generator supplied
by the ideal's IsPrincipal structure.

Constructed here:
* PrincipalQPilotIdealData: an actual ideal of O_K, its IsPrincipal instance,
  and the local-compatibility proposition for the C3/base q;
* globalQOfPrincipalIdealData: the canonical principal generator;
* globalQElementDataOfPrincipalIdeal: the actual GlobalQElementData;
* the principal ideal of the constructed global element is exactly the donor
  ideal, and the resulting q-pilot line-bundle source is constructed;
* exact missing datum: an actual principal q-pilot ideal with its principal
  generator and local compatibility. No production q-pilot ideal exists in the
  tree; this is the exact missing global element/ideal.

No arbitrary element, unit substitution, True/PUnit, axiom, or sorry is used.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.GlobalQElementActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaperArithmeticLineBundle
open LeanFormal.IUT.N8Closure.QPilotGlobalLiftActual
open LeanFormal.IUT.N8Closure.QPilotGlobalIdealActual
open LeanFormal.IUT.N8Closure.QPilotLineBundleUnconditional
open LeanFormal.IUT.N8Closure.SourcePilotRegion

universe ua uv upi umon ui

variable {l : PrimeGeFive}
variable {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable (A : InitialThetaArithmeticData l)

/-- Actual principal q-pilot ideal data: the ideal, its principal-generator
structure, and the local compatibility proposition. -/
structure PrincipalQPilotIdealData where
  qPilotIdeal : Ideal (SourceOK (A := A))
  isPrincipal : qPilotIdeal.IsPrincipal
  local_compatibility : Prop

/-- The canonical global generator of the principal q-pilot ideal. -/
def globalQOfPrincipalIdealData
    (D : PrincipalQPilotIdealData (A := A)) :
    SourceOK (A := A) :=
  letI := D.isPrincipal
  Submodule.IsPrincipal.generator D.qPilotIdeal

/-- The span of the canonical generator is exactly the donor q-pilot ideal. -/
theorem span_globalQOfPrincipalIdealData
    (D : PrincipalQPilotIdealData (A := A)) :
    Ideal.span ({globalQOfPrincipalIdealData (A := A) D} :
        Set (SourceOK (A := A))) = D.qPilotIdeal := by
  letI := D.isPrincipal
  exact Submodule.IsPrincipal.span_singleton_generator D.qPilotIdeal

/-- The actual global q-pilot element data from the principal ideal data. -/
def globalQElementDataOfPrincipalIdeal
    (D : PrincipalQPilotIdealData (A := A)) :
    GlobalQElementData (A := A) where
  globalQ := globalQOfPrincipalIdealData (A := A) D
  local_compatibility := D.local_compatibility

/-- The principal ideal of the constructed global element is exactly the donor
q-pilot ideal. -/
theorem qPilotIdealOfGlobalQElementData
    (D : PrincipalQPilotIdealData (A := A)) :
    qPilotIdealOfGlobalQ (A := A)
        (globalQElementDataOfPrincipalIdeal (A := A) D) = D.qPilotIdeal :=
  span_globalQOfPrincipalIdealData (A := A) D

/-- The constructed q-pilot line-bundle source has the donor principal ideal. -/
theorem qPilotLineBundleSourceOfPrincipalIdeal
    (D : PrincipalQPilotIdealData (A := A)) :
    (qPilotLineBundleSourceOfGlobalQ (A := A)
        (globalQElementDataOfPrincipalIdeal (A := A) D)).qPilotIdeal =
      D.qPilotIdeal :=
  qPilotIdealOfGlobalQElementData (A := A) D

/-- The constructed global element is integral (it is an element of O_K). -/
theorem globalQOfPrincipalIdealData_mem_ring
    (D : PrincipalQPilotIdealData (A := A)) :
    globalQOfPrincipalIdealData (A := A) D ∈ SourceOK (A := A) :=
  Subtype.mem _

/-- Exact missing principal q-pilot ideal data. -/
def MissingPrincipalQPilotIdeal
    (C3 : SourcePilotRegionData (l := l) (V := V) I) : Prop :=
  Nonempty (PrincipalQPilotIdealData (A := A))

/-- Exact status: principal global element and line-bundle source are
constructed from the principal ideal donor; the donor itself is the missing
q-pilot ideal. -/
theorem globalQElementActual_status
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (D : PrincipalQPilotIdealData (A := A)) :
    (qPilotLineBundleSourceOfGlobalQ (A := A)
        (globalQElementDataOfPrincipalIdeal (A := A) D)).qPilotIdeal =
        D.qPilotIdeal ∧
      Nonempty (PaperQPilotLineBundleSource A) :=
  ⟨qPilotLineBundleSourceOfPrincipalIdeal (A := A) D,
    ⟨qPilotLineBundleSourceOfGlobalQ (A := A)
      (globalQElementDataOfPrincipalIdeal (A := A) D)⟩⟩

end LeanFormal.IUT.N8Closure.GlobalQElementActual

end
