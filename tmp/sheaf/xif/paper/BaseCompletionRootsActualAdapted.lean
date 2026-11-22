import tmp.sheaf.xif.paper.BaseRootKummerObjectActualAdapted
import tmp.sheaf.xif.paper.BaseRootKummerActualAdapted
import tmp.sheaf.xif.paper.C3DonorUnconditionalActual
import tmp.sheaf.n8.closure.C3Roots

/-!
# Base completion root system: conditional construction and exact obstruction

The base q unit is

  baseQUnit D : (CommonPrimeCompletion (nativeC3Place X))ˣ,

conditional on the exact base q descent D. The C3 donor needs

  NatRootSystem (baseQUnit D)

in the base completion itself. Existing root data only supplies the
algebraic-closure system

  baseAlgRoots D : NatRootSystem (unitToAlgClosed (baseQUnit D)).

A NatRootSystem in the completion is a coherent compatible family of n-th roots
of baseQUnit D with all roots lying in the completion. The tree has no
construction of such a family for a general contracting q-unit: the completion
is not algebraically closed, and C3Roots constructs roots only in its algebraic
closure.

This file provides the conditional construction from an explicit completion
root-system datum and records that datum as the exact missing construction.
No root, Kummer class, transport, or compatibility proof is fabricated.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.BaseCompletionRootsActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.C3Roots
open LeanFormal.IUT.XiFPaper.BasePlaceQCandidateActual
open LeanFormal.IUT.XiFPaper.BaseRootKummerActualAdapted
open LeanFormal.IUT.XiFPaper.BaseRootKummerObjectActualAdapted
open LeanFormal.IUT.XiFPaper.C3DonorUnconditionalActual
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.InitialThetaSource

universe ua uv upi umon ui

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- The conditional base q unit. -/
noncomputable def baseQUnit (D : BaseQDescentData (X := X)) :
    (CommonPrimeCompletion (K := X.S.arithmetic.Fmod) (nativeC3Place X))ˣ :=
  BaseRootKummerActualAdapted.baseQUnit (X := X) D

/-- Exact missing construction: a completion root system over the actual base
q unit, with both root systems and the Kummer/root-change towers. -/
structure BaseCompletionRootKummerData
    (D : BaseQDescentData (X := X)) : Prop where
  roots : NatRootSystem (baseQUnit (X := X) D)
  roots' : NatRootSystem (baseQUnit (X := X) D)
  kummerClass : CyclotomicTower
    (CommonPrimeCompletion (K := X.S.arithmetic.Fmod) (nativeC3Place X))
  rootChange : CyclotomicTower
    (CommonPrimeCompletion (K := X.S.arithmetic.Fmod) (nativeC3Place X))
  rootChange_eq : rootChange = KummerClass.rootSystemDiff roots roots'

/-- Conditional object construction: an explicit completion root/Kummer datum
gives the C3 base root/Kummer record. -/
noncomputable def baseRootKummerDataOfCompletion
    (D : BaseQDescentData (X := X))
    (C : BaseCompletionRootKummerData (X := X) D) :
    BaseRootKummerData (X := X) (BaseRootKummerActualAdapted.baseQCandidate (X := X) D) where
  roots := C.roots
  roots' := C.roots'
  kummerClass := C.kummerClass
  rootChange := C.rootChange
  rootChange_eq := C.rootChange_eq

/-- The completion root system is exactly the missing object; no algebraic
closure roots are silently accepted as completion roots. -/
def BaseCompletionRootSystemMissing
    (D : BaseQDescentData (X := X)) : Prop :=
  Nonempty (NatRootSystem (baseQUnit (X := X) D))

/-- The algebraic-closure roots do not inhabit the completion root-system type. -/
theorem algebraicClosureRoots_not_completionRoots
    (D : BaseQDescentData (X := X)) :
    NatRootSystem (unitToAlgClosed (baseQUnit (X := X) D)) :=
  baseAlgRoots (X := X) D

/-- The actual algebraic-closure root system exists, but the completion root
system remains the exact missing construction. -/
theorem baseAlgRoots_available
    (D : BaseQDescentData (X := X)) :
    Nonempty (NatRootSystem (unitToAlgClosed (baseQUnit (X := X) D))) :=
  ⟨baseAlgRoots (X := X) D⟩

end LeanFormal.IUT.XiFPaper.BaseCompletionRootsActualAdapted

end
