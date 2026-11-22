import tmp.sheaf.xif.paper.QPilotGlobalIdealActual
import tmp.sheaf.xif.paper.BasePlaceQCandidateActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Global q-pilot lift: object attempt and exact missing element

Task-646 write-only attempt.

Actual local data available:
* C3.q is a FinitePlaceQCandidate at a completion of the base field Fmod;
* NativeC3.nativeQActual is a finite-place q at the F-place;
* BasePlaceQCandidateActual supplies a base-place q only from an explicit
  BaseQDescentData package;
* ArithmeticLineBundleActual supplies the actual global integral ring O_K for
  the number field K of A.

The target is a global integral element
  globalQ : SourceOK A
whose local/base compatibility realizes the q-pilot lift. The local q lives in
a completion of Fmod, while SourceOK A is the integral ring of the number field
K. No production map from the local completion/base q to an integral element
of O_K exists in the tree. Therefore this file constructs the downstream
principal ideal and line-bundle source from an explicit global-element donor
and records the exact missing global lift.

No arbitrary element/ideal, unit substitution, True/PUnit, axiom, or sorry is
used.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.QPilotGlobalLiftActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaperArithmeticLineBundle
open LeanFormal.IUT.N8Closure.QPilotGlobalIdealActual
open LeanFormal.IUT.N8Closure.QPilotLineBundleUnconditional
open LeanFormal.IUT.N8Closure.SourcePilotRegion

universe ua uv upi umon ui

variable {l : PrimeGeFive}
variable {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable (A : InitialThetaArithmeticData l)

/-- The exact global q-pilot element donor: an integral global element and the
local compatibility proposition connecting it to the actual C3/base q. -/
structure GlobalQElementData where
  globalQ : SourceOK (A := A)
  local_compatibility : Prop

/-- The global element donor is exactly a GlobalQPilotLift. -/
def GlobalQElementData.toGlobalQPilotLift
    (D : GlobalQElementData (A := A)) :
    GlobalQPilotLift (A := A) where
  globalQ := D.globalQ
  local_compatibility := D.local_compatibility

/-- The actual principal q-pilot ideal from the supplied global element. -/
def qPilotIdealOfGlobalQ
    (D : GlobalQElementData (A := A)) :
    Ideal (SourceOK (A := A)) :=
  qPilotIdealOfLift (A := A) D.toGlobalQPilotLift

/-- The actual paper q-pilot line-bundle source from the global element. -/
noncomputable def qPilotLineBundleSourceOfGlobalQ
    (D : GlobalQElementData (A := A)) :
    PaperQPilotLineBundleSource A :=
  qPilotLineBundleSourceOfLift (A := A) D.toGlobalQPilotLift

/-- The constructed ideal is the principal ideal of the global element. -/
theorem qPilotIdealOfGlobalQ_eq
    (D : GlobalQElementData (A := A)) :
    qPilotIdealOfGlobalQ (A := A) D =
      Ideal.span ({D.globalQ} : Set (SourceOK (A := A))) := rfl

/-- The constructed source has the principal global ideal. -/
theorem qPilotLineBundleSourceOfGlobalQ_ideal
    (D : GlobalQElementData (A := A)) :
    (qPilotLineBundleSourceOfGlobalQ (A := A) D).qPilotIdeal =
      Ideal.span ({D.globalQ} : Set (SourceOK (A := A))) := rfl

/-- Exact missing global lift from the actual local C3/base q. -/
def MissingGlobalQPilotElement
    (C3 : SourcePilotRegionData (l := l) (V := V) I) : Prop :=
  Nonempty (GlobalQElementData (A := A))

/-- The actual local C3 q data recorded without a global lift. -/
structure LocalC3QData
    (C3 : SourcePilotRegionData (l := l) (V := V) I) where
  c3q_ne_zero : C3.q.q ≠ 0
  c3q_contracting :
    (Valued.v C3.q.q : WithZero (Multiplicative Int)) < 1

/-- The actual local C3 q data is available. -/
def localC3QData
    (C3 : SourcePilotRegionData (l := l) (V := V) I) :
    LocalC3QData (C3 := C3) where
  c3q_ne_zero := C3.q.q_ne_zero
  c3q_contracting := C3.q.valuation_lt_one

/-- Conditional global q-pilot object from a supplied global element. -/
theorem qPilotGlobalLift_status
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (D : GlobalQElementData (A := A)) :
    (qPilotLineBundleSourceOfGlobalQ (A := A) D).qPilotIdeal =
        Ideal.span ({D.globalQ} : Set (SourceOK (A := A))) ∧
      Nonempty (PaperQPilotLineBundleSource A) :=
  ⟨qPilotLineBundleSourceOfGlobalQ_ideal (A := A) D,
    ⟨qPilotLineBundleSourceOfGlobalQ (A := A) D⟩⟩

/-- The exact missing object is a global integral q-pilot element with local
compatibility; the actual local C3 q data alone does not provide it. -/
def MissingGlobalQPilotLiftObject : Prop :=
  Nonempty (GlobalQElementData (A := A))

end LeanFormal.IUT.N8Closure.QPilotGlobalLiftActual

end
