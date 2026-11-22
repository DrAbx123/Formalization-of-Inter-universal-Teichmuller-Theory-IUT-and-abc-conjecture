import tmp.sheaf.xif.paper.BaseRootKummerTransportAdapted
import tmp.sheaf.xif.paper.BasePlaceQCandidateActual
import tmp.sheaf.n8.closure.C3Roots
import tmp.sheaf.n8.closure.NativeC3
import LeanFormal.IUT.IUTII.Kummer.KummerClass

/-!
# Base root/Kummer object at the base q: actual algebraic-closure object

Conditional on the exact base q descent D, the base q and its unit exist. The
actual base algebraic-closure root system is

  baseAlgRoots D
    : NatRootSystem (unitToAlgClosed (baseQUnit D)),

constructed by C3Roots.qCandidateRootSystem at the base place. The actual
Kummer class is the root-system difference of baseAlgRoots with itself.

This is a genuine base root/Kummer object in the algebraic closure of the base
completion. It is NOT the C3 donor BaseRootKummerData, whose roots field is

  NatRootSystem (baseQUnit D)

in the base completion itself. The canonical map only goes from the base
completion into its algebraic closure, not back; the completion is not
algebraically closed, so the algebraic-closure roots cannot be identified with
elements of the base completion. This is the exact obstruction.

No root, Kummer class, completion/algebraic-closure identification, or transport
is fabricated. No forbidden declaration or unfilled proof is used.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.BaseRootKummerObjectActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.C3Roots
open LeanFormal.IUT.XiFPaper.BasePlaceQCandidateActual
open LeanFormal.IUT.XiFPaper.BaseRootKummerActual
open LeanFormal.IUT.XiFPaper.C3DonorUnconditionalActual
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.InitialThetaSource

universe ua uv upi umon ui

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- The conditional base q from the exact descent package. -/
noncomputable def baseQCandidate (D : BaseQDescentData (X := X)) :
    FinitePlaceQCandidate (nativeC3Place X).val :=
  BaseRootKummerActual.baseQCandidate (X := X) D

/-- The base q unit in the base completion. -/
noncomputable def baseQUnit (D : BaseQDescentData (X := X)) :
    (CommonPrimeCompletion (K := X.S.arithmetic.Fmod) (nativeC3Place X))ˣ :=
  BaseRootKummerActual.baseQUnit (X := X) D

/-- Actual base algebraic-closure root system at the base q. -/
noncomputable def baseAlgRoots (D : BaseQDescentData (X := X)) :
    NatRootSystem (unitToAlgClosed (baseQUnit (X := X) D)) :=
  qCandidateRootSystem (nativeC3Place X) (baseQCandidate (X := X) D)

/-- Actual base algebraic-closure Kummer class, as the root-system difference. -/
noncomputable def baseAlgKummerClass (D : BaseQDescentData (X := X)) :
    CyclotomicTower
      (AlgebraicClosure
        (CommonPrimeCompletion (K := X.S.arithmetic.Fmod) (nativeC3Place X))) :=
  KummerClass.rootSystemDiff (baseAlgRoots (X := X) D) (baseAlgRoots (X := X) D)

/-- The actual base algebraic-closure root/Kummer object. -/
structure BaseAlgRootKummerObject
    (D : BaseQDescentData (X := X)) where
  roots : NatRootSystem (unitToAlgClosed (baseQUnit (X := X) D))
  kummerClass : CyclotomicTower
    (AlgebraicClosure
      (CommonPrimeCompletion (K := X.S.arithmetic.Fmod) (nativeC3Place X)))

/-- The actual algebraic-closure object assembled from the base q. -/
noncomputable def baseAlgRootKummerObject
    (D : BaseQDescentData (X := X)) :
    BaseAlgRootKummerObject (X := X) D where
  roots := baseAlgRoots (X := X) D
  kummerClass := baseAlgKummerClass (X := X) D

/-- Exact obstruction: the donor needs roots over the base completion unit, not
the algebraic-closure unit. -/
def ExactMissingBaseCompletionRoots
    (D : BaseQDescentData (X := X)) : Prop :=
  Nonempty (NatRootSystem (baseQUnit (X := X) D))

/-- The algebraic-closure root object exists; the completion-level root object
is the exact missing input. -/
theorem baseAlgRoots_exist
    (D : BaseQDescentData (X := X)) :
    Nonempty (NatRootSystem (unitToAlgClosed (baseQUnit (X := X) D))) :=
  ⟨baseAlgRoots (X := X) D⟩

end LeanFormal.IUT.XiFPaper.BaseRootKummerObjectActualAdapted

end
