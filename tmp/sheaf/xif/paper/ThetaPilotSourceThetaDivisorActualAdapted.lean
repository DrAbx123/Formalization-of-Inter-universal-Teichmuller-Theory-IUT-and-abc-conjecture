import tmp.sheaf.xif.paper.ThetaPilotArithmeticDivisorActualAdapted
import tmp.sheaf.xif.paper.ThetaFunctionLineBundleActual

/-!
# Actual source theta divisor data and its relation to the q-pilot divisor

This file combines the actual q-pilot global ideal family of
`ThetaPilotArithmeticDivisorActualAdapted` with the actual source theta divisor data
of `ThetaFunctionLineBundleActual`.

Constructed actual objects:

* the actual source theta curve and source theta-divisor type;
* the actual source theta zero divisor;
* the actual q-pilot global ideal family;
* the actual relation between the q-pilot archimedean coordinate and the
  source theta zero divisor (both are the actual zero coordinate).

NOT constructed: the source theta line bundle, theta function/global section,
and the global theta zero divisor identified with the `{q_j^2}` divisor.  That
is recorded as the exact obstruction below; no line bundle or divisor is
fabricated.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper
namespace ThetaPilotSourceThetaDivisorActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.GlobalThetaPilotLogVolumeActual
open LeanFormal.IUT.XiFPaper.ThetaPilotArithmeticDivisorActualAdapted
open ABCBridge.SourceThetaFunctionLineBundleActual
open ABCBridge.SourceQlThetaLineBundleFromCurve
open ABCBridge.SourceQlThetaObjectActual

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The actual source arithmetic theta curve. -/
abbrev actualSourceThetaCurve :
    PuncturedEllipticCurve T.arithmetic.F :=
  actualThetaCurve (S := T.tuple.source)

/-- The actual source theta-divisor type. -/
abbrev actualSourceThetaDivisorType : Type :=
  actualThetaDivisorType (S := T.tuple.source)

/-- The actual source theta zero divisor. -/
noncomputable def actualSourceThetaZeroDivisor : actualSourceThetaDivisorType (T := T) :=
  actualThetaZeroDivisor (S := T.tuple.source)

/-- The actual q-pilot global ideal family from the actual clause-B q_v data. -/
abbrev actualSourceQPilotDivisor : GlobalIdealFamily T.arithmetic.F :=
  actualQPilotGlobalIdealFamily T

/-- The actual q-pilot archimedean coordinate is the actual source theta zero
coordinate.  This is a relation of the actual zero archimedean components; it is
not the missing finite-place theta divisor. -/
theorem actualQPilotInfinite_thetaZeroRelation
    (w : NumberField.InfinitePlace T.arithmetic.F) :
    (actualSourceQPilotDivisor T).infinite w =
      ((actualSourceThetaZeroDivisor (T := T)) w : Real) := by
  simp [actualSourceQPilotDivisor, actualSourceThetaZeroDivisor,
    actualThetaZeroDivisor, sourceThetaLineBundleZeroDivisor,
    sourceThetaObjectZeroDivisor, actualQPilotGlobalIdealFamily]

/-- The actual relation proposition between the q-pilot archimedean coordinate
and the actual source theta zero divisor. -/
def ActualQPilotThetaZeroRelation : Prop :=
  forall w : NumberField.InfinitePlace T.arithmetic.F,
    (actualSourceQPilotDivisor T).infinite w =
      ((actualSourceThetaZeroDivisor (T := T)) w : Real)

/-- The actual relation is proved for the constructed objects. -/
theorem actualQPilotThetaZeroRelation_proof :
    ActualQPilotThetaZeroRelation (T := T) := by
  intro w
  exact actualQPilotInfinite_thetaZeroRelation (T := T) w

/-- Exact outstanding obligations: the source theta line bundle, theta
function/global section, and the global theta zero divisor identified with the
`{q_j^2}` divisor are not available from the source contract.  The list is the
exact named datum; it is not a propositional gate. -/
def SourceThetaLineBundleObstruction :
    ThetaFunctionLineBundleObligations (l := l) T.tuple.source :=
  actualThetaFunctionLineBundleObligations (l := l) T.tuple.source

/-- Actual combined data: q-pilot divisor, source theta curve/divisor type,
actual theta zero divisor, the actual archimedean relation, and the exact source
line-bundle obstruction. -/
structure ActualThetaPilotSourceDivisorData where
  qPilotDivisor : GlobalIdealFamily T.arithmetic.F
  qPilotDivisor_eq : qPilotDivisor = actualSourceQPilotDivisor T
  thetaCurve : PuncturedEllipticCurve T.arithmetic.F
  thetaCurve_eq : thetaCurve = actualSourceThetaCurve (T := T)
  thetaZeroDivisor : actualSourceThetaDivisorType (T := T)
  thetaZeroDivisor_eq : thetaZeroDivisor = actualSourceThetaZeroDivisor (T := T)
  qPilotThetaRelation : Prop
  qPilotThetaRelation_eq : qPilotThetaRelation = ActualQPilotThetaZeroRelation (T := T)
  qPilotThetaRelation_proved : qPilotThetaRelation
  sourceThetaLineBundleObstruction :
    ThetaFunctionLineBundleObligations (l := l) T.tuple.source
  sourceThetaLineBundleObstruction_eq :
    sourceThetaLineBundleObstruction = SourceThetaLineBundleObstruction (T := T)

/-- The actual combined Theta-pilot/source-theta-divisor data. -/
noncomputable def actualThetaPilotSourceDivisorData :
    ActualThetaPilotSourceDivisorData (T := T) where
  qPilotDivisor := actualSourceQPilotDivisor T
  qPilotDivisor_eq := rfl
  thetaCurve := actualSourceThetaCurve (T := T)
  thetaCurve_eq := rfl
  thetaZeroDivisor := actualSourceThetaZeroDivisor (T := T)
  thetaZeroDivisor_eq := rfl
  qPilotThetaRelation := ActualQPilotThetaZeroRelation (T := T)
  qPilotThetaRelation_eq := rfl
  qPilotThetaRelation_proved := actualQPilotThetaZeroRelation_proof (T := T)
  sourceThetaLineBundleObstruction := SourceThetaLineBundleObstruction (T := T)
  sourceThetaLineBundleObstruction_eq := rfl

/-- The constructed q-pilot divisor is the actual clause-B q-pilot ideal family. -/
theorem actualThetaPilotSourceDivisorData_qPilotDivisor :
    (actualThetaPilotSourceDivisorData (T := T)).qPilotDivisor =
      actualQPilotGlobalIdealFamily T := rfl

end ThetaPilotSourceThetaDivisorActualAdapted
end LeanFormal.IUT.XiFPaper
end
