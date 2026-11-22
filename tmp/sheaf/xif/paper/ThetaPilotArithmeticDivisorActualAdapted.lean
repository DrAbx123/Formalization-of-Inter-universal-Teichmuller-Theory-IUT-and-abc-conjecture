import tmp.sheaf.xif.paper.QPilotZeroLocusDivisorActual
import tmp.sheaf.xif.paper.GlobalThetaPilotLogVolumeActual
import tmp.sheaf.xif.paper.ThetaFunctionLineBundleActual

/-!
# Actual Theta-pilot arithmetic-divisor data

This file constructs the actual parts of the Theta-pilot arithmetic-divisor
package available from the native source:

* the actual global q-pilot ideal family, built from the actual clause-B q_v
  family at each native bad place;
* the actual Theta-value family q_v^(j^2);
* the actual theta-value zero locus (empty for the positive real theta values,
  explicitly not the source theta divisor);
* an exact source obstruction for the source theta divisor, global zero
  divisor, and Theta-link identification.

No global theta divisor, line bundle, or Theta-link is fabricated.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper
namespace ThetaPilotArithmeticDivisorActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.GlobalThetaPilotLogVolumeActual

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The actual global q-pilot ideal family: the finite sum of the local q_v
zero-locus divisors, with zero archimedean coordinate. -/
noncomputable def actualQPilotGlobalIdealFamily :
    GlobalIdealFamily T.arithmetic.F where
  finite :=
    ∑ b : Bad (nativePlaceSelection T),
      Finsupp.single ((nativeBadLift T).lift b).maximalIdeal
        ((qVFamily T b).exponent)
  infinite := fun _ => 0

/-- The finite part of the actual q-pilot ideal family is the q_v sum. -/
theorem actualQPilotGlobalIdealFamily_finite :
    (actualQPilotGlobalIdealFamily T).finite =
      ∑ b : Bad (nativePlaceSelection T),
        Finsupp.single ((nativeBadLift T).lift b).maximalIdeal
          ((qVFamily T b).exponent) := rfl

/-- The archimedean part of the actual q-pilot ideal family is zero. -/
theorem actualQPilotGlobalIdealFamily_infinite
    (w : NumberField.InfinitePlace T.arithmetic.F) :
    (actualQPilotGlobalIdealFamily T).infinite w = 0 := rfl

/-- The actual Theta-value family q_v^(j^2) at each native bad place. -/
noncomputable def actualThetaValueFamily
    (b : Bad (nativePlaceSelection T)) (j : SignedLabel l.value) : Real :=
  thetaValueFromQ T b j

/-- The actual theta-value family is positive. -/
theorem actualThetaValueFamily_pos
    (b : Bad (nativePlaceSelection T)) (j : SignedLabel l.value) :
    0 < actualThetaValueFamily (l := l) T b j :=
  thetaValueFromQ_pos (l := l) T b j

/-- The actual theta-value zero locus: the indices where the real theta value
vanishes.  This is empty because the actual theta values are positive; it is
not the source theta divisor. -/
def actualThetaValueZeroLocus : Set (Bad (nativePlaceSelection T) × SignedLabel l.value) :=
  {x | actualThetaValueFamily (l := l) T x.1 x.2 = 0}

/-- The actual Theta-value zero locus is empty. -/
theorem actualThetaValueZeroLocus_eq_empty :
    actualThetaValueZeroLocus (l := l) T = ∅ := by
  ext x
  constructor
  · intro hx
    exact (ne_of_gt (actualThetaValueFamily_pos (l := l) T x.1 x.2)) hx
  · intro hx
    exact absurd hx (Set.not_mem_empty x)

/-- Exact outstanding obligations: the source theta function/line bundle, its
global zero divisor identified with the {q_j^2} divisor, and the Theta-link
identification are not constructed.  The list is the exact named datum; it is
not a propositional gate. -/
def SourceThetaDivisorObstruction :
    ABCBridge.SourceThetaFunctionLineBundleActual.ThetaFunctionLineBundleObligations
      T.tuple.source :=
  ABCBridge.SourceThetaFunctionLineBundleActual.actualThetaFunctionLineBundleObligations
    T.tuple.source

/-- Actual Theta-pilot / q-pilot arithmetic-divisor data available from the
native source.  The theta-link relation is kept as the exact source
obstruction, not as a fake link. -/
structure ActualThetaPilotArithmeticDivisorData where
  qPilotDivisor : GlobalIdealFamily T.arithmetic.F
  qPilotDivisor_eq : qPilotDivisor = actualQPilotGlobalIdealFamily T
  thetaValueFamily :
    (b : Bad (nativePlaceSelection T)) -> SignedLabel l.value -> Real
  thetaValueFamily_eq : thetaValueFamily = actualThetaValueFamily (l := l) T
  thetaValueZeroLocus :
    Set (Bad (nativePlaceSelection T) × SignedLabel l.value)
  thetaValueZeroLocus_eq : thetaValueZeroLocus = actualThetaValueZeroLocus (l := l) T
  thetaLinkRelation :
    ABCBridge.SourceThetaFunctionLineBundleActual.ThetaFunctionLineBundleObligations
      T.tuple.source
  thetaLinkRelation_eq : thetaLinkRelation = SourceThetaDivisorObstruction (l := l) T

/-- The actual arithmetic-divisor data object. -/
noncomputable def actualThetaPilotArithmeticDivisorData :
    ActualThetaPilotArithmeticDivisorData (l := l) T where
  qPilotDivisor := actualQPilotGlobalIdealFamily T
  qPilotDivisor_eq := rfl
  thetaValueFamily := actualThetaValueFamily (l := l) T
  thetaValueFamily_eq := rfl
  thetaValueZeroLocus := actualThetaValueZeroLocus (l := l) T
  thetaValueZeroLocus_eq := rfl
  thetaLinkRelation := SourceThetaDivisorObstruction (l := l) T
  thetaLinkRelation_eq := rfl

/-- The actual q-pilot divisor is the constructed global ideal family. -/
theorem actualThetaPilotArithmeticDivisorData_qPilotDivisor :
    (actualThetaPilotArithmeticDivisorData (l := l) T).qPilotDivisor =
      actualQPilotGlobalIdealFamily T := rfl

/-- The actual theta-value zero locus is empty. -/
theorem actualThetaPilotArithmeticDivisorData_zeroLocus :
    (actualThetaPilotArithmeticDivisorData (l := l) T).thetaValueZeroLocus = ∅ :=
  actualThetaValueZeroLocus_eq_empty (l := l) T

end ThetaPilotArithmeticDivisorActualAdapted
end LeanFormal.IUT.XiFPaper
end
