import LeanFormal.IUT.IUTI.InitialTheta.ConcreteInitialThetaCStage
import tmp.sheaf.xif.paper.QPilotZeroLocusDivisorActual

/-!
# Source theater thetaPacket versus qVFamily: actual mismatch

The concrete source theater theta packet is built from the fixed rational value

  gaussianFiveThetaQ

(ConcreteInitialThetaCStage.theta_q).  The qVFamily used by the qside global
divisor is the per-bad-place Clause-B Tate comparison parameter q_v.  There is no
theorem in the tree identifying the source theater thetaPacket q with qVFamily
q_v, and no one-column scale identification either.

This file records the actual concrete source q and the exact missing
identification type.  It does not continue the comparison using the independent
q family.

No fake equality, PUnit/True, arbitrary data, axiom or sorry is used.
-/

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

namespace LeanFormal.IUT.XiFPaper.SourceTheaterQVFamilyMismatchActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual

universe u

variable {l : PrimeGeFive}

/-- The concrete source theater theta q. -/
noncomputable def concreteSourceTheaterQ (l : PrimeGeFive) : Real :=
  (concreteInitialThetaCStage l).theater.thetaPacket.q

/-- The concrete source theater q is the fixed gaussianFiveThetaQ. -/
theorem concreteSourceTheaterQ_eq_gaussian (l : PrimeGeFive) :
    concreteSourceTheaterQ l = gaussianFiveThetaQ :=
  concreteInitialThetaCStage_theta_q l

/-- The qVFamily q at an actual bad place. -/
noncomputable def sourceQVFamilyQ
    (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) : Real :=
  (qVFamily T b).q

/-- Exact missing source identification: the concrete theater theta q equals
the qVFamily q_v at every bad place. -/
structure SourceTheaterQVFamilyIdentification
    (T : SourceNativeInitialThetaData.{0} l) where
  sourceQ_eq_qVFamily : ∀ b : Bad (nativePlaceSelection T),
    concreteSourceTheaterQ l = sourceQVFamilyQ T b

/-- Exact mismatch obstruction: no actual source theorem identifies the
concrete theater theta q with the qVFamily q_v. -/
def SourceTheaterQVFamilyMismatch
    (T : SourceNativeInitialThetaData.{0} l) : Prop :=
  Nonempty (SourceTheaterQVFamilyIdentification T)

/-- The mismatch is exactly the missing identification type. -/
theorem SourceTheaterQVFamilyMismatch_iff
    (T : SourceNativeInitialThetaData.{0} l) :
    SourceTheaterQVFamilyMismatch T ↔
      Nonempty (SourceTheaterQVFamilyIdentification T) :=
  Iff.rfl

/-- The concrete source q is fixed by the concrete C-stage construction. -/
theorem concreteSourceTheaterQ_fixed :
    concreteSourceTheaterQ (l := l) = gaussianFiveThetaQ :=
  concreteSourceTheaterQ_eq_gaussian l

end LeanFormal.IUT.XiFPaper.SourceTheaterQVFamilyMismatchActualAdapted

end
