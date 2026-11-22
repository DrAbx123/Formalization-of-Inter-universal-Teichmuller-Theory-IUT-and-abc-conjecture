import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31D4FKDescentBridge
import LeanFormal.IUT.IUTI.InitialTheta.SourcePlacePartitionReduction
import tmp.sheaf.xif.paper.QPilotZeroLocusDivisorActual
import LeanFormal.IUT.Foundations.Geometry.TatePointQuotientBoundary
import tmp.sheaf.n8.closure.NativeBadLiftActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S436KSideQVActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- The actual section-chosen K-place above the bad moduli place b.1. -/
abbrev kSidePlace : NumberField.FinitePlace T.arithmetic.K :=
  sectionFiniteLift (nativePlaceSelection T) b.1

/-- The base-changed curve over K. -/
abbrev kSideCurve : PuncturedEllipticCurve T.arithmetic.K :=
  T.arithmetic.curve.baseChange T.arithmetic.K

/-- Exact missing paper K-side q_v data.  This deliberately does not use
badPlaceQCandidate or Classical.choice of an arbitrary q-candidate. -/
structure KSideQVFamilySpec where
  kPlace : NumberField.FinitePlace T.arithmetic.K
  kPlace_eq : kPlace = kSidePlace (T := T) b
  kCurve : PuncturedEllipticCurve T.arithmetic.K
  kCurve_eq : kCurve = kSideCurve (T := T)
  q : FinitePlaceQCandidate kPlace
  uniformization : TateCurveComparison kCurve kPlace q
  fPlace : NumberField.FinitePlace T.arithmetic.F
  fPlace_eq : fPlace = (nativeBadLift T).lift b
  shadow_compatible :
    fkDescentShadow (nativePlaceSelection T) b.1 = fPlace
  fOrder : Nat
  fOrder_eq : fOrder = (qVFamily T b).order
  order_eq : q.order =
    fkDescentSectionRamificationIndex (nativePlaceSelection T) b.1 * fOrder

/-- Exact missing K-side q_v object. -/
def KSideQVFamilyRequired : Prop :=
  Nonempty (KSideQVFamilySpec (T := T) (b := b))

/-- The three exact missing fields, packaged separately for audit. -/
structure MissingKSideQVFields where
  fPlace : NumberField.FinitePlace T.arithmetic.F
  fPlace_eq : fPlace = (nativeBadLift T).lift b
  shadowEq : Prop
  qObject : Prop
  uniformization : Prop
  orderEquality : Prop

def MissingKSideQVFieldsRequired : Prop :=
  Nonempty (MissingKSideQVFields (T := T) (b := b))

end LeanFormal.IUT.XiFPaper.S436KSideQVActual

end
