import LeanFormal.IUT.Foundations.Theta.OddTheta
import LeanFormal.IUT.Foundations.Geometry.TateYCoordinateSeries
import LeanFormal.IUT.Foundations.Geometry.TateWeierstrassPointEquation

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.TateCurve
open LeanFormal.IUT.Foundations.Theta
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1600000

namespace LeanFormal.IUT.XiFPaper.TateThetaLayerAttempt

abbrev tateTheta {L : Type*} [NormedField L] [IsUltrametricDist L]
    [CompleteSpace L] (q U : L) : L :=
  oddTheta q U

theorem tateTheta_summable {L : Type*} [NormedField L] [IsUltrametricDist L]
    [CompleteSpace L] (q U : L) (hU : U ≠ 0) (hq : norm q < 1) :
    Summable (fun n : Int => oddThetaTerm q U n) :=
  summable_oddThetaTerm q U hU hq

theorem tateTheta_hasSum {L : Type*} [NormedField L] [IsUltrametricDist L]
    [CompleteSpace L] (q U : L) (hU : U ≠ 0) (hq : norm q < 1) :
    HasSum (fun n : Int => oddThetaTerm q U n) (tateTheta q U) :=
  (tateTheta_summable q U hU hq).hasSum

def TateThetaXRelationTarget {L : Type*} [NormedField L] [IsUltrametricDist L] [CompleteSpace L]
    (xOfTheta : L -> L -> L -> L) : Prop :=
  forall (q u : L), coordinateSeries q u = xOfTheta q u (tateTheta q u)

def TateThetaYRelationTarget {L : Type*} [NormedField L] [IsUltrametricDist L] [CompleteSpace L]
    (yOfTheta : L -> L -> L -> L) : Prop :=
  forall (q u : L), yCoordinateSeries q u = yOfTheta q u (tateTheta q u)

def TateThetaDuplicationTarget {L : Type*} [NormedField L] [IsUltrametricDist L] [CompleteSpace L]
    (addTheta : L -> L -> L -> L) : Prop :=
  forall (q u v : L), addTheta q u v = tateTheta q (u * v)

def TateThetaOddEquationTarget {L : Type*} [NormedField L] [CharZero L]
    [CompleteSpace L] (q : L) : Prop :=
  forall u : L,
    inversionOddYCoordinateSeries q u ^ 2 =
      4 * coordinateSeries q u ^ 3 + coordinateSeries q u ^ 2 +
        4 * a4 L q * coordinateSeries q u + 4 * a6 L q

#check tateTheta
#check tateTheta_summable
#check tateTheta_hasSum
#check TateThetaXRelationTarget
#check TateThetaYRelationTarget
#check TateThetaDuplicationTarget
#check TateThetaOddEquationTarget
#print axioms tateTheta_summable
#print axioms tateTheta_hasSum

end LeanFormal.IUT.XiFPaper.TateThetaLayerAttempt
end