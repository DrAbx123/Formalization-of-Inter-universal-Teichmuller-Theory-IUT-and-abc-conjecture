import tmp.sheaf.xif.paper.SignedSourceTheoryGateAdapted
import tmp.sheaf.xif.paper.PaperThetaMagnitudeSignedActual
import tmp.sheaf.xif.paper.SignedAverageBoundActual
import tmp.sheaf.xif.paper.SignedHnormalActual

/-! # CONDITIONAL STATUS (xi-f)

Conditional gate via a q-norm/log-5 route. That route is only a conditional diagnostic and is not valid as target evidence without actual objects; the true missing field is the direct SignedThetaAverageLeQMagnitude.

This module is NOT an unconditional target closure. Do not use it as evidence that paper xi-f is proved; read its exact Missing declarations and the audit ledger.
-/


/-!
# Conditional signed source-theory gate and exact q bound

Builds the final `SignedSourceTheoryGateAdapted` from `SignedHnormal` plus an
explicit signed magnitude comparison. The q-norm conditional route uses
`paperQPilotLogMagnitude = log 5` and the proposed bound
`SignedThetaAverageLeLogFive`; that bound is exactly the missing q bound.

`SignedAverageBoundActual` computes the actual signed average as
`log 5 * gaussExponentSum / card(SignedLabel 5)`. At l = 5 the Gauss sum is
10 over 5 labels, so the signed average is `2 log 5`, strictly larger than
`log 5 = paperQPilotLogMagnitude`. Hence the q-norm/log-5 bound is FALSE for
l = 5 and cannot be used; the true missing q bound is the direct signed
magnitude comparison, not a consequence of q-norm. No fake bound is
asserted. WRITE-ONLY: no lake.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.SignedSourceTheoryGateAdaptedConditional

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8C6ActualIQ
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.SignedXiFAssembly
open LeanFormal.IUT.XiFPaper.SignedSourceTheoryGateAdapted
open LeanFormal.IUT.XiFPaper.PaperThetaMagnitudeSignedActual
open LeanFormal.IUT.XiFPaper.SignedAverageBoundActual
open MeasureTheory
open scoped BigOperators

universe ua uv upi umon ui uK uW

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable {K : Type uK} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {iota : Type uv} [Fintype iota] {W : iota -> Type uW}
variable (places : (i : iota) -> W i -> FinitePlaceAtPrime K p)
variable (tuple : (i : iota) -> W i)
variable [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
variable [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
variable (mu : Measure (ArithmeticTensorTupleBlock places tuple))
variable [Measure.IsAddHaarMeasure mu]

/-- The q-norm/conditional bound used by the gate: signed average <= log 5. -/
def SignedQNormBound
    (D : SourcePilotRegionDonors (l := l) (V := V) I) : Prop :=
  SignedThetaAverageLeLogFive (l := l) (V := V) (I := I) D

/-- Conditional conversion of the q-norm/log-5 bound to the exact signed
/-- magnitude comparison, assuming the actual q-pilot magnitude is log 5. -/
def signedMagnitudeComparison_of_qNormBound
    (D : SourcePilotRegionDonors (l := l) (V := V) I)
    (hqmag : paperQPilotLogMagnitude
      (actualSignedC3 (l := l) (V := V) (I := I) D) = Real.log 5)
    (hbound : SignedQNormBound (l := l) (V := V) (I := I) D) :
    SignedThetaAverageLeQMagnitude (l := l) (V := V) (I := I) D := by
  unfold SignedQNormBound SignedThetaAverageLeLogFive at hbound
  unfold SignedThetaAverageLeQMagnitude
  rw [hqmag]
  exact hbound

/-- Conditional final gate from SignedHnormal plus the q-norm/log-5 bound. -/
def signedSourceTheoryGate_of_qNormBound
    (D : SourcePilotRegionDonors (l := l) (V := V) I)
    (hnormal : SignedHnormal (l := l) (V := V) (I := I)
      places tuple mu D)
    (hqmag : paperQPilotLogMagnitude
      (actualSignedC3 (l := l) (V := V) (I := I) D) = Real.log 5)
    (hbound : SignedQNormBound (l := l) (V := V) (I := I) D) :
    SignedSourceTheoryGateAdapted (l := l) (V := V) (I := I) places tuple mu D where
  hlog := actualSignedC3_hlog (l := l) (V := V) (I := I) D
  signedHnormal := hnormal
  signedThetaAverageLeQMagnitude :=
    signedMagnitudeComparison_of_qNormBound (l := l) (V := V) (I := I)
      places tuple mu D hqmag hbound

/-- Exact missing q bound: the direct signed magnitude comparison. The-
/-- q-norm/log-5 route is not sufficient: at l = 5 the actual signed average
/-- is 2 log 5, so SignedQNormBound is false for l = 5 and cannot be supplied
/-- as a theorem. -/
def ExactMissingSignedQBound
    (D : SourcePilotRegionDonors (l := l) (V := V) I) : Prop :=
  SignedThetaAverageLeQMagnitude (l := l) (V := V) (I := I) D

#check SignedQNormBound
#check signedMagnitudeComparison_of_qNormBound
#check signedSourceTheoryGate_of_qNormBound
#check ExactMissingSignedQBound
#check SignedSourceTheoryGateAdapted
#check SignedHnormal
#check SignedThetaAverageLeQMagnitude
#check gaussExponentSum
#check SignedThetaAverageLeLogFive

end LeanFormal.IUT.XiFPaper.SignedSourceTheoryGateAdaptedConditional

end
