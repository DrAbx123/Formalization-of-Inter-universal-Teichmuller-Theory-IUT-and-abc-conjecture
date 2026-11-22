import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceIQHullSignedCertificateNonvacuous
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.ConcreteFiniteRouteColumns

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S616FinalCor312ContractActualAdapted

open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ConcreteFiniteStepXI

universe u v w uL

variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {ι : Type v} [Fintype ι] {V : ι -> Type w}
variable (places : (i : ι) -> V i -> FinitePlaceAtPrime K p)
variable (tuple : (i : ι) -> V i)
variable [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
variable [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
variable (μ : Measure (ArithmeticTensorTupleBlock places tuple))
variable [Measure.IsAddHaarMeasure μ]
variable (l : PrimeGeFive) (N : Nat)

/-- Actual final Step-XI contract: qSigned/thetaSigned are the actual
arithmetic-tuple Haar logs; ipl/she/apt are the actual finite-column
propositions with their proofs. -/
noncomputable def finalCor312Contract
    (l : PrimeGeFive) (N : Nat) : StepXIContract :=
  (arithmeticTupleSignedFloorCertificate (places := places) (tuple := tuple)
    (label := PUnit) μ).toContract
    (arithmeticTupleSignedFloorLinkEvidence (places := places) (tuple := tuple)
      (label := PUnit) μ
      (finiteIPLProposition l N) (finiteSHEProposition l N)
      (finiteAPTProposition l N)
      (finiteIPLProposition_proved l N)
      (finiteSHEProposition_proved l N)
      (finiteAPTProposition_proved l N))

theorem finalCor312Contract_conclusion : Cor312Conclusion (finalCor312Contract places tuple μ l N) :=
  arithmeticTupleSignedFloorCor312Conclusion (places := places) (tuple := tuple)
    (label := PUnit) μ
    (finiteIPLProposition l N) (finiteSHEProposition l N)
    (finiteAPTProposition l N)
    (finiteIPLProposition_proved l N)
    (finiteSHEProposition_proved l N)
    (finiteAPTProposition_proved l N)

theorem finalCor312Contract_q_negative : (finalCor312Contract places tuple μ l N).qSigned < 0 :=
  (finalCor312Contract places tuple μ l N).q_negative

theorem finalCor312Contract_q_le_target :
    (finalCor312Contract places tuple μ l N).qSigned ≤
      (finalCor312Contract places tuple μ l N).targetSigned :=
  (finalCor312Contract places tuple μ l N).q_le_target

theorem finalCor312Contract_target_le_theta :
    (finalCor312Contract places tuple μ l N).targetSigned ≤
      (finalCor312Contract places tuple μ l N).thetaSigned :=
  (finalCor312Contract places tuple μ l N).target_le_theta

theorem finalCor312Contract_ipl : (finalCor312Contract places tuple μ l N).ipl :=
  (finalCor312Contract places tuple μ l N).ipl_evidence

theorem finalCor312Contract_she : (finalCor312Contract places tuple μ l N).she :=
  (finalCor312Contract places tuple μ l N).she_evidence

theorem finalCor312Contract_apt : (finalCor312Contract places tuple μ l N).apt :=
  (finalCor312Contract places tuple μ l N).apt_evidence

end LeanFormal.IUT.XiFPaper.S616FinalCor312ContractActualAdapted

end
