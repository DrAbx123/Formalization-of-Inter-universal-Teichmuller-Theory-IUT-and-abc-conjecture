import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceIQHullSignedCertificate
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.ConcreteFiniteRouteColumns

/-! # S650: actual signed Cor312Conclusion contract

The contract is built from the actual signed Haar certificate:

* qSigned = canonical hull Haar log;
* thetaSigned = unit-region Haar log;
* targetSigned = unit-region Haar log;
* ipl/she/apt = actual finite-column propositions with actual evidence.

The conclusion is the real signed inequality qSigned <= thetaSigned. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 6000000

namespace LeanFormal.IUT.XiFPaper.S650ActualSignedCor312Contract

open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.IUTIII.Corollary312.StepXI

universe u v w uL

variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {ι : Type v} [Fintype ι] {V : ι → Type w}
variable (places : (i : ι) → V i → NumberField.FinitePlace K p)
variable (tuple : (i : ι) → V i)
variable [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
variable [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
variable (μ : Measure (ArithmeticTensorTupleBlock places tuple))
variable [Measure.IsAddHaarMeasure μ]
variable (hneg : arithmeticTupleCanonicalHullHaarLog places tuple μ < 0)
variable (l : PrimeGeFive) (N : Nat)

/-- Actual signed contract with finite-column IPL/SHE/APT evidence. -/
noncomputable def s650ActualSignedContract : StepXIContract :=
  (arithmeticTupleSignedFiniteCertificate places tuple
    (FiniteColumnIndex l N) μ hneg).toContract
    (arithmeticTupleSignedLinkEvidence places tuple
      (FiniteColumnIndex l N) μ hneg
      (finiteIPLProposition l N)
      (finiteSHEProposition l N)
      (finiteAPTProposition l N)
      (finiteIPLProposition_proved l N)
      (finiteSHEProposition_proved l N)
      (finiteAPTProposition_proved l N))

/-- Final Corollary 3.12 conclusion for the actual signed contract. -/
theorem s650ActualSignedCor312Conclusion :
    Cor312Conclusion (s650ActualSignedContract places tuple μ hneg l N) :=
  cor312_of_signed_finite_certificate
    (arithmeticTupleSignedFiniteCertificate places tuple
      (FiniteColumnIndex l N) μ hneg)
    (arithmeticTupleSignedLinkEvidence places tuple
      (FiniteColumnIndex l N) μ hneg
      (finiteIPLProposition l N)
      (finiteSHEProposition l N)
      (finiteAPTProposition l N)
      (finiteIPLProposition_proved l N)
      (finiteSHEProposition_proved l N)
      (finiteAPTProposition_proved l N))

end LeanFormal.IUT.XiFPaper.S650ActualSignedCor312Contract

end
