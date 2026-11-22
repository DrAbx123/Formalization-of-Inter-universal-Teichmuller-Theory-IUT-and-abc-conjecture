import tmp.sheaf.xif.paper.S3014StepVProcessionAverageActual
import tmp.sheaf.xif.paper.S2921HeightBridgeActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.XiFPaper.S3014StepVProcessionAverageActual
open LeanFormal.IUT.XiFPaper.S2921HeightBridgeActual
open Finset
open scoped BigOperators
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000000

namespace LeanFormal.IUT.XiFPaper.S3029StepVAlignmentActual

universe u v w

variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {ι : Type v} [Fintype ι] {V : ι -> Type w}

noncomputable def S3029DifferentTerm
    (places : (i : ι) -> V i -> FinitePlaceAtPrime K p)
    (tuple : (i : ι) -> V i) : Real :=
  (∑ i, localNormOrder p (arithmeticTupleLocalDifferent places tuple i)) *
    Real.log (p : Real)

noncomputable def S3029ExceptionalTerm
    (places : (i : ι) -> V i -> FinitePlaceAtPrime K p)
    (tuple : (i : ι) -> V i) (exceptional : Finset ι) : Real :=
  ∑ i ∈ exceptional, (3 + Real.log
    (logShellRamificationExponent
      (K := CommonPrimeCompletion (places i (tuple i))) (p := p) : Real))

noncomputable def S3029StepVTerm
    (places : (i : ι) -> V i -> FinitePlaceAtPrime K p)
    (tuple : (i : ι) -> V i) (istar : ι)
    (jValue : CommonPrimeCompletion (places istar (tuple istar)))
    (l label : Nat) : Real :=
  -(stepVLambda p label jValue l) * Real.log (p : Real)

variable (places : (i : ι) -> V i -> FinitePlaceAtPrime K p)
variable (tuple : (i : ι) -> V i) (istar : ι)
variable (jValue : CommonPrimeCompletion (places istar (tuple istar)))
variable (exceptional : Finset ι) (l n : Nat)

theorem S3029_perLabel_decomposition (label : Nat) :
    S3014PerLabelBound places tuple istar jValue exceptional l label =
      S3029StepVTerm places tuple istar jValue l label +
        S3029DifferentTerm places tuple + Real.log (p : Real) +
        S3029ExceptionalTerm places tuple exceptional :=
by
  unfold S3014PerLabelBound S3029StepVTerm S3029DifferentTerm S3029ExceptionalTerm
  ring

structure S3029AlignmentData
    (places : (i : ι) -> V i -> FinitePlaceAtPrime K p)
    (tuple : (i : ι) -> V i) (istar : ι)
    (jValue : CommonPrimeCompletion (places istar (tuple istar)))
    (exceptional : Finset ι) (l : Nat) (D Q S T : Real) where
  cD : Real
  cQ : Real
  cS : Real
  cT : Real
  c0 : Real
  sS : Real
  sT : Real
  qCoeff : Nat -> Real
  labelRest : Nat -> Real
  different_eq :
    S3029DifferentTerm places tuple = cD * D + cQ * Q + cS * S + cT * T + c0
  exceptional_eq :
    S3029ExceptionalTerm places tuple exceptional = sS * S + sT * T
  stepV_eq :
    ∀ label, S3029StepVTerm places tuple istar jValue l label =
      qCoeff label * Q + labelRest label

theorem S3029_perLabel_affine
    (D Q S T : Real) (A : S3029AlignmentData places tuple istar jValue exceptional l D Q S T)
    (label : Nat) :
    S3014PerLabelBound places tuple istar jValue exceptional l label =
      A.cD * D + (A.qCoeff label + A.cQ) * Q +
        (A.cS + A.sS) * S + (A.cT + A.sT) * T +
        (A.c0 + Real.log (p : Real)) + A.labelRest label :=
by
  rw [S3029_perLabel_decomposition]
  rw [A.different_eq, A.exceptional_eq, A.stepV_eq]
  ring

#check S3029DifferentTerm
#check S3029ExceptionalTerm
#check S3029StepVTerm
#check S3029_perLabel_decomposition
#check S3029AlignmentData
#check S3029_perLabel_affine
#print axioms S3029_perLabel_decomposition
#print axioms S3029_perLabel_affine

end LeanFormal.IUT.XiFPaper.S3029StepVAlignmentActual
end
