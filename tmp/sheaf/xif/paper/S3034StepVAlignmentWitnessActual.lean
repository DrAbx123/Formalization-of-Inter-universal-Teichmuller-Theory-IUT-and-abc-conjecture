import tmp.sheaf.xif.paper.S3029StepVAlignmentActual
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.XiFPaper.S3029StepVAlignmentActual
open LeanFormal.IUT.XiFPaper.S3014StepVProcessionAverageActual
open Finset
open scoped BigOperators
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000
namespace LeanFormal.IUT.XiFPaper.S3034StepVAlignmentWitnessActual

universe u v w
variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {ι : Type v} [Fintype ι] {V : ι -> Type w}
variable (places : (i : ι) -> V i -> FinitePlaceAtPrime K p)
variable (tuple : (i : ι) -> V i) (istar : ι)
variable (jValue : CommonPrimeCompletion (places istar (tuple istar)))
variable (exceptional : Finset ι) (l : Nat)

/-- A concrete (trivial-coefficient) alignment datum: D is the different term, S is the exceptional term, and all StepV labels are put in labelRest.  This proves the alignment structure is inhabited; it is not the paper's numerical alignment. -/
noncomputable def S3034AlignmentData :
    S3029AlignmentData places tuple istar jValue exceptional l
      (S3029DifferentTerm places tuple) 0
      (S3029ExceptionalTerm places tuple exceptional) 0 where
  cD := 1
  cQ := 0
  cS := 0
  cT := 0
  c0 := 0
  sS := 1
  sT := 0
  qCoeff := fun _ => 0
  labelRest := fun label => S3029StepVTerm places tuple istar jValue l label
  different_eq := by
    unfold S3029DifferentTerm
    ring
  exceptional_eq := by
    unfold S3029ExceptionalTerm
    ring
  stepV_eq := by
    intro label
    ring

theorem S3034_perLabel_affine (label : Nat) :
    S3014PerLabelBound places tuple istar jValue exceptional l label =
      (S3034AlignmentData places tuple istar jValue exceptional l).cD *
          (S3029DifferentTerm places tuple) +
        ((S3034AlignmentData places tuple istar jValue exceptional l).qCoeff label +
          (S3034AlignmentData places tuple istar jValue exceptional l).cQ) * 0 +
        ((S3034AlignmentData places tuple istar jValue exceptional l).cS +
          (S3034AlignmentData places tuple istar jValue exceptional l).sS) *
          (S3029ExceptionalTerm places tuple exceptional) +
        ((S3034AlignmentData places tuple istar jValue exceptional l).cT +
          (S3034AlignmentData places tuple istar jValue exceptional l).sT) * 0 +
        ((S3034AlignmentData places tuple istar jValue exceptional l).c0 + Real.log (p : Real)) +
        (S3034AlignmentData places tuple istar jValue exceptional l).labelRest label :=
  S3029_perLabel_affine places tuple istar jValue exceptional l
    (S3029DifferentTerm places tuple) 0
    (S3029ExceptionalTerm places tuple exceptional) 0
    (S3034AlignmentData places tuple istar jValue exceptional l) label

#check S3034AlignmentData
#check S3034_perLabel_affine
#print axioms S3034_perLabel_affine

end LeanFormal.IUT.XiFPaper.S3034StepVAlignmentWitnessActual